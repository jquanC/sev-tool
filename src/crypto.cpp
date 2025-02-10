/**************************************************************************
 * Copyright 2018 Advanced Micro Devices, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 **************************************************************************/

#include "crypto.h"
#include "sevapi.h"
#include "sevcert.h"

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/objects.h>
#include <openssl/ts.h>
#include <openssl/ecdh.h>
#include <openssl/err.h>

// #include <openssl/core_names.h> // e.g., use EVP_PKEY_assign_EC_KEY

// NIST Compliant KDF
bool kdf(uint8_t *key_out,       size_t key_out_length,
         const uint8_t *key_in,  size_t key_in_length,
         const uint8_t *label,   size_t label_length,
         const uint8_t *context, size_t context_length)
{
    if (!key_out || !key_in || !label || (key_out_length == 0) ||
       (key_in_length == 0) || (label_length == 0))
        return false;

    bool ret_val = false;
    uint8_t null_byte = '\0';
    unsigned int out_len = 0;
    uint8_t prf_out[NIST_KDF_H_BYTES];      // Buffer to collect PRF output

    // Length in bits of derived key
    uint32_t l = (uint32_t)(key_out_length * BITS_PER_BYTE);

    // Number of iterations to produce enough derived key bits
    uint32_t n = ((l - 1) / NIST_KDF_H) + 1;

    size_t BytesLeft = key_out_length;
    uint32_t offset = 0;

    // Create and initialize the context
    HMAC_CTX *ctx;
    if (!(ctx = HMAC_CTX_new()))
        return ret_val;

    for (unsigned int i = 1; i <= n; i++) {
        if (HMAC_CTX_reset(ctx) != 1)
            break;

        // Calculate a chunk of random data from the PRF
        if (HMAC_Init_ex(ctx, key_in, (int)key_in_length, EVP_sha256(), NULL) != 1)
            break;
        if (HMAC_Update(ctx, (uint8_t *)&i, sizeof(i)) != 1)
            break;
        if (HMAC_Update(ctx, (unsigned char*)label, label_length) != 1)
            break;
        if (HMAC_Update(ctx, &null_byte, sizeof(null_byte)) != 1)
            break;
        if ((context) && (context_length != 0)) {
            if (HMAC_Update(ctx, (unsigned char*)context, context_length) != 1)
                break;
        }
        if (HMAC_Update(ctx, (uint8_t *)&l, sizeof(l)) != 1)
            break;
        if (HMAC_Final(ctx, prf_out, &out_len) != 1)
            break;

        // Write out the key bytes
        if (BytesLeft <= NIST_KDF_H_BYTES) {
            memcpy(key_out + offset, prf_out, BytesLeft);
        }
        else {
            memcpy(key_out + offset, prf_out, NIST_KDF_H_BYTES);
            offset    += NIST_KDF_H_BYTES;
            BytesLeft -= NIST_KDF_H_BYTES;
        }

        if (i == n)          // If successfully finished all iterations
            ret_val = true;
    }

    HMAC_CTX_free(ctx);
    return ret_val;
}

/**
 * Note that this function NEWs/allocates memory for a
 * uint8_t array using OPENSSL_malloc that must be freed
 * in the calling function using OPENSSL_FREE()
 */
uint8_t *calculate_shared_secret(EVP_PKEY *priv_key, EVP_PKEY *peer_key,
                                 size_t& shared_key_len_out)
{
    if (!priv_key || !peer_key)
        return NULL;

    bool success = false;
    EVP_PKEY_CTX *ctx = NULL;
    uint8_t *shared_key = NULL;

    do {
        // Create the context using your private key
        if (!(ctx = EVP_PKEY_CTX_new(priv_key, NULL)))
            break;

        // Calculate the intermediate secret
        if (EVP_PKEY_derive_init(ctx) <= 0)
            break;
        if (EVP_PKEY_derive_set_peer(ctx, peer_key) <= 0)
            break;

        // Determine buffer length
        if (EVP_PKEY_derive(ctx, NULL, &shared_key_len_out) <= 0)
            break;

        // Need to free shared_key using OPENSSL_FREE() in the calling function
        shared_key = (unsigned char*)OPENSSL_malloc(shared_key_len_out);
        if (!shared_key)
            break;      // malloc failure

        // Compute the shared secret with the ECDH key material.
        if (EVP_PKEY_derive(ctx, shared_key, &shared_key_len_out) <= 0)
            break;

        success = true;
    } while (0);

    EVP_PKEY_CTX_free(ctx);

    return success ? shared_key : NULL;
}

/**
 * Generate a master_secret value from our (test suite) Private DH key,
 *   the Platform's public DH key, and a nonce
 * This function calls two functions (above) which allocate memory
 *   for keys, and this function must free that memory
 */
bool derive_master_secret(aes_128_key master_secret,
                        EVP_PKEY *godh_priv_key,
                        const sev_cert *pdh_public,
                        const uint8_t nonce[sizeof(nonce_128)])
{
    if (!godh_priv_key || !pdh_public)
        return false;

    sev_cert dummy;
    memset(&dummy, 0, sizeof(sev_cert));    // To remove compile warnings
    SEVCert temp_obj(&dummy);           // TODO. Hack b/c just want to call function later
    bool ret = false;
    EVP_PKEY *plat_pub_key = NULL;   // Peer key
    size_t shared_key_len = 0;

    do {
        // New up the Platform's public EVP_PKEY
        if (!(plat_pub_key = EVP_PKEY_new()))
            break;

        /*
         * Get the friend's Public EVP_PKEY from the certificate
         * This function allocates memory and attaches an EC_Key
         *  to your EVP_PKEY so, to prevent mem leaks, make sure
         *  the EVP_PKEY is freed at the end of this function
         */
        if (temp_obj.compile_public_key_from_certificate(pdh_public, plat_pub_key) != STATUS_SUCCESS)
            break;

        /*
         * Calculate the shared secret
         * This function is allocating memory for this uint8_t[],
         *  must free it at the end of this function
         */
        uint8_t *shared_key = calculate_shared_secret(godh_priv_key, plat_pub_key, shared_key_len);
        if (!shared_key)
            break;

        // Derive the master secret from the intermediate secret
        if (!kdf((unsigned char*)master_secret, sizeof(aes_128_key), shared_key,
            shared_key_len, (uint8_t *)SEV_MASTER_SECRET_LABEL,
            sizeof(SEV_MASTER_SECRET_LABEL)-1, nonce, sizeof(nonce_128))) // sizeof(nonce), bad?
            break;

        // Free memory allocated in calculate_shared_secret
        OPENSSL_free(shared_key);    // Local variable

        ret = true;
    } while (0);

    EVP_PKEY_free(plat_pub_key);

    return ret;
}

bool derive_kek(aes_128_key kek, const aes_128_key master_secret)
{
    bool ret = kdf((unsigned char*)kek, sizeof(aes_128_key), master_secret, sizeof(aes_128_key),
                   (uint8_t *)SEV_KEK_LABEL, sizeof(SEV_KEK_LABEL)-1, NULL, 0);
    return ret;
}

bool derive_kik(hmac_key_128 kik, const aes_128_key master_secret)
{
    bool ret = kdf((unsigned char*)kik, sizeof(aes_128_key), master_secret, sizeof(aes_128_key),
                   (uint8_t *)SEV_KIK_LABEL, sizeof(SEV_KIK_LABEL)-1, NULL, 0);
    return ret;
}

bool gen_hmac(hmac_sha_256 *out, hmac_key_128 key, uint8_t *msg, size_t msg_len)
{
    if (!out || !msg)
        return false;

    unsigned int out_len = 0;
    HMAC(EVP_sha256(), key, sizeof(hmac_key_128), msg,    // Returns NULL or value of out
         msg_len, (uint8_t *)out, &out_len);

    if ((out != NULL) && (out_len == sizeof(hmac_sha_256)))
        return true;
    else
        return false;
}

bool encrypt(uint8_t *out, const uint8_t *in, size_t length,
             const aes_128_key key, const iv_128 iv)
{
    if (!out || !in)
        return false;

    EVP_CIPHER_CTX *ctx;
    int len = 0;
    bool ret_val = false;

    do {
        // Create and initialize the context
        if (!(ctx = EVP_CIPHER_CTX_new()))
            break;

        // Initialize the encryption operation. IMPORTANT - ensure you
        // use a key and IV size appropriate for your cipher
        if (EVP_EncryptInit_ex(ctx, EVP_aes_128_ctr(), NULL, key, iv) != 1)
            break;

        // Provide the message to be encrypted, and obtain the encrypted output
        if (EVP_EncryptUpdate(ctx, out, &len, in, (int)length) != 1)
            break;

        // Finalize the encryption. Further out bytes may be written at
        // this stage
        if (EVP_EncryptFinal_ex(ctx, out + len, &len) != 1)
            break;

        ret_val = true;
    } while (0);

    // Clean up
    EVP_CIPHER_CTX_free(ctx);

    return ret_val;
}

/**
 * Description:   Generates a new P-384 key pair
 * Typical Usage: Used to create a new Guest Owner DH
 *                (Elliptic Curve Diffie Hellman (ECDH)) P-384 key pair
 * Parameters:    [evp_key_pair] the output EVP_PKEY to which the keypair gets
 *                  set
 *                [curve] P-384 (default) or P-256 (only for negative testing)
 * Note:          This key must be initialized (with EVP_PKEY_new())
 *                before passing in
 */
bool generate_ecdh_key_pair(EVP_PKEY **evp_key_pair, SEV_EC curve)
{
    if (!evp_key_pair)
        return false;

    bool ret = false;
    int nid = 0;
    EC_KEY *ec_key_pair = NULL;

    do {
        // New up the Guest Owner's private EVP_PKEY
        if (!(*evp_key_pair = EVP_PKEY_new()))
            break;

        // New up the EC_KEY with the EC_GROUP
        if (curve == SEV_EC_P256)
            nid = EC_curve_nist2nid("P-256");   // NID_secp256r1
        else if(curve == SEV_EC_P384)
            nid = EC_curve_nist2nid("P-384");   // NID_secp384r1
        else{
            // SM2 flow:
            EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_EC, NULL);
            if (ctx == NULL) {
                ERR_print_errors_fp(stderr);
                return false;
            }

            if (EVP_PKEY_keygen_init(ctx) <= 0) {
                ERR_print_errors_fp(stderr);
                EVP_PKEY_CTX_free(ctx);
                return false;
            }

            // Set the group name to "sm2" for SM2 keys
            if (EVP_PKEY_CTX_set_group_name(ctx, "sm2") <= 0) {
                ERR_print_errors_fp(stderr);
                EVP_PKEY_CTX_free(ctx);
                return false;
            }

            if (EVP_PKEY_keygen(ctx, evp_key_pair) <= 0) {
                ERR_print_errors_fp(stderr);
                EVP_PKEY_CTX_free(ctx);
                return false;
            }

            EVP_PKEY_CTX_free(ctx);
            
            return true;
        }
        // other flow:
        ec_key_pair = EC_KEY_new_by_curve_name(nid);

        // Create the new public/private EC key pair. EC_key must have a group
        // associated with it before calling this function
        if (EC_KEY_generate_key(ec_key_pair) != 1)
            break;

        /*
         * Convert EC key to EVP_PKEY
         * This function links evp_key_pair to ec_key_pair, so when evp_key_pair is
         *  freed, ec_key_pair is freed. We don't want the user to have to manage 2
         *  keys, so just return EVP_PKEY and make sure user free's it
         */
        if (EVP_PKEY_assign_EC_KEY(*evp_key_pair, ec_key_pair) != 1)
            break;

        if (!evp_key_pair)
            break;

        ret = true;
    } while (0);

    return ret;
}

//bakin 09.02.2025
// bool generate_ecdh_key_pair(EVP_PKEY **evp_key_pair, SEV_EC curve)
// {
//     if (!evp_key_pair)
//         return false;

//     bool ret = false;
//     int nid = 0;
//     EC_KEY *ec_key_pair = NULL;

//     do {
//         // New up the Guest Owner's private EVP_PKEY
//         if (!(*evp_key_pair = EVP_PKEY_new()))
//             break;

//         // New up the EC_KEY with the EC_GROUP
//         if (curve == SEV_EC_P256)
//             nid = EC_curve_nist2nid("P-256");   // NID_secp256r1
//         else if(curve == SEV_EC_P384)
//             nid = EC_curve_nist2nid("P-384");   // NID_secp384r1
//         else{
//             // SM2 flow:
//             //gen sm2 keypair
//             // EVP_PKEY_CTX *param_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_SM2, NULL);
//             // EVP_PKEY_CTX *param_ctx = EVP_PKEY_CTX_new_id(NID_sm2, NULL); //这两个宏是一样的EVP_PKEY_SM2 和 NID_sm2
//             /* 如果设置 'EVP_PKEY_EC', 则 EVP_PKEY_CTX_set1_id 会报错*/
//             EVP_PKEY_CTX *param_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_EC, NULL);
//             if(!param_ctx){
//                 printf("EVP_PKEY_CTX_new_NID_sm2id failed\n");
//                 return false;
//             }
            
//             // // 设置参数编码方式为命名曲线
//             // if (EVP_PKEY_CTX_ctrl(param_ctx, -1, EVP_PKEY_OP_PARAMGEN,
//             //                     EVP_PKEY_CTRL_EC_PARAM_ENC, OPENSSL_EC_NAMED_CURVE, NULL) <= 0) 
//             // {
//             //     printf("EVP_PKEY_CTRL_EC_PARAM_ENC failed\n");
//             //     EVP_PKEY_CTX_free(param_ctx);
//             //     return false;
//             // }
//             if(EVP_PKEY_paramgen_init(param_ctx) <= 0){
//                 printf("EVP_PKEY_paramgen_init failed\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }
//             if(EVP_PKEY_CTX_set_ec_paramgen_curve_nid(param_ctx, NID_sm2) <= 0){
//                 printf("EVP_PKEY_CTX_set_ec_paramgen_curve_nid failed\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }

//             //生成参数
//             EVP_PKEY *params = NULL;
//             if(EVP_PKEY_paramgen(param_ctx, &params) <= 0){
//                 printf("EVP_PKEY_paramgen failed\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }    
//             //基于参数生成密钥
//             EVP_PKEY_CTX *keygen_ctx = EVP_PKEY_CTX_new(params, NULL);
//             if(!keygen_ctx){
//                 printf("EVP_PKEY_CTX_new failed\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }

//             if(EVP_PKEY_keygen_init(keygen_ctx) <= 0){
//                 printf("EVP_PKEY_keygen_init failed\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }

//             if(EVP_PKEY_keygen(keygen_ctx, evp_key_pair) <= 0){
//                 printf("EVP_PKEY_keygen failed\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }
//             EVP_PKEY_CTX_free(param_ctx);
//             return true;
//         }
//         // other flow:
//         ec_key_pair = EC_KEY_new_by_curve_name(nid);

//         // Create the new public/private EC key pair. EC_key must have a group
//         // associated with it before calling this function
//         if (EC_KEY_generate_key(ec_key_pair) != 1)
//             break;

//         /*
//          * Convert EC key to EVP_PKEY
//          * This function links evp_key_pair to ec_key_pair, so when evp_key_pair is
//          *  freed, ec_key_pair is freed. We don't want the user to have to manage 2
//          *  keys, so just return EVP_PKEY and make sure user free's it
//          */
//         if (EVP_PKEY_assign_EC_KEY(*evp_key_pair, ec_key_pair) != 1)
//             break;

//         if (!evp_key_pair)
//             break;

//         ret = true;
//     } while (0);

//     return ret;
// }

// bool generate_ecdh_key_pair(EVP_PKEY **evp_key_pair, SEV_EC curve)
// {
//     if (!evp_key_pair)
//         return false;

//     bool ret = false;
//     int nid = 0;
//     EC_KEY *ec_key_pair = NULL;

//     do {
//         // New up the Guest Owner's private EVP_PKEY
//         if (!(*evp_key_pair = EVP_PKEY_new()))
//             break;

//         // New up the EC_KEY with the EC_GROUP
//         if (curve == SEV_EC_P256)
//             nid = EC_curve_nist2nid("P-256");   // NID_secp256r1
//         else if(curve == SEV_EC_P384)
//             nid = EC_curve_nist2nid("P-384");   // NID_secp384r1
//         else{
        
//         // SM2 flow:
//             // ===============参数生成阶段================
//             // EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_SM2, NULL);
//             EC_GROUP *group = EC_GROUP_new_by_curve_name(NID_sm2);
//             if(!group){
//                 printf("EC_GROUP_new_by_curve_name failed\n");
//                 return false;
//             }

//             EVP_PKEY_CTX *param_ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_EC, NULL); // pkcs8 标准
//             if(!param_ctx){
//                 printf("EVP_PKEY_CTX_new_id failed\n");
//                 return false;
//             }
            
//             if(EVP_PKEY_paramgen_init(param_ctx) <= 0){
//                 printf("EVP_PKEY_paramgen_init failed\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }

//             //校验
//              EVP_PKEY *params = NULL;
//             // if(EVP_PKEY_keygen_init(ctx) <= 0){
//             //     printf("EVP_PKEY_keygen_init failed\n");
//             //     EVP_PKEY_CTX_free(ctx);
//             //     return false;
//             // } 
//             if(EVP_PKEY_CTX_set_ec_paramgen_curve_nid(param_ctx, NID_sm2) <= 0){
//                 printf("EVP_PKEY_CTX_set_ec_paramgen_curve_nid\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }
//             if(EVP_PKEY_paramgen(param_ctx, &params) <= 0){
//                 printf("EVP_PKEY_paramgen\n");
//                 EVP_PKEY_CTX_free(param_ctx);
//                 return false;
//             }

//             //==================密钥生成阶段========================
//             //生成密钥对
//             EVP_PKEY_CTX *keygen_ctx = NULL;
//             keygen_ctx = EVP_PKEY_CTX_new(params, NULL);
//             if(!keygen_ctx || EVP_PKEY_keygen_init(keygen_ctx) <= 0){
//                 printf("EVP_PKEY_keygen_init failed\n");
//                 EVP_PKEY_CTX_free(keygen_ctx);
//                 return false;
//             }
//             if( EVP_PKEY_keygen(keygen_ctx, evp_key_pair) <= 0){
//                 printf("EVP_PKEY_keygen failed\n");
//                 EVP_PKEY_CTX_free(keygen_ctx);
//                 return false;
//             }

//             // 关键：强制设置密钥类型为SM2
//             const EC_KEY *ec_key = EVP_PKEY_get0_EC_KEY(*evp_key_pair);
//             if (!ec_key) {
//                 printf("EVP_PKEY_get0_EC_KEY failed\n");
//                 return false;
            
//             }
//             EC_KEY_set_group(ec_key, group);
//             EVP_PKEY_set_alias_type(*evp_key_pair, EVP_PKEY_SM2);

//             return true; 
//         }
//         // other flow:
//         ec_key_pair = EC_KEY_new_by_curve_name(nid);

//         // Create the new public/private EC key pair. EC_key must have a group
//         // associated with it before calling this function
//         if (EC_KEY_generate_key(ec_key_pair) != 1)
//             break;

//         /*
//          * Convert EC key to EVP_PKEY
//          * This function links evp_key_pair to ec_key_pair, so when evp_key_pair is
//          *  freed, ec_key_pair is freed. We don't want the user to have to manage 2
//          *  keys, so just return EVP_PKEY and make sure user free's it
//          */
//         if (EVP_PKEY_assign_EC_KEY(*evp_key_pair, ec_key_pair) != 1)
//             break;

//         if (!evp_key_pair)
//             break;

//         ret = true;
//     } while (0);

//     return ret;
// }

/**
 * Description:   Generates a new RSA key pair with salt
 * Typical Usage: Used to create a new OCA cert
 * Parameters:    [evp_key_pair] the output EVP_PKEY to which the keypair gets
 *                  set
 * Note:          This key must be initialized (with EVP_PKEY_new())
 *                before passing in
 */
bool GenerateRSAKeypair(EVP_PKEY **evp_key_pair)
{
    if (!evp_key_pair)
        return false;

    bool ret = false;
    RSA *rsa_key_pair = NULL;
    BIGNUM *bne = NULL;
    int bits = 4096;    // Modulus size in bits
    unsigned long e = RSA_F4;       // 65537

    do {
        // New up the Guest Owner's private EVP_PKEY
        if (!(*evp_key_pair = EVP_PKEY_new()))
            break;

        // Generate RSA key
        bne = BN_new();
        if (BN_set_word(bne, e) != 1)
           break;

        // New up the RSA key
        if (!(rsa_key_pair = RSA_new()))
            break;

        // Create the new public/private EC key pair. EC_key must have a group
        // associated with it before calling this function
        if (RSA_generate_key_ex(rsa_key_pair, bits, bne, NULL) != 1)
            break;

        /*
         * Convert RSA key to EVP_PKEY
         * This function links EVP_PKEY to rsa_key_pair, so when EVP_PKEY is
         *  freed, rsa_key_pair is freed. We don't want the user to have to manage 2
         *  keys, so just return EVP_PKEY and make sure user free's it
         */
        if (EVP_PKEY_assign_RSA(*evp_key_pair, rsa_key_pair) != 1)
            break;

        if (!rsa_key_pair)
            break;

        ret = true;
    } while (0);

    return ret;
}

/**
 * Calculate the complete SHA256/SHA384 digest of the input message.
 * Use for RSA and ECDSA, not ECDH
 * Formerly called CalcHashDigest
 *
 * msg       : message buffer to hash.
 * msg_len   : length of the input message.
 *             - For SEV_CERTs, use PubKeyOffset (number of bytes to be hashed,
 *               from the top of the sev_cert until the first signature.
 *               Version through and including pub_key)
 * digest    : output buffer for the final digest.
 * digest_len: length of the output buffer.
 */
bool digest_sha(const void *msg, size_t msg_len, uint8_t *digest,
                size_t digest_len, SHA_TYPE sha_type)
{
    bool ret = false;

    do {    //TODO 384 vs 512 is all a mess
            /* •在处理SHA-384时，代码使用了SHA512_CTX上下文，这是因为SHA-384和SHA-512都基于SHA-512内部状态机，但它们有不同的初始向量（IV）和输出长度。虽然可以共用相同的上下文结构，但这种做法可能会引起混淆。 */
            /* ECDSA with SHA-384 (curve P-384) 是更推荐的组合；P-384曲线提供了大约192位的安全强度，而SHA-384哈希函数也提供相似级别的安全性（192位）。因此，它们被认为是匹配良好的一对。 */
        if ((sha_type == SHA_TYPE_256 && digest_len != SHA256_DIGEST_LENGTH)/* ||
            (sha_type == SHA_TYPE_384 && digest_len != SHA384_DIGEST_LENGTH)*/)
                break;

        if (sha_type == SHA_TYPE_256) {
            SHA256_CTX context;

            if (SHA256_Init(&context) != 1)
                break;
            if (SHA256_Update(&context, (void *)msg, msg_len) != 1)
                break;
            if (SHA256_Final(digest, &context) != 1)
                break;
        }
        else if (sha_type == SHA_TYPE_384) {
            SHA512_CTX context;

            if (SHA384_Init(&context) != 1)
                break;
            if (SHA384_Update(&context, (void *)msg, msg_len) != 1)
                break;
            if (SHA384_Final(digest, &context) != 1)
                break;
        }

        ret = true;
    } while (0);

    return ret;
}

bool digest_sm3(const void *msg, size_t msg_len, uint8_t *digest,
                size_t digest_len, SHA_TYPE sha_type)
{
    bool ret = false;

    do {    //TODO 384 vs 512 is all a mess
            /* •在处理SHA-384时，代码使用了SHA512_CTX上下文，这是因为SHA-384和SHA-512都基于SHA-512内部状态机，但它们有不同的初始向量（IV）和输出长度。虽然可以共用相同的上下文结构，但这种做法可能会引起混淆。 */
            /* ECDSA with SHA-384 (curve P-384) 是更推荐的组合；P-384曲线提供了大约192位的安全强度，而SHA-384哈希函数也提供相似级别的安全性（192位）。因此，它们被认为是匹配良好的一对。 */
        if ((sha_type == SHA_TYPE_256 && digest_len != SHA256_DIGEST_LENGTH)/* ||
            (sha_type == SHA_TYPE_384 && digest_len != SHA384_DIGEST_LENGTH)*/)
                break;

        if (sha_type == SHA_TYPE_256) {
            SHA256_CTX context;

            if (SHA256_Init(&context) != 1)
                break;
            if (SHA256_Update(&context, (void *)msg, msg_len) != 1)
                break;
            if (SHA256_Final(digest, &context) != 1)
                break;
        }
        else if (sha_type == SHA_TYPE_384) {
            SHA512_CTX context;

            if (SHA384_Init(&context) != 1)
                break;
            if (SHA384_Update(&context, (void *)msg, msg_len) != 1)
                break;
            if (SHA384_Final(digest, &context) != 1)
                break;
        }else if(sha_type == SHA_TYPE_SM3){
            EVP_MD_CTX *md_ctx = EVP_MD_CTX_new();
            if (md_ctx == NULL){
                printf("Error: EVP_MD_CTX_new failed\n");
                break;
            }
                
            const EVP_MD *md = EVP_sm3();
            if(md == NULL || EVP_DigestInit_ex(md_ctx, md, NULL) != 1){
                printf("Error: EVP_sm3() or EVP_DigestInit_ex failed\n");
                break;
            }
            if(EVP_DigestUpdate(md_ctx, msg, msg_len) != 1){
                printf("Error: EVP_DigestUpdate failed\n");
                break;
            }
            unsigned int outlen=0;
            if(EVP_DigestFinal_ex(md_ctx, digest, &outlen) != 1){
                printf("Error: EVP_DigestFinal_ex failed\n");
                break;
            }
            if(outlen != digest_len){
                printf("Error: EVP_DigestFinal_ex returned wrong length\n");
                break;
            }
            /*  Referrence 
                SM3_CTX context;
                if (SM3_Init(&context) != 1)
                    break;
                if (SM3_Update(&context, (void *)msg, msg_len) != 1)
                    break;
                if (SM3_Final(digest, &context) != 1)
                    break;        
            */
        }

        ret = true;
    } while (0);

    return ret;
}

static bool rsa_sign(sev_sig *sig, EVP_PKEY **priv_evp_key, const uint8_t *digest,
                     size_t length, SHA_TYPE sha_type, bool pss)
{
    bool is_valid = false;
    RSA *priv_rsa_key = NULL;
    uint32_t sig_len = 0;

    do {
        // Pull the RSA key from the EVP_PKEY
        priv_rsa_key = EVP_PKEY_get1_RSA(*priv_evp_key);
        if (!priv_rsa_key)
            break;

        if ((size_t)RSA_size(priv_rsa_key) > sizeof(sev_sig::rsa)) {
            printf("rsa_sign buffer too small\n");
            break;
        }

        if (pss) {
            uint8_t encrypted[4096/BITS_PER_BYTE] = {0};
            uint8_t signature[4096/BITS_PER_BYTE] = {0};

            // Memzero all the buffers
            memset(encrypted, 0, sizeof(encrypted));
            memset(signature, 0, sizeof(signature));

            // Compute the pss padded data
            if (RSA_padding_add_PKCS1_PSS(priv_rsa_key, encrypted, digest,
                                         (sha_type == SHA_TYPE_256) ? EVP_sha256() : EVP_sha384(),
                                         -2) != 1) // maximum salt length
            {
                break;
            }

            // Perform digital signature
            if (RSA_private_encrypt(sizeof(encrypted), encrypted, signature, priv_rsa_key, RSA_NO_PADDING) == -1)
                break;

            // Swap the bytes of the signature
            if (!sev::reverse_bytes(signature, 4096/BITS_PER_BYTE))
                break;
            memcpy(sig->rsa.s, signature, 4096/BITS_PER_BYTE);
        }
        else {
            if (RSA_sign((sha_type == SHA_TYPE_256) ? NID_sha256 : NID_sha384, digest,
                        (uint32_t)length, (uint8_t *)&sig->rsa, &sig_len, priv_rsa_key) != 1)
                break;
        }

        if (sig_len > sizeof(sev_sig::rsa)) {
            printf("rsa_sign buffer too small\n");
            break;
        }

        is_valid = true;
    } while (0);

    // Free memory
    // RSA_free(priv_rsa_key);

    return is_valid;
}

/**
 * rsa_pss_verify
 */
static bool rsa_verify(sev_sig *sig, EVP_PKEY **evp_pub_key, const uint8_t *sha_digest,
                       size_t sha_length, SHA_TYPE sha_type, bool pss)
{
    bool is_valid = false;
    RSA *rsa_pub_key = NULL;
    uint32_t sig_len = 0;

    do {
        // Pull the RSA key from the EVP_PKEY
        rsa_pub_key = EVP_PKEY_get1_RSA(*evp_pub_key);
        if (!rsa_pub_key)
            break;

        sig_len = RSA_size(rsa_pub_key);

        if (pss) {
            uint8_t decrypted[4096/BITS_PER_BYTE] = {0}; // TODO wrong length
            uint8_t signature[4096/BITS_PER_BYTE] = {0};

            // Memzero all the buffers
            memset(decrypted, 0, sizeof(decrypted));
            memset(signature, 0, sizeof(signature));

            // Swap the bytes of the signature
            memcpy(signature, sig->rsa.s, 4096/BITS_PER_BYTE);
            if (!sev::reverse_bytes(signature, 4096/BITS_PER_BYTE))
                break;

            // Now we will verify the signature. Start by a RAW decrypt of the signature
            if (RSA_public_decrypt(sig_len, signature, decrypted, rsa_pub_key, RSA_NO_PADDING) == -1)
                break;

            // Verify the data
            // SLen of -2 means salt length is recovered from the signature
            if (RSA_verify_PKCS1_PSS(rsa_pub_key, sha_digest,
                                     (sha_type == SHA_TYPE_256) ? EVP_sha256() : EVP_sha384(),
                                     decrypted, -2) != 1)
            {
                printf("Error: rsa_verify with pss Failed\n");
                break;
            }
        }
        else {
            // Verify the data
            if (RSA_verify((sha_type == SHA_TYPE_256) ? NID_sha256 : NID_sha384,
                            sha_digest, (uint32_t)sha_length, sig->rsa.s, sig_len, rsa_pub_key) != 1)
            {
                printf("Error: rsa_verify without pss Failed\n");
                break;
            }
        }

        is_valid = true;
    } while (0);

    // Free the keys and contexts
    // if (rsa_pub_key)
    //     RSA_free(rsa_pub_key);

    // if (md_ctx)
    //     EVP_MD_CTX_free(md_ctx);

    return is_valid;
}

/**
 * Call sign_verify_message and it will call this
 */
static bool ecdsa_sign(sev_sig *sig, EVP_PKEY **priv_evp_key,
                       const uint8_t *digest, size_t length)
{
    bool is_valid = false;
    EC_KEY *priv_ec_key = NULL;
    const BIGNUM *r = NULL;
    const BIGNUM *s = NULL;
    ECDSA_SIG *ecdsa_sig = NULL;

    do {
        priv_ec_key = EVP_PKEY_get1_EC_KEY(*priv_evp_key);
        if (!priv_ec_key)
            break;

        ecdsa_sig = ECDSA_do_sign(digest, (uint32_t)length, priv_ec_key); // Contains 2 bignums
        if (!ecdsa_sig)
            break;

        // Extract the bignums from ecdsa_sig and store the signature in sig
        ECDSA_SIG_get0(ecdsa_sig, &r, &s);
        BN_bn2lebinpad(r, sig->ecdsa.r, sizeof(sev_ecdsa_sig::r));    // LE to BE
        BN_bn2lebinpad(s, sig->ecdsa.s, sizeof(sev_ecdsa_sig::s));

        ECDSA_SIG_free(ecdsa_sig);

        is_valid = true;
    } while (0);

    // Free memory
    EC_KEY_free(priv_ec_key);

    return is_valid;
}

EVP_PKEY *adjust_sm2_key(const EVP_PKEY *ori_priv_evp_key) {
    if (!ori_priv_evp_key || EVP_PKEY_base_id(ori_priv_evp_key) != EVP_PKEY_SM2) {
        fprintf(stderr, "Invalid input: EVP_PKEY is NULL or not an SM2 key.\n");
        return NULL;
    }

    EVP_PKEY *new_evp_key = NULL;
    //typedef struct ec_key_st EC_KEY;
    // EC_KEY *ecc_key = (EC_KEY*)EVP_PKEY_get0_EC_KEY(ori_priv_evp_key);
    const EC_KEY *ecc_key_const = EVP_PKEY_get0_EC_KEY(ori_priv_evp_key);
    if (!ecc_key_const) {
        fprintf(stderr, "Failed to extract EC_KEY from EVP_PKEY.\n");
        return NULL;
    }
    EC_KEY *ecc_key_copy = EC_KEY_dup(ecc_key_const);

    // 提取私钥和公钥
    const BIGNUM *priv_key = EC_KEY_get0_private_key(ecc_key_copy);
    const EC_POINT *pub_key = EC_KEY_get0_public_key(ecc_key_copy);

    if (!priv_key || !pub_key) {
        fprintf(stderr, "Failed to extract private or public key from EC_KEY.\n");
        return NULL;
    }

    // 创建新的 EC_KEY
    EC_KEY *new_ec_key = EC_KEY_new_by_curve_name(NID_sm2);
    if (!new_ec_key) {
        fprintf(stderr, "Failed to create new EC_KEY for SM2.\n");
        return NULL;
    }

    // 设置私钥和公钥
    if (EC_KEY_set_private_key(new_ec_key, priv_key) != 1 ||
        EC_KEY_set_public_key(new_ec_key, pub_key) != 1) {
        fprintf(stderr, "Failed to set private or public key for new EC_KEY.\n");
        EC_KEY_free(new_ec_key);
        return NULL;
    }

    // 创建新的 EVP_PKEY
    new_evp_key = EVP_PKEY_new();
    if (!new_evp_key || EVP_PKEY_assign_EC_KEY(new_evp_key, new_ec_key) != 1) {
        fprintf(stderr, "Failed to create or assign new EVP_PKEY.\n");
        EC_KEY_free(new_ec_key);
        if (new_evp_key) EVP_PKEY_free(new_evp_key);
        return NULL;
    }

    /**
     * OpenSSL 3.x 会默认附加 `ASN1_OID`，无需手动处理。
     * 如果需要低级修改，可以通过 OpenSSL 的 `ASN1` 构造器实现。
     */

    return new_evp_key;
}

/* digest ptr to unhased contend */
/* 在签名函数中，他们使用了EVP_DigestSign系列函数生成签名，然后将DER格式的签名转换为ECDSA_SIG结构，提取r和s，存储到sig结构体中。验证时，他们又从sig中读取r和s，重新构造ECDSA_SIG，再转换成DER格式进行验证 */

static bool sm2sa_sign(sev_sig *sig, EVP_PKEY **priv_evp_key,
                       const uint8_t *msg, size_t length, const uint8_t * user_id, size_t user_id_len){
    bool is_valid = false;
    // EC_KEY *priv_ec_key = NULL;
    EVP_MD_CTX *mdctx = NULL;
    uint8_t *signature = NULL;
    uint8_t *signature_ptr = NULL;
    EVP_PKEY_CTX *pctx = NULL;

    const BIGNUM *r = NULL;
    const BIGNUM *s = NULL;
    ECDSA_SIG *sm2_sig = NULL;
    size_t sig_len;

    do {
        // We use id-ecPublicKey, not SM2
        // if(EVP_PKEY_id(*priv_evp_key) != EVP_PKEY_SM2){
        //     printf("Error: EVP_PKEY_id failed\n");
        //     break;
        // }

        EVP_MD_CTX *md_ctx = EVP_MD_CTX_new();
        if (md_ctx == NULL) {
            printf("Error: EVP_MD_CTX_new failed\n");
            ERR_print_errors_fp(stderr);
            return false;
        }

        if (EVP_DigestSignInit(md_ctx, NULL, EVP_sm3(), NULL, *priv_evp_key) <= 0) {
            printf("Error: EVP_DigestSignInit failed\n");
            ERR_print_errors_fp(stderr);
            EVP_MD_CTX_free(md_ctx);
            return false;
        }

        // 设置用户ID
        if (EVP_PKEY_CTX_set1_id(EVP_MD_CTX_get_pkey_ctx(md_ctx), user_id, user_id_len) <= 0) {
            printf("Error: EVP_PKEY_CTX_set1_id failed\n");
            ERR_print_errors_fp(stderr);
            EVP_MD_CTX_free(md_ctx);
            return false;
        }

        // 计算签名所需的空间大小
        if (EVP_DigestSign(md_ctx, NULL, &sig_len, msg, length) <= 0) {
            printf("Error: EVP_DigestSign failed\n");
            ERR_print_errors_fp(stderr);
            EVP_MD_CTX_free(md_ctx);
            return false;
        }

        // 分配空间并计算签名
        signature = (uint8_t *)OPENSSL_malloc(sig_len);
        
        if (signature == NULL || EVP_DigestSign(md_ctx, signature, &sig_len, msg, length) <= 0) {
            printf("Error: EVP_DigestSign failed\n");
            ERR_print_errors_fp(stderr);
            OPENSSL_free(signature);
            signature = NULL;
            EVP_MD_CTX_free(md_ctx);
            return false;
        }
        printf("Generate signature successfully\n");
        EVP_MD_CTX_free(md_ctx);

        //trans Der-encoded signature to ECDSA_SIG
        signature_ptr =signature;
        sm2_sig = d2i_ECDSA_SIG(NULL, (const unsigned char**)&signature_ptr, sig_len);
        if(!sm2_sig){
            printf("Error: d2i_ECDSA_SIG failed\n");
            //避免重复释放
            // EVP_MD_CTX_free(mdctx);
            // OPENSSL_free(signature); 
            break;
        }
        // Extract the bignums from sm2_sig and store the signature in sig
        ECDSA_SIG_get0(sm2_sig, &r, &s);
        if (!BN_bn2lebinpad(r, sig->ecdsa.r, sizeof(sig->ecdsa.r)) ||
            !BN_bn2lebinpad(s, sig->ecdsa.s, sizeof(sig->ecdsa.s))) {
            printf("Error: BN_bn2binpad failed\n");
            break;
        }
        // BN_bn2lebinpad(r, sig->ecdsa.r, sizeof(sev_ecdsa_sig::r));    // BigNum to Binary in Little Endian
        // BN_bn2lebinpad(s, sig->ecdsa.s, sizeof(sev_ecdsa_sig::s));
        
        printf("Genetete cert signature successfully\n");
        is_valid = true;
    } while (0);

    // Free memory
    ECDSA_SIG_free(sm2_sig);
    OPENSSL_free(signature);//check point: the signaure (r,s) are copied to sig->ecdsa.r and sig->ecdsa.s
    EVP_MD_CTX_free(mdctx);
    //free mdctx的时候，会释放自动关联的pctx
    // EVP_PKEY_CTX_free(pctx);
    // EC_KEY_free(priv_ec_key);

    return is_valid;
}

//bakin 09.02.2025
// static bool sm2sa_sign(sev_sig *sig, EVP_PKEY **priv_evp_key,
//                        const uint8_t *msg, size_t length, const uint8_t * user_id, size_t user_id_len){
//     bool is_valid = false;
//     // EC_KEY *priv_ec_key = NULL;
//     EVP_MD_CTX *mdctx = NULL;
//     uint8_t *signature = NULL;
//     uint8_t *signature_ptr = NULL;
//     EVP_PKEY_CTX *pctx = NULL;

//     const BIGNUM *r = NULL;
//     const BIGNUM *s = NULL;
//     ECDSA_SIG *sm2_sig = NULL;
//     size_t sig_len;

//     do {
//         // We use id-ecPublicKey, not SM2
//         // if(EVP_PKEY_id(*priv_evp_key) != EVP_PKEY_SM2){
//         //     printf("Error: EVP_PKEY_id failed\n");
//         //     break;
//         // }

//         // create a new EVP_MD_CTX
//         mdctx = EVP_MD_CTX_new();
//         if(!mdctx){
//             printf("Error: EVP_MD_CTX_new failed\n");
//             break;
//         }

//         // start sign process, set sm3 as the digest algorithm
//         const EVP_MD *sm3_md = EVP_sm3();
//         if(!sm3_md){
//             printf("Error: EVP_sm3 failed\n");
//             break;
//         }
//         if(EVP_DigestSignInit(mdctx, &pctx, sm3_md, NULL, *priv_evp_key) != 1){
//             printf("Error: EVP_DigestSignInit failed\n");
//             break;
//         }
//         // set context
//         if(!pctx){
//             printf("Error: get pctx in EVP_DigestSignInit failed\n");
//             break;
//         }
//         if(EVP_PKEY_CTX_set1_id(pctx, user_id, user_id_len)!=1){
//             printf("Error: EVP_PKEY_CTX_set1_id failed\n");
//             break;
//         }
        
//         if(EVP_DigestSignUpdate(mdctx, msg, length) != 1){
//             printf("Error: EVP_DigestSignUpdate failed\n");
//             break;
//         }
//         // get the length of signature
//         if(EVP_DigestSignFinal(mdctx, NULL, &sig_len) != 1){
//             printf("Error: EVP_DigestSignFinal failed\n");
//             break;
//         }
//         // allocate memory for signature
//         signature = (uint8_t *)OPENSSL_malloc(sig_len);
//         if(!signature){
//             printf("Error: OPENSSL_malloc failed\n");
//             break;
//         }
//         // store signature in val'signature', in DER format
//         if(EVP_DigestSignFinal(mdctx, signature, &sig_len) != 1){
//             printf("Error: EVP_DigestFinal failed\n");
//             break;
//         }

//         //trans Der-encoded signature to ECDSA_SIG
//         signature_ptr =signature;
//         sm2_sig = d2i_ECDSA_SIG(NULL, (const unsigned char**)&signature_ptr, sig_len);
//         if(!sm2_sig){
//             printf("Error: d2i_ECDSA_SIG failed\n");
//             //避免重复释放
//             // EVP_MD_CTX_free(mdctx);
//             // OPENSSL_free(signature); 
//             break;
//         }
//         // Extract the bignums from sm2_sig and store the signature in sig
//         ECDSA_SIG_get0(sm2_sig, &r, &s);
//         if (!BN_bn2lebinpad(r, sig->ecdsa.r, sizeof(sig->ecdsa.r)) ||
//             !BN_bn2lebinpad(s, sig->ecdsa.s, sizeof(sig->ecdsa.s))) {
//             printf("Error: BN_bn2binpad failed\n");
//             break;
//         }
//         // BN_bn2lebinpad(r, sig->ecdsa.r, sizeof(sev_ecdsa_sig::r));    // BigNum to Binary in Little Endian
//         // BN_bn2lebinpad(s, sig->ecdsa.s, sizeof(sev_ecdsa_sig::s));

//         is_valid = true;
//     } while (0);

//     // Free memory
//     ECDSA_SIG_free(sm2_sig);
//     OPENSSL_free(signature);//check point: the signaure (r,s) are copied to sig->ecdsa.r and sig->ecdsa.s
//     EVP_MD_CTX_free(mdctx);
//     //free mdctx的时候，会释放自动关联的pctx
//     // EVP_PKEY_CTX_free(pctx);
//     // EC_KEY_free(priv_ec_key);

//     return is_valid;
// }


/**
 * It would be easier if we could just pass in the populated ECDSA_SIG from
 *  ecdsa_sign instead of using sev_sig to BigNums as the intermediary, but we
 *  do need to ecdsa_verify to verify something signed by firmware, so we
 *  wouldn't have the ECDSA_SIG
 */
bool ecdsa_verify(sev_sig *sig, EVP_PKEY **pub_evp_key, uint8_t *digest, size_t length)
{
    bool is_valid = false;
    EC_KEY *pub_ec_key = NULL;
    BIGNUM *r = NULL;
    BIGNUM *s = NULL;
    ECDSA_SIG *ecdsa_sig = NULL;

    do {
        pub_ec_key = EVP_PKEY_get1_EC_KEY(*pub_evp_key);
        if (!pub_ec_key)
            break;

        // Store the x and y components as separate BIGNUM objects. The values in the
        // SEV certificate are little-endian, must reverse bytes before storing in BIGNUM
        r = BN_lebin2bn(sig->ecdsa.r, sizeof(sig->ecdsa.r), NULL);  // New's up BigNum
        s = BN_lebin2bn(sig->ecdsa.s, sizeof(sig->ecdsa.s), NULL);

        // Create a ecdsa_sig from the bignums and store in sig
        ecdsa_sig = ECDSA_SIG_new();
        ECDSA_SIG_set0(ecdsa_sig, r, s);

        // Validation will also be done by the FW
        if (ECDSA_do_verify(digest, (uint32_t)length, ecdsa_sig, pub_ec_key) != 1) {
            ECDSA_SIG_free(ecdsa_sig);
            break;
        }
        ECDSA_SIG_free(ecdsa_sig);

        is_valid = true;
    } while (0);

    // Free memory
    EC_KEY_free(pub_ec_key);

    return is_valid;
}

bool sm2sa_verify(sev_sig *sig, EVP_PKEY **pub_evp_key, const uint8_t *msg, size_t length, const uint8_t *user_id, size_t user_id_len)
{
    bool is_valid = false;
    EVP_MD_CTX *mdctx = NULL;
    EVP_PKEY_CTX *pctx = NULL;
    unsigned char *sig_der = NULL;
    int sig_der_len;
    ECDSA_SIG *ecdsa_sig = NULL;
    BIGNUM *r = NULL;
    BIGNUM *s = NULL;

    do{
        // create a new EVP_MD_CTX
        mdctx = EVP_MD_CTX_new();
        if (!mdctx){
            printf("Error: EVP_MD_CTX_new failed\n");
            break;
        }   

        // initialize the verification context
        if (EVP_DigestVerifyInit(mdctx, &pctx, EVP_sm3(), NULL, *pub_evp_key) <= 0){
            printf("Error: EVP_DigestVerifyInit failed\n");
            break;
        }

        if (!pctx){
            printf("Error: EVP_DigestVerifyInit failed\n");
            break;
        }

        // set user ID
        if (EVP_PKEY_CTX_set1_id(pctx, user_id, user_id_len) <= 0){
            printf("Error: EVP_PKEY_CTX_set1_id failed\n");
            break;
        }
            
        // update ctx and raw msg
        if (EVP_DigestVerifyUpdate(mdctx, msg, length) <= 0){
            printf("Error: EVP_DigestVerifyUpdate failed\n");
            break;
        }

        // extrac signature from sig, then turn into ECDSA_SIG and further turn into  DER format
        r = BN_lebin2bn(sig->ecdsa.r, sizeof(sig->ecdsa.r),NULL);
        s = BN_lebin2bn(sig->ecdsa.s, sizeof(sig->ecdsa.s),NULL);  
        ecdsa_sig = ECDSA_SIG_new();
        ECDSA_SIG_set0(ecdsa_sig, r, s);
        sig_der_len = i2d_ECDSA_SIG(ecdsa_sig, &sig_der);
        if (sig_der_len <= 0){
            printf("Error: i2d_ECDSA_SIG failed\n");
            break;
        }

        // verify the signature
        if (EVP_DigestVerifyFinal(mdctx, sig_der, (size_t)sig_der_len) <= 0){
            printf("Error: EVP_DigestVerifyFinal failed\n");
            break;
        }

        is_valid = true; // 验证成功

    }while(0);

        // free resources
    OPENSSL_free(sig_der);
    EVP_MD_CTX_free(mdctx);
    // EVP_PKEY_CTX_free(pctx);

    return is_valid;
}
/**
 * A generic sign function that takes a byte array (not specifically an sev_cert)
 *  and signs it using an sev_sig
 *
 * Note that verify always happens, even after a sign operation, just to make
 *  sure the sign worked correctly
 */
static bool sign_verify_message(sev_sig *sig, EVP_PKEY **evp_key_pair, const uint8_t *msg,
                                size_t length, const SEV_SIG_ALGO algo, bool sign)
{
    bool is_valid = false;
    hmac_sha_256 sha_digest_256;   // Hash on the cert from Version to PubKey
    hmac_sha_512 sha_digest_384;   // Hash on the cert from Version to PubKey
    SHA_TYPE sha_type;
    uint8_t *sha_digest = NULL;
    size_t sha_length;
    const bool pss = true;

    do {
        // Determine if SHA_TYPE is 256 bit or 384 bit
        if (algo == SEV_SIG_ALGO_RSA_SHA256 || algo == SEV_SIG_ALGO_ECDSA_SHA256 ||
            algo == SEV_SIG_ALGO_ECDH_SHA256)
        {
            sha_type = SHA_TYPE_256;
            sha_digest = sha_digest_256;
            sha_length = sizeof(hmac_sha_256);
        }
        else if (algo == SEV_SIG_ALGO_RSA_SHA384 || algo == SEV_SIG_ALGO_ECDSA_SHA384 ||
                 algo == SEV_SIG_ALGO_ECDH_SHA384)
        {
            sha_type = SHA_TYPE_384;
            sha_digest = sha_digest_384;
            sha_length = sizeof(hmac_sha_512);
        }
        else
        {
            break;
        }
        memset(sha_digest, 0, sha_length);

        // Calculate the hash digest
        if (!digest_sha(msg, length, sha_digest, sha_length, sha_type))
            break;

        if ((algo == SEV_SIG_ALGO_RSA_SHA256) || (algo == SEV_SIG_ALGO_RSA_SHA384)) {
            if (sign && !rsa_sign(sig, evp_key_pair, sha_digest, sha_length, sha_type, pss))
                break;
            if (!rsa_verify(sig, evp_key_pair, sha_digest, sha_length, sha_type, pss))
                break;
        }
        else if ((algo == SEV_SIG_ALGO_ECDSA_SHA256) || (algo == SEV_SIG_ALGO_ECDSA_SHA384)) {
            if (sign && !ecdsa_sign(sig, evp_key_pair, sha_digest, sha_length))
                break;
            if (!ecdsa_verify(sig, evp_key_pair, sha_digest, sha_length))
                break;
        }
        else if ((algo == SEV_SIG_ALGO_ECDH_SHA256) || (algo == SEV_SIG_ALGO_ECDH_SHA384)) {
            printf("Error: ECDH signing unsupported");
            break;                       // Error unsupported
        }
        else {
            printf("Error: invalid signing algo. Can't sign");
            break;                          // Invalid params
        }

        is_valid = true;
    } while (0);

    return is_valid;
}

/* Extend the origin function: sign_verify_message to support SM2 algo in Hygon/CSV */
/* evp_key_pair 可能是公钥可能是私钥； */
/* sign: true = sign; false = verify */
static bool sign_verify_message_csv(sev_sig *sig, EVP_PKEY **evp_key_pair, const uint8_t *msg,
                                size_t length, const uint8_t *user_id,size_t user_id_len, const SEV_SIG_ALGO algo, bool sign)
{
    bool is_valid = false;
    hmac_sha_256 sha_digest_256;   // Hash on the cert from Version to PubKey
    hmac_sha_512 sha_digest_384;   // Hash on the cert from Version to PubKey
    SHA_TYPE sha_type;
    uint8_t *sha_digest = NULL;
    size_t sha_length;
    const bool pss = true;

    do {
        // Determine if SHA_TYPE is 256 bit or 384 bit
        if (algo == SEV_SIG_ALGO_RSA_SHA256 || algo == SEV_SIG_ALGO_ECDSA_SHA256 ||
            algo == SEV_SIG_ALGO_ECDH_SHA256)
        {
            sha_type = SHA_TYPE_256;
            sha_digest = sha_digest_256;
            sha_length = sizeof(hmac_sha_256);
        }
        else if (algo == SEV_SIG_ALGO_RSA_SHA384 || algo == SEV_SIG_ALGO_ECDSA_SHA384 ||
                 algo == SEV_SIG_ALGO_ECDH_SHA384)
        {
            sha_type = SHA_TYPE_384;
            sha_digest = sha_digest_384;
            sha_length = sizeof(hmac_sha_512);
        }
        else if (algo == SIG_ALGO_TYPE_SM2_SA) 
        {
            sha_type = SHA_TYPE_SM3;
            sha_digest = sha_digest_256;
            sha_length = sizeof(hmac_sha_256);
        }
        else
        {
            break;
        }
     //直接用openssl 3的新方法，使用EVP的高级API

        //  memset(sha_digest, 0, sha_length);

        // Don't calculate the hash digest in advance 
        // Calculate the hash digest using SM3
        // if (!digest_sm3(msg, length, sha_digest, sha_length, sha_type))
        //     break;

        if(algo == SIG_ALGO_TYPE_SM2_SA){
            if(sign && !sm2sa_sign(sig, evp_key_pair, msg, length,user_id,user_id_len))
                break;
            if(!sm2sa_verify(sig, evp_key_pair, msg, length,user_id,user_id_len)) //sm2sa_verify 还没实现
                break;
        }
        else {
            printf("Error: invalid signing algo. Can't sign");
            break;                          // Invalid params
        }


        is_valid = true;
    } while (0);

    return is_valid;
}

bool sign_message(sev_sig *sig, EVP_PKEY **evp_key_pair, const uint8_t *msg,
                 size_t length, const SEV_SIG_ALGO algo)
{
    return sign_verify_message(sig, evp_key_pair, msg, length, algo, true);
}

bool verify_message(sev_sig *sig, EVP_PKEY **evp_key_pair, const uint8_t *msg,
                    size_t length, const SEV_SIG_ALGO algo)
{
    return sign_verify_message(sig, evp_key_pair, msg, length, algo, false);
}

bool sign_message_csv(sev_sig *sig, EVP_PKEY **evp_key_pair, const uint8_t *msg,
                 size_t length, const uint8_t * user_id, size_t user_id_len,const SEV_SIG_ALGO algo)
{
    return sign_verify_message_csv(sig, evp_key_pair, msg, length, user_id,user_id_len, algo, true);
}

bool verify_message_csv(sev_sig *sig, EVP_PKEY **evp_key_pair, const uint8_t *msg,
                    size_t length, const uint8_t * user_id, size_t user_id_len, const SEV_SIG_ALGO algo)
{
    return sign_verify_message_csv(sig, evp_key_pair, msg,length, user_id,user_id_len,algo, false);
}

/**
 * p_key = K param in spec = The guest's VMPCK identified by MSG_VMPCK
 * p_aad = A in the spec. is the metadata 0x30h to 0x5F of the request message
 * p_msg = P in spec = PAYLOAD plaintext
 * p_out = output cyphertext
 * p_tag = T = AUTHTAG in spec
 * p_iv = iv in spec = bits 95:0 of the iv
 */
SEV_ERROR_CODE aes_256_gcm_authenticated_encrypt(const uint8_t *p_key, size_t key_size,
                                                 const uint8_t *p_aad, size_t aad_size,
                                                 const uint8_t *p_msg, size_t msg_size,
                                                 uint8_t *p_out, const uint8_t *p_iv,
                                                 size_t iv_size,
                                                 uint8_t *p_tag) // [out, 16 bytes]
{
    SEV_ERROR_CODE cmd_ret = ERROR_INVALID_PARAM;
    const int tag_len = 16; // 16 bytes
    int out_len = 0;
    int tmp_len = 0;

    do {
        if (!p_key || !p_msg || !p_out || !p_iv || !p_tag || (aad_size && !p_aad))
            break;

        if (key_size != 32 || msg_size == 0 || (msg_size & 15) != 0 ||
            /*aad_size > sizeof(aligned_aad) ||*/ iv_size < 8 || iv_size > 16)
            break;

        EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();

        // Set the cipher and context only
        if (!EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL))
            break;

        // Sets the IV length: Can only be called before specifying an IV [Optional for GCM]
        if (!EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, (int)iv_size, NULL))
            break;

        // Now initialize the context with key and IV
        if (!EVP_EncryptInit_ex(ctx, NULL, NULL, p_key, p_iv))
            break;

        // Set the key length
        if (!EVP_CIPHER_CTX_set_key_length(ctx, (int)key_size))
            break;
        OPENSSL_assert(EVP_CIPHER_CTX_key_length(ctx) == (int)key_size);
        OPENSSL_assert(EVP_CIPHER_CTX_iv_length(ctx) == (int)iv_size);
        // printf("blocksize %i\n", EVP_CIPHER_CTX_block_size(ctx));

        /*
         * To specify any additional authenticated data (AAD) a call to EVP_CipherUpdate(),
         * EVP_EncryptUpdate() or EVP_DecryptUpdate() should be made with the output parameter
         * out set to NULL
         */
        // Add Additional associated data (AAD) [Optional for GCM]
        if (!EVP_EncryptUpdate(ctx, NULL, &out_len, p_aad, (int)aad_size))
            break;
        // Now encrypt the data
        if (!EVP_EncryptUpdate(ctx, p_out, &out_len, p_msg, (int)msg_size))
            break;

        /*
         * Buffer passed to EVP_EncryptFinal() must be after the data that we
         * just encrypted to avoid overwriting it
         */
        if (!EVP_EncryptFinal_ex(ctx, p_out + out_len, &tmp_len))
            break;
        out_len += tmp_len;

        /*
         * Writes taglen bytes of the tag value to the buffer indicated by tag.
         * This call can only be made when encrypting data and after all data has
         * been processed (e.g. after an EVP_EncryptFinal()
         */
        // Append authentication tag at the end
        if (!EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, tag_len, p_tag))
            break;

        EVP_CIPHER_CTX_free(ctx);

        cmd_ret = STATUS_SUCCESS;
    } while (0);

    return cmd_ret;
}

/**
 * p_key = K param in spec = The guest's VMPCK identified by MSG_VMPCK
 * p_aad = A in the spec. is the metadata 0x30h to 0x5F of the request message
 * p_msg = C in spec = PAYLOAD
 * p_out = output cyphertext
 * p_tag = T = AUTHTAG in spec
 * p_iv = iv in spec
 */
SEV_ERROR_CODE aes_256_gcm_authenticated_decrypt(const uint8_t *p_key, size_t key_size,
                                                 const uint8_t *p_aad, size_t aad_size,
                                                 const uint8_t *p_msg, size_t msg_size,
                                                 uint8_t *p_out, const uint8_t *p_iv,
                                                 size_t iv_size,
                                                 const uint8_t *p_tag) // [in, 16 bytes]
{
    SEV_ERROR_CODE cmd_ret = ERROR_INVALID_PARAM;
    const int tag_len = 16; // 16 bytes
    int out_len = 0;
    int tmp_len = 0;

    do {
        if (!p_key || !p_msg || !p_out || !p_iv || !p_tag || (aad_size && !p_aad))
            break;

        if (key_size != 32 || msg_size == 0 || (msg_size & 15) != 0 ||
            /*aad_size > sizeof(aligned_aad) ||*/ iv_size < 8 || iv_size > 16)
            break;

        EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();

        // Set the cipher and context only.
        if (!EVP_DecryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL))
            break;

        EVP_CIPHER_CTX_set_padding(ctx, 0);

        // Sets the IV length: Can only be called before specifying an IV [Optional for GCM]
        if (!EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, (int)iv_size, NULL))
            break;

        // Set Tag from the data
        if (!EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_TAG, tag_len, (uint8_t *)p_tag))
            break;

        // Now initialize the context with key and IV
        if (!EVP_DecryptInit_ex(ctx, NULL, NULL, p_key, p_iv))
            break;

        // Set the key length
        if (!EVP_CIPHER_CTX_set_key_length(ctx, (int)key_size))
            break;
        OPENSSL_assert(EVP_CIPHER_CTX_key_length(ctx) == (int)key_size);
        OPENSSL_assert(EVP_CIPHER_CTX_iv_length(ctx) == (int)iv_size);
        // printf("blocksize %i\n", EVP_CIPHER_CTX_block_size(ctx));

        /*
         * To specify any additional authenticated data (AAD) a call to EVP_CipherUpdate(),
         * EVP_EncryptUpdate() or EVP_DecryptUpdate() should be made with the output parameter
         * out set to NULL
         */
        // Add Additional associated data (AAD) [Optional for GCM]
        if (!EVP_DecryptUpdate(ctx, NULL, &tmp_len, p_aad, (int)aad_size))
            break;
        out_len += tmp_len;
        // Now decrypt the data
        if (!EVP_DecryptUpdate(ctx, p_out, &tmp_len, p_msg, (int)msg_size))
            break;
        out_len += tmp_len;

        /*
         * Buffer passed to EVP_DecryptFinal() must be after the data that we
         * just encrypted to avoid overwriting it
         */
        if (!EVP_DecryptFinal_ex(ctx, p_out + out_len, &tmp_len))
            //break;    //TODO
        out_len += tmp_len;

        EVP_CIPHER_CTX_free(ctx);

        cmd_ret = STATUS_SUCCESS;
    } while (0);

    return cmd_ret;
}
