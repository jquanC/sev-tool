# The name of the resulting application after it is build.
bin_PROGRAMS = mysevtool

mysevtool_SOURCES = amdcert.cpp commands.cpp crypto.cpp\
				  main.cpp sevcert.cpp\
				  utilities.cpp tests.cpp x509cert.cpp
if LINUX
mysevtool_SOURCES += sevcore_linux.cpp
else
mysevtool_SOURCES += sevcore_win.cpp
endif

# linked libraries
mysevtool_LDADD = -lcrypto -lssl -luuid

# Compilation flags
mysevtool_CXXFLAGS = -g -Wall -Wextra -Wconversion -pthread -std=c++11 -I../lib
