# The name of the resulting application after it is build.
bin_PROGRAMS = sevtooldev

sevtooldev_SOURCES = amdcert.cpp commands.cpp crypto.cpp\
				  main.cpp sevcert.cpp\
				  utilities.cpp tests.cpp x509cert.cpp
if LINUX
sevtooldev_SOURCES += sevcore_linux.cpp
else
sevtooldev_SOURCES += sevcore_win.cpp
endif

# linked libraries
sevtooldev_LDADD = -lcrypto -lssl -luuid

# Compilation flags
sevtooldev_CXXFLAGS = -g -Wall -Wextra -Wconversion -pthread -std=c++11 -I../lib
