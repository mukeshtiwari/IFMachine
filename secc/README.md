# SecC

A prototype program verification tool for proving information flow security
of C code.

## Requirements

* Java 8
* Z3 (tested with various versions >= 4.4.0) 

## Supported Platforms

* Linux (tested with Ubuntu 16.04 and 18.04)
* Mac OS (tested with 10.13 and 10.14)

## Installation

### Java 8

First check that Java 8 is installed. Run `java -version` and look for
a version number that begins with `1.8`.

### Z3

Either by distribution package (e.g. `sudo apt-get install z3`) or by
downloading a binary release from: https://github.com/Z3Prover/z3/releases

Once installed, make sure the `z3` binary is in your `PATH`.

## Building SecC

SecC should build by simply typing `make` in the top-level directory.

```
make
```

This should produce a shell script `SecC.sh` for running SecC.

## Running SecC

Simply run `SecC.sh`, supplying a list of files to analyse as command line
arguments.

```
./SecC.sh file1.c file2.c ...
```





