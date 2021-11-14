.PHONY: all test clean mrproper parser check-dependencies

MILL = ./mill --no-server

SECC_EXAMPLES = examples

VPATH     	= $(SECC_EXAMPLES)
SECC_C    	= $(wildcard $(SECC_EXAMPLES)/*.c)
SECC_OBJ  	= $(SECC_C:$(SECC_EXAMPLES)/%.c=obj/%.o)
SECC_JAVA 	= secc/src/secc/c/Parser.java \
              secc/src/secc/c/Scanner.java
SECC_SCALA	= $(shell find secc/src -iname "*.scala")

CC ?= cc
CFLAGS ?= -Iinclude -Wall -W -Wpedantic -g

BEAVER = ./beaver
JFLEX  = ./jflex

SECC_JAR = out/secc/jar/dest/out.jar

SECC_LAUNCHER = out/secc/launcher/dest/run
SECC_SH  = ./SecC.sh

all: $(SECC_JAR) $(SECC_SH)

parser: $(SECC_JAVA)

test:
	$(MILL) secc.test

clean:
	$(MILL) clean
	rm -f $(SECC_SH)

mrproper: clean
	rm -f $(SECC_JAVA)

check-dependencies:
	$(MILL) mill.scalalib.Dependency/updates

$(SECC_LAUNCHER):
	@echo $@
	$(MILL) secc.launcher

$(SECC_JAR): $(SECC_JAVA) $(SECC_SCALA)
	@echo $@
	$(MILL) secc.jar

$(SECC_SH): $(SECC_LAUNCHER)
	@echo "[echo]  $@"
	@echo "#!/usr/bin/env bash" > $@
	@echo "export LD_LIBRARY_PATH=$(PWD)/secc/lib" >> $@
	@echo "export PATH=.:\$$PATH" >> $@
	@echo "source $(PWD)/$(SECC_LAUNCHER)" >> $@
	@echo "[chmod] $@"; chmod +x $@

%.java: %.grammar
	$(BEAVER) -t $^

%.java: %.flex
	$(JFLEX) -nobak $^

o: $(SECC_OBJ)
	@echo $(SECC_OBJ)

CFLAGS ?= -W -Wall -Wpedantic

# Note compilation produces (only) unused variable warnings
auction.o: examples/case-studies/auction.c
	$(CC) $(CFLAGS) $^ -c -o $@

auction-main.o: examples/auction-main.c
	$(CC) $(CFLAGS) $^ -c -o $@

auction-main: auction-main.o auction.o
	$(CC) $(CFLAGS) $(LDFLAGS) -pthread $^ -o $@

client-fed-learn.o: examples/federated_learning/client_fed_learn.c
	$(CC) $(CFLAGS) $^ -c -o $@

client-fed-main.o: examples/federated_learning/drive_fed_client.c
	$(CC) $(CFLAGS) $^ -c -o $@

client-fed-main: client-fed-main.o client-fed-learn.o
	$(CC) $(CFLAGS) $(LDFLAGS) -pthread $^ -o $@
	
rb.o: examples/case-studies/rb.c
	$(CC) $(CFLAGS) $^ -c -o $@

cddc-main.o: examples/cddc-main.c
	$(CC) $(CFLAGS) $^ -c -o $@

cddc-main: cddc-main.o rb.o
	$(CC) $(CFLAGS) $(LDFLAGS) -pthread $^ -o $@

ct.o: examples/case-studies/ct.c
	$(CC) $(CFLAGS) $^ -c -o $@

memcmp-main.o: examples/memcmp-main.c
	$(CC) $(CFLAGS) $^ -c -o $@

memcmp-main: memcmp-main.o ct.o
	$(CC) $(CFLAGS) $(LDFLAGS) $^ -o $@
