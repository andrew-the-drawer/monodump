# Standard out-of-tree OP-TEE CA Makefile (matches optee_examples/*/host).
# UNTESTED -- see cdm/tee/optee/README.md.

CC ?= $(CROSS_COMPILE)gcc

CFLAGS += -Wall -I../ta/include -I$(TEEC_EXPORT)/include
LDADD += -lteec -L$(TEEC_EXPORT)/lib

BINARY = drm_poc_ca

.PHONY: all
all: $(BINARY)

$(BINARY): main.o
	$(CC) -o $@ $< $(LDADD)

.PHONY: clean
clean:
	rm -f main.o $(BINARY)
