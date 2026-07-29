# Standard out-of-tree OP-TEE TA Makefile (matches optee_examples/*/ta).
# UNTESTED -- see cdm/tee/optee/README.md.

CFG_TEE_TA_LOG_LEVEL ?= 2
CPPFLAGS += -DTEE_TA_LOG_LEVEL=$(CFG_TEE_TA_LOG_LEVEL)

# Must match the UUID in include/drm_poc_ta.h exactly (that's what
# TEEC_OpenSession dials, and what names the built .ta file).
BINARY = 4f2b6a6e-9c1d-4e8a-b30f-6a8e1d2c7f51

-include $(TA_DEV_KIT_DIR)/mk/ta_dev_kit.mk
