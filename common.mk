HAVE_STACK := $(shell command -v stack 2> /dev/null)

ifdef HAVE_STACK
ifdef FOREIGN_HS_TO_COQ
ifndef HS_TO_COQ_DIR
$(error "Using `hs-to-coq/common.mk' outside the hs-to-coq directory requires setting `HS_TO_COQ_DIR'")
endif
HS_TO_COQ = $(shell cd $(HS_TO_COQ_DIR) && stack exec env | perl -ne 'print "$$1/hs-to-coq\n" if /^PATH=([^:]+)/')
else
HS_TO_COQ = stack exec hs-to-coq --
endif
else
ifndef FOREIGN_HS_TO_COQ
$(error "Using `hs-to-coq/common.mk' outside the hs-to-coq directory requires `stack'")
endif
ifeq ($(HS_TO_COQ_COVERAGE),True)
	CABAL_OPTS = --enable-coverage
endif
TOP := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
HS_TO_COQ = cabal new-run --project-file=$(TOP)/cabal.project  -v0 $(CABAL_OPTS) exe:hs-to-coq --
endif

SHELL = bash
