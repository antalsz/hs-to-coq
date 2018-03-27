
HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
ifeq ($(HS_TO_COQ_COVERAGE),True)
	CABAL_OPTS = --enable-coverage
endif
HS_TO_COQ = cabal new-run -v0 $(CABAL_OPTS) exe:hs-to-coq --
endif
SHELL = bash

