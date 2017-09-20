HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

ifeq (,$(wildcard ghc))
$(error Please create a symlink base (see README.md))
endif

all: coq

Bag.v: ghc/compiler/utils/Bag.hs edits preamble.v
	$(HS_TO_COQ) -e edits -p preamble.v $< -o $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq Bag.v Proofs.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d Bag.v Makefile.coq  */*.v~
