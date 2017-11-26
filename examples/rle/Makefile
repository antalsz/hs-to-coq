HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

all: coq

RLE.v: RLE.hs edits preamble.v
	$(HS_TO_COQ) -e edits -p preamble.v -e ../../base/edits RLE.hs -o .

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq RLE.v Proofs.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.glob *.v.d RLE.v Makefile.coq  */*.v~
