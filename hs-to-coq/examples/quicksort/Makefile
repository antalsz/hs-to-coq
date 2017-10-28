HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

all: coq

QuickSort.v: QuickSort.hs edits
	$(HS_TO_COQ) -e edits -e ../ghc-base/edits QuickSort.hs -o .

QuickSort2.v: QuickSort2.hs edits2 preamble2.v
	$(HS_TO_COQ) -e edits2 -e ../ghc-base/edits -p preamble2.v QuickSort2.hs -o .

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq QuickSort.v QuickSort2.v Proofs.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d QuickSort.v QuickSort2.v Makefile.coq  */*.v~
