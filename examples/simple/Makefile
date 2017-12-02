COQFILES=Simple.v

HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

all: coq

%.v: %.hs Makefile
	$(HS_TO_COQ) -e ../../base/edits $*.hs -o .

_CoqProject: Makefile
	> $@
	echo "-Q . \"\"" >> $@
	echo "-R ../../base \"\"" >> $@
	echo "-Q ../../base-thy  Proofs" >> $@
	echo "-Q ../containers/lib   \"\"" >> $@
	echo $(COQFILES) >> $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(COQFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f *.vo *.glob *.v.d *.vo *.glob Makefile.coq  *.v~ _CoqProject
