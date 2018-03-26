include ../../common.mk

COQFILES=Simple.v

all: coq

%.v: %.hs Makefile
	$(HS_TO_COQ) -e ../../base/edits $*.hs -o .

_CoqProject: Makefile
	> $@
	echo '-Q . ""' >> $@
	echo '-R ../../base ""' >> $@
	echo '-Q ../../base-thy  Proofs' >> $@
	echo '-Q ../containers/lib   ""' >> $@
	echo $(COQFILES) >> $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(COQFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f *.vo *.glob *.v.d *.vo *.glob Makefile.coq  *.v~ _CoqProject
