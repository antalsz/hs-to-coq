all: coq

VFILES=$(shell find . -name '*.v')

_CoqProject : Makefile $(VFILES)
	> $@
	echo "-Q . Proofs" >> $@
	echo "-Q ../ghc-base/lib/ \"\"" >> $@
	echo $(VFILES)                  >> $@

Makefile.coq: _CoqProject $(VFILES)
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d _CoqProject Makefile.coq */*.v~
