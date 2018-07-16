FILES=Fib

all: coq vfiles

VFILES = $(addsuffix .v, $(FILES))
vfiles: _CoqProject Makefile.coq $(VFILES)

%.v: %.hs proof-suffix.v
	cabal new-exec -- ghc --make $<
	echo >> $@
	echo >> $@
	cat proof-suffix.v >> $@
	rm -f $*.o $*.hi

_CoqProject: Makefile
	> $@
	echo '-Q ../theories Proofs' >> $@
	echo '-Q ../lib ""' >> $@
	echo '-R ../../../base ""' >> $@
	echo '-Q ../../../base-thy  Proofs' >> $@
	echo '-Q ../../containers/lib   ""' >> $@
	echo '-Q ../../transformers/lib  ""' >> $@
	echo '-Q ../../containers/lib ""' >> $@
	echo '-Q ../../containers/theories ""' >> $@
	echo $(VFILES) >> $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)


clean:
	rm -f $(VFILES) _CoqProject

