include ../../common.mk

all: coq

Lambda.v: Lambda.hs edits preamble.v
	$(HS_TO_COQ) -e edits -p preamble.v -e ../../base/edits Lambda.hs > Lambda.v

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq Lambda.v Proofs.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d Lambda.v Makefile.coq  */*.v~
