include ../../common.mk

all: coq

RLE.v: RLE.hs edits preamble.v
	$(HS_TO_COQ) -e edits -p preamble.v -e ../../base/edits RLE.hs -o .

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq RLE.v Proofs.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.glob *.v.d RLE.v Makefile.coq  */*.v~
