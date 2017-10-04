HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

MODULES=\
	Combined
	#Common \
	#Size  \
	#Types
VFILES_GEN = $(addsuffix .v,$(MODULES)) 
VFILES = $(VFILES_GEN)

all: $(VFILES) coq


$(VFILES_GEN): %.v: orig/%.hs edits/%/edits edits/%/preamble.v ../ghc-base/renamings renamings
	$(HS_TO_COQ) $< -e ../ghc-base/renamings -e renamings -e edits/$*/edits -p edits/$*/preamble.v -o $@
	# Work around https://github.com/antalsz/hs-to-coq/issues/12
	if [ $* = 'Combined' ]; then sed -e 's/Mk_Stream {s} :/Mk_Stream : forall {s},/' -i $@; fi
	if [ $* = 'Combined' ]; then sed -e 's/| (Mk_Stream /| (Mk_Stream _ /' -i $@; fi

_CoqProject:
	> $@
	echo '-R ../ghc-base/lib/ Top' >> $@
	echo '-R . Top' >> $@
	echo $(VFILES) >> $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.glob *.vo *.v.d $(VFILES_GEN) _CoqProject Makefile.coq  */*.v~
