HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

# Edit this
GENMODS = Intervals
MANMODS = Ensemble_facts Proofs

# Abstract stuff

VFILES_GEN = $(addsuffix .v,$(subst .,/,$(GENMODS)))
VFILES_MAN = $(addsuffix .v,$(MANMODS))

VFILES   = $(VFILES_GEN) $(VFILES_MAN)

all: coq

$(VFILES_GEN): %.v : %.hs edits  ../../base/edits
	$(HS_TO_COQ) -e edits -e ../../base/edits $< -o .

_CoqProject : Makefile
	> $@
	echo "-Q .               \"\""		>> $@
	echo "-Q ../../base-thy/ Proofs" >> $@
	echo "-Q ../../base/     \"\""		>> $@
	echo $(VFILES)										>> $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*/*.vo */*/*.glob */*/*.v.d */*.vo */*.glob */*.v.d *.glob *.vo *.v.d _CoqProject Makefile.coq $(VFILES_GEN) */*.v~
