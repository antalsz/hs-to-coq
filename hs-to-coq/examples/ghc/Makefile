HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

ifeq (,$(wildcard ghc))
$(error Please create a symlink ghc (see README.md))
endif

# Handwritten modules
HANDMOD = Proofs \


# Generated modules
MODULES  = MonadUtils \
           Pair \
           Bag \



VFILES_GEN     = $(addsuffix .v,$(MODULES))
VFILES_MAN     = $(addsuffix .v,$(HANDMOD))
VFILES_SPECIAL = $(addsuffix .v,$(SPECIAL_MODULES))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_SPECIAL)

all: $(VFILES) coq

_CoqProject : Makefile
	> $@
	echo "-Q .                \"\"" >> $@
	echo "-Q ../base-thy      Proofs" >> $@
	echo "-Q ../ghc-base/lib/ \"\"" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(EMPTY_MODS)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@

Makefile.coq: _CoqProject $(VFILES)
	coq_makefile -f _CoqProject -o Makefile.coq

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

.SECONDEXPANSION:
$(VFILES_GEN): %.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) -e edits \
	             -e ../ghc-base/edits \
                -p preamble.v \
	             $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             --ghc-tree ghc \
	             -I ghc/includes \
	             -I ghc/compiler \
	             -I ghc/compiler/stage2 \
	             -I ghc/compiler/stage2/build \
	             --ghc -DSTAGE=2 \
	             --ghc -package=ghc-boot-th \
	             -N \
	             -o . \
	             ghc/compiler/*/$*.hs
	test -e $@
# We added the `test` because `hs-to-coq` doesn't return an error

# $(VFILES_MAN): lib/%.v : manual/%.v
#	mkdir -p "$$(dirname lib/$*.v)"
#	cp -v $< $@

clean:
	rm -f */*.vo *.glob */*.v.d *.glob *.vo *.v.d  $(VFILES_GEN) _CoqProject Makefile.coq  */*.v~
