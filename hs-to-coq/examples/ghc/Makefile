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

# Handwritten modules (usually by modification of generated version)
HANDMOD = Proofs

# Empty mods (to please imports)
EMPTY_MODS =

# Generated modules
# All except BaseGen are generated directly from GHC/libraries/base
MODULES  = Bag

VFILES_GEN     = $(addsuffix .v,$(MODULES))
VFILES_MAN     = $(addsuffix .v,$(HANDMOD))
VFILES_EMPTY   = $(addsuffix .v,$(EMPTY_MODS))
VFILES_SPECIAL = $(addsuffix .v,$(SPECIAL_MODULES))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_EMPTY) $(VFILES_SPECIAL)

all: $(VFILES) coq

_CoqProject : Makefile
	> $@
	echo "-R .                Top" >> $@
	echo "-R ../base-thy      Proofs" >> $@
	echo "-R ../ghc-base/lib/ Top" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(EMPTY_MODS)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@

Makefile.coq: _CoqProject $(VFILES)
	coq_makefile -f _CoqProject -o Makefile.coq

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)


$(VFILES_GEN): %.v : edits
	$(HS_TO_COQ) -e edits \
	             -e ../ghc-base/edits \
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

$(VFILES_EMPTY): %.v :
	mkdir -p "$$(dirname lib/$*.v)"
	echo '(* Empty module, exists only to make Import statments not fail *)' > $@

clean:
	rm -f */*.vo *.glob */*.v.d *.glob *.vo *.v.d  $(VFILES_GEN) $(VFILES_EMPTY) _CoqProject Makefile.coq  */*.v~
