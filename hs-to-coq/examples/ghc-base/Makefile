HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

ifeq (,$(wildcard base))
$(error Please create a symlink base (see README.md))
endif

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.

# GHC/Unicode needs precedence resolution, plus a few issues with unicode constants
# Data/Char needs a show instance.  Also use of data cons separate from definition.
# Data/Monoid redefines the notation "<>" (at a different level). Need to sort this out.

# Handwritten modules (usually by modification of generated version)
HANDMOD = GHC/Prim \
          GHC/Num \
          GHC/Char \
          GHC/Enum \
          GHC/Real \
          GHC/Unicode \
          GHC/Base \
          Data/Char \
          Data/Bits \
          Data/Type/Equality \
          GHC/Word \
          GHC/Int \
          Data/Bool \
          Prelude

# GHC.Base imports modules without using anything from it (e.g. because
# everything using there was renamed or skipped). For now, provide these empty
# modules.
# Ideally, hs-to-coq should be smarter, and maybe only import names that occur in
# the code?
EMPTY_MODS  =\
	  GHC/Types \
	  GHC/Classes \
	  GHC/CString \
	  GHC/Magic \
	  GHC/Err \
	  GHC/IO \
	  GHC/Tuple \
	  GHC/Integer \
	  GHC/Read \
	  GHC/Show \
	  GHC/Generics \
	  _GHC/Base \
	  _GHC/BaseGen \
	  _GHC/Num \


# Generated modules
# All except BaseGen are generated directly from GHC/libraries/base
MODULES  = GHC/List \
           Data/Tuple \
           Data/Maybe \
           Data/Function \
           Data/Ord \
           Data/Eq \
           Data/Monoid

# generated from drop-in/
SPECIAL_MODULES = GHC/BaseGen

VFILES_GEN = $(addprefix lib/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix lib/,$(addsuffix .v,$(HANDMOD)))
VFILES_EMPTY = $(addprefix lib/,$(addsuffix .v,$(EMPTY_MODS)))
VFILES_SPECIAL = $(addprefix lib/,$(addsuffix .v,$(SPECIAL_MODULES)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_EMPTY) $(VFILES_SPECIAL)

all:  $(VFILES) coq

lib/_CoqProject : Makefile
	mkdir -p lib
	> $@
	echo "-R . Top" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(EMPTY_MODS)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@

lib/Makefile.coq: lib/_CoqProject $(VFILES)
	cd lib; coq_makefile -f _CoqProject -o Makefile.coq

coq: lib/Makefile.coq $(VFILES)
	$(MAKE) -C lib -f Makefile.coq OPT=$(COQFLAGS)


$(VFILES_GEN): lib/%.v : edits/%/edits renamings edits/%/preamble.v
	$(HS_TO_COQ) -e edits/$*/edits \
	             -r renamings \
		     -N \
		     -o lib \
		     -p edits/$*/preamble.v \
		     base/$*.hs

$(VFILES_MAN): lib/%.v : manual/%.v
	mkdir -p "$$(dirname lib/$*.v)"
	cp -v $< $@

$(VFILES_EMPTY): lib/%.v :
	mkdir -p "$$(dirname lib/$*.v)"
	echo '(* Empty module, exists only to make Import statments not fail *)' > $@

lib/GHC/BaseGen.v : edits/GHC/Base/edits renamings edits/GHC/Base/preamble.v drop-in/GHC/BaseGen.hs
	$(HS_TO_COQ) -e edits/GHC/Base/edits \
	             -r renamings \
		     -o lib \
		     -N \
		     -p edits/GHC/Base/preamble.v \
		     --ghc -ibase \
		     --ghc -ibase/dist-install/build \
		     -Ibase/include \
		     --ghc -this-unit-id=base \
		     drop-in/GHC/BaseGen.hs


clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d  $(VFILES) _CoqProject Makefile.coq  */*.v~

