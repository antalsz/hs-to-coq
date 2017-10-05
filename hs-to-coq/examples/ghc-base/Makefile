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
# Also derives many type classes. We should fill the instances in.


# Handwritten modules (usually by modification of generated version)
HANDMOD = GHC/Base \
          GHC/Num \
          GHC/Char \
          GHC/Enum \
          GHC/Real \
          GHC/Unicode \
          Data/Char \
          Data/Bits \
          Data/Type/Equality \
          GHC/Word \
          GHC/Int \
          Data/Bool \
          Control/Category \
		    Data/Either \
          Control/Arrow \
          Data/Proxy \
	       Data/Foldable \
          Data/Functor/Const \
          Data/Monoid \
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
	  _GHC/Num \
	  Data/Type/Coercion \
	  GHC/Arr \
     GHC/ST \
     System/IO \
     Control/Monad/Fix \
     Foreign/Storable \
     GHC/Float \
     Control/Applicative

# Generated modules
# generated directly from GHC/libraries/base
MODULES  = GHC/List \
           Data/Tuple \
           Data/Maybe \
           Data/Function \
           Data/Ord \
           Data/Eq \
           Data/Functor \


# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix lib/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix lib/,$(addsuffix .v,$(HANDMOD)))
VFILES_EMPTY = $(addprefix lib/,$(addsuffix .v,$(EMPTY_MODS)))
VFILES_SPECIAL = $(addprefix lib/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN = $(addprefix lib/,$(addsuffix .v,$(DROPIN)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_EMPTY) $(VFILES_SPECIAL) $(VFILES_DROPIN)

all:  $(VFILES) coq

lib/_CoqProject : Makefile
	mkdir -p lib
	> $@
	echo "-R . Top" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(EMPTY_MODS)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

lib/Makefile.coq: lib/_CoqProject $(VFILES)
	cd lib; coq_makefile -f _CoqProject -o Makefile.coq

coq: lib/Makefile.coq $(VFILES)
	$(MAKE) -C lib -f Makefile.coq OPT=$(COQFLAGS)


$(VFILES_GEN): lib/%.v : module-edits/%/edits edits module-edits/%/preamble.v
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             -e edits \
		     -N \
		     -o lib \
		     -p module-edits/$*/preamble.v \
		     base/$*.hs

$(VFILES_MAN): lib/%.v : manual/%.v
	mkdir -p "$$(dirname lib/$*.v)"
	cp -v $< $@

$(VFILES_EMPTY): lib/%.v :
	mkdir -p "$$(dirname lib/$*.v)"
	echo '(* Empty module, exists only to make Import statments not fail *)' > $@

# lib/GHC/BaseGen.v : module-edits/GHC/Base/edits edits module-edits/GHC/Base/preamble.v drop-in/GHC/BaseGen.hs
#	$(HS_TO_COQ) -e module-edits/GHC/Base/edits \
#	             -e edits \
#		     -o lib \
#		     -N \
#		     -p module-edits/GHC/Base/preamble.v \
#		     --ghc -ibase \
#		     --ghc -ibase/dist-install/build \
#		     -Ibase/include \
#		     --ghc -this-unit-id=base \
#		     drop-in/GHC/BaseGen.hs


$(VFILES_DROPIN): lib/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             -e edits \
		     -o lib \
		     -N \
		     -p module-edits/$*/preamble.v \
		     --ghc -ibase \
		     --ghc -ibase/dist-install/build \
		     -Ibase/include \
		     --ghc -this-unit-id=base \
		     drop-in/$*.hs



# lib/Data/Foldable.v : module-edits/Data/Foldable/edits edits module-edits/Data/Foldable/preamble.v drop-in/Data/Foldable.hs
#	$(HS_TO_COQ) -e module-edits/Data/Foldable/edits \
#	             -e edits \
#		     -o lib \
#		     -N \
#		     -p module-edits/Data/Foldable/preamble.v \
#		     --ghc -ibase \
#		     --ghc -ibase/dist-install/build \
#		     -Ibase/include \
#		     --ghc -this-unit-id=base \
#		     drop-in/Data/Foldable.hs


clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d  $(VFILES) _CoqProject Makefile.coq  */*.v~
