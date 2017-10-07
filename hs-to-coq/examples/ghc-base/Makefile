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


# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  GHC/Num \
  GHC/Char \
  GHC/Enum \
  GHC/Real \
  GHC/Unicode \
  Data/Char \
  Data/Type/Equality \
  GHC/Word \
  GHC/Int \
  Data/Bool \
  Control/Category \
  Data/Either \
  Data/Proxy \
  Data/Foldable \
  Data/Functor/Const \
  Control/Arrow \
  Data/Bits \
  Prelude

# Generated modules
# generated directly from GHC/libraries/base
MODULES = \
  GHC/List \
  Data/Tuple \
  Data/Maybe \
  Data/Function \
  Data/Ord \
  Data/Eq \
  Data/Functor \
  Data/Monoid \
  Control/Monad \
  Data/OldList \
  Data/Traversable \

# generated from drop-in/
DROPIN = GHC/Base \


# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix lib/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix lib/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix lib/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN = $(addprefix lib/,$(addsuffix .v,$(DROPIN)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_SPECIAL) $(VFILES_DROPIN)

all:  $(VFILES) coq

lib/_CoqProject : Makefile
	mkdir -p lib
	> $@
	echo "-Q . \"\"" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

lib/Makefile.coq: lib/_CoqProject $(VFILES)
	cd lib; coq_makefile -f _CoqProject -o Makefile.coq

coq: lib/Makefile.coq $(VFILES)
	$(MAKE) -C lib -f Makefile.coq OPT=$(COQFLAGS)


.SECONDEXPANSION:
$(VFILES_GEN): lib/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             -e edits \
		     -N \
		     -i base \
		     -i base/dist-install/build \
		     -I base/include \
		     --ghc -this-unit-id --ghc base \
		     -o lib \
		     base/$*.hs
	test -e $@

$(VFILES_MAN): lib/%.v : manual/%.v
	mkdir -p "$$(dirname lib/$*.v)"
	cp -v $< $@


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

clean:
	rm -rf lib

todo:
	grep Axiom lib/*.v lib/*/*.v lib/*/*/*.v
	grep Admitted lib/*.v lib/*/*.v lib/*/*/*.v
	grep errorWithout lib/*.v lib/*/*.v lib/*/*/*.v
