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

OUT=lib

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  FastString \
  Panic \
  Util \
  CallArity \
  IdInfo \
  IdInfo2 \
  Id \

# Generated modules
# generated directly from ghc/compiler/*/
MODULES = \
  Maybes \
  MonadUtils \
  Pair \
  Bag \
  SrcLoc \
  BasicTypes \
  Unique \
  UniqSupply \
  UniqFM \
  CmmType \
  BooleanFormula \
  UniqSet \
  OccName \
  Module \
  DynFlags \
  UniqDFM \
  UniqDSet \
  Name \
  NameEnv \
  NameSet \
  Var \
  VarSet \
  VarEnv \
  FastStringEnv \
  FieldLabel \
  Literal \
  Class \
  DataCon \
  PatSyn \
  ConLike \
  CoreSyn \
  CoreArity \
  CoreUtils \
  UnVarGraph \
  Demand \


# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_SPECIAL)

all:  $(VFILES) coq $(OUT)/edits $(OUT)/README.md

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo "-Q . \"\"" >> $@
	echo "-R ../../../base \"\"" >> $@
	echo "-Q ../../../base-thy  Proofs" >> $@
	echo "-Q ../../containers/lib   \"\"" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject $(VFILES)
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits:
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc`.' >> $@

coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)


.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
                     --ghc-tree ghc \
                     -I ghc/includes \
                     -I ghc/compiler \
                     -I ghc/compiler/stage2 \
                     -I ghc/compiler/stage2/build \
                     --ghc -DSTAGE=2 \
                     --ghc -package=ghc-boot-th \
                     -e ../../base/edits \
                     -e ../containers/edits \
                     -e edits \
                     -N \
                     -o $(OUT) \
		     ghc/compiler/*/$*.hs
	test -e $@
# We added the `test` because `hs-to-coq` doesn't return an error


$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

clean:
	rm -rf $(OUT)
	rm -f *.aux *.log
