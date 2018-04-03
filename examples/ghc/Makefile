include ../../common.mk

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
  ListSetOps \
  Digraph \
  IdInfo \
  IdInfo2 \
  Class \
  DataCon \
  PatSyn \
  Core \
  TyCoRep \
  PrelNames \
  TysWiredIn \
  CallArity \

# generated from drop-in/
DROPIN = \


# Generated modules
# generated directly from ghc/compiler/*/
MODULES = \
  Maybes \
  MonadUtils \
  Pair \
  Bag \
  SrcLoc \
  Unique \
  UniqSupply \
  UniqFM \
  EnumSet \
  CmmType \
  BooleanFormula \
  UniqSet \
  BasicTypes \
  FiniteMap \
  UniqDFM \
  UniqDSet \
  FastStringEnv \
  DynFlags \
  Module \
  OrdList \
  OccName \
  Name \
  NameEnv \
  NameSet \
  FieldLabel \
  Constants \

## These are the modules most directly related to the core language
CORE_MODULES = \
  VarSet \
  VarEnv \
  ConLike \
  FV \
  TyCon \
  Literal \
  CoreSyn \
  UnVarGraph \
  Demand \
  CoreSubst \
  CoreUtils \
  CoAxiom \
  Id \
  CoreFVs \
  CoreArity \

CORETYPE = \
  TyCoRep \
  Coercion \
  Type \
  Var \


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_CORE = $(addprefix $(OUT)/,$(addsuffix .v,$(CORE_MODULES)))
VFILES_DROPIN = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_CORE) $(VFILES_DROPIN) lib/CoreType.v

all: $(OUT)/edits $(OUT)/README.md $(VFILES) coq

$(OUT):
	mkdir -p $(OUT)

$(OUT)/_CoqProject: $(OUT) Makefile
	> $@
	echo '-Q . ""' >> $@
	echo '-R ../../../base ""' >> $@
	echo '-Q ../../../base-thy  Proofs' >> $@
	echo '-Q ../../containers/lib   ""' >> $@
	echo '-Q ../../transformers/lib  ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(CORE_MODULES)) >> $@
	echo CoreType.v >> $@

$(OUT)/Makefile: $(OUT) $(OUT)/_CoqProject $(VFILES)
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits: $(OUT)
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc`.' >> $@

coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)


HS_TO_COQ_GHC_OPTS=\
     --ghc-tree ghc \
     -I ghc/includes \
     -I ghc/includes/dist-derivedconstants/header \
     -I ghc/compiler \
     -I ghc/compiler/stage2 \
     -I ghc/compiler/stage2/build \
     --ghc -DSTAGE=2 \
     --ghc -package=ghc-boot-th \
     --ghc -XNoImplicitPrelude \
     -e ../../base/edits \
     -e ../containers/edits \
     -e ../transformers/edits \
     -e edits \
     -N \


.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -o $(OUT) \
		     ghc/compiler/*/$*.hs
	test -e $@
# We added the `test` because `hs-to-coq` doesn't return an error


$(VFILES_CORE): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits core-edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e core-edits \
                     -o $(OUT) \
		     ghc/compiler/*/$*.hs
	test -e $@


$(OUT)/CoreType.v : edits core-edits module-edits/CoreType/preamble.v  module-edits/CoreType/midamble.v module-edits/CoreType/edits
	$(HS_TO_COQ) -e module-edits/CoreType/edits \
	                  -p module-edits/CoreType/preamble.v \
	                  --midamble module-edits/CoreType/midamble.v \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e core-edits \
                     -o $(OUT) \
		     ghc/compiler/types/TyCoRep.hs \
		     ghc/compiler/types/Coercion.hs \
		     ghc/compiler/types/Type.hs \
		     ghc/compiler/basicTypes/Var.hs
	test -e $@



# We added the `test` because `hs-to-coq` doesn't return an error


$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

clean:
	rm -rf $(OUT)
	rm -f *.aux *.log
