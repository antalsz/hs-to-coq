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
  ListSetOps \
  Digraph \
  PrelNames \
#  CallArity \
#  TysWiredIn \


# generated from drop-in/
DROPIN = \


# Generated modules
# generated directly from ghc/compiler/*/
# These are general purpose utility modules
MODULES = \
  Util \
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

## These are the modules most directly related to the core language
CORE_MODULES = \
  IdInfo \
  CoreSyn \
  UnVarGraph \
  Demand \
  CoreSubst \
  CoreUtils \
  Id \
  CoreFVs \
  CoreArity \
  Var \
  VarEnv \
  VarSet \
  FV \
  Literal \
  Class \
  DataCon \
  PatSyn \
  ConLike \
  Name \
  NameEnv \
  NameSet \
  FieldLabel \
  Constants \

CORETYPE = \
  TyCoRep \
  Coercion \
  CoAxiom \
  Type \
  TyCon \



# These modules translate, but do not compile, at the moment and
# should not be processed by coq
BROKEN_MODULES = \
  CoreType \
  CoreSyn \
  IdInfo2 \
  TyCoRep \
  CoreSubst \
  CoreArity \
  CallArity \
  Literal \
  UnVarGraph \
  Demand \
  CoreUtils \
  Id \
  CoreFVs \

VFILES_GEN       = $(addsuffix .v,$(MODULES))
VFILES_MAN       = $(addsuffix .v,$(HANDMOD))
VFILES_DROPIN    = $(addsuffix .v,$(DROPIN))
VFILES_CORE      = $(addsuffix .v,$(CORE_MODULES))
VFILES_CORETYPE  = CoreType.v

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_DROPIN) $(VFILES_CORE) $(VFILES_CORETYPE)

OUTFILES_GEN       = $(addprefix $(OUT)/,$(VFILES_GEN))
OUTFILES_MAN       = $(addprefix $(OUT)/,$(VFILES_MAN))
OUTFILES_CORE      = $(addprefix $(OUT)/,$(VFILES_CORE))
OUTFILES_DROPIN    = $(addprefix $(OUT)/,$(VFILES_DROPIN))
OUTFILES_CORETYPE  = $(addprefix $(OUT)/,$(VFILES_CORETYPE))

OUTFILES   = $(OUTFILES_GEN) $(OUTFILES_MAN) $(OUTFILES_DROPIN) $(OUTFILES_CORE) $(OUTFILES_CORETYPE)

all: $(OUT)/README.md $(OUTFILES) coq

# This target is also used as a dependecy to ensure that $(OUT) exists. 
$(OUT)/README.md:
	mkdir -p $(OUT)
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc`.' >> $@
	ln -fs ../edits $(OUT)/edits

$(OUT)/_CoqProject: $(OUT)/README.md Makefile
	> $@
	echo '-Q . ""' >> $@
	echo '-R ../../../base ""' >> $@
	echo '-Q ../../../base-thy  Proofs' >> $@
	echo '-Q ../../containers/lib   ""' >> $@
	echo '-Q ../../transformers/lib  ""' >> $@
	echo $(filter-out $(addsuffix .v,$(BROKEN_MODULES)), $(VFILES)) >> $@

$(OUT)/Makefile: $(OUT)/README.md $(OUT)/_CoqProject $(OUTFILES) Makefile
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

coq: $(OUT)/Makefile $(OUTFILES)
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
$(OUTFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -o $(OUT) \
		     ghc/compiler/*/$*.hs
	test -e $@

$(OUTFILES_CORE): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits core-edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e no-type-edits \
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
		     $(addprefix ghc/compiler/*/, $(addsuffix .hs, $(CORETYPE)))
	test -e $@

$(OUTFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

clean:
	rm -rf $(OUT)
	rm -f *.aux *.log
