include ../../common.mk

OUT=lib

CORE_EDITS=axiomatize-types.edits

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  FastString \
  AxiomatizedTypes \
  NestedRecursionHelpers \
  IntMap
  # Used by CSE
  # TysWiredIn \


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
  State \
  ListSetOps \
  Panic \

##
CORESYN = \
   IdInfo Class TyCon DataCon PatSyn Var VarSet VarEnv CoreSyn Demand Type $(CORETYPE)  \

##
CONSTRUCTORS = \


## These are the modules most directly related to the core language
CORE_MODULES = \
  Constants \
  Id \
  UnVarGraph \
  CoreSubst \
  CoreUtils \
  Name \
  NameEnv \
  NameSet \
  FV \
  Literal \
  FieldLabel \
  ConLike \
  CoreFVs \
  Exitify \
  CoreArity \
  CoreTidy \
  TrieMap \
  CSE \
  CoreStats \
  PrelNames \
#  CoAxiom \
#  TysWiredIn \
#  MkCore \
  CallArity \


NOTRANSLATE = \
  Constructors \
  CoreType \
  IdInfo2 \

CORETYPE = \
  TyCoRep \
  Coercion \

# These modules translate, but do not compile, at the moment and
# should not be processed by coq
BROKEN_MODULES = \



VFILES_GEN       = $(addsuffix .v,$(MODULES))
VFILES_MAN       = $(addsuffix .v,$(HANDMOD))
VFILES_DROPIN    = $(addsuffix .v,$(DROPIN))
VFILES_CORE      = $(addsuffix .v,$(CORE_MODULES))
VFILES_CONSTR    = Constructors.v
VFILES_CORESYN   = Core.v
VFILES_TYPE      = Type_.v

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_DROPIN) $(VFILES_CORE) $(VFILES_CORESYN) 

OUTFILES_GEN       = $(addprefix $(OUT)/,$(VFILES_GEN))
OUTFILES_MAN       = $(addprefix $(OUT)/,$(VFILES_MAN))
OUTFILES_CORE      = $(addprefix $(OUT)/,$(VFILES_CORE))
OUTFILES_DROPIN    = $(addprefix $(OUT)/,$(VFILES_DROPIN))
OUTFILES_CORETYPE  = $(addprefix $(OUT)/,$(VFILES_CORETYPE))
OUTFILES_CONSTR    = $(addprefix $(OUT)/,$(VFILES_CONSTR))
OUTFILES_CORESYN   = $(addprefix $(OUT)/,$(VFILES_CORESYN))
OUTFILES_TYPE      = $(addprefix $(OUT)/,$(VFILES_TYPE))

OUTFILES   = $(OUTFILES_GEN) $(OUTFILES_MAN) $(OUTFILES_DROPIN) $(OUTFILES_CORE) $(OUTFILES_CORESYN) 

HSFILES    = $(addsuffix .hs,$(MODULES)) $(addsuffix .hs,$(CORESYN)) $(addsuffix .hs,$(CORE_MODULES)) 
HSFILESPATH = $(addprefix ghc/compiler/*/,$(HSFILES)) 

all: vfiles coq

vfiles: $(OUT)/edits  $(OUT)/README.md $(OUT)/Makefile $(OUTFILES)

core: $(OUT)/README.md coq


filelist:
	@ls -1 $(HSFILESPATH) 

# This target is also used as a dependecy to ensure that $(OUT) exists.
$(OUT)/README.md:
	mkdir -p $(OUT)
	mkdir -p deps
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc`.' >> $@

$(OUT)/edits:
	mkdir -p $(OUT)
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
     -i gen-files \
     -I gen-files \
     -I ghc/includes \
     -I ghc/compiler \
     --ghc -DSTAGE=2 \
     --ghc -package=ghc-boot-th \
     --ghc -XNoImplicitPrelude \
     -e ../../base/edits \
     -e ../containers/edits \
     -e ../transformers/edits \
     --iface-dir ../../base \
     --iface-dir ../containers/lib \
     --iface-dir ../transformers/lib \
     --iface-dir $(OUT) \
     --dependency-dir deps \
     -e edits \
     -N \


-include deps/*.mk

%.h2ci: %.v
	test -e $@

.SECONDEXPANSION:
$(OUTFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -o $(OUT) \
		     $(word 1,$(wildcard ghc-head/$*.hs ghc/compiler/*/$*.hs))
	test -e $@

$(OUTFILES_CORE): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits $(CORE_EDITS)
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e $(CORE_EDITS) \
                     -o $(OUT) \
		     $(word 1,$(wildcard ghc-head/$*.hs ghc/compiler/*/$*.hs))
	test -e $@

CORESYN_PRE = $(wildcard $(addprefix module-edits/, $(addsuffix /preamble.v, $(CORESYN))))
CORESYN_MID = $(wildcard $(addprefix module-edits/, $(addsuffix /midamble.v, $(CORESYN))))

$(OUTFILES_CORESYN) : edits $(CORE_EDITS) $(CORESYN_PRE) $(CORESYN_MID) $(wildcard $(addprefix module-edits/, $(addsuffix /edits, $(CORESYN))))
	cat $(CORESYN_PRE) > CoreSyn_preamble.v
	cat $(CORESYN_MID) > CoreSyn_midamble.v
	$(HS_TO_COQ) $(HS_TO_COQ_GHC_OPTS) \
                -p CoreSyn_preamble.v \
                --midamble CoreSyn_midamble.v \
	             $(addprefix -e , $(wildcard $(addprefix module-edits/, $(addsuffix /edits, $(CORESYN))))) \
                -e $(CORE_EDITS) \
                -o $(OUT) \
		     $(addprefix ghc/compiler/*/, $(addsuffix .hs, $(CORESYN)))
	test -e $@
	rm -f CoreSyn_preamble.v CoreSyn_midamble.v

$(OUTFILES_TYPE) : edits $(CORE_EDITS) $$(wildcard module-edits/Type/preamble.v) $$(wildcard module-edits/Type/midamble.v)  $$(wildcard module-edits/Type/edits)
		$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/Type/edits)) \
	             $(addprefix -p , $(wildcard module-edits/Type/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/Type/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
            -o Type_.v \
		     $(word 1,$(wildcard ghc-head/Type.hs ghc/compiler/*/Type.hs))
	test -e $@

$(OUTFILES_CONSTR) : edits $(CORE_EDITS) module-edits/Constructors/preamble.v  module-edits/Constructors/midamble.v module-edits/Constructors/edits
	$(HS_TO_COQ) -e module-edits/Constructors/edits \
	                  -p module-edits/Constructors/preamble.v \
	                  --midamble module-edits/Constructors/midamble.v \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -e $(CORE_EDITS) \
                     -o $(OUT) \
		     $(addprefix ghc/compiler/*/, $(addsuffix .hs, $(CONSTRUCTORS)))
	test -e $@


$(OUTFILES_CORETYPE) : edits core-edits module-edits/CoreType/preamble.v  module-edits/CoreType/midamble.v module-edits/CoreType/edits
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

cleancore:
	rm -rf $(OUTFILES_CORE)
