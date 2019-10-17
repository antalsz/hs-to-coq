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

# These are core dependencies that we do not need to translate
#
EXTRA_CORE = Json \
  FastFunctions \
  Encoding \
  ErrUtils \
  Annotations \
  GhcPrelude \
  Packages \
  Foreign \
  IfaceType \
  PrelNames \
  TysWiredIn \
  CoAxiom 


UTILS = \
  Util \
  SrcLoc \
  Unique \
  UniqSupply \
  BasicTypes \
  DynFlags \
  Panic \
  OccName \
  Module \

DATASTRUCTS = \
  Bag \
  EnumSet \
  BooleanFormula \
  UniqFM \
  UniqSet \
  OrdList \
  FiniteMap \
  ListSetOps \
  Pair \
  State \
  Maybes \
  MonadUtils \

# Generated modules
# generated directly from ghc/compiler/*/
# These are general purpose utility modules
MODULES = \
  $(UTILS) \
  $(DATASTRUCTS) \

## Not actually used??
#  CmmType \


##
CORESYN = \
   IdInfo Class TyCon DataCon PatSyn Var VarSet VarEnv CoreSyn Demand Type TyCoRep Coercion  \

##
CONSTRUCTORS = \

# These are modules that we translate but do not do anything about
EXTRAS = \
  TrieMap \
  CSE \
  CoreStats \
  UnVarGraph \
  CoreArity \
  CoreTidy \
  CallArity \
  CoAxiom \
  TysWiredIn \
  MkCore \
  Digraph \
  SetLevels \
  CoreMonad \
  OccurAnal \
  FloatIn \
  FloatOut \

## These are the modules most directly related to the core language
CORE_MODULES = \
  FastStringEnv \
  Constants \
  Id \
  CoreSubst \
  PrelNames \
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
VFILES_CORE      = $(addsuffix .v,$(CORE_MODULES) $(EXTRAS))
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


HSFILES     = $(addsuffix .hs,$(MODULES) $(CORESYN) $(CORE_MODULES)) 
HSFILESPATH = $(addprefix ghc/compiler/*/,$(HSFILES)) 

SMALLCORE = $(addsuffix .hs,$(CORESYN))
SMALLPATH  = $(addprefix ghc/compiler/*/,$(SMALLCORE)) 

EDITPATHS = $(addprefix module-edits/,$(MODULES) $(CORESYN) $(CORE_MODULES))
EDITFILES = edits $(CORE_EDITS) $(addsuffix /edits,$(EDITPATHS)) $(addsuffix /*.v, $(EDITPATHS))

all: vfiles coq

vfiles: $(OUT)/edits  $(OUT)/README.md $(OUT)/Makefile $(OUTFILES)

core: $(OUT)/README.md coq


filelist:
	@ls -1 $(HSFILESPATH)


editlist:
	@ls -1 $(EDITFILES) 2>/dev/null | xargs cloc --by-file-by-lang --lang-no-ext=zsh --force-lang=zsh,edits --force-lang=Coq,v --skip-uniqueness

edittable:
	@echo "skip"
	@cat $(EDITFILES) 2>/dev/null | grep "skip" | grep -v "#" | grep -v "constructor" | grep -v "module" | wc -l
	@echo "skip constructor"
	@cat $(EDITFILES) 2>/dev/null | grep "skip constructor" | grep -v "#" | wc -l
	@echo "skip module"
	@cat $(EDITFILES) 2>/dev/null | grep "skip module" | grep -v "#" | wc -l
	@echo "axiomatize"
	@cat $(EDITFILES) 2>/dev/null | grep "axiomatize" | grep -v "#" | grep -v "module" | wc -l
	@echo "redefine Axiom"
	@cat $(EDITFILES) 2>/dev/null | grep "redefine Axiom" | grep -v "#" | wc -l
	@echo "axiomatize module"
	@cat $(EDITFILES) 2>/dev/null | grep "axiomatize" | grep "module" | grep -v "#" | wc -l
	@echo "order"
	@cat $(EDITFILES) 2>/dev/null | grep "order" | grep -v "#" | wc -l
	@echo "termination"
	@cat $(EDITFILES) 2>/dev/null | grep "termination" | grep -v "#" | wc -l
	@echo "rewrite"
	@cat $(EDITFILES) 2>/dev/null | grep "rewrite" | grep -v "#" | wc -l
	@echo "redefine"
	@cat $(EDITFILES) 2>/dev/null | grep "redefine" | grep -v "#" | grep -v "Axiom" 
	@echo "rename type"
	@cat $(EDITFILES) 2>/dev/null | grep "rename type" | grep -v "#" | wc -l
	@echo "rename value"
	@cat $(EDITFILES) 2>/dev/null | grep "rename value" | grep -v "#" | wc -l
	@echo "set type"
	@cat $(EDITFILES) 2>/dev/null | grep "set type" | grep -v "#" | wc -l
	@echo "inline mutual"
	@cat $(EDITFILES) 2>/dev/null | grep "inline mutual" | grep -v "#" | wc -l
	@echo "rename module"
	@cat $(EDITFILES) 2>/dev/null | grep "rename module" | grep -v "#" | wc -l
	@echo "TOTAL"
	@cat $(EDITFILES) 2>/dev/null | grep -v "#" --include "*edits" | wc -l

ghc.all.pdf: Makefile
	find ghc/compiler -name \*.hs | xargs graphmod --no-cluster --prune-edges -r Outputable -r GhcPrelude | dot -Tpdf -o ghc.all.pdf


ghc.core.pdf: Makefile
	@ls -1 $(HSFILESPATH) | xargs	graphmod -i ghc/compiler/coreSyn -i ghc/compiler/basicTypes -i ghc/compiler/types -i ghc/compiler/utils -i ghc/compiler/simplCore -i ghc/compiler/main --no-cluster --prune-edges | dot -Tpdf -o ghc.core.pdf

# ghcrec.dot: Makefile
#	@ls -1 $(SMALLPATH) | xargs	graphmod -s 2 -i ghc/compiler/coreSyn -i ghc/compiler/basicTypes -i ghc/compiler/types -i ghc/compiler/utils -i ghc/compiler/simplCore -i ghc/compiler/main --prune-edges -r BooleanFormula -r Outputable -r Util -r DynFlags -r Module -r FiniteMap -r MonadUtils -r GhcPrelude -r FastString -r StringBuffer -r Lexeme -r UniqSupply -r BasicTypes -r CmdLineParser -r Packages -r Platform -r Binary -r UniqDSet -r OccName -r Digraph -r ErrUtils -r Panic -r Bag -r CoreStats -r SrcLoc -r Maybes -r Unique -r ListSetOps -r FastStringEnv -r UniqFM -r InteractiveEvalTypes -r OrdList -r DriverPhases -r Exception -r Pair -r UniqDFM -r UniqSet -r Constants > ghcrec.dot

ghcrec.pdf: ghcrec.dot
	dot -Tpdf -o ghcrec.pdf ghcrec.dot


cloc_table: 
	echo MANUAL
	cloc --by-file $(addsuffix .v, $(addprefix manual/,$(HANDMOD)))
	echo UTIL 
	cloc --by-file $(addsuffix .hs,$(addprefix ghc/compiler/*/,$(UTILS))) $(addsuffix .v,$(addprefix lib/,$(UTILS)))
	echo DATASTRUCTS
	cloc --by-file $(addsuffix .hs,$(addprefix ghc/compiler/*/,$(DATASTRUCTS))) $(addsuffix .v,$(addprefix lib/,$(DATASTRUCTS)))
	echo CORESYN
	cloc --by-file $(addsuffix .hs,$(addprefix ghc/compiler/*/,$(CORESYN))) lib/Core.v 
	echo CORE_MODULES
	cloc --by-file $(addsuffix .hs,$(addprefix ghc/compiler/*/,$(CORE_MODULES))) $(addsuffix .v,$(addprefix lib/,$(CORE_MODULES)))
	echo TOTAL
	cloc $(addsuffix .hs,$(addprefix ghc/compiler/*/,$(MODULES) $(CORESYN) $(CORE_MODULES))) $(addsuffix .v,$(addprefix lib/,$(MODULES) $(CORE_MODULES))) lib/Core.v $(addsuffix .v, $(addprefix manual/,$(HANDMOD)))


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
	echo '-Q ../../containers/theories  ""' >> $@
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
