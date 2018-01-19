HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run -v0 exe:hs-to-coq --
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

CORE_MODULES = \
  Var \
  VarSet \
  VarEnv \
  ConLike \
  FV \
  TyCon \
  Literal \
  CoreSyn \
  CoreArity \
  UnVarGraph \
  Demand \
  CoreUtils \
  CoAxiom \
  Id \

VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_CORE = $(addprefix $(OUT)/,$(addsuffix .v,$(CORE_MODULES)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_CORE)

all: $(OUT)/edits $(OUT)/README.md $(VFILES) coq

$(OUT):
	mkdir -p $(OUT)

$(OUT)/_CoqProject: $(OUT) Makefile
	> $@
	echo "-Q . \"\"" >> $@
	echo "-R ../../../base \"\"" >> $@
	echo "-Q ../../../base-thy  Proofs" >> $@
	echo "-Q ../../containers/lib   \"\"" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(CORE_MODULES)) >> $@

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


$(VFILES_CORE): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits core-edits
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
                     -e core-edits \
                     -N \
                     -o $(OUT) \
		     ghc/compiler/*/$*.hs
	test -e $@



$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

clean:
	rm -rf $(OUT)
	rm -f *.aux *.log
