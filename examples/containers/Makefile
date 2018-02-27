HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run -v0 exe:hs-to-coq --
endif
SHELL = bash

ifeq (,$(wildcard containers))
$(error Please create a symlink containers (see README.md))
endif

OUT=lib

RENAMED=renamed

HS_SPEC=hs-spec

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  Data/SequenceManual \
  Utils/Containers/Internal/PtrEquality \
  CTZ \
  Popcount \
  BitTerminationProofs \

# Generated modules
# generated directly from GHC/libraries/containers
MODULES = \
  Data/Set/Internal \
  Utils/Containers/Internal/BitQueue\
  Utils/Containers/Internal/BitUtil \
  Data/IntSet/Internal \
  Data/IntMap/Internal \
  Data/Map/Internal \
  IntSetValidity \

HS_SPEC_MODULES = \
  IntSetProperties # RENAMED from tests/containers/intset-properties.hs

# Generated modules
# generated directly from GHC/libraries/containers/tests
TEST_MODULES = \

# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_HS_SPEC_GEN = $(addprefix $(HS_SPEC)/,$(addsuffix .v,$(HS_SPEC_MODULES)))
VFILES_GEN_TEST = $(addprefix $(OUT)/,$(addsuffix .v,$(TEST_MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES = $(VFILES_GEN_TEST) $(VFILES_GEN) $(VFILES_HS_SPEC_GEN) $(VFILES_MAN) $(VFILES_SPECIAL) $(VFILES_DROPIN)

all:  $(VFILES) coq $(OUT)/edits $(OUT)/README.md $(HS_SPEC)/README.md

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo "-R ../../../base ''" >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject $(VFILES)
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits:
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	> $@
	echo 'This directory contains a Coq’ified version of the Haskell containers library' >> $@
	echo 'Do not edit files here! Instead, look in `examples/containers`.' >> $@

$(HS_SPEC)/README.md:
	> $@
	echo 'This directory contains a Coq’ified version of the Haskell containers library specification' >> $@
	echo 'Do not edit files here! Instead, look in `examples/containers`.' >> $@

coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)

# There ought to be some way to parameterize this
$(HS_SPEC)/IntSetProperties.v: $(RENAMED)/IntSetProperties.hs
$(RENAMED)/IntSetProperties.hs: containers/tests/intset-properties.hs
	mkdir -p $(RENAMED)
	ln -s ../$< $@

# KEEP THIS IN SYNC WITH THE NEXT RULE (there ought to be a better way)
.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) $(wildcard module-edits/$$*/flags) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
	             -e ../base-src/edits \
	             -e edits \
	             -N \
	             -i containers \
	             -i containers/tests \
	             -i containers/dist-install/build \
	             -I containers/include \
	             --ghc -package --ghc QuickCheck \
	             --ghc -this-unit-id --ghc containers \
	             $(addprefix `cat , $(addsuffix ` , $(wildcard module-edits/$*/flags))) \
	             -o $(OUT) \
	             $(wildcard containers/$*.hs) $(wildcard containers/tests/$*.hs) $$([[ -e $(RENAMED)/$*.hs ]] && echo $(RENAMED)/$*.hs)
	               # Can't use $(wildcard $(RENAMED)/$*.hs), I think because of .SECONDEXPANSION
	if [[ -e $(OUT)/Main.v && ( ! -e $@ || $(OUT)/Main.v -nt $@ ) ]]; then mv $(OUT)/Main.v $@; fi
	test -e $@ && test \! -e $(OUT)/Main.v

# KEEP THIS IN SYNC WITH THE PREVIOUS RULE (there ought to be a better way)
.SECONDEXPANSION:
$(VFILES_HS_SPEC_GEN): $(HS_SPEC)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) $(wildcard module-edits/$$*/flags) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
	             -e ../base-src/edits \
	             -e edits \
	             -N \
	             -i containers \
	             -i containers/tests \
	             -i containers/dist-install/build \
	             -I containers/include \
	             --ghc -package --ghc QuickCheck \
	             --ghc -this-unit-id --ghc containers \
	             $(addprefix `cat , $(addsuffix ` , $(wildcard module-edits/$*/flags))) \
	             -o $(HS_SPEC) \
	             $(wildcard containers/$*.hs) $(wildcard containers/tests/$*.hs) $$([[ -e $(RENAMED)/$*.hs ]] && echo $(RENAMED)/$*.hs)
	               # Can't use $(wildcard $(RENAMED)/$*.hs), I think because of .SECONDEXPANSION
	if [[ -e $(HS_SPEC)/Main.v && ( ! -e $@ || $(HS_SPEC)/Main.v -nt $@ ) ]]; then mv $(HS_SPEC)/Main.v $@; fi
	test -e $@ && test \! -e $(HS_SPEC)/Main.v

$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/


$(VFILES_DROPIN): $(OUT)/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             -e edits \
	       -o $(OUT) \
	       -N \
	       -p module-edits/$*/preamble.v \
	       --ghc -icontainers \
	       --ghc -icontainers/dist-install/build \
	       -Icontainers/include \
	       --ghc -this-unit-id=containers \
	       drop-in/$*.hs

clean:
	rm -rf $(OUT) $(RENAMED) $(HS_SPEC)
	rm -f counts.pdf *.aux *.log

todo:
	grep -a Axiom $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	grep -a Admitted $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	grep -a errorWithout $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	grep -a Parameter $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v

counts.pdf: counts.fig
	pdflatex counts

counts.fig: Makefile $(VFILES)
	(echo "\\begin{tabular}{lllll}"; \
    echo "Module & Defs & Class & Insts & Skipped\\\\"; \
    echo "\\multicolumn{4}{l}{\emph{Generated modules}}\\\\"; \
	 for i in  $(MODULES) $(DROPIN) ; \
       do (echo $$i; echo "&"; grep -a "Definition" $(OUT)/$$i.v | wc -l ; echo "&"; \
           grep -a "Class" $(OUT)/$$i.v | wc -l;  echo "&"; \
           grep -a "Instance" $(OUT)/$$i.v | wc -l;  echo "&"; \
           grep -a "skip" module-edits/$$i/edits | wc -l;  echo "\\\\" ) done; \
    echo "\\\\"; \
    echo "\\multicolumn{4}{l}{\emph{Manually adapted modules}}\\\\"; \
	 for i in  $(HANDMOD) ; \
       do (echo $$i; echo "&"; grep -a "Definition" $(OUT)/$$i.v | wc -l ;  echo "&"; \
           grep -a "Class" $(OUT)/$$i.v | wc -l ;  echo "&"; \
           grep -a "Instance" $(OUT)/$$i.v| wc -l; echo "\\\\" ) done; \
	 echo "\\end{tabular}") > counts.fig
