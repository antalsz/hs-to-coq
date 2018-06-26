HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run -v0 exe:hs-to-coq --
endif
SHELL = bash

SRC=transformers

OUT=lib

RENAMED=renamed

HS_SPEC=hs-spec

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \

#  Data/SequenceManual \

# Generated modules
# generated directly from GHC/libraries/$(SRC)
MODULES = \
   Data/Functor/Constant \
   Data/Functor/Reverse \
   Control/Applicative/Backwards \
   Control/Applicative/Lift \
   Control/Monad/Trans/Class \
   Control/Monad/Signatures \
   Control/Monad/Trans/Identity \
   Control/Monad/Trans/Reader \
   Control/Monad/Trans/Writer/Lazy \
   Control/Monad/Trans/State/Lazy \
   Control/Monad/Trans/Cont \
   Control/Monad/Trans/Except \
   Control/Monad/Trans/Maybe \
   Control/Monad/Trans/RWS/Lazy \

# Not in ghc version of transformers
#	Control/Monad/Trans/Accum \
#	Control/Monad/Trans/Select \

# Generated modules
# generated directly from GHC/libraries/$(SRC)/tests
TEST_MODULES = \

# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_GEN_TEST = $(addprefix $(OUT)/,$(addsuffix .v,$(TEST_MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES = $(VFILES_GEN_TEST) $(VFILES_GEN) $(VFILES_MAN) $(VFILES_SPECIAL) $(VFILES_DROPIN)

all: vfiles coq

vfiles: $(OUT)/edits  $(OUT)/README.md $(OUT)/Makefile $(VFILES)

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo '-R ../../../base ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject $(VFILES)
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits: $(OUT)/README.md
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	mkdir -p $(OUT)
	> $@
	echo 'This directory contains a Coq’ified version of the Haskell $(SRC) library' >> $@
	echo 'Do not edit files here! Instead, look in `examples/$(SRC)`.' >> $@


coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)

HS_TO_COQ_OPTS := \
  -e ../../base/edits \
  -e edits \
  --iface-dir ../../base \
  --iface-dir $(OUT) \
  --dependency-dir deps/ \
  -N \
  -i $(SRC) \
  -i $(SRC)/tests \
  -i $(SRC)/dist-install/build \
  -I $(SRC)/include \
  -o $(OUT) \

include  deps/*.mk

.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) $(wildcard module-edits/$$*/flags) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_OPTS) \
	             $(addprefix `cat , $(addsuffix ` , $(wildcard module-edits/$*/flags))) \
	             $(wildcard $(SRC)/$*.hs) $(wildcard $(SRC)/tests/$*.hs)
	test -e $@

$(VFILES_DROPIN): $(OUT)/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             $(HS_TO_COQ_OPTS) \
	             drop-in/$*.hs

.SECONDEXPANSION:
$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

%.h2ci: %.v
	test -e $@

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
