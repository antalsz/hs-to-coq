HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run -v0 exe:hs-to-coq --
endif
SHELL = bash

SRC=riscv-semantics/src

ifeq (,$(wildcard $(SRC)))
$(error Please create a symlink to input source location)
endif

OUT=lib

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  Program

MODULES = \
  Decode \
  ExecuteI



# Generated modules
# generated directly from GHC/libraries/containers/tests
TEST_MODULES = \


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))

VFILES = $(VFILES_GEN) $(VFILES_MAN)

all:  $(VFILES) coq

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo '-R ../../../base ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject $(VFILES)
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile


coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)


.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard $$(SRC)/$$*.hs) $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) $(wildcard module-edits/$$*/flags) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
	             -e ../base-src/edits \
	             -e edits \
	             -N \
	             -i $(SRC) \
	             $(addprefix `cat , $(addsuffix ` , $(wildcard module-edits/$*/flags))) \
	             -o $(OUT) \
	             $(wildcard $(SRC)/$*.hs)
	if [[ -e $(OUT)/Main.v && ( ! -e $@ || $(OUT)/Main.v -nt $@ ) ]]; then mv $(OUT)/Main.v $@; fi
	test -e $@ && test \! -e $(OUT)/Main.v

$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/


clean:
	rm -rf $(OUT)
