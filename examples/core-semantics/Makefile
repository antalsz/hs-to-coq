include ../../common.mk

SRC=ghc-core-smallstep

ifeq (,$(wildcard $(SRC)))
$(error Please create a symlink to $(SRC) (see README.md))
endif

OUT=lib

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \

# Generated modules
# generated directly from ghc-core-smallstep/compiler/*/
MODULES = \
  GHC/SmallStep


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN)

all: vfiles coq

vfiles: $(OUT)/edits  $(OUT)/README.md $(OUT)/Makefile $(VFILES)

$(OUT)/_CoqProject : Makefile
	> $@
	echo '-Q . ""' >> $@
	echo '-R ../../../base ""' >> $@
	echo '-Q ../../../base-thy  Proofs' >> $@
	echo '-Q ../../containers/lib   ""' >> $@
	echo '-Q ../../transformers/lib  ""' >> $@
	echo '-Q ../../ghc/lib  ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@

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
  --ghc -package=ghc-boot-th \
  --ghc -package=ghc \
  -e ../../base/edits \
  -e ../containers/edits \
  -e ../transformers/edits \
  -e ../ghc/edits \
  -e ../ghc/no-type-edits \
  -e edits \
   --iface-dir ../../base \
   --iface-dir ../containers/lib \
   --iface-dir ../transformers/lib \
   --iface-dir ../ghc/lib \
   --iface-dir $(OUT) \
  -N \
  -o $(OUT) \

include  deps/*.mk

.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_OPTS) \
		     $(SRC)/$*.hs
	test -e $@


.SECONDEXPANSION:
$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

%.h2ci: %.v
	test -e $@

clean:
	rm -rf $(OUT)
	rm -f *.aux *.log
