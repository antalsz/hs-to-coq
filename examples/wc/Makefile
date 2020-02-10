include ../../common.mk

OUT=lib

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
   Types \
   SimpleFold \
   InlinedBSFold \
   SimpleBSFold \
   BL \
   Monads \
   IO

# Generated modules
MODULES =  \
   MonoidBSFold \
   InlinedMonoidBSFold \
   Lazy \
   LazyUTFAgnostic \
   Simple \
   Stupid \
   Strict

# generated from drop-in/
DROPIN = \
   MultiCore \
   Control/Concurrent/Async


VFILES_GEN       = $(addsuffix .v,$(MODULES))
VFILES_MAN       = $(addsuffix .v,$(HANDMOD))
VFILES_DROPIN    = $(addsuffix .v,$(DROPIN))


VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_DROPIN)

OUTFILES_GEN       = $(addprefix $(OUT)/,$(VFILES_GEN))
OUTFILES_MAN       = $(addprefix $(OUT)/,$(VFILES_MAN))
OUTFILES_DROPIN    = $(addprefix $(OUT)/,$(VFILES_DROPIN))

OUTFILES   = $(OUTFILES_GEN) $(OUTFILES_MAN) $(OUTFILES_DROPIN)

HSFILES     = $(addsuffix .hs,$(MODULES)) 
HSFILESPATH = $(addprefix wc/src/,$(HSFILES)) 

all: vfiles coq

vfiles: $(OUT)/edits  $(OUT)/README.md $(OUT)/Makefile $(OUTFILES)

# This target is also used as a dependecy to ensure that $(OUT) exists.
$(OUT)/README.md:
	mkdir -p $(OUT)
	mkdir -p deps
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/wc`.' >> $@

$(OUT)/edits:
	mkdir -p $(OUT)
	ln -fs ../edits $(OUT)/edits

$(OUT)/_CoqProject: $(OUT)/README.md Makefile
	> $@
	echo '-Q . ""' >> $@
	echo '-Q ../../../base ""' >> $@
	echo '-Q ../../../base-thy  Proofs' >> $@
	echo '-Q ../../containers/lib   ""' >> $@
	echo '-Q ../../containers/theories  ""' >> $@
	echo '-Q ../../transformers/lib  ""' >> $@
	echo $(filter-out $(addsuffix .v,$(BROKEN_MODULES)), $(VFILES)) >> $@

$(OUT)/Makefile: $(OUT)/README.md $(OUT)/_CoqProject $(OUTFILES) Makefile
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

coq: $(OUT)/Makefile $(OUTFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)


HS_TO_COQ_OPTS=\
     -i wc/src \
     -e ../../base/edits \
     -e ../containers/edits \
     -e ../transformers/edits \
     -e edits \
     --iface-dir ../../base \
     --iface-dir ../containers/lib \
     --iface-dir ../transformers/lib \
     --iface-dir $(OUT) \
     --dependency-dir deps \
     -N \


-include deps/*.mk

%.h2ci: %.v
	test -e $@

.SECONDEXPANSION:
$(OUTFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_OPTS) -o $(OUT) wc/src/$*.hs
	test -e $@


$(OUTFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/


$(OUTFILES_DROPIN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) drop-in/%.hs
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_OPTS) -o $(OUT) drop-in/$*.hs


clean:
	rm -rf $(OUT)
	rm -f *.aux *.log

