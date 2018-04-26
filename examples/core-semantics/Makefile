include ../../common.mk

ifeq (,$(wildcard ghc-core-smallstep))
$(error Please create a symlink ghc-core-smallstep (see README.md))
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
VFILES_CORE = $(addprefix $(OUT)/,$(addsuffix .v,$(CORE_MODULES)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_CORE)

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
	echo '-Q ../../ghc/lib  ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(CORE_MODULES)) >> $@

$(OUT)/Makefile: $(OUT) $(OUT)/_CoqProject $(VFILES)
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits: $(OUT)
	ln -fs ../edits $(OUT)/edits

$(OUT)/README.md:
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC-CORE-SMALLSTEP' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc-core-smallstep`.' >> $@

coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)


.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
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
		     ghc-core-smallstep/$*.hs
	test -e $@
# We added the `test` because `hs-to-coq` doesn't return an error



$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/

clean:
	rm -rf $(OUT)
	rm -f *.aux *.log
