include ../../common.mk

OUT = lib

PREAMBLE = translation/preamble.v
EDITS    = translation/edits

SOURCES = \
  functional-shuffle/src \
  MonadRandom \
  random

################################################################################

all: translate coq

translate: $(OUT) $(OUT)/Makefile

coq: $(OUT)/Makefile
	make -C $(OUT)

$(OUT)/_CoqProject: $(OUT) Makefile
	mkdir -p $(OUT)
	echo '-Q .                      ""' >  $@
	echo '-R ../../../base          ""' >> $@
	echo '-Q ../../containers/lib   ""' >> $@
	echo '-Q ../../transformers/lib ""' >> $@
	(cd $(OUT) && find . -name '*.v')   >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject
	cd $(OUT) && coq_makefile -f _CoqProject -o Makefile

$(OUT): $(PREAMBLE) $(EDITS) 
	mkdir -p $(OUT)
	$(HS_TO_COQ) \
	  -e ../../base/edits      --iface-dir ../../base          \
	  -e ../containers/edits   --iface-dir ../containers/lib   \
	  -e ../transformers/edits --iface-dir ../transformers/lib \
	  \
	  $(addprefix -i , $(SOURCES)) \
	  -p $(PREAMBLE) -e $(EDITS) \
	  \
	  --ghc -XCPP \
	  \
	  -o $(OUT) \
	  functional-shuffle/src/Data/List/Shuffle.hs

clean:
	@rm -rf .ghc-tmp $(OUT)
