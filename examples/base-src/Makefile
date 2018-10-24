include ../../common.mk

OUT=../../base

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.
# see [notes.md] for discussion of issues

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  GHC/Wf \
  GHC/DeferredFix \
  GHC/DeferredFixImpl \
  GHC/Num \
  GHC/Char \
  GHC/Real \
  GHC/Enum \
  Data/Bits \
  GHC/Prim \
  GHC/Types \
  GHC/Tuple \
  Data/Type/Equality \
  GHC/Err \
  GHC/Nat \
  GHC/Unicode \
  GHC/MVar \
  Prelude\

# Generated modules
# generated directly from GHC/libraries/base
MODULES = \
  GHC/Base \
  Data/Maybe \
  GHC/List \
  Data/List \
  Data/OldList \
  Data/Bool \
  Data/Tuple \
  Data/Void \
  Data/Function \
  Data/Ord \
  Data/Functor \
  Data/Either \
  Data/Proxy \
  Control/Monad \
  Data/Monoid \
  Data/Functor/Utils \
  Data/Traversable \
  Control/Monad/Fail \
  Data/Foldable \
  Control/Arrow \
  Data/Functor/Identity \
  Data/Functor/Const \
  Control/Applicative \
  Data/Functor/Classes \
  Control/Category \
  Data/Bifunctor \
  Data/List/NonEmpty \
  Data/Semigroup \
  Data/Functor/Compose \
  Data/Functor/Product \
  Data/Functor/Sum \
  Data/Bifoldable \
  Data/Bitraversable \
  Control/Monad/Zip
  Control/Concurrent/MVar \

RENAMED = \
  Data/SemigroupInternal \


# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN     = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_RENAMED = $(addprefix $(OUT)/,$(addsuffix .v,$(RENAMED)))
VFILES_MAN     = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN  = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_SPECIAL) $(VFILES_DROPIN) $(VFILES_RENAMED)

all:  vfiles coq

vfiles: $(OUT)/edits $(OUT)/README.md $(OUT)/Makefile $(VFILES)

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(RENAMED)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/edits:
	mkdir -p $(OUT)
	ln -fs ../examples/base-src/edits $(OUT)/edits

$(OUT)/README.md:
	mkdir -p $(OUT)
	> $@
	echo 'This directory contains a Coq’ified version of the Haskell base library' >> $@
	echo 'Do not edit files here! Instead, look in `examples/base-src`.' >> $@

coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)

HS_TO_COQ_OPTS := \
    -e edits \
    -N \
    -i gen-files \
    -I gen-files \
    -i base \
    -I base/include \
    --iface-dir $(OUT) \
    --dependency-dir deps \
    --ghc -this-unit-id --ghc base \
    -o $(OUT)


include deps/*.mk

.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_OPTS) \
		     base/$*.hs
	test -e $@

# This is renamed, which confuses Make, so hence the special rule
$(OUT)/Data/SemigroupInternal.v : $(wildcard module-edits/Data/Semigroup/Internal/preamble.v) $(wildcard module-edits/Data/Semigroup/Internal/midamble.v)  $(wildcard module-edits/Data/Semigroup/Internal/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/Data/Semigroup/Internal/edits)) \
	             $(addprefix -p , $(wildcard module-edits/Data/Semigroup/Internal/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/Data/Semigroup/Internal/midamble.v)) \
		     $(HS_TO_COQ_OPTS) \
		     base/Data/Semigroup/Internal.hs
	test -e $(OUT)/Data/SemigroupInternal.v

$(VFILES_MAN): $(OUT)/% : manual/%
	rm -f $@
	lndir ../examples/base-src/manual $(OUT)/


$(VFILES_DROPIN): $(OUT)/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             -e edits \
		     $(HS_TO_COQ_OPTS) \
		     drop-in/$*.hs

# Every rule that builds a .v also produces the corresponding interface file
%.h2ci: %.v
	test -e $@

clean:
	rm -rf $(OUT)
	rm -f counts.pdf *.aux *.log

todo:
	-grep -a Parameter $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	-grep -a Axiom $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	-grep -a Admitted $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	-grep -a errorWithout $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v


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
