include ../../common.mk

ifeq (,$(wildcard base))
$(error Please create a symlink base (see README.md))
endif

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
  Data/Functor/Const \
  GHC/Err \
  GHC/Unicode \
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
  Data/Traversable \
  Control/Monad/Fail \
  Data/Foldable \
  Control/Arrow \
  Data/Functor/Identity \
  Data/Functor/Sum \
  Data/Functor/Product \
  Control/Applicative \
  Data/Functor/Classes \
  Control/Category \
  Data/Bifunctor \
  Data/List/NonEmpty \
  Data/Semigroup \
  Data/Semigroup/Internal \


# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES =


VFILES_GEN = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VFILES_MAN = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES   = $(VFILES_GEN) $(VFILES_MAN) $(VFILES_SPECIAL) $(VFILES_DROPIN)

all:  $(OUT)/edits $(OUT)/README.md $(VFILES) coq

$(OUT)/_CoqProject : Makefile
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
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


.SECONDEXPANSION:
$(VFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
	             -e edits \
           -N \
		     -i base \
		     -i base/dist-install/build \
		     -I base/include \
		     --ghc -this-unit-id --ghc base \
		     -o $(OUT) \
		     base/$*.hs
	test -e $@

$(VFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../examples/base-src/manual $(OUT)/


$(VFILES_DROPIN): $(OUT)/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs
	$(HS_TO_COQ) -e module-edits/$*/edits \
	             -e edits \
		     -o $(OUT) \
		     -N \
		     -p module-edits/$*/preamble.v \
		     --ghc -ibase \
		     --ghc -ibase/dist-install/build \
		     -Ibase/include \
		     --ghc -this-unit-id=base \
		     drop-in/$*.hs

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
