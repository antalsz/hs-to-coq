HS_TO_COQ = stack exec hs-to-coq --
SHELL = bash
LIB = /Users/sweirich/github/hs-to-coq/ghc-8.0.2/libraries/base

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-coq is improved.

# GHC/Unicode needs precedence resolution, plus a few issues with unicode constants
# Data/Char needs a show instance.  Also use of data cons separate from definition.
# Data/Monoid redefines the notation "<>" (at a different level). Need to sort this out.

# Handwritten modules (usually by modification of generated version)
HANDMOD = GHC/Prim \
          GHC/Num \
	       GHC/Char \
          GHC/Enum \
          GHC/Real \
          GHC/Unicode \
          GHC/Base \
          Data/Char \
          Data/Bits \
          Data/Eq \
          Data/Type/Equality \
          GHC/Word \
          GHC/Int \
          Data/Bool \
          Prelude

# Generated modules
# All except BaseGen are generated directly from GHC/libraries/base
MODULES  = GHC/BaseGen \
           GHC/List \
           Data/Tuple \
           Data/Maybe \
           Data/Function \
           Data/Ord \
           Data/Monoid

#           Data/OldList \

VFILES   = $(addsuffix .v,$(MODULES))
VOFILES  = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS = ""

all:  $(VFILES) coq

_CoqProject : Makefile
	echo "-R . Top" > _CoqProject
	echo $(addsuffix .v,$(HANDMOD)) >> _CoqProject
	echo $(VFILES) >> _CoqProject

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES) GHC/Prim.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)


%.v : %/edits renamings %/preamble.v
	$(HS_TO_COQ) -e $*/edits -r renamings -o $*.v -p $*/preamble.v $(LIB)/$*.hs


GHC/BaseGen.v : GHC/Base/edits renamings GHC/Base/preamble.v GHC/Base.hs
	$(HS_TO_COQ) -e GHC/Base/edits -r renamings -o GHC/BaseGen.v -p GHC/Base/preamble.v GHC/Base.hs


clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d  $(VFILES) _CoqProject Makefile.coq  */*.v~


.SECONDARY: $(VFILES)
