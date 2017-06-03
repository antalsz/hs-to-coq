LIB = /Users/sweirich/github/hs-to-coq/ghc-8.0.2/libraries/base

MODULES  = GHC/Base GHC/List Data/Tuple Data/Maybe Data/Bool Data/Function

VFILES   = $(addsuffix .v,$(MODULES))
VOFILES  = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS = ""

all:  $(VFILES) coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES) GHC/Prim.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)


%.v : %/edits renamings %/preamble.v
	stack exec hs-to-coq -- -e $*/edits -r renamings -o $*.v -p $*/preamble.v $(LIB)/$*.hs


GHC/Base.v : GHC/Base/edits renamings GHC/Base/preamble.v GHC/Base.hs
	stack exec hs-to-coq -- -e GHC/Base/edits -r renamings -o GHC/Base.v -p GHC/Base/preamble.v GHC/Base.hs




clean:
	rm -f */*.vo */*.glob Makefile.coq $(VFILES)

.SECONDARY: $(VFILES)
