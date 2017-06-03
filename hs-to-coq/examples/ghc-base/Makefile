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


%.v : %/edits renamings %/preamble.v %.hs
	rm -f $*.v
	stack exec hs-to-coq -- -e $*/edits -r renamings -o $*.v -p $*/preamble.v $*.hs

Data/Tuple.v : Data/Tuple/edits renamings Data/Tuple/preamble.v $(LIB)/Data/Tuple.hs
	stack exec hs-to-coq -- -e Data/Tuple/edits -r renamings -o Data/Tuple.v -p Data/Tuple/preamble.v $(LIB)/Data/Tuple.hs

Data/Maybe.v : Data/Maybe/edits renamings Data/Maybe/preamble.v $(LIB)/Data/Maybe.hs
	stack exec hs-to-coq -- -e Data/Maybe/edits -r renamings -o Data/Maybe.v -p Data/Maybe/preamble.v $(LIB)/Data/Maybe.hs

Data/Bool.v : renamings $(LIB)/Data/Bool.hs
	stack exec hs-to-coq -- -r renamings -o Data/Bool.v $(LIB)/Data/Bool.hs

Data/Function.v : renamings $(LIB)/Data/Function.hs
	stack exec hs-to-coq -- -e Data/Function/edits -r renamings -o Data/Function.v $(LIB)/Data/Function.hs

clean:
	rm -f */*.vo */*.glob Makefile.coq $(VFILES)

.SECONDARY: $(VFILES)
