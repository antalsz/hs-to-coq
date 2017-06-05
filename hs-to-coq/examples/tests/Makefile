MODULES  = EqList \
           Poly \
           Self \
           Mutrec

VFILES   = $(addsuffix .v,$(MODULES))
VOFILES  = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS = ""

all:  $(VFILES) coq

_CoqProject : Makefile $(VFILES)
	echo "-R . HS" > _CoqProject
#	echo $(addsuffix .v,$(HANDMOD)) >> _CoqProject
	echo $(VFILES) >> _CoqProject

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

%.vo : %.v
	coqc $*.v

%.v : %/edits renamings %/preamble.v %.hs
	stack exec hs-to-coq -- -e $*/edits -r renamings -o $*.v -p $*/preamble.v $*.hs


clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d *.glob $(VFILES) _CoqProject Makefile.coq *~

.SECONDARY: $(VFILES)
