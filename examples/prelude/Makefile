HS_TO_COQ = stack exec hs-to-coq --
SHELL = bash

top: Prelude.vo

%.vo : %.hs Prelude.renamings Prelude.edits Prelude.preamble.v
	rm -f $*.v
	$(HS_TO_COQ) -e Prelude.edits -e Prelude.renamings  -o $*.v -p Prelude.preamble.v $*.hs
	coqc $*.v
	chmod a-w $*.v

clean:
	rm -f *.vo *.glob
