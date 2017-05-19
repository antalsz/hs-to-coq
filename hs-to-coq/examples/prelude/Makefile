top: Prelude.vo

%.vo : %.hs Prelude.renamings Prelude.edits Prelude.preamble.v
	rm -f $*.v
	stack exec hs-to-coq -- -e Prelude.edits -r Prelude.renamings  -o $*.v -p Prelude.preamble.v $*.hs
	coqc $*.v
	chmod a-w $*.v

clean:
	rm -f *.vo *.glob
