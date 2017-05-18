top: Prelude.vo

%.vo : %.hs %.renamings %.edits %.preamble.v
	rm -f $*.v
	stack exec hs-to-coq -- -e $*.edits -r $*.renamings  -o $*.v -p $*.preamble.v $*.hs
	coqc $*.v
	chmod a-w $*.v

clean:
	rm -f *.vo *.glob
