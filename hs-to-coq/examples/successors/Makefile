HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

all: Successors.vo


Successors.v: Successors.hs edits preamble.v
	$(HS_TO_COQ) -e edits -p preamble.v  Successors.hs -o Successors.v
	sed -e 's,{list},,' -i Successors.v

Successors.vo: Successors.v
	coqc -R ../ghc-base/ 'Top' Successors.v

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d Successors.v _CoqProject Makefile.coq  */*.v~
