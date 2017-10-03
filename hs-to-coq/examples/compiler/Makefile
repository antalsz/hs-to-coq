HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif
SHELL = bash

all: coq

CompilerRev.v: CompilerRev.hs edits ../ghc-base/renamings
	$(HS_TO_COQ) -e edits -r ../ghc-base/renamings CompilerRev.hs -o .

Compiler.v: Compiler.hs edits ../ghc-base/renamings
	$(HS_TO_COQ) -e edits -r ../ghc-base/renamings Compiler.hs -o .

CompilerOrig.v: CompilerOrig.hs edits ../ghc-base/renamings
	$(HS_TO_COQ) -e edits -r ../ghc-base/renamings CompilerOrig.hs -o .

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq Compiler.v CompilerOrig.v Proofs.v ProofsOrig.v CompilerRev.v ProofsRev.v
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d CompilerOrig.v Compiler.v CompilerRev.v Makefile.coq  */*.v~
