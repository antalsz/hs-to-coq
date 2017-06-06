# tests that should pass
PASS = Expr \
       Poly

# tests that *should* pass but currently fail
TODO_PASS  = EqList \
             Self \
             MutrecInst \
             \
             Mutrec \
             DotName \
             PatternGuard

MODULES = $(PASS) $(TODO_PASS)

VFILES   = $(addsuffix .v,$(MODULES))
VOFILES  = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS = ""

# typecheck *quietly*
TYPECHECK=coqc 1>/dev/null

all:  $(VFILES) pass todo_pass

pass: $(addsuffix .pass,$(PASS))

todo_pass: $(foreach f,$(TODO_PASS),$(f).pass)
	@echo
	@echo "Any names printed without errors should be moved from TODO_PASS to PASS"

%.pass : %.v
	@/bin/echo -n "$<: "
	@if ! $(TYPECHECK) $< >&/dev/null; then echo "\033[1;31mfailed\033[0;30m (should pass)" >&2; else echo "\033[1;31mpassed\033[0;30m"; fi

%.vo : %.v
	@coqc $*.v

%.v : %/edits renamings %/preamble.v %.hs
	@stack exec hs-to-coq -- -e $*/edits -r renamings -o $*.v -p $*/preamble.v $*.hs 1>/dev/null


clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d *.glob $(VFILES) _CoqProject Makefile.coq *~

.SECONDARY: $(VFILES)
