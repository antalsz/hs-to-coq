HS_TO_COQ = stack exec hs-to-coq --
SHELL = bash

# tests that should pass
PASS = Expr \
       Sub \
       Self \
       Poly \
       Guard2 \
       InstCtx \
       OpTyCon \
       ExhaustGuard \
       MapAccumR \
       MutrecInst


# tests that *should* pass but currently fail
TODO_PASS  = EqList \
             PolyInstance2 \
             \
             Mutrec \
             DotName \
             PatternGuard \
             Bits

MODULES = $(PASS) $(TODO_PASS)

VFILES    = $(addsuffix .v,$(MODULES))
VOFILES   = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS  = ""

# typecheck *quietly*
TYPECHECK=coqc 1>/dev/null

all:  $(VFILES) pass todo_pass

pass: $(addsuffix .pass,$(PASS))
	@echo -------- END PASS ------------

todo_pass: $(foreach f,$(TODO_PASS),$(f).pass)
	@echo
	@echo "Any names printed without errors should be moved from TODO_PASS to PASS"

%.pass : %.v
	@/bin/echo -n "$<: "
	@if ! $(TYPECHECK) $< >&/dev/null; then echo -e "\033[1;31mfailed\033[0m (should pass)" >&2; else echo -e "\033[1;31mpassed\033[0m"; fi

%.vo : %.v
	@coqc $*.v

%.v : %/edits renamings %/preamble.v %.hs
	@$(HS_TO_COQ) -e $*/edits -r renamings -o . -p $*/preamble.v $*.hs 1>/dev/null


clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d *.glob $(VFILES) _CoqProject Makefile.coq *~

.SECONDARY: $(VFILES)
