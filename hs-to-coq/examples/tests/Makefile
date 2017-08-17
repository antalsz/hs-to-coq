SHELL = bash

HAVE_STACK := $(shell command -v stack 2> /dev/null)
ifdef HAVE_STACK
HS_TO_COQ = stack exec hs-to-coq --
else
HS_TO_COQ = cabal new-run exe:hs-to-coq --
endif

# tests that should pass
PASS = \
  Simple \
  Self \
  Poly \
  InstCtx \
  Guard2 \
  ExhaustGuard \
  PartialAppliedPolyDataCon \
  PatternGuard \
  MapAccumR \
  FTP \
  FTPDefault \
  MutrecInst


# tests that *should* pass but currently fail
TODO_PASS  = \
  EqList \
  PolyInstance2 \
  Expr \
  Sub \
  Mutrec \
  DotName \
  OpTyCon \
  Successors \
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
	@if ! grep -q -F '(* Successfully converted the following code: *)' $<; \
	 then echo -e "\033[1;31mempty\033[0m (should pass)";\
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;31mfailed\033[0m (should pass)" >&2; \
	 else echo -e "\033[1;32mpassed\033[0m"; \
	 fi

%.vo : %.v
	@coqc $*.v

.SECONDEXPANSION:
%.v : FORCE $$(wildcard $*/edits) renamings $$(wildcard $*/preamble.v) %.hs
	@rm -f $*.v
	@if [ -e $*/preamble.v ]; then P_ARG="-p $*/preamble.v"; else P_ARG=; fi;\
	if [ -e $*/edits ]; then E_ARG="-e $*/edits"; else E_ARG=; fi;\
	$(HS_TO_COQ) $${E_ARG} -r renamings -o $*.v $${P_ARG} $*.hs 1>/dev/null

# We always want to re-build the .v files, to test the current build of hs-to-coq
FORCE:

clean:
	rm -f */*.vo */*.glob */*.v.d *.vo *.v.d *.glob $(VFILES) _CoqProject Makefile.coq *~

.SECONDARY: $(VFILES)
