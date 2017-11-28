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
  Irrefutable \
  InstCtx \
  Guard2 \
  ExhaustGuard \
  PartialAppliedPolyDataCon \
  PatternGuard \
  NonStructuralRec \
  DotName \
  MapAccumR \
  Sub \
  FTP \
  AddAndReplace \
  FTPDefault \
  PolyInstance2 \
  PolyInstance3 \
  MutrecInst


# tests that *should* pass but currently fail
TODO_PASS  = \
  EqList \
  Endo \
  NestedRec \
  InstVar \
  Expr \
  Mutrec \
  PaperExamples \
  OpTyCon \
  Existential \
  Bits

MODULES = $(PASS) $(TODO_PASS)

VFILES    = $(addsuffix .v,$(MODULES))
VOFILES   = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS  = ""

# typecheck *quietly*
TYPECHECK=coqc 1>/dev/null

main:
	# Call ourselves with -k, so that we see all test outputs,
	# even if some fail
	$(MAKE) -k all

all:  $(VFILES) pass todo_pass

pass: $(addsuffix .pass,$(PASS))
	@echo -------- END PASS ------------

todo_pass: $(foreach f,$(TODO_PASS),$(f).fail)
	@echo
	@echo "Any names printed without errors should be moved from TODO_PASS to PASS"

%.pass : %.v
	@/bin/echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m (should pass)"; exit 1;\
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;31mfailed\033[0m (should pass)"; exit 1;  \
	 else echo -e "\033[1;32mpassed\033[0m"; \
	 fi

%.fail : %.v
	@/bin/echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m"; \
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;31mfailed\033[0m"; \
	 else echo -e "\033[1;32mpassed\033[0m (unexpected)"; exit 1; \
	 fi

%.vo : %.v
	@coqc $*.v

.SECONDEXPANSION:
%.v : FORCE $$(wildcard $*/edits) renamings $$(wildcard $*/preamble.v) %.hs
	@rm -f $*.v
	@if [ -e $*/preamble.v ]; then P_ARG="-p $*/preamble.v"; else P_ARG=; fi;\
	if [ -e $*/edits ]; then E_ARG="-e $*/edits"; else E_ARG=; fi;\
	$(HS_TO_COQ) $${E_ARG} -e renamings -o . $${P_ARG} $*.hs 1>/dev/null

# We always want to re-build the .v files, to test the current build of hs-to-coq
FORCE:

clean:
	rm -rf */*.vo */*.glob */*.v.d *.vo *.v.d *.glob $(VFILES) _CoqProject Makefile.coq *~

.SECONDARY: $(VFILES)
