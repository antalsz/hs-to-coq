include ../../common.mk

# tests that should pass
PASS = \
  Simple \
  Self \
  Poly \
  Irrefutable \
  LocalTopoSort \
  InstCtx \
  ExhaustGuard \
  PartialAppliedPolyDataCon \
  NonStructuralRec \
  DotName \
  MapAccumR \
  Sub \
  FTP \
  AddAndReplace \
  FTPDefault \
  PolyInstance2 \
  PolyInstance3 \
  Bits \
  BitsRewrite \
  PatternGuard \
  Guard2 \
  Notations \
  Renamed \
  RenameModule \
  Mutrec \
  GADT \
  Underscore_Module \
  LetPattern \
  AxiomatizeModule \
  RedefineAddAxiom \
  AddTheorem \
  Existential \
	SkipConstructor \
	SkipMatches

# tests that *should* pass but currently fail
TODO_PASS = \
  InstVar \
  TypeAnnotations \
  StrictPair \
  MutrecInst \
  TopBind

# tests that *should* pass but currently don't even translate
TODO_TRANSLATE = \


MODULES = $(PASS) $(TODO_PASS) $(TODO_TRANSLATE)

VFILES    = $(addsuffix .v,$(MODULES)) Renamed.v
VOFILES   = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS  = ""

# typecheck *quietly*
TYPECHECK=coqc 1>/dev/null

main:
	# Call ourselves with -k, so that we see all test outputs,
	# even if some fail
	$(MAKE) -k all

all:  $(VFILES) pass todo_pass todo_translate

pass: $(addsuffix .pass,$(PASS))
	@echo
	@echo -------- END PASS ------------
	@echo

todo_pass: $(foreach f,$(TODO_PASS),$(f).fail)
	@echo
	@echo "Any names printed without errors should be moved from TODO_PASS to PASS"
	@echo -------- END FAIL ------------
	@echo
	@echo "(Errors are expected from now on)"
	@echo

todo_translate: $(foreach f, $(TODO_TRANSLATE), $(f).fail_translate)
	@echo
	@echo "Any names that fail should be moved from TODO_TRANSLATE to TODO_PASS"
	@echo "Any names that pass should be moved from TODO_TRANSLATE to PASS"
	@echo -------- END UNTRANSLATABLE ------------

%.pass : %.v
	@/bin/echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m (should pass)"; exit 1;\
	 elif ! $(TYPECHECK) $< >&/dev/null;\
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

%.fail_translate : %.v
	@/bin/echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m"; \
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;33mfailed\033[0m (unexpected)"; exit 1;\
	 else echo -e "\033[1;32mpassed\033[0m (unexpected)"; exit 1; \
	 fi

%.vo : %.v
	@coqc -Q . "" $*.v

.SECONDEXPANSION:
%.v : FORCE $$(wildcard $*/edits) $$(wildcard $*/preamble.v) %.hs
	@rm -f $*.v
	@if [ -e $*/preamble.v ]; then P_ARG="--preamble $*/preamble.v"; else P_ARG=; fi;\
	 if [ -e $*/midamble.v ]; then M_ARG="--midamble $*/midamble.v"; else M_ARG=; fi;\
	 if [ -e $*/edits ];      then E_ARG="--edits    $*/edits";      else E_ARG=; fi;\
	 $(HS_TO_COQ) $${E_ARG} -N -e renamings -o . $${P_ARG} $${M_ARG} $*.hs 1>/dev/null || true

Renamed.v: RenameMe.hs RenameMe.hs-boot RenameMeToo.hs RenameMe/edits
	@rm -f Renamed.v
	$(HS_TO_COQ) -N -e RenameMe/edits -e renamings -o . RenameMe.hs RenameMeToo.hs 1>/dev/null

RenameModule.v:: Renamed.vo

# We always want to re-build the .v files, to test the current build of hs-to-coq
FORCE:

clean:
	rm -rf */*.vo */*.glob */*.v.d *.vo *.v.d *.glob *.hi *.o *.hi-boot *.o-boot $(VFILES) _CoqProject Makefile.coq *~

.SECONDARY: $(VFILES)
