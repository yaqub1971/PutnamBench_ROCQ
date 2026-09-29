#!/usr/bin/env bash
# Verification of the extended set (extended/<problem>/). Run from anywhere:
#   bash extended/verify.sh              # every problem folder
#   bash extended/verify.sh putnam_2001_b2 putnam_1977_b5   # selected folders
#   CHK=1 bash extended/verify.sh        # additionally run coqchk/rocqchk on every proof (slow)
# Needs coqc or rocq (Coq 8.18 / MathComp 2.1 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1,
# the environment the files were verified on, or the CI toolchain) and curl for step 4.
# For every folder it performs:
#   1. compile, in dependency order: <p>.v (the upstream copy; may legitimately fail for the
#      "compile" verdicts -- reported, not fatal), <p>_corrected.v (must compile), the
#      evidence file <p>_statement_is_{false,vacuous}.v if present (must compile), and
#      <p>_corrected_proof.v if present (must compile). Any warning from a file's own
#      lines (as opposed to the library import lines) is a failure.
#   2. proof hygiene: <p>_corrected_proof.v declares no notation, tactic, axiom or
#      parameter, contains no admit/Admitted, and its only Set Warnings lines are the
#      marked compat lines.
#   3. Print Assumptions of the proved theorem: only the statement's own Variable, the
#      classical axioms of mathcomp.classical (boolp.*), the axioms behind the standard
#      library's reals (ClassicalDedekindReals.*, functional_extensionality_dep),
#      Classical_Prop.classic, and Extensionality_Ensembles are accepted.
#      For an evidence file, the admitted upstream theorem must be among its assumptions
#      (False derivation) or the file must be closed under the global context (vacuity proof).
#   4. statement integrity: <p>.v is the upstream PutnamBench file at the pinned commit
#      apart from its header comment and the marked compat lines; every non-blank line of
#      <p>_corrected.v (header removed) occurs, in order, in <p>_corrected_proof.v, and the
#      Theorem block (Theorem ... up to Proof) is identical in both.
#   5. (CHK=1) independent kernel check of every proof.
# On success the build products it created are removed; on failure they are kept.
set -uo pipefail
cd "$(dirname "$0")"
COMMIT=4dbe26ef21563af851eedaeb82d936fe1f94fc52
UP="https://raw.githubusercontent.com/trishullab/PutnamBench/$COMMIT/coq/src"
if command -v rocq >/dev/null 2>&1; then COMPILE="rocq compile"; CHKCMD="rocqchk"; VER="$(rocq --version | head -1)"
else COMPILE="coqc"; CHKCMD="coqchk"; VER="$(coqc --version | head -1)"; fi
echo "toolchain: $VER  ($COMPILE)"
fail=0; nprob=0; nproof=0
ok()  { echo "OK   $*"; }
bad() { echo "FAIL $*"; fail=1; }
note(){ echo "NOTE $*"; }

# header = the leading (* ====...==== *) box; compat lines = the three marked kinds
strip() { awk 'BEGIN{h=1} h&&/^   =+ \*\)$/{h=0; getline; next} h{next} !/^(Set Warnings "[^"]*"\.|From mathcomp Require Import ssralg\.|Local Open Scope classical_set_scope\.) \(\* compat: /{print}' "$1"; }
thm()   { sed -n '/^Theorem/,/^Proof/p' | sed '$d'; }
compile_one() { # file (in cwd)  -> 0 ok, 1 error, 2 own-line warnings
  local f=$1
  if $COMPILE -R . "" "$f" > "$f.log" 2>&1; then
    local imp own
    imp=$(grep -n -E '^From |^Require |^Import |^Local Notation R := ' "$f" | cut -d: -f1 | paste -s -d '|' -)
    own=$(grep '^File "' "$f.log" | grep -vcE "line (${imp:-0})," || true)
    [ "$own" = "0" ] && return 0
    awk -v P="line (${imp:-0})," '/^File "/{show=($0 !~ P)} show{print}' "$f.log" | head -20
    return 2
  else
    grep -A8 "^Error" "$f.log" | head -20; return 1
  fi
}
pa() { # module theorem tag -> writes ci_pa_<tag>.names; returns 0 if the query ran
  printf 'Require %s.\nPrint Assumptions %s.%s.\n' "$1" "$1" "$2" > "ci_pa_$3.v"
  $COMPILE -R . "" "ci_pa_$3.v" > "ci_pa_$3.log" 2>&1 || return 1
  sed -n '/^Axioms:/,$p' "ci_pa_$3.log" | grep -v '^Axioms:' | grep -v '^ ' | sed 's/ .*//' > "ci_pa_$3.names"
  return 0
}
ALLOWED='^boolp\.|^([A-Za-z0-9_]+\.)*ClassicalDedekindReals\.sig_not_dec$|^([A-Za-z0-9_]+\.)*ClassicalDedekindReals\.sig_forall_dec$|^([A-Za-z0-9_]+\.)*FunctionalExtensionality\.functional_extensionality_dep$|^([A-Za-z0-9_]+\.)*Classical_Prop\.classic$|^([A-Za-z0-9_]+\.)*Extensionality_Ensembles$'

if [ $# -gt 0 ]; then PROBLEMS="$*"; else PROBLEMS=$(ls -d putnam_* 2>/dev/null | tr '\n' ' '); fi
mkdir -p ci_upstream
for p in $PROBLEMS; do
  [ -d "$p" ] || { bad "$p: no such folder"; continue; }
  nprob=$((nprob+1)); echo; echo "### $p"
  pushd "$p" > /dev/null
  rm -f -- *.vo *.vos *.vok *.glob .*.aux ci_pa_* 2>/dev/null
  up_ok=0
  # every .v file must start with the header box, otherwise strip() would empty it and the diffs below would pass vacuously
  for f in "$p.v" "${p}_corrected.v" "${p}_corrected_proof.v" "${p}_statement_is_false.v" "${p}_statement_is_vacuous.v"; do
    [ -f "$f" ] || continue
    head -1 "$f" | grep -qE '^\(\* =+$' && [ -n "$(strip "$f")" ] || bad "$f: header box missing or malformed (must start with '(* ====' and end with '   ==== *)')"
  done
  # --- 1. compile
  if [ -f "$p.v" ]; then
    if compile_one "$p.v"; then ok "$p.v (upstream copy) compiles"; up_ok=1
    else note "$p.v (upstream copy) does not compile on this toolchain (expected for the 'compile' verdicts)"; fi
  else bad "$p.v missing"; fi
  if [ -f "${p}_corrected.v" ]; then
    case $(compile_one "${p}_corrected.v"; echo $?) in
      0) ok "${p}_corrected.v compiles";; 2) bad "${p}_corrected.v has warnings from its own lines";; *) bad "${p}_corrected.v does not compile";; esac
    grep -q '^Proof\. Admitted\.' "${p}_corrected.v" && ok "${p}_corrected.v ends in Admitted (statement only)" || bad "${p}_corrected.v should end in 'Proof. Admitted.'"
  else bad "${p}_corrected.v missing"; fi
  ev=$(ls "${p}_statement_is_false.v" "${p}_statement_is_vacuous.v" 2>/dev/null | head -1)
  if [ -n "$ev" ]; then
    case $(compile_one "$ev"; echo $?) in
      0) ok "$ev compiles";; 2) bad "$ev has warnings from its own lines";; *) bad "$ev does not compile";; esac
  fi
  pf="${p}_corrected_proof.v"; has_proof=0
  if [ -f "$pf" ]; then
    has_proof=1; nproof=$((nproof+1))
    case $(compile_one "$pf"; echo $?) in
      0) ok "$pf compiles";; 2) bad "$pf has warnings from its own lines";; *) bad "$pf does not compile";; esac
    # --- 2. hygiene
    # (section-local Variable/Hypothesis are fine: they are discharged; an undischarged one shows up in Print Assumptions)
    pat='^ *(Local |Global )?(Notation|Reserved Notation|Infix|Ltac|Ltac2|Axiom|Axioms|Parameter|Parameters|Conjecture) |Admitted\.|(^|[^A-Za-z_])admit([^A-Za-z_]|$)'
    if grep -nE "$pat" "$pf" | grep -vE '^[0-9]+: *Set Warnings' >/dev/null
    then bad "$pf declares a notation/tactic/axiom/parameter or contains admit/Admitted:"; grep -nE "$pat" "$pf"
    else ok "$pf: no notation, tactic, axiom or parameter declarations, no admit/Admitted"; fi
    # (a top-level Variable other than the statement's own would show up in Print Assumptions below)
    if grep -nE '^Set Warnings' "$pf" | grep -v 'compat:' >/dev/null; then bad "$pf has a Set Warnings line that is not a marked compat line"; fi
    # --- 3. Print Assumptions
    thmname=$(grep -oE '^Theorem +[A-Za-z0-9_]+' "${p}_corrected.v" | head -1 | awk '{print $2}')
    if [ -n "$thmname" ] && pa "${p}_corrected_proof" "$thmname" proof; then
      if grep -q 'Closed under the global context' ci_pa_proof.log; then ok "$thmname: closed under the global context (no axioms)"
      else
        unexpected=$(grep -vE "$ALLOWED|^${p}_corrected_proof\.[A-Za-z0-9_]+\$" ci_pa_proof.names || true)
        # a <module>.<name> assumption must be a Variable of the statement
        for a in $(grep -E "^${p}_corrected_proof\." ci_pa_proof.names); do v=${a#*.}; grep -qE "^ *(Variable|Variables) .*\b$v\b" "${p}_corrected.v" || unexpected="$unexpected $a"; done
        if [ -z "$unexpected" ]; then ok "$thmname: assumptions are only the statement's Variable(s) and library axioms: $(tr '\n' ' ' < ci_pa_proof.names)"
        else bad "$thmname has unexpected assumptions: $unexpected"; fi
      fi
    else bad "Print Assumptions of $thmname in $pf could not be run"; fi
    # --- 4b. statement integrity: corrected lines occur in order in the proof file; Theorem block identical
    if diff <(strip "${p}_corrected.v" | thm) <(strip "$pf" | thm) >/dev/null
    then ok "$pf: Theorem block identical to ${p}_corrected.v"; else bad "$pf: Theorem block differs from ${p}_corrected.v"; fi
    # (import lines are excluded: the proof may extend them, as the root B5 proof does)
    missing=$(strip "${p}_corrected.v" | grep -v '^$' | grep -vE '^\(\*.*\*\)$|^(From |Require |Import |Proof\.)' | awk 'NR==FNR{stmt[++n]=$0; next} {if (i<n && $0==stmt[i+1]) i++} END{for(j=i+1;j<=n;j++) print stmt[j]}' - <(strip "$pf") 2>/dev/null)
    if [ -z "$missing" ]; then ok "$pf: every non-import statement line of ${p}_corrected.v occurs in it, in order"
    else bad "$pf: statement lines of ${p}_corrected.v missing or out of order:"; echo "$missing" | head -10; fi
    # --- 4c. semantic agreement (guards against a helper Definition/Notation/Import in the proof file
    # silently changing the meaning of the textually identical statement): under Set Printing All,
    # the type of the theorem and the bodies of the statement's Definitions must print identically
    # from both modules, up to the module prefix
    if [ -n "$thmname" ] && [ -f "${p}_corrected.vo" ] && [ -f "${p}_corrected_proof.vo" ]; then
      defs=$(grep -oE '^Definition +[A-Za-z0-9_]+' "${p}_corrected.v" | awk '{print $2}')
      for m in "${p}_corrected" "${p}_corrected_proof"; do
        { echo "Require $m."; echo "Set Printing All. Set Printing Width 1000000. Set Printing Depth 10000000."
          echo "Check $m.$thmname."; for d in $defs; do echo "Print $m.$d."; done; } > "ci_same_$m.v"
        $COMPILE -w none -R . "" "ci_same_$m.v" > "ci_same_$m.log" 2>&1 || bad "ci_same_$m.v: could not print the statement of module $m"
      done
      if diff <(grep -v '^$' "ci_same_${p}_corrected.log") <(sed "s/${p}_corrected_proof\./${p}_corrected./g" "ci_same_${p}_corrected_proof.log" | grep -v '^$') > ci_same.diff
      then ok "$pf: the theorem's type and the statement's Definitions print identically (Set Printing All) in both modules"
      else bad "$pf: the statement differs semantically from ${p}_corrected.v (Set Printing All):"; head -20 ci_same.diff; fi
    fi
  fi
  # evidence assumptions
  if [ -n "$ev" ] && [ "$up_ok" = 1 ]; then
    evthm=$(grep -oE '^(Lemma|Theorem) +[A-Za-z0-9_]+' "$ev" | tail -1 | awk '{print $2}')
    if [ -n "$evthm" ] && pa "${ev%.v}" "$evthm" ev; then
      case $ev in
        *_is_false.v) grep -qxE "($p\.)?$p" ci_pa_ev.names && ok "$ev: assumes the admitted upstream theorem $p (False follows from it)" || bad "$ev: the admitted upstream $p is not among its assumptions: $(tr '\n' ' ' < ci_pa_ev.names)";;
        *) if grep -q 'Closed under the global context' ci_pa_ev.log; then ok "$ev: closed under the global context"
           else unexpected=$(grep -vE "$ALLOWED|^${ev%.v}\.R\$" ci_pa_ev.names || true); [ -z "$unexpected" ] && ok "$ev: only library axioms / the statement's R: $(tr '\n' ' ' < ci_pa_ev.names)" || bad "$ev has unexpected assumptions: $unexpected"; fi;;
      esac
    else note "$ev: could not run Print Assumptions (no Lemma/Theorem found or query failed)"; fi
  fi
  # --- 4a. upstream copy vs PutnamBench
  if [ -f "$p.v" ]; then
    if [ -f "../ci_upstream/$p.v" ] || curl -sSfL -o "../ci_upstream/$p.v" "$UP/$p.v"; then
      if diff <(awk '{print}' "../ci_upstream/$p.v") <(strip "$p.v") >/dev/null
      then ok "$p.v: identical to upstream PutnamBench ${COMMIT:0:7} apart from header and compat lines"
      else bad "$p.v differs from upstream:"; diff <(awk '{print}' "../ci_upstream/$p.v") <(strip "$p.v") | head -10; fi
    else note "$p.v: could not download upstream for comparison"; fi
  fi
  # --- 5. kernel check
  if [ "${CHK:-0}" = 1 ] && [ "$has_proof" = 1 ]; then
    if $CHKCMD -R . "" "${p}_corrected_proof" > "ci_chk.log" 2>&1 && grep -q "Modules were successfully checked" ci_chk.log
    then ok "$CHKCMD ${p}_corrected_proof"; else bad "$CHKCMD ${p}_corrected_proof:"; tail -n 10 ci_chk.log; fi
  fi
  popd > /dev/null
done

echo
echo "checked $nprob problem folder(s), $nproof with a proof file"
if [ "$fail" = "0" ]; then
  echo "ALL CHECKS PASSED"
  for p in $PROBLEMS; do ( cd "$p" 2>/dev/null && rm -f -- *.vo *.vos *.vok *.glob *.log .*.aux ci_pa_* .ci_pa_*.aux ci_same_* .ci_same_*.aux ci_same.diff ci_chk.log .lia.cache .nia.cache .lra.cache .nra.cache ); done
  rm -rf ci_upstream
  echo "(build products and logs removed)"
else
  echo "SOME CHECKS FAILED (build products and .log files kept for inspection)"
fi
exit $fail
