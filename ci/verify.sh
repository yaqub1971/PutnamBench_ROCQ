#!/usr/bin/env bash
# Full verification of this repository. Run from anywhere: bash ci/verify.sh
# Needs Rocq 9.1 (or Coq 8.18+) with MathComp, MathComp-Analysis, zify and
# Algebra-Tactics; curl for the upstream comparison in step 4.
#   1. compile all 14 .v files in dependency order (fails on any error, and
#      reports any warning that comes from a file's own lines rather than the
#      library imports)
#   2. Print Assumptions: A5 and 1963 A2 closed; B5 only R + classical axioms;
#      the three False/vacuity derivations assume exactly the admitted upstream
#      theorem (or nothing)
#   3. independent kernel check (rocqchk / coqchk) of the three proofs
#   4. statement integrity: diff every statement against the upstream
#      PutnamBench files at the pinned commit, ignoring only the header comments
#      and the marked compat lines
set -uo pipefail
cd "$(dirname "$0")/.."
COMMIT=4dbe26ef21563af851eedaeb82d936fe1f94fc52
UP="https://raw.githubusercontent.com/trishullab/PutnamBench/$COMMIT/coq/src"

if command -v rocq >/dev/null 2>&1; then COMPILE="rocq compile"; CHK="rocqchk"; VER="$(rocq --version | head -1)"
else COMPILE="coqc"; CHK="coqchk"; VER="$(coqc --version | head -1)"; fi
echo "toolchain: $VER  ($COMPILE, $CHK)"
fail=0
step() { echo; echo "### $*"; }
ok()   { echo "OK   $*"; }
bad()  { echo "FAIL $*"; fail=1; }

PROOFS="putnam_1962_a5 putnam_1963_a2 putnam_1962_b5_corrected_proof"
FILES="$PROOFS audit_1962_a5 audit_1963_a2 \
 putnam_1962_b5 putnam_1962_b5_statement_is_false putnam_1962_b5_corrected \
 putnam_1962_a6 putnam_1962_a6_corrected putnam_1962_a6_statement_is_vacuous \
 putnam_1962_a2 putnam_1962_a2_statement_is_false putnam_1962_a2_corrected"

step "1. compile"
for f in $FILES; do
  if $COMPILE -R . "" "$f.v" > "$f.log" 2>&1; then
    imp=$(grep -n -E '^From mathcomp|^Require Import' "$f.v" | cut -d: -f1 | paste -s -d '|' -)
    own=$(grep '^File "' "$f.log" | grep -vcE "line ($imp)," || true)
    if [ "$own" = "0" ]; then ok "$f"; else
      bad "$f compiles but has $own warning(s) from its own lines:"
      awk -v P="line (${imp})," '/^File "/{show=($0 !~ P)} show{print}' "$f.log"
    fi
  else
    bad "$f does not compile:"; grep -A8 "^Error" "$f.log" | head -20
  fi
done

step "2. Print Assumptions"
pa() { # name  module  theorem
  printf 'Require %s.\nPrint Assumptions %s.%s.\n' "$2" "$2" "$3" > "ci_pa_$1.v"
  $COMPILE -R . "" "ci_pa_$1.v" > "ci_pa_$1.log" 2>&1 || { bad "Print Assumptions of $2.$3 failed to run"; return 1; }
  sed -n '/^Axioms:/,$p' "ci_pa_$1.log" | grep -v '^Axioms:' | grep -v '^ ' | sed 's/ .*//' > "ci_pa_$1.names"
  return 0
}
pa a5 putnam_1962_a5 putnam_1962_a5 && { grep -q "Closed under the global context" ci_pa_a5.log && ok "putnam_1962_a5: closed under the global context (no axioms)" || bad "putnam_1962_a5 has assumptions: $(cat ci_pa_a5.names | tr '\n' ' ')"; }
pa a2 putnam_1963_a2 putnam_1963_a2 && { grep -q "Closed under the global context" ci_pa_a2.log && ok "putnam_1963_a2: closed under the global context (no axioms)" || bad "putnam_1963_a2 has assumptions: $(cat ci_pa_a2.names | tr '\n' ' ')"; }
pa b5 putnam_1962_b5_corrected_proof putnam_1962_b5 && {
  unexpected=$(grep -vE '^boolp\.|(^|\.)R$' ci_pa_b5.names || true)
  if [ -z "$unexpected" ] && grep -q '^boolp\.' ci_pa_b5.names; then ok "putnam_1962_b5 (corrected): only R and the classical axioms of mathcomp.reals: $(tr '\n' ' ' < ci_pa_b5.names)"
  else bad "putnam_1962_b5 (corrected) has unexpected assumptions: $unexpected"; fi; }
pa b5f putnam_1962_b5_statement_is_false putnam_1962_b5_rocq_statement_is_false && {
  grep -qxE '(putnam_1962_b5\.)?putnam_1962_b5' ci_pa_b5f.names && ok "B5 refutation assumes exactly the admitted upstream putnam_1962_b5 (plus R and classical axioms)" || bad "B5 refutation: expected the admitted putnam_1962_b5 among the assumptions: $(tr '\n' ' ' < ci_pa_b5f.names)"; }
pa a2f putnam_1962_a2_statement_is_false putnam_1962_a2_rocq_statement_is_false && {
  grep -qxE '(putnam_1962_a2\.)?putnam_1962_a2' ci_pa_a2f.names && ok "A2 refutation assumes exactly the admitted upstream putnam_1962_a2 (plus R and classical axioms)" || bad "A2 refutation: expected the admitted putnam_1962_a2 among the assumptions: $(tr '\n' ' ' < ci_pa_a2f.names)"; }
pa a6v putnam_1962_a6_statement_is_vacuous putnam_1962_a6 && { grep -q "Closed under the global context" ci_pa_a6v.log && ok "A6 vacuity proof: closed under the global context" || bad "A6 vacuity proof has assumptions: $(tr '\n' ' ' < ci_pa_a6v.names)"; }

step "3. independent kernel check"
for f in $PROOFS; do
  if $CHK -R . "" "$f" > "ci_chk_$f.log" 2>&1 && grep -q "Modules were successfully checked" "ci_chk_$f.log"; then ok "$CHK $f"
  else bad "$CHK $f:"; tail -n 15 "ci_chk_$f.log"; fi
done

step "4. statement integrity against upstream PutnamBench commit ${COMMIT:0:7}"
mkdir -p ci_upstream
for p in putnam_1962_a5 putnam_1963_a2 putnam_1962_b5 putnam_1962_a6 putnam_1962_a2; do
  curl -sSfL -o "ci_upstream/$p.v" "$UP/$p.v" || { bad "could not download upstream $p.v"; }
done
strip() { awk 'BEGIN{h=1} h&&/^   =+ \*\)$/{h=0; getline; next} h{next} !/compat:/{print}' "$1"; }
up()    { sed -e '$a\' "ci_upstream/$1.v"; }          # upstream, with a final newline
thm()   { sed -n '/^Theorem/,/^Proof/p' | sed '$d'; }  # the Theorem block
nchanged() { diff "$1" "$2" | grep -c '^[<>]' || true; }
# A5: preamble + Definition + Theorem block identical
if diff <(up putnam_1962_a5 | sed -n '1,9p') <(strip putnam_1962_a5.v | sed -n '1,9p') >/dev/null \
   && diff <(up putnam_1962_a5 | thm) <(strip putnam_1962_a5.v | thm) >/dev/null
then ok "putnam_1962_a5.v: preamble, Definition and Theorem identical to upstream"; else bad "putnam_1962_a5.v differs from upstream in its statement"; fi
# 1963 A2: everything before Proof identical, apart from the added zify import
if diff <(up putnam_1963_a2 | sed '/^Proof/,$d') <(strip putnam_1963_a2.v | grep -v '^From mathcomp Require Import zify\.$' | sed '/^Proof/,$d') >/dev/null
then ok "putnam_1963_a2.v: statement identical to upstream (one added import: zify)"; else bad "putnam_1963_a2.v differs from upstream in its statement"; fi
# B5: evidence copy identical; corrected differs in exactly one line; proof's Theorem block differs in exactly that line
diff <(up putnam_1962_b5) <(strip putnam_1962_b5.v) >/dev/null && ok "putnam_1962_b5.v: identical to upstream (apart from compat lines)" || bad "putnam_1962_b5.v differs from upstream"
n=$(nchanged <(up putnam_1962_b5) <(strip putnam_1962_b5_corrected.v)); [ "$n" = "2" ] && ok "putnam_1962_b5_corrected.v: exactly one line differs from upstream (the bound)" || bad "putnam_1962_b5_corrected.v: $n changed lines vs upstream (expected 2 = one line)"
n=$(nchanged <(up putnam_1962_b5 | thm) <(strip putnam_1962_b5_corrected_proof.v | thm)); [ "$n" = "2" ] && ok "putnam_1962_b5_corrected_proof.v: Theorem block differs from upstream in exactly the bound line" || bad "putnam_1962_b5_corrected_proof.v: $n changed Theorem lines vs upstream (expected 2)"
diff <(strip putnam_1962_b5_corrected.v | thm) <(strip putnam_1962_b5_corrected_proof.v | thm) >/dev/null && ok "putnam_1962_b5_corrected_proof.v proves exactly the statement of putnam_1962_b5_corrected.v" || bad "corrected B5 statement and proof file disagree"
# A6: evidence copy identical; vacuity proof's Theorem identical; corrected differs in exactly the hSScond line
diff <(up putnam_1962_a6) <(strip putnam_1962_a6.v) >/dev/null && ok "putnam_1962_a6.v: identical to upstream" || bad "putnam_1962_a6.v differs from upstream"
diff <(up putnam_1962_a6 | thm) <(strip putnam_1962_a6_statement_is_vacuous.v | thm) >/dev/null && ok "putnam_1962_a6_statement_is_vacuous.v: Theorem identical to upstream" || bad "A6 vacuity file: Theorem differs from upstream"
n=$(nchanged <(up putnam_1962_a6) <(strip putnam_1962_a6_corrected.v)); [ "$n" = "2" ] && ok "putnam_1962_a6_corrected.v: exactly one line differs from upstream (hSScond)" || bad "putnam_1962_a6_corrected.v: $n changed lines vs upstream (expected 2)"
# A2: evidence copy identical; corrected differs only in the solution-set Definition
diff <(up putnam_1962_a2) <(strip putnam_1962_a2.v) >/dev/null && ok "putnam_1962_a2.v: identical to upstream (apart from compat lines)" || bad "putnam_1962_a2.v differs from upstream"
nosol() { awk '/^\(\* Proposed fix:|^Definition putnam_1962_a2_solution/{skip=1} /^Theorem/{skip=0} !skip{print}'; }
if diff <(up putnam_1962_a2 | nosol) <(strip putnam_1962_a2_corrected.v | nosol) >/dev/null
then ok "putnam_1962_a2_corrected.v: differs from upstream only in the solution-set definition"; else bad "putnam_1962_a2_corrected.v differs from upstream outside the solution set"; fi

echo
if [ "$fail" = "0" ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $fail
