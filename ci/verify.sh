#!/usr/bin/env bash
# Full verification of this repository. Run from anywhere: bash ci/verify.sh
# Needs Rocq 9.1 with MathComp, MathComp-Analysis, zify, Algebra-Tactics and
# Coquelicot; curl for the upstream comparison in step 4.
#   1. compile all 17 .v files in dependency order (fails on any error, and
#      reports any warning that comes from a file's own lines rather than the
#      library imports)
#   2. Print Assumptions: A5 and 1963 A2 closed; B5, B2, A4 and the corrected A2
#      only R + the classical axioms of mathcomp.reals; the corrected A6 only the
#      standard library's Extensionality_Ensembles; B6 only the axioms behind the
#      standard library's reals and Rolle's theorem plus the classical axioms of
#      mathcomp.classical; the three False/vacuity derivations assume exactly the
#      admitted upstream theorem (or nothing)
#   3. independent kernel check (rocqchk / coqchk) of the eight proofs
#   4. statement integrity: diff every statement against the upstream
#      PutnamBench files at the pinned commit, ignoring only the header comments
#      and the marked compat lines; for B6 the upstream file is also compiled and
#      the kernel checks that the proved theorem has exactly its type
# When every check passes, the script removes everything it produced (.vo, .vok,
# .vos, .glob, .*.aux, .lia.cache, .nia.cache, .lra.cache, .nra.cache, *.log,
# ci_pa_*, ci_chk_*, ci_up_b6.*, ci_same_b6.*, ci_upstream/), leaving the folder exactly as it
# found it. When a check fails, all of it is kept so the .log files can be inspected.
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

PROOFS="putnam_1962_a5 putnam_1963_a2 putnam_1962_b5_corrected_proof putnam_1962_b2 putnam_1962_a4 putnam_1962_a6_corrected_proof putnam_1962_a2_corrected_proof putnam_1962_b6"
FILES="$PROOFS \
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

# the eight proof files add no axiom, notation or tactic definition and contain no Admitted/admit
for f in $PROOFS; do
  pat='^ *(Local |Global )?(Notation|Reserved Notation|Infix|Ltac|Axiom|Axioms|Parameter|Parameters) |Admitted\.|(^|[^A-Za-z_])admit([^A-Za-z_]|$)'
  if grep -nE "$pat" "$f.v" >/dev/null
  then bad "$f.v declares a notation, tactic or axiom, or contains admit/Admitted:"; grep -nE "$pat" "$f.v"
  else ok "$f.v: no notation, tactic or axiom declarations, no admit/Admitted"; fi
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
# R + the three classical axioms of mathcomp.reals, and nothing else
classical_only() { # tag  module  theorem  label
  pa "$1" "$2" "$3" && {
    unexpected=$(grep -vE "^boolp\.|^$2\.R\$" "ci_pa_$1.names" || true)
    if [ -z "$unexpected" ] && grep -q '^boolp\.' "ci_pa_$1.names"; then ok "$4: only R and the classical axioms of mathcomp.reals: $(tr '\n' ' ' < "ci_pa_$1.names")"
    else bad "$4 has unexpected assumptions: $unexpected"; fi; }
}
classical_only b5 putnam_1962_b5_corrected_proof putnam_1962_b5 "putnam_1962_b5 (corrected)"
classical_only b2 putnam_1962_b2 putnam_1962_b2 "putnam_1962_b2"
classical_only a4 putnam_1962_a4 putnam_1962_a4 "putnam_1962_a4"
classical_only a2p putnam_1962_a2_corrected_proof putnam_1962_a2 "putnam_1962_a2 (corrected)"
pa b5f putnam_1962_b5_statement_is_false putnam_1962_b5_rocq_statement_is_false && {
  grep -qxE '(putnam_1962_b5\.)?putnam_1962_b5' ci_pa_b5f.names && ok "B5 refutation assumes exactly the admitted upstream putnam_1962_b5 (plus R and classical axioms)" || bad "B5 refutation: expected the admitted putnam_1962_b5 among the assumptions: $(tr '\n' ' ' < ci_pa_b5f.names)"; }
pa a2f putnam_1962_a2_statement_is_false putnam_1962_a2_rocq_statement_is_false && {
  grep -qxE '(putnam_1962_a2\.)?putnam_1962_a2' ci_pa_a2f.names && ok "A2 refutation assumes exactly the admitted upstream putnam_1962_a2 (plus R and classical axioms)" || bad "A2 refutation: expected the admitted putnam_1962_a2 among the assumptions: $(tr '\n' ' ' < ci_pa_a2f.names)"; }
pa a6v putnam_1962_a6_statement_is_vacuous putnam_1962_a6 && { grep -q "Closed under the global context" ci_pa_a6v.log && ok "A6 vacuity proof: closed under the global context" || bad "A6 vacuity proof has assumptions: $(tr '\n' ' ' < ci_pa_a6v.names)"; }
pa a6p putnam_1962_a6_corrected_proof putnam_1962_a6 && {
  if [ "$(grep -c '' ci_pa_a6p.names)" = "1" ] && grep -qxE '([A-Za-z0-9_]+\.)*Extensionality_Ensembles' ci_pa_a6p.names
  then ok "putnam_1962_a6 (corrected): only the standard library's Extensionality_Ensembles"
  else bad "putnam_1962_a6 (corrected) has unexpected assumptions: $(tr '\n' ' ' < ci_pa_a6p.names)"; fi; }
# B6: the axioms the standard library's real numbers are built on (ClassicalDedekindReals.sig_not_dec,
# sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep), Classical_Prop.classic
# (used by the standard library's Rolle), and the three classical axioms of mathcomp.classical
# (boolp), and nothing else -- in particular nothing declared by the proof file itself
pa b6 putnam_1962_b6 putnam_1962_b6 && {
  unexpected=$(grep -vxE '([A-Za-z0-9_]+\.)*ClassicalDedekindReals\.sig_not_dec|([A-Za-z0-9_]+\.)*ClassicalDedekindReals\.sig_forall_dec|([A-Za-z0-9_]+\.)*FunctionalExtensionality\.functional_extensionality_dep|([A-Za-z0-9_]+\.)*Classical_Prop\.classic|boolp\.propositional_extensionality|boolp\.functional_extensionality_dep|boolp\.constructive_indefinite_description' ci_pa_b6.names || true)
  if [ -z "$unexpected" ] && grep -q '^boolp\.' ci_pa_b6.names && grep -q 'ClassicalDedekindReals' ci_pa_b6.names
  then ok "putnam_1962_b6: only the axioms behind the standard library's reals and Rolle's theorem, and the classical axioms of mathcomp.classical: $(tr '\n' ' ' < ci_pa_b6.names)"
  else bad "putnam_1962_b6 has unexpected assumptions: $unexpected"; fi; }

step "3. independent kernel check"
for f in $PROOFS; do
  if $CHK -R . "" "$f" > "ci_chk_$f.log" 2>&1 && grep -q "Modules were successfully checked" "ci_chk_$f.log"; then ok "$CHK $f"
  else bad "$CHK $f:"; tail -n 15 "ci_chk_$f.log"; fi
done

step "4. statement integrity against upstream PutnamBench commit ${COMMIT:0:7}"
mkdir -p ci_upstream
for p in putnam_1962_a5 putnam_1963_a2 putnam_1962_b5 putnam_1962_a6 putnam_1962_a2 putnam_1962_b2 putnam_1962_a4 putnam_1962_b6; do
  curl -sSfL -o "ci_upstream/$p.v" "$UP/$p.v" || { bad "could not download upstream $p.v"; }
done
strip() { awk 'BEGIN{h=1} h&&/^   =+ \*\)$/{h=0; getline; next} h{next} !/^(Set Warnings "[^"]*"\.|From mathcomp Require Import ssralg\.|Local Open Scope classical_set_scope\.) \(\* compat: /{print}' "$1"; }  # drops the header and exactly the three kinds of marked compat lines
up()    { awk '{print}' "ci_upstream/$1.v"; }           # upstream, with a final newline (awk adds one if missing; portable to macOS)
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
diff <(strip putnam_1962_a6_corrected.v | thm) <(strip putnam_1962_a6_corrected_proof.v | thm) >/dev/null && ok "putnam_1962_a6_corrected_proof.v proves exactly the statement of putnam_1962_a6_corrected.v" || bad "corrected A6 statement and proof file disagree"
# B2 and A4: preamble (everything before the Variable) and Theorem block identical
if diff <(up putnam_1962_b2 | sed -n '1,10p') <(strip putnam_1962_b2.v | sed -n '1,10p') >/dev/null \
   && diff <(up putnam_1962_b2 | thm) <(strip putnam_1962_b2.v | thm) >/dev/null
then ok "putnam_1962_b2.v: preamble and Theorem identical to upstream"; else bad "putnam_1962_b2.v differs from upstream in its statement"; fi
if diff <(up putnam_1962_a4 | sed -n '1,10p') <(strip putnam_1962_a4.v | sed -n '1,10p') >/dev/null \
   && diff <(up putnam_1962_a4 | thm) <(strip putnam_1962_a4.v | thm) >/dev/null
then ok "putnam_1962_a4.v: preamble and Theorem identical to upstream"; else bad "putnam_1962_a4.v differs from upstream in its statement"; fi
# A2: evidence copy identical; corrected differs only in the solution-set Definition
diff <(up putnam_1962_a2) <(strip putnam_1962_a2.v) >/dev/null && ok "putnam_1962_a2.v: identical to upstream (apart from compat lines)" || bad "putnam_1962_a2.v differs from upstream"
nosol() { awk '/^\(\* Proposed fix:|^Definition putnam_1962_a2_solution/{skip=1} /^Theorem/{skip=0} !skip{print}'; }
if diff <(up putnam_1962_a2 | nosol) <(strip putnam_1962_a2_corrected.v | nosol) >/dev/null
then ok "putnam_1962_a2_corrected.v: differs from upstream only in the solution-set definition"; else bad "putnam_1962_a2_corrected.v differs from upstream outside the solution set"; fi
# corrected A2 proof: the statement's preamble (its first 10 lines), everything from the Variable
# through the solution-set Definition, and the Theorem block are identical to putnam_1962_a2_corrected.v,
# and the only lines added between the preamble and the Variable are the proof's extra imports
stmt() { sed -n '/^Variable R/,/\]\.$/p'; }   # Variable R, Definition mu, the solution set (ends with ")].")
extra=$(strip putnam_1962_a2_corrected_proof.v | sed -n '11,/^Variable R/p' | grep -v '^$' | grep -vxE 'Variable R : realType\.|\(\* Extra imports for the proof \(they add nothing to the statement\)\. \*\)|From mathcomp Require Import boolp functions set_interval numfun constructive_ereal ereal\.|From mathcomp Require Import measurable_realfun realfun ftc interval ring lra\.|Import GRing\.Theory Num\.Theory Order\.Theory\.|Import numFieldNormedType\.Exports\.' || true)
if diff <(strip putnam_1962_a2_corrected.v | sed -n '1,10p') <(strip putnam_1962_a2_corrected_proof.v | sed -n '1,10p') >/dev/null \
   && diff <(strip putnam_1962_a2_corrected.v | stmt) <(strip putnam_1962_a2_corrected_proof.v | stmt) >/dev/null \
   && diff <(strip putnam_1962_a2_corrected.v | thm) <(strip putnam_1962_a2_corrected_proof.v | thm) >/dev/null \
   && [ -z "$extra" ]
then ok "putnam_1962_a2_corrected_proof.v proves exactly the statement of putnam_1962_a2_corrected.v (preamble, Definition and Theorem identical; only the proof's imports added)"
else bad "corrected A2 statement and proof file disagree${extra:+ (unexpected lines before the Variable: $extra)}"; fi
# B6: preamble (the upstream file's first four lines: the Require Import line, the coercion and the blank
# lines around them) and Theorem block identical; then the upstream file itself is compiled (its theorem
# is Admitted) and the kernel checks that the theorem proved here has exactly the type of the upstream one
if diff <(up putnam_1962_b6 | sed -n '1,4p') <(strip putnam_1962_b6.v | sed -n '1,4p') >/dev/null \
   && diff <(up putnam_1962_b6 | thm) <(strip putnam_1962_b6.v | thm) >/dev/null
then ok "putnam_1962_b6.v: preamble and Theorem identical to upstream"; else bad "putnam_1962_b6.v differs from upstream in its statement"; fi
cp ci_upstream/putnam_1962_b6.v ci_up_b6.v
printf 'Require ci_up_b6 putnam_1962_b6.\nDefinition ci_same_statement : ltac:(let T := type of ci_up_b6.putnam_1962_b6 in exact T) := putnam_1962_b6.putnam_1962_b6.\n' > ci_same_b6.v
if $COMPILE -R . "" ci_up_b6.v > ci_up_b6.log 2>&1 && $COMPILE -R . "" ci_same_b6.v > ci_same_b6.log 2>&1
then ok "putnam_1962_b6: the kernel accepts the proved theorem at the type of the upstream admitted theorem (compiled from the upstream file itself)"
else bad "putnam_1962_b6: the proved theorem does not have the type of the upstream theorem:"; grep -A8 "^Error" ci_up_b6.log ci_same_b6.log | head -20; fi

echo
if [ "$fail" = "0" ]; then
  echo "ALL CHECKS PASSED"
  # leave the folder as it was: remove everything this script produced
  for f in $FILES; do rm -f "$f.vo" "$f.vok" "$f.vos" "$f.glob" "$f.log" ".$f.aux"; done
  rm -f ci_pa_* .ci_pa_*.aux ci_chk_* ci_up_b6.* .ci_up_b6.aux ci_same_b6.* .ci_same_b6.aux .lia.cache .nia.cache .lra.cache .nra.cache
  rm -rf ci_upstream
  echo "(build products and logs removed; the folder is as it was before the run)"
else
  echo "SOME CHECKS FAILED (build products and .log files kept for inspection)"
fi
exit $fail
