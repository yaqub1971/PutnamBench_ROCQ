(* ============================================================================
   PutnamBench 1969 B3 -- the UPSTREAM statement, kept as evidence. Ends in Admitted
   (it is a statement, not a proof).
   Source: coq/src/putnam_1969_b3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Below this comment the file is upstream's text verbatim (no compat lines were added:
   they cannot make the file compile, see below).
   Problem: if a real sequence T satisfies T_n T_(n+1) = n for every n >= 1 and
   T_n / T_(n+1) -> 1 as n -> oo, then pi T_1^2 = 2.
   Defect (audit verdict: compile): the file does not compile. The target of "-->" in
   hypothesis hT2 is the bare numeral 1, which elaborates to 1 in an unknown semiring and
   cannot be unified with the filter structure the notation expects (upstream line 17,
   i.e. line 50 of this file):
     Error: The term "1" has type "GRing.SemiRing.sort ?s0"
     while it is expected to have type "Filtered.sort ?s".
   Mathematically the statement is faithful to the problem (it is PutnamBench's Lean
   statement of the same problem, transcribed). Proposed fix, one token,
   "--> 1" -> "--> (1 : R)": putnam_1969_b3_corrected.v. No evidence file: the
   statement is neither false nor vacuous, so there is no False to derive.
   Does not compile on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   the error quoted above (checked by running coqc on this file; the audit's build log of
   the upstream file shows the same error at the same position).
   Does not compile on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix)
   either: there it stops earlier, at "Variable R : realType." outside a Section (an error
   since Rocq 9.0, declaration-outside-section). With the repository's marked compat lines
   added (tried on a scratch copy, not kept here) it gets past that and stops at the same
   "--> 1" token: The term "1" has type "GRing.PzSemiRing.sort ?s0" while it is expected
   to have type "Filtered.sort ?s".
   About the warnings: the import lines below trigger library warnings emitted by MathComp
   itself (overridden notations, ambiguous coercion paths, all_ssreflect deprecated since
   MathComp 2.5); they are not about this file. The import lines are kept exactly as
   upstream wrote them so that the statement stays identical to the benchmark's.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals exp sequences topology normedtype trigo.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Theorem putnam_1969_b3
    (T : nat -> R)
    (hT1 : forall n : nat, ge n 1 -> (T n) * (T (n.+1)) = n%:R)
    (hT2 : (fun n => (T n)/(T n.+1)) @ \oo --> 1)
    : pi * (T 1%nat) ^+ 2 = 2.
Proof. Admitted.