(* ============================================================================
   PutnamBench 1974 A3 -- proof that the UPSTREAM statement is vacuous.
   The Definition and the Theorem below are upstream's statement verbatim
   (coq/src/putnam_1974_a3.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)), closed by a three-line proof
   that only exploits the contradiction in the hypothesis assmption (no mathematics
   involved): instantiated at p = 4, its left side "(prime 4 /\ gt 4 2) -> ..." holds
   vacuously because prime 4 evaluates to false, so its right side 4 = 1 %[mod 4],
   i.e. 4 %% 4 = 1 %% 4, i.e. 0 = 1, would follow. Hence the theorem holds for any
   solution sets whatsoever.
   Compile with:  rocq compile -R . "" putnam_1974_a3_statement_is_vacuous.v
   (standalone; with Coq 8.18 use coqc instead of rocq compile).
   Print Assumptions at the end lists only the three classical axioms of
   mathcomp.classical (boolp.propositional_extensionality,
   boolp.functional_extensionality_dep, boolp.constructive_indefinite_description);
   they come from the statement itself: membership "p \in A" in a classical set
   A : set nat is decided by boolp's asbool. No other assumption is used.
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 (Nix) and on
   Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 (Ubuntu 24.04): compiles and
   prints the assumption list described above.
   About the warnings: the PutnamBench Rocq statements were written for Coq 8.x with
   MathComp 2.1. Under Rocq 9.1.1 / MathComp 2.5.0 the first import line below triggers
   30 warnings emitted by MathComp itself (all_ssreflect is deprecated since 2.5,
   ambiguous coercion paths, overridden notations); under Coq 8.18.0 / MathComp 2.1.0 it
   triggers 23. They are library warnings, not warnings about this file: none of this
   file's own lines produce any. The import lines are kept exactly as upstream wrote them.
   ============================================================================ *)

(* The benchmark statement putnam_1974_a3.v, verbatim, closed by a proof that only
   exploits the contradiction in assmption (no mathematics involved): *)
From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition putnam_1974_a3_solution : (set nat) * (set nat) := ([set p : nat | prime p /\ p = 1 %[mod 8]], [set p : nat | prime p /\ p = 5 %[mod 8]]).
Theorem putnam_1974_a3
    (assmption : forall p : nat, ((prime p /\ gt p 2) -> ((exists m n : int, p%:Z = m ^+ 2 + n ^+ 2))) <-> p = 1 %[mod 4])
    : forall p : nat, 
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = x ^+ 2 + 16 * y ^+ 2)) <-> p \in fst putnam_1974_a3_solution) /\
        ((prime p /\ gt p 2 /\ (exists x y : int, p%:Z = 4 * x ^+ 2 + 4 * x * y + 5 * y ^+ 2)) <-> p \in snd putnam_1974_a3_solution).
Proof.
(* at p = 4 the left side of assmption holds vacuously (4 is not prime), so the right
   side 4 = 1 %[mod 4], i.e. 0 = 1, follows *)
case: (assmption 4%N) => h _.
suff: 4%N = 1 %[mod 4] by [].
by apply: h => -[].
Qed.
Print Assumptions putnam_1974_a3.
