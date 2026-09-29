(* ============================================================================
   PutnamBench 2022 A6 -- proof that the UPSTREAM statement is vacuous.
   The Theorem below is upstream's statement verbatim (coq/src/putnam_2022_a6.v from
   PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)), closed by a short
   proof that only exploits the contradiction in its hypotheses (no mathematics of the
   problem involved): hvalid m is "exists s, (ordering conditions) -> valid m s", and
   the constant function s = 0 violates the first ordering conjunct at i0 (0 < 0 is
   false), so hvalid (M+1) holds vacuously; hMub then gives M+1 <= M.
   Compile with:  rocq compile -R . "" putnam_2022_a6_statement_is_vacuous.v
   (Coq 8.18: coqc -R . "" putnam_2022_a6_statement_is_vacuous.v); it does not load
   putnam_2022_a6.vo, it restates the upstream theorem.
   Print Assumptions at the end lists only two axioms the standard library's reals are
   built on, ClassicalDedekindReals.sig_forall_dec and
   FunctionalExtensionality.functional_extensionality_dep (reached through Rlt_irrefl).
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   compiles and prints the assumption list described above.
   About the warnings: the import line below triggers warnings emitted by the libraries
   themselves (Rocq 9.1: "Loading Stdlib without prefix is deprecated"; MathComp:
   ambiguous coercion paths, overridden notations, hidden scope keys); none of this
   file's own lines produce any. The import line is kept exactly as upstream wrote it.
   ============================================================================ *)

(* The benchmark statement putnam_2022_a6.v, verbatim, closed by a proof that only
   exploits the contradiction between hvalid and hMub: *)
Require Import Nat Reals Coquelicot.Hierarchy. From mathcomp Require Import div fintype seq ssralg ssrbool ssrnat ssrnum .
Definition putnam_2022_a6_solution := fun n : nat => n.
Theorem putnam_2022_a6
    (N : nat)
    (M : nat)
    (n := mul N 2)
    (i0 : 'I_n)
    (sumIntervals : ('I_n -> R) -> nat -> R := fun s k => sum_n (fun i => (((s (nth i0 (enum 'I_n) (i+1))))^(2*k-1) - ((s (nth i0 (enum 'I_n) i)))^(2*k-1))) (n-1))
    (valid : nat -> ('I_n -> R) -> Prop := fun m s => forall (k: nat), and (le 1 k) (le k m) -> sumIntervals s k = 1)
    (hvalid : nat -> Prop := fun m => exists (s : 'I_n -> R), (forall (i : 'I_n),  (s i < s (ordS i)) /\ s (nth i0 (enum 'I_n) 0) > -1 /\ s (nth i0 (enum 'I_n) (n-1)) < 1) -> valid m s)
    (hM : hvalid M)
    (hMub : forall m : nat, hvalid m -> le m M)
    : M = putnam_2022_a6_solution n.
Proof.
  (* hvalid (S M) holds vacuously: the constant 0 violates "s i0 < s (ordS i0)" *)
  exfalso. apply (Nat.nle_succ_diag_l M). apply hMub.
  exists (fun _ => 0). intros H. destruct (H i0) as [H0 _]. destruct (Rlt_irrefl 0 H0).
Qed.
Print Assumptions putnam_2022_a6.
