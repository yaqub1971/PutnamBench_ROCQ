(* ============================================================================
   PutnamBench 2013 B2 -- proof that the UPSTREAM statement is vacuous.
   The Definition and the Theorem below are upstream's statement verbatim
   (coq/src/putnam_2013_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)), closed by a short proof
   that only exploits the contradiction in the hypotheses (no mathematics about the
   problem is involved; hm is not even used): because E puts "exists a N" under
   "forall x", the function g(x) = 1 + |m| cos(2 pi x)^2 is in E -- at each x take N = 1
   and the x-dependent coefficient a_1 = |m| cos(2 pi x) (a_n = 0 otherwise, in
   particular for every multiple of 3); g >= 0 because |m| cos(2 pi x)^2 >= 0 -- and
   hmub g gives g(0) = 1 + |m| <= m <= |m|, which is absurd.
   Compile with:  rocq compile -R . "" putnam_2013_b2_statement_is_vacuous.v
   (standalone; with Coq 8.18 use coqc instead of rocq compile).
   Print Assumptions at the end lists only the three axioms the standard library's
   reals are built on (ClassicalDedekindReals.sig_not_dec,
   ClassicalDedekindReals.sig_forall_dec,
   FunctionalExtensionality.functional_extensionality_dep); no other assumption is used.
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4
   (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1
   (Ubuntu 24.04): compiles and prints the assumption list described above.
   About the warnings: the Require line below triggers library warnings only: under
   Rocq 9.1.1 three "Loading Stdlib without prefix is deprecated" warnings and
   Coquelicot's "New coercion path [real; Finite] : Rbar >-> Rbar" ambiguous-path
   warning; under Coq 8.18.0 only the latter. None of this file's own lines produce any.
   The line is kept exactly as upstream wrote it.
   ============================================================================ *)

(* The benchmark statement putnam_2013_b2.v, verbatim, closed by a proof that only
   exploits the contradiction in hmub (no mathematics involved): *)
Require Import Ensembles Finite_sets Reals Coquelicot.Coquelicot.
Definition putnam_2013_b2_solution : R := 3.
Theorem putnam_2013_b2
    (E: Ensemble (R -> R) := fun f => forall (x : R), exists (a : nat -> R) (N : nat), f x = 1 + sum_n_m (fun n => a n * cos (2 * PI * INR n * x)) 1 N /\ f x >= 0 /\ 
    forall (n: nat), n mod 3 = 0%nat -> a n = 0)
    (m: R)
    (hm : exists f: R -> R, E f /\ f 0 = m)
    (hmub : forall f : R -> R, E f -> f 0 <= m)
    : m = putnam_2013_b2_solution.
Proof.
  (* g(x) = 1 + |m| cos(2 pi x)^2 is >= 0 and at each x equals the "cosine polynomial"
     1 + a_1 cos(2 pi x) with the x-dependent coefficient a_1 = |m| cos(2 pi x); so E g,
     and hmub g would give 1 + |m| = g 0 <= m <= |m|. *)
  clear hm.
  set (g := fun x : R => 1 + Rabs m * cos (2 * PI * INR 1 * x) * cos (2 * PI * INR 1 * x)).
  assert (hg : E g).
  { intros x.
    exists (fun n => match n with 1%nat => Rabs m * cos (2 * PI * INR 1 * x) | _ => 0 end), 1%nat.
    split; [|split].
    - unfold g; rewrite sum_n_n; reflexivity.
    - unfold g; apply Rle_ge, Rplus_le_le_0_compat; [apply Rle_0_1|].
      rewrite Rmult_assoc; apply Rmult_le_pos; [apply Rabs_pos | apply Rle_0_sqr].
    - intros [|[|n]] h; [reflexivity | discriminate h | reflexivity]. }
  pose proof (hmub g hg) as h; unfold g in h.
  rewrite Rmult_0_r, cos_0, !Rmult_1_r in h.
  exfalso; apply (Rlt_irrefl m).
  apply Rle_lt_trans with (Rabs m); [apply Rle_abs|].
  apply Rlt_le_trans with (1 + Rabs m); [rewrite Rplus_comm; apply Rlt_plus_1 | exact h].
Qed.
Print Assumptions putnam_2013_b2.
