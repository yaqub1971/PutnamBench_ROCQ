(* ============================================================================
   PutnamBench 2010 B2 -- proof that the UPSTREAM statement is vacuous.
   The Definition and the Theorem below are upstream's statement verbatim
   (coq/src/putnam_2010_b2.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)), closed by a two-line proof
   that only exploits the contradiction in hypothesis hm (no mathematics involved): hm
   provides points A, B, C with p A B C, whose first conjunct noncollinear A B C denies the
   existence of reals s, t with s (B - A) + t (C - A) = (0, 0); but s = t = 0 is such a
   pair. Hence the theorem holds whatever putnam_2010_b2_solution is.
   Compile with:  rocq compile -R . "" putnam_2010_b2_statement_is_vacuous.v
   (standalone; with Coq 8.18 use coqc instead of rocq compile).
   Print Assumptions at the end lists only the three axioms the standard library's reals
   are built on (ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec,
   FunctionalExtensionality.functional_extensionality_dep); they enter through the ring
   identities 0 * x + 0 * y = 0 on R. No other assumption is used.
   Verified on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on
   Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04):
   compiles and prints the assumption list described above.
   About the warnings: the file is written for Coq 8.x. Rocq 9.1 warns "Loading Stdlib
   without prefix is deprecated" on the Require line and would prefer
   "From Stdlib Require Import Reals Rgeom ZArith"; the line is kept as upstream wrote it.
   ============================================================================ *)

(* The benchmark statement putnam_2010_b2.v, verbatim, closed by a proof that only
   exploits the contradiction in hm (no mathematics involved): *)
Require Import Reals Rgeom ZArith.
Open Scope R.
Definition putnam_2010_b2_solution := 3.
Theorem putnam_2010_b2
    (dist : (R * R) -> (R * R) -> R := fun A B => let (a, b) := A in let (c, d) := B in dist_euc a b c d)
    (int_val : (R * R) -> Prop := fun P => exists (x y : Z), P = (IZR x, IZR y))
    (noncollinear: (R * R) -> (R * R) -> (R * R) -> Prop := fun A B C => let (a, b) := A in let (c, d) := B in let (e, f) := C in
        ~exists (s t : R), (s * (c - a) + t * (e - a), s * (d - b) + t * (f - b)) = (0, 0))
    (p : (R * R) -> (R * R) -> (R * R) -> Prop :=
        fun A B C => noncollinear A B C /\ int_val A /\ int_val B /\ int_val C /\
        (exists (x : Z), dist A B = IZR x) /\ (exists (y : Z), dist A C = IZR y) /\ (exists (z : Z), dist B C = IZR z))
    (m : R)
    (hm : exists (A B C: R * R), p A B C /\ dist A B = m)
    (hmlb : forall (A B C: R * R), p A B C -> dist A B >= m)
    : m = putnam_2010_b2_solution.
Proof.
  (* hm provides a triple satisfying p; its first conjunct noncollinear is refuted by s = t = 0 *)
  destruct hm as [[a b] [[c d] [[e f] [[hnc _] _]]]].
  exfalso; apply hnc; exists 0, 0; f_equal; ring.
Qed.
Print Assumptions putnam_2010_b2.
