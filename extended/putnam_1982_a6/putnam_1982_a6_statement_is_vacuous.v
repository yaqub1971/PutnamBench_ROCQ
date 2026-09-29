(* ============================================================================
   PutnamBench 1982 A6 -- proof that the UPSTREAM statement is vacuous.
   The Definition and the Theorem below are upstream's statement verbatim
   (coq/src/putnam_1982_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20)), closed by a one-line proof
   that only exploits the contradiction in the monotonicity condition (no mathematics
   involved): "forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)" at i = j = 0
   demands Rabs (a 0) > Rabs (a 0), so the left side of the biconditional is False for
   every a, and "False <-> putnam_1982_a6_solution" holds because the solution is False.
   Compile with:  rocq compile -R . "" putnam_1982_a6_statement_is_vacuous.v
   (standalone; with Coq 8.18 use coqc instead of rocq compile).
   Print Assumptions at the end lists only ClassicalDedekindReals.sig_not_dec,
   ClassicalDedekindReals.sig_forall_dec and
   FunctionalExtensionality.functional_extensionality_dep, the axioms the standard
   library's reals (and hence Coquelicot's Series / Lim_seq in the statement) are built
   on. No other assumption is used.
   Verified on Rocq 9.1.1 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / Coquelicot 3.4.1
   (Ubuntu 24.04): compiles and prints the assumption list described above.
   About the warnings: the file is written for Coq 8.x. The Require line below triggers
   library warnings only: under Rocq 9.1.1 "Loading Stdlib without prefix is
   deprecated" and, on both toolchains, Coquelicot's "New coercion path [real; Finite]
   : Rbar >-> Rbar is not definitionally an identity function". None of this file's own
   lines produce any. The line is kept exactly as upstream wrote it.
   ============================================================================ *)

(* The benchmark statement putnam_1982_a6.v, verbatim, closed by a proof that only
   exploits the contradiction in the monotonicity condition (no mathematics involved): *)
Require Import Nat Reals Coquelicot.Coquelicot.
Open Scope R.
Definition putnam_1982_a6_solution := False.
Theorem putnam_1982_a6
    (a: nat -> R) 
    : ((Series a = 1 /\ forall (i j: nat), le i j -> Rabs (a i) > Rabs (a j)) /\
    forall (f: nat -> nat), Lim_seq (fun i => Rabs (INR (f i - i)) * Rabs (a i)) = 0 -> exists f', forall x, f' (f x) = x /\ f (f' x) = x -> 
    Series (fun i => a (f i)) = 1) <-> putnam_1982_a6_solution.    
Proof.
  (* at i = j = 0 the monotonicity conjunct demands Rabs (a 0) > Rabs (a 0), so the left
     side is False; the right side is False by definition *)
  split; [intros [[_ h] _]; exact (Rlt_irrefl _ (h 0%nat 0%nat (le_n 0))) | intros []].
Qed.
Print Assumptions putnam_1982_a6.
