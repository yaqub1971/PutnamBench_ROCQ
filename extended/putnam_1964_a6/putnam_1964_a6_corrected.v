(* ============================================================================
   PutnamBench 1964 A6 -- PROPOSED FIX of the upstream statement. Ends in Admitted
   (it is a statement, not a proof).
   Problem: S is a finite set of collinear points; k is the largest distance between two
   of its points; whenever two points of S are a distance d < k apart, some other pair
   of points of S is also a distance d apart. Show that the ratio of the distances of
   any two pairs of points of S is rational.
   Source: coq/src/putnam_1964_a6.v from PutnamBench (github.com/trishullab/PutnamBench), commit 4dbe26ef21563af851eedaeb82d936fe1f94fc52 (2026-09-20).
   Defect of the upstream statement: the finiteness of the point set, which the problem
   states ("a finite set of collinear points") and the Lean statement encodes as
   S : Finset R, is missing: T is an arbitrary set R. With T = [set: R] every hypothesis
   holds (for any pair p the translate (p.1 + 1, p.2 + 1) is a second pair at the same
   distance, so hrepdist is satisfied), and the conclusion for the pairs (0, sqrt 2)
   and (0, 1) asserts that sqrt 2 is a ratio of two integers. So the upstream theorem is
   FALSE (derivation of False: putnam_1964_a6_statement_is_false.v).
   Fix: apart from this header comment, this file differs from putnam_1964_a6.v (the
   upstream statement with the same compat lines) in one changed line and one added line:
     -From mathcomp Require Import classical_sets.
     +From mathcomp Require Import classical_sets cardinality.
        (cardinality is the MathComp-Analysis module that defines finite_set; this is
        the import line the upstream corpus itself uses where it needs finite_set,
        e.g. putnam_1974_a1.v, putnam_2015_b5.v)
     +    (hT : finite_set T)
        (inserted right after "(T : set R)": the finiteness hypothesis of the problem,
        the counterpart of Lean's S : Finset R)
   Printed with Set Printing All, the theorem's type differs from the upstream one only
   by the added binder (_ : cardinality.finite_set T); the new import changes nothing
   else. Everything else is upstream's and was re-read against the problem: pairs is
   the set of ordered pairs (a, b) of points of T with a < b (in bijection with the
   unordered pairs of distinct points); distance p = p.2 - p.1, positive on pairs;
   hrepdist says that a pair whose distance is exceeded by the distance of some other
   pair -- for a finite set this is exactly "d < k", k being the attained maximum --
   has a second, different pair at the same distance; the conclusion says that the
   ratio of the distances of two distinct pairs is n / d with integers n, d, d <> 0,
   i.e. rational (for q = p the ratio is 1, so restricting to q <> p loses nothing;
   Lean has the same q <> p). With finiteness restored the statement is the problem's
   (proof sketch in NOTES.md).
   Compat lines: the lines marked "(* compat: ... *)" are those of putnam_1964_a6.v:
   (1) a Variable outside a Section is an error since Rocq 9.0 (the Set Warnings line
   before "Variable R"); (2) with MathComp 2.5, importing all_ssreflect after
   all_algebra (upstream's order) overrides the ring notations 1 and %:R, so ssralg is
   re-imported (the three lines after the imports). The statement writes neither 1 nor
   %:R, and its type printed with Set Printing All is the same with and without (2);
   (2) is kept, as in the repository's other MathComp files over a ring, so that the
   ring notations mean the same on every MathComp version. Neither changes the meaning
   of the statement. On Coq 8.18.0 they are no-ops, except that (1) also silences the
   "local-declaration" warning that the upstream Variable line emits there.
   Verified: compiles on Rocq 9.1.1 / MathComp 2.5.0 / MathComp-Analysis 1.16.0 / Coquelicot 3.4.4 (Nix) and on Coq 8.18.0 / MathComp 2.1.0 / MathComp-Analysis 1.0.0 / Coquelicot 3.4.1 (Ubuntu 24.04).
   About the warnings: on both toolchains the first import line emits library warnings
   (ambiguous coercion paths, overridden notations; on MathComp 2.5 also the
   deprecation of all_ssreflect) that come from MathComp itself; none of this file's
   own lines produce any. Apart from the added module cardinality the import lines are
   kept exactly as upstream wrote them.
   ============================================================================ *)

From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals topology normedtype.
From mathcomp Require Import classical_sets cardinality.
Set Warnings "-notation-overridden". (* compat: the re-import on the next line necessarily re-declares 1, - 1 and %:R; silence that one warning category while it runs. *)
From mathcomp Require Import ssralg. (* compat: MathComp >= 2.5 re-declares the ring notations 1 and %:R inside all_ssreflect; imported after all_algebra (the upstream order) it overrides them, so ssralg is re-imported here. Harmless on MathComp <= 2.4. *)
Set Warnings "notation-overridden". (* compat: restore the default. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Set Warnings "-declaration-outside-section,-local-declaration". (* compat: Rocq >= 9.0 rejects a Variable declared outside a Section (Coq 8.x only warns); the upstream statement declares R this way. *)
Variable R : realType.
Theorem putnam_1964_a6 
    (T : set R)
    (hT : finite_set T)
    (pairs : set (R * R) := [set p : R * R | p.1 \in T /\ p.2 \in T /\ p.1 < p.2])
    (distance : (R * R) -> R := fun p => p.2 - p.1)
    (hrepdist : forall p : R * R, p \in pairs ->
        (exists m : R * R, m \in pairs /\ distance m > distance p) ->
        (exists q : R * R, q \in pairs /\ q <> p /\ distance p = distance q))
    : forall p q : R * R, (p \in pairs /\ q \in pairs /\ q <> p) ->
        exists n d : int, d <> 0 /\ distance p / distance q = (n%:~R)/(d%:~R).
Proof. Admitted.