(* Verified sorting from lol.theories.Sorting.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Sorting.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.List.
Import lol.theories.ListRelations.
Import lol.theories.Sorting.

Numerals O S.

Definition unsorted : list nat := cons 5 (cons 2 (cons 9 (cons 1 (cons 5 (cons 3 (nil nat)))))).

Compute insertion_sort unsorted.
Compute merge_sort unsorted.

(* Each sort returns a sorted permutation of its input. *)
Check insertion_sort_correct.
Check merge_sort_correct.

Theorem unsorted_sorted : Sorted (merge_sort unsorted).
Proof.
    apply merge_sort_sorted.
Qed.

Print Assumptions merge_sort_correct.
