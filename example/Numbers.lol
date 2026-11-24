(* Division, greatest common divisors and primes from the standard library.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Numbers.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Division.
Import lol.theories.Gcd.
Import lol.theories.Primes.

Numerals O S.

(* div and gcd are defined by well-founded recursion, and they compute. *)
Compute div 17 5.
Compute modulo 17 5.
Compute gcd 12 18.
Compute factorial 4.

Theorem gcd_12_18 : gcd 12 18 = 6.
Proof.
    reflexivity.
Qed.

Check div_mod.
Check gcd_greatest.

(* There is a prime above any number. *)
Check primes_unbounded.
Print Assumptions primes_unbounded.
