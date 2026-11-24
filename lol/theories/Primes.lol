(* Euclid's argument: every natural bound has a larger prime. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.
Import lol.theories.NatProperties.
Import lol.theories.Decidable.
Import lol.theories.Divisibility.
Import lol.theories.NatSearch.
Import lol.theories.WfNat.

Definition prime (p : nat) : Prop := and (lt one p) (forall d : nat, divides d p -> or (d = one) (d = p)).

Definition proper_factor (n d : nat) : Prop := and (lt one d) (and (lt d n) (divides d n)).

Definition proper_factor_dec (n d : nat) : Decidable (proper_factor n d) :=
    decide_and (lt one d) (and (lt d n) (divides d n)) (nat_lt_dec one d)
        (decide_and (lt d n) (divides d n) (nat_lt_dec d n) (divides_dec d n)).

Theorem prime_if_no_factor : forall n : nat, lt one n ->
    (forall d : nat, le d n -> not (proper_factor n d)) -> prime n :=
    fun n positive missing => conj (lt one n) (forall d : nat, divides d n -> or (d = one) (d = n)) positive
        (fun d => match d as k return divides k n -> or (k = one) (k = n) with
        | O => fun h => False_rect (or (O = one) (O = n))
            (lt_zero_false one (eq_transport nat (lt one) n O (zero_divides n h) positive))
        | S p => match p as k return divides (S k) n -> or ((S k) = one) ((S k) = n) with
            | O => fun h => or_introl (one = one) (one = n) (eq_refl one)
            | S q => fun h => match nat_eq_dec (S (S q)) n with
                | yes _ _ same => or_intror ((S (S q)) = one) ((S (S q)) = n) same
                | no _ _ distinct =>
                    let bound := divides_le (S (S q)) n h (positive_nonzero n (lt_le_trans O one n (lt_succ O) (lt_le one n positive))) in
                    False_rect (or ((S (S q)) = one) ((S (S q)) = n))
                        (missing (S (S q)) bound
                            (conj (lt one (S (S q))) (and (lt (S (S q)) n) (divides (S (S q)) n))
                                (le_succ_mono one (S q) (le_succ_mono O q (le_zero q)))
                                (conj (lt (S (S q)) n) (divides (S (S q)) n) (le_distinct_lt (S (S q)) n bound distinct) h)))
                end
            end
        end).

Inductive factorization_step (n : nat) : Set :=
    | already_prime : prime n -> factorization_step n
    | smaller_factor : forall d : nat, lt one d -> lt d n -> divides d n -> factorization_step n.

Definition find_factor (n : nat) (positive : lt one n) : factorization_step n :=
    match bounded_search (proper_factor n) (proper_factor_dec n) n with
    | found _ _ d bound h => smaller_factor n d
        (and_left (lt one d) (and (lt d n) (divides d n)) h)
        (and_left (lt d n) (divides d n) (and_right (lt one d) (and (lt d n) (divides d n)) h))
        (and_right (lt d n) (divides d n) (and_right (lt one d) (and (lt d n) (divides d n)) h))
    | absent _ _ missing => already_prime n (prime_if_no_factor n positive missing)
    end.

Inductive prime_factor_result (n : nat) : Set :=
    | prime_factor_intro : forall p : nat, prime p -> divides p n -> prime_factor_result n.

Definition prime_factor_step (n : nat)
    (rec : forall d : nat, lt d n -> lt one d -> prime_factor_result d)
    (positive : lt one n) : prime_factor_result n :=
    match find_factor n positive with
    | already_prime _ proof => prime_factor_intro n n proof (divides_refl n)
    | smaller_factor _ d lower upper divisor => match rec d upper lower with
        | prime_factor_intro _ p proof factor => prime_factor_intro n p proof (divides_trans p d n factor divisor)
        end
    end.

Definition prime_factor (n : nat) : lt one n -> prime_factor_result n :=
    nat_strong_recursion (fun k => lt one k -> prime_factor_result k) prime_factor_step n.

Theorem prime_factor_exists : forall n : nat, lt one n -> ex nat (fun p => and (prime p) (divides p n)) :=
    fun n positive => match prime_factor n positive with
    | prime_factor_intro _ p proof divisor => ex_intro nat (fun p => and (prime p) (divides p n)) p (conj (prime p) (divides p n) proof divisor)
    end.

Fixpoint factorial (n : nat) : nat := match n with | O => one | S p => mul (S p) (factorial p) end.

Theorem factorial_positive : forall n : nat, not ((factorial n) = O) :=
    fix go (n : nat) {struct n} : not ((factorial n) = O) :=
    match n as k return not ((factorial k) = O) with
    | O => S_not_O O
    | S p => fun e => or_elim ((S p) = O) ((factorial p) = O) False (S_not_O p) (go p) (mul_eq_zero (S p) (factorial p) e)
    end.

Theorem factorial_divisible : forall n d : nat, lt O d -> le d n -> divides d (factorial n) :=
    fix go (n d : nat) {struct n} : lt O d -> le d n -> divides d (factorial n) :=
    match n as k return lt O d -> le d k -> divides d (factorial k) with
    | O => fun positive bound => False_rect (divides d one) (lt_zero_false O (lt_le_trans O d O positive bound))
    | S p => fun positive bound => match nat_order_dec d p with
        | yes _ _ smaller => divides_mul_left d (factorial p) (S p) (go p d positive smaller)
        | no _ _ bigger => eq_transport nat (fun k => divides k (mul (S p) (factorial p))) (S p) d
            (eq_sym d (S p) (le_antisym d (S p) bound bigger))
            (divides_mul_right (S p) (S p) (factorial p) (divides_refl (S p)))
        end
    end.

Theorem sub_succ_self : forall n : nat, ((sub (S n) n) = one) :=
    fix go (n : nat) {struct n} : ((sub (S n) n) = one) :=
    match n as k return ((sub (S k) k) = one) with | O => eq_refl one | S p => go p end.

Theorem prime_above_factorial : forall n p : nat, prime p -> divides p (S (factorial n)) -> lt n p :=
    fun n p proof divisor => not_le_lt p n (fun bound =>
        let positive := and_left (lt one p) (forall d : nat, divides d p -> or (d = one) (d = p)) proof in
        let factor := factorial_divisible n p (lt_le_trans O one p (lt_succ O) (lt_le one p positive)) bound in
        let unit := eq_transport nat (divides p) (sub (S (factorial n)) (factorial n)) one (sub_succ_self (factorial n))
            (divides_sub p (S (factorial n)) (factorial n) divisor factor) in
        lt_not_le one p positive (divides_le p one unit (S_not_O O))).

Theorem primes_unbounded : forall n : nat, ex nat (fun p => and (lt n p) (prime p)) :=
    fun n => match prime_factor (S (factorial n)) (le_succ_mono one (factorial n) (nonzero_positive (factorial n) (factorial_positive n))) with
    | prime_factor_intro _ p proof divisor => ex_intro nat (fun p => and (lt n p) (prime p)) p
        (conj (lt n p) (prime p) (prime_above_factorial n p proof divisor) proof)
    end.

Theorem no_largest_prime : forall p : nat, prime p -> ex nat (fun q => and (lt p q) (prime q)) :=
    fun p proof => primes_unbounded p.
