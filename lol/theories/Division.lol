(* Division by positive naturals computes through well-founded recursion. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.
Import lol.theories.NatProperties.
Import lol.theories.Decidable.
Import lol.theories.WfNat.

Inductive division_result (n d : nat) : Set :=
    | division_intro : forall q r : nat, (n = (add (mul q d) r)) -> lt r d -> division_result n d.

Definition quotient (n d : nat) (result : division_result n d) : nat :=
    match result with | division_intro _ _ q r equation bound => q end.

Definition remainder (n d : nat) (result : division_result n d) : nat :=
    match result with | division_intro _ _ q r equation bound => r end.

Theorem division_equation : forall (n d : nat) (result : division_result n d),
    (n = (add (mul (quotient n d result) d) (remainder n d result))) :=
    fun n d result => match result as a return (n = (add (mul (quotient n d a) d) (remainder n d a))) with
    | division_intro _ _ q r equation bound => equation
    end.

Theorem division_bound : forall (n d : nat) (result : division_result n d), lt (remainder n d result) d :=
    fun n d result => match result as a return lt (remainder n d a) d with
    | division_intro _ _ q r equation bound => bound
    end.

Theorem division_decrease : forall n d : nat, le (S d) n -> lt (sub n (S d)) n :=
    fun n d h => sub_succ_strict n d
        (le_trans (S O) (S d) n (le_succ_mono O d (le_zero d)) h).

Theorem division_subtract_equation : forall n d q r : nat,
    le d n -> ((sub n d) = (add (mul q d) r)) -> (n = (add (mul (S q) d) r)) :=
    fun n d q r h e => eq_trans n (add d (sub n d)) (add (add d (mul q d)) r)
        (eq_sym (add d (sub n d)) n (add_sub_cancel n d h))
        (eq_trans (add d (sub n d)) (add d (add (mul q d) r)) (add (add d (mul q d)) r)
            (f_equal (add d) (sub n d) (add (mul q d) r) e)
            (eq_sym (add (add d (mul q d)) r) (add d (add (mul q d) r)) (add_assoc d (mul q d) r))).

Definition division_step (d n : nat)
    (rec : forall m : nat, lt m n -> division_result m (S d)) : division_result n (S d) :=
    match nat_order_dec (S d) n with
    | yes _ _ h => match rec (sub n (S d)) (division_decrease n d h) with
        | division_intro _ _ q r e bound => division_intro n (S d) (S q) r
            (division_subtract_equation n (S d) q r h e) bound
        end
    | no _ _ h => division_intro n (S d) O n (eq_refl n) h
    end.

Definition division (n d : nat) : division_result n (S d) :=
    nat_strong_recursion (fun k => division_result k (S d)) (division_step d) n.

(* The zero divisor has the explicit total convention (quotient 0, remainder n). *)
Definition div (n d : nat) : nat :=
    match d with | O => O | S p => quotient n (S p) (division n p) end.

Definition modulo (n d : nat) : nat :=
    match d with | O => n | S p => remainder n (S p) (division n p) end.

Theorem div_mod : forall n d : nat, (n = (add (mul (div n d) d) (modulo n d))) :=
    fun n d => match d as k return (n = (add (mul (div n k) k) (modulo n k))) with
    | O => eq_refl n
    | S p => division_equation n (S p) (division n p)
    end.

Theorem modulo_bound : forall n d : nat, lt (modulo n (S d)) (S d) :=
    fun n d => division_bound n (S d) (division n d).

Theorem modulo_positive_bound : forall n d : nat, not (d = O) -> lt (modulo n d) d :=
    fun n d => match d as k return not (k = O) -> lt (modulo n k) k with
    | O => fun h => False_rect (lt n O) (h (eq_refl O))
    | S p => fun h => modulo_bound n p
    end.

Theorem div_zero_divisor : forall n : nat, ((div n O) = O) := fun n => eq_refl O.

Theorem modulo_zero_divisor : forall n : nat, ((modulo n O) = n) := fun n => eq_refl n.

Theorem div_product_le : forall n d : nat, le (mul (div n d) d) n :=
    fun n d => eq_transport nat (le (mul (div n d) d)) (add (mul (div n d) d) (modulo n d)) n
        (eq_sym n (add (mul (div n d) d) (modulo n d)) (div_mod n d))
        (le_add_left (mul (div n d) d) (modulo n d)).

Theorem modulo_le : forall n d : nat, le (modulo n d) n :=
    fun n d => eq_transport nat (le (modulo n d)) (add (mul (div n d) d) (modulo n d)) n
        (eq_sym n (add (mul (div n d) d) (modulo n d)) (div_mod n d))
        (le_add_right (mul (div n d) d) (modulo n d)).

Theorem modulo_zero : forall d : nat, ((modulo O d) = O) :=
    fun d => le_zero_right (modulo O d) (modulo_le O d).

Theorem division_unique_remainders : forall n d q r q' r' : nat,
    (n = (add (mul q d) r)) -> (n = (add (mul q' d) r')) -> (q = q') -> (r = r') :=
    fun n d q r q' r' e e' same => add_cancel_left (mul q d) r r'
        (eq_trans (add (mul q d) r) n (add (mul q d) r')
            (eq_sym n (add (mul q d) r) e)
            (eq_trans n (add (mul q' d) r') (add (mul q d) r') e'
                (f_equal (fun k : nat => add (mul k d) r') q' q (eq_sym q q' same)))).

(* The quotient and the remainder below a positive divisor are unique. *)
Theorem division_unique : forall d q q' r r' : nat, lt r d -> lt r' d ->
    ((add (mul q d) r) = (add (mul q' d) r')) -> and (q = q') (r = r') :=
    fun d => fix go (q q' : nat) {struct q} : forall r r' : nat, lt r d -> lt r' d ->
        ((add (mul q d) r) = (add (mul q' d) r')) -> and (q = q') (r = r') :=
    match q as k return forall r r' : nat, lt r d -> lt r' d ->
        ((add (mul k d) r) = (add (mul q' d) r')) -> and (k = q') (r = r') with
    | O => match q' as k return forall r r' : nat, lt r d -> lt r' d ->
            ((add (mul O d) r) = (add (mul k d) r')) -> and (O = k) (r = r') with
        | O => fun r r' h h' e => conj (O = O) (r = r') (eq_refl O) e
        | S p' => fun r r' h h' e => False_rect (and (O = (S p')) (r = r'))
            (lt_not_le r d h (eq_transport nat (le d) (add (add d (mul p' d)) r') r
                (eq_sym r (add (add d (mul p' d)) r') e)
                (le_trans d (add d (mul p' d)) (add (add d (mul p' d)) r')
                    (le_add_left d (mul p' d)) (le_add_left (add d (mul p' d)) r'))))
        end
    | S p => match q' as k return forall r r' : nat, lt r d -> lt r' d ->
            ((add (mul (S p) d) r) = (add (mul k d) r')) -> and ((S p) = k) (r = r') with
        | O => fun r r' h h' e => False_rect (and ((S p) = O) (r = r'))
            (lt_not_le r' d h' (eq_transport nat (le d) (add (add d (mul p d)) r) r' e
                (le_trans d (add d (mul p d)) (add (add d (mul p d)) r)
                    (le_add_left d (mul p d)) (le_add_left (add d (mul p d)) r))))
        | S p' => fun r r' h h' e => and_map (p = p') (r = r') ((S p) = (S p')) (r = r')
            (f_equal S p p') (fun same => same)
            (go p p' r r' h h'
                (add_cancel_left d (add (mul p d) r) (add (mul p' d) r')
                    (eq_trans (add d (add (mul p d) r)) (add (add d (mul p d)) r) (add d (add (mul p' d) r'))
                        (eq_sym (add (add d (mul p d)) r) (add d (add (mul p d) r)) (add_assoc d (mul p d) r))
                        (eq_trans (add (add d (mul p d)) r) (add (add d (mul p' d)) r') (add d (add (mul p' d) r'))
                            e (add_assoc d (mul p' d) r')))))
        end
    end.

Theorem div_unique : forall n d q r : nat, lt r d -> (n = (add (mul q d) r)) -> ((div n d) = q) :=
    fun n d => match d as k return forall q r : nat, lt r k -> (n = (add (mul q k) r)) -> ((div n k) = q) with
    | O => fun q r h e => False_rect ((div n O) = q) (lt_zero_false r h)
    | S p => fun q r h e => and_left ((div n (S p)) = q) ((modulo n (S p)) = r)
        (division_unique (S p) (div n (S p)) q (modulo n (S p)) r (modulo_bound n p) h
            (eq_trans (add (mul (div n (S p)) (S p)) (modulo n (S p))) n (add (mul q (S p)) r)
                (eq_sym n (add (mul (div n (S p)) (S p)) (modulo n (S p))) (div_mod n (S p))) e))
    end.

Theorem modulo_unique : forall n d q r : nat, lt r d -> (n = (add (mul q d) r)) -> ((modulo n d) = r) :=
    fun n d q r h e => division_unique_remainders n d (div n d) (modulo n d) q r
        (div_mod n d) e (div_unique n d q r h e).

Theorem modulo_idempotent : forall n d : nat, ((modulo (modulo n d) d) = (modulo n d)) :=
    fun n d => match d as k return ((modulo (modulo n k) k) = (modulo n k)) with
    | O => eq_refl n
    | S p => modulo_unique (modulo n (S p)) (S p) O (modulo n (S p)) (modulo_bound n p) (eq_refl (modulo n (S p)))
    end.

Theorem div_multiple : forall q d : nat, not (d = O) -> ((div (mul q d) d) = q) :=
    fun q d => match d as k return not (k = O) -> ((div (mul q k) k) = q) with
    | O => fun h => False_rect ((div (mul q O) O) = q) (h (eq_refl O))
    | S p => fun h => div_unique (mul q (S p)) (S p) q O (le_succ_mono O p (le_zero p))
        (eq_sym (add (mul q (S p)) O) (mul q (S p)) (add_n_O (mul q (S p))))
    end.

Theorem modulo_add_multiple : forall q d r : nat, ((modulo (add (mul q d) r) d) = (modulo r d)) :=
    fun q d r => match d as k return ((modulo (add (mul q k) r) k) = (modulo r k)) with
    | O => f_equal (fun k : nat => add k r) (mul q O) O (mul_n_O q)
    | S p => modulo_unique (add (mul q (S p)) r) (S p) (add q (div r (S p))) (modulo r (S p))
        (modulo_bound r p)
        (eq_trans (add (mul q (S p)) r)
            (add (mul q (S p)) (add (mul (div r (S p)) (S p)) (modulo r (S p))))
            (add (mul (add q (div r (S p))) (S p)) (modulo r (S p)))
            (f_equal (add (mul q (S p))) r (add (mul (div r (S p)) (S p)) (modulo r (S p))) (div_mod r (S p)))
            (eq_trans (add (mul q (S p)) (add (mul (div r (S p)) (S p)) (modulo r (S p))))
                (add (add (mul q (S p)) (mul (div r (S p)) (S p))) (modulo r (S p)))
                (add (mul (add q (div r (S p))) (S p)) (modulo r (S p)))
                (eq_sym (add (add (mul q (S p)) (mul (div r (S p)) (S p))) (modulo r (S p)))
                    (add (mul q (S p)) (add (mul (div r (S p)) (S p)) (modulo r (S p))))
                    (add_assoc (mul q (S p)) (mul (div r (S p)) (S p)) (modulo r (S p))))
                (f_equal (fun k : nat => add k (modulo r (S p)))
                    (add (mul q (S p)) (mul (div r (S p)) (S p))) (mul (add q (div r (S p))) (S p))
                    (eq_sym (mul (add q (div r (S p))) (S p)) (add (mul q (S p)) (mul (div r (S p)) (S p)))
                        (mul_add_left q (div r (S p)) (S p))))))
    end.
