(* Constructive divisibility witnesses and the Euclidean remainder invariant. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.
Import lol.theories.NatProperties.
Import lol.theories.Division.
Import lol.theories.Decidable.

Definition divides (d n : nat) : Prop := ex nat (fun k => n = (mul k d)).

Theorem divides_intro : forall d n k : nat, (n = (mul k d)) -> divides d n :=
    fun d n k e => ex_intro nat (fun q => n = (mul q d)) k e.

Theorem divides_zero : forall d : nat, divides d O := fun d => divides_intro d O O (eq_refl O).

Theorem divides_refl : forall d : nat, divides d d :=
    fun d => divides_intro d d one (eq_sym (mul one d) d (mul_one_left d)).

Theorem one_divides : forall n : nat, divides one n :=
    fun n => divides_intro one n n (eq_sym (mul n one) n (mul_one_right n)).

Theorem zero_divides : forall n : nat, divides O n -> (n = O) :=
    fun n h => match h with
    | ex_intro _ _ k e => eq_trans n (mul k O) O e (mul_n_O k)
    end.

Theorem divides_trans : forall d a b : nat, divides d a -> divides a b -> divides d b :=
    fun d a b h j => match h with
    | ex_intro _ _ k e => match j with
        | ex_intro _ _ l f => divides_intro d b (mul l k)
            (eq_trans b (mul l a) (mul (mul l k) d) f
                (eq_trans (mul l a) (mul l (mul k d)) (mul (mul l k) d)
                    (f_equal (mul l) a (mul k d) e)
                    (eq_sym (mul (mul l k) d) (mul l (mul k d)) (mul_assoc l k d))))
        end
    end.

Theorem divides_add : forall d a b : nat, divides d a -> divides d b -> divides d (add a b) :=
    fun d a b h j => match h with
    | ex_intro _ _ k e => match j with
        | ex_intro _ _ l f => divides_intro d (add a b) (add k l)
            (eq_trans (add a b) (add (mul k d) b) (mul (add k l) d)
                (f_equal (fun q : nat => add q b) a (mul k d) e)
                (eq_trans (add (mul k d) b) (add (mul k d) (mul l d)) (mul (add k l) d)
                    (f_equal (add (mul k d)) b (mul l d) f)
                    (eq_sym (mul (add k l) d) (add (mul k d) (mul l d)) (mul_add_left k l d))))
        end
    end.

Theorem divides_mul_left : forall d n m : nat, divides d n -> divides d (mul m n) :=
    fun d n m h => divides_trans d n (mul m n) h (divides_intro n (mul m n) m (eq_refl (mul m n))).

Theorem divides_mul_right : forall d n m : nat, divides d n -> divides d (mul n m) :=
    fun d n m h => eq_transport nat (divides d) (mul m n) (mul n m) (mul_comm m n) (divides_mul_left d n m h).

Theorem divides_sub : forall d a b : nat, divides d a -> divides d b -> divides d (sub a b) :=
    fun d a b h j => match h with
    | ex_intro _ _ k e => match j with
        | ex_intro _ _ l f => divides_intro d (sub a b) (sub k l)
            (eq_trans (sub a b) (sub (mul k d) b) (mul (sub k l) d)
                (f_equal (fun q : nat => sub q b) a (mul k d) e)
                (eq_trans (sub (mul k d) b) (sub (mul k d) (mul l d)) (mul (sub k l) d)
                    (f_equal (sub (mul k d)) b (mul l d) f)
                    (eq_sym (mul (sub k l) d) (sub (mul k d) (mul l d)) (mul_sub_left k l d))))
        end
    end.

Theorem modulo_as_sub : forall n d : nat, ((modulo n d) = (sub n (mul (div n d) d))) :=
    fun n d => eq_trans (modulo n d) (sub (add (mul (div n d) d) (modulo n d)) (mul (div n d) d)) (sub n (mul (div n d) d))
        (eq_sym (sub (add (mul (div n d) d) (modulo n d)) (mul (div n d) d)) (modulo n d) (sub_add_left (mul (div n d) d) (modulo n d)))
        (f_equal (fun k : nat => sub k (mul (div n d) d)) (add (mul (div n d) d) (modulo n d)) n
            (eq_sym n (add (mul (div n d) d) (modulo n d)) (div_mod n d))).

Theorem common_divides_modulo : forall d a b : nat, divides d a -> divides d b -> divides d (modulo a b) :=
    fun d a b h j => eq_transport nat (divides d) (sub a (mul (div a b) b)) (modulo a b)
        (eq_sym (modulo a b) (sub a (mul (div a b) b)) (modulo_as_sub a b))
        (divides_sub d a (mul (div a b) b) h (divides_mul_left d b (div a b) j)).

Theorem divides_from_modulo : forall d a b : nat, divides d b -> divides d (modulo a b) -> divides d a :=
    fun d a b h j => eq_transport nat (divides d) (add (mul (div a b) b) (modulo a b)) a
        (eq_sym a (add (mul (div a b) b) (modulo a b)) (div_mod a b))
        (divides_add d (mul (div a b) b) (modulo a b) (divides_mul_left d b (div a b) h) j).

Theorem divides_modulo_iff : forall d a b : nat, divides d b -> iff (divides d a) (divides d (modulo a b)) :=
    fun d a b h => conj (divides d a -> divides d (modulo a b)) (divides d (modulo a b) -> divides d a)
        (fun j => common_divides_modulo d a b j h) (divides_from_modulo d a b h).

Theorem modulo_zero_divides : forall d n : nat, ((modulo n d) = O) -> divides d n :=
    fun d n e => divides_intro d n (div n d)
        (eq_trans n (add (mul (div n d) d) (modulo n d)) (mul (div n d) d) (div_mod n d)
            (eq_trans (add (mul (div n d) d) (modulo n d)) (add (mul (div n d) d) O) (mul (div n d) d)
                (f_equal (add (mul (div n d) d)) (modulo n d) O e) (add_n_O (mul (div n d) d)))).

Theorem divides_le : forall d n : nat, divides d n -> not (n = O) -> le d n :=
    fun d n h => match h with
    | ex_intro _ _ k e => (match k as q return (n = (mul q d)) -> not (n = O) -> le d n with
        | O => fun same nonzero => False_rect (le d n) (nonzero same)
        | S p => fun same nonzero => eq_transport nat (le d) (add d (mul p d)) n
            (eq_sym n (add d (mul p d)) same) (le_add_left d (mul p d))
        end) e
    end.

Theorem divides_antisym : forall a b : nat, divides a b -> divides b a -> (a = b) :=
    fun a b h j => match a as n return divides n b -> divides b n -> (n = b) with
    | O => fun p q => eq_sym b O (zero_divides b p)
    | S n => fun p q => match b as m return divides (S n) m -> divides m (S n) -> ((S n) = m) with
        | O => fun r s => False_rect ((S n) = O) (S_not_O n (zero_divides (S n) s))
        | S m => fun r s => le_antisym (S n) (S m)
            (divides_le (S n) (S m) r (S_not_O m)) (divides_le (S m) (S n) s (S_not_O n))
        end p q
    end h j.

Theorem small_multiple_zero : forall d r : nat, divides d r -> lt r d -> (r = O) :=
    fun d r => match r as n return divides d n -> lt n d -> (n = O) with
    | O => fun h bound => eq_refl O
    | S p => fun h bound => False_rect ((S p) = O)
        (lt_not_le (S p) d bound (divides_le d (S p) h (S_not_O p)))
    end.

Theorem divides_modulo_zero : forall d n : nat, divides d n -> ((modulo n d) = O) :=
    fun d n => match d as k return divides k n -> ((modulo n k) = O) with
    | O => fun h => zero_divides n h
    | S p => fun h => small_multiple_zero (S p) (modulo n (S p))
        (common_divides_modulo (S p) n (S p) h (divides_refl (S p))) (modulo_bound n p)
    end.

Theorem divides_modulo_zero_iff : forall d n : nat, iff (divides d n) ((modulo n d) = O) :=
    fun d n => conj (divides d n -> ((modulo n d) = O)) (((modulo n d) = O) -> divides d n)
        (divides_modulo_zero d n) (modulo_zero_divides d n).

Definition divides_dec (d n : nat) : Decidable (divides d n) :=
    decide_transport ((modulo n d) = O) (divides d n)
        (iff_sym (divides d n) ((modulo n d) = O) (divides_modulo_zero_iff d n))
        (nat_eq_dec (modulo n d) O).

Theorem divides_add_cancel : forall d a b : nat, divides d a -> divides d (add a b) -> divides d b :=
    fun d a b h j => eq_transport nat (divides d) (sub (add a b) a) b (sub_add_left a b)
        (divides_sub d (add a b) a j h).

Theorem divides_mul_mono : forall a b c d : nat, divides a b -> divides c d -> divides (mul a c) (mul b d) :=
    fun a b c d h j => match h return divides (mul a c) (mul b d) with
    | ex_intro _ _ k e => match j return divides (mul a c) (mul b d) with
        | ex_intro _ _ l f => divides_intro (mul a c) (mul b d) (mul k l)
            (eq_trans (mul b d) (mul (mul k a) (mul l c)) (mul (mul k l) (mul a c))
                (eq_trans (mul b d) (mul (mul k a) d) (mul (mul k a) (mul l c))
                    (f_equal (fun q : nat => mul q d) b (mul k a) e)
                    (f_equal (mul (mul k a)) d (mul l c) f))
                (eq_trans (mul (mul k a) (mul l c)) (mul k (mul a (mul l c))) (mul (mul k l) (mul a c))
                    (mul_assoc k a (mul l c))
                    (eq_trans (mul k (mul a (mul l c))) (mul k (mul l (mul a c))) (mul (mul k l) (mul a c))
                        (f_equal (mul k) (mul a (mul l c)) (mul l (mul a c)) (mul_left_comm a l c))
                        (eq_sym (mul (mul k l) (mul a c)) (mul k (mul l (mul a c))) (mul_assoc k l (mul a c))))))
        end
    end.

Theorem divides_mul_cancel : forall p a b : nat, not (p = O) -> divides (mul a p) (mul b p) -> divides a b :=
    fun p a b nonzero h => match h return divides a b with
    | ex_intro _ _ k e => divides_intro a b k (mul_cancel_right p b (mul k a) nonzero
        (eq_trans (mul b p) (mul k (mul a p)) (mul (mul k a) p) e
            (eq_sym (mul (mul k a) p) (mul k (mul a p)) (mul_assoc k a p))))
    end.

Theorem divides_div_exact : forall d n : nat, divides d n -> (n = (mul (div n d) d)) :=
    fun d n h => eq_trans n (add (mul (div n d) d) (modulo n d)) (mul (div n d) d) (div_mod n d)
        (eq_trans (add (mul (div n d) d) (modulo n d)) (add (mul (div n d) d) O) (mul (div n d) d)
            (f_equal (add (mul (div n d) d)) (modulo n d) O (divides_modulo_zero d n h))
            (add_n_O (mul (div n d) d))).
