(* Euclid's algorithm with a greatest-common-divisor certificate. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.
Import lol.theories.Division.
Import lol.theories.Divisibility.
Import lol.theories.WfNat.

Definition is_gcd (a b g : nat) : Prop :=
    and (divides g a) (and (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g)).

Inductive gcd_result (a b : nat) : Set := | gcd_intro : forall g : nat, is_gcd a b g -> gcd_result a b.

Definition gcd_value (a b : nat) (result : gcd_result a b) : nat :=
    match result with | gcd_intro _ _ g proof => g end.

Theorem gcd_result_spec : forall (a b : nat) (result : gcd_result a b), is_gcd a b (gcd_value a b result) :=
    fun a b result => match result as r return is_gcd a b (gcd_value a b r) with
    | gcd_intro _ _ g proof => proof
    end.

Theorem is_gcd_zero : forall a : nat, is_gcd a O a :=
    fun a => conj (divides a a) (and (divides a O) (forall d : nat, divides d a -> divides d O -> divides d a))
        (divides_refl a)
        (conj (divides a O) (forall d : nat, divides d a -> divides d O -> divides d a) (divides_zero a) (fun d h j => h)).

Theorem is_gcd_euclid : forall a b g : nat, is_gcd b (modulo a b) g -> is_gcd a b g :=
    fun a b g h =>
        let gb := and_left (divides g b) (and (divides g (modulo a b)) (forall d : nat, divides d b -> divides d (modulo a b) -> divides d g)) h in
        let rest := and_right (divides g b) (and (divides g (modulo a b)) (forall d : nat, divides d b -> divides d (modulo a b) -> divides d g)) h in
        let gr := and_left (divides g (modulo a b)) (forall d : nat, divides d b -> divides d (modulo a b) -> divides d g) rest in
        let greatest := and_right (divides g (modulo a b)) (forall d : nat, divides d b -> divides d (modulo a b) -> divides d g) rest in
        conj (divides g a) (and (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g))
            (divides_from_modulo g a b gb gr)
            (conj (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g) gb
                (fun d da db => greatest d db (common_divides_modulo d a b da db))).

Definition gcd_step (b : nat) : (forall r : nat, lt r b -> forall a : nat, gcd_result a r) -> forall a : nat, gcd_result a b :=
    match b as k return (forall r : nat, lt r k -> forall a : nat, gcd_result a r) -> forall a : nat, gcd_result a k with
    | O => fun rec a => gcd_intro a O a (is_gcd_zero a)
    | S p => fun rec a => match rec (modulo a (S p)) (modulo_bound a p) (S p) with
        | gcd_intro _ _ g proof => gcd_intro a (S p) g (is_gcd_euclid a (S p) g proof)
        end
    end.

Definition gcd_compute (a b : nat) : gcd_result a b :=
    nat_strong_recursion (fun k => forall n : nat, gcd_result n k) gcd_step b a.

Definition gcd (a b : nat) : nat := gcd_value a b (gcd_compute a b).

Theorem gcd_spec : forall a b : nat, is_gcd a b (gcd a b) := fun a b => gcd_result_spec a b (gcd_compute a b).

Theorem gcd_divides_left : forall a b : nat, divides (gcd a b) a :=
    fun a b => and_left (divides (gcd a b) a)
        (and (divides (gcd a b) b) (forall d : nat, divides d a -> divides d b -> divides d (gcd a b))) (gcd_spec a b).

Theorem gcd_divides_right : forall a b : nat, divides (gcd a b) b :=
    fun a b => and_left (divides (gcd a b) b) (forall d : nat, divides d a -> divides d b -> divides d (gcd a b))
        (and_right (divides (gcd a b) a)
            (and (divides (gcd a b) b) (forall d : nat, divides d a -> divides d b -> divides d (gcd a b))) (gcd_spec a b)).

Theorem gcd_greatest : forall a b d : nat, divides d a -> divides d b -> divides d (gcd a b) :=
    fun a b => and_right (divides (gcd a b) b) (forall d : nat, divides d a -> divides d b -> divides d (gcd a b))
        (and_right (divides (gcd a b) a)
            (and (divides (gcd a b) b) (forall d : nat, divides d a -> divides d b -> divides d (gcd a b))) (gcd_spec a b)).

Theorem is_gcd_unique : forall a b g h : nat, is_gcd a b g -> is_gcd a b h -> (g = h) :=
    fun a b g h pg ph =>
        let g_rest := and_right (divides g a) (and (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g)) pg in
        let h_rest := and_right (divides h a) (and (divides h b) (forall d : nat, divides d a -> divides d b -> divides d h)) ph in
        divides_antisym g h
            (and_right (divides h b) (forall d : nat, divides d a -> divides d b -> divides d h) h_rest g
                (and_left (divides g a) (and (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g)) pg)
                (and_left (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g) g_rest))
            (and_right (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g) g_rest h
                (and_left (divides h a) (and (divides h b) (forall d : nat, divides d a -> divides d b -> divides d h)) ph)
                (and_left (divides h b) (forall d : nat, divides d a -> divides d b -> divides d h) h_rest)).

Theorem gcd_zero_right : forall a : nat, ((gcd a O) = a) :=
    fun a => is_gcd_unique a O (gcd a O) a (gcd_spec a O) (is_gcd_zero a).

Theorem gcd_euclid : forall a b : nat, ((gcd a b) = (gcd b (modulo a b))) :=
    fun a b => is_gcd_unique a b (gcd a b) (gcd b (modulo a b)) (gcd_spec a b)
        (is_gcd_euclid a b (gcd b (modulo a b)) (gcd_spec b (modulo a b))).

Theorem is_gcd_sym : forall a b g : nat, is_gcd a b g -> is_gcd b a g :=
    fun a b g h =>
        let rest := and_right (divides g a) (and (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g)) h in
        conj (divides g b) (and (divides g a) (forall d : nat, divides d b -> divides d a -> divides d g))
            (and_left (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g) rest)
            (conj (divides g a) (forall d : nat, divides d b -> divides d a -> divides d g)
                (and_left (divides g a) (and (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g)) h)
                (fun d db da => and_right (divides g b) (forall d : nat, divides d a -> divides d b -> divides d g) rest d da db)).

Theorem gcd_comm : forall a b : nat, ((gcd a b) = (gcd b a)) :=
    fun a b => is_gcd_unique a b (gcd a b) (gcd b a) (gcd_spec a b) (is_gcd_sym b a (gcd b a) (gcd_spec b a)).

Theorem gcd_assoc : forall a b c : nat, ((gcd (gcd a b) c) = (gcd a (gcd b c))) :=
    fun a b c => is_gcd_unique a (gcd b c) (gcd (gcd a b) c) (gcd a (gcd b c))
        (conj (divides (gcd (gcd a b) c) a)
            (and (divides (gcd (gcd a b) c) (gcd b c)) (forall d : nat, divides d a -> divides d (gcd b c) -> divides d (gcd (gcd a b) c)))
            (divides_trans (gcd (gcd a b) c) (gcd a b) a (gcd_divides_left (gcd a b) c) (gcd_divides_left a b))
            (conj (divides (gcd (gcd a b) c) (gcd b c)) (forall d : nat, divides d a -> divides d (gcd b c) -> divides d (gcd (gcd a b) c))
                (gcd_greatest b c (gcd (gcd a b) c)
                    (divides_trans (gcd (gcd a b) c) (gcd a b) b (gcd_divides_left (gcd a b) c) (gcd_divides_right a b))
                    (gcd_divides_right (gcd a b) c))
                (fun d da dbc => gcd_greatest (gcd a b) c d
                    (gcd_greatest a b d da (divides_trans d (gcd b c) b dbc (gcd_divides_left b c)))
                    (divides_trans d (gcd b c) c dbc (gcd_divides_right b c)))))
        (gcd_spec a (gcd b c)).

Theorem divides_gcd_iff : forall a b : nat, iff (divides a b) ((gcd a b) = a) :=
    fun a b => conj (divides a b -> ((gcd a b) = a)) (((gcd a b) = a) -> divides a b)
        (fun h => is_gcd_unique a b (gcd a b) a (gcd_spec a b)
            (conj (divides a a) (and (divides a b) (forall d : nat, divides d a -> divides d b -> divides d a))
                (divides_refl a)
                (conj (divides a b) (forall d : nat, divides d a -> divides d b -> divides d a) h (fun d da db => da))))
        (fun e => eq_transport nat (fun k => divides k b) (gcd a b) a e (gcd_divides_right a b)).

Theorem gcd_eq_zero : forall a b : nat, ((gcd a b) = O) -> and (a = O) (b = O) :=
    fun a b e => conj (a = O) (b = O)
        (zero_divides a (eq_transport nat (fun k => divides k a) (gcd a b) O e (gcd_divides_left a b)))
        (zero_divides b (eq_transport nat (fun k => divides k b) (gcd a b) O e (gcd_divides_right a b))).
