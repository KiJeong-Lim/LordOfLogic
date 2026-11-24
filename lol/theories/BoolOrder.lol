(* Boolean comparisons reflected into the natural-number order. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Bool.
Import lol.theories.Order.

Theorem true_not_false : not (true = false) :=
    fun e => match e in eq _ b return Is_true b with | eq_refl _ => I end.
Theorem false_not_true : not (false = true) :=
    fun e => true_not_false (eq_sym false true e).
Theorem Is_true_eq : forall b : bool, Is_true b -> (b = true) :=
    fun b => match b as a return Is_true a -> (a = true) with
    | true => fun h => eq_refl true
    | false => fun h => False_rect (false = true) h
    end.
Theorem eq_Is_true : forall b : bool, (b = true) -> Is_true b :=
    fun b e => eq_transport bool Is_true true b (eq_sym b true e) I.

Theorem leb_true_sound : forall n m : nat, Is_true (leb n m) -> le n m :=
    fix go (n m : nat) {struct n} : Is_true (leb n m) -> le n m :=
    match n as k return Is_true (leb k m) -> le k m with
    | O => fun h => le_zero m
    | S p => match m as k return Is_true (leb (S p) k) -> le (S p) k with
        | O => fun h => False_rect (le (S p) O) h
        | S q => fun h => le_succ_mono p q (go p q h)
        end
    end.
Theorem leb_false_sound : forall n m : nat, Is_true (negb (leb n m)) -> lt m n :=
    fix go (n m : nat) {struct n} : Is_true (negb (leb n m)) -> lt m n :=
    match n as k return Is_true (negb (leb k m)) -> lt m k with
    | O => fun h => False_rect (lt m O) h
    | S p => match m as k return Is_true (negb (leb (S p) k)) -> lt k (S p) with
        | O => fun h => le_succ_mono O p (le_zero p)
        | S q => fun h => le_succ_mono (S q) p (go p q h)
        end
    end.
Theorem leb_true_complete : forall n m : nat, le n m -> Is_true (leb n m) :=
    fix go (n m : nat) {struct n} : le n m -> Is_true (leb n m) :=
    match n as k return le k m -> Is_true (leb k m) with
    | O => fun h => I
    | S p => match m as k return le (S p) k -> Is_true (leb (S p) k) with
        | O => fun h => lt_zero_false p h
        | S q => fun h => go p q (le_succ_inv p q h)
        end
    end.
Theorem leb_false_complete : forall n m : nat, lt m n -> Is_true (negb (leb n m)) :=
    fix go (n m : nat) {struct n} : lt m n -> Is_true (negb (leb n m)) :=
    match n as k return lt m k -> Is_true (negb (leb k m)) with
    | O => fun h => lt_zero_false m h
    | S p => match m as k return lt k (S p) -> Is_true (negb (leb (S p) k)) with
        | O => fun h => I
        | S q => fun h => go p q (le_succ_inv (S q) p h)
        end
    end.
Theorem leb_true_iff : forall n m : nat, iff (Is_true (leb n m)) (le n m) :=
    fun n m => conj (Is_true (leb n m) -> le n m) (le n m -> Is_true (leb n m))
        (leb_true_sound n m) (leb_true_complete n m).
Theorem leb_false_iff : forall n m : nat, iff (Is_true (negb (leb n m))) (lt m n) :=
    fun n m => conj (Is_true (negb (leb n m)) -> lt m n) (lt m n -> Is_true (negb (leb n m)))
        (leb_false_sound n m) (leb_false_complete n m).
Theorem ltb_true_sound : forall n m : nat, Is_true (ltb n m) -> lt n m :=
    fun n m => leb_true_sound (S n) m.
Theorem ltb_true_complete : forall n m : nat, lt n m -> Is_true (ltb n m) :=
    fun n m => leb_true_complete (S n) m.
Theorem ltb_true_iff : forall n m : nat, iff (Is_true (ltb n m)) (lt n m) :=
    fun n m => leb_true_iff (S n) m.
Theorem leb_spec : forall n m : nat, match leb n m return Prop with | true => le n m | false => lt m n end :=
    fun n m => (match leb n m as b return
        (Is_true b -> le n m) -> (Is_true (negb b) -> lt m n) ->
        (match b return Prop with | true => le n m | false => lt m n end) with
    | true => fun yes no => yes I
    | false => fun yes no => no I
    end) (leb_true_sound n m) (leb_false_sound n m).
