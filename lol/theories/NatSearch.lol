(* Finite search returns either a witness or a proof that none exists. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.
Import lol.theories.Decidable.

Inductive bounded_result (P : nat -> Prop) (bound : nat) : Set :=
    | found : forall x : nat, le x bound -> P x -> bounded_result P bound
    | absent : (forall x : nat, le x bound -> not (P x)) -> bounded_result P bound.

Definition bounded_search (P : nat -> Prop) (decision : forall n : nat, Decidable (P n)) :
    forall bound : nat, bounded_result P bound :=
    fix go (bound : nat) {struct bound} : bounded_result P bound :=
    match bound as k return bounded_result P k with
    | O => match decision O with
        | yes _ _ h => found P O O (le_n O) h
        | no _ _ h => absent P O (fun x bound px => h
            (eq_transport nat P x O (le_zero_right x bound) px))
        end
    | S p => match go p with
        | found _ _ x bound proof => found P (S p) x (le_S x p bound) proof
        | absent _ _ missing => match decision (S p) with
            | yes _ _ h => found P (S p) (S p) (le_n (S p)) h
            | no _ _ h => absent P (S p) (fun x bound px => match nat_order_dec x p with
                | yes _ _ smaller => missing x smaller px
                | no _ _ bigger => h (eq_transport nat P x (S p) (le_antisym x (S p) bound bigger) px)
                end)
            end
        end
    end.

Definition bounded_exists_dec (P : nat -> Prop) (decision : forall n : nat, Decidable (P n)) (bound : nat) :
    Decidable (ex nat (fun x => and (le x bound) (P x))) :=
    match bounded_search P decision bound with
    | found _ _ x limit proof => yes (ex nat (fun x => and (le x bound) (P x))) (not (ex nat (fun x => and (le x bound) (P x))))
        (ex_intro nat (fun x => and (le x bound) (P x)) x (conj (le x bound) (P x) limit proof))
    | absent _ _ missing => no (ex nat (fun x => and (le x bound) (P x))) (not (ex nat (fun x => and (le x bound) (P x))))
        (fun e => match e with | ex_intro _ _ x h => missing x (and_left (le x bound) (P x) h) (and_right (le x bound) (P x) h) end)
    end.

Definition bounded_forall_dec (P : nat -> Prop) (decision : forall n : nat, Decidable (P n)) (bound : nat) :
    Decidable (forall x : nat, le x bound -> P x) :=
    match bounded_search (fun x => not (P x)) (fun n => decide_not (P n) (decision n)) bound
        return Decidable (forall x : nat, le x bound -> P x) with
    | found _ _ x limit proof => no (forall x : nat, le x bound -> P x) (not (forall x : nat, le x bound -> P x))
        (fun every => proof (every x limit))
    | absent _ _ missing => yes (forall x : nat, le x bound -> P x) (not (forall x : nat, le x bound -> P x))
        (fun x limit => decidable_double_neg (P x) (decision x) (missing x limit))
    end.

Theorem le_distinct_lt : forall n m : nat, le n m -> not (n = m) -> lt n m :=
    fun n m bound distinct => match nat_order_dec (S n) m with
    | yes _ _ smaller => smaller
    | no _ _ bigger => False_rect (lt n m) (distinct (le_antisym n m bound (le_succ_inv m n bigger)))
    end.

Theorem le_lt_or_eq : forall n m : nat, le n m -> or (lt n m) (n = m) :=
    fun n m h => match h in le _ k return or (lt n k) (n = k) with
    | le_n _ => or_intror (lt n n) (n = n) (eq_refl n)
    | le_S _ k p => or_introl (lt n (S k)) (n = (S k)) (le_succ_mono n k p)
    end.

Theorem lt_trichotomy : forall n m : nat, or (lt n m) (or (n = m) (lt m n)) :=
    fun n m => or_elim (le n m) (lt m n) (or (lt n m) (or (n = m) (lt m n)))
        (fun h => or_map (lt n m) (n = m) (lt n m) (or (n = m) (lt m n))
            (fun p => p) (fun e => or_introl (n = m) (lt m n) e) (le_lt_or_eq n m h))
        (fun h => or_intror (lt n m) (or (n = m) (lt m n)) (or_intror (n = m) (lt m n) h))
        (le_or_gt n m).

Theorem positive_nonzero : forall n : nat, lt O n -> not (n = O) :=
    fun n positive e => lt_zero_false O (eq_transport nat (lt O) n O e positive).

Theorem nonzero_positive : forall n : nat, not (n = O) -> lt O n :=
    fun n => match n as k return not (k = O) -> lt O k with
    | O => fun h => False_rect (lt O O) (h (eq_refl O))
    | S p => fun h => le_succ_mono O p (le_zero p)
    end.
