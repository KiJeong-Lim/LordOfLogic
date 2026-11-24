(* Minimum and maximum form the constructive lattice of natural order. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.

Theorem min_greatest : forall n m p : nat, le p n -> le p m -> le p (min n m) :=
    fix go (n m p : nat) {struct n} : le p n -> le p m -> le p (min n m) :=
    match n as k return le p k -> le p m -> le p (min k m) with
    | O => fun h j => h
    | S q => match m as k return le p (S q) -> le p k -> le p (min (S q) k) with
        | O => fun h j => j
        | S r => match p as k return le k (S q) -> le k (S r) -> le k (S (min q r)) with
            | O => fun h j => le_zero (S (min q r))
            | S s => fun h j => le_succ_mono s (min q r) (go q r s (le_succ_inv s q h) (le_succ_inv s r j))
            end
        end
    end.

Theorem max_least : forall n m p : nat, le n p -> le m p -> le (max n m) p :=
    fix go (n m p : nat) {struct n} : le n p -> le m p -> le (max n m) p :=
    match n as k return le k p -> le m p -> le (max k m) p with
    | O => fun h j => j
    | S q => match m as k return le (S q) p -> le k p -> le (max (S q) k) p with
        | O => fun h j => h
        | S r => match p as k return le (S q) k -> le (S r) k -> le (S (max q r)) k with
            | O => fun h j => False_rect (le (S (max q r)) O) (lt_zero_false q h)
            | S s => fun h j => le_succ_mono (max q r) s (go q r s (le_succ_inv q s h) (le_succ_inv r s j))
            end
        end
    end.

Theorem min_comm : forall n m : nat, ((min n m) = (min m n)) :=
    fun n m => le_antisym (min n m) (min m n)
        (min_greatest m n (min n m) (min_le_right n m) (min_le_left n m))
        (min_greatest n m (min m n) (min_le_right m n) (min_le_left m n)).

Theorem max_comm : forall n m : nat, ((max n m) = (max m n)) :=
    fun n m => le_antisym (max n m) (max m n)
        (max_least n m (max m n) (le_max_right m n) (le_max_left m n))
        (max_least m n (max n m) (le_max_right n m) (le_max_left n m)).

Theorem min_assoc : forall n m p : nat, ((min (min n m) p) = (min n (min m p))) :=
    fun n m p => le_antisym (min (min n m) p) (min n (min m p))
        (min_greatest n (min m p) (min (min n m) p)
            (le_trans (min (min n m) p) (min n m) n (min_le_left (min n m) p) (min_le_left n m))
            (min_greatest m p (min (min n m) p)
                (le_trans (min (min n m) p) (min n m) m (min_le_left (min n m) p) (min_le_right n m)) (min_le_right (min n m) p)))
        (min_greatest (min n m) p (min n (min m p))
            (min_greatest n m (min n (min m p)) (min_le_left n (min m p))
                (le_trans (min n (min m p)) (min m p) m (min_le_right n (min m p)) (min_le_left m p)))
            (le_trans (min n (min m p)) (min m p) p (min_le_right n (min m p)) (min_le_right m p))).

Theorem max_assoc : forall n m p : nat, ((max (max n m) p) = (max n (max m p))) :=
    fun n m p => le_antisym (max (max n m) p) (max n (max m p))
        (max_least (max n m) p (max n (max m p))
            (max_least n m (max n (max m p)) (le_max_left n (max m p))
                (le_trans m (max m p) (max n (max m p)) (le_max_left m p) (le_max_right n (max m p))))
            (le_trans p (max m p) (max n (max m p)) (le_max_right m p) (le_max_right n (max m p))))
        (max_least n (max m p) (max (max n m) p)
            (le_trans n (max n m) (max (max n m) p) (le_max_left n m) (le_max_left (max n m) p))
            (max_least m p (max (max n m) p)
                (le_trans m (max n m) (max (max n m) p) (le_max_right n m) (le_max_left (max n m) p)) (le_max_right (max n m) p))).

Theorem min_of_le : forall n m : nat, le n m -> ((min n m) = n) :=
    fun n m h => le_antisym (min n m) n (min_le_left n m) (min_greatest n m n (le_n n) h).

Theorem max_of_le : forall n m : nat, le n m -> ((max n m) = m) :=
    fun n m h => le_antisym (max n m) m (max_least n m m h (le_n m)) (le_max_right n m).

Theorem min_idempotent : forall n : nat, ((min n n) = n) := fun n => min_of_le n n (le_n n).
Theorem max_idempotent : forall n : nat, ((max n n) = n) := fun n => max_of_le n n (le_n n).

Theorem min_absorb_max : forall n m : nat, ((min n (max n m)) = n) := fun n m => min_of_le n (max n m) (le_max_left n m).
Theorem max_absorb_min : forall n m : nat, ((max n (min n m)) = n) :=
    fun n m => eq_trans (max n (min n m)) (max (min n m) n) n (max_comm n (min n m)) (max_of_le (min n m) n (min_le_left n m)).

Theorem min_monotone : forall n m p q : nat, le n m -> le p q -> le (min n p) (min m q) :=
    fun n m p q h j => min_greatest m q (min n p)
        (le_trans (min n p) n m (min_le_left n p) h) (le_trans (min n p) p q (min_le_right n p) j).

Theorem max_monotone : forall n m p q : nat, le n m -> le p q -> le (max n p) (max m q) :=
    fun n m p q h j => max_least n p (max m q)
        (le_trans n m (max m q) h (le_max_left m q)) (le_trans p q (max m q) j (le_max_right m q)).

Theorem le_min_iff : forall n m p : nat, iff (le p (min n m)) (and (le p n) (le p m)) :=
    fun n m p => conj (le p (min n m) -> and (le p n) (le p m)) (and (le p n) (le p m) -> le p (min n m))
        (fun h => conj (le p n) (le p m) (le_trans p (min n m) n h (min_le_left n m)) (le_trans p (min n m) m h (min_le_right n m)))
        (fun h => min_greatest n m p (and_left (le p n) (le p m) h) (and_right (le p n) (le p m) h)).

Theorem max_le_iff : forall n m p : nat, iff (le (max n m) p) (and (le n p) (le m p)) :=
    fun n m p => conj (le (max n m) p -> and (le n p) (le m p)) (and (le n p) (le m p) -> le (max n m) p)
        (fun h => conj (le n p) (le m p) (le_trans n (max n m) p (le_max_left n m) h) (le_trans m (max n m) p (le_max_right n m) h))
        (fun h => max_least n m p (and_left (le n p) (le m p) h) (and_right (le n p) (le m p) h)).

Theorem min_eq_left_iff : forall n m : nat, iff ((min n m) = n) (le n m) :=
    fun n m => conj (((min n m) = n) -> le n m) (le n m -> ((min n m) = n))
        (fun e => eq_transport nat (fun k => le k m) (min n m) n e (min_le_right n m)) (min_of_le n m).

Theorem max_eq_right_iff : forall n m : nat, iff ((max n m) = m) (le n m) :=
    fun n m => conj (((max n m) = m) -> le n m) (le n m -> ((max n m) = m))
        (fun e => eq_transport nat (le n) (max n m) m e (le_max_left n m)) (max_of_le n m).

Theorem min_add_prefix : forall p n m : nat, ((min (add p n) (add p m)) = (add p (min n m))) :=
    fix go (p n m : nat) {struct p} : ((min (add p n) (add p m)) = (add p (min n m))) :=
    match p as k return ((min (add k n) (add k m)) = (add k (min n m))) with
    | O => eq_refl (min n m)
    | S q => f_equal S (min (add q n) (add q m)) (add q (min n m)) (go q n m)
    end.

Theorem max_add_prefix : forall p n m : nat, ((max (add p n) (add p m)) = (add p (max n m))) :=
    fix go (p n m : nat) {struct p} : ((max (add p n) (add p m)) = (add p (max n m))) :=
    match p as k return ((max (add k n) (add k m)) = (add k (max n m))) with
    | O => eq_refl (max n m)
    | S q => f_equal S (max (add q n) (add q m)) (add q (max n m)) (go q n m)
    end.

Theorem min_le_max : forall n m : nat, le (min n m) (max n m) :=
    fun n m => le_trans (min n m) n (max n m) (min_le_left n m) (le_max_left n m).

Theorem max_le_sum : forall n m : nat, le (max n m) (add n m) :=
    fun n m => max_least n m (add n m) (le_add_left n m) (le_add_right n m).

Theorem min_cases : forall n m : nat, or ((min n m) = n) ((min n m) = m) :=
    fun n m => or_map (le n m) (le m n) ((min n m) = n) ((min n m) = m)
        (min_of_le n m)
        (fun h => eq_trans (min n m) (min m n) m (min_comm n m) (min_of_le m n h))
        (le_total n m).

Theorem max_cases : forall n m : nat, or ((max n m) = n) ((max n m) = m) :=
    fun n m => or_map (le m n) (le n m) ((max n m) = n) ((max n m) = m)
        (fun h => eq_trans (max n m) (max m n) n (max_comm n m) (max_of_le m n h))
        (max_of_le n m)
        (le_total m n).

Theorem min_max_distribute : forall n m p : nat, ((min n (max m p)) = (max (min n m) (min n p))) :=
    fun n m p => le_antisym (min n (max m p)) (max (min n m) (min n p))
        (or_elim (le m p) (le p m) (le (min n (max m p)) (max (min n m) (min n p)))
            (fun h => le_trans (min n (max m p)) (min n p) (max (min n m) (min n p))
                (min_monotone n n (max m p) p (le_n n) (max_least m p p h (le_n p)))
                (le_max_right (min n m) (min n p)))
            (fun h => le_trans (min n (max m p)) (min n m) (max (min n m) (min n p))
                (min_monotone n n (max m p) m (le_n n) (max_least m p m (le_n m) h))
                (le_max_left (min n m) (min n p)))
            (le_total m p))
        (max_least (min n m) (min n p) (min n (max m p))
            (min_monotone n n m (max m p) (le_n n) (le_max_left m p))
            (min_monotone n n p (max m p) (le_n n) (le_max_right m p))).

Theorem max_min_distribute : forall n m p : nat, ((max n (min m p)) = (min (max n m) (max n p))) :=
    fun n m p => le_antisym (max n (min m p)) (min (max n m) (max n p))
        (min_greatest (max n m) (max n p) (max n (min m p))
            (max_monotone n n (min m p) m (le_n n) (min_le_left m p))
            (max_monotone n n (min m p) p (le_n n) (min_le_right m p)))
        (or_elim (le m p) (le p m) (le (min (max n m) (max n p)) (max n (min m p)))
            (fun h => le_trans (min (max n m) (max n p)) (max n m) (max n (min m p))
                (min_le_left (max n m) (max n p))
                (max_monotone n n m (min m p) (le_n n) (min_greatest m p m (le_n m) h)))
            (fun h => le_trans (min (max n m) (max n p)) (max n p) (max n (min m p))
                (min_le_right (max n m) (max n p))
                (max_monotone n n p (min m p) (le_n n) (min_greatest m p p h (le_n p))))
            (le_total m p)).

Theorem min_add_max : forall n m : nat, ((add (min n m) (max n m)) = (add n m)) :=
    fix go (n m : nat) {struct n} : ((add (min n m) (max n m)) = (add n m)) :=
    match n as k return ((add (min k m) (max k m)) = (add k m)) with
    | O => eq_refl m
    | S p => match m as k return ((add (min (S p) k) (max (S p) k)) = (add (S p) k)) with
        | O => f_equal S p (add p O) (eq_sym (add p O) p (add_n_O p))
        | S q => f_equal S (add (min p q) (S (max p q))) (add p (S q))
            (eq_trans (add (min p q) (S (max p q))) (S (add (min p q) (max p q))) (add p (S q))
                (add_n_Sm (min p q) (max p q))
                (eq_trans (S (add (min p q) (max p q))) (S (add p q)) (add p (S q))
                    (f_equal S (add (min p q) (max p q)) (add p q) (go p q))
                    (eq_sym (add p (S q)) (S (add p q)) (add_n_Sm p q))))
        end
    end.
