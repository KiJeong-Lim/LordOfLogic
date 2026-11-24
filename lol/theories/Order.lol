(* Natural order facts used by the ALPHA2 arithmetic and sorting libraries. *)
Import lol.theories.Logic.
Import lol.theories.Nat.

Theorem le_pred_self : forall n : nat, le (pred n) n :=
    fun n => match n as k return le (pred k) k with
    | O => le_n O
    | S p => le_S p p (le_n p)
    end.

Theorem le_succ_mono : forall n m : nat, le n m -> le (S n) (S m) :=
    fix go (n m : nat) (h : le n m) {struct h} : le (S n) (S m) :=
    match h in le _ k return le (S n) (S k) with
    | le_n _ => le_n (S n)
    | le_S _ k p => le_S (S n) (S k) (go n k p)
    end.

Theorem le_pred_mono : forall n m : nat, le n m -> le (pred n) (pred m) :=
    fix go (n m : nat) (h : le n m) {struct h} : le (pred n) (pred m) :=
    match h in le _ k return le (pred n) (pred k) with
    | le_n _ => le_n (pred n)
    | le_S _ k p => le_trans (pred n) (pred k) k (go n k p) (le_pred_self k)
    end.

Theorem le_succ_inv : forall n m : nat, le (S n) (S m) -> le n m :=
    fun n m h => le_pred_mono (S n) (S m) h.

Theorem le_succ_left : forall n m : nat, le (S n) m -> le n m :=
    fun n m h => le_trans n (S n) m (le_S n n (le_n n)) h.

Theorem lt_le : forall n m : nat, lt n m -> le n m :=
    fun n m h => le_succ_left n m h.

Theorem lt_trans : forall n m p : nat, lt n m -> lt m p -> lt n p :=
    fun n m p h j => le_trans (S n) m p h (lt_le m p j).

Theorem le_lt_trans : forall n m p : nat, le n m -> lt m p -> lt n p :=
    fun n m p h j => le_trans (S n) (S m) p (le_succ_mono n m h) j.

Theorem lt_le_trans : forall n m p : nat, lt n m -> le m p -> lt n p :=
    fun n m p h j => le_trans (S n) m p h j.

Theorem le_zero_right : forall n : nat, le n O -> (n = O) :=
    fun n h => (match h in le _ k return (k = O) -> (n = O) with
    | le_n _ => fun e => e
    | le_S _ k p => fun e => False_rect (n = O) (S_not_O k e)
    end) (eq_refl O).

Theorem lt_zero_false : forall n : nat, not (lt n O) :=
    fun n h => S_not_O n (le_zero_right (S n) h).

Theorem lt_irrefl : forall n : nat, not (lt n n) :=
    fix go (n : nat) {struct n} : not (lt n n) :=
    match n as k return not (lt k k) with
    | O => lt_zero_false O
    | S p => fun h => go p (le_succ_inv (S p) p h)
    end.

Theorem lt_asym : forall n m : nat, lt n m -> not (lt m n) :=
    fun n m h j => lt_irrefl n (lt_trans n m n h j).

Theorem le_antisym : forall n m : nat, le n m -> le m n -> (n = m) :=
    fix go (n m : nat) {struct n} : le n m -> le m n -> (n = m) :=
    match n as k return le k m -> le m k -> (k = m) with
    | O => fun h j => eq_sym m O (le_zero_right m j)
    | S p => match m as k return le (S p) k -> le k (S p) -> ((S p) = k) with
        | O => fun h j => False_rect ((S p) = O) (lt_zero_false p h)
        | S q => fun h j => f_equal S p q (go p q (le_succ_inv p q h) (le_succ_inv q p j))
        end
    end.

Theorem le_not_lt : forall n m : nat, le n m -> not (lt m n) :=
    fun n m h j => lt_irrefl m (lt_le_trans m n m j h).

Theorem lt_not_le : forall n m : nat, lt n m -> not (le m n) :=
    fun n m h j => lt_irrefl n (lt_le_trans n m n h j).

Theorem le_add_left : forall n m : nat, le n (add n m) :=
    fix go (n m : nat) {struct n} : le n (add n m) :=
    match n as k return le k (add k m) with
    | O => le_zero m
    | S p => le_succ_mono p (add p m) (go p m)
    end.

Theorem le_add_right : forall n m : nat, le m (add n m) :=
    fix go (n m : nat) {struct n} : le m (add n m) :=
    match n as k return le m (add k m) with
    | O => le_n m
    | S p => le_S m (add p m) (go p m)
    end.

Theorem add_le_mono_left : forall n m p : nat, le n m -> le (add p n) (add p m) :=
    fun n m => fix go (p : nat) {struct p} : le n m -> le (add p n) (add p m) :=
    match p as k return le n m -> le (add k n) (add k m) with
    | O => fun h => h
    | S q => fun h => le_succ_mono (add q n) (add q m) (go q h)
    end.

Theorem add_le_mono_right : forall n m p : nat, le n m -> le (add n p) (add m p) :=
    fix go (n m p : nat) (h : le n m) {struct h} : le (add n p) (add m p) :=
    match h in le _ k return le (add n p) (add k p) with
    | le_n _ => le_n (add n p)
    | le_S _ k r => le_S (add n p) (add k p) (go n k p r)
    end.

Theorem add_le_mono : forall n m p q : nat, le n m -> le p q -> le (add n p) (add m q) :=
    fun n m p q h j => le_trans (add n p) (add m p) (add m q) (add_le_mono_right n m p h) (add_le_mono_left p q m j).

Theorem add_le_cancel_left : forall p n m : nat, le (add p n) (add p m) -> le n m :=
    fix go (p n m : nat) {struct p} : le (add p n) (add p m) -> le n m :=
    match p as k return le (add k n) (add k m) -> le n m with
    | O => fun h => h
    | S q => fun h => go q n m (le_succ_inv (add q n) (add q m) h)
    end.

Theorem add_le_cancel_right : forall p n m : nat, le (add n p) (add m p) -> le n m :=
    fun p n m h => add_le_cancel_left p n m
        (eq_transport nat (fun k => le (add p n) k) (add m p) (add p m) (add_comm m p)
            (eq_transport nat (fun k => le k (add m p)) (add n p) (add p n) (add_comm n p) h)).

Theorem le_total : forall n m : nat, or (le n m) (le m n) :=
    fix go (n m : nat) {struct n} : or (le n m) (le m n) :=
    match n as k return or (le k m) (le m k) with
    | O => or_introl (le O m) (le m O) (le_zero m)
    | S p => match m as k return or (le (S p) k) (le k (S p)) with
        | O => or_intror (le (S p) O) (le O (S p)) (le_zero (S p))
        | S q => or_map (le p q) (le q p) (le (S p) (S q)) (le (S q) (S p))
            (le_succ_mono p q) (le_succ_mono q p) (go p q)
        end
    end.

Theorem le_or_gt : forall n m : nat, or (le n m) (lt m n) :=
    fix go (n m : nat) {struct n} : or (le n m) (lt m n) :=
    match n as k return or (le k m) (lt m k) with
    | O => or_introl (le O m) (lt m O) (le_zero m)
    | S p => match m as k return or (le (S p) k) (lt k (S p)) with
        | O => or_intror (le (S p) O) (lt O (S p)) (le_succ_mono O p (le_zero p))
        | S q => or_map (le p q) (lt q p) (le (S p) (S q)) (lt (S q) (S p))
            (le_succ_mono p q) (le_succ_mono (S q) p) (go p q)
        end
    end.

Theorem not_le_lt : forall n m : nat, not (le n m) -> lt m n :=
    fun n m h => or_elim (le n m) (lt m n) (lt m n)
        (fun p => False_rect (lt m n) (h p)) (fun p => p) (le_or_gt n m).

Theorem not_lt_le : forall n m : nat, not (lt n m) -> le m n :=
    fun n m h => or_elim (le m n) (lt n m) (le m n)
        (fun p => p) (fun p => False_rect (le m n) (h p)) (le_or_gt m n).

Theorem le_succ_iff : forall n m : nat, iff (le (S n) (S m)) (le n m) :=
    fun n m => conj (le (S n) (S m) -> le n m) (le n m -> le (S n) (S m))
        (le_succ_inv n m) (le_succ_mono n m).

Theorem lt_succ_iff : forall n m : nat, iff (lt n (S m)) (le n m) :=
    fun n m => le_succ_iff n m.

Theorem le_zero_iff : forall n : nat, iff (le n O) (n = O) :=
    fun n => conj (le n O -> (n = O)) ((n = O) -> le n O)
        (le_zero_right n) (fun e => eq_transport nat (fun k => le k O) O n (eq_sym n O e) (le_n O)).

Theorem lt_not_eq : forall n m : nat, lt n m -> not (n = m) :=
    fun n m h e => lt_irrefl n (eq_transport nat (fun k => lt n k) m n (eq_sym n m e) h).

Theorem min_le_left : forall n m : nat, le (min n m) n :=
    fix go (n m : nat) {struct n} : le (min n m) n :=
    match n as k return le (min k m) k with
    | O => le_n O
    | S p => match m as k return le (min (S p) k) (S p) with
        | O => le_zero (S p)
        | S q => le_succ_mono (min p q) p (go p q)
        end
    end.

Theorem min_le_right : forall n m : nat, le (min n m) m :=
    fix go (n m : nat) {struct n} : le (min n m) m :=
    match n as k return le (min k m) m with
    | O => le_zero m
    | S p => match m as k return le (min (S p) k) k with
        | O => le_n O
        | S q => le_succ_mono (min p q) q (go p q)
        end
    end.

Theorem le_max_left : forall n m : nat, le n (max n m) :=
    fix go (n m : nat) {struct n} : le n (max n m) :=
    match n as k return le k (max k m) with
    | O => le_zero m
    | S p => match m as k return le (S p) (max (S p) k) with
        | O => le_n (S p)
        | S q => le_succ_mono p (max p q) (go p q)
        end
    end.

Theorem le_max_right : forall n m : nat, le m (max n m) :=
    fix go (n m : nat) {struct n} : le m (max n m) :=
    match n as k return le m (max k m) with
    | O => le_n m
    | S p => match m as k return le k (max (S p) k) with
        | O => le_zero (S p)
        | S q => le_succ_mono q (max p q) (go p q)
        end
    end.
