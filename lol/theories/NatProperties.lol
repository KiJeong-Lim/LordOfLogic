(* Arithmetic identities and cancellation used by division and number theory. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.

Theorem add_cancel_left : forall p n m : nat, ((add p n) = (add p m)) -> (n = m) :=
    fix go (p n m : nat) {struct p} : ((add p n) = (add p m)) -> (n = m) :=
    match p as k return ((add k n) = (add k m)) -> (n = m) with
    | O => fun e => e
    | S q => fun e => go q n m (S_injective (add q n) (add q m) e)
    end.

Theorem add_cancel_right : forall p n m : nat, ((add n p) = (add m p)) -> (n = m) :=
    fun p n m e => add_cancel_left p n m
        (eq_trans (add p n) (add n p) (add p m) (add_comm p n)
            (eq_trans (add n p) (add m p) (add p m) e (add_comm m p))).

Theorem add_left_comm : forall n m p : nat, ((add n (add m p)) = (add m (add n p))) :=
    fun n m p => eq_trans (add n (add m p)) (add (add n m) p) (add m (add n p))
        (eq_sym (add (add n m) p) (add n (add m p)) (add_assoc n m p))
        (eq_trans (add (add n m) p) (add (add m n) p) (add m (add n p))
            (f_equal (fun k : nat => add k p) (add n m) (add m n) (add_comm n m)) (add_assoc m n p)).

Theorem add_shuffle : forall a b c d : nat, ((add (add a b) (add c d)) = (add (add a c) (add b d))) :=
    fun a b c d => eq_trans (add (add a b) (add c d)) (add a (add b (add c d))) (add (add a c) (add b d))
        (add_assoc a b (add c d))
        (eq_trans (add a (add b (add c d))) (add a (add c (add b d))) (add (add a c) (add b d))
            (f_equal (add a) (add b (add c d)) (add c (add b d)) (add_left_comm b c d))
            (eq_sym (add (add a c) (add b d)) (add a (add c (add b d))) (add_assoc a c (add b d)))).

Theorem add_eq_zero_left : forall n m : nat, ((add n m) = O) -> (n = O) :=
    fun n m e => le_zero_right n (eq_transport nat (le n) (add n m) O e (le_add_left n m)).

Theorem add_eq_zero_right : forall n m : nat, ((add n m) = O) -> (m = O) :=
    fun n m e => le_zero_right m (eq_transport nat (le m) (add n m) O e (le_add_right n m)).

Theorem mul_n_O : forall n : nat, ((mul n O) = O) :=
    fix go (n : nat) {struct n} : ((mul n O) = O) :=
    match n as k return ((mul k O) = O) with
    | O => eq_refl O
    | S p => go p
    end.

Theorem mul_n_Sm : forall n m : nat, ((mul n (S m)) = (add n (mul n m))) :=
    fix go (n m : nat) {struct n} : ((mul n (S m)) = (add n (mul n m))) :=
    match n as k return ((mul k (S m)) = (add k (mul k m))) with
    | O => eq_refl O
    | S p => f_equal S (add m (mul p (S m))) (add p (add m (mul p m)))
        (eq_trans (add m (mul p (S m))) (add m (add p (mul p m))) (add p (add m (mul p m)))
            (f_equal (add m) (mul p (S m)) (add p (mul p m)) (go p m))
            (add_left_comm m p (mul p m)))
    end.

Theorem mul_comm : forall n m : nat, ((mul n m) = (mul m n)) :=
    fix go (n m : nat) {struct n} : ((mul n m) = (mul m n)) :=
    match n as k return ((mul k m) = (mul m k)) with
    | O => eq_sym (mul m O) O (mul_n_O m)
    | S p => eq_trans (add m (mul p m)) (add m (mul m p)) (mul m (S p))
        (f_equal (add m) (mul p m) (mul m p) (go p m))
        (eq_sym (mul m (S p)) (add m (mul m p)) (mul_n_Sm m p))
    end.

Theorem mul_one_right : forall n : nat, ((mul n one) = n) :=
    fun n => eq_trans (mul n one) (mul one n) n (mul_comm n one) (mul_one_left n).

Theorem mul_add_left : forall n m p : nat, ((mul (add n m) p) = (add (mul n p) (mul m p))) :=
    fix go (n m p : nat) {struct n} : ((mul (add n m) p) = (add (mul n p) (mul m p))) :=
    match n as k return ((mul (add k m) p) = (add (mul k p) (mul m p))) with
    | O => eq_refl (mul m p)
    | S q => eq_trans (add p (mul (add q m) p)) (add p (add (mul q p) (mul m p))) (add (add p (mul q p)) (mul m p))
        (f_equal (add p) (mul (add q m) p) (add (mul q p) (mul m p)) (go q m p))
        (eq_sym (add (add p (mul q p)) (mul m p)) (add p (add (mul q p) (mul m p))) (add_assoc p (mul q p) (mul m p)))
    end.

Theorem mul_add_right : forall n m p : nat, ((mul n (add m p)) = (add (mul n m) (mul n p))) :=
    fix go (n m p : nat) {struct n} : ((mul n (add m p)) = (add (mul n m) (mul n p))) :=
    match n as k return ((mul k (add m p)) = (add (mul k m) (mul k p))) with
    | O => eq_refl O
    | S q => eq_trans (add (add m p) (mul q (add m p))) (add (add m p) (add (mul q m) (mul q p))) (add (add m (mul q m)) (add p (mul q p)))
        (f_equal (add (add m p)) (mul q (add m p)) (add (mul q m) (mul q p)) (go q m p))
        (add_shuffle m p (mul q m) (mul q p))
    end.

Theorem mul_assoc : forall n m p : nat, ((mul (mul n m) p) = (mul n (mul m p))) :=
    fix go (n m p : nat) {struct n} : ((mul (mul n m) p) = (mul n (mul m p))) :=
    match n as k return ((mul (mul k m) p) = (mul k (mul m p))) with
    | O => eq_refl O
    | S q => eq_trans (mul (add m (mul q m)) p) (add (mul m p) (mul (mul q m) p)) (add (mul m p) (mul q (mul m p)))
        (mul_add_left m (mul q m) p)
        (f_equal (add (mul m p)) (mul (mul q m) p) (mul q (mul m p)) (go q m p))
    end.

Theorem mul_left_comm : forall n m p : nat, ((mul n (mul m p)) = (mul m (mul n p))) :=
    fun n m p => eq_trans (mul n (mul m p)) (mul (mul n m) p) (mul m (mul n p))
        (eq_sym (mul (mul n m) p) (mul n (mul m p)) (mul_assoc n m p))
        (eq_trans (mul (mul n m) p) (mul (mul m n) p) (mul m (mul n p))
            (f_equal (fun k : nat => mul k p) (mul n m) (mul m n) (mul_comm n m)) (mul_assoc m n p)).

Theorem mul_le_mono_left : forall n m p : nat, le n m -> le (mul p n) (mul p m) :=
    fun n m => fix go (p : nat) {struct p} : le n m -> le (mul p n) (mul p m) :=
    match p as k return le n m -> le (mul k n) (mul k m) with
    | O => fun h => le_n O
    | S q => fun h => add_le_mono n m (mul q n) (mul q m) h (go q h)
    end.

Theorem mul_le_mono_right : forall n m p : nat, le n m -> le (mul n p) (mul m p) :=
    fun n m p h => eq_transport nat (le (mul n p)) (mul p m) (mul m p) (mul_comm p m)
        (eq_transport nat (fun k => le k (mul p m)) (mul p n) (mul n p) (mul_comm p n) (mul_le_mono_left n m p h)).

Theorem mul_le_mono : forall n m p q : nat, le n m -> le p q -> le (mul n p) (mul m q) :=
    fun n m p q h j => le_trans (mul n p) (mul m p) (mul m q) (mul_le_mono_right n m p h) (mul_le_mono_left p q m j).

Theorem mul_eq_zero : forall n m : nat, ((mul n m) = O) -> or (n = O) (m = O) :=
    fun n m => match n as k return ((mul k m) = O) -> or (k = O) (m = O) with
    | O => fun e => or_introl (O = O) (m = O) (eq_refl O)
    | S p => fun e => or_intror ((S p) = O) (m = O) (add_eq_zero_left m (mul p m) e)
    end.

Theorem mul_cancel_right : forall p n m : nat, not (p = O) -> ((mul n p) = (mul m p)) -> (n = m) :=
    fun p => match p as k return forall n m : nat, not (k = O) -> ((mul n k) = (mul m k)) -> (n = m) with
    | O => fun n m h e => False_rect (n = m) (h (eq_refl O))
    | S d => fun n m h => (fix go (a b : nat) {struct a} : ((mul a (S d)) = (mul b (S d))) -> (a = b) :=
        match a as k return ((mul k (S d)) = (mul b (S d))) -> (k = b) with
        | O => match b as k return ((mul O (S d)) = (mul k (S d))) -> (O = k) with
            | O => fun e => eq_refl O
            | S q => fun e => False_rect (O = (S q)) (O_not_S (add d (mul q (S d))) e)
            end
        | S r => match b as k return ((mul (S r) (S d)) = (mul k (S d))) -> ((S r) = k) with
            | O => fun e => False_rect ((S r) = O) (S_not_O (add d (mul r (S d))) e)
            | S q => fun e => f_equal S r q (go r q (add_cancel_left (S d) (mul r (S d)) (mul q (S d)) e))
            end
        end) n m
    end.

Theorem mul_cancel_left : forall p n m : nat, not (p = O) -> ((mul p n) = (mul p m)) -> (n = m) :=
    fun p n m h e => mul_cancel_right p n m h
        (eq_trans (mul n p) (mul p n) (mul m p) (mul_comm n p)
            (eq_trans (mul p n) (mul p m) (mul m p) e (mul_comm p m))).

Theorem pow_one : forall n : nat, ((pow n one) = n) := fun n => mul_one_right n.

Theorem one_pow : forall n : nat, ((pow one n) = one) :=
    fix go (n : nat) {struct n} : ((pow one n) = one) :=
    match n as k return ((pow one k) = one) with
    | O => eq_refl one
    | S p => eq_trans (mul one (pow one p)) (pow one p) one (mul_one_left (pow one p)) (go p)
    end.

Theorem zero_pow_succ : forall n : nat, ((pow O (S n)) = O) := fun n => eq_refl O.

Theorem pow_add : forall n m p : nat, ((pow n (add m p)) = (mul (pow n m) (pow n p))) :=
    fun n => fix go (m p : nat) {struct m} : ((pow n (add m p)) = (mul (pow n m) (pow n p))) :=
    match m as k return ((pow n (add k p)) = (mul (pow n k) (pow n p))) with
    | O => eq_sym (mul one (pow n p)) (pow n p) (mul_one_left (pow n p))
    | S q => eq_trans (mul n (pow n (add q p))) (mul n (mul (pow n q) (pow n p))) (mul (mul n (pow n q)) (pow n p))
        (f_equal (mul n) (pow n (add q p)) (mul (pow n q) (pow n p)) (go q p))
        (eq_sym (mul (mul n (pow n q)) (pow n p)) (mul n (mul (pow n q) (pow n p))) (mul_assoc n (pow n q) (pow n p)))
    end.

Theorem pow_mul : forall n m p : nat, ((pow n (mul m p)) = (pow (pow n m) p)) :=
    fun n m => fix go (p : nat) {struct p} : ((pow n (mul m p)) = (pow (pow n m) p)) :=
    match p as k return ((pow n (mul m k)) = (pow (pow n m) k)) with
    | O => f_equal (pow n) (mul m O) O (mul_n_O m)
    | S q => eq_trans (pow n (mul m (S q))) (pow n (add m (mul m q))) (mul (pow n m) (pow (pow n m) q))
        (f_equal (pow n) (mul m (S q)) (add m (mul m q)) (mul_n_Sm m q))
        (eq_trans (pow n (add m (mul m q))) (mul (pow n m) (pow n (mul m q))) (mul (pow n m) (pow (pow n m) q))
            (pow_add n m (mul m q))
            (f_equal (mul (pow n m)) (pow n (mul m q)) (pow (pow n m) q) (go q)))
    end.

Theorem sub_O_left : forall n : nat, ((sub O n) = O) :=
    fun n => match n as k return ((sub O k) = O) with | O => eq_refl O | S p => eq_refl O end.

Theorem sub_self : forall n : nat, ((sub n n) = O) :=
    fix go (n : nat) {struct n} : ((sub n n) = O) :=
    match n as k return ((sub k k) = O) with | O => eq_refl O | S p => go p end.

Theorem sub_add_prefix : forall p n m : nat, ((sub (add p n) (add p m)) = (sub n m)) :=
    fix go (p n m : nat) {struct p} : ((sub (add p n) (add p m)) = (sub n m)) :=
    match p as k return ((sub (add k n) (add k m)) = (sub n m)) with
    | O => eq_refl (sub n m)
    | S q => go q n m
    end.

Theorem sub_add_left : forall n m : nat, ((sub (add n m) n) = m) :=
    fix go (n m : nat) {struct n} : ((sub (add n m) n) = m) :=
    match n as k return ((sub (add k m) k) = m) with | O => eq_refl m | S p => go p m end.

Theorem sub_add_right : forall n m : nat, ((sub (add n m) m) = n) :=
    fun n m => eq_trans (sub (add n m) m) (sub (add m n) m) n
        (f_equal (fun k : nat => sub k m) (add n m) (add m n) (add_comm n m)) (sub_add_left m n).

Theorem sub_one : forall n : nat, ((sub n one) = (pred n)) :=
    fun n => match n as k return ((sub k one) = (pred k)) with | O => eq_refl O | S p => eq_refl p end.

Theorem sub_le_self : forall n m : nat, le (sub n m) n :=
    fix go (n m : nat) {struct n} : le (sub n m) n :=
    match n as k return le (sub k m) k with
    | O => eq_transport nat (fun k => le k O) O (sub O m) (eq_sym (sub O m) O (sub_O_left m)) (le_n O)
    | S p => match m as k return le (sub (S p) k) (S p) with
        | O => le_n (S p)
        | S q => le_S (sub p q) p (go p q)
        end
    end.

Theorem sub_succ_le : forall n m : nat, le (sub n (S m)) (sub n m) :=
    fix go (n m : nat) {struct n} : le (sub n (S m)) (sub n m) :=
    match n as k return le (sub k (S m)) (sub k m) with
    | O => eq_transport nat (le O) O (sub O m) (eq_sym (sub O m) O (sub_O_left m)) (le_n O)
    | S p => match m as k return le (sub (S p) (S k)) (sub (S p) k) with
        | O => le_S p p (le_n p)
        | S q => go p q
        end
    end.

Theorem sub_succ_strict : forall n m : nat, lt O n -> lt (sub n (S m)) n :=
    fun n m => match n as k return lt O k -> lt (sub k (S m)) k with
    | O => fun h => False_rect (lt (sub O (S m)) O) (lt_zero_false O h)
    | S p => fun h => le_succ_mono (sub p m) p (sub_le_self p m)
    end.

Theorem le_sub_zero : forall n m : nat, le n m -> ((sub n m) = O) :=
    fix go (n m : nat) {struct n} : le n m -> ((sub n m) = O) :=
    match n as k return le k m -> ((sub k m) = O) with
    | O => fun h => sub_O_left m
    | S p => match m as k return le (S p) k -> ((sub (S p) k) = O) with
        | O => fun h => False_rect ((S p) = O) (lt_zero_false p h)
        | S q => fun h => go p q (le_succ_inv p q h)
        end
    end.

Theorem sub_zero_le : forall n m : nat, ((sub n m) = O) -> le n m :=
    fix go (n m : nat) {struct n} : ((sub n m) = O) -> le n m :=
    match n as k return ((sub k m) = O) -> le k m with
    | O => fun e => le_zero m
    | S p => match m as k return ((sub (S p) k) = O) -> le (S p) k with
        | O => fun e => False_rect (le (S p) O) (S_not_O p e)
        | S q => fun e => le_succ_mono p q (go p q e)
        end
    end.

Theorem sub_zero_iff : forall n m : nat, iff ((sub n m) = O) (le n m) :=
    fun n m => conj (((sub n m) = O) -> le n m) (le n m -> ((sub n m) = O)) (sub_zero_le n m) (le_sub_zero n m).

Theorem add_sub_cancel : forall n m : nat, le m n -> ((add m (sub n m)) = n) :=
    fix go (n m : nat) {struct n} : le m n -> ((add m (sub n m)) = n) :=
    match n as k return le m k -> ((add m (sub k m)) = k) with
    | O => fun h => eq_transport nat (fun k => (add k (sub O k)) = O) O m (eq_sym m O (le_zero_right m h)) (eq_refl O)
    | S p => match m as k return le k (S p) -> ((add k (sub (S p) k)) = (S p)) with
        | O => fun h => eq_refl (S p)
        | S q => fun h => f_equal S (add q (sub p q)) p (go p q (le_succ_inv q p h))
        end
    end.

Theorem sub_add_cancel : forall n m : nat, le m n -> ((add (sub n m) m) = n) :=
    fun n m h => eq_trans (add (sub n m) m) (add m (sub n m)) n (add_comm (sub n m) m) (add_sub_cancel n m h).

Theorem sub_sub : forall n m p : nat, ((sub (sub n m) p) = (sub n (add m p))) :=
    fix go (n m p : nat) {struct m} : ((sub (sub n m) p) = (sub n (add m p))) :=
    match m as k return ((sub (sub n k) p) = (sub n (add k p))) with
    | O => eq_refl (sub n p)
    | S q => match n as k return ((sub (sub k (S q)) p) = (sub k (add (S q) p))) with
        | O => sub_O_left p
        | S r => go r q p
        end
    end.

Theorem sub_le_mono_right : forall n m p : nat, le n m -> le (sub n p) (sub m p) :=
    fix go (n m p : nat) {struct p} : le n m -> le (sub n p) (sub m p) :=
    match p as k return le n m -> le (sub n k) (sub m k) with
    | O => fun h => h
    | S q => match n as k return le k m -> le (sub k (S q)) (sub m (S q)) with
        | O => fun h => le_zero (sub m (S q))
        | S a => match m as k return le (S a) k -> le (sub (S a) (S q)) (sub k (S q)) with
            | O => fun h => False_rect (le (sub a q) O) (lt_zero_false a h)
            | S b => fun h => go a b q (le_succ_inv a b h)
            end
        end
    end.

Theorem sub_le_mono_left : forall n m p : nat, le n m -> le (sub p m) (sub p n) :=
    fix go (n m p : nat) (h : le n m) {struct h} : le (sub p m) (sub p n) :=
    match h in le _ k return le (sub p k) (sub p n) with
    | le_n _ => le_n (sub p n)
    | le_S _ k r => le_trans (sub p (S k)) (sub p k) (sub p n) (sub_succ_le p k) (go n k p r)
    end.

Theorem add_sub_assoc : forall n m p : nat, le p m -> ((add n (sub m p)) = (sub (add n m) p)) :=
    fun n m p h => eq_sym (sub (add n m) p) (add n (sub m p))
        (eq_trans (sub (add n m) p) (sub (add n (add p (sub m p))) p) (add n (sub m p))
            (f_equal (fun k : nat => sub (add n k) p) m (add p (sub m p))
                (eq_sym (add p (sub m p)) m (add_sub_cancel m p h)))
            (eq_trans (sub (add n (add p (sub m p))) p) (sub (add p (add n (sub m p))) p) (add n (sub m p))
                (f_equal (fun k : nat => sub k p) (add n (add p (sub m p))) (add p (add n (sub m p)))
                    (add_left_comm n p (sub m p)))
                (sub_add_left p (add n (sub m p))))).

Theorem double_add : forall n : nat, ((double n) = (add n n)) :=
    fix go (n : nat) {struct n} : ((double n) = (add n n)) :=
    match n as k return ((double k) = (add k k)) with
    | O => eq_refl O
    | S p => f_equal S (S (double p)) (add p (S p))
        (eq_trans (S (double p)) (S (add p p)) (add p (S p))
            (f_equal S (double p) (add p p) (go p))
            (eq_sym (add p (S p)) (S (add p p)) (add_n_Sm p p)))
    end.

Theorem half_double : forall n : nat, ((half (double n)) = n) :=
    fix go (n : nat) {struct n} : ((half (double n)) = n) :=
    match n as k return ((half (double k)) = k) with
    | O => eq_refl O
    | S p => f_equal S (half (double p)) p (go p)
    end.

Theorem mul_sub_left : forall n m d : nat, ((mul (sub n m) d) = (sub (mul n d) (mul m d))) :=
    fix go (n m d : nat) {struct n} : ((mul (sub n m) d) = (sub (mul n d) (mul m d))) :=
    match n as k return ((mul (sub k m) d) = (sub (mul k d) (mul m d))) with
    | O => eq_trans (mul (sub O m) d) O (sub O (mul m d))
        (f_equal (fun k : nat => mul k d) (sub O m) O (sub_O_left m))
        (eq_sym (sub O (mul m d)) O (sub_O_left (mul m d)))
    | S p => match m as k return ((mul (sub (S p) k) d) = (sub (mul (S p) d) (mul k d))) with
        | O => eq_refl (mul (S p) d)
        | S q => eq_trans (mul (sub p q) d) (sub (mul p d) (mul q d)) (sub (add d (mul p d)) (add d (mul q d)))
            (go p q d)
            (eq_sym (sub (add d (mul p d)) (add d (mul q d))) (sub (mul p d) (mul q d)) (sub_add_prefix d (mul p d) (mul q d)))
        end
    end.
