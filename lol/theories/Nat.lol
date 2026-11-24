(* Unary natural numbers, primitive recursion and elementary arithmetic. *)
Import lol.theories.Logic.
Inductive nat : Set := | O : nat | S : nat -> nat.
Definition one : nat := S O.
Definition two : nat := S (S O).
Definition pred (n : nat) : nat := match n with | O => O | S p => p end.
Fixpoint add (n m : nat) : nat := match n with | O => m | S p => S (add p m) end.
Infix "+" := add (at level 50, left associativity).
Fixpoint mul (n m : nat) : nat := match n with | O => O | S p => m + mul p m end.
Infix "*" := mul (at level 40, left associativity).
Fixpoint pow (n m : nat) : nat := match m with | O => one | S p => n * pow n p end.
Fixpoint sub (n m : nat) {struct m} : nat := match m with | O => n | S q => match n with | O => O | S p => sub p q end end.
Fixpoint min (n m : nat) : nat := match n with | O => O | S p => match m with | O => O | S q => S (min p q) end end.
Fixpoint max (n m : nat) : nat := match n with | O => m | S p => match m with | O => S p | S q => S (max p q) end end.
Fixpoint double (n : nat) : nat := match n with | O => O | S p => S (S (double p)) end.
Fixpoint half (n : nat) : nat := match n with | O => O | S p => match p with | O => O | S q => S (half q) end end.
Fixpoint nat_iter {A : Set} (f : A -> A) (x : A) (n : nat) : A := match n with | O => x | S p => f (nat_iter f x p) end.
Fixpoint nat_fold {A : Set} (z : A) (f : nat -> A -> A) (n : nat) : A := match n with | O => z | S p => f p (nat_fold z f p) end.
Definition nat_recursion (P : nat -> Set) (z : P O) (s : forall n : nat, P n -> P (S n)) : forall n : nat, P n := fix go (n : nat) : P n := match n with | O => z | S p => s p (go p) end.
Definition nat_induction (P : nat -> Prop) (z : P O) (s : forall n : nat, P n -> P (S n)) : forall n : nat, P n := fix go (n : nat) : P n := match n with | O => z | S p => s p (go p) end.
Inductive le (n : nat) : nat -> Prop := | le_n : le n n | le_S : forall m : nat, le n m -> le n (S m).
Definition lt (n m : nat) : Prop := le (S n) m.
Definition ge (n m : nat) : Prop := le m n.
Definition gt (n m : nat) : Prop := lt m n.
Theorem pred_O : ((pred O) = O) := eq_refl O.
Theorem pred_S : forall n : nat, ((pred (S n)) = n) := fun n => eq_refl n.
Theorem add_O : forall n : nat, ((O + n) = n) := fun n => eq_refl n.
Theorem add_S : forall n m : nat, ((S n + m) = (S (add n m))) := fun n m => eq_refl (S (add n m)).
Theorem mul_O : forall n : nat, ((O * n) = O) := fun n => eq_refl O.
Theorem mul_S : forall n m : nat, ((S n * m) = (add m (mul n m))) := fun n m => eq_refl (add m (mul n m)).
Theorem pow_O : forall n : nat, ((pow n O) = one) := fun n => eq_refl one.
Theorem pow_S : forall n m : nat, ((pow n (S m)) = (mul n (pow n m))) := fun n m => eq_refl (mul n (pow n m)).
Theorem sub_O_right : forall n : nat, ((sub n O) = n) := fun n => eq_refl n.
Theorem sub_SS : forall n m : nat, ((sub (S n) (S m)) = (sub n m)) := fun n m => eq_refl (sub n m).
Theorem min_O : forall n : nat, ((min O n) = O) := fun n => eq_refl O.
Theorem min_SS : forall n m : nat, ((min (S n) (S m)) = (S (min n m))) := fun n m => eq_refl (S (min n m)).
Theorem max_O : forall n : nat, ((max O n) = n) := fun n => eq_refl n.
Theorem max_SS : forall n m : nat, ((max (S n) (S m)) = (S (max n m))) := fun n m => eq_refl (S (max n m)).
Theorem double_O : ((double O) = O) := eq_refl O.
Theorem double_S : forall n : nat, ((double (S n)) = (S (S (double n)))) := fun n => eq_refl (S (S (double n))).
Theorem half_O : ((half O) = O) := eq_refl O.
Theorem half_one : ((half one) = O) := eq_refl O.
Theorem half_SS : forall n : nat, ((half (S (S n))) = (S (half n))) := fun n => eq_refl (S (half n)).
Theorem nat_iter_O : forall (A : Set) (f : A -> A) (x : A), ((nat_iter f x O) = x) := fun A f x => eq_refl x.
Theorem nat_iter_S : forall (A : Set) (f : A -> A) (x : A) (n : nat), ((nat_iter f x (S n)) = (f (nat_iter f x n))) := fun A f x n => eq_refl (f (nat_iter f x n)).
Theorem add_n_O : forall n : nat, ((add n O) = n) := fix go (n : nat) : ((add n O) = n) := match n with | O => eq_refl O | S p => f_equal S (add p O) p (go p) end.
Theorem add_n_Sm : forall n m : nat, ((add n (S m)) = (S (add n m))) := fix go (n m : nat) : ((add n (S m)) = (S (add n m))) := match n with | O => eq_refl (S m) | S p => f_equal S (add p (S m)) (S (add p m)) (go p m) end.
Theorem add_comm : forall n m : nat, ((add n m) = (add m n)) := fix go (n m : nat) : ((add n m) = (add m n)) := match n with | O => eq_sym (add m O) m (add_n_O m) | S p => eq_trans (S (add p m)) (S (add m p)) (add m (S p)) (f_equal S (add p m) (add m p) (go p m)) (eq_sym (add m (S p)) (S (add m p)) (add_n_Sm m p)) end.
Theorem add_assoc : forall n m p : nat, ((add (add n m) p) = (add n (add m p))) := fix go (n m p : nat) : ((add (add n m) p) = (add n (add m p))) := match n with | O => eq_refl (add m p) | S q => f_equal S (add (add q m) p) (add q (add m p)) (go q m p) end.
Theorem add_one_left : forall n : nat, ((add one n) = (S n)) := fun n => eq_refl (S n).
Theorem add_one_right : forall n : nat, ((add n one) = (S n)) := fun n => eq_trans (add n one) (S (add n O)) (S n) (add_n_Sm n O) (f_equal S (add n O) n (add_n_O n)).
Theorem mul_one_left : forall n : nat, ((mul one n) = n) := fun n => add_n_O n.
Theorem S_injective : forall n m : nat, ((S n) = (S m)) -> (n = m) := fun n m e => f_equal pred (S n) (S m) e.
Theorem O_not_S : forall n : nat, not ((O = (S n))) := fun n e => match e in eq _ k return (match k return Prop with | O => True | S p => False end) with | eq_refl _ => I end.
Theorem S_not_O : forall n : nat, not (((S n) = O)) := fun n e => O_not_S n (eq_sym (S n) O e).
Theorem le_refl : forall n : nat, le n n := fun n => le_n n.
Theorem le_step : forall n m : nat, le n m -> le n (S m) := fun n m h => le_S n m h.
Theorem le_zero : forall n : nat, le O n := fix go (n : nat) : le O n := match n with | O => le_n O | S p => le_S O p (go p) end.
Theorem le_trans : forall n m p : nat, le n m -> le m p -> le n p := fix go (n m p : nat) (h : le n m) (j : le m p) : le n p := match j with | le_n _ => h | le_S _ q r => le_S n q (go n m q h r) end.
Theorem lt_succ : forall n : nat, lt n (S n) := fun n => le_n (S n).
