(* Decisions carry proofs. No classical axiom or boolean reflection is assumed. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.

Inductive sumbool (P Q : Prop) : Set :=
    | yes : P -> sumbool P Q
    | no : Q -> sumbool P Q.

Definition Decidable (P : Prop) : Set := sumbool P (not P).

Definition decide_true : Decidable True := yes True (not True) I.
Definition decide_false : Decidable False := no False (not False) (fun h => h).

Definition decide_not (P : Prop) (d : Decidable P) : Decidable (not P) :=
    match d with
    | yes _ _ h => no (not P) (not (not P)) (fun n => n h)
    | no _ _ h => yes (not P) (not (not P)) h
    end.

Definition decide_and (P Q : Prop) (p : Decidable P) (q : Decidable Q) : Decidable (and P Q) :=
    match p with
    | yes _ _ h => match q with
        | yes _ _ j => yes (and P Q) (not (and P Q)) (conj P Q h j)
        | no _ _ j => no (and P Q) (not (and P Q)) (fun a => j (and_right P Q a))
        end
    | no _ _ h => no (and P Q) (not (and P Q)) (fun a => h (and_left P Q a))
    end.

Definition decide_or (P Q : Prop) (p : Decidable P) (q : Decidable Q) : Decidable (or P Q) :=
    match p with
    | yes _ _ h => yes (or P Q) (not (or P Q)) (or_introl P Q h)
    | no _ _ h => match q with
        | yes _ _ j => yes (or P Q) (not (or P Q)) (or_intror P Q j)
        | no _ _ j => no (or P Q) (not (or P Q)) (or_elim P Q False h j)
        end
    end.

Definition decide_imp (P Q : Prop) (p : Decidable P) (q : Decidable Q) : Decidable (P -> Q) :=
    match p with
    | yes _ _ h => match q with
        | yes _ _ j => yes (P -> Q) (not (P -> Q)) (fun _ => j)
        | no _ _ j => no (P -> Q) (not (P -> Q)) (fun f => j (f h))
        end
    | no _ _ h => yes (P -> Q) (not (P -> Q)) (fun x => False_rect Q (h x))
    end.

Definition decide_iff (P Q : Prop) (p : Decidable P) (q : Decidable Q) : Decidable (iff P Q) :=
    decide_and (P -> Q) (Q -> P) (decide_imp P Q p q) (decide_imp Q P q p).

Definition decide_transport (P Q : Prop) (e : iff P Q) (d : Decidable P) : Decidable Q :=
    match d with
    | yes _ _ h => yes Q (not Q) (and_left (P -> Q) (Q -> P) e h)
    | no _ _ h => no Q (not Q) (fun q => h (and_right (P -> Q) (Q -> P) e q))
    end.

Theorem decidable_excluded_middle : forall P : Prop, Decidable P -> or P (not P) :=
    fun P d => match d with
    | yes _ _ h => or_introl P (not P) h
    | no _ _ h => or_intror P (not P) h
    end.

Theorem decidable_double_neg : forall P : Prop, Decidable P -> not (not P) -> P :=
    fun P d n => match d with
    | yes _ _ h => h
    | no _ _ h => False_rect P (n h)
    end.

Definition nat_eq_dec : forall n m : nat, Decidable (n = m) :=
    fix go (n m : nat) {struct n} : Decidable (n = m) :=
    match n as k return Decidable (k = m) with
    | O => match m as k return Decidable (O = k) with
        | O => yes (O = O) (not (O = O)) (eq_refl O)
        | S q => no (O = (S q)) (not (O = (S q))) (O_not_S q)
        end
    | S p => match m as k return Decidable ((S p) = k) with
        | O => no ((S p) = O) (not ((S p) = O)) (S_not_O p)
        | S q => match go p q with
            | yes _ _ h => yes ((S p) = (S q)) (not ((S p) = (S q))) (f_equal S p q h)
            | no _ _ h => no ((S p) = (S q)) (not ((S p) = (S q))) (fun e => h (S_injective p q e))
            end
        end
    end.

Definition nat_order_dec : forall n m : nat, sumbool (le n m) (lt m n) :=
    fix go (n m : nat) {struct n} : sumbool (le n m) (lt m n) :=
    match n as k return sumbool (le k m) (lt m k) with
    | O => yes (le O m) (lt m O) (le_zero m)
    | S p => match m as k return sumbool (le (S p) k) (lt k (S p)) with
        | O => no (le (S p) O) (lt O (S p)) (le_succ_mono O p (le_zero p))
        | S q => match go p q with
            | yes _ _ h => yes (le (S p) (S q)) (lt (S q) (S p)) (le_succ_mono p q h)
            | no _ _ h => no (le (S p) (S q)) (lt (S q) (S p)) (le_succ_mono (S q) p h)
            end
        end
    end.

Definition nat_le_dec (n m : nat) : Decidable (le n m) :=
    match nat_order_dec n m with
    | yes _ _ h => yes (le n m) (not (le n m)) h
    | no _ _ h => no (le n m) (not (le n m)) (lt_not_le m n h)
    end.

Definition nat_lt_dec (n m : nat) : Decidable (lt n m) := nat_le_dec (S n) m.

Definition equality_decision (A : Set) : Type@{1} := forall x y : A, Decidable (x = y).

Definition nat_equality_decision : equality_decision nat := nat_eq_dec.

Definition option_eq_dec (A : Set) (d : equality_decision A) : equality_decision (option A) :=
    fun x y => match x as a return Decidable (a = y) with
    | None _ => match y as b return Decidable ((None A) = b) with
        | None _ => yes ((None A) = (None A)) (not ((None A) = (None A))) (eq_refl (None A))
        | Some _ b => no ((None A) = (Some A b)) (not ((None A) = (Some A b)))
            (fun e => match e in eq _ z return (match z return Prop with | None _ => True | Some _ _ => False end) with | eq_refl _ => I end)
        end
    | Some _ a => match y as b return Decidable ((Some A a) = b) with
        | None _ => no ((Some A a) = (None A)) (not ((Some A a) = (None A)))
            (fun e => match e in eq _ z return (match z return Prop with | None _ => False | Some _ _ => True end) with | eq_refl _ => I end)
        | Some _ b => match d a b with
            | yes _ _ h => yes ((Some A a) = (Some A b)) (not ((Some A a) = (Some A b))) (f_equal (Some A) a b h)
            | no _ _ h => no ((Some A a) = (Some A b)) (not ((Some A a) = (Some A b)))
                (fun e => h (f_equal (option_default A a) (Some A a) (Some A b) e))
            end
        end
    end.
