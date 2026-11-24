(* Transparent accessibility for strict natural order and measure recursion. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Order.
Import lol.theories.Wf.

Definition lt_acc_bounded : forall bound n : nat, lt n bound -> Acc nat lt n :=
    fix go (bound : nat) {struct bound} : forall n : nat, lt n bound -> Acc nat lt n :=
    match bound as k return forall n : nat, lt n k -> Acc nat lt n with
    | O => fun n h => False_rect (Acc nat lt n) (lt_zero_false n h)
    | S p => fun n h => Acc_intro nat lt n
        (fun y r => go p y (le_trans (S y) n p r (le_succ_inv n p h)))
    end.

Definition lt_well_founded : well_founded nat lt :=
    fun n => lt_acc_bounded (S n) n (le_n (S n)).

Definition nat_strong_induction (P : nat -> Prop)
    (step : forall n : nat, (forall m : nat, lt m n -> P m) -> P n) : forall n : nat, P n :=
    wf_induction lt lt_well_founded P step.

Definition nat_strong_recursion (P : nat -> Set)
    (step : forall n : nat, (forall m : nat, lt m n -> P m) -> P n) : forall n : nat, P n :=
    wf_recursion lt lt_well_founded P step.

Definition Acc_inverse_image : forall (A B : Set) (R : relation B) (f : A -> B) (b : B),
    Acc B R b -> forall a : A, ((f a) = b) -> Acc A (inverse_image R f) a :=
    fun A B R f => fix go (b : B) (acc : Acc B R b) {struct acc} :
        forall a : A, ((f a) = b) -> Acc A (inverse_image R f) a :=
    match acc return forall a : A, ((f a) = b) -> Acc A (inverse_image R f) a with
    | Acc_intro _ _ _ smaller => fun a e => Acc_intro A (inverse_image R f) a
        (fun x r => go (f x)
            (smaller (f x) (eq_transport B (R (f x)) (f a) b e r)) x (eq_refl (f x)))
    end.

Definition inverse_image_well_founded : forall (A B : Set) (R : relation B) (f : A -> B),
    well_founded B R -> well_founded A (inverse_image R f) :=
    fun A B R f wf a => Acc_inverse_image A B R f (f a) (wf (f a)) a (eq_refl (f a)).

Definition measure_relation (A : Set) (measure : A -> nat) : relation A := inverse_image lt measure.

Definition measure_well_founded : forall (A : Set) (measure : A -> nat), well_founded A (measure_relation A measure) :=
    fun A measure => inverse_image_well_founded A nat lt measure lt_well_founded.

Definition measure_induction (A : Set) (measure : A -> nat) (P : A -> Prop)
    (step : forall x : A, (forall y : A, lt (measure y) (measure x) -> P y) -> P x) : forall x : A, P x :=
    wf_induction (measure_relation A measure) (measure_well_founded A measure) P step.

Definition measure_recursion (A : Set) (measure : A -> nat) (P : A -> Set)
    (step : forall x : A, (forall y : A, lt (measure y) (measure x) -> P y) -> P x) : forall x : A, P x :=
    wf_recursion (measure_relation A measure) (measure_well_founded A measure) P step.
