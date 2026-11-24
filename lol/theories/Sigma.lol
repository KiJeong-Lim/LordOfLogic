(* Proof-carrying subsets and dependent pairs. No proof irrelevance is assumed. *)
Import lol.theories.Logic.

Inductive sig (A : Set) (P : A -> Prop) : Set :=
    | exist : forall x : A, P x -> sig A P.
Definition proj1_sig (A : Set) (P : A -> Prop) (s : sig A P) : A :=
    match s with | exist _ _ x h => x end.
Definition proj2_sig (A : Set) (P : A -> Prop) (s : sig A P) : P (proj1_sig A P s) :=
    match s as t return P (proj1_sig A P t) with | exist _ _ x h => h end.
Theorem sig_eta : forall (A : Set) (P : A -> Prop) (s : sig A P),
    ((exist A P (proj1_sig A P s) (proj2_sig A P s)) = s) :=
    fun A P s => match s as t return ((exist A P (proj1_sig A P t) (proj2_sig A P t)) = t) with
    | exist _ _ x h => eq_refl (exist A P x h) end.
Theorem sig_fst_equal : forall (A : Set) (P : A -> Prop) (s t : sig A P),
    (s = t) -> ((proj1_sig A P s) = (proj1_sig A P t)) :=
    fun A P s t e => f_equal (proj1_sig A P) s t e.
Theorem sig_transport : forall (A : Set) (P : A -> Prop) (x y : A) (e : (x = y)) (p : P x),
    ((exist A P x p) = (exist A P y (eq_transport A P x y e p))) :=
    fun A P x y e p => match e as d in eq _ z return ((exist A P x p) = (exist A P z (eq_transport A P x z d p))) with
    | eq_refl _ => eq_refl (exist A P x p) end.
Theorem sig_pair_equal : forall (A : Set) (P : A -> Prop) (x y : A) (e : (x = y)) (p : P x) (q : P y),
    ((eq_transport A P x y e p) = q) -> ((exist A P x p) = (exist A P y q)) :=
    fun A P x y e p q h => eq_trans (exist A P x p) (exist A P y (eq_transport A P x y e p)) (exist A P y q)
        (sig_transport A P x y e p) (f_equal (exist A P y) (eq_transport A P x y e p) q h).
Definition sig_map (A B : Set) (P : A -> Prop) (Q : B -> Prop) (f : A -> B)
    (h : forall x : A, P x -> Q (f x)) (s : sig A P) : sig B Q :=
    exist B Q (f (proj1_sig A P s)) (h (proj1_sig A P s) (proj2_sig A P s)).
Theorem sig_map_id : forall (A : Set) (P : A -> Prop) (s : sig A P),
    ((sig_map A A P P (fun x => x) (fun x h => h) s) = s) := fun A P s => sig_eta A P s.
Theorem sig_map_comp : forall (A B C : Set) (P : A -> Prop) (Q : B -> Prop) (R : C -> Prop)
    (f : A -> B) (g : B -> C) (h : forall x : A, P x -> Q (f x)) (k : forall y : B, Q y -> R (g y)) (s : sig A P),
    ((sig_map B C Q R g k (sig_map A B P Q f h s)) =
     (sig_map A C P R (fun x => g (f x)) (fun x p => k (f x) (h x p)) s)) :=
    fun A B C P Q R f g h k s => eq_refl (sig_map A C P R (fun x => g (f x)) (fun x p => k (f x) (h x p)) s).
Definition sig_to_exists (A : Set) (P : A -> Prop) (s : sig A P) : ex A P :=
    ex_intro A P (proj1_sig A P s) (proj2_sig A P s).
Definition sig_refine (A : Set) (P Q : A -> Prop) (s : sig A P) (h : Q (proj1_sig A P s)) : sig A (fun x => and (P x) (Q x)) :=
    exist A (fun x => and (P x) (Q x)) (proj1_sig A P s)
        (conj (P (proj1_sig A P s)) (Q (proj1_sig A P s)) (proj2_sig A P s) h).
Definition sig_weaken (A : Set) (P Q : A -> Prop) (h : forall x : A, P x -> Q x) (s : sig A P) : sig A Q :=
    sig_map A A P Q (fun x => x) h s.
Theorem sig_weaken_fst : forall (A : Set) (P Q : A -> Prop) (h : forall x : A, P x -> Q x) (s : sig A P),
    ((proj1_sig A Q (sig_weaken A P Q h s)) = (proj1_sig A P s)) := fun A P Q h s => eq_refl (proj1_sig A P s).
Definition sig_choice (A : Set) (B : A -> Set) (P : forall x : A, B x -> Prop)
    (h : forall x : A, sig (B x) (P x)) : sig (forall x : A, B x) (fun f => forall x : A, P x (f x)) :=
    exist (forall x : A, B x) (fun f => forall x : A, P x (f x))
        (fun x => proj1_sig (B x) (P x) (h x)) (fun x => proj2_sig (B x) (P x) (h x)).

Inductive sigT (A : Set) (P : A -> Set) : Set :=
    | existT : forall x : A, P x -> sigT A P.
Definition projT1 (A : Set) (P : A -> Set) (s : sigT A P) : A :=
    match s with | existT _ _ x p => x end.
Definition projT2 (A : Set) (P : A -> Set) (s : sigT A P) : P (projT1 A P s) :=
    match s as t return P (projT1 A P t) with | existT _ _ x p => p end.
Theorem sigT_eta : forall (A : Set) (P : A -> Set) (s : sigT A P),
    ((existT A P (projT1 A P s) (projT2 A P s)) = s) :=
    fun A P s => match s as t return ((existT A P (projT1 A P t) (projT2 A P t)) = t) with
    | existT _ _ x p => eq_refl (existT A P x p) end.
Theorem sigT_fst_equal : forall (A : Set) (P : A -> Set) (s t : sigT A P),
    (s = t) -> ((projT1 A P s) = (projT1 A P t)) := fun A P s t e => f_equal (projT1 A P) s t e.
Theorem sigT_transport : forall (A : Set) (P : A -> Set) (x y : A) (e : (x = y)) (p : P x),
    ((existT A P x p) = (existT A P y (eq_transport A P x y e p))) :=
    fun A P x y e p => match e as d in eq _ z return ((existT A P x p) = (existT A P z (eq_transport A P x z d p))) with
    | eq_refl _ => eq_refl (existT A P x p) end.
Theorem sigT_pair_equal : forall (A : Set) (P : A -> Set) (x y : A) (e : (x = y)) (p : P x) (q : P y),
    ((eq_transport A P x y e p) = q) -> ((existT A P x p) = (existT A P y q)) :=
    fun A P x y e p q h => eq_trans (existT A P x p) (existT A P y (eq_transport A P x y e p)) (existT A P y q)
        (sigT_transport A P x y e p) (f_equal (existT A P y) (eq_transport A P x y e p) q h).
Definition sigT_map (A B : Set) (P : A -> Set) (Q : B -> Set) (f : A -> B)
    (h : forall x : A, P x -> Q (f x)) (s : sigT A P) : sigT B Q :=
    existT B Q (f (projT1 A P s)) (h (projT1 A P s) (projT2 A P s)).
Theorem sigT_map_id : forall (A : Set) (P : A -> Set) (s : sigT A P),
    ((sigT_map A A P P (fun x => x) (fun x p => p) s) = s) := fun A P s => sigT_eta A P s.
Theorem sigT_map_comp : forall (A B C : Set) (P : A -> Set) (Q : B -> Set) (R : C -> Set)
    (f : A -> B) (g : B -> C) (h : forall x : A, P x -> Q (f x)) (k : forall y : B, Q y -> R (g y)) (s : sigT A P),
    ((sigT_map B C Q R g k (sigT_map A B P Q f h s)) =
     (sigT_map A C P R (fun x => g (f x)) (fun x p => k (f x) (h x p)) s)) :=
    fun A B C P Q R f g h k s => eq_refl (sigT_map A C P R (fun x => g (f x)) (fun x p => k (f x) (h x p)) s).
Definition sigT_of_prod (A B : Set) (p : prod A B) : sigT A (fun _ => B) :=
    existT A (fun _ => B) (fst A B p) (snd A B p).
Definition sigT_to_prod (A B : Set) (s : sigT A (fun _ => B)) : prod A B :=
    pair A B (projT1 A (fun _ => B) s) (projT2 A (fun _ => B) s).
Theorem sigT_prod_roundtrip : forall (A B : Set) (p : prod A B), ((sigT_to_prod A B (sigT_of_prod A B p)) = p) :=
    fun A B p => prod_eta A B p.
Theorem prod_sigT_roundtrip : forall (A B : Set) (s : sigT A (fun _ => B)), ((sigT_of_prod A B (sigT_to_prod A B s)) = s) :=
    fun A B s => sigT_eta A (fun _ => B) s.
Definition sigT_choice (A : Set) (B : A -> Set) (R : forall x : A, B x -> Set)
    (h : forall x : A, sigT (B x) (R x)) : sigT (forall x : A, B x) (fun f => forall x : A, R x (f x)) :=
    existT (forall x : A, B x) (fun f => forall x : A, R x (f x))
        (fun x => projT1 (B x) (R x) (h x)) (fun x => projT2 (B x) (R x) (h x)).
