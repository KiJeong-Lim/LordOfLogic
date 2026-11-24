(* Constructive connective and quantifier laws. No propositional extensionality. *)
Import lol.theories.Logic.

Theorem not_and_iff : forall A B : Prop, iff (not (and A B)) (A -> not B) :=
    fun A B => conj (not (and A B) -> A -> not B) ((A -> not B) -> not (and A B))
        (fun h a b => h (conj A B a b)) (fun h p => h (and_left A B p) (and_right A B p)).
Theorem triple_negation : forall A : Prop, iff (not (not (not A))) (not A) :=
    fun A => conj (not (not (not A)) -> not A) (not A -> not (not (not A)))
        (fun h a => h (fun n => n a)) (fun n h => h n).
Theorem iff_not : forall A B : Prop, iff A B -> iff (not A) (not B) :=
    fun A B h => conj (not A -> not B) (not B -> not A)
        (fun n b => n (and_right (A -> B) (B -> A) h b))
        (fun n a => n (and_left (A -> B) (B -> A) h a)).
Theorem iff_and : forall A B C D : Prop, iff A B -> iff C D -> iff (and A C) (and B D) :=
    fun A B C D h k => conj (and A C -> and B D) (and B D -> and A C)
        (and_map A C B D (and_left (A -> B) (B -> A) h) (and_left (C -> D) (D -> C) k))
        (and_map B D A C (and_right (A -> B) (B -> A) h) (and_right (C -> D) (D -> C) k)).
Theorem iff_or : forall A B C D : Prop, iff A B -> iff C D -> iff (or A C) (or B D) :=
    fun A B C D h k => conj (or A C -> or B D) (or B D -> or A C)
        (or_map A C B D (and_left (A -> B) (B -> A) h) (and_left (C -> D) (D -> C) k))
        (or_map B D A C (and_right (A -> B) (B -> A) h) (and_right (C -> D) (D -> C) k)).
Theorem iff_imp : forall A B C D : Prop, iff A B -> iff C D -> iff (A -> C) (B -> D) :=
    fun A B C D h k => conj ((A -> C) -> B -> D) ((B -> D) -> A -> C)
        (fun f b => and_left (C -> D) (D -> C) k (f (and_right (A -> B) (B -> A) h b)))
        (fun f a => and_right (C -> D) (D -> C) k (f (and_left (A -> B) (B -> A) h a))).
Theorem implication_curry : forall A B C : Prop, iff (and A B -> C) (A -> B -> C) :=
    fun A B C => conj ((and A B -> C) -> A -> B -> C) ((A -> B -> C) -> and A B -> C)
        (fun f a b => f (conj A B a b)) (fun f h => f (and_left A B h) (and_right A B h)).
Theorem implication_and : forall A B C : Prop, iff (A -> and B C) (and (A -> B) (A -> C)) :=
    fun A B C => conj ((A -> and B C) -> and (A -> B) (A -> C)) (and (A -> B) (A -> C) -> A -> and B C)
        (fun f => conj (A -> B) (A -> C) (fun a => and_left B C (f a)) (fun a => and_right B C (f a)))
        (fun h a => conj B C (and_left (A -> B) (A -> C) h a) (and_right (A -> B) (A -> C) h a)).
Theorem implication_or : forall A B C : Prop, iff (or A B -> C) (and (A -> C) (B -> C)) :=
    fun A B C => conj ((or A B -> C) -> and (A -> C) (B -> C)) (and (A -> C) (B -> C) -> or A B -> C)
        (fun f => conj (A -> C) (B -> C) (fun a => f (or_introl A B a)) (fun b => f (or_intror A B b)))
        (fun h => or_elim A B C (and_left (A -> C) (B -> C) h) (and_right (A -> C) (B -> C) h)).
Theorem and_or_distribute : forall A B C : Prop, iff (and A (or B C)) (or (and A B) (and A C)) :=
    fun A B C => conj (and A (or B C) -> or (and A B) (and A C)) (or (and A B) (and A C) -> and A (or B C))
        (fun h => or_elim B C (or (and A B) (and A C))
            (fun b => or_introl (and A B) (and A C) (conj A B (and_left A (or B C) h) b))
            (fun c => or_intror (and A B) (and A C) (conj A C (and_left A (or B C) h) c)) (and_right A (or B C) h))
        (or_elim (and A B) (and A C) (and A (or B C))
            (fun h => conj A (or B C) (and_left A B h) (or_introl B C (and_right A B h)))
            (fun h => conj A (or B C) (and_left A C h) (or_intror B C (and_right A C h)))).
Theorem or_and_distribute : forall A B C : Prop, iff (or A (and B C)) (and (or A B) (or A C)) :=
    fun A B C => conj (or A (and B C) -> and (or A B) (or A C)) (and (or A B) (or A C) -> or A (and B C))
        (or_elim A (and B C) (and (or A B) (or A C))
            (fun a => conj (or A B) (or A C) (or_introl A B a) (or_introl A C a))
            (fun h => conj (or A B) (or A C) (or_intror A B (and_left B C h)) (or_intror A C (and_right B C h))))
        (fun h => or_elim A B (or A (and B C)) (or_introl A (and B C))
            (fun b => or_elim A C (or A (and B C)) (or_introl A (and B C))
                (fun c => or_intror A (and B C) (conj B C b c)) (and_right (or A B) (or A C) h)) (and_left (or A B) (or A C) h)).
Theorem or_associate : forall A B C : Prop, iff (or (or A B) C) (or A (or B C)) :=
    fun A B C => conj (or (or A B) C -> or A (or B C)) (or A (or B C) -> or (or A B) C)
        (or_elim (or A B) C (or A (or B C))
            (or_elim A B (or A (or B C)) (or_introl A (or B C)) (fun b => or_intror A (or B C) (or_introl B C b)))
            (fun c => or_intror A (or B C) (or_intror B C c)))
        (or_elim A (or B C) (or (or A B) C)
            (fun a => or_introl (or A B) C (or_introl A B a))
            (or_elim B C (or (or A B) C) (fun b => or_introl (or A B) C (or_intror A B b)) (or_intror (or A B) C))).
Theorem forall_and : forall (A : Set) (P Q : A -> Prop),
    iff (forall x : A, and (P x) (Q x)) (and (forall x : A, P x) (forall x : A, Q x)) :=
    fun A P Q => conj ((forall x : A, and (P x) (Q x)) -> and (forall x : A, P x) (forall x : A, Q x))
        (and (forall x : A, P x) (forall x : A, Q x) -> forall x : A, and (P x) (Q x))
        (fun h => conj (forall x : A, P x) (forall x : A, Q x) (fun x => and_left (P x) (Q x) (h x)) (fun x => and_right (P x) (Q x) (h x)))
        (fun h x => conj (P x) (Q x) (and_left (forall y : A, P y) (forall y : A, Q y) h x) (and_right (forall y : A, P y) (forall y : A, Q y) h x)).
Theorem forall_iff : forall (A : Set) (P Q : A -> Prop), (forall x : A, iff (P x) (Q x)) -> iff (forall x : A, P x) (forall x : A, Q x) :=
    fun A P Q h => conj ((forall x : A, P x) -> forall x : A, Q x) ((forall x : A, Q x) -> forall x : A, P x)
        (fun p x => and_left (P x -> Q x) (Q x -> P x) (h x) (p x))
        (fun q x => and_right (P x -> Q x) (Q x -> P x) (h x) (q x)).
Theorem exists_iff : forall (A : Set) (P Q : A -> Prop), (forall x : A, iff (P x) (Q x)) -> iff (ex A P) (ex A Q) :=
    fun A P Q h => conj (ex A P -> ex A Q) (ex A Q -> ex A P)
        (ex_map A P Q (fun x => and_left (P x -> Q x) (Q x -> P x) (h x)))
        (ex_map A Q P (fun x => and_right (P x -> Q x) (Q x -> P x) (h x))).
Theorem exists_or : forall (A : Set) (P Q : A -> Prop), iff (ex A (fun x => or (P x) (Q x))) (or (ex A P) (ex A Q)) :=
    fun A P Q => conj (ex A (fun x => or (P x) (Q x)) -> or (ex A P) (ex A Q)) (or (ex A P) (ex A Q) -> ex A (fun x => or (P x) (Q x)))
        (fun e => match e return or (ex A P) (ex A Q) with
            | ex_intro _ _ x h => or_elim (P x) (Q x) (or (ex A P) (ex A Q))
                (fun p => or_introl (ex A P) (ex A Q) (ex_intro A P x p))
                (fun q => or_intror (ex A P) (ex A Q) (ex_intro A Q x q)) h end)
        (or_elim (ex A P) (ex A Q) (ex A (fun x => or (P x) (Q x)))
            (ex_map A P (fun x => or (P x) (Q x)) (fun x => or_introl (P x) (Q x)))
            (ex_map A Q (fun x => or (P x) (Q x)) (fun x => or_intror (P x) (Q x)))).
Theorem exists_and_constant : forall (A : Set) (P : A -> Prop) (Q : Prop), iff (ex A (fun x => and (P x) Q)) (and (ex A P) Q) :=
    fun A P Q => conj (ex A (fun x => and (P x) Q) -> and (ex A P) Q) (and (ex A P) Q -> ex A (fun x => and (P x) Q))
        (fun e => match e return and (ex A P) Q with | ex_intro _ _ x h => conj (ex A P) Q (ex_intro A P x (and_left (P x) Q h)) (and_right (P x) Q h) end)
        (fun h => ex_map A P (fun x => and (P x) Q) (fun x p => conj (P x) Q p (and_right (ex A P) Q h)) (and_left (ex A P) Q h)).
Theorem exists_and_projections : forall (A : Set) (P Q : A -> Prop), ex A (fun x => and (P x) (Q x)) -> and (ex A P) (ex A Q) :=
    fun A P Q e => conj (ex A P) (ex A Q)
        (ex_map A (fun x => and (P x) (Q x)) P (fun x => and_left (P x) (Q x)) e)
        (ex_map A (fun x => and (P x) (Q x)) Q (fun x => and_right (P x) (Q x)) e).
Theorem not_exists : forall (A : Set) (P : A -> Prop), iff (not (ex A P)) (forall x : A, not (P x)) :=
    fun A P => conj (not (ex A P) -> forall x : A, not (P x)) ((forall x : A, not (P x)) -> not (ex A P))
        (fun h x p => h (ex_intro A P x p))
        (fun h e => match e return False with | ex_intro _ _ x p => h x p end).
Theorem exists_not_forall : forall (A : Set) (P : A -> Prop), ex A (fun x => not (P x)) -> not (forall x : A, P x) :=
    fun A P e h => match e return False with | ex_intro _ _ x p => p (h x) end.
Theorem exists_implication : forall (A : Set) (P : A -> Prop) (Q : Prop), iff (ex A P -> Q) (forall x : A, P x -> Q) :=
    fun A P Q => conj ((ex A P -> Q) -> forall x : A, P x -> Q) ((forall x : A, P x -> Q) -> ex A P -> Q)
        (fun h x p => h (ex_intro A P x p))
        (fun h e => match e return Q with | ex_intro _ _ x p => h x p end).
Theorem forall_swap : forall (A B : Set) (R : A -> B -> Prop), iff (forall x : A, forall y : B, R x y) (forall y : B, forall x : A, R x y) :=
    fun A B R => conj ((forall x : A, forall y : B, R x y) -> forall y : B, forall x : A, R x y)
        ((forall y : B, forall x : A, R x y) -> forall x : A, forall y : B, R x y)
        (fun h y x => h x y) (fun h x y => h y x).
Theorem exists_swap : forall (A B : Set) (R : A -> B -> Prop), iff (ex A (fun x => ex B (R x))) (ex B (fun y => ex A (fun x => R x y))) :=
    fun A B R => conj (ex A (fun x => ex B (R x)) -> ex B (fun y => ex A (fun x => R x y)))
        (ex B (fun y => ex A (fun x => R x y)) -> ex A (fun x => ex B (R x)))
        (fun h => match h return ex B (fun y => ex A (fun x => R x y)) with
            | ex_intro _ _ x p => match p return ex B (fun y => ex A (fun x => R x y)) with
                | ex_intro _ _ y q => ex_intro B (fun v => ex A (fun u => R u v)) y (ex_intro A (fun u => R u y) x q) end end)
        (fun h => match h return ex A (fun x => ex B (R x)) with
            | ex_intro _ _ y p => match p return ex A (fun x => ex B (R x)) with
                | ex_intro _ _ x q => ex_intro A (fun u => ex B (R u)) x (ex_intro B (R x) y q) end end).
Theorem forall_constant_inhabited : forall (A : Set) (a : A) (P : Prop), iff (forall x : A, P) P :=
    fun A a P => conj ((forall x : A, P) -> P) (P -> forall x : A, P) (fun h => h a) (fun p x => p).
Theorem exists_constant_inhabited : forall (A : Set) (a : A) (P : Prop), iff (ex A (fun _ => P)) P :=
    fun A a P => conj (ex A (fun _ => P) -> P) (P -> ex A (fun _ => P))
        (fun h => match h return P with | ex_intro _ _ x p => p end) (fun p => ex_intro A (fun _ => P) a p).
Theorem exists_equal : forall (A : Set) (P : A -> Prop) (a : A), iff (ex A (fun x => and (x = a) (P x))) (P a) :=
    fun A P a => conj (ex A (fun x => and (x = a) (P x)) -> P a) (P a -> ex A (fun x => and (x = a) (P x)))
        (fun h => match h return P a with | ex_intro _ _ x p => eq_transport A P x a (and_left (x = a) (P x) p) (and_right (x = a) (P x) p) end)
        (fun p => ex_intro A (fun x => and (x = a) (P x)) a (conj (a = a) (P a) (eq_refl a) p)).
Theorem forall_equal : forall (A : Set) (P : A -> Prop) (a : A), iff (forall x : A, (x = a) -> P x) (P a) :=
    fun A P a => conj ((forall x : A, (x = a) -> P x) -> P a) (P a -> forall x : A, (x = a) -> P x)
        (fun h => h a (eq_refl a)) (fun p x e => eq_transport A P a x (eq_sym x a e) p).
