(* Product isomorphisms, componentwise relations and constructive equality. *)
Import lol.theories.Logic.
Import lol.theories.Decidable.

Theorem pair_fst_injective : forall (A B : Set) (a c : A) (b d : B),
    ((pair A B a b) = (pair A B c d)) -> (a = c) :=
    fun A B a c b d e => f_equal (fst A B) (pair A B a b) (pair A B c d) e.
Theorem pair_snd_injective : forall (A B : Set) (a c : A) (b d : B),
    ((pair A B a b) = (pair A B c d)) -> (b = d) :=
    fun A B a c b d e => f_equal (snd A B) (pair A B a b) (pair A B c d) e.
Theorem pair_congr : forall (A B : Set) (a c : A) (b d : B), (a = c) -> (b = d) -> ((pair A B a b) = (pair A B c d)) :=
    fun A B a c b d h k => eq_trans (pair A B a b) (pair A B c b) (pair A B c d)
        (f_equal (fun x => pair A B x b) a c h) (f_equal (pair A B c) b d k).
Theorem prod_ext : forall (A B : Set) (p q : prod A B), ((fst A B p) = (fst A B q)) ->
    ((snd A B p) = (snd A B q)) -> (p = q) :=
    fun A B p q h k => eq_trans p (pair A B (fst A B p) (snd A B p)) q
        (eq_sym (pair A B (fst A B p) (snd A B p)) p (prod_eta A B p))
        (eq_trans (pair A B (fst A B p) (snd A B p)) (pair A B (fst A B q) (snd A B q)) q
            (pair_congr A B (fst A B p) (fst A B q) (snd A B p) (snd A B q) h k) (prod_eta A B q)).
Theorem prod_eq_iff : forall (A B : Set) (p q : prod A B),
    iff (p = q) (and ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q))) :=
    fun A B p q => conj ((p = q) -> and ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q)))
        (and ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q)) -> (p = q))
        (fun e => conj ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q))
            (f_equal (fst A B) p q e) (f_equal (snd A B) p q e))
        (fun h => prod_ext A B p q
            (and_left ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q)) h)
            (and_right ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q)) h)).
Theorem prod_map_id : forall (A B : Set) (p : prod A B), ((prod_map A B A B (fun x => x) (fun y => y) p) = p).
Proof.
    intros A B p.
    exact (prod_eta A B p).
Qed.
Theorem prod_map_comp : forall (A B C D E F : Set) (f : A -> C) (g : B -> D) (h : C -> E) (k : D -> F) (p : prod A B),
    ((prod_map C D E F h k (prod_map A B C D f g p)) = (prod_map A B E F (fun x => h (f x)) (fun y => k (g y)) p)).
Proof.
    intros.
    reflexivity.
Qed.
Theorem prod_map_ext : forall (A B C D : Set) (f h : A -> C) (g k : B -> D),
    (forall x : A, ((f x) = (h x))) -> (forall y : B, ((g y) = (k y))) ->
    forall p : prod A B, ((prod_map A B C D f g p) = (prod_map A B C D h k p)) :=
    fun A B C D f h g k e j p => pair_congr C D (f (fst A B p)) (h (fst A B p)) (g (snd A B p)) (k (snd A B p))
        (e (fst A B p)) (j (snd A B p)).
Theorem prod_map_injective : forall (A B C D : Set) (f : A -> C) (g : B -> D),
    (forall x y : A, ((f x) = (f y)) -> (x = y)) -> (forall x y : B, ((g x) = (g y)) -> (x = y)) ->
    forall p q : prod A B, ((prod_map A B C D f g p) = (prod_map A B C D f g q)) -> (p = q) :=
    fun A B C D f g h k p q e => prod_ext A B p q
        (h (fst A B p) (fst A B q) (f_equal (fst C D) (prod_map A B C D f g p) (prod_map A B C D f g q) e))
        (k (snd A B p) (snd A B q) (f_equal (snd C D) (prod_map A B C D f g p) (prod_map A B C D f g q) e)).
Theorem prod_swap_involutive : forall (A B : Set) (p : prod A B), ((prod_swap B A (prod_swap A B p)) = p).
Proof.
    intros A B p.
    exact (prod_eta A B p).
Qed.
Theorem prod_swap_map : forall (A B C D : Set) (f : A -> C) (g : B -> D) (p : prod A B),
    ((prod_swap C D (prod_map A B C D f g p)) = (prod_map B A D C g f (prod_swap A B p))) :=
    fun A B C D f g p => eq_refl (pair D C (g (snd A B p)) (f (fst A B p))).
Theorem curry_uncurry : forall (A B C : Set) (f : A -> B -> C) (a : A) (b : B),
    ((curry A B C (uncurry A B C f) a b) = (f a b)).
Proof.
    intros.
    reflexivity.
Qed.
Theorem uncurry_curry : forall (A B C : Set) (f : prod A B -> C) (p : prod A B),
    ((uncurry A B C (curry A B C f) p) = (f p)) :=
    fun A B C f p => f_equal f (pair A B (fst A B p) (snd A B p)) p (prod_eta A B p).
Definition prod_assoc (A B C : Set) (p : prod (prod A B) C) : prod A (prod B C) :=
    pair A (prod B C) (fst A B (fst (prod A B) C p))
        (pair B C (snd A B (fst (prod A B) C p)) (snd (prod A B) C p)).
Definition prod_unassoc (A B C : Set) (p : prod A (prod B C)) : prod (prod A B) C :=
    pair (prod A B) C (pair A B (fst A (prod B C) p) (fst B C (snd A (prod B C) p))) (snd B C (snd A (prod B C) p)).
Theorem prod_assoc_inverse : forall (A B C : Set) (p : prod (prod A B) C), ((prod_unassoc A B C (prod_assoc A B C p)) = p) :=
    fun A B C p => prod_ext (prod A B) C (prod_unassoc A B C (prod_assoc A B C p)) p
        (prod_eta A B (fst (prod A B) C p)) (eq_refl (snd (prod A B) C p)).
Theorem prod_unassoc_inverse : forall (A B C : Set) (p : prod A (prod B C)), ((prod_assoc A B C (prod_unassoc A B C p)) = p) :=
    fun A B C p => prod_ext A (prod B C) (prod_assoc A B C (prod_unassoc A B C p)) p
        (eq_refl (fst A (prod B C) p)) (prod_eta B C (snd A (prod B C) p)).
Definition prod_eq_dec (A B : Set) (da : equality_decision A) (db : equality_decision B) : equality_decision (prod A B) :=
    fun p q => decide_transport (and ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q))) (p = q)
        (iff_sym (p = q) (and ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q))) (prod_eq_iff A B p q))
        (decide_and ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q))
            (da (fst A B p) (fst A B q)) (db (snd A B p) (snd A B q))).
Definition prod_rel (A B C D : Set) (R : A -> C -> Prop) (S : B -> D -> Prop) (p : prod A B) (q : prod C D) : Prop :=
    and (R (fst A B p) (fst C D q)) (S (snd A B p) (snd C D q)).
Theorem prod_rel_refl : forall (A B : Set) (R : A -> A -> Prop) (S : B -> B -> Prop),
    (forall x : A, R x x) -> (forall y : B, S y y) -> forall p : prod A B, prod_rel A B A B R S p p :=
    fun A B R S h k p => conj (R (fst A B p) (fst A B p)) (S (snd A B p) (snd A B p)) (h (fst A B p)) (k (snd A B p)).
Theorem prod_rel_eq : forall (A B : Set) (p q : prod A B), prod_rel A B A B (fun x y => (x = y)) (fun x y => (x = y)) p q -> (p = q) :=
    fun A B p q h => prod_ext A B p q
        (and_left ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q)) h)
        (and_right ((fst A B p) = (fst A B q)) ((snd A B p) = (snd A B q)) h).
Definition prod_distribute (A B C : Set) (p : prod A (sum B C)) : sum (prod A B) (prod A C) :=
    match snd A (sum B C) p with
    | inl _ _ b => inl (prod A B) (prod A C) (pair A B (fst A (sum B C) p) b)
    | inr _ _ c => inr (prod A B) (prod A C) (pair A C (fst A (sum B C) p) c)
    end.
Definition prod_factor (A B C : Set) (s : sum (prod A B) (prod A C)) : prod A (sum B C) :=
    match s with
    | inl _ _ p => pair A (sum B C) (fst A B p) (inl B C (snd A B p))
    | inr _ _ p => pair A (sum B C) (fst A C p) (inr B C (snd A C p))
    end.
Theorem prod_distribute_inverse : forall (A B C : Set) (p : prod A (sum B C)), ((prod_factor A B C (prod_distribute A B C p)) = p) :=
    fun A B C p => match p as q return ((prod_factor A B C (prod_distribute A B C q)) = q) with
    | pair _ _ a s => match s as t return ((prod_factor A B C (prod_distribute A B C (pair A (sum B C) a t))) = (pair A (sum B C) a t)) with
        | inl _ _ b => eq_refl (pair A (sum B C) a (inl B C b))
        | inr _ _ c => eq_refl (pair A (sum B C) a (inr B C c)) end
    end.
Theorem prod_factor_inverse : forall (A B C : Set) (s : sum (prod A B) (prod A C)), ((prod_distribute A B C (prod_factor A B C s)) = s) :=
    fun A B C s => match s as t return ((prod_distribute A B C (prod_factor A B C t)) = t) with
    | inl _ _ p => f_equal (inl (prod A B) (prod A C)) (pair A B (fst A B p) (snd A B p)) p (prod_eta A B p)
    | inr _ _ p => f_equal (inr (prod A B) (prod A C)) (pair A C (fst A C p) (snd A C p)) p (prod_eta A C p)
    end.
