(* Relation algebra and finite paths, reusing the accessibility library. *)
Import lol.theories.Logic.
Import lol.theories.Wf.

Definition antisymmetric (A : Set) (R : relation A) : Prop := forall x y : A, R x y -> R y x -> (x = y).
Definition equivalence (A : Set) (R : relation A) : Prop := and (reflexive R) (and (symmetric R) (transitive R)).
Definition preorder (A : Set) (R : relation A) : Prop := and (reflexive R) (transitive R).
Definition partial_order (A : Set) (R : relation A) : Prop := and (preorder A R) (antisymmetric A R).
Definition relation_equiv (A : Set) (R S : relation A) : Prop := forall x y : A, iff (R x y) (S x y).
Theorem subrelation_refl : forall (A : Set) (R : relation A), subrelation R R := fun A R x y h => h.
Theorem subrelation_trans : forall (A : Set) (R S T : relation A), subrelation R S -> subrelation S T -> subrelation R T :=
    fun A R S T h k x y e => k x y (h x y e).
Theorem relation_equiv_refl : forall (A : Set) (R : relation A), relation_equiv A R R := fun A R x y => iff_refl (R x y).
Theorem relation_equiv_sym : forall (A : Set) (R S : relation A), relation_equiv A R S -> relation_equiv A S R :=
    fun A R S h x y => iff_sym (R x y) (S x y) (h x y).
Theorem relation_equiv_trans : forall (A : Set) (R S T : relation A), relation_equiv A R S -> relation_equiv A S T -> relation_equiv A R T :=
    fun A R S T h k x y => iff_trans (R x y) (S x y) (T x y) (h x y) (k x y).
Theorem relation_equiv_sub : forall (A : Set) (R S : relation A), relation_equiv A R S -> subrelation R S :=
    fun A R S h x y => and_left (R x y -> S x y) (S x y -> R x y) (h x y).
Theorem subrelation_equiv : forall (A : Set) (R S : relation A), subrelation R S -> subrelation S R -> relation_equiv A R S :=
    fun A R S h k x y => conj (R x y -> S x y) (S x y -> R x y) (h x y) (k x y).
Theorem inverse_involutive : forall (A : Set) (R : relation A), relation_equiv A (inverse_relation (inverse_relation R)) R :=
    fun A R => relation_equiv_refl A R.
Theorem inverse_subrelation : forall (A : Set) (R S : relation A), subrelation R S -> subrelation (inverse_relation R) (inverse_relation S) :=
    fun A R S h x y => h y x.
Theorem inverse_reflexive : forall (A : Set) (R : relation A), reflexive R -> reflexive (inverse_relation R) := fun A R h => h.
Theorem inverse_symmetric : forall (A : Set) (R : relation A), symmetric R -> symmetric (inverse_relation R) := fun A R h x y => h y x.
Theorem inverse_transitive : forall (A : Set) (R : relation A), transitive R -> transitive (inverse_relation R) :=
    fun A R h x y z p q => h z y x q p.
Theorem inverse_antisymmetric : forall (A : Set) (R : relation A), antisymmetric A R -> antisymmetric A (inverse_relation R) :=
    fun A R h x y p q => h x y q p.
Theorem intersection_reflexive : forall (A : Set) (R S : relation A), reflexive R -> reflexive S -> reflexive (relation_intersection R S) :=
    fun A R S h k x => conj (R x x) (S x x) (h x) (k x).
Theorem intersection_symmetric : forall (A : Set) (R S : relation A), symmetric R -> symmetric S -> symmetric (relation_intersection R S) :=
    fun A R S h k x y e => conj (R y x) (S y x) (h x y (and_left (R x y) (S x y) e)) (k x y (and_right (R x y) (S x y) e)).
Theorem intersection_transitive : forall (A : Set) (R S : relation A), transitive R -> transitive S -> transitive (relation_intersection R S) :=
    fun A R S h k x y z p q => conj (R x z) (S x z)
        (h x y z (and_left (R x y) (S x y) p) (and_left (R y z) (S y z) q))
        (k x y z (and_right (R x y) (S x y) p) (and_right (R y z) (S y z) q)).
Theorem union_symmetric : forall (A : Set) (R S : relation A), symmetric R -> symmetric S -> symmetric (relation_union R S) :=
    fun A R S h k x y => or_map (R x y) (S x y) (R y x) (S y x) (h x y) (k x y).
Theorem union_sub_left : forall (A : Set) (R S : relation A), subrelation R (relation_union R S) :=
    fun A R S x y => or_introl (R x y) (S x y).
Theorem union_sub_right : forall (A : Set) (R S : relation A), subrelation S (relation_union R S) :=
    fun A R S x y => or_intror (R x y) (S x y).
Theorem union_least : forall (A : Set) (R S T : relation A), subrelation R T -> subrelation S T -> subrelation (relation_union R S) T :=
    fun A R S T h k x y => or_elim (R x y) (S x y) (T x y) (h x y) (k x y).
Theorem intersection_greatest : forall (A : Set) (R S T : relation A), subrelation T R -> subrelation T S -> subrelation T (relation_intersection R S) :=
    fun A R S T h k x y e => conj (R x y) (S x y) (h x y e) (k x y e).
Theorem equality_equivalence : forall A : Set, equivalence A (fun x y => (x = y)) :=
    fun A => conj (reflexive (fun x y : A => (x = y))) (and (symmetric (fun x y : A => (x = y))) (transitive (fun x y : A => (x = y))))
        (fun x => eq_refl x)
        (conj (symmetric (fun x y : A => (x = y))) (transitive (fun x y : A => (x = y))) (fun x y => eq_sym x y) (fun x y z => eq_trans x y z)).
Theorem equivalence_preorder : forall (A : Set) (R : relation A), equivalence A R -> preorder A R :=
    fun A R h => conj (reflexive R) (transitive R) (and_left (reflexive R) (and (symmetric R) (transitive R)) h)
        (and_right (symmetric R) (transitive R) (and_right (reflexive R) (and (symmetric R) (transitive R)) h)).
Definition relation_comp (A : Set) (R S : relation A) : relation A := fun x z => ex A (fun y => and (R x y) (S y z)).
Theorem relation_comp_intro : forall (A : Set) (R S : relation A) (x y z : A), R x y -> S y z -> relation_comp A R S x z :=
    fun A R S x y z h k => ex_intro A (fun v => and (R x v) (S v z)) y (conj (R x y) (S y z) h k).
Theorem relation_comp_mono : forall (A : Set) (R S U V : relation A), subrelation R U -> subrelation S V -> subrelation (relation_comp A R S) (relation_comp A U V) :=
    fun A R S U V h k x z e => match e return relation_comp A U V x z with
    | ex_intro _ _ y p => relation_comp_intro A U V x y z (h x y (and_left (R x y) (S y z) p)) (k y z (and_right (R x y) (S y z) p)) end.
Theorem relation_comp_assoc_forward : forall (A : Set) (R S T : relation A),
    subrelation (relation_comp A (relation_comp A R S) T) (relation_comp A R (relation_comp A S T)) :=
    fun A R S T x z e => match e return relation_comp A R (relation_comp A S T) x z with
    | ex_intro _ _ y p => match and_left (relation_comp A R S x y) (T y z) p return relation_comp A R (relation_comp A S T) x z with
        | ex_intro _ _ v q => relation_comp_intro A R (relation_comp A S T) x v z (and_left (R x v) (S v y) q)
            (relation_comp_intro A S T v y z (and_right (R x v) (S v y) q) (and_right (relation_comp A R S x y) (T y z) p)) end
    end.
Theorem relation_comp_assoc_backward : forall (A : Set) (R S T : relation A),
    subrelation (relation_comp A R (relation_comp A S T)) (relation_comp A (relation_comp A R S) T) :=
    fun A R S T x z e => match e return relation_comp A (relation_comp A R S) T x z with
    | ex_intro _ _ y p => match and_right (R x y) (relation_comp A S T y z) p return relation_comp A (relation_comp A R S) T x z with
        | ex_intro _ _ v q => relation_comp_intro A (relation_comp A R S) T x v z
            (relation_comp_intro A R S x y v (and_left (R x y) (relation_comp A S T y z) p) (and_left (S y v) (T v z) q))
            (and_right (S y v) (T v z) q) end
    end.
Theorem relation_comp_assoc : forall (A : Set) (R S T : relation A),
    relation_equiv A (relation_comp A (relation_comp A R S) T) (relation_comp A R (relation_comp A S T)) :=
    fun A R S T => subrelation_equiv A (relation_comp A (relation_comp A R S) T) (relation_comp A R (relation_comp A S T))
        (relation_comp_assoc_forward A R S T) (relation_comp_assoc_backward A R S T).

Inductive rtc (A : Set) (R : relation A) : A -> A -> Prop :=
    | rtc_refl : forall x : A, rtc A R x x
    | rtc_step : forall x y z : A, R x y -> rtc A R y z -> rtc A R x z.
Arguments rtc {A} R x y.
Arguments rtc_refl {A} {R} x.
Arguments rtc_step {A} {R} x y z edge path.
Theorem rtc_single : forall (A : Set) (R : relation A), subrelation R (rtc R) :=
    fun A R x y h => rtc_step x y y h (rtc_refl y).
Theorem rtc_transitive : forall (A : Set) (R : relation A), transitive (rtc R) :=
    fun A R => fix go (x y z : A) (h : rtc R x y) {struct h} : rtc R y z -> rtc R x z :=
        match h in rtc _ a b return rtc R b z -> rtc R a z with
        | rtc_refl a => fun k => k
        | rtc_step a b c e p => fun k => rtc_step a b z e (go b c z p k)
        end.
Theorem rtc_map : forall (A B : Set) (R : relation A) (S : relation B) (f : A -> B),
    (forall x y : A, R x y -> S (f x) (f y)) -> forall x y : A, rtc R x y -> rtc S (f x) (f y) :=
    fun A B R S f edge => fix go (x y : A) (h : rtc R x y) {struct h} : rtc S (f x) (f y) :=
        match h in rtc _ a b return rtc S (f a) (f b) with
        | rtc_refl a => rtc_refl (f a)
        | rtc_step a b c e p => rtc_step (f a) (f b) (f c) (edge a b e) (go b c p)
        end.
Theorem rtc_mono : forall (A : Set) (R S : relation A), subrelation R S -> subrelation (rtc R) (rtc S) :=
    fun A R S h => rtc_map A A R S (fun x => x) h.
Theorem rtc_least : forall (A : Set) (R S : relation A), reflexive S -> transitive S -> subrelation R S -> subrelation (rtc R) S :=
    fun A R S refl trans edge => fix go (x y : A) (h : rtc R x y) {struct h} : S x y :=
        match h in rtc _ a b return S a b with
        | rtc_refl a => refl a
        | rtc_step a b c e p => trans a b c (edge a b e) (go b c p)
        end.
Theorem rtc_flatten : forall (A : Set) (R : relation A), subrelation (rtc (rtc R)) (rtc R) :=
    fun A R => rtc_least A (rtc R) (rtc R) (fun x => rtc_refl x) (rtc_transitive A R) (subrelation_refl A (rtc R)).
Theorem rtc_idempotent : forall (A : Set) (R : relation A), relation_equiv A (rtc (rtc R)) (rtc R) :=
    fun A R => subrelation_equiv A (rtc (rtc R)) (rtc R) (rtc_flatten A R) (rtc_single A (rtc R)).
Theorem rtc_induction : forall (A : Set) (R : relation A) (P : A -> Prop),
    (forall x y : A, R x y -> P x -> P y) -> forall x y : A, rtc R x y -> P x -> P y :=
    fun A R P step => fix go (x y : A) (h : rtc R x y) {struct h} : P x -> P y :=
        match h in rtc _ a b return P a -> P b with
        | rtc_refl a => fun p => p
        | rtc_step a b c e p => fun q => go b c p (step a b e q)
        end.
Theorem rtc_symmetric : forall (A : Set) (R : relation A), symmetric R -> symmetric (rtc R) :=
    fun A R sym => fix go (x y : A) (h : rtc R x y) {struct h} : rtc R y x :=
        match h in rtc _ a b return rtc R b a with
        | rtc_refl a => rtc_refl a
        | rtc_step a b c e p => rtc_transitive A R c b a (go b c p) (rtc_single A R b a (sym a b e))
        end.
Theorem rtc_preorder : forall (A : Set) (R : relation A), preorder A (rtc R) :=
    fun A R => conj (reflexive (rtc R)) (transitive (rtc R)) (fun x => rtc_refl x) (rtc_transitive A R).
Theorem rtc_inverse : forall (A : Set) (R : relation A) (x y : A), rtc R x y -> rtc (inverse_relation R) y x :=
    fun A R => fix go (x y : A) (h : rtc R x y) {struct h} : rtc (inverse_relation R) y x :=
        match h in rtc _ a b return rtc (inverse_relation R) b a with
        | rtc_refl a => rtc_refl a
        | rtc_step a b c e p => rtc_transitive A (inverse_relation R) c b a (go b c p) (rtc_single A (inverse_relation R) b a e)
        end.
Inductive tc (A : Set) (R : relation A) : A -> A -> Prop :=
    | tc_single : forall x y : A, R x y -> tc A R x y
    | tc_step : forall x y z : A, R x y -> tc A R y z -> tc A R x z.
Arguments tc {A} R x y.
Arguments tc_single {A} {R} x y edge.
Arguments tc_step {A} {R} x y z edge path.
Theorem tc_to_rtc : forall (A : Set) (R : relation A), subrelation (tc R) (rtc R) :=
    fun A R => fix go (x y : A) (h : tc R x y) {struct h} : rtc R x y :=
        match h in tc _ a b return rtc R a b with
        | tc_single a b e => rtc_single A R a b e
        | tc_step a b c e p => rtc_step a b c e (go b c p)
        end.
Theorem tc_transitive : forall (A : Set) (R : relation A), transitive (tc R) :=
    fun A R => fix go (x y z : A) (h : tc R x y) {struct h} : tc R y z -> tc R x z :=
        match h in tc _ a b return tc R b z -> tc R a z with
        | tc_single a b e => fun p => tc_step a b z e p
        | tc_step a b c e p => fun q => tc_step a b z e (go b c z p q)
        end.
Theorem tc_least : forall (A : Set) (R S : relation A), transitive S -> subrelation R S -> subrelation (tc R) S :=
    fun A R S trans edge => fix go (x y : A) (h : tc R x y) {struct h} : S x y :=
        match h in tc _ a b return S a b with
        | tc_single a b e => edge a b e
        | tc_step a b c e p => trans a b c (edge a b e) (go b c p)
        end.
Theorem tc_map : forall (A B : Set) (R : relation A) (S : relation B) (f : A -> B),
    (forall x y : A, R x y -> S (f x) (f y)) -> forall x y : A, tc R x y -> tc S (f x) (f y) :=
    fun A B R S f edge => fix go (x y : A) (h : tc R x y) {struct h} : tc S (f x) (f y) :=
        match h in tc _ a b return tc S (f a) (f b) with
        | tc_single a b e => tc_single (f a) (f b) (edge a b e)
        | tc_step a b c e p => tc_step (f a) (f b) (f c) (edge a b e) (go b c p)
        end.
Theorem tc_mono : forall (A : Set) (R S : relation A), subrelation R S -> subrelation (tc R) (tc S) :=
    fun A R S h => tc_map A A R S (fun x => x) h.
Theorem rtc_equivalence : forall (A : Set) (R : relation A), symmetric R -> equivalence A (rtc R) :=
    fun A R h => conj (reflexive (rtc R)) (and (symmetric (rtc R)) (transitive (rtc R)))
        (fun x => rtc_refl x) (conj (symmetric (rtc R)) (transitive (rtc R)) (rtc_symmetric A R h) (rtc_transitive A R)).
Theorem tc_flatten : forall (A : Set) (R : relation A), subrelation (tc (tc R)) (tc R) :=
    fun A R => tc_least A (tc R) (tc R) (tc_transitive A R) (subrelation_refl A (tc R)).
Theorem tc_idempotent : forall (A : Set) (R : relation A), relation_equiv A (tc (tc R)) (tc R) :=
    fun A R => subrelation_equiv A (tc (tc R)) (tc R) (tc_flatten A R)
        (fun x y h => @tc_single A (tc R) x y h).
Theorem tc_induction : forall (A : Set) (R : relation A) (P : A -> A -> Prop),
    (forall x y : A, R x y -> P x y) -> (forall x y z : A, R x y -> P y z -> P x z) ->
    forall x y : A, tc R x y -> P x y :=
    fun A R P base step => fix go (x y : A) (h : tc R x y) {struct h} : P x y :=
        match h in tc _ a b return P a b with
        | tc_single a b e => base a b e
        | tc_step a b c e p => step a b c e (go b c p)
        end.
