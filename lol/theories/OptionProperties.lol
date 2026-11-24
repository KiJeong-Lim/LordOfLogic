(* Partial computations: functor, monad, left-biased choice and relation laws. *)
Import lol.theories.Logic.
Import lol.theories.Bool.

Theorem Some_injective : forall (A : Set) (x y : A), ((Some A x) = (Some A y)) -> (x = y) :=
    fun A x y e => f_equal (option_default A x) (Some A x) (Some A y) e.
Theorem None_not_Some : forall (A : Set) (x : A), not ((None A) = (Some A x)) :=
    fun A x e => match e in eq _ o return (match o return Prop with | None _ => True | Some _ _ => False end) with | eq_refl _ => I end.
Theorem Some_not_None : forall (A : Set) (x : A), not ((Some A x) = (None A)) :=
    fun A x e => None_not_Some A x (eq_sym (Some A x) (None A) e).
Theorem option_map_comp : forall (A B C : Set) (f : A -> B) (g : B -> C) (o : option A),
    ((option_map B C g (option_map A B f o)) = (option_map A C (fun x => g (f x)) o)) :=
    fun A B C f g o => match o as p return ((option_map B C g (option_map A B f p)) = (option_map A C (fun x => g (f x)) p)) with
    | None _ => eq_refl (None C)
    | Some _ x => eq_refl (Some C (g (f x)))
    end.
Theorem option_map_ext : forall (A B : Set) (f g : A -> B), (forall x : A, ((f x) = (g x))) ->
    forall o : option A, ((option_map A B f o) = (option_map A B g o)) :=
    fun A B f g h o => match o as p return ((option_map A B f p) = (option_map A B g p)) with
    | None _ => eq_refl (None B)
    | Some _ x => f_equal (Some B) (f x) (g x) (h x)
    end.
Theorem option_map_injective : forall (A B : Set) (f : A -> B),
    (forall x y : A, ((f x) = (f y)) -> (x = y)) ->
    forall p q : option A, ((option_map A B f p) = (option_map A B f q)) -> (p = q) :=
    fun A B f h p q => match p as a return ((option_map A B f a) = (option_map A B f q)) -> (a = q) with
    | None _ => match q as b return ((None B) = (option_map A B f b)) -> ((None A) = b) with
        | None _ => fun e => eq_refl (None A)
        | Some _ y => fun e => False_rect ((None A) = (Some A y)) (None_not_Some B (f y) e)
        end
    | Some _ x => match q as b return ((Some B (f x)) = (option_map A B f b)) -> ((Some A x) = b) with
        | None _ => fun e => False_rect ((Some A x) = (None A)) (Some_not_None B (f x) e)
        | Some _ y => fun e => f_equal (Some A) x y (h x y (Some_injective B (f x) (f y) e))
        end
    end.
Theorem option_bind_left_unit : forall (A B : Set) (x : A) (f : A -> option B),
    ((option_bind A B (Some A x) f) = (f x)) := fun A B x f => eq_refl (f x).
Theorem option_bind_right_unit : forall (A : Set) (o : option A),
    ((option_bind A A o (Some A)) = o) :=
    fun A o => match o as p return ((option_bind A A p (Some A)) = p) with
    | None _ => eq_refl (None A) | Some _ x => eq_refl (Some A x) end.
Theorem option_bind_assoc : forall (A B C : Set) (o : option A) (f : A -> option B) (g : B -> option C),
    ((option_bind B C (option_bind A B o f) g) = (option_bind A C o (fun x => option_bind B C (f x) g))) :=
    fun A B C o f g => match o as p return ((option_bind B C (option_bind A B p f) g) = (option_bind A C p (fun x => option_bind B C (f x) g))) with
    | None _ => eq_refl (None C) | Some _ x => eq_refl (option_bind B C (f x) g) end.
Theorem option_bind_ext : forall (A B : Set) (o : option A) (f g : A -> option B),
    (forall x : A, ((f x) = (g x))) -> ((option_bind A B o f) = (option_bind A B o g)) :=
    fun A B o f g h => match o as p return ((option_bind A B p f) = (option_bind A B p g)) with
    | None _ => eq_refl (None B) | Some _ x => h x end.
Theorem option_map_bind : forall (A B C : Set) (o : option A) (f : A -> option B) (g : B -> C),
    ((option_map B C g (option_bind A B o f)) = (option_bind A C o (fun x => option_map B C g (f x)))) :=
    fun A B C o f g => match o as p return ((option_map B C g (option_bind A B p f)) = (option_bind A C p (fun x => option_map B C g (f x)))) with
    | None _ => eq_refl (None C) | Some _ x => eq_refl (option_map B C g (f x)) end.
Theorem option_bind_map : forall (A B C : Set) (o : option A) (f : A -> B) (g : B -> option C),
    ((option_bind B C (option_map A B f o) g) = (option_bind A C o (fun x => g (f x)))) :=
    fun A B C o f g => match o as p return ((option_bind B C (option_map A B f p) g) = (option_bind A C p (fun x => g (f x)))) with
    | None _ => eq_refl (None C) | Some _ x => eq_refl (g (f x)) end.
Theorem option_map_as_bind : forall (A B : Set) (f : A -> B) (o : option A),
    ((option_map A B f o) = (option_bind A B o (fun x => Some B (f x)))) :=
    fun A B f o => match o as p return ((option_map A B f p) = (option_bind A B p (fun x => Some B (f x)))) with
    | None _ => eq_refl (None B) | Some _ x => eq_refl (Some B (f x)) end.
Definition option_join (A : Set) (o : option (option A)) : option A := option_bind (option A) A o (fun x => x).
Theorem option_join_map : forall (A B : Set) (f : A -> B) (o : option (option A)),
    ((option_map A B f (option_join A o)) = (option_join B (option_map (option A) (option B) (option_map A B f) o))) :=
    fun A B f o => match o as p return ((option_map A B f (option_join A p)) = (option_join B (option_map (option A) (option B) (option_map A B f) p))) with
    | None _ => eq_refl (None B) | Some _ x => eq_refl (option_map A B f x) end.
Theorem option_join_assoc : forall (A : Set) (o : option (option (option A))),
    ((option_join A (option_join (option A) o)) = (option_join A (option_map (option (option A)) (option A) (option_join A) o))) :=
    fun A o => match o as p return ((option_join A (option_join (option A) p)) = (option_join A (option_map (option (option A)) (option A) (option_join A) p))) with
    | None _ => eq_refl (None A) | Some _ x => eq_refl (option_join A x) end.
Definition option_or (A : Set) (p q : option A) : option A := match p with | None _ => q | Some _ x => Some A x end.
Theorem option_or_assoc : forall (A : Set) (p q r : option A),
    ((option_or A (option_or A p q) r) = (option_or A p (option_or A q r))) :=
    fun A p q r => match p as o return ((option_or A (option_or A o q) r) = (option_or A o (option_or A q r))) with
    | None _ => eq_refl (option_or A q r) | Some _ x => eq_refl (Some A x) end.
Theorem option_or_none_left : forall (A : Set) (p : option A), ((option_or A (None A) p) = p) := fun A p => eq_refl p.
Theorem option_or_none_right : forall (A : Set) (p : option A), ((option_or A p (None A)) = p) :=
    fun A p => match p as o return ((option_or A o (None A)) = o) with | None _ => eq_refl (None A) | Some _ x => eq_refl (Some A x) end.
Theorem option_or_idempotent : forall (A : Set) (p : option A), ((option_or A p p) = p) :=
    fun A p => match p as o return ((option_or A o o) = o) with | None _ => eq_refl (None A) | Some _ x => eq_refl (Some A x) end.
Theorem option_map_or : forall (A B : Set) (f : A -> B) (p q : option A),
    ((option_map A B f (option_or A p q)) = (option_or B (option_map A B f p) (option_map A B f q))) :=
    fun A B f p q => match p as o return ((option_map A B f (option_or A o q)) = (option_or B (option_map A B f o) (option_map A B f q))) with
    | None _ => eq_refl (option_map A B f q) | Some _ x => eq_refl (Some B (f x)) end.
Definition option_is_some (A : Set) (o : option A) : bool := match o with | None _ => false | Some _ _ => true end.
Theorem option_is_some_map : forall (A B : Set) (f : A -> B) (o : option A),
    ((option_is_some B (option_map A B f o)) = (option_is_some A o)) :=
    fun A B f o => match o as p return ((option_is_some B (option_map A B f p)) = (option_is_some A p)) with
    | None _ => eq_refl false | Some _ _ => eq_refl true end.
Theorem option_default_map : forall (A B : Set) (f : A -> B) (d : A) (o : option A),
    ((option_default B (f d) (option_map A B f o)) = (f (option_default A d o))) :=
    fun A B f d o => match o as p return ((option_default B (f d) (option_map A B f p)) = (f (option_default A d p))) with
    | None _ => eq_refl (f d) | Some _ x => eq_refl (f x) end.
Definition option_rel (A B : Set) (R : A -> B -> Prop) (p : option A) (q : option B) : Prop :=
    match p with | None _ => match q with | None _ => True | Some _ _ => False end
    | Some _ x => match q with | None _ => False | Some _ y => R x y end end.
Theorem option_rel_refl : forall (A : Set) (R : A -> A -> Prop), (forall x : A, R x x) -> forall p : option A, option_rel A A R p p :=
    fun A R h p => match p as o return option_rel A A R o o with | None _ => I | Some _ x => h x end.
Theorem option_rel_sym : forall (A : Set) (R : A -> A -> Prop), (forall x y : A, R x y -> R y x) ->
    forall p q : option A, option_rel A A R p q -> option_rel A A R q p :=
    fun A R h p q => match p as o return option_rel A A R o q -> option_rel A A R q o with
    | None _ => match q as o return option_rel A A R (None A) o -> option_rel A A R o (None A) with
        | None _ => fun e => e | Some _ y => fun e => e end
    | Some _ x => match q as o return option_rel A A R (Some A x) o -> option_rel A A R o (Some A x) with
        | None _ => fun e => e | Some _ y => fun e => h x y e end
    end.
Theorem option_rel_eq : forall (A : Set) (p q : option A), option_rel A A (fun x y => (x = y)) p q -> (p = q) :=
    fun A p q => match p as o return option_rel A A (fun x y => (x = y)) o q -> (o = q) with
    | None _ => match q as o return option_rel A A (fun x y => (x = y)) (None A) o -> ((None A) = o) with
        | None _ => fun e => eq_refl (None A) | Some _ y => fun e => False_rect ((None A) = (Some A y)) e end
    | Some _ x => match q as o return option_rel A A (fun x y => (x = y)) (Some A x) o -> ((Some A x) = o) with
        | None _ => fun e => False_rect ((Some A x) = (None A)) e | Some _ y => fun e => f_equal (Some A) x y e end
    end.
