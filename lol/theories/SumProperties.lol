(* Coproduct isomorphisms and the error-or-result computation laws. *)
Import lol.theories.Logic.
Import lol.theories.Decidable.
Import lol.theories.OptionProperties.

Definition sum_left (A B : Set) (s : sum A B) : option A :=
    match s with | inl _ _ x => Some A x | inr _ _ y => None A end.
Definition sum_right (A B : Set) (s : sum A B) : option B :=
    match s with | inl _ _ x => None B | inr _ _ y => Some B y end.
Theorem inl_injective : forall (A B : Set) (x y : A), ((inl A B x) = (inl A B y)) -> (x = y) :=
    fun A B x y e => Some_injective A x y (f_equal (sum_left A B) (inl A B x) (inl A B y) e).
Theorem inr_injective : forall (A B : Set) (x y : B), ((inr A B x) = (inr A B y)) -> (x = y) :=
    fun A B x y e => Some_injective B x y (f_equal (sum_right A B) (inr A B x) (inr A B y) e).
Theorem inl_not_inr : forall (A B : Set) (x : A) (y : B), not ((inl A B x) = (inr A B y)) :=
    fun A B x y e => Some_not_None A x (f_equal (sum_left A B) (inl A B x) (inr A B y) e).
Theorem inr_not_inl : forall (A B : Set) (x : A) (y : B), not ((inr A B y) = (inl A B x)) :=
    fun A B x y e => inl_not_inr A B x y (eq_sym (inr A B y) (inl A B x) e).
Theorem sum_eta : forall (A B : Set) (s : sum A B), ((sum_elim A B (sum A B) (inl A B) (inr A B) s) = s) :=
    fun A B s => match s as t return ((sum_elim A B (sum A B) (inl A B) (inr A B) t) = t) with
    | inl _ _ x => eq_refl (inl A B x) | inr _ _ y => eq_refl (inr A B y) end.
Theorem sum_map_id : forall (A B : Set) (s : sum A B), ((sum_map A B A B (fun x => x) (fun y => y) s) = s) :=
    fun A B s => sum_eta A B s.
Theorem sum_map_comp : forall (A B C D E F : Set) (f : A -> C) (g : B -> D) (h : C -> E) (k : D -> F) (s : sum A B),
    ((sum_map C D E F h k (sum_map A B C D f g s)) = (sum_map A B E F (fun x => h (f x)) (fun y => k (g y)) s)) :=
    fun A B C D E F f g h k s => match s as t return ((sum_map C D E F h k (sum_map A B C D f g t)) = (sum_map A B E F (fun x => h (f x)) (fun y => k (g y)) t)) with
    | inl _ _ x => eq_refl (inl E F (h (f x))) | inr _ _ y => eq_refl (inr E F (k (g y))) end.
Theorem sum_map_ext : forall (A B C D : Set) (f h : A -> C) (g k : B -> D),
    (forall x : A, ((f x) = (h x))) -> (forall y : B, ((g y) = (k y))) ->
    forall s : sum A B, ((sum_map A B C D f g s) = (sum_map A B C D h k s)) :=
    fun A B C D f h g k e j s => match s as t return ((sum_map A B C D f g t) = (sum_map A B C D h k t)) with
    | inl _ _ x => f_equal (inl C D) (f x) (h x) (e x)
    | inr _ _ y => f_equal (inr C D) (g y) (k y) (j y) end.
Theorem sum_map_injective : forall (A B C D : Set) (f : A -> C) (g : B -> D),
    (forall x y : A, ((f x) = (f y)) -> (x = y)) -> (forall x y : B, ((g x) = (g y)) -> (x = y)) ->
    forall p q : sum A B, ((sum_map A B C D f g p) = (sum_map A B C D f g q)) -> (p = q) :=
    fun A B C D f g h k p q => match p as a return ((sum_map A B C D f g a) = (sum_map A B C D f g q)) -> (a = q) with
    | inl _ _ x => match q as b return ((inl C D (f x)) = (sum_map A B C D f g b)) -> ((inl A B x) = b) with
        | inl _ _ y => fun e => f_equal (inl A B) x y (h x y (inl_injective C D (f x) (f y) e))
        | inr _ _ y => fun e => False_rect ((inl A B x) = (inr A B y)) (inl_not_inr C D (f x) (g y) e) end
    | inr _ _ x => match q as b return ((inr C D (g x)) = (sum_map A B C D f g b)) -> ((inr A B x) = b) with
        | inl _ _ y => fun e => False_rect ((inr A B x) = (inl A B y)) (inr_not_inl C D (f y) (g x) e)
        | inr _ _ y => fun e => f_equal (inr A B) x y (k x y (inr_injective C D (g x) (g y) e)) end
    end.
Definition sum_swap (A B : Set) (s : sum A B) : sum B A := sum_elim A B (sum B A) (inr B A) (inl B A) s.
Theorem sum_swap_involutive : forall (A B : Set) (s : sum A B), ((sum_swap B A (sum_swap A B s)) = s) :=
    fun A B s => match s as t return ((sum_swap B A (sum_swap A B t)) = t) with
    | inl _ _ x => eq_refl (inl A B x) | inr _ _ y => eq_refl (inr A B y) end.
Theorem sum_swap_map : forall (A B C D : Set) (f : A -> C) (g : B -> D) (s : sum A B),
    ((sum_swap C D (sum_map A B C D f g s)) = (sum_map B A D C g f (sum_swap A B s))) :=
    fun A B C D f g s => match s as t return ((sum_swap C D (sum_map A B C D f g t)) = (sum_map B A D C g f (sum_swap A B t))) with
    | inl _ _ x => eq_refl (inr D C (f x)) | inr _ _ y => eq_refl (inl D C (g y)) end.
Definition sum_assoc (A B C : Set) (s : sum (sum A B) C) : sum A (sum B C) :=
    match s with | inl _ _ t => match t with | inl _ _ a => inl A (sum B C) a | inr _ _ b => inr A (sum B C) (inl B C b) end
    | inr _ _ c => inr A (sum B C) (inr B C c) end.
Definition sum_unassoc (A B C : Set) (s : sum A (sum B C)) : sum (sum A B) C :=
    match s with | inl _ _ a => inl (sum A B) C (inl A B a)
    | inr _ _ t => match t with | inl _ _ b => inl (sum A B) C (inr A B b) | inr _ _ c => inr (sum A B) C c end end.
Theorem sum_assoc_inverse : forall (A B C : Set) (s : sum (sum A B) C), ((sum_unassoc A B C (sum_assoc A B C s)) = s) :=
    fun A B C s => match s as t return ((sum_unassoc A B C (sum_assoc A B C t)) = t) with
    | inl _ _ u => match u as v return ((sum_unassoc A B C (sum_assoc A B C (inl (sum A B) C v))) = (inl (sum A B) C v)) with
        | inl _ _ a => eq_refl (inl (sum A B) C (inl A B a)) | inr _ _ b => eq_refl (inl (sum A B) C (inr A B b)) end
    | inr _ _ c => eq_refl (inr (sum A B) C c) end.
Theorem sum_unassoc_inverse : forall (A B C : Set) (s : sum A (sum B C)), ((sum_assoc A B C (sum_unassoc A B C s)) = s) :=
    fun A B C s => match s as t return ((sum_assoc A B C (sum_unassoc A B C t)) = t) with
    | inl _ _ a => eq_refl (inl A (sum B C) a)
    | inr _ _ u => match u as v return ((sum_assoc A B C (sum_unassoc A B C (inr A (sum B C) v))) = (inr A (sum B C) v)) with
        | inl _ _ b => eq_refl (inr A (sum B C) (inl B C b)) | inr _ _ c => eq_refl (inr A (sum B C) (inr B C c)) end
    end.
Definition sum_eq_dec (A B : Set) (da : equality_decision A) (db : equality_decision B) : equality_decision (sum A B) :=
    fun p q => match p as a return Decidable (a = q) with
    | inl _ _ x => match q as b return Decidable ((inl A B x) = b) with
        | inl _ _ y => match da x y with
            | yes _ _ e => yes ((inl A B x) = (inl A B y)) (not ((inl A B x) = (inl A B y))) (f_equal (inl A B) x y e)
            | no _ _ e => no ((inl A B x) = (inl A B y)) (not ((inl A B x) = (inl A B y))) (fun h => e (inl_injective A B x y h)) end
        | inr _ _ y => no ((inl A B x) = (inr A B y)) (not ((inl A B x) = (inr A B y))) (inl_not_inr A B x y) end
    | inr _ _ x => match q as b return Decidable ((inr A B x) = b) with
        | inl _ _ y => no ((inr A B x) = (inl A B y)) (not ((inr A B x) = (inl A B y))) (inr_not_inl A B y x)
        | inr _ _ y => match db x y with
            | yes _ _ e => yes ((inr A B x) = (inr A B y)) (not ((inr A B x) = (inr A B y))) (f_equal (inr A B) x y e)
            | no _ _ e => no ((inr A B x) = (inr A B y)) (not ((inr A B x) = (inr A B y))) (fun h => e (inr_injective A B x y h)) end
        end
    end.
Definition sum_bind (E A B : Set) (s : sum E A) (f : A -> sum E B) : sum E B :=
    match s with | inl _ _ e => inl E B e | inr _ _ a => f a end.
Theorem sum_bind_left_unit : forall (E A B : Set) (x : A) (f : A -> sum E B), ((sum_bind E A B (inr E A x) f) = (f x)) :=
    fun E A B x f => eq_refl (f x).
Theorem sum_bind_right_unit : forall (E A : Set) (s : sum E A), ((sum_bind E A A s (inr E A)) = s) :=
    fun E A s => match s as t return ((sum_bind E A A t (inr E A)) = t) with
    | inl _ _ e => eq_refl (inl E A e) | inr _ _ a => eq_refl (inr E A a) end.
Theorem sum_bind_assoc : forall (E A B C : Set) (s : sum E A) (f : A -> sum E B) (g : B -> sum E C),
    ((sum_bind E B C (sum_bind E A B s f) g) = (sum_bind E A C s (fun a => sum_bind E B C (f a) g))) :=
    fun E A B C s f g => match s as t return ((sum_bind E B C (sum_bind E A B t f) g) = (sum_bind E A C t (fun a => sum_bind E B C (f a) g))) with
    | inl _ _ e => eq_refl (inl E C e) | inr _ _ a => eq_refl (sum_bind E B C (f a) g) end.
Theorem sum_bind_ext : forall (E A B : Set) (s : sum E A) (f g : A -> sum E B),
    (forall x : A, ((f x) = (g x))) -> ((sum_bind E A B s f) = (sum_bind E A B s g)) :=
    fun E A B s f g h => match s as t return ((sum_bind E A B t f) = (sum_bind E A B t g)) with
    | inl _ _ e => eq_refl (inl E B e) | inr _ _ a => h a end.
Theorem sum_bind_map : forall (E A B C : Set) (s : sum E A) (f : A -> B) (g : B -> sum E C),
    ((sum_bind E B C (sum_map E A E B (fun e => e) f s) g) = (sum_bind E A C s (fun a => g (f a)))) :=
    fun E A B C s f g => match s as t return ((sum_bind E B C (sum_map E A E B (fun e => e) f t) g) = (sum_bind E A C t (fun a => g (f a)))) with
    | inl _ _ e => eq_refl (inl E C e) | inr _ _ a => eq_refl (g (f a)) end.
Theorem sum_right_map : forall (A B C D : Set) (f : A -> C) (g : B -> D) (s : sum A B),
    ((sum_right C D (sum_map A B C D f g s)) = (option_map B D g (sum_right A B s))) :=
    fun A B C D f g s => match s as t return ((sum_right C D (sum_map A B C D f g t)) = (option_map B D g (sum_right A B t))) with
    | inl _ _ x => eq_refl (None D) | inr _ _ y => eq_refl (Some D (g y)) end.
Theorem sum_right_bind : forall (E A B : Set) (s : sum E A) (f : A -> sum E B),
    ((sum_right E B (sum_bind E A B s f)) = (option_bind A B (sum_right E A s) (fun a => sum_right E B (f a)))) :=
    fun E A B s f => match s as t return ((sum_right E B (sum_bind E A B t f)) = (option_bind A B (sum_right E A t) (fun a => sum_right E B (f a)))) with
    | inl _ _ e => eq_refl (None B) | inr _ _ a => eq_refl (sum_right E B (f a)) end.
