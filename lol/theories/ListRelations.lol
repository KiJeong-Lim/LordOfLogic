(* List predicates and permutations used by sorting specifications. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.List.

Fixpoint Forall {A : Set} (P : A -> Prop) (l : list A) : Prop :=
    match l with | nil _ => True | cons x t => and (P x) (Forall P t) end.
Fixpoint Exists {A : Set} (P : A -> Prop) (l : list A) : Prop :=
    match l with | nil _ => False | cons x t => or (P x) (Exists P t) end.
Definition In {A : Set} (x : A) (l : list A) : Prop := Exists (fun y => (x = y)) l.

Theorem Forall_head : forall (A : Set) (P : A -> Prop) (x : A) (l : list A), Forall P (cons x l) -> P x :=
    fun A P x l h => and_left (P x) (Forall P l) h.
Theorem Forall_tail : forall (A : Set) (P : A -> Prop) (x : A) (l : list A), Forall P (cons x l) -> Forall P l :=
    fun A P x l h => and_right (P x) (Forall P l) h.
Theorem Forall_impl : forall (A : Set) (P Q : A -> Prop), (forall x : A, P x -> Q x) -> forall l : list A, Forall P l -> Forall Q l :=
    fun A P Q f => fix go (l : list A) {struct l} : Forall P l -> Forall Q l :=
        match l as xs return Forall P xs -> Forall Q xs with
        | nil _ => fun h => I
        | cons x t => fun h => conj (Q x) (Forall Q t) (f x (Forall_head A P x t h)) (go t (Forall_tail A P x t h))
        end.
Theorem Forall_app_left : forall (A : Set) (P : A -> Prop) (l m : list A), Forall P (app l m) -> Forall P l :=
    fun A P => fix go (l : list A) {struct l} : forall m : list A, Forall P (app l m) -> Forall P l :=
        match l as xs return forall m : list A, Forall P (app xs m) -> Forall P xs with
        | nil _ => fun m h => I
        | cons x t => fun m h => conj (P x) (Forall P t) (Forall_head A P x (app t m) h) (go t m (Forall_tail A P x (app t m) h))
        end.
Theorem Forall_app_right : forall (A : Set) (P : A -> Prop) (l m : list A), Forall P (app l m) -> Forall P m :=
    fun A P => fix go (l : list A) {struct l} : forall m : list A, Forall P (app l m) -> Forall P m :=
        match l as xs return forall m : list A, Forall P (app xs m) -> Forall P m with
        | nil _ => fun m h => h
        | cons x t => fun m h => go t m (Forall_tail A P x (app t m) h)
        end.
Theorem Forall_app_join : forall (A : Set) (P : A -> Prop) (l m : list A), Forall P l -> Forall P m -> Forall P (app l m) :=
    fun A P => fix go (l : list A) {struct l} : forall m : list A, Forall P l -> Forall P m -> Forall P (app l m) :=
        match l as xs return forall m : list A, Forall P xs -> Forall P m -> Forall P (app xs m) with
        | nil _ => fun m h k => k
        | cons x t => fun m h k => conj (P x) (Forall P (app t m)) (Forall_head A P x t h) (go t m (Forall_tail A P x t h) k)
        end.
Theorem Forall_app : forall (A : Set) (P : A -> Prop) (l m : list A), iff (Forall P (app l m)) (and (Forall P l) (Forall P m)) :=
    fun A P l m => conj (Forall P (app l m) -> and (Forall P l) (Forall P m)) (and (Forall P l) (Forall P m) -> Forall P (app l m))
        (fun h => conj (Forall P l) (Forall P m) (Forall_app_left A P l m h) (Forall_app_right A P l m h))
        (fun h => Forall_app_join A P l m (and_left (Forall P l) (Forall P m) h) (and_right (Forall P l) (Forall P m) h)).
Theorem Forall_map : forall (A B : Set) (f : A -> B) (P : B -> Prop) (l : list A), Forall (fun x => P (f x)) l -> Forall P (map f l) :=
    fun A B f P => fix go (l : list A) {struct l} : Forall (fun x => P (f x)) l -> Forall P (map f l) :=
        match l as xs return Forall (fun x => P (f x)) xs -> Forall P (map f xs) with
        | nil _ => fun h => I
        | cons x t => fun h => conj (P (f x)) (Forall P (map f t)) (Forall_head A (fun y => P (f y)) x t h) (go t (Forall_tail A (fun y => P (f y)) x t h))
        end.
Theorem Exists_impl : forall (A : Set) (P Q : A -> Prop), (forall x : A, P x -> Q x) -> forall l : list A, Exists P l -> Exists Q l :=
    fun A P Q f => fix go (l : list A) {struct l} : Exists P l -> Exists Q l :=
        match l as xs return Exists P xs -> Exists Q xs with
        | nil _ => fun h => h
        | cons x t => fun h => or_elim (P x) (Exists P t) (Exists Q (cons x t))
            (fun p => or_introl (Q x) (Exists Q t) (f x p))
            (fun p => or_intror (Q x) (Exists Q t) (go t p)) h
        end.
Theorem Exists_app_left : forall (A : Set) (P : A -> Prop) (l m : list A), Exists P l -> Exists P (app l m) :=
    fun A P => fix go (l : list A) {struct l} : forall m : list A, Exists P l -> Exists P (app l m) :=
        match l as xs return forall m : list A, Exists P xs -> Exists P (app xs m) with
        | nil _ => fun m h => False_rect (Exists P m) h
        | cons x t => fun m h => or_elim (P x) (Exists P t) (Exists P (cons x (app t m)))
            (fun p => or_introl (P x) (Exists P (app t m)) p)
            (fun p => or_intror (P x) (Exists P (app t m)) (go t m p)) h
        end.
Theorem Exists_app_right : forall (A : Set) (P : A -> Prop) (l m : list A), Exists P m -> Exists P (app l m) :=
    fun A P => fix go (l : list A) {struct l} : forall m : list A, Exists P m -> Exists P (app l m) :=
        match l as xs return forall m : list A, Exists P m -> Exists P (app xs m) with
        | nil _ => fun m h => h
        | cons x t => fun m h => or_intror (P x) (Exists P (app t m)) (go t m h)
        end.
Theorem Exists_app_split : forall (A : Set) (P : A -> Prop) (l m : list A), Exists P (app l m) -> or (Exists P l) (Exists P m) :=
    fun A P => fix go (l : list A) {struct l} : forall m : list A, Exists P (app l m) -> or (Exists P l) (Exists P m) :=
        match l as xs return forall m : list A, Exists P (app xs m) -> or (Exists P xs) (Exists P m) with
        | nil _ => fun m h => or_intror False (Exists P m) h
        | cons x t => fun m h => or_elim (P x) (Exists P (app t m)) (or (Exists P (cons x t)) (Exists P m))
            (fun p => or_introl (Exists P (cons x t)) (Exists P m) (or_introl (P x) (Exists P t) p))
            (fun p => or_elim (Exists P t) (Exists P m) (or (Exists P (cons x t)) (Exists P m))
                (fun q => or_introl (Exists P (cons x t)) (Exists P m) (or_intror (P x) (Exists P t) q))
                (fun q => or_intror (Exists P (cons x t)) (Exists P m) q) (go t m p)) h
        end.
Theorem In_head : forall (A : Set) (x : A) (l : list A), In x (cons x l) :=
    fun A x l => or_introl (x = x) (In x l) (eq_refl x).
Theorem In_tail : forall (A : Set) (x y : A) (l : list A), In x l -> In x (cons y l) :=
    fun A x y l h => or_intror (x = y) (In x l) h.
Theorem In_app_left : forall (A : Set) (x : A) (l m : list A), In x l -> In x (app l m) :=
    fun A x l m => Exists_app_left A (fun y => (x = y)) l m.
Theorem In_app_right : forall (A : Set) (x : A) (l m : list A), In x m -> In x (app l m) :=
    fun A x l m => Exists_app_right A (fun y => (x = y)) l m.
Theorem In_app_split : forall (A : Set) (x : A) (l m : list A), In x (app l m) -> or (In x l) (In x m) :=
    fun A x l m => Exists_app_split A (fun y => (x = y)) l m.

Inductive Permutation (A : Set) : list A -> list A -> Prop :=
    | perm_nil : Permutation A (nil A) (nil A)
    | perm_skip : forall (x : A) (l m : list A), Permutation A l m -> Permutation A (cons x l) (cons x m)
    | perm_swap : forall (x y : A) (l : list A), Permutation A (cons y (cons x l)) (cons x (cons y l))
    | perm_trans : forall (l m n : list A), Permutation A l m -> Permutation A m n -> Permutation A l n.
Arguments Permutation {A} l m.
Arguments perm_nil {A}.
Arguments perm_skip {A} x l m p.
Arguments perm_swap {A} x y l.
Arguments perm_trans {A} l m n p q.
Theorem Permutation_refl : forall (A : Set) (l : list A), Permutation l l :=
    fun A => fix go (l : list A) {struct l} : Permutation l l :=
        match l as xs return Permutation xs xs with
        | nil _ => @perm_nil A
        | cons x t => perm_skip x t t (go t)
        end.
Theorem Permutation_sym : forall (A : Set) (l m : list A), Permutation l m -> Permutation m l :=
    fun A => fix go (l m : list A) (h : Permutation l m) {struct h} : Permutation m l :=
        match h in Permutation xs ys return Permutation ys xs with
        | perm_nil => @perm_nil A
        | perm_skip x xs ys p => perm_skip x ys xs (go xs ys p)
        | perm_swap x y xs => perm_swap y x xs
        | perm_trans xs ys zs p q => perm_trans zs ys xs (go ys zs q) (go xs ys p)
        end.
Theorem Permutation_length : forall (A : Set) (l m : list A), Permutation l m -> ((length l) = (length m)) :=
    fun A => fix go (l m : list A) (h : Permutation l m) {struct h} : ((length l) = (length m)) :=
        match h in Permutation xs ys return ((length xs) = (length ys)) with
        | perm_nil => eq_refl O
        | perm_skip x xs ys p => f_equal S (length xs) (length ys) (go xs ys p)
        | perm_swap x y xs => eq_refl (S (S (length xs)))
        | perm_trans xs ys zs p q => eq_trans (length xs) (length ys) (length zs) (go xs ys p) (go ys zs q)
        end.
Theorem Permutation_map : forall (A B : Set) (f : A -> B) (l m : list A), Permutation l m -> Permutation (map f l) (map f m) :=
    fun A B f => fix go (l m : list A) (h : Permutation l m) {struct h} : Permutation (map f l) (map f m) :=
        match h in Permutation xs ys return Permutation (map f xs) (map f ys) with
        | perm_nil => @perm_nil B
        | perm_skip x xs ys p => perm_skip (f x) (map f xs) (map f ys) (go xs ys p)
        | perm_swap x y xs => perm_swap (f x) (f y) (map f xs)
        | perm_trans xs ys zs p q => perm_trans (map f xs) (map f ys) (map f zs) (go xs ys p) (go ys zs q)
        end.
Theorem Permutation_Forall : forall (A : Set) (P : A -> Prop) (l m : list A), Permutation l m -> Forall P l -> Forall P m :=
    fun A P => fix go (l m : list A) (h : Permutation l m) {struct h} : Forall P l -> Forall P m :=
        match h in Permutation xs ys return Forall P xs -> Forall P ys with
        | perm_nil => fun p => p
        | perm_skip x xs ys q => fun p => conj (P x) (Forall P ys) (Forall_head A P x xs p) (go xs ys q (Forall_tail A P x xs p))
        | perm_swap x y xs => fun p => conj (P x) (Forall P (cons y xs))
            (Forall_head A P x xs (Forall_tail A P y (cons x xs) p))
            (conj (P y) (Forall P xs) (Forall_head A P y (cons x xs) p) (Forall_tail A P x xs (Forall_tail A P y (cons x xs) p)))
        | perm_trans xs ys zs p q => fun h => go ys zs q (go xs ys p h)
        end.
Theorem Permutation_app_right : forall (A : Set) (l m : list A), Permutation l m -> forall r : list A, Permutation (app l r) (app m r) :=
    fun A => fix go (l m : list A) (h : Permutation l m) {struct h} : forall r : list A, Permutation (app l r) (app m r) :=
        match h in Permutation xs ys return forall r : list A, Permutation (app xs r) (app ys r) with
        | perm_nil => fun r => Permutation_refl A r
        | perm_skip x xs ys p => fun r => perm_skip x (app xs r) (app ys r) (go xs ys p r)
        | perm_swap x y xs => fun r => perm_swap x y (app xs r)
        | perm_trans xs ys zs p q => fun r => perm_trans (app xs r) (app ys r) (app zs r) (go xs ys p r) (go ys zs q r)
        end.
Theorem Permutation_app_left : forall (A : Set) (l m : list A), Permutation l m -> forall r : list A, Permutation (app r l) (app r m) :=
    fun A l m h => fix go (r : list A) {struct r} : Permutation (app r l) (app r m) :=
        match r as xs return Permutation (app xs l) (app xs m) with
        | nil _ => h
        | cons x t => perm_skip x (app t l) (app t m) (go t)
        end.
Theorem Permutation_app : forall (A : Set) (l m r s : list A), Permutation l m -> Permutation r s -> Permutation (app l r) (app m s) :=
    fun A l m r s h k => perm_trans (app l r) (app m r) (app m s) (Permutation_app_right A l m h r) (Permutation_app_left A r s k m).
Theorem Forall_In : forall (A : Set) (P : A -> Prop) (l : list A), Forall P l -> forall x : A, In x l -> P x :=
    fun A P => fix go (l : list A) {struct l} : Forall P l -> forall x : A, In x l -> P x :=
        match l as xs return Forall P xs -> forall x : A, In x xs -> P x with
        | nil _ => fun h x e => False_rect (P x) e
        | cons y t => fun h x e => or_elim (x = y) (In x t) (P x)
            (fun q => eq_transport A P y x (eq_sym x y q) (Forall_head A P y t h))
            (fun q => go t (Forall_tail A P y t h) x q) e
        end.
Theorem Forall_of_In : forall (A : Set) (P : A -> Prop) (l : list A), (forall x : A, In x l -> P x) -> Forall P l :=
    fun A P => fix go (l : list A) {struct l} : (forall x : A, In x l -> P x) -> Forall P l :=
        match l as xs return (forall x : A, In x xs -> P x) -> Forall P xs with
        | nil _ => fun h => I
        | cons x t => fun h => conj (P x) (Forall P t) (h x (In_head A x t)) (go t (fun y e => h y (In_tail A y x t e)))
        end.
Theorem In_map : forall (A B : Set) (f : A -> B) (x : A) (l : list A), In x l -> In (f x) (map f l) :=
    fun A B f x => fix go (l : list A) {struct l} : In x l -> In (f x) (map f l) :=
        match l as xs return In x xs -> In (f x) (map f xs) with
        | nil _ => fun h => h
        | cons y t => fun h => or_elim (x = y) (In x t) (In (f x) (cons (f y) (map f t)))
            (fun e => or_introl ((f x) = (f y)) (In (f x) (map f t)) (f_equal f x y e))
            (fun e => In_tail B (f x) (f y) (map f t) (go t e)) h
        end.
Theorem Permutation_Exists : forall (A : Set) (P : A -> Prop) (l m : list A), Permutation l m -> Exists P l -> Exists P m :=
    fun A P => fix go (l m : list A) (h : Permutation l m) {struct h} : Exists P l -> Exists P m :=
        match h in Permutation xs ys return Exists P xs -> Exists P ys with
        | perm_nil => fun p => p
        | perm_skip x xs ys q => fun p => or_elim (P x) (Exists P xs) (Exists P (cons x ys))
            (fun e => or_introl (P x) (Exists P ys) e)
            (fun e => or_intror (P x) (Exists P ys) (go xs ys q e)) p
        | perm_swap x y xs => fun p => or_elim (P y) (Exists P (cons x xs)) (Exists P (cons x (cons y xs)))
            (fun e => or_intror (P x) (Exists P (cons y xs)) (or_introl (P y) (Exists P xs) e))
            (fun e => or_elim (P x) (Exists P xs) (Exists P (cons x (cons y xs)))
                (fun q => or_introl (P x) (Exists P (cons y xs)) q)
                (fun q => or_intror (P x) (Exists P (cons y xs)) (or_intror (P y) (Exists P xs) q)) e) p
        | perm_trans xs ys zs p q => fun h => go ys zs q (go xs ys p h)
        end.
Theorem Permutation_In : forall (A : Set) (x : A) (l m : list A), Permutation l m -> In x l -> In x m :=
    fun A x l m => Permutation_Exists A (fun y => (x = y)) l m.
Theorem Permutation_middle : forall (A : Set) (x : A) (l r : list A), Permutation (cons x (app l r)) (app l (cons x r)) :=
    fun A x => fix go (l : list A) {struct l} : forall r : list A, Permutation (cons x (app l r)) (app l (cons x r)) :=
        match l as xs return forall r : list A, Permutation (cons x (app xs r)) (app xs (cons x r)) with
        | nil _ => fun r => Permutation_refl A (cons x r)
        | cons y t => fun r => perm_trans (cons x (cons y (app t r))) (cons y (cons x (app t r))) (cons y (app t (cons x r)))
            (perm_swap y x (app t r)) (perm_skip y (cons x (app t r)) (app t (cons x r)) (go t r))
        end.
Theorem Permutation_app_comm : forall (A : Set) (l m : list A), Permutation (app l m) (app m l) :=
    fun A => fix go (l : list A) {struct l} : forall m : list A, Permutation (app l m) (app m l) :=
        match l as xs return forall m : list A, Permutation (app xs m) (app m xs) with
        | nil _ => fun m => eq_transport (list A) (fun ys => Permutation m ys) m (app m (nil A)) (eq_sym (app m (nil A)) m (app_nil_right A m)) (Permutation_refl A m)
        | cons x t => fun m => perm_trans (cons x (app t m)) (cons x (app m t)) (app m (cons x t))
            (perm_skip x (app t m) (app m t) (go t m)) (Permutation_middle A x m t)
        end.
Theorem Permutation_rev : forall (A : Set) (l : list A), Permutation l (rev l) :=
    fun A => fix go (l : list A) {struct l} : Permutation l (rev l) :=
        match l as xs return Permutation xs (rev xs) with
        | nil _ => @perm_nil A
        | cons x t => perm_trans (cons x t) (cons x (rev t)) (app (rev t) (singleton x))
            (perm_skip x t (rev t) (go t)) (Permutation_app_comm A (singleton x) (rev t))
        end.
