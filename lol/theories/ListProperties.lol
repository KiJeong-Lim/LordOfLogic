(* Structural list laws used by permutation and sorting proofs. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.List.
Theorem cons_injective_head : forall (A : Set) (x y : A) (l m : list A), ((cons x l) = (cons y m)) -> (x = y) :=
    fun A x y l m e => f_equal (hd x) (cons x l) (cons y m) e.
Theorem cons_injective_tail : forall (A : Set) (x y : A) (l m : list A), ((cons x l) = (cons y m)) -> (l = m) :=
    fun A x y l m e => f_equal (tail) (cons x l) (cons y m) e.
Theorem map_comp : forall (A B C : Set) (f : B -> C) (g : A -> B) (l : list A), ((map f (map g l)) = (map (fun x => f (g x)) l)) :=
    fun A B C f g => fix go (l : list A) {struct l} : ((map f (map g l)) = (map (fun x => f (g x)) l)) :=
        match l as xs return ((map f (map g xs)) = (map (fun x => f (g x)) xs)) with
        | nil _ => eq_refl (nil C)
        | cons x t => f_equal (cons (f (g x))) (map f (map g t)) (map (fun y => f (g y)) t) (go t)
        end.
Theorem map_app : forall (A B : Set) (f : A -> B) (l m : list A), ((map f (app l m)) = (app (map f l) (map f m))) :=
    fun A B f => fix go (l m : list A) {struct l} : ((map f (app l m)) = (app (map f l) (map f m))) :=
        match l as xs return ((map f (app xs m)) = (app (map f xs) (map f m))) with
        | nil _ => eq_refl (map f m)
        | cons x t => f_equal (cons (f x)) (map f (app t m)) (app (map f t) (map f m)) (go t m)
        end.
Theorem rev_app : forall (A : Set) (l m : list A), ((rev (app l m)) = (app (rev m) (rev l))) :=
    fun A => fix go (l m : list A) {struct l} : ((rev (app l m)) = (app (rev m) (rev l))) :=
        match l as xs return ((rev (app xs m)) = (app (rev m) (rev xs))) with
        | nil _ => eq_sym (app (rev m) (nil A)) (rev m) (app_nil_right A (rev m))
        | cons x t => eq_trans (app (rev (app t m)) (singleton x)) (app (app (rev m) (rev t)) (singleton x)) (app (rev m) (app (rev t) (singleton x))) (f_equal (fun ys => app ys (singleton x)) (rev (app t m)) (app (rev m) (rev t)) (go t m)) (app_assoc A (rev m) (rev t) (singleton x))
        end.
Theorem rev_involutive : forall (A : Set) (l : list A), ((rev (rev l)) = l) :=
    fun A => fix go (l : list A) {struct l} : ((rev (rev l)) = l) :=
        match l as xs return ((rev (rev xs)) = xs) with
        | nil _ => eq_refl (nil A)
        | cons x t => eq_trans (rev (app (rev t) (singleton x))) (cons x (rev (rev t))) (cons x t) (rev_app A (rev t) (singleton x)) (f_equal (cons x) (rev (rev t)) t (go t))
        end.
Theorem rev_injective : forall (A : Set) (l m : list A), ((rev l) = (rev m)) -> (l = m) :=
    fun A l m e => eq_trans l (rev (rev l)) m (eq_sym (rev (rev l)) l (rev_involutive A l)) (eq_trans (rev (rev l)) (rev (rev m)) m (f_equal (rev) (rev l) (rev m) e) (rev_involutive A m)).
Theorem map_rev : forall (A B : Set) (f : A -> B) (l : list A), ((map f (rev l)) = (rev (map f l))) :=
    fun A B f => fix go (l : list A) {struct l} : ((map f (rev l)) = (rev (map f l))) :=
        match l as xs return ((map f (rev xs)) = (rev (map f xs))) with
        | nil _ => eq_refl (nil B)
        | cons x t => eq_trans (map f (app (rev t) (singleton x))) (app (map f (rev t)) (singleton (f x))) (app (rev (map f t)) (singleton (f x))) (map_app A B f (rev t) (singleton x)) (f_equal (fun ys => app ys (singleton (f x))) (map f (rev t)) (rev (map f t)) (go t))
        end.
Theorem length_rev : forall (A : Set) (l : list A), ((length (rev l)) = (length l)) :=
    fun A => fix go (l : list A) {struct l} : ((length (rev l)) = (length l)) :=
        match l as xs return ((length (rev xs)) = (length xs)) with
        | nil _ => eq_refl O
        | cons x t => eq_trans (length (app (rev t) (singleton x))) (add (length (rev t)) one) (S (length t)) (length_app A (rev t) (singleton x)) (eq_trans (add (length (rev t)) one) (S (length (rev t))) (S (length t)) (add_one_right (length (rev t))) (f_equal S (length (rev t)) (length t) (go t)))
        end.
Theorem fold_right_app : forall (A B : Set) (f : A -> B -> B) (z : B) (l m : list A), ((fold_right f z (app l m)) = (fold_right f (fold_right f z m) l)) :=
    fun A B f z => fix go (l m : list A) {struct l} : ((fold_right f z (app l m)) = (fold_right f (fold_right f z m) l)) :=
        match l as xs return ((fold_right f z (app xs m)) = (fold_right f (fold_right f z m) xs)) with
        | nil _ => eq_refl (fold_right f z m)
        | cons x t => f_equal (f x) (fold_right f z (app t m)) (fold_right f (fold_right f z m) t) (go t m)
        end.
Theorem fold_right_map : forall (A B C : Set) (f : B -> C -> C) (g : A -> B) (z : C) (l : list A), ((fold_right f z (map g l)) = (fold_right (fun x y => f (g x) y) z l)) :=
    fun A B C f g z => fix go (l : list A) {struct l} : ((fold_right f z (map g l)) = (fold_right (fun x y => f (g x) y) z l)) :=
        match l as xs return ((fold_right f z (map g xs)) = (fold_right (fun x y => f (g x) y) z xs)) with
        | nil _ => eq_refl z
        | cons x t => f_equal (f (g x)) (fold_right f z (map g t)) (fold_right (fun y acc => f (g y) acc) z t) (go t)
        end.
Theorem concat_app : forall (A : Set) (l m : list (list A)), ((concat (app l m)) = (app (concat l) (concat m))) :=
    fun A => fix go (l m : list (list A)) {struct l} : ((concat (app l m)) = (app (concat l) (concat m))) :=
        match l as xs return ((concat (app xs m)) = (app (concat xs) (concat m))) with
        | nil _ => eq_refl (concat m)
        | cons x t => eq_trans (app x (concat (app t m))) (app x (app (concat t) (concat m))) (app (app x (concat t)) (concat m)) (f_equal (app x) (concat (app t m)) (app (concat t) (concat m)) (go t m)) (eq_sym (app (app x (concat t)) (concat m)) (app x (app (concat t) (concat m))) (app_assoc A x (concat t) (concat m)))
        end.
Theorem flat_map_app : forall (A B : Set) (f : A -> list B) (l m : list A), ((flat_map f (app l m)) = (app (flat_map f l) (flat_map f m))) :=
    fun A B f l m => eq_trans (concat (map f (app l m))) (concat (app (map f l) (map f m))) (app (concat (map f l)) (concat (map f m))) (f_equal (concat) (map f (app l m)) (app (map f l) (map f m)) (map_app A (list B) f l m)) (concat_app B (map f l) (map f m)).
Theorem length_repeat : forall (A : Set) (x : A) (n : nat), ((length (repeat x n)) = n) :=
    fun A x => fix go (n : nat) {struct n} : ((length (repeat x n)) = n) :=
        match n as k return ((length (repeat x k)) = k) with
        | O => eq_refl O
        | S p => f_equal S (length (repeat x p)) p (go p)
        end.
Theorem take_app_length : forall (A : Set) (l m : list A), ((take (length l) (app l m)) = l) :=
    fun A => fix go (l m : list A) {struct l} : ((take (length l) (app l m)) = l) :=
        match l as xs return ((take (length xs) (app xs m)) = xs) with
        | nil _ => eq_refl (nil A)
        | cons x t => f_equal (cons x) (take (length t) (app t m)) t (go t m)
        end.
Theorem drop_app_length : forall (A : Set) (l m : list A), ((drop (length l) (app l m)) = m) :=
    fun A => fix go (l m : list A) {struct l} : ((drop (length l) (app l m)) = m) :=
        match l as xs return ((drop (length xs) (app xs m)) = m) with
        | nil _ => eq_refl m
        | cons x t => go t m
        end.
Theorem take_drop_app : forall (A : Set) (n : nat) (l : list A), ((app (take n l) (drop n l)) = l) :=
    fun A => fix go (n : nat) {struct n} : forall l : list A, ((app (take n l) (drop n l)) = l) :=
        match n as k return forall l : list A, ((app (take k l) (drop k l)) = l) with
        | O => fun l => eq_refl l
        | S p => fun l => match l as xs return ((app (take (S p) xs) (drop (S p) xs)) = xs) with
            | nil _ => eq_refl (nil A)
            | cons x t => f_equal (cons x) (app (take p t) (drop p t)) t (go p t)
            end
        end.
Theorem app_cancel_left : forall (A : Set) (l m n : list A), ((app l m) = (app l n)) -> (m = n) :=
    fun A => fix go (l : list A) {struct l} : forall m n : list A, ((app l m) = (app l n)) -> (m = n) :=
        match l as xs return forall m n : list A, ((app xs m) = (app xs n)) -> (m = n) with
        | nil _ => fun m n e => e
        | cons x t => fun m n e => go t m n (cons_injective_tail A x x (app t m) (app t n) e)
        end.
Theorem app_cancel_right : forall (A : Set) (l m n : list A), ((app l n) = (app m n)) -> (l = m) :=
    fun A l m n e => rev_injective A l m
        (app_cancel_left A (rev n) (rev l) (rev m)
            (eq_trans (app (rev n) (rev l)) (rev (app l n)) (app (rev n) (rev m))
                (eq_sym (rev (app l n)) (app (rev n) (rev l)) (rev_app A l n))
                (eq_trans (rev (app l n)) (rev (app m n)) (app (rev n) (rev m))
                    (f_equal (rev) (app l n) (app m n) e) (rev_app A m n)))).
Theorem app_eq_nil : forall (A : Set) (l m : list A), ((app l m) = (nil A)) -> and (l = (nil A)) (m = (nil A)) :=
    fun A l m => match l as xs return ((app xs m) = (nil A)) -> and (xs = (nil A)) (m = (nil A)) with
        | nil _ => fun e => conj ((nil A) = (nil A)) (m = (nil A)) (eq_refl (nil A)) e
        | cons x t => fun e => False_rect (and ((cons x t) = (nil A)) (m = (nil A)))
            (O_not_S (length (app t m)) (f_equal (length) (nil A) (cons x (app t m)) (eq_sym (cons x (app t m)) (nil A) e)))
        end.
Theorem length_zero_nil : forall (A : Set) (l : list A), ((length l) = O) -> (l = (nil A)) :=
    fun A l => match l as xs return ((length xs) = O) -> (xs = (nil A)) with
        | nil _ => fun e => eq_refl (nil A)
        | cons x t => fun e => False_rect ((cons x t) = (nil A)) (S_not_O (length t) e)
        end.
Theorem map_ext : forall (A B : Set) (f g : A -> B), (forall x : A, ((f x) = (g x))) -> forall l : list A, ((map f l) = (map g l)) :=
    fun A B f g h => fix go (l : list A) {struct l} : ((map f l) = (map g l)) :=
        match l as xs return ((map f xs) = (map g xs)) with
        | nil _ => eq_refl (nil B)
        | cons x t => eq_trans (cons (f x) (map f t)) (cons (g x) (map f t)) (cons (g x) (map g t))
            (f_equal (fun y => cons y (map f t)) (f x) (g x) (h x))
            (f_equal (cons (g x)) (map f t) (map g t) (go t))
        end.
Theorem fold_left_app : forall (A B : Set) (f : B -> A -> B) (l m : list A) (z : B), ((fold_left f z (app l m)) = (fold_left f (fold_left f z l) m)) :=
    fun A B f => fix go (l m : list A) (z : B) {struct l} : ((fold_left f z (app l m)) = (fold_left f (fold_left f z l) m)) :=
        match l as xs return ((fold_left f z (app xs m)) = (fold_left f (fold_left f z xs) m)) with
        | nil _ => eq_refl (fold_left f z m)
        | cons x t => go t m (f z x)
        end.
Theorem fold_left_rev_right : forall (A B : Set) (f : A -> B -> B) (l : list A) (z : B), ((fold_right f z (rev l)) = (fold_left (fun acc x => f x acc) z l)) :=
    fun A B f => fix go (l : list A) (z : B) {struct l} : ((fold_right f z (rev l)) = (fold_left (fun acc x => f x acc) z l)) :=
        match l as xs return ((fold_right f z (rev xs)) = (fold_left (fun acc x => f x acc) z xs)) with
        | nil _ => eq_refl z
        | cons x t => eq_trans (fold_right f z (app (rev t) (singleton x))) (fold_right f (f x z) (rev t)) (fold_left (fun acc y => f y acc) (f x z) t)
            (fold_right_app A B f z (rev t) (singleton x))
            (go t (f x z))
        end.
