(* Constructive list decisions and boolean reflection from supplied decisions. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Bool.
Import lol.theories.List.
Import lol.theories.ListProperties.
Import lol.theories.ListRelations.
Import lol.theories.Decidable.
Definition decision_bool (P : Prop) (d : Decidable P) : bool := match d with | yes _ _ h => true | no _ _ h => false end.
Theorem decision_bool_sound : forall (P : Prop) (d : Decidable P), Is_true (decision_bool P d) -> P := fun P d => match d as q return (Is_true (decision_bool P q) -> P) with | yes _ _ h => fun _ => h | no _ _ h => fun f => False_rect P f end.
Theorem decision_bool_complete : forall (P : Prop) (d : Decidable P), P -> Is_true (decision_bool P d) := fun P d => match d as q return (P -> Is_true (decision_bool P q)) with | yes _ _ h => fun _ => I | no _ _ h => h end.
Theorem decision_bool_reflect : forall (P : Prop) (d : Decidable P), iff (Is_true (decision_bool P d)) P := fun P d => conj (Is_true (decision_bool P d) -> P) (P -> Is_true (decision_bool P d)) (decision_bool_sound P d) (decision_bool_complete P d).
Theorem nil_not_cons : forall (A : Set) (x : A) (l : list A), not (((nil A) = (cons x l))) := fun A x l e => O_not_S (length l) (f_equal (length) (nil A) (cons x l) e).
Theorem cons_not_nil : forall (A : Set) (x : A) (l : list A), not (((cons x l) = (nil A))) := fun A x l e => nil_not_cons A x l (eq_sym (cons x l) (nil A) e).
Theorem cons_congruence : forall (A : Set) (x y : A) (l m : list A), (x = y) -> (l = m) -> ((cons x l) = (cons y m)) := fun A x y l m e f => eq_trans (cons x l) (cons y l) (cons y m) (f_equal (fun z => cons z l) x y e) (f_equal (cons y) l m f).
Definition list_eq_dec (A : Set) (d : equality_decision A) : equality_decision (list A) := fix go (l m : list A) {struct l} : Decidable (l = m) := match l as xs return Decidable (xs = m) with | nil _ => match m as ys return Decidable ((nil A) = ys) with | nil _ => yes (((nil A) = (nil A))) (not (((nil A) = (nil A)))) (eq_refl (nil A)) | cons y u => no (((nil A) = (cons y u))) (not (((nil A) = (cons y u)))) (nil_not_cons A y u) end | cons x t => match m as ys return Decidable ((cons x t) = ys) with | nil _ => no (((cons x t) = (nil A))) (not (((cons x t) = (nil A)))) (cons_not_nil A x t) | cons y u => match d x y with | yes _ _ xy => match go t u with | yes _ _ tu => yes (((cons x t) = (cons y u))) (not (((cons x t) = (cons y u)))) (cons_congruence A x y t u xy tu) | no _ _ tu => no (((cons x t) = (cons y u))) (not (((cons x t) = (cons y u)))) (fun e => tu (cons_injective_tail A x y t u e)) end | no _ _ xy => no (((cons x t) = (cons y u))) (not (((cons x t) = (cons y u)))) (fun e => xy (cons_injective_head A x y t u e)) end end end.
Definition list_eqb {A : Set} (d : equality_decision A) (l m : list A) : bool := decision_bool (l = m) (list_eq_dec A d l m).
Theorem list_eqb_sound : forall (A : Set) (d : equality_decision A) (l m : list A), Is_true (list_eqb d l m) -> (l = m) := fun A d l m => decision_bool_sound (l = m) (list_eq_dec A d l m).
Theorem list_eqb_complete : forall (A : Set) (d : equality_decision A) (l m : list A), (l = m) -> Is_true (list_eqb d l m) := fun A d l m => decision_bool_complete (l = m) (list_eq_dec A d l m).
Theorem list_eqb_reflect : forall (A : Set) (d : equality_decision A) (l m : list A), iff (Is_true (list_eqb d l m)) (l = m) := fun A d l m => decision_bool_reflect (l = m) (list_eq_dec A d l m).
Theorem list_eqb_refl : forall (A : Set) (d : equality_decision A) (l : list A), Is_true (list_eqb d l l) := fun A d l => list_eqb_complete A d l l (eq_refl l).
Theorem list_eqb_symmetric : forall (A : Set) (d : equality_decision A) (l m : list A), Is_true (list_eqb d l m) -> Is_true (list_eqb d m l) := fun A d l m h => list_eqb_complete A d m l (eq_sym l m (list_eqb_sound A d l m h)).
Theorem list_eqb_transitive : forall (A : Set) (d : equality_decision A) (l m n : list A), Is_true (list_eqb d l m) -> Is_true (list_eqb d m n) -> Is_true (list_eqb d l n) := fun A d l m n h k => list_eqb_complete A d l n (eq_trans l m n (list_eqb_sound A d l m h) (list_eqb_sound A d m n k)).
Definition In_dec (A : Set) (d : equality_decision A) (x : A) : forall l : list A, Decidable (In x l) := fix go (l : list A) {struct l} : Decidable (In x l) := match l as xs return Decidable (In x xs) with | nil _ => decide_false | cons y t => decide_or (x = y) (In x t) (d x y) (go t) end.
Definition Forall_dec (A : Set) (P : A -> Prop) (d : forall x : A, Decidable (P x)) : forall l : list A, Decidable (Forall P l) := fix go (l : list A) {struct l} : Decidable (Forall P l) := match l as xs return Decidable (Forall P xs) with | nil _ => decide_true | cons x t => decide_and (P x) (Forall P t) (d x) (go t) end.
Definition Exists_dec (A : Set) (P : A -> Prop) (d : forall x : A, Decidable (P x)) : forall l : list A, Decidable (Exists P l) := fix go (l : list A) {struct l} : Decidable (Exists P l) := match l as xs return Decidable (Exists P xs) with | nil _ => decide_false | cons x t => decide_or (P x) (Exists P t) (d x) (go t) end.
Definition mem_decision {A : Set} (d : equality_decision A) (x : A) (l : list A) : bool := decision_bool (In x l) (In_dec A d x l).
Theorem mem_decision_reflect : forall (A : Set) (d : equality_decision A) (x : A) (l : list A), iff (Is_true (mem_decision d x l)) (In x l) := fun A d x l => decision_bool_reflect (In x l) (In_dec A d x l).
Theorem mem_decision_head : forall (A : Set) (d : equality_decision A) (x : A) (l : list A), Is_true (mem_decision d x (cons x l)) := fun A d x l => decision_bool_complete (In x (cons x l)) (In_dec A d x (cons x l)) (In_head A x l).
Theorem mem_decision_tail : forall (A : Set) (d : equality_decision A) (x y : A) (l : list A), Is_true (mem_decision d x l) -> Is_true (mem_decision d x (cons y l)) := fun A d x y l h => decision_bool_complete (In x (cons y l)) (In_dec A d x (cons y l)) (In_tail A x y l (decision_bool_sound (In x l) (In_dec A d x l) h)).
Theorem mem_decision_app : forall (A : Set) (d : equality_decision A) (x : A) (l m : list A), iff (Is_true (mem_decision d x (app l m))) (or (In x l) (In x m)) := fun A d x l m => conj (Is_true (mem_decision d x (app l m)) -> or (In x l) (In x m)) (or (In x l) (In x m) -> Is_true (mem_decision d x (app l m))) (fun h => In_app_split A x l m (decision_bool_sound (In x (app l m)) (In_dec A d x (app l m)) h)) (fun h => decision_bool_complete (In x (app l m)) (In_dec A d x (app l m)) (or_elim (In x l) (In x m) (In x (app l m)) (In_app_left A x l m) (In_app_right A x l m) h)).
Definition all_decision {A : Set} (P : A -> Prop) (d : forall x : A, Decidable (P x)) (l : list A) : bool := decision_bool (Forall P l) (Forall_dec A P d l).
Definition any_decision {A : Set} (P : A -> Prop) (d : forall x : A, Decidable (P x)) (l : list A) : bool := decision_bool (Exists P l) (Exists_dec A P d l).
Theorem all_decision_reflect : forall (A : Set) (P : A -> Prop) (d : forall x : A, Decidable (P x)) (l : list A), iff (Is_true (all_decision P d l)) (Forall P l) := fun A P d l => decision_bool_reflect (Forall P l) (Forall_dec A P d l).
Theorem any_decision_reflect : forall (A : Set) (P : A -> Prop) (d : forall x : A, Decidable (P x)) (l : list A), iff (Is_true (any_decision P d l)) (Exists P l) := fun A P d l => decision_bool_reflect (Exists P l) (Exists_dec A P d l).
Theorem list_andb_reflect : forall a b : bool, iff (Is_true (andb a b)) (and (Is_true a) (Is_true b)) := fun a b => match a as q return iff (Is_true (andb q b)) (and (Is_true q) (Is_true b)) with | true => conj (Is_true b -> and True (Is_true b)) (and True (Is_true b) -> Is_true b) (fun h => conj True (Is_true b) I h) (and_right True (Is_true b)) | false => conj (False -> and False (Is_true b)) (and False (Is_true b) -> False) (fun h => False_rect (and False (Is_true b)) h) (and_left False (Is_true b)) end.
Theorem list_orb_reflect : forall a b : bool, iff (Is_true (orb a b)) (or (Is_true a) (Is_true b)) := fun a b => match a as q return iff (Is_true (orb q b)) (or (Is_true q) (Is_true b)) with | true => conj (True -> or True (Is_true b)) (or True (Is_true b) -> True) (fun h => or_introl True (Is_true b) I) (fun h => I) | false => conj (Is_true b -> or False (Is_true b)) (or False (Is_true b) -> Is_true b) (or_intror False (Is_true b)) (or_elim False (Is_true b) (Is_true b) (fun f => False_rect (Is_true b) f) (fun h => h)) end.
Theorem forallb_sound : forall (A : Set) (p : A -> bool) (l : list A), Is_true (forallb p l) -> Forall (fun x => Is_true (p x)) l := fun A p => fix go (l : list A) {struct l} : Is_true (forallb p l) -> Forall (fun x => Is_true (p x)) l := match l as xs return (Is_true (forallb p xs) -> Forall (fun x => Is_true (p x)) xs) with | nil _ => fun h => I | cons x t => fun h => match and_left (Is_true (andb (p x) (forallb p t)) -> and (Is_true (p x)) (Is_true (forallb p t))) (and (Is_true (p x)) (Is_true (forallb p t)) -> Is_true (andb (p x) (forallb p t))) (list_andb_reflect (p x) (forallb p t)) h return Forall (fun y => Is_true (p y)) (cons x t) with | conj _ _ a b => conj (Is_true (p x)) (Forall (fun y => Is_true (p y)) t) a (go t b) end end.
Theorem forallb_complete : forall (A : Set) (p : A -> bool) (l : list A), Forall (fun x => Is_true (p x)) l -> Is_true (forallb p l) := fun A p => fix go (l : list A) {struct l} : Forall (fun x => Is_true (p x)) l -> Is_true (forallb p l) := match l as xs return (Forall (fun x => Is_true (p x)) xs -> Is_true (forallb p xs)) with | nil _ => fun h => I | cons x t => fun h => and_right (Is_true (andb (p x) (forallb p t)) -> and (Is_true (p x)) (Is_true (forallb p t))) (and (Is_true (p x)) (Is_true (forallb p t)) -> Is_true (andb (p x) (forallb p t))) (list_andb_reflect (p x) (forallb p t)) (conj (Is_true (p x)) (Is_true (forallb p t)) (Forall_head A (fun y => Is_true (p y)) x t h) (go t (Forall_tail A (fun y => Is_true (p y)) x t h))) end.
Theorem forallb_reflect : forall (A : Set) (p : A -> bool) (l : list A), iff (Is_true (forallb p l)) (Forall (fun x => Is_true (p x)) l) := fun A p l => conj (Is_true (forallb p l) -> Forall (fun x => Is_true (p x)) l) (Forall (fun x => Is_true (p x)) l -> Is_true (forallb p l)) (forallb_sound A p l) (forallb_complete A p l).
Theorem existsb_sound : forall (A : Set) (p : A -> bool) (l : list A), Is_true (existsb p l) -> Exists (fun x => Is_true (p x)) l := fun A p => fix go (l : list A) {struct l} : Is_true (existsb p l) -> Exists (fun x => Is_true (p x)) l := match l as xs return (Is_true (existsb p xs) -> Exists (fun x => Is_true (p x)) xs) with | nil _ => fun h => h | cons x t => fun h => or_elim (Is_true (p x)) (Is_true (existsb p t)) (Exists (fun y => Is_true (p y)) (cons x t)) (or_introl (Is_true (p x)) (Exists (fun y => Is_true (p y)) t)) (fun k => or_intror (Is_true (p x)) (Exists (fun y => Is_true (p y)) t) (go t k)) (and_left (Is_true (orb (p x) (existsb p t)) -> or (Is_true (p x)) (Is_true (existsb p t))) (or (Is_true (p x)) (Is_true (existsb p t)) -> Is_true (orb (p x) (existsb p t))) (list_orb_reflect (p x) (existsb p t)) h) end.
Theorem existsb_complete : forall (A : Set) (p : A -> bool) (l : list A), Exists (fun x => Is_true (p x)) l -> Is_true (existsb p l) := fun A p => fix go (l : list A) {struct l} : Exists (fun x => Is_true (p x)) l -> Is_true (existsb p l) := match l as xs return (Exists (fun x => Is_true (p x)) xs -> Is_true (existsb p xs)) with | nil _ => fun h => h | cons x t => fun h => and_right (Is_true (orb (p x) (existsb p t)) -> or (Is_true (p x)) (Is_true (existsb p t))) (or (Is_true (p x)) (Is_true (existsb p t)) -> Is_true (orb (p x) (existsb p t))) (list_orb_reflect (p x) (existsb p t)) (or_elim (Is_true (p x)) (Exists (fun y => Is_true (p y)) t) (or (Is_true (p x)) (Is_true (existsb p t))) (or_introl (Is_true (p x)) (Is_true (existsb p t))) (fun k => or_intror (Is_true (p x)) (Is_true (existsb p t)) (go t k)) h) end.
Theorem existsb_reflect : forall (A : Set) (p : A -> bool) (l : list A), iff (Is_true (existsb p l)) (Exists (fun x => Is_true (p x)) l) := fun A p l => conj (Is_true (existsb p l) -> Exists (fun x => Is_true (p x)) l) (Exists (fun x => Is_true (p x)) l -> Is_true (existsb p l)) (existsb_sound A p l) (existsb_complete A p l).

(* Witnesses of the list quantifiers and of membership; no decision is needed for them. *)
Theorem Exists_of_In : forall (A : Set) (P : A -> Prop) (l : list A) (x : A), In x l -> P x -> Exists P l :=
    fun A P l x h p => Exists_impl A (fun y => (x = y)) P (fun y e => eq_transport A P x y e p) l h.
Theorem Exists_witness : forall (A : Set) (P : A -> Prop) (l : list A), Exists P l -> ex A (fun x => and (In x l) (P x)) :=
    fun A P => fix go (l : list A) {struct l} : Exists P l -> ex A (fun x => and (In x l) (P x)) :=
        match l as xs return Exists P xs -> ex A (fun x => and (In x xs) (P x)) with
        | nil _ => fun h => False_rect (ex A (fun x => and (In x (nil A)) (P x))) h
        | cons y t => fun h => or_elim (P y) (Exists P t) (ex A (fun x => and (In x (cons y t)) (P x)))
            (fun p => ex_intro A (fun x => and (In x (cons y t)) (P x)) y
                (conj (In y (cons y t)) (P y) (In_head A y t) p))
            (fun p => ex_map A (fun x => and (In x t) (P x)) (fun x => and (In x (cons y t)) (P x))
                (fun x q => conj (In x (cons y t)) (P x)
                    (In_tail A x y t (and_left (In x t) (P x) q)) (and_right (In x t) (P x) q))
                (go t p)) h
        end.
Theorem Exists_map_inv : forall (A B : Set) (f : A -> B) (P : B -> Prop) (l : list A), Exists P (map f l) -> Exists (fun x => P (f x)) l :=
    fun A B f P => fix go (l : list A) {struct l} : Exists P (map f l) -> Exists (fun x => P (f x)) l :=
        match l as xs return Exists P (map f xs) -> Exists (fun x => P (f x)) xs with
        | nil _ => fun h => h
        | cons x t => fun h => or_map (P (f x)) (Exists P (map f t)) (P (f x)) (Exists (fun y => P (f y)) t)
            (fun p => p) (go t) h
        end.
Theorem In_map_inv : forall (A B : Set) (f : A -> B) (y : B) (l : list A), In y (map f l) -> ex A (fun x => and (In x l) (y = (f x))) :=
    fun A B f y l h => Exists_witness A (fun x => (y = (f x))) l (Exists_map_inv A B f (fun z => (y = z)) l h).
Theorem Forall_and : forall (A : Set) (P Q : A -> Prop) (l : list A), Forall P l -> Forall Q l -> Forall (fun x => and (P x) (Q x)) l :=
    fun A P Q l h k => Forall_of_In A (fun x => and (P x) (Q x)) l
        (fun x i => conj (P x) (Q x) (Forall_In A P l h x i) (Forall_In A Q l k x i)).
Theorem Forall_Exists_neg : forall (A : Set) (P : A -> Prop) (l : list A), iff (Forall (fun x => not (P x)) l) (not (Exists P l)) :=
    fun A P l => conj (Forall (fun x => not (P x)) l -> not (Exists P l)) (not (Exists P l) -> Forall (fun x => not (P x)) l)
        (fun h e => match Exists_witness A P l e return False with
            | ex_intro _ _ x q => Forall_In A (fun y => not (P y)) l h x (and_left (In x l) (P x) q) (and_right (In x l) (P x) q)
            end)
        (fun h => Forall_of_In A (fun x => not (P x)) l (fun x i p => h (Exists_of_In A P l x i p))).
Theorem In_split : forall (A : Set) (x : A) (l : list A), In x l ->
    ex (list A) (fun l1 => ex (list A) (fun l2 => (l = (app l1 (cons x l2))))) :=
    fun A x => fix go (l : list A) {struct l} : In x l -> ex (list A) (fun l1 => ex (list A) (fun l2 => (l = (app l1 (cons x l2))))) :=
        match l as xs return In x xs -> ex (list A) (fun l1 => ex (list A) (fun l2 => (xs = (app l1 (cons x l2))))) with
        | nil _ => fun h => False_rect (ex (list A) (fun l1 => ex (list A) (fun l2 => ((nil A) = (app l1 (cons x l2)))))) h
        | cons y t => fun h => or_elim (x = y) (In x t) (ex (list A) (fun l1 => ex (list A) (fun l2 => ((cons y t) = (app l1 (cons x l2))))))
            (fun e => ex_intro (list A) (fun l1 => ex (list A) (fun l2 => ((cons y t) = (app l1 (cons x l2))))) (nil A)
                (ex_intro (list A) (fun l2 => ((cons y t) = (app (nil A) (cons x l2)))) t
                    (f_equal (fun z => cons z t) y x (eq_sym x y e))))
            (fun e => match go t e return ex (list A) (fun l1 => ex (list A) (fun l2 => ((cons y t) = (app l1 (cons x l2))))) with
                | ex_intro _ _ l1 rest => match rest return ex (list A) (fun m1 => ex (list A) (fun m2 => ((cons y t) = (app m1 (cons x m2))))) with
                    | ex_intro _ _ l2 same => ex_intro (list A) (fun m1 => ex (list A) (fun m2 => ((cons y t) = (app m1 (cons x m2))))) (cons y l1)
                        (ex_intro (list A) (fun m2 => ((cons y t) = (app (cons y l1) (cons x m2)))) l2
                            (f_equal (cons y) t (app l1 (cons x l2)) same))
                    end
                end) h
        end.
Theorem In_nth_error : forall (A : Set) (l : list A) (x : A), In x l -> ex nat (fun n => ((nth_error l n) = (Some A x))) :=
    fun A => fix go (l : list A) {struct l} : forall x : A, In x l -> ex nat (fun n => ((nth_error l n) = (Some A x))) :=
        match l as xs return (forall x : A, In x xs -> ex nat (fun n => ((nth_error xs n) = (Some A x)))) with
        | nil _ => fun x h => False_rect (ex nat (fun n => ((nth_error (nil A) n) = (Some A x)))) h
        | cons y t => fun x h => or_elim (x = y) (In x t) (ex nat (fun n => ((nth_error (cons y t) n) = (Some A x))))
            (fun e => ex_intro nat (fun n => ((nth_error (cons y t) n) = (Some A x))) O (f_equal (Some A) y x (eq_sym x y e)))
            (fun e => match go t x e return ex nat (fun n => ((nth_error (cons y t) n) = (Some A x))) with
                | ex_intro _ _ n same => ex_intro nat (fun k => ((nth_error (cons y t) k) = (Some A x))) (S n) same
                end) h
        end.
