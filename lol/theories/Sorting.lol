(* Verified natural-number sorting. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Bool.
Import lol.theories.Order.
Import lol.theories.BoolOrder.
Import lol.theories.List.
Import lol.theories.ListRelations.

Fixpoint Sorted (l : list nat) : Prop :=
    match l with | nil _ => True | cons x t => and (Forall (le x) t) (Sorted t) end.
Theorem Sorted_tail : forall (x : nat) (l : list nat), Sorted (cons x l) -> Sorted l :=
    fun x l h => and_right (Forall (le x) l) (Sorted l) h.
Theorem Sorted_bound : forall (x : nat) (l : list nat), Sorted (cons x l) -> Forall (le x) l :=
    fun x l h => and_left (Forall (le x) l) (Sorted l) h.
Theorem Forall_le_trans : forall (x y : nat) (l : list nat), le x y -> Forall (le y) l -> Forall (le x) l :=
    fun x y l h => Forall_impl nat (le y) (le x) (fun z => le_trans x y z h) l.

Fixpoint insert (x : nat) (l : list nat) : list nat :=
    match l with
    | nil _ => singleton x
    | cons y t => match leb x y with
        | true => cons x (cons y t)
        | false => cons y (insert x t)
        end
    end.
Theorem insert_permutation : forall (x : nat) (l : list nat), Permutation (cons x l) (insert x l) :=
    fun x => fix go (l : list nat) {struct l} : Permutation (cons x l) (insert x l) :=
        match l as xs return Permutation (cons x xs) (insert x xs) with
        | nil _ => Permutation_refl nat (singleton x)
        | cons y t => match leb x y as b return Permutation (cons x (cons y t)) (match b with | true => cons x (cons y t) | false => cons y (insert x t) end) with
            | true => Permutation_refl nat (cons x (cons y t))
            | false => perm_trans (cons x (cons y t)) (cons y (cons x t)) (cons y (insert x t))
                (perm_swap y x t) (perm_skip y (cons x t) (insert x t) (go t))
            end
        end.
Theorem insert_Forall : forall (P : nat -> Prop) (x : nat) (l : list nat), P x -> Forall P l -> Forall P (insert x l) :=
    fun P x l h k => Permutation_Forall nat P (cons x l) (insert x l) (insert_permutation x l)
        (conj (P x) (Forall P l) h k).
Theorem insert_sorted : forall (x : nat) (l : list nat), Sorted l -> Sorted (insert x l) :=
    fun x => fix go (l : list nat) {struct l} : Sorted l -> Sorted (insert x l) :=
        match l as xs return Sorted xs -> Sorted (insert x xs) with
        | nil _ => fun h => conj True True I I
        | cons y t => fun h => (match leb x y as b return
            (match b return Prop with | true => le x y | false => lt y x end) ->
            Sorted (match b with | true => cons x (cons y t) | false => cons y (insert x t) end) with
            | true => fun xy => conj (Forall (le x) (cons y t)) (Sorted (cons y t))
                (conj (le x y) (Forall (le x) t) xy (Forall_le_trans x y t xy (Sorted_bound y t h))) h
            | false => fun yx => conj (Forall (le y) (insert x t)) (Sorted (insert x t))
                (insert_Forall (le y) x t (lt_le y x yx) (Sorted_bound y t h))
                (go t (Sorted_tail y t h))
            end) (leb_spec x y)
        end.
Fixpoint insertion_sort (l : list nat) : list nat :=
    match l with | nil _ => nil nat | cons x t => insert x (insertion_sort t) end.
Theorem insertion_sort_permutation : forall l : list nat, Permutation l (insertion_sort l) :=
    fix go (l : list nat) {struct l} : Permutation l (insertion_sort l) :=
        match l as xs return Permutation xs (insertion_sort xs) with
        | nil _ => @perm_nil nat
        | cons x t => perm_trans (cons x t) (cons x (insertion_sort t)) (insert x (insertion_sort t))
            (perm_skip x t (insertion_sort t) (go t)) (insert_permutation x (insertion_sort t))
        end.
Theorem insertion_sort_sorted : forall l : list nat, Sorted (insertion_sort l) :=
    fix go (l : list nat) {struct l} : Sorted (insertion_sort l) :=
        match l as xs return Sorted (insertion_sort xs) with
        | nil _ => I
        | cons x t => insert_sorted x (insertion_sort t) (go t)
        end.
Theorem insertion_sort_correct : forall l : list nat, and (Sorted (insertion_sort l)) (Permutation l (insertion_sort l)) :=
    fun l => conj (Sorted (insertion_sort l)) (Permutation l (insertion_sort l))
        (insertion_sort_sorted l) (insertion_sort_permutation l).

(* The inner recursion consumes the right list, and the outer recursion
   consumes the left list. Both are structural; no termination axiom is used. *)
Fixpoint merge (l r : list nat) {struct l} : list nat :=
    match l with
    | nil _ => r
    | cons x t => (fix right (s : list nat) {struct s} : list nat :=
        match s with
        | nil _ => cons x t
        | cons y u => match leb x y with
            | true => cons x (merge t (cons y u))
            | false => cons y (right u)
            end
        end) r
    end.
Theorem merge_permutation : forall l r : list nat, Permutation (app l r) (merge l r) :=
    fix go (l r : list nat) {struct l} : Permutation (app l r) (merge l r) :=
        match l as xs return Permutation (app xs r) (merge xs r) with
        | nil _ => Permutation_refl nat r
        | cons x t => (fix right (s : list nat) {struct s} : Permutation (app (cons x t) s) (merge (cons x t) s) :=
            match s as ys return Permutation (app (cons x t) ys) (merge (cons x t) ys) with
            | nil _ => eq_transport (list nat) (fun zs => Permutation zs (cons x t))
                (cons x t) (app (cons x t) (nil nat))
                (eq_sym (app (cons x t) (nil nat)) (cons x t) (app_nil_right nat (cons x t)))
                (Permutation_refl nat (cons x t))
            | cons y u => match leb x y as b return
                Permutation (app (cons x t) (cons y u))
                    (match b with | true => cons x (merge t (cons y u)) | false => cons y (merge (cons x t) u) end) with
                | true => perm_skip x (app t (cons y u)) (merge t (cons y u)) (go t (cons y u))
                | false => perm_trans (app (cons x t) (cons y u)) (cons y (app (cons x t) u)) (cons y (merge (cons x t) u))
                    (Permutation_sym nat (cons y (app (cons x t) u)) (app (cons x t) (cons y u)) (Permutation_middle nat y (cons x t) u))
                    (perm_skip y (app (cons x t) u) (merge (cons x t) u) (right u))
                end
            end) r
        end.
Theorem merge_Forall : forall (P : nat -> Prop) (l r : list nat), Forall P l -> Forall P r -> Forall P (merge l r) :=
    fun P l r h k => Permutation_Forall nat P (app l r) (merge l r) (merge_permutation l r)
        (Forall_app_join nat P l r h k).
Theorem merge_sorted : forall l r : list nat, Sorted l -> Sorted r -> Sorted (merge l r) :=
    fix go (l r : list nat) {struct l} : Sorted l -> Sorted r -> Sorted (merge l r) :=
        match l as xs return Sorted xs -> Sorted r -> Sorted (merge xs r) with
        | nil _ => fun h k => k
        | cons x t => fun h => (fix right (s : list nat) {struct s} : Sorted s -> Sorted (merge (cons x t) s) :=
            match s as ys return Sorted ys -> Sorted (merge (cons x t) ys) with
            | nil _ => fun k => h
            | cons y u => fun k => (match leb x y as b return
                (match b return Prop with | true => le x y | false => lt y x end) ->
                Sorted (match b with | true => cons x (merge t (cons y u)) | false => cons y (merge (cons x t) u) end) with
                | true => fun xy => conj (Forall (le x) (merge t (cons y u))) (Sorted (merge t (cons y u)))
                    (merge_Forall (le x) t (cons y u) (Sorted_bound x t h)
                        (conj (le x y) (Forall (le x) u) xy (Forall_le_trans x y u xy (Sorted_bound y u k))))
                    (go t (cons y u) (Sorted_tail x t h) k)
                | false => fun yx => conj (Forall (le y) (merge (cons x t) u)) (Sorted (merge (cons x t) u))
                    (merge_Forall (le y) (cons x t) u
                        (conj (le y x) (Forall (le y) t) (lt_le y x yx) (Forall_le_trans y x t (lt_le y x yx) (Sorted_bound x t h)))
                        (Sorted_bound y u k))
                    (right u (Sorted_tail y u k))
                end) (leb_spec x y)
            end) r
        end.

(* Alternating split avoids arithmetic division in the algorithm. *)
Fixpoint split_even (l : list nat) : list nat :=
    match l with | nil _ => nil nat | cons x t => cons x (split_odd t) end
with split_odd (l : list nat) : list nat :=
    match l with | nil _ => nil nat | cons x t => split_even t end.
Theorem split_permutation : forall l : list nat, Permutation l (app (split_even l) (split_odd l)) :=
    fix go (l : list nat) {struct l} : Permutation l (app (split_even l) (split_odd l)) :=
        match l as xs return Permutation xs (app (split_even xs) (split_odd xs)) with
        | nil _ => @perm_nil nat
        | cons x t => perm_skip x t (app (split_odd t) (split_even t))
            (perm_trans t (app (split_even t) (split_odd t)) (app (split_odd t) (split_even t))
                (go t) (Permutation_app_comm nat (split_even t) (split_odd t)))
        end.
Theorem split_lengths : forall l : list nat, and (le (length (split_even l)) (length l)) (le (length (split_odd l)) (length l)) :=
    fix go (l : list nat) {struct l} : and (le (length (split_even l)) (length l)) (le (length (split_odd l)) (length l)) :=
        match l as xs return and (le (length (split_even xs)) (length xs)) (le (length (split_odd xs)) (length xs)) with
        | nil _ => conj (le O O) (le O O) (le_n O) (le_n O)
        | cons x t => let h := go t in
            conj (le (S (length (split_odd t))) (S (length t))) (le (length (split_even t)) (S (length t)))
                (le_succ_mono (length (split_odd t)) (length t)
                    (and_right (le (length (split_even t)) (length t)) (le (length (split_odd t)) (length t)) h))
                (le_S (length (split_even t)) (length t)
                    (and_left (le (length (split_even t)) (length t)) (le (length (split_odd t)) (length t)) h))
        end.
Theorem split_even_length : forall l : list nat, le (length (split_even l)) (length l) :=
    fun l => and_left (le (length (split_even l)) (length l)) (le (length (split_odd l)) (length l)) (split_lengths l).
Theorem split_odd_length : forall l : list nat, le (length (split_odd l)) (length l) :=
    fun l => and_right (le (length (split_even l)) (length l)) (le (length (split_odd l)) (length l)) (split_lengths l).
Theorem split_even_decrease : forall (x y : nat) (l : list nat) (n : nat), le (length (cons x (cons y l))) (S n) -> le (length (split_even (cons x (cons y l)))) n :=
    fun x y l n h => le_trans (S (length (split_even l))) (S (length l)) n
        (le_succ_mono (length (split_even l)) (length l) (split_even_length l))
        (le_succ_inv (S (length l)) n h).
Theorem split_odd_decrease : forall (x y : nat) (l : list nat) (n : nat), le (length (cons x (cons y l))) (S n) -> le (length (split_odd (cons x (cons y l)))) n :=
    fun x y l n h => le_trans (S (length (split_odd l))) (S (length l)) n
        (le_succ_mono (length (split_odd l)) (length l) (split_odd_length l))
        (le_succ_inv (S (length l)) n h).

(* Fuel recursion is total for every fuel; correctness requires the explicit
   bound below. The public algorithm supplies length l, which satisfies it.
   This is structural fuel recursion, not an accessibility recursion claim. *)
Fixpoint merge_sort_fuel (fuel : nat) (l : list nat) {struct fuel} : list nat :=
    match fuel with
    | O => l
    | S n => match l with
        | nil _ => nil nat
        | cons x t => match t with
            | nil _ => singleton x
            | cons y u => merge (merge_sort_fuel n (split_even (cons x (cons y u))))
                (merge_sort_fuel n (split_odd (cons x (cons y u))))
            end
        end
    end.
Theorem merge_sort_fuel_correct : forall (fuel : nat) (l : list nat), le (length l) fuel ->
    and (Sorted (merge_sort_fuel fuel l)) (Permutation l (merge_sort_fuel fuel l)) :=
    fix go (fuel : nat) (l : list nat) {struct fuel} : le (length l) fuel ->
        and (Sorted (merge_sort_fuel fuel l)) (Permutation l (merge_sort_fuel fuel l)) :=
        match fuel as n return le (length l) n -> and (Sorted (merge_sort_fuel n l)) (Permutation l (merge_sort_fuel n l)) with
        | O => match l as xs return le (length xs) O -> and (Sorted xs) (Permutation xs xs) with
            | nil _ => fun h => conj True (Permutation (nil nat) (nil nat)) I (@perm_nil nat)
            | cons x t => fun h => False_rect (and (Sorted (cons x t)) (Permutation (cons x t) (cons x t))) (lt_zero_false (length t) h)
            end
        | S n => match l as xs return le (length xs) (S n) -> and (Sorted (merge_sort_fuel (S n) xs)) (Permutation xs (merge_sort_fuel (S n) xs)) with
            | nil _ => fun h => conj True (Permutation (nil nat) (nil nat)) I (@perm_nil nat)
            | cons x t => match t as ys return le (length (cons x ys)) (S n) ->
                and (Sorted (merge_sort_fuel (S n) (cons x ys))) (Permutation (cons x ys) (merge_sort_fuel (S n) (cons x ys))) with
                | nil _ => fun h => conj (Sorted (singleton x)) (Permutation (singleton x) (singleton x))
                    (conj True True I I) (Permutation_refl nat (singleton x))
                | cons y u => fun h =>
                    let left := split_even (cons x (cons y u)) in
                    let right := split_odd (cons x (cons y u)) in
                    let ls := merge_sort_fuel n left in
                    let rs := merge_sort_fuel n right in
                    let hl := go n left (split_even_decrease x y u n h) in
                    let hr := go n right (split_odd_decrease x y u n h) in
                    conj (Sorted (merge ls rs)) (Permutation (cons x (cons y u)) (merge ls rs))
                        (merge_sorted ls rs
                            (and_left (Sorted ls) (Permutation left ls) hl)
                            (and_left (Sorted rs) (Permutation right rs) hr))
                        (perm_trans (cons x (cons y u)) (app left right) (merge ls rs)
                            (split_permutation (cons x (cons y u)))
                            (perm_trans (app left right) (app ls rs) (merge ls rs)
                                (Permutation_app nat left ls right rs
                                    (and_right (Sorted ls) (Permutation left ls) hl)
                                    (and_right (Sorted rs) (Permutation right rs) hr))
                                (merge_permutation ls rs)))
                end
            end
        end.
Definition merge_sort (l : list nat) : list nat := merge_sort_fuel (length l) l.
Theorem merge_sort_correct : forall l : list nat, and (Sorted (merge_sort l)) (Permutation l (merge_sort l)) :=
    fun l => merge_sort_fuel_correct (length l) l (le_n (length l)).
Theorem merge_sort_sorted : forall l : list nat, Sorted (merge_sort l) :=
    fun l => and_left (Sorted (merge_sort l)) (Permutation l (merge_sort l)) (merge_sort_correct l).
Theorem merge_sort_permutation : forall l : list nat, Permutation l (merge_sort l) :=
    fun l => and_right (Sorted (merge_sort l)) (Permutation l (merge_sort l)) (merge_sort_correct l).
Theorem insertion_sort_length : forall l : list nat, ((length l) = (length (insertion_sort l))) :=
    fun l => Permutation_length nat l (insertion_sort l) (insertion_sort_permutation l).
Theorem merge_sort_length : forall l : list nat, ((length l) = (length (merge_sort l))) :=
    fun l => Permutation_length nat l (merge_sort l) (merge_sort_permutation l).
Theorem insertion_sort_member : forall (x : nat) (l : list nat), In x l -> In x (insertion_sort l) :=
    fun x l => Permutation_In nat x l (insertion_sort l) (insertion_sort_permutation l).
Theorem merge_sort_member : forall (x : nat) (l : list nat), In x l -> In x (merge_sort l) :=
    fun x l => Permutation_In nat x l (merge_sort l) (merge_sort_permutation l).
