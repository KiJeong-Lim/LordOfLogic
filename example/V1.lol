(* From the repository root, run: cabal run -v0 lol -- example/V1.lol
   Rocq export: cabal run -v0 lol -- --rocq example/V1.lol
   The editor accepts the same file in a trusted VS Code workspace. *)
Section Operations.
Context (A : Set) (combine : forall _ : A, forall _ : A, A).
Definition twice (a : A) : A := combine a a.
End Operations.
Search _ "twice".
Axiom Item : Set.
Axiom seed : Item.
Axiom mix : forall _ : Item, forall _ : Item, Item.
Declare Scope calc_scope.
Delimit Scope calc_scope with calc.
Infix "⊕" := mix (at level 50, left associativity) : calc_scope.
Open Scope calc_scope.
Definition doubled : Item := seed ⊕ seed.
Close Scope calc_scope.
Definition explicit_scope : Item := (seed ⊕ seed)%calc.
Declare Custom Entry expression.
Notation "<{ x }>" := x (x custom expression).
Notation "'atom'" := seed (in custom expression at level 0).
Notation "x + y" := (mix x y) (in custom expression at level 50, left associativity).
Definition parsed : Item := <{atom + atom}>.
Check twice.
Theorem retain : forall P : Prop, forall _ : P, P.
Proof.
    intros P h.
    exact h.
Qed.
