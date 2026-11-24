(* From the repository root run
     cabal run -v0 lol -- example/V1Scopes.lol
   In the VS Code extension, put the cursor after intros and run
   "LoL: Check to Cursor". Change the last tactic and run again. *)

Section Choice.
Context (A : Set).
Definition keep_left (x y : A) : A := x.
Definition keep_right (x y : A) : A := y.
End Choice.

Inductive Color : Set := | red : Color | blue : Color.
Declare Scope left_scope.
Declare Scope right_scope.
Delimit Scope left_scope with L.
Delimit Scope right_scope with R.
Reserved Infix "⊕" (at level 50, left associativity).
Notation "x ⊕ y" := (keep_left Color x y) : left_scope.
Notation "x ⊕ y" := (keep_right Color x y) : right_scope.
Open Scope left_scope.

Compute red ⊕ blue.
Compute (red ⊕ blue)%R.
Search (forall A : Set, forall x y : A, A) "keep_".

Theorem choose_proof : forall (P : Prop) (p q : P), P.
Proof.
intros P p q.
exact p.
Qed.
