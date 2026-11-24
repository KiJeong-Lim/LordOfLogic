(* The simply typed lambda calculus of lol.theories.STLC: a typing derivation,
   a reduction step and the preservation theorem of the library.
   Run from the root of the repository:

       cabal run -v0 lol -- example/STLC.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.STLC.

(* Variables are de Bruijn indices: st_var O is the nearest binder. *)
Definition identity : sterm := st_lam st_unit (st_var O).
Definition applied : sterm := st_app identity st_tt.

(* A typing derivation is built from the constructors of styping. *)
Theorem identity_typed : styping sempty identity (st_arrow st_unit st_unit).
Proof.
    unfold identity.
    apply st_ty_lam.
    apply st_ty_var.
    reflexivity.
Qed.

Theorem applied_typed : styping sempty applied st_unit.
Proof.
    unfold applied.
    apply (st_ty_app sempty st_unit st_unit).
    - exact identity_typed.
    - apply st_ty_tt.
Qed.

(* The step substitutes tt for the variable. *)
Compute sbeta (st_var O) st_tt.

Theorem applied_steps : sstep applied st_tt.
Proof.
    unfold applied, identity.
    change (sstep (st_app (st_lam st_unit (st_var O)) st_tt) (sbeta (st_var O) st_tt)).
    apply st_step_beta.
    exact I.
Qed.

(* Preservation: a step keeps the type. *)
Check stlc_preservation.
Theorem result_typed : styping sempty st_tt st_unit :=
    stlc_preservation applied st_tt applied_steps sempty st_unit applied_typed.

Print Assumptions result_typed.
