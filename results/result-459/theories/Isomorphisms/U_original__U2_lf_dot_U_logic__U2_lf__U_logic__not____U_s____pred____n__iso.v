From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_logic__not__iso Isomorphisms.U_nat__pred__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_not__S__pred__n : (forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_S (imported_Nat_pred x)) x) -> imported_False := Imported.Original_LF__DOT__Logic_LF_Logic_not__S__pred__n.

(* The main isomorphism: This is an axiom isomorphism since the original is Admitted.
   Both sides are axioms, so we need to show they're related via rel_iso.
   Since both False and imported_False (PFalse) are empty types in SProp,
   we can prove the isomorphism using the False elimination principle. *)
Instance Original_LF__DOT__Logic_LF_Logic_not__S__pred__n_iso : forall (x1 : forall n : nat, Datatypes.S (Nat.pred n) = n) (x2 : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_S (imported_Nat_pred x)) x),
  (forall (x3 : nat) (x4 : imported_nat) (hx : rel_iso nat_iso x3 x4), rel_iso (relax_Iso_Ts_Ps (Corelib_Init_Logic_eq_iso (S_iso (Nat_pred_iso hx)) hx)) (x1 x3) (x2 x4)) ->
  rel_iso (relax_Iso_Ts_Ps False_iso) (Original.LF_DOT_Logic.LF.Logic.not_S_pred_n x1) (imported_Original_LF__DOT__Logic_LF_Logic_not__S__pred__n x2).
Proof.
  intros x1 x2 Hrel.
  unfold rel_iso, relax_Iso_Ts_Ps, imported_Original_LF__DOT__Logic_LF_Logic_not__S__pred__n.
  simpl.
  (* The goal is: eq (to False_iso (not_S_pred_n x1)) (Original_LF__DOT__Logic_LF_Logic_not__S__pred__n x2)
     Both sides are in imported_False = PFalse, which is an empty SProp.
     We can use PFalse_indl to eliminate any element of PFalse. *)
  apply (Imported.PFalse_indl (fun f => IsomorphismDefinitions.eq (to False_iso (Original.LF_DOT_Logic.LF.Logic.not_S_pred_n x1)) f)).
Qed.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.not_S_pred_n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_not__S__pred__n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_S_pred_n Original_LF__DOT__Logic_LF_Logic_not__S__pred__n_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_S_pred_n Imported.Original_LF__DOT__Logic_LF_Logic_not__S__pred__n Original_LF__DOT__Logic_LF_Logic_not__S__pred__n_iso := {}.