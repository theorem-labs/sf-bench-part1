From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.U_logic__not__iso Isomorphisms.U_s__iso Isomorphisms.le__iso.

Definition imported_Original_LF_Rel_le__Sn__n : forall x : imported_nat, imported_le (imported_S x) x -> imported_False := Imported.Original_LF_Rel_le__Sn__n.

(* Both sides are axioms that return False/imported_False from an empty type *)
(* Since both sides have no inhabitants (le (S n) n is empty), we just need to show *)
(* that applying False_iso works. Both sides have uninhabited inputs, so *)
(* we use the fact that any two proofs into an empty type are equal. *)
Instance Original_LF_Rel_le__Sn__n_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : S x1 <= x1) (x4 : imported_le (imported_S x2) x2),
  rel_iso (le_iso (S_iso hx) hx) x3 x4 -> rel_iso False_iso (Original.LF.Rel.le_Sn_n x1 x3) (imported_Original_LF_Rel_le__Sn__n x4).
Proof.
  intros x1 x2 hx x3 x4 hle.
  unfold rel_iso.
  simpl.
  (* Both Original.LF.Rel.le_Sn_n x1 x3 and imported_Original_LF_Rel_le__Sn__n x4 *)
  (* return empty types (False and imported_False respectively) *)
  (* The isomorphism between False and imported_False preserves the empty structure *)
  (* We need to show that to False_iso (Original.LF.Rel.le_Sn_n x1 x3) = imported_Original_LF_Rel_le__Sn__n x4 *)
  (* Since imported_False is empty (it's RFalse), any two elements are equal *)
  unfold imported_Original_LF_Rel_le__Sn__n.
  (* imported_Original_LF_Rel_le__Sn__n x4 : imported_False, i.e. RFalse *)
  (* RFalse has no constructors so we can destruct on any value *)
  destruct (Imported.Original_LF_Rel_le__Sn__n x2 x4).
Defined.

Instance: KnownConstant Original.LF.Rel.le_Sn_n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF_Rel_le__Sn__n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF.Rel.le_Sn_n Original_LF_Rel_le__Sn__n_iso := {}.
Instance: IsoStatementProofBetween Original.LF.Rel.le_Sn_n Imported.Original_LF_Rel_le__Sn__n Original_LF_Rel_le__Sn__n_iso := {}.