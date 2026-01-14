From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_natU_playground__nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred : imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat -> imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat := Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred.

(* Helper lemma: the to map commutes with pred *)
Lemma pred_commutes : forall x1 : Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat,
  to Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso (Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred x1) =
  Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred (to Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso x1).
Proof.
  intros x1.
  destruct x1 as [| x1'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat),
  rel_iso Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso (Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred x1) (imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred x2).
Proof.
  intros x1 x2 Hrel.
  (* rel_iso says: to iso x1 = x2 *)
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred.
  (* We need: to iso (pred x1) = Imported.pred x2 *)
  (* Hrel says: to iso x1 = x2 *)
  (* Use pred_commutes: to iso (pred x1) = Imported.pred (to iso x1) *)
  (* Then rewrite with Hrel *)
  rewrite pred_commutes.
  apply (IsoEq.f_equal Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred Hrel).
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred_iso := {}.