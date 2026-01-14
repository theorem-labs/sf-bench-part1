From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n : forall x : imported_nat, imported_le imported_0 x := Imported.Original_LF__DOT__IndProp_LF_IndProp_O__le__n.

(* The rel_iso for two elements of an Iso is just the SProp equality between
   applying 'to' to the first and getting the second. *)
Instance Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := le_iso _0_iso hx;
      from := from (le_iso _0_iso hx);
      to_from := fun x : imported_le imported_0 x2 => to_from (le_iso _0_iso hx) x;
      from_to := fun x : Peano.le Datatypes.O x1 => seq_p_of_t (from_to (le_iso _0_iso hx) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.O_le_n x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n x2).
Proof.
  intros x1 x2 hx.
  unfold rel_iso. simpl.
  (* We need to show: IsomorphismDefinitions.eq 
       (to (le_iso _0_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.O_le_n x1))
       (imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n x2) *)
  (* Both sides are in SProp (imported_le imported_0 x2), so they are equal by proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.O_le_n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_O__le__n := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.O_le_n Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.O_le_n Imported.Original_LF__DOT__IndProp_LF_IndProp_O__le__n Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso := {}.