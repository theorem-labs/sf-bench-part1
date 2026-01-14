From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.U_s__iso Isomorphisms.le__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m : forall x x0 : imported_nat, imported_le (imported_S x) (imported_S x0) -> imported_le x x0 := Imported.Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m.
Instance Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : (S x1 <= S x3)%nat)
    (x6 : imported_le (imported_S x2) (imported_S x4)),
  rel_iso
    {|
      to := le_iso (S_iso hx) (S_iso hx0);
      from := from (le_iso (S_iso hx) (S_iso hx0));
      to_from := fun x : imported_le (imported_S x2) (imported_S x4) => to_from (le_iso (S_iso hx) (S_iso hx0)) x;
      from_to := fun x : (S x1 <= S x3)%nat => seq_p_of_t (from_to (le_iso (S_iso hx) (S_iso hx0)) x)
    |} x5 x6 ->
  rel_iso
    {| to := le_iso hx hx0; from := from (le_iso hx hx0); to_from := fun x : imported_le x2 x4 => to_from (le_iso hx hx0) x; from_to := fun x : (x1 <= x3)%nat => seq_p_of_t (from_to (le_iso hx hx0) x) |}
    (Original.LF_DOT_IndProp.LF.IndProp.Sn_le_Sm__n_le_m x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 H.
  unfold rel_iso. simpl.
  (* Both sides are in SProp (imported_le x2 x4), so eq is trivially satisfied *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.Sn_le_Sm__n_le_m := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Sn_le_Sm__n_le_m Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Sn_le_Sm__n_le_m Imported.Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m Original_LF__DOT__IndProp_LF_IndProp_Sn__le__Sm____n__le__m_iso := {}.