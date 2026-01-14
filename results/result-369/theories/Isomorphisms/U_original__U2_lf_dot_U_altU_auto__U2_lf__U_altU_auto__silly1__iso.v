From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__AltAuto_LF_AltAuto_silly1 : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S imported_0) x) (imported_S x) := Imported.Original_LF__DOT__AltAuto_LF_AltAuto_silly1.

Instance Original_LF__DOT__AltAuto_LF_AltAuto_silly1_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx);
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S imported_0) x2) (imported_S x2) => to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx)) x;
      from_to := fun x : 1 + x1 = S x1 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso _0_iso) hx) (S_iso hx)) x)
    |} (Original.LF_DOT_AltAuto.LF.AltAuto.silly1 x1) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_silly1 x2).
Proof.
  intros x1 x2 hx.
  (* Both Original.LF_DOT_AltAuto.LF.AltAuto.silly1 and the imported version are proofs 
     of SProp statements, so they're unique *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_AltAuto.LF.AltAuto.silly1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__AltAuto_LF_AltAuto_silly1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.silly1 Original_LF__DOT__AltAuto_LF_AltAuto_silly1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.silly1 Imported.Original_LF__DOT__AltAuto_LF_AltAuto_silly1 Original_LF__DOT__AltAuto_LF_AltAuto_silly1_iso := {}.