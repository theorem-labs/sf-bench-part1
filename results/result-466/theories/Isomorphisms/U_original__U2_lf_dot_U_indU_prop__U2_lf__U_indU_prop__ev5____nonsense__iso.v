From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__add__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) ->
  imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
    (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense.
Instance Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev 5)
    (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))) x1 x2 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))));
      from := from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq (imported_Nat_add (imported_S (imported_S imported_0)) (imported_S (imported_S imported_0)))
                (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))))) =>
        to_from (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) x;
      from_to :=
        fun x : ((2 + 2)%nat = (9)%nat) =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_add_iso (S_iso (S_iso _0_iso)) (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense x2).
Proof.
  intros x1 x2 Hx.
  unfold rel_iso. simpl.
  (* The goal is: to(...) (ev5_nonsense x1) = imported_ev5_nonsense x2 *)
  (* Both sides are in SProp, so we use definitional equality *)
  exact IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev5_nonsense Imported.Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense_iso := {}.