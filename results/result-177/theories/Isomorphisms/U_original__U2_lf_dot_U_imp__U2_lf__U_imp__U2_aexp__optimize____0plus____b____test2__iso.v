From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_band__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_ble__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_btrue__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b
       (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
          (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe
             (imported_Original_LF__DOT__Imp_LF_Imp_AExp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum imported_0)
                (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S imported_0))))))
             (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
          imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue))
    (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
       (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S imported_0)))))
          (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
       imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue) := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2.
Instance Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso
             (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso
                   (Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso _0_iso) (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                   (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
          (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
             (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
             Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso);
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
                   (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso
                      (Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso _0_iso)
                         (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                      (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                   Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
             (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                   (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b
                   (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
                      (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe
                         (imported_Original_LF__DOT__Imp_LF_Imp_AExp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum imported_0)
                            (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S imported_0))))))
                         (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                      imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue))
                (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
                   (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S imported_0)))))
                      (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))
                   imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
                   (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso
                      (Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso _0_iso)
                         (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                      (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                   Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
             (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                   (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b
                (Original.LF_DOT_Imp.LF.Imp.AExp.BAnd
                   (Original.LF_DOT_Imp.LF.Imp.AExp.BLe (Original.LF_DOT_Imp.LF.Imp.AExp.APlus (Original.LF_DOT_Imp.LF.Imp.AExp.ANum 0) (Original.LF_DOT_Imp.LF.Imp.AExp.ANum 4))
                      (Original.LF_DOT_Imp.LF.Imp.AExp.ANum 5))
                   Original.LF_DOT_Imp.LF.Imp.AExp.BTrue) =
              Original.LF_DOT_Imp.LF.Imp.AExp.BAnd (Original.LF_DOT_Imp.LF.Imp.AExp.BLe (Original.LF_DOT_Imp.LF.Imp.AExp.ANum 4) (Original.LF_DOT_Imp.LF.Imp.AExp.ANum 5))
                Original.LF_DOT_Imp.LF.Imp.AExp.BTrue =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso
                   (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
                      (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso
                         (Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso _0_iso)
                            (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                         (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                      Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
                (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
                   (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))
                      (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))
                   Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
             x)
    |} Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test2 imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2.
Proof.
  unfold rel_iso.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2.
  simpl.
  (* Both source and target are SProp, so proof irrelevance applies *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test2 Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2 Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2_iso := {}.