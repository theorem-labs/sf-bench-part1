From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.cons__iso Isomorphisms.nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aminus__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_anum__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_sload__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_sminus__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_smult__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_spush__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____compile__iso Isomorphisms.U_s__iso.

(* Define imported_Original_LF__DOT__Imp_LF_Imp_s__compile1 using the imported axiom *)
(* s_compile1 is Admitted in Original.v, and we exported it as an axiom from Lean *)
Definition imported_Original_LF__DOT__Imp_LF_Imp_s__compile1 : 
  imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Imp_LF_Imp_s__compile
       (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
          (imported_Original_LF__DOT__Imp_LF_Imp_AMult (imported_Original_LF__DOT__Imp_LF_Imp_ANum (imported_S (imported_S imported_0)))
             (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))))
    (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SLoad imported_Original_LF__DOT__Imp_LF_Imp_X)
       (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S (imported_S imported_0)))
          (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SLoad imported_Original_LF__DOT__Imp_LF_Imp_Y)
             (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SMult (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SMinus (imported_nil imported_Original_LF__DOT__Imp_LF_Imp_sinstr))))))
  := Imported.Original_LF__DOT__Imp_LF_Imp_s__compile1.

Instance Original_LF__DOT__Imp_LF_Imp_s__compile1_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Imp_LF_Imp_s__compile_iso
             (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                (Original_LF__DOT__Imp_LF_Imp_AMult_iso (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))))
          (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
             (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso _0_iso)))
                (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                   (cons_iso Original_LF__DOT__Imp_LF_Imp_SMult_iso (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso))))));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_s__compile_iso
                (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                   (Original_LF__DOT__Imp_LF_Imp_AMult_iso (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))))
             (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso _0_iso)))
                   (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                      (cons_iso Original_LF__DOT__Imp_LF_Imp_SMult_iso (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso)))))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Imp_LF_Imp_s__compile
                   (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                      (imported_Original_LF__DOT__Imp_LF_Imp_AMult (imported_Original_LF__DOT__Imp_LF_Imp_ANum (imported_S (imported_S imported_0)))
                         (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))))
                (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SLoad imported_Original_LF__DOT__Imp_LF_Imp_X)
                   (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S (imported_S imported_0)))
                      (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SLoad imported_Original_LF__DOT__Imp_LF_Imp_Y)
                         (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SMult
                            (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SMinus (imported_nil imported_Original_LF__DOT__Imp_LF_Imp_sinstr)))))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_s__compile_iso
                (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                   (Original_LF__DOT__Imp_LF_Imp_AMult_iso (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))))
             (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso _0_iso)))
                   (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                      (cons_iso Original_LF__DOT__Imp_LF_Imp_SMult_iso (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso)))))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Imp.LF.Imp.s_compile
                (Original.LF_DOT_Imp.LF.Imp.AMinus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X)
                   (Original.LF_DOT_Imp.LF.Imp.AMult (Original.LF_DOT_Imp.LF.Imp.ANum 2) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y))) =
              (Original.LF_DOT_Imp.LF.Imp.SLoad Original.LF_DOT_Imp.LF.Imp.X
               :: Original.LF_DOT_Imp.LF.Imp.SPush 2 :: Original.LF_DOT_Imp.LF.Imp.SLoad Original.LF_DOT_Imp.LF.Imp.Y :: Original.LF_DOT_Imp.LF.Imp.SMult :: Original.LF_DOT_Imp.LF.Imp.SMinus :: nil)%list =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Imp_LF_Imp_s__compile_iso
                   (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                      (Original_LF__DOT__Imp_LF_Imp_AMult_iso (Original_LF__DOT__Imp_LF_Imp_ANum_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))))
                (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                   (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso _0_iso)))
                      (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                         (cons_iso Original_LF__DOT__Imp_LF_Imp_SMult_iso (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso)))))))
             x)
    |} Original.LF_DOT_Imp.LF.Imp.s_compile1 imported_Original_LF__DOT__Imp_LF_Imp_s__compile1.
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.s_compile1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_s__compile1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.s_compile1 Original_LF__DOT__Imp_LF_Imp_s__compile1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.s_compile1 Imported.Original_LF__DOT__Imp_LF_Imp_s__compile1 Original_LF__DOT__Imp_LF_Imp_s__compile1_iso := {}.