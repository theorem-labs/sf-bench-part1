From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.cons__iso Isomorphisms.nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_sminus__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_spush__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_s__execute1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Imp_LF_Imp_s__execute (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x) (imported_nil imported_nat)
       (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
          (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S (imported_S (imported_S imported_0))))
             (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S imported_0))
                (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SMinus (imported_nil imported_Original_LF__DOT__Imp_LF_Imp_sinstr))))))
    (imported_cons (imported_S (imported_S imported_0)) (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) (imported_nil imported_nat))) := Imported.Original_LF__DOT__Imp_LF_Imp_s__execute1.
Instance Original_LF__DOT__Imp_LF_Imp_s__execute1_iso : rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Imp_LF_Imp_s__execute_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x)
             (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) => Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx) (nil_iso nat_iso)
             (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso _0_iso))))
                   (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso _0_iso)) (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso))))))
          (cons_iso (S_iso (S_iso _0_iso)) (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (nil_iso nat_iso)));
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_s__execute_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x)
                (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) => Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx) (nil_iso nat_iso)
                (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                   (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso _0_iso))))
                      (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso _0_iso)) (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso))))))
             (cons_iso (S_iso (S_iso _0_iso)) (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (nil_iso nat_iso))));
      to_from :=
        fun
          x : imported_Corelib_Init_Logic_eq
                (imported_Original_LF__DOT__Imp_LF_Imp_s__execute (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x) (imported_nil imported_nat)
                   (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))))
                      (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S (imported_S (imported_S imported_0))))
                         (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S imported_0))
                            (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SMinus (imported_nil imported_Original_LF__DOT__Imp_LF_Imp_sinstr))))))
                (imported_cons (imported_S (imported_S imported_0)) (imported_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) (imported_nil imported_nat))) =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_s__execute_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0)
                (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) => Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx) (nil_iso nat_iso)
                (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                   (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso _0_iso))))
                      (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso _0_iso)) (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso))))))
             (cons_iso (S_iso (S_iso _0_iso)) (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (nil_iso nat_iso))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_Imp.LF.Imp.s_execute Original.LF_DOT_Imp.LF.Imp.empty_st (@Datatypes.nil Datatypes.nat)
                (@Datatypes.cons _ (Original.LF_DOT_Imp.LF.Imp.SPush (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S Datatypes.O)))))) 
                  (@Datatypes.cons _ (Original.LF_DOT_Imp.LF.Imp.SPush (Datatypes.S (Datatypes.S (Datatypes.S Datatypes.O)))) 
                    (@Datatypes.cons _ (Original.LF_DOT_Imp.LF.Imp.SPush (Datatypes.S Datatypes.O)) 
                      (@Datatypes.cons _ Original.LF_DOT_Imp.LF.Imp.SMinus (@Datatypes.nil _))))) =
              (@Datatypes.cons Datatypes.nat (Datatypes.S (Datatypes.S Datatypes.O)) 
                (@Datatypes.cons Datatypes.nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S Datatypes.O))))) 
                  (@Datatypes.nil Datatypes.nat))) =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Imp_LF_Imp_s__execute_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0)
                   (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) => Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx) (nil_iso nat_iso)
                   (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))))
                      (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso _0_iso))))
                         (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso _0_iso)) (cons_iso Original_LF__DOT__Imp_LF_Imp_SMinus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso))))))
                (cons_iso (S_iso (S_iso _0_iso)) (cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (nil_iso nat_iso))))
             x)
    |} Original.LF_DOT_Imp.LF.Imp.s_execute1 imported_Original_LF__DOT__Imp_LF_Imp_s__execute1.
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.s_execute1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_s__execute1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.s_execute1 Original_LF__DOT__Imp_LF_Imp_s__execute1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.s_execute1 Imported.Original_LF__DOT__Imp_LF_Imp_s__execute1 Original_LF__DOT__Imp_LF_Imp_s__execute1_iso := {}.