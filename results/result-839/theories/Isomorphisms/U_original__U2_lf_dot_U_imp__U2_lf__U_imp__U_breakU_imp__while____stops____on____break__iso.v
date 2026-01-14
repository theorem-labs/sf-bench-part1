From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cwhile__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_sbreak__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__beval__iso Isomorphisms.true__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break 
  (x : imported_Original_LF__DOT__Imp_LF_Imp_bexp) 
  (x0 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) 
  (x1 x2 : imported_String_string -> imported_nat)
  (H1 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_beval (fun s => x1 s) x) imported_true)
  (H2 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x0 (fun s => x1 s) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak (fun s => x2 s))
  : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile x x0) (fun s => x1 s)
      imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue (fun s => x2 s) :=
  Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break x x0 x1 x2 H1 H2.
(* The isomorphism proof for while_stops_on_break - this corresponds to an Admitted theorem *)
Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_bexp) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_bexp_iso x1 x2)
    (x3 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (hx0 : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x3 x4)
    (x5 : Original.LF_DOT_Imp.LF.Imp.state) (x6 : imported_String_string -> imported_nat)
    (hx1 : forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8)) (x7 : Original.LF_DOT_Imp.LF.Imp.state)
    (x8 : imported_String_string -> imported_nat) (hx2 : forall (x9 : String.string) (x10 : imported_String_string), rel_iso String_string_iso x9 x10 -> rel_iso nat_iso (x7 x9) (x8 x10))
    (x9 : Original.LF_DOT_Imp.LF.Imp.beval x5 x1 = true) (x10 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_beval (fun x : imported_String_string => x6 x) x2) imported_true),
  rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Imp_LF_Imp_beval_iso x5 (fun x : imported_String_string => x6 x)
             (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) hx)
          true_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_beval_iso x5 (fun x : imported_String_string => x6 x)
                (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) hx)
             true_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_beval (fun x : imported_String_string => x6 x) x2) imported_true =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_beval_iso x5 (fun x0 : imported_String_string => x6 x0)
                (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) hx)
             true_iso)
          x;
      from_to :=
        fun x : Original.LF_DOT_Imp.LF.Imp.beval x5 x1 = true =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Imp_LF_Imp_beval_iso x5 (fun x0 : imported_String_string => x6 x0)
                   (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) hx)
                true_iso)
             x)
    |} x9 x10 ->
  forall (x11 : Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x3 x5 Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak x7)
    (x12 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x4 (fun x : imported_String_string => x6 x) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak
             (fun x : imported_String_string => x8 x)),
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso hx0 x5 (fun x : imported_String_string => x6 x)
       (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx1 x13 x14 hx4) Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso x7
       (fun x : imported_String_string => x8 x) (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx2 x13 x14 hx4))
    x11 x12 ->
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso (Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso hx hx0) x5 (fun x : imported_String_string => x6 x)
       (fun (x13 : String.string) (x14 : imported_String_string) (hx5 : rel_iso String_string_iso x13 x14) => hx1 x13 x14 hx5) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x7
       (fun x : imported_String_string => x8 x) (fun (x13 : String.string) (x14 : imported_String_string) (hx5 : rel_iso String_string_iso x13 x14) => hx2 x13 x14 hx5))
    (Original.LF_DOT_Imp.LF.Imp.BreakImp.while_stops_on_break x1 x3 x5 x7 x9 x11) (@imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break x2 x4 x6 x8 x10 x12).
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.BreakImp.while_stops_on_break := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.while_stops_on_break Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.while_stops_on_break Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break Original_LF__DOT__Imp_LF_Imp_BreakImp_while__stops__on__break_iso := {}.