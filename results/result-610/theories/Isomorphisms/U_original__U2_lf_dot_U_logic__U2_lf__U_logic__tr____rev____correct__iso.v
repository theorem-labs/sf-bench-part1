From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__tr____rev__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_tr__rev__correct : forall x : Type,
  imported_Corelib_Init_Logic_eq (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x => imported_Original_LF__DOT__Logic_LF_Logic_tr__rev x4)
    (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x => imported_Original_LF__DOT__Poly_LF_Poly_rev x4) := Imported.Original_LF__DOT__Logic_LF_Logic_tr__rev__correct.

(* tr_rev_correct is an axiom (Admitted in Original.v), so we prove the isomorphism *)
Instance Original_LF__DOT__Logic_LF_Logic_tr__rev__correct_iso : forall (x1 x2 : Type) (hx : Iso x1 x2),
  @rel_iso (@Original.LF_DOT_Logic.LF.Logic.tr_rev x1 = @Original.LF_DOT_Poly.LF.Poly.rev x1)
    (@imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_list x2 -> imported_Original_LF__DOT__Poly_LF_Poly_list x2)
       (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Logic_LF_Logic_tr__rev x2 x4)
       (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Poly_LF_Poly_rev x2 x4))
    (@relax_Iso_Ts_Ps (@Original.LF_DOT_Logic.LF.Logic.tr_rev x1 = @Original.LF_DOT_Poly.LF.Poly.rev x1)
       (@imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_list x2 -> imported_Original_LF__DOT__Poly_LF_Poly_list x2)
          (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Logic_LF_Logic_tr__rev x2 x4)
          (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Poly_LF_Poly_rev x2 x4))
       (@Corelib_Init_Logic_eq_iso (Original.LF_DOT_Poly.LF.Poly.list x1 -> Original.LF_DOT_Poly.LF.Poly.list x1)
          (imported_Original_LF__DOT__Poly_LF_Poly_list x2 -> imported_Original_LF__DOT__Poly_LF_Poly_list x2)
          (@IsoArrow (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx)
             (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx))
          (@Original.LF_DOT_Logic.LF.Logic.tr_rev x1) (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Logic_LF_Logic_tr__rev x2 x4)
          (@IsoFunND (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx)
             (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) (@Original.LF_DOT_Logic.LF.Logic.tr_rev x1)
             (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Logic_LF_Logic_tr__rev x2 x4)
             (fun (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
                (hx0 : @rel_iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) x3 x4) =>
              @Original_LF__DOT__Logic_LF_Logic_tr__rev_iso x1 x2 hx x3 x4 hx0))
          (@Original.LF_DOT_Poly.LF.Poly.rev x1) (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Poly_LF_Poly_rev x2 x4)
          (@IsoFunND (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx)
             (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) (@Original.LF_DOT_Poly.LF.Poly.rev x1)
             (fun x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => @imported_Original_LF__DOT__Poly_LF_Poly_rev x2 x4)
             (fun (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
                (hx0 : @rel_iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) x3 x4) =>
              @Original_LF__DOT__Poly_LF_Poly_rev_iso x1 x2 hx x3 x4 hx0))))
    (Original.LF_DOT_Logic.LF.Logic.tr_rev_correct x1) (imported_Original_LF__DOT__Logic_LF_Logic_tr__rev__correct x2).
Proof.
  intros x1 x2 hx.
  (* rel_iso means: IsomorphismDefinitions.eq (to iso (tr_rev_correct x1)) (imported_tr_rev_correct x2) *)
  (* Since the target is in SProp and any two SProp proofs are equal, we just need to show any SProp element *)
  unfold rel_iso. simpl.
  (* Both sides are in SProp, so they are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.tr_rev_correct := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_tr__rev__correct := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.tr_rev_correct Original_LF__DOT__Logic_LF_Logic_tr__rev__correct_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.tr_rev_correct Imported.Original_LF__DOT__Logic_LF_Logic_tr__rev__correct Original_LF__DOT__Logic_LF_Logic_tr__rev__correct_iso := {}.