From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_fold__example1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_fold (fun x x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool => imported_Original_LF__DOT__Basics_LF_Basics_andb x x0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
          (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
             (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_false
                (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
                   (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Original_LF__DOT__Basics_LF_Basics_bool)))))
       imported_Original_LF__DOT__Basics_LF_Basics_true)
    imported_Original_LF__DOT__Basics_LF_Basics_false := Imported.Original_LF__DOT__Poly_LF_Poly_fold__example1.

(* Build an Iso Prop SProp directly *)
Definition fold_example1_prop_sprop_iso : 
  Iso (Original.LF_DOT_Poly.LF.Poly.fold Original.LF_DOT_Basics.LF.Basics.andb
         (Original.LF_DOT_Poly.LF.Poly.cons Original.LF_DOT_Basics.LF.Basics.true
            (Original.LF_DOT_Poly.LF.Poly.cons Original.LF_DOT_Basics.LF.Basics.true
               (Original.LF_DOT_Poly.LF.Poly.cons Original.LF_DOT_Basics.LF.Basics.false
                  (Original.LF_DOT_Poly.LF.Poly.cons Original.LF_DOT_Basics.LF.Basics.true
                     Original.LF_DOT_Poly.LF.Poly.nil))))
         Original.LF_DOT_Basics.LF.Basics.true = Original.LF_DOT_Basics.LF.Basics.false)
      (imported_Corelib_Init_Logic_eq
         (imported_Original_LF__DOT__Poly_LF_Poly_fold
            (fun x x0 => imported_Original_LF__DOT__Basics_LF_Basics_andb x x0)
            (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
               (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
                  (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_false
                     (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_Original_LF__DOT__Basics_LF_Basics_true
                        (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Original_LF__DOT__Basics_LF_Basics_bool)))))
            imported_Original_LF__DOT__Basics_LF_Basics_true)
         imported_Original_LF__DOT__Basics_LF_Basics_false).
Proof.
  apply Build_Iso with
    (to := fun _ => imported_Original_LF__DOT__Poly_LF_Poly_fold__example1)
    (from := fun _ => Original.LF_DOT_Poly.LF.Poly.fold_example1).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply sUIPt.
Defined.

(* Now provide the rel_iso for this specific iso *)
Instance Original_LF__DOT__Poly_LF_Poly_fold__example1_iso : 
  rel_iso (relax_Iso_Ts_Ps fold_example1_prop_sprop_iso)
    Original.LF_DOT_Poly.LF.Poly.fold_example1 imported_Original_LF__DOT__Poly_LF_Poly_fold__example1.
Proof.
  unfold rel_iso, relax_Iso_Ts_Ps.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.fold_example1 := {}. 
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_fold__example1 := {}. 
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.fold_example1 Original_LF__DOT__Poly_LF_Poly_fold__example1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.fold_example1 Imported.Original_LF__DOT__Poly_LF_Poly_fold__example1 Original_LF__DOT__Poly_LF_Poly_fold__example1_iso := {}.
