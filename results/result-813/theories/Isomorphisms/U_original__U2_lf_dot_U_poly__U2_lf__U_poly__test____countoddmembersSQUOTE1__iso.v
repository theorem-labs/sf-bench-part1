From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__countoddmembersSQUOTE__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_countoddmembers'
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
          (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_0
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S imported_0))))
                      (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))
                         (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))))))
    (imported_S (imported_S (imported_S (imported_S imported_0)))) := Imported.Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Instance Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Poly_LF_Poly_countoddmembers'_iso
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso _0_iso
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))))))
       (S_iso (S_iso (S_iso (S_iso _0_iso)))))
    Original.LF_DOT_Poly.LF.Poly.test_countoddmembers'1 imported_Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1.
Proof.
  (* rel_iso for this Prop-to-SProp case needs an eq proof *)
  unfold rel_iso.
  (* The Iso applied to the Original gives us the imported version *)
  (* Since both are Props and are inhabited (the theorems are admitted), we can use eq_refl *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_countoddmembers'1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_countoddmembers'1 Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_countoddmembers'1 Imported.Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1 Original_LF__DOT__Poly_LF_Poly_test__countoddmembers'1_iso := {}.
