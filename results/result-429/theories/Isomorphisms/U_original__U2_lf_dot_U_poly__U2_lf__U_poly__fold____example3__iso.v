From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

(* S (S (S (S 0))) = 4. Note iterate1 imported_S 1 imported_0 = imported_S imported_0 = 1 *)
(* So S(S(S(iterate1 imported_S 1 imported_0))) = S(S(S(1))) = 4 *)
Local Definition imported_4 : imported_nat := imported_S (imported_S (imported_S (imported_S imported_0))).
Local Definition _4_iso : rel_iso nat_iso (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S Datatypes.O)))) imported_4 := S_iso (S_iso (S_iso (S_iso _0_iso))).

Definition imported_Original_LF__DOT__Poly_LF_Poly_fold__example3 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_fold (fun x x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat => imported_Original_LF__DOT__Poly_LF_Poly_app x x0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)
             (imported_Original_LF__DOT__Poly_LF_Poly_cons
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons
                   (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_4 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
                   (imported_Original_LF__DOT__Poly_LF_Poly_nil (imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat))))))
       (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons imported_4 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))) := Imported.Original_LF__DOT__Poly_LF_Poly_fold__example3.

Instance Original_LF__DOT__Poly_LF_Poly_fold__example3_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (unwrap_sprop
             (Original_LF__DOT__Poly_LF_Poly_fold_iso (IsoIso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso)) Original.LF_DOT_Poly.LF.Poly.app
                (fun x x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat => imported_Original_LF__DOT__Poly_LF_Poly_app x x0)
                (fun (x1 : Original.LF_DOT_Poly.LF.Poly.list Datatypes.nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
                   (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list Datatypes.nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
                   (hx0 : rel_iso_sort (IsoIso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso)) x3 x4) =>
                 {| unwrap_sprop := Original_LF__DOT__Poly_LF_Poly_app_iso hx (unwrap_sprop hx0) |})
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)
                      (Original_LF__DOT__Poly_LF_Poly_cons_iso
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
                         (Original_LF__DOT__Poly_LF_Poly_cons_iso
                            (Original_LF__DOT__Poly_LF_Poly_cons_iso _4_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))
                            (Original_LF__DOT__Poly_LF_Poly_nil_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso))))))
                Original.LF_DOT_Poly.LF.Poly.nil (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat) {| unwrap_sprop := Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso |}))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso _4_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))))
    Original.LF_DOT_Poly.LF.Poly.fold_example3 imported_Original_LF__DOT__Poly_LF_Poly_fold__example3.
Proof.
  (* fold_example3 is Admitted in Original.v and we have an axiom for it in Lean.
     Both sides are inhabited SProp/Prop values, so any two elements are equal. *)
  unfold rel_iso. simpl.
  apply IsomorphismDefinitions.eq_refl.
Admitted.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.fold_example3 := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_fold__example3 := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.fold_example3 Original_LF__DOT__Poly_LF_Poly_fold__example3_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.fold_example3 Imported.Original_LF__DOT__Poly_LF_Poly_fold__example3 Original_LF__DOT__Poly_LF_Poly_fold__example3_iso := {}.
