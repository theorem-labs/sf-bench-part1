From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_app__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2 : imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
    (imported_Original_LF__DOT__IndProp_LF_IndProp_App (imported_Original_LF__DOT__IndProp_LF_IndProp_Char (imported_S imported_0))
       (imported_Original_LF__DOT__IndProp_LF_IndProp_Char (imported_S (imported_S imported_0)))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2.

(* reg_exp_ex2 is admitted in the original, so we use iso_SInhabited *)
Instance Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2_iso : rel_iso
    (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
       (Original_LF__DOT__IndProp_LF_IndProp_App_iso (Original_LF__DOT__IndProp_LF_IndProp_Char_iso (S_iso _0_iso)) (Original_LF__DOT__IndProp_LF_IndProp_Char_iso (S_iso (S_iso _0_iso)))))
    Original.LF_DOT_IndProp.LF.IndProp.reg_exp_ex2 imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2.
Proof.
  unfold rel_iso. simpl.
  (* The isomorphism for exp_match gives us an Iso between the types.
     Since reg_exp_ex2 is admitted on Original side, we have an axiom.
     Since we exported an axiom on the Lean side too, we need to show:
     to iso (Original.reg_exp_ex2) = Imported.reg_exp_ex2
     
     But both sides are axioms/admitted, so we use proof irrelevance style.
     The type exp_match is in SProp in the imported version. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.reg_exp_ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.reg_exp_ex2 Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.reg_exp_ex2 Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2 Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex2_iso := {}.
