From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__beval__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso Isomorphisms.bool__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound : forall x : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_AExp_beval (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b x)) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_beval x) := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound.

(* This is an isomorphism between two axioms. Both sides are equality proofs (SProp).
   We use the fact that for Prop/SProp propositions, the isomorphism can be constructed
   by showing both propositions are inhabited (which they are via the axioms). *)
Instance Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso x1 x2),
  rel_iso
    (Corelib_Init_Logic_eq_iso 
       (Original_LF__DOT__Imp_LF_Imp_AExp_beval_iso (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso hx))
       (Original_LF__DOT__Imp_LF_Imp_AExp_beval_iso hx))
    (Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_sound x1) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound x2).
Proof.
  intros x1 x2 hx.
  constructor. simpl.
  (* The goal is an equality in SProp. All SProp proofs are equal. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_sound := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_sound Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_sound Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__sound_iso := {}.
