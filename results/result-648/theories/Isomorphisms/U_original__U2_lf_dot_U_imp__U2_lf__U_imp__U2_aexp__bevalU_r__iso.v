From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Isomorphisms.bool__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp -> imported_bool -> SProp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_bevalR.

(* Both bevalR definitions are empty inductives (no constructors), so they're both uninhabited.
   We construct an isomorphism manually using the fact that both types are empty. *)

Instance Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso : (forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp)
     (_ : @rel_iso Original.LF_DOT_Imp.LF.Imp.AExp.bexp imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso x1 x2) (x3 : bool) (x4 : imported_bool)
     (_ : @rel_iso bool imported_bool bool_iso x3 x4),
   Iso (Original.LF_DOT_Imp.LF.Imp.AExp.bevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR x2 x4)).
Proof.
  intros x1 x2 Hx12 x3 x4 Hx34.
  (* Both are empty inductive types - bevalR has no constructors *)
  unshelve econstructor;
  intro H; destruct H.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.bevalR := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_bevalR := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.bevalR Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.bevalR Imported.Original_LF__DOT__Imp_LF_Imp_AExp_bevalR Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso := {}.
