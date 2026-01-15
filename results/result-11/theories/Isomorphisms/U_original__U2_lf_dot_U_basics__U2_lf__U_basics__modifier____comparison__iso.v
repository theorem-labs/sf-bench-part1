From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__modifier__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_modifier__comparison : imported_Original_LF__DOT__Basics_LF_Basics_modifier -> imported_Original_LF__DOT__Basics_LF_Basics_modifier -> imported_Original_LF__DOT__Basics_LF_Basics_comparison := Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison.

Lemma modifier_comparison_iso_helper : forall m1 m2,
  IsomorphismDefinitions.eq
    (comparison_to (Original.LF_DOT_Basics.LF.Basics.modifier_comparison m1 m2))
    (Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison 
       (modifier_to m1) (modifier_to m2)).
Proof.
  intros m1 m2.
  destruct m1; destruct m2; simpl; apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.modifier) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_modifier),
  rel_iso Original_LF__DOT__Basics_LF_Basics_modifier_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.modifier) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_modifier),
  rel_iso Original_LF__DOT__Basics_LF_Basics_modifier_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_comparison_iso (Original.LF_DOT_Basics.LF.Basics.modifier_comparison x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_modifier__comparison x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  destruct H12 as [H12']. destruct H34 as [H34'].
  simpl in *. constructor. destruct H12'. destruct H34'.
  apply modifier_comparison_iso_helper.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.modifier_comparison := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.modifier_comparison Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.modifier_comparison Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso := {}.