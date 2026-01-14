From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__modifier__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_modifier__comparison : imported_Original_LF__DOT__Basics_LF_Basics_modifier -> imported_Original_LF__DOT__Basics_LF_Basics_modifier -> imported_Original_LF__DOT__Basics_LF_Basics_comparison := Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison.

(* We need to prove that:
   rel_iso comparison_iso (modifier_comparison x1 x3) (imported_modifier_comparison x2 x4)
   given rel_iso modifier_iso x1 x2 and rel_iso modifier_iso x3 x4
   
   rel_iso is defined as eq (to x) y, so we have:
   - eq (modifier_to x1) x2
   - eq (modifier_to x3) x4
   And we need: eq (comparison_to (modifier_comparison x1 x3)) (imported_modifier_comparison x2 x4)
   
   Since modifier_to x1 = x2 and modifier_to x3 = x4, we can substitute and show that
   comparison_to (modifier_comparison x1 x3) = imported_modifier_comparison (modifier_to x1) (modifier_to x3)
*)

(* Helper lemma: the two functions are compatible under the isomorphisms *)
Lemma modifier_comparison_compat : forall (x1 x3 : Original.LF_DOT_Basics.LF.Basics.modifier),
  IsomorphismDefinitions.eq 
    (comparison_to (Original.LF_DOT_Basics.LF.Basics.modifier_comparison x1 x3))
    (Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison (modifier_to x1) (modifier_to x3)).
Proof.
  intros x1 x3.
  destruct x1, x3; simpl; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.modifier) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_modifier),
  rel_iso Original_LF__DOT__Basics_LF_Basics_modifier_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.modifier) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_modifier),
  rel_iso Original_LF__DOT__Basics_LF_Basics_modifier_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_comparison_iso (Original.LF_DOT_Basics.LF.Basics.modifier_comparison x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_modifier__comparison x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in *.
  simpl in *.
  (* H12 : eq (modifier_to x1) x2 *)
  (* H34 : eq (modifier_to x3) x4 *)
  (* Goal: eq (comparison_to (modifier_comparison x1 x3)) (imported_modifier_comparison x2 x4) *)
  
  (* Use f_equal2 to get eq on the imported function, then use transitivity with compat *)
  pose proof (IsoEq.f_equal2 Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison H12 H34) as Hf.
  apply (IsoEq.eq_trans (modifier_comparison_compat x1 x3) Hf).
Qed.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.modifier_comparison := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.modifier_comparison Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.modifier_comparison Imported.Original_LF__DOT__Basics_LF_Basics_modifier__comparison Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso := {}.