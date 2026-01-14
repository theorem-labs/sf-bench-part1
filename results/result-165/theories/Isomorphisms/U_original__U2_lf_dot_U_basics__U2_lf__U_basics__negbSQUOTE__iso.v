From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_negb' : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_negb'.

Lemma negb'_iso_lemma : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool),
  IsomorphismDefinitions.eq 
    (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.negb' x1))
    (Imported.Original_LF__DOT__Basics_LF_Basics_negb' (bool_to_imported x1)).
Proof.
  intros x1.
  destruct x1; simpl; apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Original_LF__DOT__Basics_LF_Basics_negb'_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.negb' x1) (imported_Original_LF__DOT__Basics_LF_Basics_negb' x2).
Proof.
  intros x1 x2 Hrel.
  unfold rel_iso in *.
  simpl in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_negb'.
  (* Hrel : eq (bool_to_imported x1) x2 *)
  (* Goal : eq (bool_to_imported (negb' x1)) (negb' x2) *)
  pose proof (negb'_iso_lemma x1) as H.
  (* H : eq (bool_to_imported (negb' x1)) (negb' (bool_to_imported x1)) *)
  (* We need to use that x2 = bool_to_imported x1 (from Hrel) *)
  eapply eq_trans.
  - exact H.
  - apply f_equal. exact Hrel.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.negb' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_negb' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.negb' Original_LF__DOT__Basics_LF_Basics_negb'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.negb' Imported.Original_LF__DOT__Basics_LF_Basics_negb' Original_LF__DOT__Basics_LF_Basics_negb'_iso := {}.