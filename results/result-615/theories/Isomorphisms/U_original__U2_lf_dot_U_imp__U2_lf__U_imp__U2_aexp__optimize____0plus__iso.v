From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus.

(* Helper lemma: if x2 = aexp_to_imported x1, then optimize_0plus results are also related *)
Lemma optimize_0plus_related : forall x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp,
  IsomorphismDefinitions.eq 
    (aexp_to_imported (Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus x1))
    (Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus (aexp_to_imported x1)).
Proof.
  intro x1.
  induction x1 as [n | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2].
  - (* ANum *)
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* APlus *)
    simpl.
    destruct e1 as [n1 | e1a e1b | e1a e1b | e1a e1b].
    + (* APlus (ANum n1) e2 *)
      destruct n1 as [|n1'].
      * (* n1 = 0, so optimize_0plus (APlus (ANum 0) e2) = optimize_0plus e2 *)
        simpl. exact IH2.
      * (* n1 = S n1', so we apply APlus recursively *)
        simpl.
        unfold Imported.Original_LF__DOT__Imp_LF_Imp_AExp_APlus.
        apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aexp_APlus).
        -- simpl in IH1. exact IH1.
        -- exact IH2.
    + (* APlus (APlus e1a e1b) e2 *)
      simpl.
      unfold Imported.Original_LF__DOT__Imp_LF_Imp_AExp_APlus.
      apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aexp_APlus).
      -- exact IH1.
      -- exact IH2.
    + (* APlus (AMinus e1a e1b) e2 *)
      simpl.
      unfold Imported.Original_LF__DOT__Imp_LF_Imp_AExp_APlus.
      apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aexp_APlus).
      -- exact IH1.
      -- exact IH2.
    + (* APlus (AMult e1a e1b) e2 *)
      simpl.
      unfold Imported.Original_LF__DOT__Imp_LF_Imp_AExp_APlus.
      apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aexp_APlus).
      -- exact IH1.
      -- exact IH2.
  - (* AMinus *)
    simpl.
    apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aexp_AMinus).
    -- exact IH1.
    -- exact IH2.
  - (* AMult *)
    simpl.
    apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aexp_AMult).
    -- exact IH1.
    -- exact IH2.
Qed.

Instance Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2 ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso (Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus x1) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus x2).
Proof.
  intros x1 x2 H.
  unfold rel_iso in *.
  simpl in *.
  (* H : IsomorphismDefinitions.eq (aexp_to_imported x1) x2 *)
  (* Goal : IsomorphismDefinitions.eq (aexp_to_imported (optimize_0plus x1)) (imported_... (aexp_to_imported x1)) after transport *)
  pose proof (optimize_0plus_related x1) as Hrel.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus.
  (* Need to transport along H *)
  apply (IsoEq.eq_trans Hrel).
  apply (IsoEq.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus H).
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus Imported.Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus_iso := {}.