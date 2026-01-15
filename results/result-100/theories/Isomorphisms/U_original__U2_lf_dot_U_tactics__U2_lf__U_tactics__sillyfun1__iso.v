From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Tactics_LF_Tactics_sillyfun1 : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun1.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__eqb__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__false__iso Isomorphisms.U_s__iso Isomorphisms.__0__iso.

Instance Original_LF__DOT__Tactics_LF_Tactics_sillyfun1_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Tactics.LF.Tactics.sillyfun1 x1) (imported_Original_LF__DOT__Tactics_LF_Tactics_sillyfun1 x2).
Proof.
  intros n1 n2 Hn.
  unfold Original.LF_DOT_Tactics.LF.Tactics.sillyfun1.
  unfold imported_Original_LF__DOT__Tactics_LF_Tactics_sillyfun1.
  unfold Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun1.
  (* Get the eqb comparison results *)
  assert (H3 : rel_iso nat_iso (S (S (S O))) (Imported.S (Imported.S (Imported.S Imported._0)))) by (repeat apply S_iso; apply _0_iso).
  assert (H5 : rel_iso nat_iso (S (S (S (S (S O))))) (Imported.S (Imported.S (Imported.S (Imported.S (Imported.S Imported._0)))))) by (repeat apply S_iso; apply _0_iso).
  pose proof (@Original_LF__DOT__Basics_LF_Basics_eqb_iso n1 n2 Hn (S (S (S O))) (Imported.S (Imported.S (Imported.S Imported._0))) H3) as Heqb3.
  pose proof (@Original_LF__DOT__Basics_LF_Basics_eqb_iso n1 n2 Hn (S (S (S (S (S O))))) (Imported.S (Imported.S (Imported.S (Imported.S (Imported.S Imported._0))))) H5) as Heqb5.
  destruct Heqb3 as [Heqb3]. destruct Heqb5 as [Heqb5].
  simpl in *.
  constructor. simpl.
  (* Case analysis on eqb n 3 *)
  destruct (Original.LF_DOT_Basics.LF.Basics.eqb n1 3) eqn:E1.
  - (* n =? 3 = true *)
    apply (@IsoEq.eq_srect_r _ (to Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.true)
      (fun b => IsomorphismDefinitions.eq (to Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.true)
        (Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1 _ b _ _))).
    + simpl. apply IsomorphismDefinitions.eq_refl.
    + exact (IsoEq.eq_sym Heqb3).
  - (* n =? 3 = false *)
    apply (@IsoEq.eq_srect_r _ (to Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.false)
      (fun b => IsomorphismDefinitions.eq 
        (to Original_LF__DOT__Basics_LF_Basics_bool_iso (if Original.LF_DOT_Basics.LF.Basics.eqb n1 5 then _ else _))
        (Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1 _ b _ _))).
    + simpl.
      destruct (Original.LF_DOT_Basics.LF.Basics.eqb n1 5) eqn:E2.
      * apply (@IsoEq.eq_srect_r _ (to Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.true)
          (fun b => IsomorphismDefinitions.eq (to Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.true)
            (Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1 _ b _ _))).
        -- simpl. apply IsomorphismDefinitions.eq_refl.
        -- exact (IsoEq.eq_sym Heqb5).
      * apply (@IsoEq.eq_srect_r _ (to Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.false)
          (fun b => IsomorphismDefinitions.eq (to Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.false)
            (Imported.Original_LF__DOT__Basics_LF_Basics_negb_match_1 _ b _ _))).
        -- simpl. apply IsomorphismDefinitions.eq_refl.
        -- exact (IsoEq.eq_sym Heqb5).
    + exact (IsoEq.eq_sym Heqb3).
Defined.
Instance: KnownConstant Original.LF_DOT_Tactics.LF.Tactics.sillyfun1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.sillyfun1 Original_LF__DOT__Tactics_LF_Tactics_sillyfun1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.sillyfun1 Imported.Original_LF__DOT__Tactics_LF_Tactics_sillyfun1 Original_LF__DOT__Tactics_LF_Tactics_sillyfun1_iso := {}.