From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso Isomorphisms.nat__iso Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__U_some__iso.

Monomorphic Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_nat -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error.

(* Helper lemma: nth_error commutes with the isomorphism *)
Lemma nth_error_commutes :
  forall (l : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (n : nat),
  Logic.eq 
    (natoption_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.nth_error l n))
    (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error (natlist_to_imported l) (nat_to_imported n)).
Proof.
  intros l.
  induction l as [| h t IH]; intros n.
  - (* nil case *)
    destruct n; reflexivity.
  - (* cons case *)
    destruct n as [| n'].
    + (* n = 0 *)
      simpl. reflexivity.
    + (* n = S n' *)
      simpl. apply IH.
Defined.

Monomorphic Instance Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso (Original.LF_DOT_Lists.LF.Lists.NatList.nth_error x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  constructor.
  unfold imported_Original_LF__DOT__Lists_LF_Lists_NatList_nth__error.
  unfold Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso.
  simpl.
  pose proof (seq_of_eq (nth_error_commutes x1 x3)) as Hcomm.
  pose proof (f_equal2 Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error (proj_rel_iso H1) (proj_rel_iso H2)) as Harg.
  apply (eq_trans Hcomm Harg).
Defined.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.nth_error := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.nth_error Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.nth_error Imported.Original_LF__DOT__Lists_LF_Lists_NatList_nth__error Original_LF__DOT__Lists_LF_Lists_NatList_nth__error_iso := {}.