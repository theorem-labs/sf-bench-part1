From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat : imported_nat -> imported_nat -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat.

(* Prove that repeat preserves the isomorphism *)
Fixpoint repeat_compat (n count : nat) {struct count} :
  Logic.eq (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat (nat_to_imported n) (nat_to_imported count))
           (natlist_to_imported (Original.LF_DOT_Lists.LF.Lists.NatList.repeat n count)) :=
  match count with
  | O => Corelib.Init.Logic.eq_refl
  | S count' => 
      match repeat_compat n count' in (_ = r)
            return (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons 
                      (nat_to_imported n) 
                      (Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat (nat_to_imported n) (nat_to_imported count')) =
                    Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist_cons (nat_to_imported n) r)
      with
      | Corelib.Init.Logic.eq_refl => Corelib.Init.Logic.eq_refl
      end
  end.

Instance Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso (Original.LF_DOT_Lists.LF.Lists.NatList.repeat x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso, imported_Original_LF__DOT__Lists_LF_Lists_NatList_repeat in *.
  simpl in *.
  destruct H12. destruct H34.
  pose proof (repeat_compat x1 x3) as Hcompat.
  apply seq_of_eq.
  apply Logic.eq_sym.
  exact Hcompat.
Defined.

Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.repeat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.repeat Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.repeat Imported.Original_LF__DOT__Lists_LF_Lists_NatList_repeat Original_LF__DOT__Lists_LF_Lists_NatList_repeat_iso := {}.