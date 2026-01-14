From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_even : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_even.

(* Prove that even commutes with the isomorphism *)
Lemma even_commutes : forall n : nat,
  IsomorphismDefinitions.eq 
    (bool_to_imported (Original.LF_DOT_Basics.LF.Basics.even n))
    (imported_Original_LF__DOT__Basics_LF_Basics_even (nat_to_imported n)).
Proof.
  fix IH 1.
  intro n. destruct n as [|n'].
  { (* n = 0: even 0 = true *)
    apply IsomorphismDefinitions.eq_refl. }
  { destruct n' as [|n''].
    { (* n = 1: even 1 = false *)
      apply IsomorphismDefinitions.eq_refl. }
    { (* n = S (S n''): even (S (S n'')) = even n'' *)
      simpl Original.LF_DOT_Basics.LF.Basics.even.
      simpl nat_to_imported.
      unfold imported_Original_LF__DOT__Basics_LF_Basics_even.
      (* LHS: bool_to_imported (even n'')
         RHS: Imported.Original... (nat_S (nat_S (nat_to_imported n''))) *)
      pose proof (IH n'') as H.
      unfold imported_Original_LF__DOT__Basics_LF_Basics_even in H.
      exact H. } }
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_even_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.even x1) (imported_Original_LF__DOT__Basics_LF_Basics_even x2).
Proof.
  intros x1 x2 H.
  unfold rel_iso in *. simpl in *.
  pose proof (even_commutes x1) as Hec.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_even in *.
  destruct H.
  exact Hec.
Qed.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.even Original_LF__DOT__Basics_LF_Basics_even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.even Imported.Original_LF__DOT__Basics_LF_Basics_even Original_LF__DOT__Basics_LF_Basics_even_iso := {}.