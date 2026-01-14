From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_minustwo : imported_nat -> imported_nat := Imported.Original_LF__DOT__Basics_LF_Basics_minustwo.

(* Prove that minustwo commutes with the nat isomorphism *)
Lemma nat_to_imported_minustwo_compat (n : nat) :
  nat_to_imported (Original.LF_DOT_Basics.LF.Basics.minustwo n) = 
  Imported.Original_LF__DOT__Basics_LF_Basics_minustwo (nat_to_imported n).
Proof.
  destruct n as [|[|n']]; reflexivity.
Defined.

Instance Original_LF__DOT__Basics_LF_Basics_minustwo_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Basics.LF.Basics.minustwo x1) (imported_Original_LF__DOT__Basics_LF_Basics_minustwo x2).
Proof.
  unfold rel_iso. simpl.
  intros x1 x2 H12.
  (* H12 : eq (nat_to_imported x1) x2 *)
  (* Goal : eq (nat_to_imported (minustwo x1)) (Imported_Original_LF__DOT__Basics_LF_Basics_minustwo x2) *)
  eapply eq_trans.
  - apply seq_of_eq. apply nat_to_imported_minustwo_compat.
  - apply f_equal. assumption.
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.minustwo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_minustwo := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.minustwo Original_LF__DOT__Basics_LF_Basics_minustwo_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.minustwo Imported.Original_LF__DOT__Basics_LF_Basics_minustwo Original_LF__DOT__Basics_LF_Basics_minustwo_iso := {}.