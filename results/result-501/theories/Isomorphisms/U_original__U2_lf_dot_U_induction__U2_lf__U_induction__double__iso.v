From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Induction_LF_Induction_double : imported_nat -> imported_nat := Imported.Original_LF__DOT__Induction_LF_Induction_double.

(* Define nat_to_imported using the isomorphism *)
Definition nat_to_imported : nat -> imported_nat := to nat_iso.

(* Prove that double commutes with the isomorphism *)
Lemma double_commutes : forall n : nat,
  IsomorphismDefinitions.eq 
    (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n))
    (imported_Original_LF__DOT__Induction_LF_Induction_double (nat_to_imported n)).
Proof.
  fix IH 1.
  intro n. destruct n as [|n'].
  { apply IsomorphismDefinitions.eq_refl. }
  { unfold imported_Original_LF__DOT__Induction_LF_Induction_double.
    simpl Original.LF_DOT_Induction.LF.Induction.double.
    unfold nat_to_imported. simpl to.
    (* LHS: nat_S (nat_S (to nat_iso (double n')))
       RHS: Imported.Original... (nat_S (to nat_iso n')) *)
    (* By IH: to nat_iso (double n') = Imported.Original... (to nat_iso n') *)
    pose proof (IH n') as H.
    unfold imported_Original_LF__DOT__Induction_LF_Induction_double in H.
    unfold nat_to_imported in H.
    apply (IsoEq.f_equal (fun x => Imported.nat_S (Imported.nat_S x))). exact H. }
Qed.

Instance Original_LF__DOT__Induction_LF_Induction_double_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Induction.LF.Induction.double x1) (imported_Original_LF__DOT__Induction_LF_Induction_double x2).
Proof.
  intros x1 x2 H.
  unfold rel_iso in *. simpl in *.
  (* H : IsomorphismDefinitions.eq (to nat_iso x1) x2 *)
  pose proof (double_commutes x1) as Hdc.
  unfold imported_Original_LF__DOT__Induction_LF_Induction_double in *.
  unfold nat_to_imported in Hdc.
  destruct H.
  (* Goal : IsomorphismDefinitions.eq (to nat_iso (double x1)) (Imported... (to nat_iso x1)) *)
  exact Hdc.
Qed.
Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.double := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_double := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.double Original_LF__DOT__Induction_LF_Induction_double_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.double Imported.Original_LF__DOT__Induction_LF_Induction_double Original_LF__DOT__Induction_LF_Induction_double_iso := {}.