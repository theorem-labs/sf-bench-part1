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

(* Prove that nat_to_imported preserves double *)
Fixpoint nat_to_imported_double_compat (n : nat) :
  nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n) = 
  Imported.Original_LF__DOT__Induction_LF_Induction_double (nat_to_imported n) :=
  match n with
  | O => Corelib.Init.Logic.eq_refl
  | S n' => 
    match nat_to_imported_double_compat n' in (_ = r)
    return (Imported.nat_S (Imported.nat_S (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n'))) =
            Imported.nat_S (Imported.nat_S r)) with
    | Corelib.Init.Logic.eq_refl => Corelib.Init.Logic.eq_refl
    end
  end.

Instance Original_LF__DOT__Induction_LF_Induction_double_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Induction.LF.Induction.double x1) (imported_Original_LF__DOT__Induction_LF_Induction_double x2).
Proof.
  unfold rel_iso. simpl.
  intros x1 x2 H12.
  eapply eq_trans.
  - apply seq_of_eq. apply nat_to_imported_double_compat.
  - apply f_equal. assumption.
Defined.

Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.double := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_double := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.double Original_LF__DOT__Induction_LF_Induction_double_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.double Imported.Original_LF__DOT__Induction_LF_Induction_double Original_LF__DOT__Induction_LF_Induction_double_iso := {}.