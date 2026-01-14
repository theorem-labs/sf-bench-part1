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

(* We need to show: nat_to_imported (double n) = Imported.double (nat_to_imported n) *)
(* when nat_to_imported n = x2, we need nat_to_imported (double n) = Imported.double x2 *)

(* First, prove that the two double functions commute with the isomorphism *)
Lemma double_commutes : forall n : nat,
  IsomorphismDefinitions.eq 
    (nat_to_imported (Original.LF_DOT_Induction.LF.Induction.double n))
    (Imported.Original_LF__DOT__Induction_LF_Induction_double (nat_to_imported n)).
Proof.
  fix IH 1.
  intros n.
  destruct n as [|n'].
  - (* n = O: double O = O on both sides *)
    simpl.
    apply IsomorphismDefinitions.eq_refl.
  - (* n = S n': double (S n') = S (S (double n')) *)
    simpl.
    (* LHS: nat_S (nat_S (nat_to_imported (double n'))) *)
    (* RHS: Imported.double (nat_S (nat_to_imported n')) *)
    (* By IH: nat_to_imported (double n') = Imported.double (nat_to_imported n') *)
    apply (IsoEq.f_equal (fun x => Imported.nat_S (Imported.nat_S x)) (IH n')).
Defined.

Instance Original_LF__DOT__Induction_LF_Induction_double_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Induction.LF.Induction.double x1) (imported_Original_LF__DOT__Induction_LF_Induction_double x2).
Proof.
  intros x1 x2 H.
  unfold rel_iso, imported_Original_LF__DOT__Induction_LF_Induction_double in *.
  simpl in *.
  (* H : nat_to_imported x1 = x2 *)
  (* Goal : nat_to_imported (double x1) = Imported.double x2 *)
  apply (IsoEq.eq_trans (double_commutes x1)).
  apply (IsoEq.f_equal Imported.Original_LF__DOT__Induction_LF_Induction_double H).
Defined.

Instance: KnownConstant Original.LF_DOT_Induction.LF.Induction.double := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Induction_LF_Induction_double := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.double Original_LF__DOT__Induction_LF_Induction_double_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.double Imported.Original_LF__DOT__Induction_LF_Induction_double Original_LF__DOT__Induction_LF_Induction_double_iso := {}.