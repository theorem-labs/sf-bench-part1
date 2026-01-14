From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
From Stdlib Require Import Strings.String.
From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso.

(* Nat isomorphism *)
Fixpoint to_nat (n : Datatypes.nat) : Imported.mynat :=
  match n with
  | Datatypes.O => Imported.mynat_O
  | Datatypes.S n' => Imported.mynat_S (to_nat n')
  end.

Fixpoint from_nat (n : Imported.mynat) : Datatypes.nat :=
  match n with
  | Imported.mynat_O => Datatypes.O
  | Imported.mynat_S n' => Datatypes.S (from_nat n')
  end.

Lemma to_from_nat : forall n, IsomorphismDefinitions.eq (to_nat (from_nat n)) n.
Proof.
  fix to_from 1.
  intros n.
  destruct n; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply (IsoEq.f_equal Imported.mynat_S). apply to_from.
Qed.

Lemma from_to_nat : forall n, IsomorphismDefinitions.eq (from_nat (to_nat n)) n.
Proof.
  fix from_to 1.
  intros n.
  destruct n; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply (IsoEq.f_equal Datatypes.S). apply from_to.
Qed.

Definition imported_Original_LF__DOT__Imp_LF_Imp_aexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_aexp.

Fixpoint aexp_to_imported (a : Original.LF_DOT_Imp.LF.Imp.aexp) : imported_Original_LF__DOT__Imp_LF_Imp_aexp :=
  match a with
  | Original.LF_DOT_Imp.LF.Imp.ANum n => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum (to_nat n)
  | Original.LF_DOT_Imp.LF.Imp.AId x => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId (string_to_String_string x)
  | Original.LF_DOT_Imp.LF.Imp.APlus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMinus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMult a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult (aexp_to_imported a1) (aexp_to_imported a2)
  end.

Fixpoint aexp_from_imported (a : imported_Original_LF__DOT__Imp_LF_Imp_aexp) : Original.LF_DOT_Imp.LF.Imp.aexp :=
  match a with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum n => Original.LF_DOT_Imp.LF.Imp.ANum (from_nat n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId x => Original.LF_DOT_Imp.LF.Imp.AId (String_string_to_string x)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus a1 a2 => Original.LF_DOT_Imp.LF.Imp.APlus (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMinus (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMult (aexp_from_imported a1) (aexp_from_imported a2)
  end.

Instance Original_LF__DOT__Imp_LF_Imp_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aexp imported_Original_LF__DOT__Imp_LF_Imp_aexp.
Proof.
  unshelve eapply Build_Iso.
  - exact aexp_to_imported.
  - exact aexp_from_imported.
  - fix to_from 1. intro a. destruct a; simpl.
    + apply (IsoEq.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum). apply to_from_nat.
    + apply (IsoEq.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId). apply (@IsomorphismDefinitions.to_from _ _ String_string_iso).
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus); apply to_from.
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus); apply to_from.
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult); apply to_from.
  - fix from_to 1. intro a. destruct a; simpl.
    + apply (IsoEq.f_equal Original.LF_DOT_Imp.LF.Imp.ANum). apply from_to_nat.
    + apply (IsoEq.f_equal Original.LF_DOT_Imp.LF.Imp.AId). apply (@IsomorphismDefinitions.from_to _ _ String_string_iso).
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.APlus); apply from_to.
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.AMinus); apply from_to.
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.AMult); apply from_to.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aexp := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aexp := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aexp Imported.Original_LF__DOT__Imp_LF_Imp_aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.