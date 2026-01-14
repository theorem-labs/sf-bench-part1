From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import String Ascii.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso.

(* Helper to convert standard equality to SProp equality *)
Lemma prop_to_sprop_eq_aexp : forall {A : Type} (a b : A), a = b -> IsomorphismDefinitions.eq a b.
Proof. intros A a b H. subst b. exact IsomorphismDefinitions.eq_refl. Qed.

(* Now we can define the aexp isomorphism *)

Fixpoint aexp_to_imported (a : Original.LF_DOT_Imp.LF.Imp.aexp) : Imported.Original_LF__DOT__Imp_LF_Imp_aexp :=
  match a with
  | Original.LF_DOT_Imp.LF.Imp.ANum n => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum (nat_to_imported n)
  | Original.LF_DOT_Imp.LF.Imp.AId s => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId (string_to_imported s)
  | Original.LF_DOT_Imp.LF.Imp.APlus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMinus a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.AMult a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult (aexp_to_imported a1) (aexp_to_imported a2)
  end.

Fixpoint imported_to_aexp (a : Imported.Original_LF__DOT__Imp_LF_Imp_aexp) : Original.LF_DOT_Imp.LF.Imp.aexp :=
  match a with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_ANum n => Original.LF_DOT_Imp.LF.Imp.ANum (imported_to_nat n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AId s => Original.LF_DOT_Imp.LF.Imp.AId (imported_to_string s)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_APlus a1 a2 => Original.LF_DOT_Imp.LF.Imp.APlus (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMinus a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMinus (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aexp_AMult a1 a2 => Original.LF_DOT_Imp.LF.Imp.AMult (imported_to_aexp a1) (imported_to_aexp a2)
  end.

Lemma aexp_roundtrip1 : forall a, imported_to_aexp (aexp_to_imported a) = a.
Proof.
  fix IH 1. intros a. destruct a; simpl.
  - f_equal. apply nat_roundtrip.
  - f_equal. apply string_roundtrip1.
  - f_equal; apply IH.
  - f_equal; apply IH.
  - f_equal; apply IH.
Qed.

Lemma aexp_roundtrip2 : forall a, aexp_to_imported (imported_to_aexp a) = a.
Proof.
  fix IH 1. intros a. destruct a; simpl.
  - f_equal. apply imported_nat_roundtrip.
  - f_equal. apply string_roundtrip2.
  - f_equal; apply IH.
  - f_equal; apply IH.
  - f_equal; apply IH.
Qed.

Definition imported_Original_LF__DOT__Imp_LF_Imp_aexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_aexp.
Instance Original_LF__DOT__Imp_LF_Imp_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aexp imported_Original_LF__DOT__Imp_LF_Imp_aexp.
Proof.
  exists aexp_to_imported imported_to_aexp.
  - intro a. apply prop_to_sprop_eq_aexp. apply aexp_roundtrip2.
  - intro a. apply prop_to_sprop_eq_aexp. apply aexp_roundtrip1.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aexp := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aexp := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aexp Imported.Original_LF__DOT__Imp_LF_Imp_aexp Original_LF__DOT__Imp_LF_Imp_aexp_iso := {}.