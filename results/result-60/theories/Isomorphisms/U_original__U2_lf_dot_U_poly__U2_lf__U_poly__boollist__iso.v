From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_boollist : Type := Imported.Original_LF__DOT__Poly_LF_Poly_boollist.

(* Helper: convert bool *)
Definition bool_to_imported (b : Original.LF_DOT_Basics.LF.Basics.bool) : Imported.Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original.LF_DOT_Basics.LF.Basics.true => Imported.Original_LF__DOT__Basics_LF_Basics_bool_true
  | Original.LF_DOT_Basics.LF.Basics.false => Imported.Original_LF__DOT__Basics_LF_Basics_bool_false
  end.

Definition bool_from_imported (b : Imported.Original_LF__DOT__Basics_LF_Basics_bool) : Original.LF_DOT_Basics.LF.Basics.bool :=
  match b with
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Original.LF_DOT_Basics.LF.Basics.true
  | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Original.LF_DOT_Basics.LF.Basics.false
  end.

(* Convert boollist *)
Fixpoint boollist_to_imported (l : Original.LF_DOT_Poly.LF.Poly.boollist) : imported_Original_LF__DOT__Poly_LF_Poly_boollist :=
  match l with
  | Original.LF_DOT_Poly.LF.Poly.bool_nil => Imported.Original_LF__DOT__Poly_LF_Poly_boollist_bool_nil
  | Original.LF_DOT_Poly.LF.Poly.bool_cons b t => Imported.Original_LF__DOT__Poly_LF_Poly_boollist_bool_cons (bool_to_imported b) (boollist_to_imported t)
  end.

Fixpoint boollist_from_imported (l : imported_Original_LF__DOT__Poly_LF_Poly_boollist) : Original.LF_DOT_Poly.LF.Poly.boollist :=
  match l with
  | Imported.Original_LF__DOT__Poly_LF_Poly_boollist_bool_nil => Original.LF_DOT_Poly.LF.Poly.bool_nil
  | Imported.Original_LF__DOT__Poly_LF_Poly_boollist_bool_cons b t => Original.LF_DOT_Poly.LF.Poly.bool_cons (bool_from_imported b) (boollist_from_imported t)
  end.

Lemma boollist_to_from : forall x, IsomorphismDefinitions.eq (boollist_to_imported (boollist_from_imported x)) x.
Proof.
  fix IH 1.
  intro x.
  destruct x as [| b rest].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    destruct b; apply IsoEq.f_equal; apply IH.
Qed.

Lemma boollist_from_to : forall x, IsomorphismDefinitions.eq (boollist_from_imported (boollist_to_imported x)) x.
Proof.
  fix IH 1.
  intro x.
  destruct x as [| b rest].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    destruct b; apply IsoEq.f_equal; apply IH.
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_boollist_iso : Iso Original.LF_DOT_Poly.LF.Poly.boollist imported_Original_LF__DOT__Poly_LF_Poly_boollist.
Proof.
  apply Build_Iso with
    (to := boollist_to_imported)
    (from := boollist_from_imported).
  - exact boollist_to_from.
  - exact boollist_from_to.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.boollist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_boollist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.boollist Original_LF__DOT__Poly_LF_Poly_boollist_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.boollist Imported.Original_LF__DOT__Poly_LF_Poly_boollist Original_LF__DOT__Poly_LF_Poly_boollist_iso := {}.
