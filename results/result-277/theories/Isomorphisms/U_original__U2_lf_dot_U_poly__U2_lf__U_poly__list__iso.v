From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Poly_LF_Poly_list : Type -> Type := Imported.Original_LF__DOT__Poly_LF_Poly_list.

Fixpoint list_to_imported {x1 x2 : Type} (Hx : Iso x1 x2) (l : Original.LF_DOT_Poly.LF.Poly.list x1) : imported_Original_LF__DOT__Poly_LF_Poly_list x2 :=
  match l with
  | Original.LF_DOT_Poly.LF.Poly.nil => Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2
  | Original.LF_DOT_Poly.LF.Poly.cons h t => 
      Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (to Hx h) (list_to_imported Hx t)
  end.

Fixpoint list_from_imported {x1 x2 : Type} (Hx : Iso x1 x2) (l : imported_Original_LF__DOT__Poly_LF_Poly_list x2) : Original.LF_DOT_Poly.LF.Poly.list x1 :=
  match l with
  | Imported.Original_LF__DOT__Poly_LF_Poly_list_nil _ => Original.LF_DOT_Poly.LF.Poly.nil
  | Imported.Original_LF__DOT__Poly_LF_Poly_list_cons _ h t => 
      Original.LF_DOT_Poly.LF.Poly.cons (from Hx h) (list_from_imported Hx t)
  end.

Lemma list_to_from : forall {x1 x2 : Type} (Hx : Iso x1 x2) (l : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  IsomorphismDefinitions.eq (list_to_imported Hx (list_from_imported Hx l)) l.
Proof.
  intros x1 x2 Hx l.
  induction l as [|h t IH].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2) (to_from Hx h) IH).
Qed.

Lemma list_from_to : forall {x1 x2 : Type} (Hx : Iso x1 x2) (l : Original.LF_DOT_Poly.LF.Poly.list x1),
  IsomorphismDefinitions.eq (list_from_imported Hx (list_to_imported Hx l)) l.
Proof.
  intros x1 x2 Hx l.
  induction l as [|h t IH].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (IsoEq.f_equal2 (@Original.LF_DOT_Poly.LF.Poly.cons x1) (from_to Hx h) IH).
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_list_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) :=
  fun x1 x2 Hx => Build_Iso (list_to_imported Hx) (list_from_imported Hx) (list_to_from Hx) (list_from_to Hx).

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.list := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_list := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.list Original_LF__DOT__Poly_LF_Poly_list_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.list Imported.Original_LF__DOT__Poly_LF_Poly_list Original_LF__DOT__Poly_LF_Poly_list_iso := {}.