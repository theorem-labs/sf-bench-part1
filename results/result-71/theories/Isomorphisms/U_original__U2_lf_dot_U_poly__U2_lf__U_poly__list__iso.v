From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* (* (*  *) *) *) (* for speed *)

Definition imported_Original_LF__DOT__Poly_LF_Poly_list : Type -> Type := 
  Imported.Original_LF__DOT__Poly_LF_Poly_list.

Fixpoint list_to_imported {A B : Type} (iso_elem : Iso A B) (l : Original.LF_DOT_Poly.LF.Poly.list A) : imported_Original_LF__DOT__Poly_LF_Poly_list B :=
  match l with
  | Original.LF_DOT_Poly.LF.Poly.nil => Imported.Original_LF__DOT__Poly_LF_Poly_list_nil B
  | Original.LF_DOT_Poly.LF.Poly.cons h t => 
      Imported.Original_LF__DOT__Poly_LF_Poly_list_cons B (to iso_elem h) (list_to_imported iso_elem t)
  end.

Fixpoint list_from_imported {A B : Type} (iso_elem : Iso A B) (l : imported_Original_LF__DOT__Poly_LF_Poly_list B) : Original.LF_DOT_Poly.LF.Poly.list A :=
  match l with
  | Imported.Original_LF__DOT__Poly_LF_Poly_list_nil _ => Original.LF_DOT_Poly.LF.Poly.nil
  | Imported.Original_LF__DOT__Poly_LF_Poly_list_cons _ h t => 
      Original.LF_DOT_Poly.LF.Poly.cons (from iso_elem h) (list_from_imported iso_elem t)
  end.

Lemma list_to_from {A B : Type} (iso_elem : Iso A B) :
  forall l, IsomorphismDefinitions.eq (list_to_imported iso_elem (list_from_imported iso_elem l)) l.
Proof.
  fix IH 1.
  intro l; destruct l as [|h t].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    pose proof (to_from iso_elem h) as Hh.
    pose proof (IH t) as Ht.
    exact (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons B) Hh Ht).
Defined.

Lemma list_from_to {A B : Type} (iso_elem : Iso A B) :
  forall l, IsomorphismDefinitions.eq (list_from_imported iso_elem (list_to_imported iso_elem l)) l.
Proof.
  fix IH 1.
  intro l; destruct l as [|h t].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    pose proof (from_to iso_elem h) as Hh.
    pose proof (IH t) as Ht.
    exact (IsoEq.f_equal2 (Original.LF_DOT_Poly.LF.Poly.cons) Hh Ht).
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_list_iso : forall x1 x2 : Type, Iso x1 x2 -> 
  Iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2).
Proof.
  intros x1 x2 hx.
  apply Build_Iso with 
    (to := list_to_imported hx) 
    (from := list_from_imported hx).
  - apply list_to_from.
  - apply list_from_to.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.list := {}.
Instance: KnownConstant imported_Original_LF__DOT__Poly_LF_Poly_list := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.list Original_LF__DOT__Poly_LF_Poly_list_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.list imported_Original_LF__DOT__Poly_LF_Poly_list Original_LF__DOT__Poly_LF_Poly_list_iso := {}.
