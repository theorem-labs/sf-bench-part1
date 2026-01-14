From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Poly_LF_Poly_list' : Type -> Type := (@Imported.Original_LF__DOT__Poly_LF_Poly_list').

(* Forward direction: Original -> Imported *)
Fixpoint list'_to_imported {X1 X2 : Type} (f : X1 -> X2) (l : @Original.LF_DOT_Poly.LF.Poly.list' X1) : Imported.Original_LF__DOT__Poly_LF_Poly_list' X2 :=
  match l with
  | Original.LF_DOT_Poly.LF.Poly.nil' => Imported.Original_LF__DOT__Poly_LF_Poly_list'_nil' X2
  | Original.LF_DOT_Poly.LF.Poly.cons' x xs => Imported.Original_LF__DOT__Poly_LF_Poly_list'_cons' X2 (f x) (list'_to_imported f xs)
  end.

(* Backward direction: Imported -> Original *)
Fixpoint list'_from_imported {X1 X2 : Type} (g : X2 -> X1) (l : Imported.Original_LF__DOT__Poly_LF_Poly_list' X2) : @Original.LF_DOT_Poly.LF.Poly.list' X1 :=
  match l with
  | Imported.Original_LF__DOT__Poly_LF_Poly_list'_nil' _ => Original.LF_DOT_Poly.LF.Poly.nil'
  | Imported.Original_LF__DOT__Poly_LF_Poly_list'_cons' _ x xs => Original.LF_DOT_Poly.LF.Poly.cons' (g x) (list'_from_imported g xs)
  end.

(* Prove roundtrip properties *)
Lemma roundtrip_to_from : forall {X1 X2 : Type} (f : X1 -> X2) (g : X2 -> X1) 
  (Hgf : forall x, IsomorphismDefinitions.eq (g (f x)) x) 
  (l : @Original.LF_DOT_Poly.LF.Poly.list' X1),
  IsomorphismDefinitions.eq (list'_from_imported g (list'_to_imported f l)) l.
Proof.
  intros X1 X2 f g Hgf.
  fix IH 1.
  intros l.
  destruct l as [| x xs].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. 
    apply IsoEq.f_equal2.
    + apply Hgf.
    + apply IH.
Qed.

Lemma roundtrip_from_to : forall {X1 X2 : Type} (f : X1 -> X2) (g : X2 -> X1) 
  (Hfg : forall x, IsomorphismDefinitions.eq (f (g x)) x) 
  (l : Imported.Original_LF__DOT__Poly_LF_Poly_list' X2),
  IsomorphismDefinitions.eq (list'_to_imported f (list'_from_imported g l)) l.
Proof.
  intros X1 X2 f g Hfg.
  fix IH 1.
  intros l.
  destruct l as [| x xs].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply IsoEq.f_equal2.
    + apply Hfg.
    + apply IH.
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_list'_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (@Original.LF_DOT_Poly.LF.Poly.list' x1) (imported_Original_LF__DOT__Poly_LF_Poly_list' x2).
Proof.
  intros X1 X2 [f g Hfg Hgf].
  unshelve econstructor.
  - exact (list'_to_imported f).
  - exact (list'_from_imported g).
  - intro l. apply roundtrip_from_to. exact Hfg.
  - intro l. apply roundtrip_to_from. exact Hgf.
Defined.

Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.list') := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_list') := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.list') Original_LF__DOT__Poly_LF_Poly_list'_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.list') (@Imported.Original_LF__DOT__Poly_LF_Poly_list') Original_LF__DOT__Poly_LF_Poly_list'_iso := {}.