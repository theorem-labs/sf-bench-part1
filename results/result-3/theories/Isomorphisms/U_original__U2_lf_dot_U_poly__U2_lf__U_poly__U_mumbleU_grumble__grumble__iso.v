From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_mumbleU_grumble__mumble__iso.

Monomorphic Definition imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble : Type -> Type := Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble.

Definition grumble_to_imported {X Y : Type} (f : X -> Y) (g : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble X) : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble Y :=
  match g with
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.d _ m =>
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_d Y (mumble_to_imported m)
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.e _ x =>
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_e Y (f x)
  end.

Definition imported_to_grumble {X Y : Type} (f : X -> Y) (g : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble X) : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble Y :=
  match g with
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_d _ m =>
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.d Y (imported_to_mumble m)
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_e _ x =>
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.e Y (f x)
  end.

Lemma grumble_roundtrip1 {X : Type} : forall g : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble X,
  IsomorphismDefinitions.eq (imported_to_grumble id (grumble_to_imported id g)) g.
Proof.
  intros g. destruct g as [m | x].
  - simpl. apply IsoEq.f_equal. apply mumble_roundtrip1.
  - simpl. apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma grumble_roundtrip2 {X : Type} : forall g : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble X,
  IsomorphismDefinitions.eq (grumble_to_imported id (imported_to_grumble id g)) g.
Proof.
  intros g. destruct g as [m | x].
  - simpl. apply IsoEq.f_equal. apply mumble_roundtrip2.
  - simpl. apply IsomorphismDefinitions.eq_refl.
Defined.

Monomorphic Instance Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble x1) (imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble x2).
Proof.
  intros x1 x2 hx.
  refine (Build_Iso (grumble_to_imported (to hx)) (imported_to_grumble (from hx)) _ _).
  - intro g. destruct g as [m | x].
    + simpl. apply IsoEq.f_equal. apply mumble_roundtrip2.
    + simpl. apply IsoEq.f_equal. apply (to_from hx).
  - intro g. destruct g as [m | x].
    + simpl. apply IsoEq.f_equal. apply mumble_roundtrip1.
    + simpl. apply IsoEq.f_equal. apply (from_to hx).
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_iso := {}.