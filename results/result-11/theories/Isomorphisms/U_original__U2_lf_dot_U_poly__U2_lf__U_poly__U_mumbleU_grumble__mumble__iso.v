From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble : Type := Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble.

Fixpoint mumble_to_imported (m : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble) : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble :=
  match m with
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.a =>
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_a
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b m' n =>
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b (mumble_to_imported m') (nat_to_imported n)
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.c =>
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_c
  end.

Fixpoint imported_to_mumble (m : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble) : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble :=
  match m with
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_a =>
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.a
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b m' n =>
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b (imported_to_mumble m') (imported_to_nat n)
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_c =>
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.c
  end.

Lemma mumble_roundtrip1 : forall m, IsomorphismDefinitions.eq (imported_to_mumble (mumble_to_imported m)) m.
Proof.
  fix IH 1.
  intro m. destruct m as [|m' n|].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal2 Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.b).
    + apply IH.
    + apply seq_of_eq. apply nat_roundtrip.
  - simpl. apply IsomorphismDefinitions.eq_refl.
Defined.

Lemma mumble_roundtrip2 : forall m, IsomorphismDefinitions.eq (mumble_to_imported (imported_to_mumble m)) m.
Proof.
  fix IH 1.
  intro m. destruct m as [|m' n|].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_b).
    + apply IH.
    + apply seq_of_eq. apply imported_nat_roundtrip.
  - simpl. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_iso : Iso Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble.
Proof.
  exact (Build_Iso mumble_to_imported imported_to_mumble mumble_roundtrip2 mumble_roundtrip1).
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.mumble Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble_iso := {}.
