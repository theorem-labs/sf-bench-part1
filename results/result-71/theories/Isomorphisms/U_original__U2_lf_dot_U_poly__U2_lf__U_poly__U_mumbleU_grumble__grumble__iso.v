From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker.Isomorphisms Require U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_mumbleU_grumble__mumble__iso.

Definition mumble_to_imported := U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_mumbleU_grumble__mumble__iso.mumble_to_imported.
Definition imported_to_mumble := U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_mumbleU_grumble__mumble__iso.imported_to_mumble.
Definition mumble_roundtrip1 := U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_mumbleU_grumble__mumble__iso.mumble_roundtrip1.
Definition mumble_roundtrip2 := U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_mumbleU_grumble__mumble__iso.mumble_roundtrip2.

Definition iso_roundtrip1 {A B : Type} (iso : Iso A B) : forall a, Logic.eq (IsomorphismDefinitions.from iso (IsomorphismDefinitions.to iso a)) a :=
  fun a => eq_of_seq (from_to iso a).

Definition iso_roundtrip2 {A B : Type} (iso : Iso A B) : forall b, Logic.eq (IsomorphismDefinitions.to iso (IsomorphismDefinitions.from iso b)) b :=
  fun b => eq_of_seq (to_from iso b).

Definition imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble : Type -> Type := Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble.

Definition grumble_to (X Y : Type) (f : X -> Y) 
  (og : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble X) 
  : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble Y :=
  match og with
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.d _ m => 
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_d Y (mumble_to_imported m)
  | Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.e _ x => 
      Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_e Y (f x)
  end.

Definition grumble_from (X Y : Type) (g : Y -> X) 
  (ig : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble Y) 
  : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble X :=
  match ig with
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_d _ m => 
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.d X (imported_to_mumble m)
  | Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_e _ y => 
      Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.e X (g y)
  end.

Lemma grumble_to_from (X Y : Type) (f : X -> Y) (g : Y -> X)
  (Hfg : forall y, Logic.eq (f (g y)) y)
  (ig : Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble Y)
  : Logic.eq (@grumble_to X Y f (@grumble_from X Y g ig)) ig.
Proof.
  destruct ig as [m | y].
  - simpl. apply Logic.f_equal. exact (mumble_roundtrip2 m).
  - simpl. apply Logic.f_equal. exact (Hfg y).
Qed.

Lemma grumble_from_to (X Y : Type) (f : X -> Y) (g : Y -> X)
  (Hgf : forall x, Logic.eq (g (f x)) x)
  (og : Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble X)
  : Logic.eq (@grumble_from X Y g (@grumble_to X Y f og)) og.
Proof.
  destruct og as [m | x].
  - simpl. apply Logic.f_equal. exact (mumble_roundtrip1 m).
  - simpl. apply Logic.f_equal. exact (Hgf x).
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble x1) (imported_Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble x2).
Proof.
  intros X Y iso_XY.
  exact (@Build_Iso 
            (Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble X)
            (Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble Y)
            (@grumble_to X Y (IsomorphismDefinitions.to iso_XY))
            (@grumble_from X Y (IsomorphismDefinitions.from iso_XY))
            (fun ig => seq_of_eq (@grumble_to_from X Y (IsomorphismDefinitions.to iso_XY) (IsomorphismDefinitions.from iso_XY) (iso_roundtrip2 iso_XY) ig))
            (fun og => seq_of_eq (@grumble_from_to X Y (IsomorphismDefinitions.to iso_XY) (IsomorphismDefinitions.from iso_XY) (iso_roundtrip1 iso_XY) og))).
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.MumbleGrumble.grumble Imported.Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble_iso := {}.
