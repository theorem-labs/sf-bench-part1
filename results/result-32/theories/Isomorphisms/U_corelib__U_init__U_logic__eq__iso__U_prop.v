From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
(* Don't require the main eq iso file to avoid circular dependency *)
(* From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso. *)

(* For SProp types, we use proof irrelevance: all inhabitants of an SProp are equal *)

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp :=
  @Imported.Corelib_Init_Logic_eq_Prop.

(* The isomorphism between eq on Type (which gets sent to SProp) and eq on SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 ->
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  { intro H. exact Imported.True_intro. }
  { intro H.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    (* Need: from hx (to hx x3) = x5 *)
    (* We have: from hx (to hx x5) = x5 (Hx5) *)
    (* Since x2 is SProp, to hx x3 = to hx x5 definitionally *)
    pose proof (IsoEq.f_equal (from hx) (IsomorphismDefinitions.eq_refl (to hx x3) : IsomorphismDefinitions.eq (to hx x3) (to hx x5))) as Hmid.
    apply (IsoEq.eq_trans Hmid).
    exact Hx5. }
  { intro x. apply IsomorphismDefinitions.eq_refl. }
  { intro x. destruct x. apply IsomorphismDefinitions.eq_refl. }
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
