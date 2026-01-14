From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop equality going to SProp equality:
   Original: x3 = x5 in Prop (which is Type here due to universe constraints)
   Imported: Corelib_Init_Logic_eq_Prop x4 x6 = True (in SProp)
   
   Key insight: if x1 : Type is isomorphic to x2 : SProp, then x1 is contractible
   (has at most one element up to equality). This is because SProp is proof-irrelevant.
   
   Therefore from hx : x2 -> x1 must map all SProp elements to the same x1 element.
   Since from_to gives us from(to x3) = x3 and from(to x5) = x5,
   and to x3, to x5 are both in SProp (hence equal as arguments to from),
   we get x3 = x5.
*)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 ->
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  simpl.
  (* The target is Imported.True which is always inhabited *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.True *)
    intro Heq. exact Imported.True_intro.
  - (* from: Imported.True -> x3 = x5 *)
    intro Htrue.
    (* Key: if x2 is SProp, then from hx is constant on SProp elements *)
    (* x4 and x6 are both in x2 : SProp, so from hx x4 = from hx x6 *)
    (* But we have from_to hx x3 : from hx (hx x3) = x3 *)
    (* and from_to hx x5 : from hx (hx x5) = x5 *)
    (* H34 : hx x3 = x4, H56 : hx x5 = x6 *)
    unfold rel_iso in *.
    (* from hx (hx x3) = from hx x4 via f_equal *)
    pose (step1 := f_equal (from hx) H34). (* from hx (hx x3) = from hx x4 *)
    pose (step2 := f_equal (from hx) H56). (* from hx (hx x5) = from hx x6 *)
    pose (ft3 := from_to hx x3). (* from hx (hx x3) = x3 *)
    pose (ft5 := from_to hx x5). (* from hx (hx x5) = x5 *)
    (* x3 = from hx (hx x3) = from hx x4 *)
    pose (x3_eq_from_x4 := eq_trans (eq_sym ft3) step1).
    (* x5 = from hx (hx x5) = from hx x6 *)
    pose (x5_eq_from_x6 := eq_trans (eq_sym ft5) step2).
    (* from hx x4 = from hx x6 because x4 and x6 are in SProp and from is a function *)
    (* This follows from SProp irrelevance *)
    assert (from_eq : IsomorphismDefinitions.eq (from hx x4) (from hx x6)).
    { apply IsomorphismDefinitions.eq_refl. }
    pose (final := eq_trans x3_eq_from_x4 (eq_trans from_eq (eq_sym x5_eq_from_x6))).
    exact (eq_of_seq final).
  - (* to_from: trivial since target is SProp *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use proof irrelevance for Prop equality *)
    intro x. apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
