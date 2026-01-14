From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use imported Corelib_Init_Logic_eq_Prop which is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For the Prop case, we have x1 : Type (but actually Prop), x2 : SProp *)
(* The isomorphism between Type and SProp involves SInhabited *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* We need Iso (x3 = x5 : Prop) (imported_Corelib_Init_Logic_eq_Prop x4 x6 : SProp) *)
  (* Use relax_Iso_Ps_Ts to convert Iso@{Prop SProp} to Iso@{Type SProp} *)
  apply relax_Iso_Ps_Ts.
  (* Now goal is Iso@{Prop SProp} (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6) *)
  apply (iso_trans iso_SInhabited).
  (* Now we need Iso (SInhabited (x3 = x5)) (imported_Corelib_Init_Logic_eq_Prop x4 x6) *)
  (* Both are SProp, construct an iso between them *)
  unshelve eapply Build_Iso.
  - (* to: SInhabited (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro H.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* x4 x6 : x2 (SProp) *)
    (* We need to show Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> SInhabited (x3 = x5) *)
    intro H.
    unfold imported_Corelib_Init_Logic_eq_Prop in H.
    destruct H.
    (* H34 : eq (to hx x3) x4, H56 : eq (to hx x5) x4 (since x4 = x6 now) *)
    apply sinhabits.
    (* Need to prove x3 = x5 *)
    (* Use from_to_tseq which gives Prop equality when target is SProp *)
    pose proof (from_to_tseq hx x3) as Hx3.
    pose proof (from_to_tseq hx x5) as Hx5.
    (* Hx3, Hx5 are Prop equalities *)
    (* H34, H56 are SProp equalities: to hx x3 = x4, to hx x5 = x4 *)
    (* We can destruct them since they're SProp *)
    destruct H34. destruct H56.
    (* Now x4 = to hx x3 = to hx x5 *)
    (* So from hx x4 = from hx (to hx x3) = x3 and also = from hx (to hx x5) = x5 *)
    transitivity (from hx (to hx x3)).
    + symmetry. exact Hx3.
    + exact Hx5.
  - (* to_from *)
    intro x. apply eq_refl.
  - (* from_to *)
    intro x. apply eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
