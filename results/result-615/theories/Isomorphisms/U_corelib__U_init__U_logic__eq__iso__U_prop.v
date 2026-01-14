From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop takes SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp types, we can use proof irrelevance more directly *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Both source (eq in Prop) and target (eq in SProp over SProp) are propositions.
     We build the isomorphism directly. *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* After destruct, x3 = x5. We need imported eq x4 x6.
       Since x2 is SProp, x4 and x6 are definitionally equal by SProp proof irrelevance. *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    (* We need to prove x3 = x5.
       Use the from_to properties of the isomorphism hx. *)
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    apply eq_of_seq.
    apply (eq_trans (eq_sym Hx3)).
    apply (eq_trans (f_equal (from hx) H34)).
    (* x4 and x6 are both elements of SProp x2, so they're definitionally equal.
       Hence from hx x4 = from hx x6 definitionally. *)
    apply (eq_trans (f_equal (from hx) (eq_sym H56))).
    exact Hx5.
  - (* to_from *)
    intro Heq.
    (* Both sides are in SProp, so proof irrelevance applies *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
