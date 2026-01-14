From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism for equality on Prop types (which become SProp in import) *)
(* Both x3 = x5 (in Prop) and imported_Corelib_Init_Logic_eq_Prop x4 x6 (in SProp) are propositions *)
(* We build the isomorphism directly *)

(* Helper lemma for the from direction *)
Lemma from_imported_eq_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 x5 : x1), 
  imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5.
Proof.
  intros x1 x2 hx x3 x5 Heq.
  pose proof (eq_of_seq (from_to hx x3)) as Hft3.
  pose proof (eq_of_seq (from_to hx x5)) as Hft5.
  pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) 
           (fun z _ => from hx (to hx x3) = from hx z) 
           (Corelib.Init.Logic.eq_refl (from hx (to hx x3))) (to hx x5) Heq) as H.
  rewrite Hft3 in H. rewrite Hft5 in H. exact H.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from *)
    intro Heq. exact (@from_imported_eq_Prop x1 x2 hx x3 x5 Heq).
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: need IsomorphismDefinitions.eq (from (to Heq)) Heq where Heq : x3 = x5 *)
    intro Heq.
    (* Both from (to Heq) and Heq are proofs of (x3 = x5). 
       Use sUIPt to show they are equal in SProp. *)
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
