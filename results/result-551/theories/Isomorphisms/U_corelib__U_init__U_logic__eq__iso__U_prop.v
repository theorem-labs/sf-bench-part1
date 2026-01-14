From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop takes SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop equality when the first type argument is Prop (becomes SProp):
   We have: x1 : Type, x2 : SProp (via Iso), x3, x5 : x1, x4, x6 : x2
   We want to show: Iso (x3 = x5) (Corelib_Init_Logic_eq_Prop x4 x6)
   Since both sides are propositions (one in Prop, one in SProp), 
   the isomorphism follows from proof irrelevance. *)

(* Build the iso directly using Build_Iso *)
#[local] Unset Universe Polymorphism.
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  destruct H34. destruct H56.
  (* Now x4 = to hx x3, x6 = to hx x5 *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from: Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Hseq.
    (* Eliminate SProp to SInhabited, then extract *)
    apply sinhabitant.
    assert (H3 : Logic.eq (from hx (to hx x3)) x3) by (apply eq_of_seq; apply from_to).
    assert (H5 : Logic.eq (from hx (to hx x5)) x5) by (apply eq_of_seq; apply from_to).
    (* Need to show SInhabited (x3 = x5) *)
    rewrite <- H5.
    apply (Imported.Corelib_Init_Logic_eq_Prop_indl _ (to hx x3) 
             (fun y _ => SInhabited (Logic.eq x3 (from hx y))) 
             (sinhabits (Logic.eq_sym H3)) 
             (to hx x5) Hseq).
  - (* to_from: SProp target, so eq_refl *)
    intro s. reflexivity.
  - (* from_to: Prop domain, use proof irrelevance *)
    intro p.
    apply seq_of_peq_t.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
#[local] Set Universe Polymorphism.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
