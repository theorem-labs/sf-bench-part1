From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop for SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop version, we need an isomorphism between (x3 = x5) and (imported_Corelib_Init_Logic_eq_Prop x4 x6) *)
(* x1 : Type, x2 : SProp with an Iso between them *)
(* x3, x5 : x1 and x4, x6 : x2 are related via the isomorphism *)
(* We need to build an isomorphism between the equality types *)

(* For the Prop version, we need Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)
   where x2 : SProp.
   
   Since both (x3 = x5) and (imported_Corelib_Init_Logic_eq_Prop x2 x4 x6) are propositions,
   and we have an isomorphism between x1 (a Type/Prop) and x2 (an SProp),
   we can build this isomorphism using the principle that all strict propositions
   are isomorphic to their SInhabited version. *)

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  (* Since x2 : SProp, all its inhabitants are definitionally equal. *)
  (* Thus to hx x3 = to hx x5 definitionally, so from hx (to hx x3) = from hx (to hx x5) *)
  (* By from_to, x3 = from hx (to hx x3) and x5 = from hx (to hx x5) *)
  (* So x3 = x5 definitionally once we unfold the isomorphism roundtrip *)
  
  unshelve eapply Build_Iso.
  + (* to: x3 = x5 -> Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    intro Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  + (* from: Corelib_Init_Logic_eq_Prop x2 x4 x6 -> x3 = x5 *)
    intro Hseq.
    (* Since x2 : SProp, to hx x3 and to hx x5 are definitionally equal *)
    (* So from hx (to hx x3) = from hx (to hx x5) definitionally *)
    assert (H1 : Logic.eq (from hx (to hx x3)) x3) by (apply eq_of_seq; apply from_to).
    assert (H2 : Logic.eq (from hx (to hx x5)) x5) by (apply eq_of_seq; apply from_to).
    rewrite <- H1. rewrite <- H2. reflexivity.
  + (* to_from *)
    intro Hseq. reflexivity. (* SProp *)
  + (* from_to: need IsomorphismDefinitions.eq (from (to Heq)) Heq *)
    intro Heq.
    (* Both sides are equalities in x1, which is a proposition if we're in the Prop case *)
    (* Use proof irrelevance in SProp form *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
