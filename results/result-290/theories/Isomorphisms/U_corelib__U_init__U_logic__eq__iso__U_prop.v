From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is in SProp for Prop-level equality *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop -> SProp isomorphisms with SProp-valued equality *)
(* Key insight: when x2 : SProp, all elements of x2 are definitionally equal *)
(* So x4 = x6 definitionally, and thus imported_Corelib_Init_Logic_eq_Prop x4 x6 is inhabited by refl *)
(* For the reverse, we need to show x3 = x5 given that x4 = x6 (definitionally) *)
(* Since hx is an isomorphism and x4 = hx x3, x6 = hx x5 (by H34, H56), 
   and x4 = x6 definitionally, we have hx x3 = hx x5 definitionally.
   Since elements of SProp are definitionally unique, from hx (hx x3) = from hx (hx x5).
   Combined with from_to, this gives us x3 = x5. *)

(* Helper: when the target type is SProp, we can get equality from the roundtrip *)
Lemma sprop_iso_injective : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 x5 : x1),
  x3 = x5.
Proof.
  intros x1 x2 hx x3 x5.
  (* hx x3 and hx x5 are both in SProp, hence definitionally equal *)
  (* from_to : eq (from hx (hx x)) x for any x *)
  pose proof (from_to hx x3) as H3.
  pose proof (from_to hx x5) as H5.
  (* H3 : eq (from hx (hx x3)) x3 *)
  (* H5 : eq (from hx (hx x5)) x5 *)
  (* from hx (hx x3) = from hx (hx x5) definitionally since hx x3 = hx x5 in SProp *)
  destruct H3. destruct H5. reflexivity.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  (* Both source (x3 = x5) and target (imported_eq x4 x6) are propositions *)
  (* Since x4, x6 : x2 : SProp, x4 = x6 definitionally, so target is inhabited by refl *)
  (* For source, by sprop_iso_injective, x3 = x5 always *)
  unshelve eapply Build_Iso.
  - (* to *)
    intro Heq. 
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ x4).
  - (* from *)
    intro Hseq.
    exact (sprop_iso_injective hx x3 x5).
  - (* to_from: SProp is proof irrelevant *)
    intro Hseq. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop is proof irrelevant *)
    intro Heq.
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5) (sprop_iso_injective hx x3 x5) Heq) as H.
    destruct H.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
