From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Iso between Prop eq for Prop arguments and SProp eq for SProp arguments *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56. simpl in H34, H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - intro Heq.
    (* For SProp eq, we need to get back a Prop eq *)
    (* Since x4 = to hx x3 and x6 = to hx x5, and we have Heq in SProp *)
    (* All SProp proofs are irrelevant, so we just need any proof *)
    (* We use from_to to convert back *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    exact (Corelib.Init.Logic.eq_refl (from hx (to hx x3))).
  - intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - intro Heq.
    (* Use proof irrelevance for Prop eq *)
    set (lhs := (let Hft3 := from_to hx x3 in
                 let Hft5 := from_to hx x5 in
                 match Hft3 in (IsomorphismDefinitions.eq _ x) return (x = x5) with
                 | IsomorphismDefinitions.eq_refl =>
                   match Hft5 in (IsomorphismDefinitions.eq _ x) return (from hx (hx x3) = x) with
                   | IsomorphismDefinitions.eq_refl => Logic.eq_refl
                   end
                 end)).
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance (x3 = x5) lhs Heq) as H.
    destruct H.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
