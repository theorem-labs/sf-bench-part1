From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: extract eq from imported eq_Prop *)
Definition seq_to_eq_prop {A : SProp} {x y : A} (H : Imported.Corelib_Init_Logic_eq_Prop A x y) : IsomorphismDefinitions.eq x y :=
  match H with Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => IsomorphismDefinitions.eq_refl end.

(* Helper: use from_to to derive equality in the domain *)
Definition iso_injective_ts : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A),
  IsomorphismDefinitions.eq (to i x) (to i y) -> x = y.
Proof.
  intros A B i x y H.
  rewrite <- (from_to_tseq i x).
  rewrite <- (from_to_tseq i y).
  destruct H.
  reflexivity.
Defined.

(* We define the isomorphism for Prop version *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + intro Hseq.
    destruct H34. destruct H56.
    (* The from direction: we need to show x3 = x5 in Type x1 *)
    pose proof (seq_to_eq_prop Hseq) as Hseq'.
    exact (iso_injective_ts hx x3 x5 Hseq').
  + intro Hseq.
    reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    unfold iso_injective_ts, seq_to_eq_prop. simpl.
    rewrite (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ _ Logic.eq_refl).
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
