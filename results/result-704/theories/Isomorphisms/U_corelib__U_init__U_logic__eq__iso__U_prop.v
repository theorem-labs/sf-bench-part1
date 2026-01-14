From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is SProp -> SProp -> SProp -> SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal_Prop : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

(* We need an isomorphism for equality when the type is Prop (becomes SProp) *)
(* This is technically complex due to SProp limitations *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - intro Heq. destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hseq. destruct H34. destruct H56.
    (* Need to convert SProp equality to Type equality via iso injectivity *)
    pose proof (from_to_tseq hx x3) as Hx3.
    pose proof (from_to_tseq hx x5) as Hx5.
    rewrite <- Hx3. rewrite <- Hx5.
    (* from (to hx x3) = from (to hx x5) when to hx x3 = to hx x5 *)
    (* But Hseq is in SProp, so we can match on it *)
    destruct Hseq as [a].
    reflexivity.
  - intro Hseq. apply IsomorphismDefinitions.eq_refl.
  - intro Heq. destruct H34. destruct H56. destruct Heq.
    (* Use proof irrelevance *)
    apply seq_of_eq.
    apply eq_proofs_equal_Prop.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
