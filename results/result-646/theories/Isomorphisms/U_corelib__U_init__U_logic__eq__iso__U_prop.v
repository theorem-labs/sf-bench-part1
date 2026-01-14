From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* When x2 : SProp, the isomorphism collapses all elements of x1 *)
Lemma iso_collapse_SProp (A : Type) (B : SProp) (i : Iso A B) (x y : A) : x = y.
Proof.
  pose proof (from_to i x) as H1.
  pose proof (from_to i y) as H2.
  destruct H1, H2. reflexivity.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  pose proof (iso_collapse_SProp hx x3 x5) as Heq35.
  apply (Build_Iso 
    (fun _ => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4)
    (fun _ => Heq35)
    (fun _ => IsomorphismDefinitions.eq_refl)
    (fun Heq => match Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ Heq35 Heq with Logic.eq_refl => IsomorphismDefinitions.eq_refl end)).
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
