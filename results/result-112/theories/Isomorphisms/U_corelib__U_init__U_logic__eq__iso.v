From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From LeanImport Require Import Lean.

Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Imported.

Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* For equality, both source (Prop eq) and target (SProp eq) are proof-irrelevant,
   so we can use trivial witnesses. The key is that the return type is SProp equality. *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 hx34 x5 x6 hx56.
  (* Both source and target are proof-irrelevant (Prop and SProp equalities) *)
  unfold rel_iso in hx34, hx56. simpl in hx34, hx56.
  (* Destruct the SProp equalities to reduce to the case where x4 = to x3 and x6 = to x5 *)
  destruct hx34. destruct hx56.
  (* Now build the isomorphism *)
  unshelve refine (Build_Iso _ _ _ _).
  - (* to: x3 = x5 -> imported eq (to x3) (to x5) *)
    intro H. destruct H.
    exact (Imported.Corelib_Init_Logic_eq_refl x2 (@to x1 x2 hx x3)).
  - (* from: imported eq (to x3) (to x5) -> x3 = x5 *)
    intro H.
    pose proof (eq_of_seq (@from_to x1 x2 hx x3)) as H3.
    pose proof (eq_of_seq (@from_to x1 x2 hx x5)) as H5.
    assert (Hfrom : @Corelib.Init.Logic.eq x1 (@from x1 x2 hx (@to x1 x2 hx x3)) (@from x1 x2 hx (@to x1 x2 hx x5))).
    { destruct H. reflexivity. }
    rewrite H3 in Hfrom. rewrite H5 in Hfrom. exact Hfrom.
  - (* to_from: SProp so trivially equal *)
    intro q. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop equality, use proof irrelevance *)
    intro p. 
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
