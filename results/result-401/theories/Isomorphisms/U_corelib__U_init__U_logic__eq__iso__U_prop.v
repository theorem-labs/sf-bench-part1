From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp (defined in Prop in Lean) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop/SProp equality, we construct an isomorphism between proof-irrelevant types *)
(* The key insight is that when x2 : SProp and hx : Iso x1 x2, with rel_iso relating
   x3 to x4 and x5 to x6, the equality x3 = x5 is isomorphic to the SProp equality x4 = x6 *)

(* Helper to convert from IsomorphismDefinitions.eq to Logic.eq *)
Definition from_seq {A : Type} {x y : A} (H : IsomorphismDefinitions.eq x y) : x = y.
Proof. destruct H. reflexivity. Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  destruct H34. destruct H56.
  (* Now we need Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - intro Heq. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hseq.
    (* Use from_to to go back from hx x3, hx x5 to x3, x5 *)
    pose proof (from_seq (from_to hx x3)) as E3.
    pose proof (from_seq (from_to hx x5)) as E5.
    rewrite <- E3. rewrite <- E5.
    (* Now goal is from hx (hx x3) = from hx (hx x5) *)
    apply from_seq.
    apply (IsoEq.f_equal (from hx)).
    destruct Hseq. apply IsomorphismDefinitions.eq_refl.
  - intro s. reflexivity.
  - intro p. 
    (* Use proof irrelevance since (x3 = x5) is a Prop *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
