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

(* For SProp, we need a helper that extracts equality from the inductive.
   The key observation is that x2 : SProp, and (to hx) maps x1 -> x2.
   Since x2 : SProp, all its inhabitants are equal in SProp.
   
   We use the Ssig eliminator since we can eliminate SProp into SProp. *)

(* For SProp equality, both sides are proof irrelevant, so we build the isomorphism explicitly *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  (* H34 : IsomorphismDefinitions.eq (to hx x3) x4
     H56 : IsomorphismDefinitions.eq (to hx x5) x6 
     But x4, x6 : x2 where x2 : SProp, so they're irrelevant *)
  destruct H34. destruct H56.
  (* Now we need Iso (x3 = x5) (Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to : x3 = x5 -> Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) *)
    intro Heq.
    destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from : Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Hseq.
    (* Hseq lives in SProp. We need to eliminate it to get Prop equality.
       We can eliminate SProp inductives into SProp, and then use the 
       isomorphism to extract Type equality. *)
    (* Use the rec principle: Corelib_Init_Logic_eq_Prop_rec *)
    (* Actually, for SProp, the eliminator into Prop may work. Let's check the type. *)
    (* The key is: from SProp equality, we can derive that (to hx x3) and (to hx x5) 
       are equal as SProp terms. Since hx is an Iso, we can use from_to to show x3 = x5. *)
    (* But wait - x2 : SProp, so (to hx x3) : x2, and we can't form Type equality on SProp elements directly. *)
    (* However, we know that if Corelib_Init_Logic_eq_Prop is inhabited for any SProp, 
       then we can use the rec principle. Let's see if there's a way. *)
    (* Actually the recursor for SProp inductives when eliminating to SProp should work. *)
    pose proof (match Hseq in Imported.Corelib_Init_Logic_eq_Prop _ _ b 
            return (from hx (to hx x3) = from hx b) with
            | Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => Logic.eq_refl
            end) as H.
    (* from_to gives us SProp eq, but we need Logic.eq. Let's use eq_of_seq. *)
    assert (Heq1 : from hx (to hx x3) = x3).
    { apply eq_of_seq. apply from_to. }
    assert (Heq2 : from hx (to hx x5) = x5).
    { apply eq_of_seq. apply from_to. }
    rewrite Heq1 in H. rewrite Heq2 in H. exact H.
  - (* to_from *)
    intro Hseq.
    reflexivity.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    simpl.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
