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

(* For an Iso from Type to SProp: since SProp is proof-irrelevant, 
   all inhabitants of the SProp type are equal.
   This means from must map everything to the same value if there's an inhabitant.
   More concretely, if we have an Iso hx : Iso x1 x2 where x2 : SProp,
   then for any two x2 values v1 v2, from hx v1 = from hx v2 because v1 = v2 in SProp.
   
   Key lemma: in an Iso between Type and SProp, the Type side is essentially a singleton. *)

Lemma sprop_iso_injective : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A),
  x = y.
Proof.
  intros A B i x y.
  (* to i x and to i y are in SProp, so they are definitionally equal *)
  (* Thus from i (to i x) = from i (to i y) *)
  (* Combined with from_to: x = from i (to i x) = from i (to i y) = y *)
  rewrite <- (from_to i x). rewrite <- (from_to i y).
  reflexivity. (* Works because to i x = to i y in SProp (definitional UIP) *)
Defined.

(* Isomorphism for Prop version of equality *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + (* to : x3 = x5 -> Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from : Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq.
    destruct H34. destruct H56.
    (* Now x4 = to hx x3 and x6 = to hx x5. Hseq lives in SProp. *)
    (* Since SProp is proof-irrelevant, to hx x3 = to hx x5 *)
    (* Hence from hx (to hx x3) = from hx (to hx x5) *)
    (* By from_to: x3 = x5 *)
    exact (sprop_iso_injective hx x3 x5).
  + (* to_from *)
    intro Hseq. reflexivity.
  + (* from_to : we need IsomorphismDefinitions.eq (from (to Heq)) Heq *)
    intro Heq.
    (* from (to Heq) computes to sprop_iso_injective hx x3 x5, and we need to relate it to Heq *)
    (* Since the Iso is between x3 = x5 (Prop) and Corelib_Init_Logic_eq_Prop x4 x6 (SProp),
       the from_to condition is: IsomorphismDefinitions.eq (from (to Heq)) Heq
       where both from (to Heq) and Heq are in (x3 = x5) which is a Prop.
       IsomorphismDefinitions.eq is an SProp equality.
       Since Prop embeds into Type, and we're comparing two Prop values, we can use proof irrelevance.
       But actually in SProp, all proofs of the same statement are definitionally equal.
       The issue is that x3 = x5 lives in Prop, not SProp.
       We need to use that x3 = x5 is a Prop, and show two proofs of it are equal in SProp. *)
    destruct H34. destruct H56. destruct Heq.
    (* Now the goal is: IsomorphismDefinitions.eq (sprop_iso_injective hx x3 x3) eq_refl *)
    (* sprop_iso_injective hx x3 x3 is a proof of x3 = x3, and so is eq_refl *)
    (* In SProp, we can prove they're equal using IsomorphismDefinitions.eq_refl 
       if they're definitionally equal, which they may not be.
       We need to use proof irrelevance from Prop. *)
    assert (H: sprop_iso_injective hx x3 x3 = Logic.eq_refl) by apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
    rewrite H.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
