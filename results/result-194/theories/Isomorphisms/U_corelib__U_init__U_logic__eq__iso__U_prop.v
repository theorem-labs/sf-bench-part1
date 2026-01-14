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

(* Use proof irrelevance for equality proofs *)
From Stdlib Require Import ProofIrrelevance.

(* For Type->SProp equality isomorphism, x1 is Type (with universe Prop) and x2 is SProp *)
(* Key insight: x2 is SProp, so any two elements x4, x6 : x2 are definitionally equal.
   This means imported_Corelib_Init_Logic_eq_Prop x4 x6 is always inhabited.
   Similarly, x3 = x5 follows from from_to since from(to(x3)) = from(to(x5)) when
   to(x3) and to(x5) are in SProp and thus equal. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq. destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq. destruct H34. destruct H56.
    (* Since x2 is SProp, to(x3) and to(x5) are definitionally equal (both = x4 after destruct).
       So from(to(x3)) = from(to(x5)), and by from_to we get x3 = x5. *)
    rewrite <- (from_to hx x3).
    rewrite <- (from_to hx x5).
    reflexivity.
  - (* to_from *)
    intro Hseq. reflexivity.
  - (* from_to *)
    intro Heq. destruct H34. destruct H56. destruct Heq.
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
