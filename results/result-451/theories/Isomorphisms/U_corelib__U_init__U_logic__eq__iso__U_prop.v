From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp target, we build the isomorphism directly *)
(* Both (x3 = x5) : Prop and (imported_Corelib_Init_Logic_eq_Prop x4 x6) : SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  destruct H34. destruct H56.
  (* Now we have: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  (* Since x2 : SProp, to hx x3 and to hx x5 are definitionally equal *)
  (* Therefore x3 = x5 iff reflexivity holds *)
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> (x3 = x5) *)
    intro Hseq.
    (* In SProp, to hx x3 = to hx x5 definitionally *)
    (* By from_to (in IsomorphismDefinitions.eq), from hx (to hx x3) = x3 and from hx (to hx x5) = x5 *)
    (* Since x2 : SProp, to hx x3 and to hx x5 are definitionally equal in SProp *)
    (* Thus from hx (to hx x3) and from hx (to hx x5) are equal *)
    (* Therefore x3 = x5 *)
    pose proof (from_to hx x3) as F3. (* IsomorphismDefinitions.eq (from hx (to hx x3)) x3 *)
    pose proof (from_to hx x5) as F5. (* IsomorphismDefinitions.eq (from hx (to hx x5)) x5 *)
    (* In SProp, to hx x3 and to hx x5 are definitionally equal *)
    (* So from hx (to hx x3) = from hx (to hx x5) definitionally *)
    destruct F3, F5. reflexivity.
  - (* to_from *)
    intro Hseq. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
