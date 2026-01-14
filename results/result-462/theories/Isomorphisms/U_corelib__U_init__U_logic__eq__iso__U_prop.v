From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper for proof irrelevance on Prop equalities *)
Lemma prop_eq_proof_irrel' {A : Prop} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* Helper for proof irrelevance on Type equalities - uses proof irrelevance for eq in Prop *)
Lemma type_eq_proof_irrel {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* For Prop version, x1 : Type (universe polymorphic, will be instantiated at Prop) and x2 : SProp *)
(* The hint using IsoStatementProofForWithSorts ensures x1 is Prop at use sites *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Destruct H34 and H56 to simplify - this gives us x4 = to hx x3 and x6 = to hx x5 *)
  destruct H34. destruct H56.
  (* Now goal is: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Use the recursor on the SProp eq to transport along the equality *)
    (* First build: from hx (to hx x3) = from hx (to hx x5) using the recursor *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3)
              (fun (b : x2) _ => from hx (to hx x3) = from hx b)
              Logic.eq_refl
              (to hx x5)
              Heq) as Hmid.
    (* Now use from_to to get from hx (to hx x3) = x3 and from hx (to hx x5) = x5 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* Use eq_of_seq to convert SProp eq to Prop eq *)
    pose proof (eq_of_seq Hft3) as Hft3'.
    pose proof (eq_of_seq Hft5) as Hft5'.
    (* Now we have: Hmid : from hx (to hx x3) = from hx (to hx x5) *)
    (* Hft3' : from hx (to hx x3) = x3 *)
    (* Hft5' : from hx (to hx x5) = x5 *)
    (* Combine: x3 = from hx (to hx x3) = from hx (to hx x5) = x5 *)
    exact (Logic.eq_trans (Logic.eq_sym Hft3') (Logic.eq_trans Hmid Hft5')).
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    apply type_eq_proof_irrel.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
