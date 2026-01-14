From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: proof irrelevance for Prop eq expressed in SProp eq *)
Lemma prop_eq_proof_irrel {A : Type} {x y : A} (p q : x = y) : IsomorphismDefinitions.eq p q.
Proof.
  pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ p q) as H.
  destruct H. exact (IsomorphismDefinitions.eq_refl _).
Defined.

(* This is an isomorphism between Prop eq (over Type) and SProp eq (over SProp) *)
(* x1 : Type is iso to x2 : SProp, and we relate eq on x1 to Corelib_Init_Logic_eq_Prop on x2 *)
(* Both (x3 = x5) : Prop and (imported_Corelib_Init_Logic_eq_Prop x4 x6) : SProp are propositions *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Destruct H34 and H56 first to simplify *)
  destruct H34. destruct H56.
  (* Now x4 = to hx x3 and x6 = to hx x5 *)
  (* Goal: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Use from_to to relate back *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    (* Now we need to show: from hx (to hx x3) = from hx (to hx x5) *)
    (* Use the SProp eliminator to build an SInhabited proof *)
    pose proof (sinhabitant (Imported.Corelib_Init_Logic_eq_Prop_indl x2 (to hx x3) 
                (fun z _ => SInhabited (from hx (to hx x3) = from hx z)) 
                (sinhabits Logic.eq_refl) (to hx x5) Heq)) as H.
    exact H.
  - (* to_from: in SProp, trivial *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: use proof irrelevance *)
    intro Heq.
    apply prop_eq_proof_irrel.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
