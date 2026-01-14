From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq is now in SProp (Prop from Lean gets imported as SProp) *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Helper: from rel_iso we can extract the standard Prop eq *)
Definition rel_iso_to_std_eq {A B : Type} {iso : Iso A B} {x : A} {y : B}
  (H : rel_iso iso x y) : to iso x = y.
Proof.
  unfold rel_iso in H. simpl in H.
  destruct H.
  reflexivity.
Defined.

(* to is injective for any Iso - using imported eq *)
Lemma to_injective {A B : Type} (iso : Iso A B) (x y : A) :
  Imported.Corelib_Init_Logic_eq B (to iso x) (to iso y) -> Corelib.Init.Logic.eq x y.
Proof.
  intro H.
  pose proof (from_to iso x) as Hx.
  pose proof (from_to iso y) as Hy.
  destruct Hx. destruct Hy.
  (* Goal: from iso (to iso x) = from iso (to iso y) *)
  (* H : Imported.Corelib_Init_Logic_eq B (to iso x) (to iso y) *)
  (* Use Imported.Corelib_Init_Logic_eq_recl to compute (the large eliminator) *)
  exact (@Imported.Corelib_Init_Logic_eq_recl B (to iso x) 
           (fun b _ => from iso (to iso x) = from iso b) 
           (Corelib.Init.Logic.eq_refl _) (to iso y) H).
Qed.

(* Isomorphism between Prop eq and Imported SProp eq *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq.
  pose proof (@rel_iso_to_std_eq _ _ _ _ _ H34) as E34.
  pose proof (@rel_iso_to_std_eq _ _ _ _ _ H56) as E56.
  subst x4 x6.
  unshelve eapply Build_Iso.
  - (* to: eq x3 x5 -> Imported.Corelib_Init_Logic_eq (to hx x3) (to hx x5) *)
    intro Heq.
    destruct Heq.
    apply Imported.Corelib_Init_Logic_eq_refl.
  - (* from: Imported eq -> Prop eq *)
    exact (to_injective hx x3 x5).
  - (* to_from: SProp proof irrelevance *)
    intro Heq.
    exact IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ 
                  (to_injective hx x3 x3 (Imported.Corelib_Init_Logic_eq_refl x2 (hx x3))) 
                  (Corelib.Init.Logic.eq_refl x3)) as PIR.
    destruct PIR.
    exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
