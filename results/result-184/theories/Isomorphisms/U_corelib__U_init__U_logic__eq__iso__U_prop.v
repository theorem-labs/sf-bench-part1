From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism between Prop eq on Props and SProp eq on SProps *)
(* Since x1 : Type and x2 : SProp, this converts between them *)

(* Simple transport for SProp eq *)
Definition transport_eq {A : Type} {x y : A} (H : eq x y) (P : A -> Type) : P x -> P y :=
  match H in (eq _ a) return (P x -> P a) with
  | eq_refl => fun p => p
  end.

(* Helper to go from (from hx (hx x3) = from hx (hx x5)) to (x3 = x5) using from_to *)
Lemma from_hx_eq_to_eq {x1 : Type} {x2 : SProp} (hx : Iso x1 x2) (x3 x5 : x1) :
  from hx (hx x3) = from hx (hx x5) -> x3 = x5.
Proof.
  intro H.
  pose proof (from_to hx x3) as Hft3.
  pose proof (from_to hx x5) as Hft5.
  (* Transport H along Hft5 to get: from hx (hx x3) = x5 *)
  pose proof (transport_eq Hft5 (fun y => from hx (hx x3) = y) H) as H'.
  (* Transport H' along Hft3 to get: x3 = x5 *)
  exact (transport_eq Hft3 (fun y => y = x5) H').
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Goal: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  (* Direct construction *)
  unshelve esplit.
  - (* to *) intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from *) intro Heq.
    apply (from_hx_eq_to_eq hx).
    exact (Imported.Corelib_Init_Logic_eq_Prop_recl _ (hx x3) (fun z _ => from hx (hx x3) = from hx z) (Corelib.Init.Logic.eq_refl (from hx (hx x3))) (hx x5) Heq).
  - (* to_from *) intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *) intro. apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
