From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Helper to extract standard eq from Imported.Corelib_Init_Logic_eq *)
Definition sprop_eq_to_eq {X : Type} {x y : X} (H : Imported.Corelib_Init_Logic_eq X x y) : x = y :=
  Imported.Corelib_Init_Logic_eq_recl X x (fun z _ => x = z) (@Corelib.Init.Logic.eq_refl X x) y H.

(* Helper lemma for constructing the "to" direction *)
Definition eq_to_imported_eq {x1 x2 : Type} (to_ty : x1 -> x2) (from_ty : x2 -> x1)
  (x3 x5 : x1) (x4 x6 : x2) (H34 : to_ty x3 = x4) (H56 : to_ty x5 = x6)
  (Heq : x3 = x5) : Imported.Corelib_Init_Logic_eq x2 x4 x6.
Proof.
  subst x5 x4 x6.
  exact (Imported.Corelib_Init_Logic_eq_refl x2 (to_ty x3)).
Defined.

(* Helper lemma for constructing the "from" direction *)
Definition imported_eq_to_eq {x1 x2 : Type} (to_ty : x1 -> x2) (from_ty : x2 -> x1)
  (Hft : forall x : x1, from_ty (to_ty x) = x)
  (x3 x5 : x1) (x4 x6 : x2) (H34 : to_ty x3 = x4) (H56 : to_ty x5 = x6)
  (Heq : Imported.Corelib_Init_Logic_eq x2 x4 x6) : x3 = x5.
Proof.
  pose proof (sprop_eq_to_eq Heq) as H46.
  subst x4 x6.
  (* Now H46 : to_ty x3 = to_ty x5 *)
  (* We need x3 = x5 *)
  (* from_ty (to_ty x3) = x3, from_ty (to_ty x5) = x5 *)
  (* f_equal from_ty H46 gives from_ty (to_ty x3) = from_ty (to_ty x5) *)
  (* So x3 = from_ty (to_ty x3) = from_ty (to_ty x5) = x5 *)
  pose proof (@Corelib.Init.Logic.f_equal _ _ from_ty _ _ H46) as H'.
  pose proof (Hft x3) as Hft3.
  pose proof (Hft x5) as Hft5.
  congruence.
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold imported_Corelib_Init_Logic_eq.
  unfold rel_iso in *.
  destruct hx as [to_ty from_ty iso_to_from iso_from_to].
  simpl in *.
  (* Convert SProp eq to standard eq using eq_srect *)
  pose proof (eq_srect (fun z => to_ty x3 = z) (@Corelib.Init.Logic.eq_refl _ (to_ty x3)) Hx34) as H34.
  pose proof (eq_srect (fun z => to_ty x5 = z) (@Corelib.Init.Logic.eq_refl _ (to_ty x5)) Hx56) as H56.
  pose proof (fun x => @eq_srect _ _ (fun z => from_ty (to_ty x) = z) (@Corelib.Init.Logic.eq_refl _ _) _ (iso_from_to x)) as Hft.
  refine (@Build_Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq x2 x4 x6)
    (@eq_to_imported_eq x1 x2 to_ty from_ty x3 x5 x4 x6 H34 H56)
    (@imported_eq_to_eq x1 x2 to_ty from_ty Hft x3 x5 x4 x6 H34 H56)
    (fun e => IsomorphismDefinitions.eq_refl)
    _).
  (* from_to: from (to e) = e in Prop *)
  (* This requires showing two proofs of x3 = x5 are equal (in SProp eq) *)
  (* Use sUIPp or sUIPt for this *)
  intro e.
  exact (sUIPt _ _).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
