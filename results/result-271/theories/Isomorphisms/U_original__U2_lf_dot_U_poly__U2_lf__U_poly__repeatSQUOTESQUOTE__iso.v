From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_repeat'' : forall x : Type, x -> imported_nat -> imported_Original_LF__DOT__Poly_LF_Poly_list x := Imported.Original_LF__DOT__Poly_LF_Poly_repeat''.

(* Helper lemma to relate repeat'' via induction on nat *)
Lemma repeat''_iso_aux : forall {x1 x2 : Type} (hx : Iso x1 x2) {x3 : x1} {x4 : x2},
  IsomorphismDefinitions.eq (to hx x3) x4 ->
  forall (n : nat),
  IsomorphismDefinitions.eq 
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.repeat'' x1 x3 n))
    (imported_Original_LF__DOT__Poly_LF_Poly_repeat'' x4 (to nat_iso n)).
Proof.
  intros x1 x2 hx x3 x4 H34 n.
  induction n as [|n' IH].
  - (* n = 0 *)
    simpl.
    apply IsomorphismDefinitions.eq_refl.
  - (* n = S n' *)
    simpl.
    apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2) H34 IH).
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_repeat''_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat),
  rel_iso nat_iso x5 x6 -> rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.repeat'' x1 x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_repeat'' x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H56.
  unfold rel_iso in H34.
  unfold rel_iso.
  (* H56 : to nat_iso x5 = x6 *)
  (* H34 : to hx x3 = x4 *)
  (* Need to show: to (list_iso hx) (repeat'' x3 x5) = repeat'' x4 x6 *)
  pose proof (repeat''_iso_aux hx H34 x5) as Haux.
  (* Haux : to (list_iso hx) (repeat'' x3 x5) = repeat'' x4 (to nat_iso x5) *)
  (* We need to show equality with x6 instead of (to nat_iso x5) *)
  (* Use H56 to rewrite *)
  eapply IsoEq.eq_trans.
  - exact Haux.
  - apply IsoEq.f_equal. exact H56.
Defined.

Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.repeat'' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_repeat'' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.repeat'' Original_LF__DOT__Poly_LF_Poly_repeat''_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.repeat'' Imported.Original_LF__DOT__Poly_LF_Poly_repeat'' Original_LF__DOT__Poly_LF_Poly_repeat''_iso := {}.