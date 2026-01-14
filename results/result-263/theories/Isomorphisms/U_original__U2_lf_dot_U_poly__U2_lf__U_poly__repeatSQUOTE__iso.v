From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_repeat' : forall x : Type, x -> imported_nat -> imported_Original_LF__DOT__Poly_LF_Poly_list x := Imported.Original_LF__DOT__Poly_LF_Poly_repeat'.

Definition Original_LF__DOT__Poly_LF_Poly_repeat'_iso_aux : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  IsomorphismDefinitions.eq (to hx x3) x4 ->
  forall (n : nat),
    IsomorphismDefinitions.eq
      (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.repeat' x1 x3 n))
      (Imported.Original_LF__DOT__Poly_LF_Poly_repeat' x2 x4 (to nat_iso n)).
Proof.
  intros x1 x2 hx x3 x4 H34.
  fix go 1.
  intro n.
  destruct n as [|n'].
  - (* Base case: n = 0 *)
    (* Both sides compute to nil with cbn *)
    cbn. exact (IsomorphismDefinitions.eq_refl _).
  - (* Inductive case: n = S n' *)
    cbn.
    (* LHS: cons (to hx x3) (to list_iso (repeat' ...))
       RHS: cons x4 (repeat' x4 ...) *)
    apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2) H34 (go n')).
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_repeat'_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat),
  rel_iso nat_iso x5 x6 -> rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.repeat' x1 x3 x5) (@imported_Original_LF__DOT__Poly_LF_Poly_repeat' x2 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_repeat'.
  (* Apply the auxiliary function with x6 replaced by to nat_iso x5 *)
  exact (match H56 in IsomorphismDefinitions.eq _ y return 
           IsomorphismDefinitions.eq
             (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.repeat' x1 x3 x5))
             (Imported.Original_LF__DOT__Poly_LF_Poly_repeat' x2 x4 y)
         with
         | IsomorphismDefinitions.eq_refl => @Original_LF__DOT__Poly_LF_Poly_repeat'_iso_aux x1 x2 hx x3 x4 H34 x5
         end).
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.repeat' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_repeat' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.repeat' Original_LF__DOT__Poly_LF_Poly_repeat'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.repeat' Imported.Original_LF__DOT__Poly_LF_Poly_repeat' Original_LF__DOT__Poly_LF_Poly_repeat'_iso := {}.