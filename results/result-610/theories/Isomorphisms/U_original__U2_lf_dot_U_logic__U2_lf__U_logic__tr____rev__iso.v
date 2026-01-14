From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__rev____append__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_tr__rev : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := (@Imported.Original_LF__DOT__Logic_LF_Logic_tr__rev).

Instance Original_LF__DOT__Logic_LF_Logic_tr__rev_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Logic.LF.Logic.tr_rev x3) (imported_Original_LF__DOT__Logic_LF_Logic_tr__rev x4).
Proof.
  intros x1 x2 hx x3 x4 H34.
  unfold Original.LF_DOT_Logic.LF.Logic.tr_rev.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_tr__rev.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_tr__rev.
  (* tr_rev l = rev_append l [] *)
  apply Original_LF__DOT__Logic_LF_Logic_rev__append_iso.
  - exact H34.
  - apply Original_LF__DOT__Poly_LF_Poly_nil_iso.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Logic.LF.Logic.tr_rev) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Logic_LF_Logic_tr__rev) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Logic.LF.Logic.tr_rev) Original_LF__DOT__Logic_LF_Logic_tr__rev_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Logic.LF.Logic.tr_rev) (@Imported.Original_LF__DOT__Logic_LF_Logic_tr__rev) Original_LF__DOT__Logic_LF_Logic_tr__rev_iso := {}.