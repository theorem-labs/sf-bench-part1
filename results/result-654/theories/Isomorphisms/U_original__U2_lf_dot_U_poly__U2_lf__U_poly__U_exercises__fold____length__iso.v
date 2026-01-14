From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__fold__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_nat := (@Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length).

(* Helper: imported fold_length unfolds to fold *)
Lemma imported_fold_length_unfold : forall (X : Type) (l : Imported.Original_LF__DOT__Poly_LF_Poly_list X),
  Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length X l = 
  Imported.Original_LF__DOT__Poly_LF_Poly_fold X Imported.nat (fun _ n => Imported.nat_S n) l Imported.nat_O.
Proof. intros. reflexivity. Qed.

Instance Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso nat_iso (Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length x3) (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length x4).
Proof.
  intros x1 x2 hx l1 l2 Hlist.
  unfold Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length.
  rewrite imported_fold_length_unfold.
  (* Now we need to show:
     rel_iso nat_iso (fold (fun _ n => S n) l1 0) (fold (fun _ n => S n) l2 O) *)
  (* rel_iso_sort nat_iso = WrapSProp (rel_iso nat_iso), so we can use unwrap_sprop *)
  apply unwrap_sprop.
  apply Original_LF__DOT__Poly_LF_Poly_fold_iso with (hx := hx) (hx0 := nat_iso).
  - (* Show the function argument respects the isomorphism *)
    intros _ _ _ n1 n2 Hn.
    simpl in *.
    apply wrap_sprop.
    apply unwrap_sprop in Hn.
    apply (IsoEq.f_equal Imported.nat_S Hn).
  - exact Hlist.
  - (* Show 0 and nat_O are related *)
    simpl. apply wrap_sprop. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) (@Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length) Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso := {}.