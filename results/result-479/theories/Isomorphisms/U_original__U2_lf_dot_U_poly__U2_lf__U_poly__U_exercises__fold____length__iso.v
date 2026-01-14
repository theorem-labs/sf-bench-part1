From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_nat := (@Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length).

(* Helper lemmas for imported fold_length computation *)
Lemma imported_fold_length_nil : forall (X : Type),
  Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length X (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil X) = Imported.nat_O.
Proof. intros. reflexivity. Qed.

Lemma imported_fold_length_cons : forall (X : Type) (h : X) (t : Imported.Original_LF__DOT__Poly_LF_Poly_list X),
  Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length X (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X h t) = 
  Imported.nat_S (Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length X t).
Proof. intros. reflexivity. Qed.

Instance Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso nat_iso (Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length x3) (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length x4).
Proof.
  intros x1 x2 hx.
  fix IH 1.
  intros l1 l2 Hlist.
  destruct l1 as [|h1 t1].
  - (* Base case: nil *)
    simpl. unfold Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length. simpl.
    unfold rel_iso in Hlist. simpl in Hlist.
    unfold imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length.
    pose proof (@imported_fold_length_nil x2) as Hfold_nil.
    apply (@eq_srect _ (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2) 
      (fun l2 => rel_iso nat_iso O (Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length x2 l2))).
    + unfold rel_iso. simpl. rewrite Hfold_nil. apply IsomorphismDefinitions.eq_refl.
    + exact Hlist.
  - (* Inductive case: cons *)
    simpl. unfold Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length. simpl.
    unfold rel_iso in Hlist. simpl in Hlist.
    unfold imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length.
    set (to_list := (fix to_list (l : Original.LF_DOT_Poly.LF.Poly.list x1) :
            imported_Original_LF__DOT__Poly_LF_Poly_list x2 :=
          match l with
          | Original.LF_DOT_Poly.LF.Poly.nil =>
              Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2
          | Original.LF_DOT_Poly.LF.Poly.cons h t =>
              Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 
                (hx h) (to_list t)
          end)).
    pose proof (@imported_fold_length_cons x2 (hx h1) (to_list t1)) as Hfold_cons.
    apply (@eq_srect _ (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (hx h1) (to_list t1)) 
      (fun l2 => rel_iso nat_iso (S (Original.LF_DOT_Poly.LF.Poly.fold (fun _ n => S n) t1 O)) (Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length x2 l2))).
    + unfold rel_iso. simpl. rewrite Hfold_cons.
      apply (IsoEq.f_equal Imported.nat_S).
      (* Need to show: nat_to_imported (fold ... t1 0) = fold_length (to_list t1) *)
      pose proof (IH t1 (to_list t1)) as Hrec.
      unfold rel_iso in Hrec. simpl in Hrec.
      apply Hrec.
      unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
    + exact Hlist.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) (@Imported.Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length) Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso := {}.