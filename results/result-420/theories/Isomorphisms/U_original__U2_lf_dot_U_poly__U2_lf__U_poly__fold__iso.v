From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_fold : forall x x0 : Type, (x -> x0 -> x0) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> x0 -> x0 := (@Imported.Original_LF__DOT__Poly_LF_Poly_fold).

(* Helper lemmas for imported fold computation *)
Lemma imported_fold_nil : forall (X Y : Type) (f : X -> Y -> Y) (b : Y),
  Imported.Original_LF__DOT__Poly_LF_Poly_fold X Y f (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil X) b = b.
Proof. intros. reflexivity. Qed.

Lemma imported_fold_cons : forall (X Y : Type) (f : X -> Y -> Y) (h : X) (t : Imported.Original_LF__DOT__Poly_LF_Poly_list X) (b : Y),
  Imported.Original_LF__DOT__Poly_LF_Poly_fold X Y f (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X h t) b = f h (Imported.Original_LF__DOT__Poly_LF_Poly_fold X Y f t b).
Proof. intros. reflexivity. Qed.

Instance Original_LF__DOT__Poly_LF_Poly_fold_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : IsoOrSortRelaxed x3 x4) (x5 : x1 -> x3 -> x3) (x6 : x2 -> x4 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 ->
  forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (Original.LF_DOT_Poly.LF.Poly.fold x5 x7 x9) (imported_Original_LF__DOT__Poly_LF_Poly_fold x6 x8 x10).
Proof.
  intros x1 x2 hx x3 x4 hx0 f1 f2 Hf.
  fix IH 1.
  intros l1 l2 Hlist b1 b2 Hb.
  destruct l1 as [|h1 t1].
  - (* Base case: nil *)
    simpl.
    unfold rel_iso in Hlist. simpl in Hlist.
    unfold imported_Original_LF__DOT__Poly_LF_Poly_fold.
    (* We need: rel_iso_sort hx0 b1 (fold f2 l2 b2) *)
    (* Since l2 = nil_imported, fold f2 nil b2 = b2 *)
    pose proof (@imported_fold_nil x2 x4 f2 b2) as Hfold_nil.
    apply (@eq_srect _ (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2) (fun l2 => rel_iso_sort hx0 b1 (Imported.Original_LF__DOT__Poly_LF_Poly_fold x2 x4 f2 l2 b2))).
    + (* Goal at nil: rel_iso_sort hx0 b1 (fold f2 nil b2) *)
      rewrite Hfold_nil. exact Hb.
    + exact Hlist.
  - (* Inductive case: cons *)
    simpl.
    unfold rel_iso in Hlist. simpl in Hlist.
    unfold imported_Original_LF__DOT__Poly_LF_Poly_fold.
    set (to_list := (fix to_list (l : Original.LF_DOT_Poly.LF.Poly.list x1) :
            imported_Original_LF__DOT__Poly_LF_Poly_list x2 :=
          match l with
          | Original.LF_DOT_Poly.LF.Poly.nil =>
              Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2
          | Original.LF_DOT_Poly.LF.Poly.cons h t =>
              Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 
                (hx h) (to_list t)
          end)).
    pose proof (@imported_fold_cons x2 x4 f2 (hx h1) (to_list t1) b2) as Hfold_cons.
    apply (@eq_srect _ (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (hx h1) (to_list t1)) (fun l2 => rel_iso_sort hx0 (f1 h1 (Original.LF_DOT_Poly.LF.Poly.fold f1 t1 b1)) (Imported.Original_LF__DOT__Poly_LF_Poly_fold x2 x4 f2 l2 b2))).
    + (* Goal at cons: rel_iso_sort hx0 (f1 h1 (fold f1 t1 b1)) (fold f2 (cons (hx h1) (to t1)) b2) *)
      rewrite Hfold_cons.
      apply Hf.
      * unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
      * apply IH.
        -- unfold rel_iso. simpl. apply IsomorphismDefinitions.eq_refl.
        -- exact Hb.
    + exact Hlist.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.fold) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.fold) (@Imported.Original_LF__DOT__Poly_LF_Poly_fold) Original_LF__DOT__Poly_LF_Poly_fold_iso := {}.