From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_rev : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x := Imported.Original_LF__DOT__Poly_LF_Poly_rev.

(* First, prove that Imported.rev has the expected behavior *)
Lemma imported_rev_nil : forall X, 
  Imported.Original_LF__DOT__Poly_LF_Poly_rev X (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil X) = Imported.Original_LF__DOT__Poly_LF_Poly_list_nil X.
Proof. intros. reflexivity. Qed.

Lemma imported_rev_cons : forall X h t, 
  Imported.Original_LF__DOT__Poly_LF_Poly_rev X (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X h t) = 
  Imported.Original_LF__DOT__Poly_LF_Poly_app X 
    (Imported.Original_LF__DOT__Poly_LF_Poly_rev X t) 
    (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons X h (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil X)).
Proof. intros. reflexivity. Qed.

(* Helper lemma: the to function preserves rev *)
Lemma list_to_rev_compat : forall (x1 x2 : Type) (Hx : Iso x1 x2)
  (l : Original.LF_DOT_Poly.LF.Poly.list x1),
  IsomorphismDefinitions.eq
    (to (Original_LF__DOT__Poly_LF_Poly_list_iso Hx) (Original.LF_DOT_Poly.LF.Poly.rev l))
    (Imported.Original_LF__DOT__Poly_LF_Poly_rev x2 (to (Original_LF__DOT__Poly_LF_Poly_list_iso Hx) l)).
Proof.
  intros x1 x2 Hx l.
  induction l as [|h t IH].
  - (* nil case: both reduce to nil *)
    simpl. apply IsomorphismDefinitions.eq_refl.
  - (* cons case *)
    simpl.
    (* LHS after simpl: to (app (rev t) [h]) 
       RHS: Imported.rev (Imported.cons (to h) (to t)) *)
    (* Rewrite RHS using imported_rev_cons *)
    eapply eq_trans.
    { apply list_to_app_compat. }
    (* Now goal: Imported.app (to (rev t)) (to [h]) = Imported.rev (Imported.cons (to h) (to t)) *)
    eapply eq_sym.
    eapply eq_trans.
    { apply seq_of_eq. apply imported_rev_cons. }
    (* Now goal: Imported.app (Imported.rev (to t)) [to h] = Imported.app (to (rev t)) (to [h]) *)
    apply eq_sym.
    apply f_equal2.
    + (* to (rev t) = Imported.rev (to t) by IH *)
      exact IH.
    + (* to [h] = [to h] *)
      simpl. apply f_equal2.
      * apply IsomorphismDefinitions.eq_refl.
      * apply IsomorphismDefinitions.eq_refl.
Qed.

Instance Original_LF__DOT__Poly_LF_Poly_rev_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) (Original.LF_DOT_Poly.LF.Poly.rev x3) (imported_Original_LF__DOT__Poly_LF_Poly_rev x4).
Proof.
  intros x1 x2 hx x3 x4 H34.
  unfold rel_iso. simpl.
  unfold imported_Original_LF__DOT__Poly_LF_Poly_rev.
  eapply eq_trans.
  - apply list_to_rev_compat.
  - apply f_equal. exact H34.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.rev) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Poly_LF_Poly_rev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.rev) Original_LF__DOT__Poly_LF_Poly_rev_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.rev) imported_Original_LF__DOT__Poly_LF_Poly_rev Original_LF__DOT__Poly_LF_Poly_rev_iso := {}.