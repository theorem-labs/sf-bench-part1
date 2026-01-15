From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso
  Isomorphisms.U_corelib__U_init__U_logic__eq__iso
  Isomorphisms.U_original__U_false__iso
  Isomorphisms.or__iso.

Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In : forall x : Type, x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In.

(* Convert Imported.Eq to standard equality *)
Lemma Imported_Eq_SProp_to_eq : forall (x y : SProp), Imported.Eq SProp x y -> x = y.
Proof. intros x y H. destruct H. reflexivity. Qed.

(* Reduction equation helpers *)
Lemma RecallIn_In_nil_eq : forall (A : Type) (x : A),
  Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In A x
    (Imported.Original_LF__DOT__Poly_LF_Poly_list_nil A) = Imported.FalseType.
Proof.
  intros. apply Imported_Eq_SProp_to_eq.
  exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In_nil A x).
Qed.

Lemma RecallIn_In_cons_eq : forall (A : Type) (x x' : A) (l' : Imported.Original_LF__DOT__Poly_LF_Poly_list A),
  Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In A x
    (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons A x' l') =
  Imported.or (Imported.Corelib_Init_Logic_eq A x' x)
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In A x l').
Proof.
  intros. apply Imported_Eq_SProp_to_eq.
  exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In_cons A x x' l').
Qed.

Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.RecallIn.In x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In x4 x6).
Proof.
  intros x1 x2 hx x3 x4 hx34 x5.
  induction x5 as [|h5 t5 IH].
  - (* nil case *)
    intros x6 hx56.
    simpl.
    pose proof (proj_rel_iso hx56) as Heq.
    simpl in Heq.
    unfold imported_Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In.
    rewrite <- Heq.
    rewrite RecallIn_In_nil_eq.
    exact Original_False_iso.
  - (* cons case *)
    intros x6 hx56.
    simpl.
    pose proof (proj_rel_iso hx56) as Heq.
    simpl in Heq.
    unfold imported_Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In.
    rewrite <- Heq.
    rewrite RecallIn_In_cons_eq.
    apply or_iso.
    + (* h5 = x3 <-> Imported.Corelib_Init_Logic_eq (hx h5) x4 *)
      apply (@Corelib_Init_Logic_eq_iso x1 x2 hx h5 (to hx h5)).
      * constructor. reflexivity.
      * exact hx34.
    + apply IH.
      constructor. reflexivity.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.RecallIn.In := {}.
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In := {}.
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.RecallIn.In Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.RecallIn.In Imported.Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In Original_LF__DOT__IndProp_LF_IndProp_RecallIn_In_iso := {}.
