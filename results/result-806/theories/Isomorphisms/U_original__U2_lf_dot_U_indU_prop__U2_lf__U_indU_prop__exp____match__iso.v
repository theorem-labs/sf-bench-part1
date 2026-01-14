From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x -> SProp := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match).

(* The approach: use iso_trans with iso_SInhabited, then show SInhabited equivalence *)

(* Forward direction: Original.exp_match -> SInhabited (Imported.exp_match) *)
(* We need to show that Original.exp_match x3 x5 -> Imported.exp_match x4 x6 (in SProp) *)

(* Helper to transport along IsomorphismDefinitions.eq for the list index *)
Definition eq_rect_list {x2} (l1 l2 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
  (e : IsomorphismDefinitions.eq l1 l2)
  (re : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
  (m : Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match x2 l1 re)
  : Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match x2 l2 re :=
  match e in IsomorphismDefinitions.eq _ l return Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match x2 l re with
  | IsomorphismDefinitions.eq_refl => m
  end.

Definition eq_rect_list_back {x1} (l1 l2 : Original.LF_DOT_Poly.LF.Poly.list x1)
  (e : IsomorphismDefinitions.eq l1 l2)
  (re : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1)
  (m : Original.LF_DOT_IndProp.LF.IndProp.exp_match l1 re)
  : Original.LF_DOT_IndProp.LF.IndProp.exp_match l2 re :=
  match e in IsomorphismDefinitions.eq _ l return Original.LF_DOT_IndProp.LF.IndProp.exp_match l re with
  | IsomorphismDefinitions.eq_refl => m
  end.

(* Forward: Original.exp_match -> Imported.exp_match *)
Fixpoint exp_match_to_aux (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : Original.LF_DOT_Poly.LF.Poly.list x1)
  (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1)
  (m : Original.LF_DOT_IndProp.LF.IndProp.exp_match x3 x5)
  {struct m}
  : Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match x2
      (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3)
      (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x5).
Proof.
  destruct m as [ | c | s1 re1 s2 re2 m1 m2 | s1 re1 re2 m1 | s2 re1 re2 m2 | re | s1 s2 re m1 m2 ].
  - (* MEmpty *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match_MEmpty x2).
  - (* MChar *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match_MChar x2 (to hx c)).
  - (* MApp *)
    apply (eq_rect_list (eq_sym (list_to_app_compat hx s1 s2))).
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match_MApp x2 _ _ _ _
            (exp_match_to_aux x1 x2 hx s1 re1 m1)
            (exp_match_to_aux x1 x2 hx s2 re2 m2)).
  - (* MUnionL *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match_MUnionL x2 _ _ _
            (exp_match_to_aux x1 x2 hx s1 re1 m1)).
  - (* MUnionR *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match_MUnionR x2 _ _ _
            (exp_match_to_aux x1 x2 hx s2 re2 m2)).
  - (* MStar0 *)
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match_MStar0 x2
            (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) re)).
  - (* MStarApp *)
    apply (eq_rect_list (eq_sym (list_to_app_compat hx s1 s2))).
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match_MStarApp x2 _ _ _
            (exp_match_to_aux x1 x2 hx s1 re m1)
            (exp_match_to_aux x1 x2 hx s2 (Original.LF_DOT_IndProp.LF.IndProp.Star re) m2)).
Defined.


Definition exp_match_to (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
  (H1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4)
  (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
  (H2 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x5 x6)
  (m : Original.LF_DOT_IndProp.LF.IndProp.exp_match x3 x5)
  : imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x4 x6.
Proof.
  destruct H1. destruct H2.
  exact (exp_match_to_aux hx m).
Defined.

(* Backward compat lemma for list app *)
Lemma list_from_app_compat : forall (x1 x2 : Type) (Hx : Iso x1 x2)
  (l1 l2 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  IsomorphismDefinitions.eq
    (from (Original_LF__DOT__Poly_LF_Poly_list_iso Hx) (Imported.Original_LF__DOT__Poly_LF_Poly_app x2 l1 l2))
    (Original.LF_DOT_Poly.LF.Poly.app (from (Original_LF__DOT__Poly_LF_Poly_list_iso Hx) l1) (from (Original_LF__DOT__Poly_LF_Poly_list_iso Hx) l2)).
Proof.
  intros x1 x2 Hx l1 l2.
  induction l1 as [|h t IH].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal2 (@Original.LF_DOT_Poly.LF.Poly.cons x1)).
    + apply IsomorphismDefinitions.eq_refl.
    + exact IH.
Qed.

(* For the backward direction, we exploit that both types are propositions
   and we can use SInhabited to mediate *)
Definition exp_match_from_sinhabited (x1 x2 : Type) (hx : Iso x1 x2) 
  (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
  (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
  (m : Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match x2 x4 x6)
  : SInhabited (Original.LF_DOT_IndProp.LF.IndProp.exp_match
      (from (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x4)
      (from (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x6)).
Proof.
  (* Now we can destruct m since the result is SProp *)
  revert x4 x6 m.
  fix IH 3.
  intros x4 x6 m.
  destruct m as [ | c | s1 re1 s2 re2 m1 m2 | s1 re1 re2 m1 | s2 re1 re2 m2 | re | s1 s2 re m1 m2 ].
  - (* MEmpty *)
    apply sinhabits. exact Original.LF_DOT_IndProp.LF.IndProp.MEmpty.
  - (* MChar *)
    apply sinhabits. exact (Original.LF_DOT_IndProp.LF.IndProp.MChar (from hx c)).
  - (* MApp *)
    pose proof (IH s1 re1 m1) as H1.
    pose proof (IH s2 re2 m2) as H2.
    apply sinhabits.
    apply (eq_rect_list_back (eq_sym (list_from_app_compat hx s1 s2))).
    exact (Original.LF_DOT_IndProp.LF.IndProp.MApp _ _ _ _
            (sinhabitant H1)
            (sinhabitant H2)).
  - (* MUnionL *)
    pose proof (IH s1 re1 m1) as H1.
    apply sinhabits.
    exact (Original.LF_DOT_IndProp.LF.IndProp.MUnionL _ _ _
            (sinhabitant H1)).
  - (* MUnionR *)
    pose proof (IH s2 re2 m2) as H2.
    apply sinhabits.
    exact (Original.LF_DOT_IndProp.LF.IndProp.MUnionR _ _ _
            (sinhabitant H2)).
  - (* MStar0 *)
    apply sinhabits.
    exact (Original.LF_DOT_IndProp.LF.IndProp.MStar0
            (from (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) re)).
  - (* MStarApp *)
    pose proof (IH s1 re m1) as H1.
    pose proof (IH s2 (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_Star x2 re) m2) as H2.
    apply sinhabits.
    apply (eq_rect_list_back (eq_sym (list_from_app_compat hx s1 s2))).
    exact (Original.LF_DOT_IndProp.LF.IndProp.MStarApp _ _ _
            (sinhabitant H1)
            (sinhabitant H2)).
Defined.

Definition exp_match_from (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
  (H1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4)
  (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
  (H2 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x5 x6)
  (m : imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x4 x6)
  : Original.LF_DOT_IndProp.LF.IndProp.exp_match x3 x5.
Proof.
  cbv [rel_iso] in H1, H2.
  destruct H1. destruct H2.
  (* Now m : imported_exp_match (to ... x3) (to ... x5) *)
  pose proof (sinhabitant (exp_match_from_sinhabited hx m)) as result.
  (* result : exp_match (from (to x3)) (from (to x5)) *)
  pose proof (from_to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3) as Hlist.
  pose proof (from_to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x5) as Hreg.
  exact (match Hlist in IsomorphismDefinitions.eq _ l, Hreg in IsomorphismDefinitions.eq _ r 
         return Original.LF_DOT_IndProp.LF.IndProp.exp_match l r with
         | IsomorphismDefinitions.eq_refl, IsomorphismDefinitions.eq_refl => result
         end).
Defined.

Instance Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
     (H1 : @rel_iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2) (@Original_LF__DOT__Poly_LF_Poly_list_iso x1 x2 hx) x3 x4)
     (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
     (H2 : @rel_iso (Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2) (@Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso x1 x2 hx) x5 x6),
   Iso (@Original.LF_DOT_IndProp.LF.IndProp.exp_match x1 x3 x5) (@imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H1 x5 x6 H2.
  cbv [rel_iso] in H1, H2.
  destruct H1. destruct H2.
  unshelve eapply Build_Iso.
  - (* to *)
    exact (@exp_match_to_aux x1 x2 hx x3 x5).
  - (* from *)
    intro m.
    pose proof (sinhabitant (exp_match_from_sinhabited hx m)) as result.
    pose proof (from_to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3) as Hlist.
    pose proof (from_to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x5) as Hreg.
    exact (match Hlist in IsomorphismDefinitions.eq _ l, Hreg in IsomorphismDefinitions.eq _ r 
           return Original.LF_DOT_IndProp.LF.IndProp.exp_match l r with
           | IsomorphismDefinitions.eq_refl, IsomorphismDefinitions.eq_refl => result
           end).
  - intro m. exact IsomorphismDefinitions.eq_refl.
  - intro m. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.exp_match) := {}. 
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match) := {}. 
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.exp_match) Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.exp_match) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_exp__match) Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso := {}.
