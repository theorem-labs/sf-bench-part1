From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3 : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> SProp := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3).

(* Helper: convert Original.list to Imported.list *)
Definition to_imported_list {x1 x2 : Type} (hx : Iso x1 x2) : Original.LF_DOT_Poly.LF.Poly.list x1 -> imported_Original_LF__DOT__Poly_LF_Poly_list x2 :=
  to (Original_LF__DOT__Poly_LF_Poly_list_iso hx).

Definition from_imported_list {x1 x2 : Type} (hx : Iso x1 x2) : imported_Original_LF__DOT__Poly_LF_Poly_list x2 -> Original.LF_DOT_Poly.LF.Poly.list x1 :=
  from (Original_LF__DOT__Poly_LF_Poly_list_iso hx).

(* Helper: convert Original.Perm3 to Imported.Perm3 *)
Definition Perm3_to {x1 x2 : Type} (hx : Iso x1 x2) (l1 l2 : Original.LF_DOT_Poly.LF.Poly.list x1) :
  Original.LF_DOT_IndProp.LF.IndProp.Perm3 l1 l2 ->
  imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3 (to_imported_list hx l1) (to_imported_list hx l2).
Proof.
  intro p.
  induction p.
  - (* perm3_swap12 *)
    simpl.
    apply Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3_perm3_swap12.
  - (* perm3_swap23 *)
    simpl.
    apply Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3_perm3_swap23.
  - (* perm3_trans *)
    simpl.
    apply (Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3_perm3_trans _ _ _ _ IHp1 IHp2).
Defined.

(* Helper: convert Imported.Perm3 to SInhabited Original.Perm3 - this is allowed since target is SProp *)
Fixpoint Perm3_from_sinhabited {x1 x2 : Type} (hx : Iso x1 x2) {l1 l2 : imported_Original_LF__DOT__Poly_LF_Poly_list x2}
  (p : imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3 l1 l2) {struct p} :
  SInhabited (Original.LF_DOT_IndProp.LF.IndProp.Perm3 (from_imported_list hx l1) (from_imported_list hx l2)) :=
  match p as p' in Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3 _ l1' l2'
        return SInhabited (Original.LF_DOT_IndProp.LF.IndProp.Perm3 (from_imported_list hx l1') (from_imported_list hx l2'))
  with
  | Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3_perm3_swap12 _ a b c =>
      sinhabits (Original.LF_DOT_IndProp.LF.IndProp.perm3_swap12 (from hx a) (from hx b) (from hx c))
  | Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3_perm3_swap23 _ a b c =>
      sinhabits (Original.LF_DOT_IndProp.LF.IndProp.perm3_swap23 (from hx a) (from hx b) (from hx c))
  | Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3_perm3_trans _ l1'' l2'' l3'' p1 p2 =>
      sinhabits (Original.LF_DOT_IndProp.LF.IndProp.perm3_trans 
                   (from_imported_list hx l1'') (from_imported_list hx l2'') (from_imported_list hx l3'')
                   (sinhabitant (Perm3_from_sinhabited hx p1))
                   (sinhabitant (Perm3_from_sinhabited hx p2)))
  end.

Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.Perm3 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3 x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  (* H34 : to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 = x4 (SProp eq) *)
  (* H56 : to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 = x6 (SProp eq) *)
  (* Convert to Logic.eq *)
  apply eq_of_seq in H34.
  apply eq_of_seq in H56.
  (* Rewrite using Logic.eq in goals that are Prop/Type *)
  subst x4 x6.
  (* Now the goal is: Iso (Original.Perm3 x3 x5) (Imported.Perm3 (to ... x3) (to ... x5)) *)
  unshelve eapply Build_Iso.
  - (* to: Original.Perm3 x3 x5 -> Imported.Perm3 (to x3) (to x5) *)
    intro p.
    unfold imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3.
    exact (@Perm3_to x1 x2 hx x3 x5 p).
  - (* from: Imported.Perm3 (to x3) (to x5) -> Original.Perm3 x3 x5 *)
    intro ip.
    (* Use Perm3_from_sinhabited to convert *)
    pose proof (Perm3_from_sinhabited hx ip) as H.
    apply sinhabitant in H.
    (* H : Original.Perm3 (from (to x3)) (from (to x5)) *)
    unfold from_imported_list in H.
    (* Use from_to to show from (to x) = x *)
    pose proof (from_to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3) as Hft3.
    pose proof (from_to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5) as Hft5.
    apply eq_of_seq in Hft3.
    apply eq_of_seq in Hft5.
    rewrite Hft3, Hft5 in H.
    exact H.
  - (* to_from *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. 
    (* proof irrelevance for Prop, converted to SProp eq *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.Perm3) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.Perm3) Original_LF__DOT__IndProp_LF_IndProp_Perm3_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.Perm3) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_Perm3) Original_LF__DOT__IndProp_LF_IndProp_Perm3_iso := {}.