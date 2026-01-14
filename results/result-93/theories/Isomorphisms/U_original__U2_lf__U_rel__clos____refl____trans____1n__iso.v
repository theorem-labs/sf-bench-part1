From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf__U_rel__relation__iso.

Definition imported_Original_LF_Rel_clos__refl__trans__1n : forall x : Type, (x -> x -> SProp) -> x -> x -> SProp := (@Imported.Original_LF_Rel_clos__refl__trans__1n).

(* Helper to get the rel_iso *)
Definition rel_iso_refl' {x1 x2} (hx : Iso x1 x2) (a : x1) : rel_iso hx a (hx.(to) a) := IsomorphismDefinitions.eq_refl.

(* Forward conversion: Original clos_refl_trans_1n to Imported *)
(* We need to generalize over the starting point a for the recursion to work *)
Definition crt1n_to_imp (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp)
  (Hrel : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8))
  : forall (a b : x1), Original.LF.Rel.clos_refl_trans_1n x3 a b -> imported_Original_LF_Rel_clos__refl__trans__1n x4 (hx.(to) a) (hx.(to) b).
Proof.
  refine (fix IHrec (a b : x1) (H : Original.LF.Rel.clos_refl_trans_1n x3 a b) {struct H} 
          : imported_Original_LF_Rel_clos__refl__trans__1n x4 (hx.(to) a) (hx.(to) b) := _).
  destruct H as [| y z Hxy Hrest].
  - apply Imported.Original_LF_Rel_clos__refl__trans__1n_rt1n_refl.
  - refine (Imported.Original_LF_Rel_clos__refl__trans__1n_rt1n_trans _ _ _ (hx.(to) y) _ _ (IHrec y z Hrest)).
    apply (Hrel a (hx.(to) a) (rel_iso_refl' hx a) y (hx.(to) y) (rel_iso_refl' hx y)).(to).
    exact Hxy.
Defined.

(* We need a symmetry lemma for SProp eq *)
Definition seq_sym {A : Type} {x y : A} (e : IsomorphismDefinitions.eq x y) : IsomorphismDefinitions.eq y x :=
  match e with IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl end.

(* Transport for SProp using IsomorphismDefinitions.eq *)
Definition transport_x4_seq {x2 : Type} (x4 : x2 -> x2 -> SProp) 
  {a a' b b' : x2} (ea : IsomorphismDefinitions.eq a a') (eb : IsomorphismDefinitions.eq b b') (h : x4 a b) : x4 a' b' :=
  match ea in IsomorphismDefinitions.eq _ w1, eb in IsomorphismDefinitions.eq _ w2 return x4 w1 w2 with
  | IsomorphismDefinitions.eq_refl, IsomorphismDefinitions.eq_refl => h
  end.

(* Backward conversion: Imported to Original clos_refl_trans_1n using SInhabited *)
Definition crt1n_from_imp (x1 x2 : Type) (hx : Iso x1 x2) 
  (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp)
  (Hrel : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8))
  : forall (a b : x2), imported_Original_LF_Rel_clos__refl__trans__1n x4 a b 
    -> SInhabited (Original.LF.Rel.clos_refl_trans_1n x3 (hx.(from) a) (hx.(from) b)).
Proof.
  refine (fix IH (a b : x2) (H : imported_Original_LF_Rel_clos__refl__trans__1n x4 a b) {struct H}
          : SInhabited (Original.LF.Rel.clos_refl_trans_1n x3 (hx.(from) a) (hx.(from) b)) := _).
  destruct H as [a' | a' y z Hxy Hrest].
  - apply sinhabits. apply Original.LF.Rel.rt1n_refl.
  - apply sinhabits.
    apply (Original.LF.Rel.rt1n_trans _ _ (hx.(from) y)).
    + apply (Hrel (hx.(from) a') (hx.(to) (hx.(from) a')) (rel_iso_refl' hx (hx.(from) a')) 
                  (hx.(from) y) (hx.(to) (hx.(from) y)) (rel_iso_refl' hx (hx.(from) y))).(from).
      (* Transport Hxy from x4 a' y to x4 (to (from a')) (to (from y)) *)
      (* to_from : to (from a') = a', so we use symmetry to get a' = to (from a') *)
      exact (transport_x4_seq x4 (seq_sym (to_from hx a')) (seq_sym (to_from hx y)) Hxy).
    + apply sinhabitant.
      apply IH.
      exact Hrest.
Defined.

(* Helper: transport clos_refl_trans_1n along two SProp equalities *)
Definition transport_crt1n {A : Type} {R : Original.LF.Rel.relation A} {a a' c c' : A} 
  (ea : IsomorphismDefinitions.eq a a') (ec : IsomorphismDefinitions.eq c c') 
  (p : Original.LF.Rel.clos_refl_trans_1n R a c) : Original.LF.Rel.clos_refl_trans_1n R a' c' :=
  match ea in IsomorphismDefinitions.eq _ x return 
        (forall y, IsomorphismDefinitions.eq c y -> Original.LF.Rel.clos_refl_trans_1n R x y) with
  | IsomorphismDefinitions.eq_refl => 
      fun y ec' => match ec' in IsomorphismDefinitions.eq _ z return Original.LF.Rel.clos_refl_trans_1n R a z with
                   | IsomorphismDefinitions.eq_refl => p
                   end
  end c' ec.

Instance Original_LF_Rel_clos__refl__trans__1n_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  forall (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (Original.LF.Rel.clos_refl_trans_1n x3 x5 x7) (imported_Original_LF_Rel_clos__refl__trans__1n x4 x6 x8).
Proof.
  intros A B isoAB R R' Hrel a b' hx1 c d' hx2.
  unfold rel_iso in hx1, hx2.
  destruct hx1, hx2.
  (* Build the iso manually, coercing the Prop to Type *)
  unshelve eapply (@Build_Iso (Original.LF.Rel.clos_refl_trans_1n R a c : Type) 
                               (imported_Original_LF_Rel_clos__refl__trans__1n R' (isoAB a) (isoAB c))
                               _ _ _ _).
  - (* to *)
    exact (@crt1n_to_imp A B isoAB R R' Hrel a c).
  - (* from *)
    intro H.
    exact (transport_crt1n (from_to isoAB a) (from_to isoAB c) 
            (sinhabitant (@crt1n_from_imp A B isoAB R R' Hrel (isoAB.(to) a) (isoAB.(to) c) H))).
  - (* to_from *)
    intro x. exact IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro x. apply seq_of_peq_t. apply ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant (@Original.LF.Rel.clos_refl_trans_1n) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF_Rel_clos__refl__trans__1n) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF.Rel.clos_refl_trans_1n) Original_LF_Rel_clos__refl__trans__1n_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF.Rel.clos_refl_trans_1n) (@Imported.Original_LF_Rel_clos__refl__trans__1n) Original_LF_Rel_clos__refl__trans__1n_iso := {}.