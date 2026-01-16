From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__t____tree__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect : forall x : Type, imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree x -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree x := (@Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect).

(* Helper: show that t_tree_to commutes with reflect *)
Fixpoint t_tree_to_reflect {X Y : Type} (hx : Iso X Y) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree X) :
  IsomorphismDefinitions.eq 
    (t_tree_to hx (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect t))
    (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect Y (t_tree_to hx t)) :=
  match t with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_leaf => IsomorphismDefinitions.eq_refl
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p =>
      match p as p0 return IsomorphismDefinitions.eq 
        (t_tree_to hx (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p0)))
        (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect Y (t_tree_to hx (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p0))) with
      | Original.LF_DOT_Poly.LF.Poly.pair (Original.LF_DOT_Poly.LF.Poly.pair l v) r =>
          IsoEq.f_equal3 (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_t_branch Y)
            (t_tree_to_reflect hx r)
            IsomorphismDefinitions.eq_refl
            (t_tree_to_reflect hx l)
      end
  end.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree x1) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree x2),
  rel_iso (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_iso hx) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect x3)
    (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect x4).
Proof.
  intros x1 x2 hx x3 x4 H.
  destruct H as [H]. simpl in *.
  (* H : eq (t_tree_to hx x3) x4 
     Goal: eq (t_tree_to hx (reflect x3)) (reflect x4) *)
  constructor. destruct H.
  exact (t_tree_to_reflect hx x3).
Defined.
Instance: KnownConstant (@Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect) Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect) (@Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect) Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect_iso := {}.