From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree : Type -> Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree.

(* The original has: t_branch : (t_tree X * X * t_tree X) -> t_tree X
   The imported has: t_branch : t_tree X -> X -> t_tree X -> t_tree X *)

Fixpoint t_tree_to {X Y : Type} (hx : Iso X Y) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree X) : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree Y :=
  match t with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_leaf => 
      Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_t_leaf Y
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p =>
      match p with
      | Original.LF_DOT_Poly.LF.Poly.pair (Original.LF_DOT_Poly.LF.Poly.pair l v) r => 
          Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_t_branch Y 
            (t_tree_to hx l) (to hx v) (t_tree_to hx r)
      end
  end.

Fixpoint t_tree_from {X Y : Type} (hx : Iso X Y) (t : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree Y) : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree X :=
  match t with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_t_leaf _ => 
      Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_leaf
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_t_branch _ l v r =>
      Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch 
        (Original.LF_DOT_Poly.LF.Poly.pair (Original.LF_DOT_Poly.LF.Poly.pair (t_tree_from hx l) (from hx v)) (t_tree_from hx r))
  end.

Lemma t_tree_to_from {X Y : Type} (hx : Iso X Y) (t : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree Y) :
  IsomorphismDefinitions.eq (t_tree_to hx (t_tree_from hx t)) t.
Proof.
  induction t as [| l IHl v r IHr].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl.
    apply (IsoEq.f_equal3 (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_t_branch Y) IHl (to_from hx v) IHr).
Defined.

Fixpoint t_tree_from_to {X Y : Type} (hx : Iso X Y) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree X) :
  IsomorphismDefinitions.eq (t_tree_from hx (t_tree_to hx t)) t :=
  match t with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_leaf => IsomorphismDefinitions.eq_refl
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p =>
      match p as p0 return IsomorphismDefinitions.eq (t_tree_from hx (t_tree_to hx (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p0))) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p0) with
      | Original.LF_DOT_Poly.LF.Poly.pair (Original.LF_DOT_Poly.LF.Poly.pair l v) r =>
          IsoEq.f_equal (fun p => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_branch p)
            (IsoEq.f_equal2 (@Original.LF_DOT_Poly.LF.Poly.pair _ _)
              (IsoEq.f_equal2 (@Original.LF_DOT_Poly.LF.Poly.pair _ _)
                (t_tree_from_to hx l)
                (from_to hx v))
              (t_tree_from_to hx r))
      end
  end.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree x2).
Proof.
  intros X Y hx.
  unshelve eapply Build_Iso.
  - exact (t_tree_to hx).
  - exact (t_tree_from hx).
  - exact (t_tree_to_from hx).
  - exact (t_tree_from_to hx).
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_iso := {}.