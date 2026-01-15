From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree : Type -> Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree.

(* Forward direction: Original -> Imported *)
Fixpoint tree_to_imported {X Y : Type} (f : X -> Y) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree X) : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree Y :=
  match t with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.leaf _ x => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_leaf Y (f x)
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node _ t1 t2 => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y (tree_to_imported f t1) (tree_to_imported f t2)
  end.

(* Backward direction: Imported -> Original *)
Fixpoint tree_from_imported {X Y : Type} (f : Y -> X) (t : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree Y) : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree X :=
  match t with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_leaf _ y => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.leaf X (f y)
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node _ t1 t2 => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X (tree_from_imported f t1) (tree_from_imported f t2)
  end.

(* Helper to transport equality through tree constructors *)
Definition eq_node1 {X : Type} {t1 t1' t2 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree X} 
  (H : IsomorphismDefinitions.eq t1 t1') : IsomorphismDefinitions.eq (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1 t2) 
                       (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1' t2) :=
  match H in IsomorphismDefinitions.eq _ t1'' return IsomorphismDefinitions.eq (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1 t2) 
                                                       (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1'' t2) with
  | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl
  end.

Definition eq_node2 {X : Type} {t1 t2 t2' : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree X} 
  (H : IsomorphismDefinitions.eq t2 t2') : IsomorphismDefinitions.eq (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1 t2) 
                       (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1 t2') :=
  match H in IsomorphismDefinitions.eq _ t2'' return IsomorphismDefinitions.eq (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1 t2) 
                                                       (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node X t1 t2'') with
  | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl
  end.

Definition eq_inode1 {Y : Type} {t1 t1' t2 : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree Y} 
  (H : IsomorphismDefinitions.eq t1 t1') : IsomorphismDefinitions.eq (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1 t2) 
                       (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1' t2) :=
  match H in IsomorphismDefinitions.eq _ t1'' return IsomorphismDefinitions.eq (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1 t2) 
                                                       (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1'' t2) with
  | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl
  end.

Definition eq_inode2 {Y : Type} {t1 t2 t2' : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree Y} 
  (H : IsomorphismDefinitions.eq t2 t2') : IsomorphismDefinitions.eq (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1 t2) 
                       (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1 t2') :=
  match H in IsomorphismDefinitions.eq _ t2'' return IsomorphismDefinitions.eq (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1 t2) 
                                                       (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node Y t1 t2'') with
  | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl
  end.

Definition eq_trans' {A : Type} {x y z : A} (H1 : IsomorphismDefinitions.eq x y) (H2 : IsomorphismDefinitions.eq y z) : IsomorphismDefinitions.eq x z :=
  match H2 in IsomorphismDefinitions.eq _ z' return IsomorphismDefinitions.eq x z' with
  | IsomorphismDefinitions.eq_refl => H1
  end.

Fixpoint tree_roundtrip1 {X Y : Type} (f : X -> Y) (g : Y -> X) 
  (H : forall x, IsomorphismDefinitions.eq (g (f x)) x) (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree X) 
  : IsomorphismDefinitions.eq (tree_from_imported g (tree_to_imported f t)) t :=
  match t as t0 return IsomorphismDefinitions.eq (tree_from_imported g (tree_to_imported f t0)) t0 with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.leaf _ x => 
      match H x in IsomorphismDefinitions.eq _ x' return IsomorphismDefinitions.eq (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.leaf X (g (f x))) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.leaf X x') with 
      | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl 
      end
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.node _ t1 t2 => 
      eq_trans' (eq_node1 (tree_roundtrip1 f g H t1)) (eq_node2 (tree_roundtrip1 f g H t2))
  end.

Fixpoint tree_roundtrip2 {X Y : Type} (f : X -> Y) (g : Y -> X) 
  (H : forall y, IsomorphismDefinitions.eq (f (g y)) y) (t : Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree Y)
  : IsomorphismDefinitions.eq (tree_to_imported f (tree_from_imported g t)) t :=
  match t as t0 return IsomorphismDefinitions.eq (tree_to_imported f (tree_from_imported g t0)) t0 with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_leaf _ y => 
      match H y in IsomorphismDefinitions.eq _ y' return IsomorphismDefinitions.eq (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_leaf Y (f (g y))) (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_leaf Y y') with 
      | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl 
      end
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_node _ t1 t2 => 
      eq_trans' (eq_inode1 (tree_roundtrip2 f g H t1)) (eq_inode2 (tree_roundtrip2 f g H t2))
  end.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree x2).
Proof.
  intros X Y [f g Hfg Hgf].
  exact (Build_Iso (tree_to_imported f) (tree_from_imported g) 
                   (tree_roundtrip2 f g Hfg) (tree_roundtrip1 f g Hgf)).
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_iso := {}.
