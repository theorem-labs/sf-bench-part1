From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Poly_LF_Poly_nth__error : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_nat -> imported_Original_LF__DOT__Poly_LF_Poly_option x := (@Imported.Original_LF__DOT__Poly_LF_Poly_nth__error).

(* Helper: convert Original nat to Imported nat *)
Fixpoint nat_to_imported' (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported' n')
  end.

(* Helper: convert Original option to Imported option *)
Definition option_to_imported {x1 x2 : Type} (hx : Iso x1 x2) (o : Original.LF_DOT_Poly.LF.Poly.option x1) : imported_Original_LF__DOT__Poly_LF_Poly_option x2 :=
  match o with
  | Original.LF_DOT_Poly.LF.Poly.Some v => Imported.Original_LF__DOT__Poly_LF_Poly_option_Some x2 (to hx v)
  | Original.LF_DOT_Poly.LF.Poly.None => Imported.Original_LF__DOT__Poly_LF_Poly_option_None x2
  end.

(* Helper: convert Original list to Imported list *)
Fixpoint list_to_imported' {x1 x2 : Type} (hx : Iso x1 x2) (l : Original.LF_DOT_Poly.LF.Poly.list x1) : imported_Original_LF__DOT__Poly_LF_Poly_list x2 :=
  match l with
  | Original.LF_DOT_Poly.LF.Poly.nil => Imported.Original_LF__DOT__Poly_LF_Poly_list_nil x2
  | Original.LF_DOT_Poly.LF.Poly.cons h t => 
      Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2 (to hx h) (list_to_imported' hx t)
  end.

(* Helper lemma: nth_error commutes with the isomorphisms *)
Lemma nth_error_commutes : forall (x1 x2 : Type) (hx : Iso x1 x2) (l : Original.LF_DOT_Poly.LF.Poly.list x1) (n : nat),
  IsomorphismDefinitions.eq 
    (option_to_imported hx (Original.LF_DOT_Poly.LF.Poly.nth_error l n))
    (Imported.Original_LF__DOT__Poly_LF_Poly_nth__error x2 (list_to_imported' hx l) (nat_to_imported' n)).
Proof.
  intros x1 x2 hx l.
  induction l as [|h t IH]; intro n.
  - simpl. destruct n; simpl; apply IsomorphismDefinitions.eq_refl.
  - destruct n as [|n'].
    + simpl. apply IsomorphismDefinitions.eq_refl.
    + simpl. apply IH.
Defined.

(* The option_iso to function is the same as option_to_imported *)
Lemma option_to_eq : forall (x1 x2 : Type) (hx : Iso x1 x2) o, 
  IsomorphismDefinitions.eq (to (Original_LF__DOT__Poly_LF_Poly_option_iso hx) o) (option_to_imported hx o).
Proof.
  intros x1 x2 hx o. destruct o as [v|].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsomorphismDefinitions.eq_refl.
Defined.

(* The nat_iso to function is the same as nat_to_imported' *)
Lemma nat_to_eq' : forall n, IsomorphismDefinitions.eq (to nat_iso n) (nat_to_imported' n).
Proof.
  intro n. induction n as [|n' IH].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal Imported.nat_S IH).
Defined.

(* The list_iso to function is the same as list_to_imported' *)
Lemma list_to_eq' : forall (x1 x2 : Type) (hx : Iso x1 x2) l, 
  IsomorphismDefinitions.eq (to (Original_LF__DOT__Poly_LF_Poly_list_iso hx) l) (list_to_imported' hx l).
Proof.
  intros x1 x2 hx l. induction l as [|h t IH].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal2 (Imported.Original_LF__DOT__Poly_LF_Poly_list_cons x2) (IsomorphismDefinitions.eq_refl _) IH).
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_nth__error_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat),
  rel_iso nat_iso x5 x6 -> rel_iso (Original_LF__DOT__Poly_LF_Poly_option_iso hx) (Original.LF_DOT_Poly.LF.Poly.nth_error x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_nth__error x4 x6).
Proof.
  intros A B hx l l' Hlist n n' Hnat.
  unfold rel_iso in *.
  pose proof (@nth_error_commutes A B hx l n) as Hnth.
  pose proof (@option_to_eq A B hx (Original.LF_DOT_Poly.LF.Poly.nth_error l n)) as Hopt.
  pose proof (nat_to_eq' n) as Hnat_eq.
  pose proof (@list_to_eq' A B hx l) as Hlist_eq.
  destruct Hlist using IsomorphismDefinitions.eq_sind.
  destruct Hnat using IsomorphismDefinitions.eq_sind.
  destruct Hlist_eq using IsomorphismDefinitions.eq_sind.
  destruct Hnat_eq using IsomorphismDefinitions.eq_sind.
  destruct Hopt using IsomorphismDefinitions.eq_sind.
  exact Hnth.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Poly.LF.Poly.nth_error) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Poly_LF_Poly_nth__error) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.nth_error) Original_LF__DOT__Poly_LF_Poly_nth__error_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.nth_error) (@Imported.Original_LF__DOT__Poly_LF_Poly_nth__error) Original_LF__DOT__Poly_LF_Poly_nth__error_iso := {}.