From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Ltac2 Require Ltac2.
From IsomorphismChecker Require Ltac2Utils.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Polymorphic Inductive Cumulativity.
#[local] Set Implicit Arguments.
#[export]
Hint Resolve eq_refl: core.
Arguments eq {α} a _.
Arguments eq_refl {α a} , [α] a.

Arguments eq_ind [α] a P _ y _ : rename.
Arguments eq_rec [α] a P _ y _ : rename.
Arguments eq_rect [α] a P _ y _ : rename.

(* Variant SInhabited@{s|u|} (A : Type@{s|u}) : SProp := sinhabits : A -> SInhabited A.
Arguments sinhabits {A} a.
Variant inhabited@{s|u|} (A : Type@{s|u}) : Prop := inhabits : A -> inhabited A.
Arguments inhabits {A} a.
Definition inhabitant {A : SProp} (x : inhabited A) : A := match x with inhabits a => a end. *)
Variant SInhabited (A : Prop) : SProp := sinhabits : A -> SInhabited A.
Arguments sinhabits {A} a.
Variant inhabited@{s|u|} (A : Type@{s|u}) : Prop := inhabits : A -> inhabited A.
Arguments inhabits {A} a.
Definition inhabitant@{} {A : SProp} (x : inhabited@{SProp|Set} A) : A := match x with inhabits a => a end.

Axiom SInhabited_Prop_injective@{} : forall (p q : Prop), SInhabited p = SInhabited q -> p = q.
Axiom sinhabitant@{} : forall {A : Prop}, SInhabited A -> A.
Axiom eq_SInhabited_inhabited@{} : forall x : SProp, SInhabited (inhabited@{SProp|Set} x) = x.

(* Definition cumulative_SInhabited_p_of_t@{u} {A : Prop} : SInhabited@{Type|u} A -> SInhabited@{Prop|u} A := fun x => match x with sinhabits a => sinhabits a end.
Definition cumulative_SInhabited_t_of_p@{u} {A : Prop} : SInhabited@{Prop|u} A -> SInhabited@{Type|u} A := fun x => match x with sinhabits a => sinhabits a end.
Definition sinhabitant_Prop@{} {A : Prop} (a : SInhabited@{Prop|Set} A) : A := sinhabitant (cumulative_SInhabited_t_of_p a). *)

#[local] Open Scope lean_scope.
#[local] Set Warnings "-notation-overridden".
#[local] Notation "x = y" := (eq x y) : type_scope.
#[local] Notation "x <> y" := (eq x y -> False) : type_scope.
#[local] Set Universe Polymorphism.
Module Import LeanEq.
Section Logic_lemmas.
  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
    Proof.
      destruct 1; trivial.
    Defined.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem eq_trans_r : x = y -> z = y -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
      destruct 1; trivial.
    Defined.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      intros h1 h2; apply h1; destruct h2; trivial.
    Qed.

  End equality.

  Definition eq_sind_r :
    forall (A:Type) (x:A) (P:A -> SProp), P x -> forall y:A, y = x -> P y.
  Proof.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Register eq_ind_r as core.eq.ind_r.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.
End Logic_lemmas.

Module EqNotations.
Scheme Minimality for eq Sort Type.

  Notation "'rew' H 'in' H'" := (eq_rect_nodep _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect_nodep P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (rew (eq_sym H) in H')
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (rew [P] H in H')
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect_nodep _ H' H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect_nodep P H' H)
    (at level 10, H' at level 10, only parsing).

  Notation "'rew' 'dependent' H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, only parsing).
  Notation "'rew' 'dependent' <- H 'in' H'"
    := (match eq_sym H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name, only parsing).
  Notation "'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  <-  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          only parsing).
  Notation "'rew' 'dependent' <- [ P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
End EqNotations.

Import EqNotations.

Section equality_dep.
  Variable A : Type.
  Variable B : A -> Type.
  Variable f : forall x, B x.
  Variables x y : A.

  Theorem f_equal_dep (H: x = y) : rew H in f x = f y.
  Proof.
    destruct H; reflexivity.
  Defined.

End equality_dep.

Lemma f_equal_dep2 {A A' B B'} (f : A -> A') (g : forall a:A, B a -> B' (f a))
  {x1 x2 : A} {y1 : B x1} {y2 : B x2} (H : x1 = x2) :
  rew H in y1 = y2 -> rew f_equal f H in g x1 y1 = g x2 y2.
Proof.
  destruct H, 1. reflexivity.
Defined.

Lemma rew_opp_r A (P:A->Type) (x y:A) (H:x=y) (a:P y) : rew H in rew <- H in a = a.
Proof.
destruct H.
reflexivity.
Defined.

Lemma rew_opp_l A (P:A->Type) (x y:A) (H:x=y) (a:P x) : rew <- H in rew H in a = a.
Proof.
destruct H.
reflexivity.
Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.
Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

(* Theorem f_equal_compose A B C (a b:A) (f:A->B) (g:B->C) (e:a=b) :
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
Proof.
  destruct e. reflexivity.
Defined.

(** The groupoid structure of equality *)

Theorem eq_trans_refl_l A (x y:A) (e:x=y) : eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_trans_refl_r A (x y:A) (e:x=y) : eq_trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_sym_involutive A (x y:A) (e:x=y) : eq_sym (eq_sym e) = e.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_l A (x y:A) (e:x=y) : eq_trans (eq_sym e) e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_r A (x y:A) (e:x=y) : eq_trans e (eq_sym e) = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_assoc A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t) :
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  destruct e''; reflexivity.
Defined. *)

Theorem rew_map A B (P:B->Type) (f:A->B) x1 x2 (H:x1=x2) (y:P (f x1)) :
  rew [fun x => P (f x)] H in y = rew f_equal f H in y.
Proof.
  destruct H; reflexivity.
Defined.

Theorem eq_trans_map {A B} {x1 x2 x3:A} {y1:B x1} {y2:B x2} {y3:B x3}
  (H1:x1=x2) (H2:x2=x3) (H1': rew H1 in y1 = y2) (H2': rew H2 in y2 = y3) :
  rew eq_trans H1 H2 in y1 = y3.
Proof.
  destruct H2. exact (eq_trans H1' H2').
Defined.

Lemma map_subst {A} {P Q:A->Type} (f : forall x, P x -> Q x) {x y} (H:x=y) (z:P x) :
  rew H in f x z = f y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma map_subst_map {A B} {P:A->Type} {Q:B->Type} (f:A->B) (g : forall x, P x -> Q (f x))
  {x y} (H:x=y) (z:P x) :
  rew f_equal f H in g x z = g y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma rew_swap A (P:A->Type) x1 x2 (H:x1=x2) (y1:P x1) (y2:P x2) : rew H in y1 = y2 -> y1 = rew <- H in y2.
Proof.
  destruct H. trivial.
Defined.

Lemma rew_compose A (P:A->Type) x1 x2 x3 (H1:x1=x2) (H2:x2=x3) (y:P x1) :
  rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.
Proof.
  destruct H2. reflexivity.
Defined.

(** Extra properties of equality *)

(* Theorem eq_id_comm_l A (f:A->A) (Hf:forall a, a = f a) a : f_equal f (Hf a) = Hf (f a).
Proof.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf a)).
  destruct (Hf a) at 1 2.
  destruct (Hf a).
  reflexivity.
Defined.

Theorem eq_id_comm_r A (f:A->A) (Hf:forall a, f a = a) a : f_equal f (Hf a) = Hf (f a).
Proof.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf (f (f a)))).
  set (Hfsymf := fun a => eq_sym (Hf a)).
  change (eq_sym (Hf (f (f a)))) with (Hfsymf (f (f a))).
  pattern (Hfsymf (f (f a))).
  destruct (eq_id_comm_l f Hfsymf (f a)).
  destruct (eq_id_comm_l f Hfsymf a).
  unfold Hfsymf.
  destruct (Hf a). simpl.
  rewrite eq_trans_refl_l.
  reflexivity.
Defined.

Lemma eq_refl_map_distr A B x (f:A->B) : f_equal f (eq_refl x) = eq_refl (f x).
Proof.
  reflexivity.
Qed.

Lemma eq_trans_map_distr A B x y z (f:A->B) (e:x=y) (e':y=z) : f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
destruct e'.
reflexivity.
Defined.

Lemma eq_sym_map_distr A B (x y:A) (f:A->B) (e:x=y) : eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
destruct e.
reflexivity.
Defined.

Lemma eq_trans_sym_distr A (x y z:A) (e:x=y) (e':y=z) : eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
destruct e, e'.
reflexivity.
Defined. *)

Lemma eq_trans_rew_distr A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x) :
    rew (eq_trans e e') in k = rew e' in rew e in k.
Proof.
  destruct e, e'; reflexivity.
Qed.

Lemma rew_const A P (x y:A) (e:x=y) (k:P) :
    rew [fun _ => P] e in k = k.
Proof.
  destruct e; reflexivity.
Qed.

Lemma seq_of_eq@{u} {A : Type@{u}} {x y : A} (H : Logic.eq x y) : Lean.eq x y.
Proof. destruct H; reflexivity. Defined.
Lemma eq_of_seq@{u} {A : Type@{u}} {x y : A} (H : Lean.eq x y) : Logic.eq x y.
Proof. destruct H; reflexivity. Defined.
End LeanEq.
From IsomorphismChecker Require Import IsomorphismDefinitions.
(* no idea why we need to do this again... *)
Lemma uniso_eq A A' (isoA : Iso A A') (x y : A) : Logic.eq (isoA.(to) x) (isoA.(to) y) -> Logic.eq x y.
Proof. intro H; apply (Logic.f_equal isoA.(from)) in H; rewrite !isoA.(from_to) in H; exact H. Defined.
Lemma uniso A A' (isoA : Iso A A') (x y : A) : isoA.(to) x = isoA.(to) y -> x = y.
Proof. intro H; eapply LeanEq.seq_of_eq, uniso_eq, LeanEq.eq_of_seq; exact H. Defined.

Module Import IsoEq.
#[local] Open Scope lean_scope.
#[local] Set Warnings "-notation-overridden".
#[local] Notation "x = y" := (IsomorphismDefinitions.eq x y) : type_scope.
#[local] Notation "x <> y" := (IsomorphismDefinitions.not@{SProp|Set} (IsomorphismDefinitions.eq x y)) : type_scope.
#[local] Set Universe Polymorphism.
Theorem eq_sym@{s|u|} {A : Type@{s|u}} {x y : A} (H : x = y) : y = x.
Proof. destruct H; reflexivity. Defined.
Theorem eq_trans@{s|u|} {A : Type@{s|u}} {x y z : A} (H1 : x = y) (H2 : y = z) : x = z.
Proof. destruct H2, H1; reflexivity. Defined.
Theorem eq_trans_r@{s|u|} {A : Type@{s|u}} {x y z : A} (H1 : x = y) (H2 : z = y) : x = z.
Proof. destruct H2, H1; trivial. Defined.
Theorem f_equal@{s s'|u u'|} {A : Type@{s|u}} {B : Type@{s'|u'}} (f : A -> B) {x y : A} (H : x = y) : f x = f y.
Proof. destruct H; trivial. Defined.
Theorem not_eq_sym@{s|u|} {A : Type@{s|u}} {x y : A} (H : x <> y) : y <> x.
Proof. red; intros h1; apply H; destruct h1; trivial. Qed.
Definition eq_srect@{s s'|u u'|} {A : Type@{s|u}} {x : A} (P : A -> Type@{s'|u'}) (H : P x) {y : A} (H0 : x = y) : P y.
Proof. destruct H0; exact H. Defined.
Definition eq_srect_r@{s s'|u u'|} {A : Type@{s|u}} {x : A} (P : A -> Type@{s'|u'}) (H : P x) {y : A} (H0 : y = x) : P y.
Proof. apply eq_sym in H0; eapply eq_srect; eassumption. Defined.
Definition eq_ind_r@{s|u|} {A : Type@{s|u}} {x : A} (P : A -> Prop) (H : P x) {y : A} (H0 : y = x) : P y.
Proof. eapply eq_srect_r; eassumption. Defined.
Definition eq_rec_r@{s|u|} {A : Type@{s|u}} {x : A} (P : A -> Set) (H : P x) {y : A} (H0 : y = x) : P y.
Proof. eapply eq_srect_r; eassumption. Defined.
Definition eq_rect_r@{s|u u'|} {A : Type@{s|u}} {x : A} (P : A -> Type@{u'}) (H : P x) {y : A} (H0 : y = x) : P y.
Proof. eapply eq_srect_r; eassumption. Defined.

Definition eq_srect_nodep@{α β| u v|} (α : Type@{α | u}) (a : α) (P : α -> Type@{β|v}) (f : P a) (α0 : α) (e : a = α0) :=
match e with
| eq_refl => f
end.

Module EqNotations.

  Notation "'rew' H 'in' H'" := (eq_srect_nodep _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_srect_nodep P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (rew (eq_sym H) in H')
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (rew [P] H in H')
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_srect_nodep _ H' H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_srect_nodep P H' H)
    (at level 10, H' at level 10, only parsing).

  Notation "'rew' 'dependent' H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, only parsing).
  Notation "'rew' 'dependent' <- H 'in' H'"
    := (match eq_sym H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name, only parsing).
  Notation "'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  <-  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          only parsing).
  Notation "'rew' 'dependent' <- [ P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
End EqNotations.

Import EqNotations.

Theorem f_equal_dep@{s s'|u u'|} {A : Type@{s|u}} {B : A -> Type@{s'|u'}} (f : forall x, B x) {x y : A} (H: x = y) : rew H in f x = f y.
Proof. destruct H; reflexivity. Defined.

(* Use vm_compute to work around https://github.com/coq/coq/issues/20113 *)
Lemma f_equal_dep2@{s0 s1 s2 s3|u0 u1 u2 u3|} {A : Type@{s0|u0}} {A' : Type@{s1|u1}} {B : A -> Type@{s2|u2}} {B' : A' -> Type@{s3|u3}} (f : A -> A') (g : forall a:A, B a -> B' (f a))
  {x1 x2 : A} {y1 : B x1} {y2 : B x2} (H : x1 = x2) :
  rew H in y1 = y2 -> rew f_equal f H in g x1 y1 = g x2 y2.
Proof. destruct H, 1; vm_compute; reflexivity. Defined.

Lemma rew_opp_r@{s0 s1|u0 u1|} (A : Type@{s0|u0}) (P : A -> Type@{s1|u1}) (x y : A) (H : x = y) (a : P y) : rew H in rew <- H in a = a.
Proof. destruct H; vm_compute; reflexivity. Defined.

Lemma rew_opp_l@{s0 s1|u0 u1|} (A : Type@{s0|u0}) (P : A -> Type@{s1|u1}) (x y : A) (H : x = y) (a : P x) : rew <- H in rew H in a = a.
Proof. destruct H; vm_compute; reflexivity. Defined.

Theorem f_equal2@{s0 s1 s2|u0 u1 u2|} :
  forall (A1 : Type@{s0|u0}) (A2 : Type@{s1|u1}) (B : Type@{s2|u2}) (f : A1 -> A2 -> B) (x1 y1 : A1)
    (x2 y2 : A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof. destruct 1; destruct 1; reflexivity. Defined.

Theorem f_equal3@{s0 s1 s2 s3|u0 u1 u2 u3|} :
  forall (A1 : Type@{s0|u0}) (A2 : Type@{s1|u1}) (A3 : Type@{s2|u2}) (B : Type@{s3|u3}) (f : A1 -> A2 -> A3 -> B) (x1 y1 : A1)
    (x2 y2 : A2) (x3 y3 : A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof. destruct 1; destruct 1; destruct 1; reflexivity. Defined.

Theorem f_equal4@{s0 s1 s2 s3 s4|u0 u1 u2 u3 u4|} :
  forall (A1 : Type@{s0|u0}) (A2 : Type@{s1|u1}) (A3 : Type@{s2|u2}) (A4 : Type@{s3|u3}) (B : Type@{s4|u4}) (f : A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1 : A1) (x2 y2 : A2) (x3 y3 : A3) (x4 y4 : A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof. destruct 1; destruct 1; destruct 1; destruct 1; reflexivity. Defined.

Theorem f_equal5@{s0 s1 s2 s3 s4 s5|u0 u1 u2 u3 u4 u5|} :
  forall (A1 : Type@{s0|u0}) (A2 : Type@{s1|u1}) (A3 : Type@{s2|u2}) (A4 : Type@{s3|u3}) (A5 : Type@{s4|u4}) (B : Type@{s5|u5}) (f : A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1 : A1) (x2 y2 : A2) (x3 y3 : A3) (x4 y4 : A4) (x5 y5 : A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof. destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity. Defined.

Theorem rew_map@{s0 s1 s2|u0 u1 u2|} (A : Type@{s0|u0}) (B : Type@{s1|u1}) (P : B -> Type@{s2|u2}) (f : A -> B) x1 x2 (H : x1 = x2) (y : P (f x1)) :
  rew [fun x => P (f x)] H in y = rew f_equal f H in y.
Proof. destruct H; vm_compute; reflexivity. Defined.

Theorem eq_trans_map@{s0 s1|u0 u1|} {A : Type@{s0|u0}} {B : A -> Type@{s1|u1}} {x1 x2 x3 : A} {y1 : B x1} {y2 : B x2} {y3 : B x3}
  (H1 : x1 = x2) (H2 : x2 = x3) (H1' : rew H1 in y1 = y2) (H2' : rew H2 in y2 = y3) :
  rew eq_trans H1 H2 in y1 = y3.
Proof. destruct H2. exact (eq_trans H1' H2'). Defined.

Lemma map_subst@{s0 s1 s2|u0 u1 u2|} {A : Type@{s0|u0}} {P Q : A -> Type@{s1|u1}} (f : forall x, P x -> Q x) {x y} (H : x = y) (z : P x) :
  rew H in f x z = f y (rew H in z).
Proof. destruct H. reflexivity. Defined.

Lemma map_subst_map@{s0 s1 s2 s3|u0 u1 u2 u3|} {A : Type@{s0|u0}} {B : Type@{s1|u1}} {P : A -> Type@{s2|u2}} {Q : B -> Type@{s3|u3}} (f : A -> B) (g : forall x, P x -> Q (f x))
  {x y} (H : x = y) (z : P x) :
  rew f_equal f H in g x z = g y (rew H in z).
Proof. destruct H. vm_compute. reflexivity. Defined.

Lemma rew_swap@{s0 s1 s2|u0 u1 u2|} (A : Type@{s0|u0}) (P : A -> Type@{s1|u1}) x1 x2 (H : x1 = x2) (y1 : P x1) (y2 : P x2) : rew H in y1 = y2 -> y1 = rew <- H in y2.
Proof. destruct H. vm_compute. trivial. Defined.

Lemma rew_compose@{s0 s1|u0 u1|} (A : Type@{s0|u0}) (P : A -> Type@{s1|u1}) x1 x2 x3 (H1 : x1 = x2) (H2 : x2 = x3) (y : P x1) :
  rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.
Proof. destruct H2, H1. vm_compute. reflexivity. Defined.

Lemma eq_trans_rew_distr@{s0 s1|u0 u1|} (A : Type@{s0|u0}) (P : A -> Type@{s1|u1}) (x y z : A) (e : x = y) (e' : y = z) (k : P x) :
    rew (eq_trans e e') in k = rew e' in rew e in k.
Proof. destruct e, e'; reflexivity. Defined.

Lemma rew_const@{s0 s1|u0 u1|} (A : Type@{s0|u0}) (P : Type@{s1|u1}) (x y : A) (e : x = y) (k : P) :
    rew [fun _ => P] e in k = k.
Proof. destruct e; reflexivity. Defined.

Lemma seq_of_eq@{u} {A : Type@{u}} {x y : A} (H : Logic.eq x y) : IsomorphismDefinitions.eq x y.
Proof. destruct H; reflexivity. Defined.
Lemma eq_of_seq@{u} {A : Type@{u}} {x y : A} (H : IsomorphismDefinitions.eq x y) : Logic.eq x y.
Proof. destruct H; reflexivity. Defined.
Lemma seq_of_peq@{u} {A : Prop} {x y : A} (H : Logic.eq x y) : IsomorphismDefinitions.eq@{Prop|u} x y.
Proof. destruct H; reflexivity. Defined.
Lemma peq_of_seq@{u} {A : Prop} {x y : A} (H : IsomorphismDefinitions.eq@{Prop|u} x y) : Logic.eq x y.
Proof. destruct H; reflexivity. Defined.
Lemma seq_of_peq_t@{u} {A : Prop} {x y : A} (H : Logic.eq x y) : IsomorphismDefinitions.eq@{Type|u} x y.
Proof. destruct H; reflexivity. Defined.
Lemma peq_of_seq_t@{u} {A : Prop} {x y : A} (H : IsomorphismDefinitions.eq@{Type|u} x y) : Logic.eq x y.
Proof. destruct H; reflexivity. Defined.
Axiom functional_extensionality_dep@{s s'|u u' u''|u<=u'',u'<=u''}
  : forall {A : Type@{s|u}} {B : A -> Type@{s'|u'}} (f g : forall x : A, B x), (forall x : A, f x = g x) -> eq@{s'|u''} f g.
(* Lemma functional_extensionality_dep@{|u u' u''|u<=u'',u'<=u'',u <= functional_extensionality_dep.u0,u' <= functional_extensionality_dep.u1}
  {A : Type@{u}} {B : A -> Type@{u'}} (f g : forall x : A, B x) : (forall x : A, f x = g x) -> eq@{Type|u''} f g.
Proof. intro H; apply seq_of_eq, functional_extensionality_dep; intro; apply eq_of_seq, H. Defined. *)
Lemma functional_extensionality@{s s'|u u' u''|u<=u'',u'<=u''}
  {A : Type@{s|u}} {B : Type@{s'|u'}} (f g : A -> B) : (forall x : A, f x = g x) -> eq@{s'|u''} f g.
Proof. apply functional_extensionality_dep. Defined.

Lemma seq_t_of_p@{u} {A : Prop} {x y : A} (H : IsomorphismDefinitions.eq@{Prop|u} x y) : IsomorphismDefinitions.eq@{Type|u} x y.
Proof. destruct H; reflexivity. Defined.
Lemma seq_p_of_t@{u} {A : Prop} {x y : A} (H : IsomorphismDefinitions.eq@{Type|u} x y) : IsomorphismDefinitions.eq@{Prop|u} x y.
Proof. destruct H; reflexivity. Defined.

Lemma seq_Type_of_Prop@{v ov p} {x y : Prop} (H : @IsomorphismDefinitions.eq@{Type|p} Prop x y) : @IsomorphismDefinitions.eq@{Type|ov} Type@{v} x y.
Proof. destruct H; reflexivity. Defined.
(* Lemma seq_Prop_of_Type@{v ov p} {x y : Prop} (H : @IsomorphismDefinitions.eq@{Type|ov} Type@{v} x y) : @IsomorphismDefinitions.eq@{Type|p} Prop x y.
Proof. destruct H; reflexivity. Defined. *)
End IsoEq.

Definition from_to_tteq@{u u'} {A B} (i : Iso@{Type Type|u u'} A B) x : Logic.eq (i.(from) (i.(to) x)) x.
Proof. apply eq_of_seq, i.(from_to). Defined.
Definition from_to_tpeq@{u u'} {A B} (i : Iso@{Type Prop|u u'} A B) x : Logic.eq (i.(from) (i.(to) x)) x.
Proof. apply eq_of_seq, i.(from_to). Defined.
Definition from_to_pteq@{u u'} {A B} (i : Iso@{Prop Type|u u'} A B) x : Logic.eq (i.(from) (i.(to) x)) x.
Proof. apply eq_of_seq. generalize (i.(from_to) x). generalize (i.(from) (i.(to) x)); intros ? []; reflexivity. Defined.
Definition from_to_ppeq@{u u'} {A B} (i : Iso@{Prop Prop|u u'} A B) x : Logic.eq (i.(from) (i.(to) x)) x.
Proof. apply eq_of_seq. generalize (i.(from_to) x). generalize (i.(from) (i.(to) x)); intros ? []; reflexivity. Defined.
Definition from_to_tseq@{u u'} {A B} (i : Iso@{Type SProp|u u'} A B) x : Logic.eq (i.(from) (i.(to) x)) x.
Proof. apply eq_of_seq, i.(from_to). Defined.
Definition from_to_pseq@{u u'} {A B} (i : Iso@{Prop SProp|u u'} A B) x : Logic.eq (i.(from) (i.(to) x)) x.
Proof. apply eq_of_seq. generalize (i.(from_to) x). generalize (i.(from) (i.(to) x)); intros ? []; reflexivity. Defined.

Definition to_from_tteq@{u u'} {A B} (i : Iso@{Type Type|u u'} A B) x : Logic.eq (i.(to) (i.(from) x)) x.
Proof. apply eq_of_seq, i.(to_from). Defined.
Definition to_from_tpeq@{u u'} {A B} (i : Iso@{Type Prop|u u'} A B) x : Logic.eq (i.(to) (i.(from) x)) x.
Proof. apply eq_of_seq. generalize (i.(to_from) x). generalize (i.(to) (i.(from) x)); intros ? []; reflexivity. Defined.
Definition to_from_pteq@{u u'} {A B} (i : Iso@{Prop Type|u u'} A B) x : Logic.eq (i.(to) (i.(from) x)) x.
Proof. apply eq_of_seq, i.(to_from). Defined.
Definition to_from_ppeq@{u u'} {A B} (i : Iso@{Prop Prop|u u'} A B) x : Logic.eq (i.(to) (i.(from) x)) x.
Proof. apply eq_of_seq. generalize (i.(to_from) x). generalize (i.(to) (i.(from) x)); intros ? []; reflexivity. Defined.
Definition to_from_steq@{u u'} {A B} (i : Iso@{SProp Type|u u'} A B) x : Logic.eq (i.(to) (i.(from) x)) x.
Proof. apply eq_of_seq, i.(to_from). Defined.
Definition to_from_speq@{u u'} {A B} (i : Iso@{SProp Prop|u u'} A B) x : Logic.eq (i.(to) (i.(from) x)) x.
Proof. apply eq_of_seq. generalize (i.(to_from) x). generalize (i.(to) (i.(from) x)); intros ? []; reflexivity. Defined.

Definition from_to_ttleq@{u u'} {A B} (i : Iso@{Type Type|u u'} A B) x : Lean.eq (i.(from) (i.(to) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq, i.(from_to). Defined.
Definition from_to_tpleq@{u u'} {A B} (i : Iso@{Type Prop|u u'} A B) x : Lean.eq (i.(from) (i.(to) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq, i.(from_to). Defined.
Definition from_to_ptleq@{u u'} {A B} (i : Iso@{Prop Type|u u'} A B) x : Lean.eq (i.(from) (i.(to) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq. generalize (i.(from_to) x). generalize (i.(from) (i.(to) x)); intros ? []; reflexivity. Defined.
Definition from_to_ppleq@{u u'} {A B} (i : Iso@{Prop Prop|u u'} A B) x : Lean.eq (i.(from) (i.(to) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq. generalize (i.(from_to) x). generalize (i.(from) (i.(to) x)); intros ? []; reflexivity. Defined.
Definition from_to_tsleq@{u u'} {A B} (i : Iso@{Type SProp|u u'} A B) x : Lean.eq (i.(from) (i.(to) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq, i.(from_to). Defined.
Definition from_to_psleq@{u u'} {A B} (i : Iso@{Prop SProp|u u'} A B) x : Lean.eq (i.(from) (i.(to) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq. generalize (i.(from_to) x). generalize (i.(from) (i.(to) x)); intros ? []; reflexivity. Defined.

Definition to_from_ttleq@{u u'} {A B} (i : Iso@{Type Type|u u'} A B) x : Lean.eq (i.(to) (i.(from) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq, i.(to_from). Defined.
Definition to_from_tpleq@{u u'} {A B} (i : Iso@{Type Prop|u u'} A B) x : Lean.eq (i.(to) (i.(from) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq. generalize (i.(to_from) x). generalize (i.(to) (i.(from) x)); intros ? []; reflexivity. Defined.
Definition to_from_ptleq@{u u'} {A B} (i : Iso@{Prop Type|u u'} A B) x : Lean.eq (i.(to) (i.(from) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq, i.(to_from). Defined.
Definition to_from_ppleq@{u u'} {A B} (i : Iso@{Prop Prop|u u'} A B) x : Lean.eq (i.(to) (i.(from) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq. generalize (i.(to_from) x). generalize (i.(to) (i.(from) x)); intros ? []; reflexivity. Defined.
Definition to_from_stleq@{u u'} {A B} (i : Iso@{SProp Type|u u'} A B) x : Lean.eq (i.(to) (i.(from) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq, i.(to_from). Defined.
Definition to_from_spleq@{u u'} {A B} (i : Iso@{SProp Prop|u u'} A B) x : Lean.eq (i.(to) (i.(from) x)) x.
Proof. apply LeanEq.seq_of_eq, eq_of_seq. generalize (i.(to_from) x). generalize (i.(to) (i.(from) x)); intros ? []; reflexivity. Defined.

Lemma iso_move_r_seq@{s s'|u u'|} A A' (isoA : Iso@{s s'|u u'} A A') x y : IsomorphismDefinitions.eq (isoA.(to) x) y -> IsomorphismDefinitions.eq x (isoA.(from) y).
Proof. intros []; apply eq_sym; refine (isoA.(from_to) x). Defined.
Lemma iso_move_r_tteq@{u u'} A A' (isoA : Iso@{Type Type|u u'} A A') x y : Logic.eq (isoA.(to) x) y -> Logic.eq x (isoA.(from) y).
Proof. intros; apply eq_of_seq, iso_move_r_seq, seq_of_eq; exact H. Defined.
Lemma iso_move_r_tpeq@{u u'} A A' (isoA : Iso@{Type Prop|u u'} A A') x y : Logic.eq (isoA.(to) x) y -> Logic.eq x (isoA.(from) y).
Proof. intros; apply eq_of_seq, iso_move_r_seq, seq_of_peq; exact H. Defined.
Lemma iso_move_r_pteq@{u u'} A A' (isoA : Iso@{Prop Type|u u'} A A') x y : Logic.eq (isoA.(to) x) y -> Logic.eq x (isoA.(from) y).
Proof. intros; apply peq_of_seq, iso_move_r_seq, seq_of_eq; exact H. Defined.
Lemma iso_move_r_ppeq@{u u'} A A' (isoA : Iso@{Prop Prop|u u'} A A') x y : Logic.eq (isoA.(to) x) y -> Logic.eq x (isoA.(from) y).
Proof. intros; apply peq_of_seq, iso_move_r_seq, seq_of_peq; exact H. Defined.
Lemma iso_move_r_ttleq@{u u'} A A' (isoA : Iso@{Type Type|u u'} A A') x y : Lean.eq (isoA.(to) x) y -> Lean.eq x (isoA.(from) y).
Proof. intros; apply LeanEq.seq_of_eq, eq_of_seq, iso_move_r_seq, seq_of_eq, LeanEq.eq_of_seq; exact H. Defined.
Lemma iso_move_r_tpleq@{u u'} A A' (isoA : Iso@{Type Prop|u u'} A A') x y : Lean.eq (isoA.(to) x) y -> Lean.eq x (isoA.(from) y).
Proof. intros; apply LeanEq.seq_of_eq, eq_of_seq, iso_move_r_seq, seq_of_peq, LeanEq.eq_of_seq; exact H. Defined.
Lemma iso_move_r_ptleq@{u u'} A A' (isoA : Iso@{Prop Type|u u'} A A') x y : Lean.eq (isoA.(to) x) y -> Lean.eq x (isoA.(from) y).
Proof. intros; apply LeanEq.seq_of_eq, peq_of_seq, iso_move_r_seq, seq_of_eq, LeanEq.eq_of_seq; exact H. Defined.
Lemma iso_move_r_ppleq@{u u'} A A' (isoA : Iso@{Prop Prop|u u'} A A') x y : Lean.eq (isoA.(to) x) y -> Lean.eq x (isoA.(from) y).
Proof. intros; apply LeanEq.seq_of_eq, peq_of_seq, iso_move_r_seq, seq_of_peq, LeanEq.eq_of_seq; exact H. Defined.

Lemma iso_move_r'_seq@{s s'|u u'|} A A' (isoA : Iso@{s s'|u u'} A A') x y : IsomorphismDefinitions.eq x (isoA.(from) y) -> IsomorphismDefinitions.eq (isoA.(to) x) y.
Proof. intro H; apply eq_sym in H; destruct H; apply to_from. Defined.
Lemma iso_move_r'_seq_tp@{s|u u'|} A A' (isoA : Iso@{s Prop|u u'} A A') x y : IsomorphismDefinitions.eq x (isoA.(from) y) -> IsomorphismDefinitions.eq@{Type|u'} (isoA.(to) x) y.
Proof. intro H; apply eq_sym in H; destruct H. generalize (isoA.(to) (isoA.(from) y)), (isoA.(to_from) y); intros ? []; reflexivity. Defined.
Lemma iso_move_r'_seq_pt@{s|u u'|} A A' (isoA : Iso@{Prop s|u u'} A A') x y : IsomorphismDefinitions.eq@{Type|u} x (isoA.(from) y) -> IsomorphismDefinitions.eq (isoA.(to) x) y.
Proof. intro H; apply eq_sym in H; destruct H. generalize (isoA.(to) (isoA.(from) y)), (isoA.(to_from) y); intros ? []; reflexivity. Defined.
Lemma iso_move_r'_seq_pp@{|u u'|} A A' (isoA : Iso@{Prop Prop|u u'} A A') x y : IsomorphismDefinitions.eq@{Type|u} x (isoA.(from) y) -> IsomorphismDefinitions.eq@{Type|u'} (isoA.(to) x) y.
Proof. intro H; apply eq_sym in H; destruct H. generalize (isoA.(to) (isoA.(from) y)), (isoA.(to_from) y); intros ? []; reflexivity. Defined.
Lemma iso_move_r'_tteq@{u u'} A A' (isoA : Iso@{Type Type|u u'} A A') x y : Logic.eq x (isoA.(from) y) -> Logic.eq (isoA.(to) x) y.
Proof. intros; apply eq_of_seq, iso_move_r'_seq, seq_of_eq; exact H. Defined.
Lemma iso_move_r'_tpeq@{u u'} A A' (isoA : Iso@{Type Prop|u u'} A A') x y : Logic.eq x (isoA.(from) y) -> Logic.eq (isoA.(to) x) y.
Proof. intros; eapply eq_of_seq, iso_move_r'_seq_tp, seq_of_eq; exact H. Defined.
Lemma iso_move_r'_pteq@{u u'} A A' (isoA : Iso@{Prop Type|u u'} A A') x y : Logic.eq x (isoA.(from) y) -> Logic.eq (isoA.(to) x) y.
Proof. intros; apply eq_of_seq, iso_move_r'_seq, seq_of_peq; exact H. Defined.
Lemma iso_move_r'_ppeq@{u u'} A A' (isoA : Iso@{Prop Prop|u u'} A A') x y : Logic.eq x (isoA.(from) y) -> Logic.eq (isoA.(to) x) y.
Proof. intros; apply peq_of_seq, iso_move_r'_seq, seq_of_peq; exact H. Defined.
Lemma iso_move_r'_ttleq@{u u'} A A' (isoA : Iso@{Type Type|u u'} A A') x y : Lean.eq x (isoA.(from) y) -> Lean.eq (isoA.(to) x) y.
Proof. intros; apply LeanEq.seq_of_eq, eq_of_seq, iso_move_r'_seq, seq_of_eq, LeanEq.eq_of_seq; exact H. Defined.
Lemma iso_move_r'_tpleq@{u u'} A A' (isoA : Iso@{Type Prop|u u'} A A') x y : Lean.eq x (isoA.(from) y) -> Lean.eq (isoA.(to) x) y.
Proof. intros; apply LeanEq.seq_of_eq, eq_of_seq, iso_move_r'_seq_tp, seq_of_eq, LeanEq.eq_of_seq; exact H. Defined.
Lemma iso_move_r'_ptleq@{u u'} A A' (isoA : Iso@{Prop Type|u u'} A A') x y : Lean.eq x (isoA.(from) y) -> Lean.eq (isoA.(to) x) y.
Proof. intros; apply LeanEq.seq_of_eq, eq_of_seq, iso_move_r'_seq, seq_of_peq, LeanEq.eq_of_seq; exact H. Defined.
Lemma iso_move_r'_ppleq@{u u'} A A' (isoA : Iso@{Prop Prop|u u'} A A') x y : Lean.eq x (isoA.(from) y) -> Lean.eq (isoA.(to) x) y.
Proof. intros; apply LeanEq.seq_of_eq, peq_of_seq, iso_move_r'_seq, seq_of_peq, LeanEq.eq_of_seq; exact H. Defined.

(* Kludge for dealing with things like [list Type] *)
Notation unfolded_iso_Sort :=
  {| to x := x
  ; from x := x
  ; to_from x := IsomorphismDefinitions.eq_refl
  ; from_to x := IsomorphismDefinitions.eq_refl
  |} (only parsing).
Definition iso_Sort@{s|u v v'|u < v, u < v'} : Iso@{Type Type|v v'} Type@{s|u} Type@{s|u} := unfolded_iso_Sort.
#[global] Arguments iso_Sort / .

Definition iso_refl@{s|u|} {A} : Iso@{s s|u u} A A
  := {| to x := x; from x := x;
        from_to x := eq_refl; to_from x := eq_refl |}.
Arguments iso_refl {A}, A.

Definition iso_SInhabited@{u u'|} {A : Prop} : Iso@{Prop SProp|u u'} A (SInhabited A)
  := @Build_Iso@{Prop SProp|u u'} A (SInhabited A) sinhabits sinhabitant
       (fun x => eq_refl)
       (fun x => IsoEq.seq_of_peq@{u} (proof_irrelevance A _ x)).

Notation unfolded_iso_Prop_SProp :=
  (@Build_Iso Prop SProp SInhabited inhabited
      (fun x => seq_of_eq (eq_SInhabited_inhabited x))
      (fun x => seq_of_eq (SInhabited_Prop_injective (eq_SInhabited_inhabited (SInhabited x))))) (only parsing).
Definition iso_Prop_SProp@{u u'} : Iso@{Type Type|u u'} Prop SProp := unfolded_iso_Prop_SProp.
#[global] Arguments iso_Prop_SProp / .

Definition rel_iso_refl@{s s'|u u'|} {A B i} : forall x, @rel_iso@{s s'|u u'} A B i x (i.(to) x) := fun x => eq_refl.
Arguments rel_iso_refl {A B i x}, {A B i} x, {A B} i x, A B i x.

Coercion IsoOrSortAndRelIsoIso : Iso >-> IsoOrSortAndRelIso.

Module PolymorphicSpecif.
  #[local] Set Primitive Projections.
  Polymorphic Cumulative Record sigT@{ua ub} {A : Type@{ua}} {B : A -> Type@{ub}} := existT { projT1 : A; projT2 : B projT1 }.
  #[global] Arguments existT {A} B projT1 projT2.
  #[global] Arguments sigT {A} B.
  #[global] Arguments projT1 {A B} _.
  #[global] Arguments projT2 {A B} _.
  Polymorphic Cumulative Variant option@{ua} {A : Type@{ua}} := Some (x : A) | None.
  #[global] Arguments Some {A} x.
  #[global] Arguments None {A}.
  #[global] Arguments option A : clear implicits.
End PolymorphicSpecif.

Definition wrap_sprop_eta {A} {x : WrapSProp A} : eq (wrap_sprop (unwrap_sprop x)) x.
Proof. destruct x; reflexivity. Defined.

Definition Iso_TS_WrapSProp@{s|u v|} {A : Type@{s|u}} {B : SProp} (i : Iso@{s SProp|u v} A B) : Iso@{s Type|u v} A (WrapSProp B)
  := @Build_Iso@{s Type|u v} A (WrapSProp B) (fun x => wrap_sprop (i.(to) x)) (fun x => i.(from) (unwrap_sprop x)) (fun x => eq_trans (f_equal wrap_sprop (i.(to_from) (unwrap_sprop x))) wrap_sprop_eta) (fun x => i.(from_to) x).
Definition Iso_ST_WrapSProp@{s|u v|} {A : SProp} {B : Type@{s|v}} (i : Iso@{SProp s|u v} A B) : Iso@{Type s|u v} (WrapSProp A) B
  := @Build_Iso@{Type s|u v} (WrapSProp A) B (fun x => i.(to) (unwrap_sprop x)) (fun x => wrap_sprop (i.(from) x)) (fun x => i.(to_from) x) (fun x => eq_trans (f_equal wrap_sprop (i.(from_to) (unwrap_sprop x))) wrap_sprop_eta).
Definition Iso_SS_WrapSProp@{u v} {A B : SProp} (i : Iso@{SProp SProp|u v} A B) : Iso@{Type Type|u v} (WrapSProp A) (WrapSProp B)
  := @Build_Iso@{Type Type|u v} (WrapSProp A) (WrapSProp B) (fun x => wrap_sprop (i.(to) (unwrap_sprop x))) (fun x => wrap_sprop (i.(from) (unwrap_sprop x))) (fun x => eq_trans (f_equal wrap_sprop (i.(to_from) (unwrap_sprop x))) wrap_sprop_eta) (fun x => eq_trans (f_equal wrap_sprop (i.(from_to) (unwrap_sprop x))) wrap_sprop_eta).

Definition IsoIso_S@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} (i : Iso@{Type SProp|a b} A B)
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoIso@{a b u v r} allow_relaxed _ _ (Iso_TS_WrapSProp i)).
Definition IsoIsoS_@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} (i : Iso@{SProp Type|a b} A B)
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoIso@{a b u v r} allow_relaxed _ _ (Iso_ST_WrapSProp i)).
Definition IsoIsoSS@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} (i : Iso@{SProp SProp|a b} A B)
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoIso@{a b u v r} allow_relaxed _ _ (Iso_SS_WrapSProp i)).


Definition IsoForall@{s0 s1 s2 s3|u0 u1 u2 u3 u4 u5|u0 <= u4,u1 <= u5,u2 <= u4,u3 <= u5}
  {A A'} (isoA : Iso@{s0 s1|u0 u1} A A') (B : A -> Type@{s2|u2}) (B' : A' -> Type@{s3|u3})
  : (forall a a' (He : rel_iso isoA a a'), Iso (B a) (B' a'))
    -> Iso@{s2 s3|u4 u5} (forall a, B a) (forall a', B' a').
Proof.
  intro H; unshelve esplit; [ intros f a .. | intro x; shelve | intro x; shelve ].
  all: first [ specialize (H a) | specialize (fun a' => H a' a) ].
  all: first [ specialize (H (isoA.(to) a)) | specialize (H (isoA.(from) a)) ].
  all: first [ specialize (H eq_refl) | specialize (H (isoA.(to_from) a)) ].
  all: [ > first [ apply H.(to) | apply H.(from) ]; auto .. ].
  Unshelve.
  all: cbn.
  all: apply functional_extensionality_dep; intro.
  { destruct to_from.
    apply to_from. }
  { generalize (to_from isoA (isoA.(to) x0)).
    intro e.
    assert (e' : eq (isoA.(from) (isoA.(to) x0)) x0) by apply from_to.
    assert (ee : eq@{SProp|Set} (f_equal (isoA.(to)) e') e) by reflexivity.
    destruct ee.
    generalize dependent (isoA.(from) (isoA.(to) x0)).
    intros a []; cbn.
    apply from_to. }
Defined.

Fixpoint Iso_of_IsoOrSortAndRelIso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} false A B R) : Iso@{Type Type|u u} A B :=
  match i in @IsoOrSortAndRelIso allow_relaxed A B R return if allow_relaxed then IDProp else Iso@{Type Type|u u} A B with
  | IsoOrSortAndRelIsoIso false i => i
  | IsoOrSortAndRelIsoIsoTypeSProp false i => Iso_TS_WrapSProp i
  | IsoOrSortAndRelIsoIsoSPropType false i => Iso_ST_WrapSProp i
  | IsoOrSortAndRelIsoIsoSPropSProp false i => Iso_SS_WrapSProp i
  | IsoOrSortAndRelIsoPropProp false => iso_refl
  | IsoOrSortAndRelIsoSPropSProp false => iso_refl
  | IsoOrSortAndRelIsoTypeType false => iso_refl
  | IsoOrSortAndRelIsoForall false isoA isoB =>
      IsoForall _ _ (fun a a' r => @Iso_of_IsoOrSortAndRelIso _ _ _ (isoB _ _ r))
  end.

Definition relax_Iso_PP_TT@{u v u' v'|} {A B} (iso : Iso@{Prop Prop|u v} A B) : Iso@{Type Type|u' v'} A B
  := @Build_Iso@{Type Type|u' v'} A B iso.(to@{Prop Prop|u v}) iso.(from@{Prop Prop|u v}) (fun x => seq_t_of_p@{u'} (iso.(to_from@{Prop Prop|u v}) x)) (fun x => seq_t_of_p@{v'} (iso.(from_to@{Prop Prop|u v}) x)).
Definition relax_Iso_PP_TP@{u v u' v'|} {A B} (iso : Iso@{Prop Prop|u v} A B) : Iso@{Type Prop|u' v'} A B
  := @Build_Iso@{Type Prop|u' v'} A B iso.(to@{Prop Prop|u v}) iso.(from@{Prop Prop|u v}) (fun x => iso.(to_from@{Prop Prop|u v}) x) (fun x => seq_t_of_p@{v'} (iso.(from_to@{Prop Prop|u v}) x)).
Definition relax_Iso_PP_PT@{u v u' v'|} {A B} (iso : Iso@{Prop Prop|u v} A B) : Iso@{Prop Type|u' v'} A B
  := @Build_Iso@{Prop Type|u' v'} A B iso.(to@{Prop Prop|u v}) iso.(from@{Prop Prop|u v}) (fun x => seq_t_of_p@{u'} (iso.(to_from@{Prop Prop|u v}) x)) (fun x => iso.(from_to@{Prop Prop|u v}) x).
Definition relax_Iso_PT_TT@{b u v u' v'|b<=v,b<=v'} {A : Prop} {B : Type@{b}} (iso : Iso@{Prop Type|u v} A B) : Iso@{Type Type|u' v'} A B
  := @Build_Iso@{Type Type|u' v'} A B iso.(to@{Prop Type|u v}) iso.(from@{Prop Type|u v}) (fun x => iso.(to_from@{Prop Type|u v}) x) (fun x => seq_t_of_p@{v'} (iso.(from_to@{Prop Type|u v}) x)).
Definition relax_Iso_PP_PT_TT@{u v u' v'|} {A B : Prop} (iso : Iso@{Prop Type|u v} A B) : Iso@{Type Type|u' v'} A B
  := @relax_Iso_PT_TT@{_ u v u' v'} _ _ iso.
Definition relax_Iso_PT_PT@{b u v u' v'|b<=v,b<=v'} {A : Prop} {B : Type@{b}} (iso : Iso@{Prop Type|u v} A B) : Iso@{Prop Type|u' v'} A B
  := @Build_Iso@{Prop Type|u' v'} A B iso.(to@{Prop Type|u v}) iso.(from@{Prop Type|u v}) (fun x => iso.(to_from@{Prop Type|u v}) x) (fun x => iso.(from_to@{Prop Type|u v}) x).
Definition relax_Iso_PP_PT_PT@{u v u' v'|} {A B : Prop} (iso : Iso@{Prop Type|u v} A B) : Iso@{Prop Type|u' v'} A B
  := @relax_Iso_PT_PT@{_ u v u' v'} _ _ iso.
Definition relax_Iso_PT_TP@{u v u' v'|} {A B : Prop} (iso : Iso@{Prop Type|u v} A B) : Iso@{Type Prop|u' v'} A B
  := @Build_Iso@{Type Prop|u' v'} A B iso.(to@{Prop Type|u v}) iso.(from@{Prop Type|u v}) (fun x => seq_p_of_t@{u} (iso.(to_from@{Prop Type|u v}) x)) (fun x => seq_t_of_p@{v'} (iso.(from_to@{Prop Type|u v}) x)).
Definition relax_Iso_PT_PP@{u v u' v'|} {A B : Prop} (iso : Iso@{Prop Type|u v} A B) : Iso@{Prop Prop|u' v'} A B
  := @Build_Iso@{Prop Prop|u' v'} A B iso.(to@{Prop Type|u v}) iso.(from@{Prop Type|u v}) (fun x => seq_p_of_t@{u} (iso.(to_from@{Prop Type|u v}) x)) (fun x => iso.(from_to@{Prop Type|u v}) x).
Definition relax_Iso_TP_PT@{u v u' v'|} {A B : Prop} (iso : Iso@{Type Prop|u v} A B) : Iso@{Prop Type|u' v'} A B
  := @Build_Iso@{Prop Type|u' v'} A B iso.(to@{Type Prop|u v}) iso.(from@{Type Prop|u v}) (fun x => seq_t_of_p@{u} (iso.(to_from@{Type Prop|u v}) x)) (fun x => seq_p_of_t@{v'} (iso.(from_to@{Type Prop|u v}) x)).
Definition relax_Iso_TP_TT@{a u v u' v'|a<=u,a<=u'} {A : Type@{a}} {B : Prop} (iso : Iso@{Type Prop|u v} A B) : Iso@{Type Type|u' v'} A B
  := @Build_Iso@{Type Type|u' v'} A B iso.(to@{Type Prop|u v}) iso.(from@{Type Prop|u v}) (fun x => seq_t_of_p@{u} (iso.(to_from@{Type Prop|u v}) x)) (fun x => iso.(from_to@{Type Prop|u v}) x).
Definition relax_Iso_PP_TP_TT@{u v u' v'|} {A B : Prop} (iso : Iso@{Type Prop|u v} A B) : Iso@{Type Type|u' v'} A B
  := @relax_Iso_TP_TT@{_ u v u' v'} _ _ iso.
Definition relax_Iso_TP_TP@{a u v u' v'|a<=u,a<=u'} {A : Type@{a}} {B : Prop} (iso : Iso@{Type Prop|u v} A B) : Iso@{Type Prop|u' v'} A B
  := @Build_Iso@{Type Prop|u' v'} A B iso.(to@{Type Prop|u v}) iso.(from@{Type Prop|u v}) (fun x => iso.(to_from@{Type Prop|u v}) x) (fun x => iso.(from_to@{Type Prop|u v}) x).
Definition relax_Iso_PP_TP_TP@{u v u' v'|} {A B : Prop} (iso : Iso@{Type Prop|u v} A B) : Iso@{Type Prop|u' v'} A B
  := @relax_Iso_TP_TP@{_ u v u' v'} _ _ iso.
Definition relax_Iso_TP_PP@{u v u' v'|} {A B : Prop} (iso : Iso@{Type Prop|u v} A B) : Iso@{Prop Prop|u' v'} A B
  := @Build_Iso@{Prop Prop|u' v'} A B iso.(to@{Type Prop|u v}) iso.(from@{Type Prop|u v}) (fun x => iso.(to_from@{Type Prop|u v}) x) (fun x => seq_p_of_t@{v'} (iso.(from_to@{Type Prop|u v}) x)).
Definition relax_Iso_TT_PT@{b u v u' v'|b<=v,b<=v'} {A : Prop} {B : Type@{b}} (iso : Iso@{Type Type|u v} A B) : Iso@{Prop Type|u' v'} A B
  := @Build_Iso@{Prop Type|u' v'} A B iso.(to@{Type Type|u v}) iso.(from@{Type Type|u v}) (fun x => iso.(to_from@{Type Type|u v}) x) (fun x => seq_p_of_t@{v'} (iso.(from_to@{Type Type|u v}) x)).
Definition relax_Iso_PP_TT_PT@{u v u' v'|} {A B : Prop} (iso : Iso@{Type Type|u v} A B) : Iso@{Prop Type|u' v'} A B
  := @relax_Iso_TT_PT@{_ u v u' v'} _ _ iso.
Definition relax_Iso_TT_TP@{a u v u' v'|a<=u,a<=u'} {A : Type@{a}} {B : Prop} (iso : Iso@{Type Type|u v} A B) : Iso@{Type Prop|u' v'} A B
  := @Build_Iso@{Type Prop|u' v'} A B iso.(to@{Type Type|u v}) iso.(from@{Type Type|u v}) (fun x => seq_p_of_t@{u} (iso.(to_from@{Type Type|u v}) x)) (fun x => iso.(from_to@{Type Type|u v}) x).
Definition relax_Iso_PP_TT_TP@{u v u' v'|} {A B : Prop} (iso : Iso@{Type Type|u v} A B) : Iso@{Type Prop|u' v'} A B
  := @relax_Iso_TT_TP@{_ u v u' v'} _ _ iso.
Definition relax_Iso_TT_PP@{u v u' v'|} {A B : Prop} (iso : Iso@{Type Type|u v} A B) : Iso@{Prop Prop|u' v'} A B
  := @Build_Iso@{Prop Prop|u' v'} A B iso.(to@{Type Type|u v}) iso.(from@{Type Type|u v}) (fun x => seq_p_of_t@{u} (iso.(to_from@{Type Type|u v}) x)) (fun x => seq_p_of_t@{v} (iso.(from_to@{Type Type|u v}) x)).
Definition relax_Iso_TT_TT@{a b u v u' v'|a<=u,b<=v,a<=u',b<=v'} {A : Type@{a}} {B : Type@{b}} (iso : Iso@{Type Type|u v} A B) : Iso@{Type Type|u' v'} A B
  := @Build_Iso@{Type Type|u' v'} A B iso.(to@{Type Type|u v}) iso.(from@{Type Type|u v}) (fun x => iso.(to_from@{Type Type|u v}) x) (fun x => iso.(from_to@{Type Type|u v}) x).
Definition relax_Iso_PT_TT_TT@{b u v u' v'|b<=v,b<=v'} {A : Prop} {B : Type@{b}} (iso : Iso@{Type Type|u v} A B) : Iso@{Type Type|u' v'} A B
  := @relax_Iso_TT_TT@{_ _ u v u' v'} _ _ iso.
Definition relax_Iso_TP_TT_TT@{a u v u' v'|a<=u,a<=u'} {A : Type@{a}} {B : Prop} (iso : Iso@{Type Type|u v} A B) : Iso@{Type Type|u' v'} A B
  := @relax_Iso_TT_TT@{_ _ u v u' v'} _ _ iso.
Definition relax_Iso_PP_TT_TT@{u v u' v'|u<=u',v<=v'} {A B : Prop} (iso : Iso@{Type Type|u v} A B) : Iso@{Type Type|u' v'} A B
  := @relax_Iso_TT_TT@{_ _ u v u' v'} _ _ iso.

Definition relax_Iso_sP_sT@{u v u' v'|} {A B} (iso : Iso@{SProp Prop|u v} A B) : Iso@{SProp Type|u' v'} A B
  := @Build_Iso@{SProp Type|u' v'} A B iso.(to@{SProp Prop|u v}) iso.(from@{SProp Prop|u v}) (fun x => seq_t_of_p@{u'} (iso.(to_from@{SProp Prop|u v}) x)) (fun x => iso.(from_to@{SProp Prop|u v}) x).
Definition relax_Iso_sT_sT@{b u v u' v'|b<=v,b<=v'} {A : SProp} {B : Type@{b}} (iso : Iso@{SProp Type|u v} A B) : Iso@{SProp Type|u' v'} A B
  := @Build_Iso@{SProp Type|u' v'} A B iso.(to@{SProp Type|u v}) iso.(from@{SProp Type|u v}) (fun x => iso.(to_from@{SProp Type|u v}) x) (fun x => iso.(from_to@{SProp Type|u v}) x).
Definition relax_Iso_sP_sT_sT@{u v u' v'|} {A : SProp} {B : Prop} (iso : Iso@{SProp Type|u v} A B) : Iso@{SProp Type|u' v'} A B
  := @relax_Iso_sT_sT@{_ u v u' v'} _ _ iso.
Definition relax_Iso_sT_sP@{u v u' v'|} {A} {B : Prop} (iso : Iso@{SProp Type|u v} A B) : Iso@{SProp Prop|u' v'} A B
  := @Build_Iso@{SProp Prop|u' v'} A B iso.(to@{SProp Type|u v}) iso.(from@{SProp Type|u v}) (fun x => seq_p_of_t@{u'} (iso.(to_from@{SProp Type|u v}) x)) (fun x => iso.(from_to@{SProp Type|u v}) x).
Definition relax_Iso_Ps_Ts@{u v u' v'|} {A B} (iso : Iso@{Prop SProp|u v} A B) : Iso@{Type SProp|u' v'} A B
  := @Build_Iso@{Type SProp|u' v'} A B iso.(to@{Prop SProp|u v}) iso.(from@{Prop SProp|u v}) (fun x => iso.(to_from@{Prop SProp|u v}) x) (fun x => seq_t_of_p@{v'} (iso.(from_to@{Prop SProp|u v}) x)).
Definition relax_Iso_Ts_Ts@{a u v u' v'|a<=u,a<=u'} {A : Type@{a}} {B : SProp} (iso : Iso@{Type SProp|u v} A B) : Iso@{Type SProp|u' v'} A B
  := @Build_Iso@{Type SProp|u' v'} A B iso.(to@{Type SProp|u v}) iso.(from@{Type SProp|u v}) (fun x => iso.(to_from@{Type SProp|u v}) x) (fun x => iso.(from_to@{Type SProp|u v}) x).
Definition relax_Iso_Ps_Ts_Ts@{u v u' v'|} {A : Prop} {B : SProp} (iso : Iso@{Type SProp|u v} A B) : Iso@{Type SProp|u' v'} A B
  := @relax_Iso_Ts_Ts@{_ u v u' v'} _ _ iso.
Definition relax_Iso_Ts_Ps@{u v u' v'|} {A : Prop} {B} (iso : Iso@{Type SProp|u v} A B) : Iso@{Prop SProp|u' v'} A B
  := @Build_Iso@{Prop SProp|u' v'} A B iso.(to@{Type SProp|u v}) iso.(from@{Type SProp|u v}) (fun x => iso.(to_from@{Type SProp|u v}) x) (fun x => seq_p_of_t@{u'} (iso.(from_to@{Type SProp|u v}) x)).

Definition lift_rel_iso@{s1 s'1 s2 s'2 | u1 u'1 u2 u'2 | } {A1 B1} {i1 : Iso@{s1 s'1 | u1 u'1} A1 B1} {x1 y1} {A2 B2} {i2 : Iso@{s2 s'2 | u2 u'2} A2 B2} {x2 y2}
  : (eq (i1 x1) y1 -> eq (i2 x2) y2)
    -> @rel_iso@{s1 s'1|u1 u'1} A1 B1 i1 x1 y1 -> @rel_iso@{s2 s'2|u2 u'2} A2 B2 i2 x2 y2
    := fun f => f.

Definition relax_rel_iso_iso_Sort_P_T@{u0 v0 v'0 u1 v1 v'1} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Prop|u0 v0 v'0} t1 t2 -> rel_iso iso_Sort@{Type|u1 v1 v'1} t1 t2.
Proof. apply lift_rel_iso, seq_Type_of_Prop. Defined.

Definition unrelax_rel_iso_sort@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B i x y} : rel_iso_sort (@RelaxIsoOrSort@{a b u v r} allow_relaxed A B i) x y -> rel_iso_sort i x y := fun h => h.
Definition unrelax'_rel_iso_sort@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B i x y} : rel_iso_sort (@Relax'IsoOrSort@{a b u v r} allow_relaxed A B i) x y -> rel_iso_sort i x y :=
  if allow_relaxed return rel_iso_sort (@Relax'IsoOrSort allow_relaxed A B i) x y -> rel_iso_sort i x y then fun h => h else fun h => h.

Module IsoOrSortAndRelIso.
  Fixpoint to'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B R} (i : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R) : A -> B :=
    match i in @IsoOrSortAndRelIso allow_relaxed A B R return A -> B with
    | IsoOrSortAndRelIsoIso i => i.(IsomorphismDefinitions.to)
    | IsoOrSortAndRelIsoIsoTypeSProp i => fun x => wrap_sprop (i.(IsomorphismDefinitions.to) x)
    | IsoOrSortAndRelIsoIsoSPropType i => fun x => i.(IsomorphismDefinitions.to) (unwrap_sprop x)
    | IsoOrSortAndRelIsoIsoSPropSProp i => fun x => wrap_sprop (i.(IsomorphismDefinitions.to) (unwrap_sprop x))
    | IsoOrSortAndRelIsoPropProp => fun x => x
    | IsoOrSortAndRelIsoSPropSProp => fun x => x
    | IsoOrSortAndRelIsoTypeType => fun x => x
    | IsoOrSortAndRelIsoPropType => fun x => x
    | IsoOrSortAndRelIsoPropSProp => fun x => SInhabited x
    | IsoOrSortAndRelIsoForall isoA isoB => fun f a => @to' _ _ _ _ (isoB _ _ (isoA.(IsomorphismDefinitions.to_from) a)) (f (isoA.(IsomorphismDefinitions.from) a))
    end.
  Definition to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B R} : forall (i : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R), A -> B :=
    if allow_relaxed return @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R -> A -> B then to' else fun i => (Iso_of_IsoOrSortAndRelIso i).(IsomorphismDefinitions.to).
  Definition from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} false A B R) : B -> A :=
    (Iso_of_IsoOrSortAndRelIso i).(IsomorphismDefinitions.from).
  Definition to_from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} false A B R) : forall x, eq (to i (from i x)) x :=
    (Iso_of_IsoOrSortAndRelIso i).(IsomorphismDefinitions.to_from).
  Definition from_to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} false A B R) : forall x, eq (from i (to i x)) x :=
    (Iso_of_IsoOrSortAndRelIso i).(IsomorphismDefinitions.from_to).
(*
  Fixpoint to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : A -> B :=
    match i in @IsoOrSortAndRelIso A B R return A -> B with
    | IsoOrSortAndRelIsoIso i => i.(IsomorphismDefinitions.to)
    | IsoOrSortAndRelIsoPropProp => fun x => x
    | IsoOrSortAndRelIsoSPropSProp => fun x => x
    | IsoOrSortAndRelIsoTypeType => fun x => x
    | IsoArrow isoA isoB => fun f b =>
        @to _ _ _ (isoB _ _ (isoA.(IsomorphismDefinitions.to_from) b)) (f (isoA.(IsomorphismDefinitions.from) b))
    end.

  Fixpoint from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : B -> A :=
    match i in @IsoOrSortAndRelIso A B R return B -> A with
    | IsoOrSortAndRelIsoIso i => i.(IsomorphismDefinitions.from)
    | IsoOrSortAndRelIsoPropProp => fun x => x
    | IsoOrSortAndRelIsoSPropSProp => fun x => x
    | IsoOrSortAndRelIsoTypeType => fun x => x
    | IsoArrow isoA isoB => fun f a =>
        @from _ _ _ (isoB _ _ (eq_refl (isoA.(IsomorphismDefinitions.to) a))) (f (isoA.(IsomorphismDefinitions.to) a))
    end.

  Fixpoint to_from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : forall x, eq (to i (from i x)) x.
  Proof.
    refine
      match i as i return forall x, eq (to i (from i x)) x with
      | IsoOrSortAndRelIsoIso i => i.(IsomorphismDefinitions.to_from)
      | IsoOrSortAndRelIsoPropProp => fun x => eq_refl
      | IsoOrSortAndRelIsoSPropSProp => fun x => eq_refl
      | IsoOrSortAndRelIsoTypeType => fun x => eq_refl
      | IsoOrSortAndRelIsoForall isoA isoB => fun f => _
      end.
    apply functional_extensionality_dep; intro x.
    cbn [to from].
    set (e := isoA.(IsomorphismDefinitions.to_from) x) in *.
    set (x' := isoA.(IsomorphismDefinitions.from) x) in *.
    clearbody e.
    clearbody x'.
    destruct e.
    apply to_from.
  Defined.

  Fixpoint from_to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : forall x, eq (from i (to i x)) x.
  Proof.
    refine
      match i as i return forall x, eq (from i (to i x)) x with
      | IsoOrSortAndRelIsoIso i => i.(IsomorphismDefinitions.from_to)
      | IsoOrSortAndRelIsoPropProp => fun x => eq_refl
      | IsoOrSortAndRelIsoSPropSProp => fun x => eq_refl
      | IsoOrSortAndRelIsoTypeType => fun x => eq_refl
      | IsoOrSortAndRelIsoForall isoA isoB => fun f => _
      end.
    { apply functional_extensionality_dep; intro x.
      cbn [to from].
      generalize (IsomorphismDefinitions.to_from isoA (isoA.(IsomorphismDefinitions.to) x)).
      intro e.
      assert (e' : eq (isoA.(IsomorphismDefinitions.from) (isoA.(IsomorphismDefinitions.to) x)) x) by apply IsomorphismDefinitions.from_to.
      assert (ee : eq@{SProp|Set} (f_equal (isoA.(IsomorphismDefinitions.to)) e') e) by reflexivity.
      destruct ee.
      generalize dependent (isoA.(IsomorphismDefinitions.from) (isoA.(IsomorphismDefinitions.to) x)).
      intros a []; cbn.
      apply from_to. }
  Defined. *)
(*

  #[local] Set Primitive Projections.
  Polymorphic Cumulative Record RelaxedIso@{ua ub ur} {A : Type@{ua}} {B : Type@{ub}} (R : A -> B -> Type@{ur}) := {
    relaxed_to : A -> B;
    relaxed_from : B -> A;
    relaxed_rel_to : forall a, R a (relaxed_to a);
    relaxed_rel_from : forall b, R (relaxed_from b) b;
  }.

  Fixpoint to_relaxed_iso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : @RelaxedIso@{u u u} A B R.
  Proof.
    refine
      match i in @IsoOrSortAndRelIso A B R return @RelaxedIso@{u u u} A B R with
      | IsoOrSortAndRelIsoIso i => {| relaxed_to := i.(IsomorphismDefinitions.to); relaxed_from := i.(IsomorphismDefinitions.from); relaxed_rel_to := fun x => wrap_sprop rel_iso_refl; relaxed_rel_from := fun x => wrap_sprop (i.(IsomorphismDefinitions.to_from) x) |}
      | IsoOrSortAndRelIsoPropProp => @Build_RelaxedIso@{u u u} _ _ _ (fun x => x) (fun x => x) (fun x => iso_refl@{Prop|Set}) (fun x => iso_refl@{Prop|Set})
      | IsoOrSortAndRelIsoSPropSProp => @Build_RelaxedIso@{u u u} _ _ _ (fun x => x) (fun x => x) (fun x => iso_refl@{SProp|Set}) (fun x => iso_refl@{SProp|Set})
      | IsoOrSortAndRelIsoTypeType => @Build_RelaxedIso@{u u u} _ _ _ (fun x => x) (fun x => x) (fun x => iso_refl@{Type|v}) (fun x => iso_refl@{Type|v})
      | IsoOrSortAndRelIsoForall isoA isoB =>
          let isoRelB a a' r := @to_relaxed_iso _ _ _ (isoB a a' r) in
          {| relaxed_to f b := relaxed_to (@to_relaxed_iso _ _ _ (isoB _ _ (isoA.(to_from) b))) (f (isoA.(from) b))
          ; relaxed_from f a := relaxed_from (@to_relaxed_iso _ _ _ (isoB _ _ (eq_refl (isoA.(to) a)))) (f (isoA.(to) a))
          ; relaxed_rel_to f a a' r := _ (relaxed_rel_to (isoRelB a a' r) (f _))
          ; relaxed_rel_from f a a' r := match r with eq_refl => relaxed_rel_from (isoRelB _ _ _) (f _) end
          |}
          (*
          existT _
            (fun f a => projT1 (val f a) (f (projT1 (@from_and_rel _ _ _ isoA) a)))
            (fun f a a' r => let xx := projT2 (val _ _) _ in _)*)
      end; subst isoRelB; cbv [rel_iso] in *; destruct r.
    { set (r := isoA.(to_from) (isoA.(to) a)).
      pose proof (isoA.(from_to) a) as r'.
      set (a' := isoA.(from) (isoA.(to) a)) in *.
      clearbody r a'.
      destruct r.
      destruct r'.
      exact (fun x => x). }
  Defined.

  Definition to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : A -> B :=
    relaxed_to (to_relaxed_iso i).
  Definition from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : B -> A :=
    relaxed_from (to_relaxed_iso i).
  Definition rel_to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : forall a, R a (to i a) :=
    relaxed_rel_to (to_relaxed_iso i).
  Definition rel_from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : forall b, R (from i b) b :=
    relaxed_rel_from (to_relaxed_iso i). *)
End IsoOrSortAndRelIso.

(*
  Fixpoint to_and_rel@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : sigT (fun f : A -> B => forall a, R a (f a))
  with from_and_rel@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : sigT (fun f : B -> A => forall a, R (f a) a).
  all: [ > refine match i in @IsoOrSortAndRelIso A B R return sigT (fun f : A -> B => forall a, R a (f a)) with
  | IsoOrSortAndRelIsoIso i => existT _ i.(IsomorphismDefinitions.to) (fun x => wrap_sprop rel_iso_refl)
  | IsoOrSortAndRelIsoPropProp => existT _ (fun x => x) (fun x => iso_refl)
  | IsoOrSortAndRelIsoSPropSProp => existT _ (fun x => x) (fun x => iso_refl)
  | IsoOrSortAndRelIsoTypeType => existT _ (fun x => x) (fun x => iso_refl)
  | IsoOrSortAndRelIsoForall isoA isoB =>
      let val f a := @to_and_rel _ _ _ (isoB _ _ (projT2 (@from_and_rel _ _ _ isoA) a)) in
      existT _
        (fun f a => projT1 (val f a) (f (projT1 (@from_and_rel _ _ _ isoA) a)))
        (fun f a a' r => let xx := projT2 (val _ _) _ in _)
  end
  | refine match i in @IsoOrSortAndRelIso A B R return sigT (fun f : B -> A => forall a, R (f a) a) with
  | IsoOrSortAndRelIsoIso i => existT _ i.(IsomorphismDefinitions.from) (fun x => wrap_sprop (i.(IsomorphismDefinitions.to_from) x))
  | IsoOrSortAndRelIsoPropProp => existT _ (fun x => x) (fun x => iso_refl)
  | IsoOrSortAndRelIsoSPropSProp => existT _ (fun x => x) (fun x => iso_refl)
  | IsoOrSortAndRelIsoTypeType => existT _ (fun x => x) (fun x => iso_refl)
  | IsoOrSortAndRelIsoForall isoA isoB =>
      let val f a := @from_and_rel _ _ _ (isoB _ _ (projT2 (@to_and_rel _ _ _ isoA) a)) in
      existT _
        (fun f a => projT1 (val f a) (f (projT1 (@to_and_rel _ _ _ isoA) a)))
        (fun f a a' r => let xx := projT2 (val _ _) _ in _)
  end ]; cbv beta in *.
idtac.
 *)


(* Fixpoint Iso_of_IsoOrSortAndRelIso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : Iso@{Type Type|u u} A B.
  refine match i in @IsoOrSortAndRelIso A B R return Iso@{Type Type|u u} A B with
  | IsoOrSortAndRelIsoIso i => i
  | IsoOrSortAndRelIsoPropProp => iso_Sort@{Prop|v u u}
  | IsoOrSortAndRelIsoSPropSProp => iso_Sort@{SProp|v u u}
  | IsoOrSortAndRelIsoTypeType => iso_Sort@{Type|v u u}
  | IsoOrSortAndRelIsoForall isoA i2 => IsoForall (isoA:=@Iso_of_IsoOrSortAndRelIso _ _ _ isoA) _ _ _
  end.
Defined. *)

(*

  refine rel_iso_refl.
  2: hnf.
  2:
  2: refine rel_iso_refl.

  Set Printing Depth 100000.
  Show Proof.
  hnf.
  Show Proof.
  Defined.

  Fixpoint from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B R} (i : @IsoOrSortAndRelIso@{a b u v r} A B R) : B -> A.
  Definition from@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : B -> A :=
    (Iso_of_IsoOrSort i).(from).
  Definition to_from@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : forall x, eq (to@{u v v'} i (from@{u v v'} i x)) x :=
    (Iso_of_IsoOrSort i).(to_from).
  Definition from_to@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : forall x, eq (from@{u v v'} i (to@{u v v'} i x)) x :=
    (Iso_of_IsoOrSort i).(from_to).
End IsoOrSortAndRelIso. *)
(*
Module IsoOrSort.
  Definition to@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : A -> B :=
    (Iso_of_IsoOrSort i).(to).
  Definition from@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : B -> A :=
    (Iso_of_IsoOrSort i).(from).
  Definition to_from@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : forall x, eq (to@{u v v'} i (from@{u v v'} i x)) x :=
    (Iso_of_IsoOrSort i).(to_from).
  Definition from_to@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : forall x, eq (from@{u v v'} i (to@{u v v'} i x)) x :=
    (Iso_of_IsoOrSort i).(from_to).
End IsoOrSort.
 *)

Definition Iso_of_IsoOrSort@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B} (i : @IsoOrSort@{a b u v r} A B) : Iso@{Type Type|u u} A B :=
  @Iso_of_IsoOrSortAndRelIso@{a b u v r} A B _ i.
Module IsoOrSort.
  Definition to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} (i : @IsoOrSort'@{a b u v r} allow_relaxed A B) : A -> B :=
    IsoOrSortAndRelIso.to i.
  Definition from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B} (i : @IsoOrSort@{a b u v r} A B) : B -> A :=
    (Iso_of_IsoOrSort i).(from).
  Definition to_from@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B} (i : @IsoOrSort@{a b u v r} A B) : forall x, eq (to@{a b u v r} i (from@{a b u v r} i x)) x :=
    (Iso_of_IsoOrSort i).(to_from).
  Definition from_to@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {A B} (i : @IsoOrSort@{a b u v r} A B) : forall x, eq (from@{a b u v r} i (to@{a b u v r} i x)) x :=
    (Iso_of_IsoOrSort i).(from_to).
End IsoOrSort.

Definition iso_or_sort_and_rel_iso_refl@{u v l m|l < v,v < u} {allow_relaxed} {A : Type@{v}} : @IsoOrSortAndRelIso@{v v u l v} allow_relaxed A A _ := IsoOrSortAndRelIsoIso@{v v u l v} iso_refl@{Type|v}.
Definition iso_or_sort_refl@{u v l m|l < v,v < u} {allow_relaxed} {A : Type@{v}} : IsoOrSort'@{v v u l v} allow_relaxed A A := iso_or_sort_and_rel_iso_refl@{u v l m}.
(*
Definition rel_iso_of_rel_iso_sort_and_rel@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} A B R) : forall {a b}, R a b -> rel_iso (Iso_of_IsoOrSortAndRelIso iso) a b.
  refine match iso in @IsoOrSortAndRelIso A B R return forall a b, R a b -> rel_iso (Iso_of_IsoOrSortAndRelIso iso) a b with
  | IsoOrSortAndRelIsoIso iso => fun a b r => unwrap_sprop r
  | _ => fun a b r => _ (*iso_refl@{_|v'}*)
  end.
  all: cbv [Iso_of_IsoOrSortAndRelIso]; cbn in *.
all: cbv [rel_iso iso_refl to].

Definition rel_iso_of_rel_iso_sort_and_rel@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} A B R) : forall {a b}, R a b -> rel_iso (Iso_of_IsoOrSortAndRelIso iso) a b.
  refine match iso in @IsoOrSortAndRelIso A B R return forall a b, R a b -> rel_iso (Iso_of_IsoOrSortAndRelIso iso) a b with
  | IsoOrSortAndRelIsoIso iso => fun a b r => unwrap_sprop r
  | _ => fun a b r => _ (*iso_refl@{_|v'}*)
  end.
  all: cbv [Iso_of_IsoOrSortAndRelIso]; cbn in *.
all: cbv [rel_iso iso_refl to]. *)
Fixpoint rel_iso_sort_and_rel_of_rel_iso'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R) : forall {a b}, eq (IsoOrSort.to iso a) b -> R a b.
Proof.
  refine
    match iso in @IsoOrSortAndRelIso allow_relaxed A B R return forall a b, eq (IsoOrSort.to iso a) b -> R a b with
    | IsoOrSortAndRelIsoIso (true | false) iso => fun a b r => wrap_sprop (Build_rel_iso r)
    | IsoOrSortAndRelIsoIsoTypeSProp (true | false) iso => fun a b r => wrap_sprop (Build_rel_iso (f_equal unwrap_sprop r))
    | IsoOrSortAndRelIsoIsoSPropType (true | false) iso => fun a b r => ltac:(apply wrap_sprop, Build_rel_iso, r)
    | IsoOrSortAndRelIsoIsoSPropSProp (true | false) iso => fun a b r => wrap_sprop (Build_rel_iso (f_equal unwrap_sprop r))
    | IsoOrSortAndRelIsoPropProp (true | false)
    | IsoOrSortAndRelIsoSPropSProp (true | false)
    | IsoOrSortAndRelIsoTypeType (true | false)
      => fun a b r => match r with eq_refl => iso_refl@{_|v} end
    | IsoOrSortAndRelIsoPropType
      => fun a b r => match r with eq_refl => relax_Iso_PP_PT iso_refl@{_|v} end
    | IsoOrSortAndRelIsoPropSProp
      => fun a b r => match r with eq_refl => iso_SInhabited@{a b} end
    | IsoOrSortAndRelIsoForall (true | false) isoA isoB => fun a b r a' b' e =>
        let xx := @rel_iso_sort_and_rel_of_rel_iso' _ _ _ _ (isoB _ _ _) (a _) (b _) (f_equal (fun f => f b') r) in
        _
    end.
  all: clearbody xx; revert xx.
  all: generalize (to_from isoA b').
  all: generalize (from_to isoA a').
  all: destruct e as [e]; hnf in e; destruct e.
  all: generalize (from isoA (to isoA a')); intro.
  all: intros [] [].
  all: exact (fun x => x).
Defined.

Definition rel_iso_sort_and_rel_of_rel_iso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} false A B R) : forall {a b}, rel_iso (Iso_of_IsoOrSortAndRelIso iso) a b -> R a b :=
    @rel_iso_sort_and_rel_of_rel_iso' _ _ _ _ iso.


Definition rel_iso_sort_of_rel_iso'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed A B} (iso : @IsoOrSort'@{a b u v r} allow_relaxed A B) : forall {a b}, eq (IsoOrSort.to iso a) b -> rel_iso_sort iso a b
  := @rel_iso_sort_and_rel_of_rel_iso' _ _ _ _ iso.

Definition rel_iso_sort_of_rel_iso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B} (iso : @IsoOrSort@{a b u v r} A B) : forall {a b}, rel_iso (Iso_of_IsoOrSort iso) a b -> rel_iso_sort iso a b
  := @rel_iso_sort_of_rel_iso'@{a b u v r} _ _ _ iso.

(* Definition rel_iso_sort_refl_to@{u v v'|v < u,v' < u} {A : Type@{u}} {A' : Type@{u}} {isoA : IsoOrSort@{u v v'} A A'}
  : forall {a}, rel_iso_sort isoA a (IsoOrSort.to isoA a).
Proof.
  refine
    match isoA return forall {a}, rel_iso_sort isoA a (IsoOrSort.to isoA a) with
    | IsoOrSortAndRelIsoIso isoA => fun a => wrap_sprop eq_refl@{Type|v'}
    | _ => fun a => iso_refl@{_|v}
    end.
Defined.

Definition rel_iso_sort_from_refl@{u v v'|v < u,v' < u} {A A'} {isoA : IsoOrSort@{u v v'} A A'}
  : forall {a}, rel_iso_sort isoA (IsoOrSort.from isoA a) a.
Proof.
  refine
    match isoA return forall {a}, rel_iso_sort isoA (IsoOrSort.from isoA a) a with
    | IsoOrSortAndRelIsoIso isoA => fun a => wrap_sprop (to_from isoA a)
    | _ => fun a => iso_refl@{_|v}
    end.
Defined. *)



(* Definition IsoOrSortForall'@{u0 u1 u2 u3 u23 u4 u5 v0 v1 v2 v3|v0 < u0,v1 < u0,v2 < u23,v3 < u23,u0 <= u4,u0 <= u5,u2 <= u23,u2 <= u4,u3 <= u23,u3 <= u5,u23 <= u4,u23 <= u5}
  {A A'} (isoA : IsoOrSort@{u0 v0 v1} A A') (B : A -> Type@{u2}) (B' : A' -> Type@{u3})
  : (forall a a' (He : rel_iso_sort isoA a a'), IsoOrSort@{u23 v2 v3} (B a) (B' a'))
    -> Iso@{_ _|u4 u5} (forall a, B a) (forall a', B' a').
Proof.
  intro H.
  all: unshelve esplit; [ intros f a .. | intro x; shelve | intro x; shelve ].
  all: first [ specialize (H a) | specialize (fun a' => H a' a) ].
  all: first [ specialize (H (IsoOrSort.to isoA a)) | specialize (H (IsoOrSort.from isoA a)) ].
  all: first [ specialize (H rel_iso_sort_refl_to) | specialize (H rel_iso_sort_from_refl) ].
  all: [ > first [ apply (IsoOrSort.to H) | apply (IsoOrSort.from H) ]; auto .. ].
  Unshelve.
  all: cbn.
  all: apply functional_extensionality_dep; intro.
  { destruct isoA as [A A' isoA | | | ]; cbv [rel_iso_sort_refl_to rel_iso_sort_from_refl IsoOrSort.from IsoOrSort.to rel_iso_sort rel_iso Iso_of_IsoOrSort iso_Sort] in *.
    all: cbn [to from] in *.
    all: set (H' := H _); clearbody H'; clear H.
    all: [ > set (e := to_from _ _); clearbody e | .. ].
    all: [ > set (a := to isoA (from isoA _)) in *; clearbody a | .. ].
    all: [ > destruct e | .. ].
    all: set (H := H' _ _); clearbody H; clear H'.
    all: set (xx' := x _); clearbody xx'; clear x.
    all: destruct H; [ apply to_from | .. ].
    all: constructor. }
  { destruct isoA as [A A' isoA | | | ]; cbv [rel_iso_sort_refl_to rel_iso_sort_from_refl IsoOrSort.from IsoOrSort.to rel_iso_sort rel_iso Iso_of_IsoOrSort iso_Sort] in *.
    all: cbn [to from] in *.
    { let ev := match goal with |- context[@to_from ?A ?B ?i ?x] => constr:(@to_from A B i x) end in
      set (e := ev).
      clearbody e.
      assert (e' : eq (isoA.(from) (isoA.(to) x0)) x0) by apply from_to.
      assert (ee : eq@{SProp|Set} (f_equal (isoA.(to)) e') e) by reflexivity.
      destruct ee.
      revert e'.
      set (a := from isoA (to isoA _)); clearbody a.
      intros []; cbn.
      set (H' := H _ _ _); clearbody H'; clear H.
      generalize (x a); clear x; intro x.
      destruct H'; [ apply from_to | constructor .. ]. }
    all: set (xx' := x _); clearbody xx'; clear x.
    all: destruct H; [ apply from_to | constructor .. ]. }
Defined.
*)
Definition IsoOrSortForall@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed : bool}
  {A : Type@{a}} {A' : Type@{b}} (isoA : Iso@{Type Type|a b} A A')
  (B : A -> Type@{a}) (B' : A' -> Type@{b})
  (isoB : forall a a', rel_iso isoA a a' -> @IsoOrSort'@{a b u v r} allow_relaxed (B a) (B' a'))
  : @IsoOrSort'@{a b u v r} allow_relaxed (forall a, B a) (forall a', B' a')
  := @IsoOrSortAndRelIsoForall@{a b u v r} allow_relaxed _ _ _ _ _ _ isoB.

Definition IsoArrow@{s0 s1 s2 s3|u0 u1 u2 u3 u4 u5|u0 <= u4,u1 <= u5,u2 <= u4,u3 <= u5}
  {A A'} (isoA : Iso@{s0 s1|u0 u1} A A') (B : Type@{s2|u2}) (B' : Type@{s3|u3}) (isoB : Iso@{s2 s3|u4 u5} B B')
  : Iso@{s2 s3|u4 u5} (A -> B) (A' -> B')
  := IsoForall (isoA:=isoA) (fun _ => B) (fun _ => B') (fun a a' H => isoB).

Definition IsoOrSortAndRelIsoArrow@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed : bool}
  {A : Type@{a}} {A' : Type@{b}} (isoA : Iso@{Type Type|a b} A A')
  (B : Type@{a}) (B' : Type@{b}) {R} (isoB : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed B B' R)
  : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed (A -> B) (A' -> B') (fun f g => forall a a', rel_iso isoA a a' -> R (f a) (g a'))
  := @IsoOrSortAndRelIsoForall@{a b u v r} allow_relaxed _ _ _ _ _ _ (fun a a' H => isoB).

Definition IsoOrSortArrow@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed : bool}
  {A : Type@{a}} {A' : Type@{b}} (isoA : Iso@{Type Type|a b} A A')
  (B : Type@{a}) (B' : Type@{b}) (isoB : IsoOrSort'@{a b u v r} allow_relaxed B B')
  : @IsoOrSort'@{a b u v r} allow_relaxed (A -> B) (A' -> B')
  := @IsoOrSortAndRelIsoArrow@{a b u v r} allow_relaxed _ _ _ _ _ _ isoB.

Definition IsoFun@{s0 s1 s2 s3|u0 u1 u2 u3 u4 u5|u0 <= u4,u1 <= u5,u2 <= u4,u3 <= u5}
  {A A'} (isoA : Iso@{s0 s1|u0 u1} A A')
  {B : A -> Type@{s2|u2}} {B' : A' -> Type@{s3|u3}} (isoB : forall a a' (He : rel_iso isoA a a'), Iso (B a) (B' a'))
  (f : forall a, B a) (f' : forall a', B' a')
  : (forall a a' (Ha : rel_iso isoA a a'), rel_iso (isoB a a' Ha) (f a) (f' a'))
    -> rel_iso (@IsoForall A A' isoA B B' isoB) f f'.
Proof.
  intro H; constructor.
  apply functional_extensionality_dep; intro a'.
  cbv [IsoForall].
  cbn [to from] in *.
  apply H.
Defined.

(* Fixpoint IsoOrSortAndRelIsoFun@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A : Type@{v}} {A' : Type@{v'}} (isoA : Iso@{Type Type|v v'} A A')
  {B : A -> Type@{v}} {B' : A' -> Type@{v'}} {R} (isoB : forall a a' (He : rel_iso isoA a a'), @IsoOrSortAndRelIso@{a b u v r} (B a) (B' a') (R a a' He))
  (f : forall a, B a) (f' : forall a', B' a')
  : (forall a a' (Ha : rel_iso isoA a a'), R a a' Ha (f a) (f' a'))
    -> rel_iso (@IsoOrSortAndRelIsoArrow@{a b u v r} _ _ _ _ _ _ isoB) f f'.
Proof.
  intro H.
  apply functional_extensionality_dep; intro a'.
  cbv [rel_iso] in *.
  cbv [IsoForall].
  cbn [to from] in *.
  apply H.
Defined. *)

Definition IsoOrSortFun@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed : bool}
  {A : Type@{a}} {A' : Type@{b}} (isoA : Iso@{Type Type|a b} A A')
  {B : A -> Type@{a}} {B' : A' -> Type@{b}} (isoB : forall a a' (He : rel_iso isoA a a'), @IsoOrSort'@{a b u v r} allow_relaxed (B a) (B' a'))
  (f : forall a, B a) (f' : forall a', B' a')
  : (forall a a' (Ha : rel_iso isoA a a'), rel_iso_sort (isoB a a' Ha) (f a) (f' a'))
    -> rel_iso_sort (@IsoOrSortForall@{a b u v r} allow_relaxed _ _ _ _ _ isoB) f f'
    := fun r => r.

Definition IsoFunND@{s0 s1 s2 s3|u0 u1 u2 u3 u4 u5|u0 <= u4,u1 <= u5,u2 <= u4,u3 <= u5}
  {A A'} (isoA : Iso@{s0 s1|u0 u1} A A') {B B'} (isoB : Iso@{s2 s3|u2 u3} B B')
  (f : A -> B) (f' : A' -> B')
  : (forall a a', rel_iso isoA a a' -> rel_iso isoB (f a) (f' a'))
    -> rel_iso (@IsoArrow A A' isoA B B' isoB) f f'
    := IsoFun (isoA:=isoA) (B:=fun _ => B) (B':=fun _ => B') (fun a a' H => isoB) f f'.

Definition IsoOrSortFunND@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed : bool}
  {A : Type@{a}} {A' : Type@{b}} (isoA : Iso@{Type Type|a b} A A')
  {B : Type@{a}} {B' : Type@{b}} (isoB : @IsoOrSort'@{a b u v r} allow_relaxed B B')
  (f : A -> B) (f' : A' -> B')
  : (forall a a', rel_iso isoA a a' -> rel_iso_sort isoB (f a) (f' a'))
    -> rel_iso_sort (@IsoOrSortArrow@{a b u v r} allow_relaxed _ _ isoA _ _ isoB) f f'
    := fun r => r.

Definition IsoUnFun@{s0 s1 s2 s3|u0 u1 u2 u3 u4 u5|u0 <= u4,u1 <= u5,u2 <= u4,u3 <= u5}
  {A A'} (isoA : Iso@{s0 s1|u0 u1} A A')
  {B : A -> Type@{s2|u2}} {B' : A' -> Type@{s3|u3}} (isoB : forall a a' (He : rel_iso isoA a a'), Iso (B a) (B' a'))
  (f : forall a, B a) (f' : forall a', B' a')
  : rel_iso (@IsoForall A A' isoA B B' isoB) f f'
    -> (forall a a' (Ha : rel_iso isoA a a'), rel_iso (isoB a a' Ha) (f a) (f' a')).
Proof.
  intro H.
  intros a a' Ha.
  constructor.
  destruct H as [H], Ha as [Ha].
  cbv [IsoForall] in *.
  cbn [to from] in *.
  destruct H, Ha.
  set (h := to_from isoA (isoA a)).
  clearbody h.
  set (h' := from_to isoA a).
  set (a' := from isoA (to isoA a)) in *.
  clearbody h'.
  clearbody a'.
  destruct h'.
  reflexivity.
Defined.

Definition IsoOrSortUnFun@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed : bool}
  {A : Type@{a}} {A' : Type@{b}} (isoA : Iso@{Type Type|a b} A A')
  {B : A -> Type@{a}} {B' : A' -> Type@{b}} (isoB : forall a a' (He : rel_iso isoA a a'), @IsoOrSort'@{a b u v r} allow_relaxed (B a) (B' a'))
  (f : forall a, B a) (f' : forall a', B' a')
  : rel_iso_sort (@IsoOrSortForall@{a b u v r} allow_relaxed _ _ _ _ _ isoB) f f'
    -> (forall a a' (Ha : rel_iso isoA a a'), rel_iso_sort (isoB a a' Ha) (f a) (f' a'))
    := fun r => r.

Definition IsoUnFunND@{s0 s1 s2 s3|u0 u1 u2 u3 u4 u5|u0 <= u4,u1 <= u5,u2 <= u4,u3 <= u5}
  {A A'} (isoA : Iso@{s0 s1|u0 u1} A A') {B B'} (isoB : Iso@{s2 s3|u2 u3} B B')
  (f : A -> B) (f' : A' -> B')
  : rel_iso (@IsoArrow A A' isoA B B' isoB) f f'
    -> (forall a a', rel_iso isoA a a' -> rel_iso isoB (f a) (f' a'))
    := IsoUnFun (isoA:=isoA) (B:=fun _ => B) (B':=fun _ => B') (isoB:=fun a a' H => isoB) (f:=f) (f':=f').

Definition IsoOrSortUnFunND@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed : bool}
  {A : Type@{a}} {A' : Type@{b}} (isoA : Iso@{Type Type|a b} A A')
  {B : Type@{a}} {B' : Type@{b}} (isoB : @IsoOrSort'@{a b u v r} allow_relaxed B B')
  (f : A -> B) (f' : A' -> B')
  : rel_iso_sort (@IsoOrSortArrow@{a b u v r} allow_relaxed _ _ isoA _ _ isoB) f f'
    -> (forall a a', rel_iso isoA a a' -> rel_iso_sort isoB (f a) (f' a'))
  := IsoOrSortUnFun (isoA:=isoA) (B:=fun _ => B) (B':=fun _ => B') (isoB:=fun a a' H => isoB) (f:=f) (f':=f').

  (*
Definition IsoSPropForall_seq {A A'} (isoA : Iso A A') (B : A -> Prop) (B' : A' -> SProp)
  : (forall a a' (He : rel_iso isoA a a'), IsoSProp (B a) (B' a'))
    -> IsoSProp (forall a, B a) (forall a', B' a').
Proof.
  intro H; split; intros f a.
  all: first [ specialize (H a) | specialize (fun a' => H a' a) ].
  all: first [ specialize (H (isoA.(to) a)) | specialize (H (isoA.(from) a)) ].
  all: try specialize (H eq_refl).
  all: destruct H as [H0 H1].
  all: [ > | first [ apply H0 | apply H1 ]; auto .. ].
  cbv [rel_iso].
  pose proof (isoA.(to_from) a).
  generalize dependent (isoA.(to) (isoA.(from) a)).
  clear.
  intros ? []; reflexivity.
Defined. *)

Lemma UIP@{u} (A : Type@{u}) (x y : A) (p q : Logic.eq x y) : Logic.eq p q.
Proof.
  transitivity (eq_of_seq (seq_of_eq p)); [ destruct p; reflexivity | ].
  transitivity (eq_of_seq (seq_of_eq q)); [ | destruct q; reflexivity ].
  destruct (seq_of_eq p).
  reflexivity.
Defined.

Lemma UIP_p (A : Prop) (x y : A) (p q : Logic.eq x y) : Logic.eq p q.
Proof.
  transitivity (eq_of_seq (seq_of_eq p)); [ destruct p; reflexivity | ].
  transitivity (eq_of_seq (seq_of_eq q)); [ | destruct q; reflexivity ].
  destruct (seq_of_eq p).
  reflexivity.
Defined.

Lemma sUIPp@{u v} (A : Type@{u}) (x y : A) (p q : Logic.eq x y) : eq@{Prop|v} p q.
Proof.
  transitivity (eq_of_seq (seq_of_eq p)); [ destruct p; reflexivity | ].
  transitivity (eq_of_seq (seq_of_eq q)); [ | destruct q; reflexivity ].
  destruct (seq_of_eq p).
  reflexivity.
Defined.

Lemma sUIPt@{u v} (A : Type@{u}) (x y : A) (p q : Logic.eq x y) : eq@{Type|v} p q.
Proof.
  transitivity (eq_of_seq (seq_of_eq p)); [ destruct p; reflexivity | ].
  transitivity (eq_of_seq (seq_of_eq q)); [ | destruct q; reflexivity ].
  destruct (seq_of_eq p).
  reflexivity.
Defined.

Lemma sUIPpp@{u} (A : Prop) (x y : A) (p q : Logic.eq x y) : eq@{Prop|u} p q.
Proof.
  transitivity (eq_of_seq (seq_of_eq p)); [ destruct p; reflexivity | ].
  transitivity (eq_of_seq (seq_of_eq q)); [ | destruct q; reflexivity ].
  destruct (seq_of_eq p).
  reflexivity.
Defined.

Lemma sUIPtp@{u} (A : Prop) (x y : A) (p q : Logic.eq x y) : eq@{Type|u} p q.
Proof.
  transitivity (eq_of_seq (seq_of_eq p)); [ destruct p; reflexivity | ].
  transitivity (eq_of_seq (seq_of_eq q)); [ | destruct q; reflexivity ].
  destruct (seq_of_eq p).
  reflexivity.
Defined.

Definition iso_sym@{s s'|u u'|} {A B} (iso : Iso@{s s'|u u'} A B) : Iso B A
  := {| to := iso.(from); from := iso.(to);
        from_to := iso.(to_from); to_from := iso.(from_to) |}.

Lemma iso_sym_sym@{s s'|u u' umax|u<=umax,u'<=umax} {A B} (iso : Iso@{s s'|u u'} A B) : IsomorphismDefinitions.eq@{_|umax} (iso_sym (iso_sym iso)) iso.
Proof. destruct iso; reflexivity. Defined.

Definition rel_iso_sym@{s s'|u u'|} {A B} {iso : Iso@{s s'|u u'} A B} {x y} (H : rel_iso iso x y) : rel_iso (iso_sym iso) y x.
Proof. destruct H as [H]; constructor; cbv [iso_sym] in *; cbn in *; destruct H; apply from_to. Defined.

Definition rel_iso_unsym@{s s'|u u'|} {A B} {iso : Iso@{s s'|u u'} A B} {x y} (H : rel_iso (iso_sym iso) y x) : rel_iso iso x y.
Proof. destruct H as [H]; constructor; cbv [iso_sym] in *; cbn in *; destruct H; apply to_from. Defined.

Definition rel_iso_unsym_unsym@{s s'|u u' maxu|u <= maxu,u' <= maxu} {A B} {iso : Iso@{s s'|u u'} A B} {x y} (H : rel_iso (iso_sym (iso_sym iso)) x y)
  : eq@{_|maxu} (rel_iso_unsym (rel_iso_unsym H)) (match iso_sym_sym iso in eq _ i return rel_iso i x y with eq_refl => H end).
Proof. reflexivity. Qed.

Definition rel_iso_unsym_sym@{s s'|u u' maxu|u <= maxu,u' <= maxu} {A B} {iso : Iso@{s s'|u u'} A B} {x y} (H : rel_iso (iso_sym (iso_sym iso)) x y)
  : eq@{_|maxu} (rel_iso_unsym (rel_iso_sym H)) (Build_rel_iso (match iso_sym_sym iso in eq _ i return rel_iso i x y with eq_refl => H end)).
Proof. reflexivity. Qed.

Fixpoint iso_or_sort_sym'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} false A B R) : @IsoOrSort@{b a u v r} B A :=
    match iso in @IsoOrSortAndRelIso allow_relaxed A B R return if allow_relaxed return Type@{u} then IDProp else @IsoOrSort@{b a u v r} B A with
    | IsoOrSortAndRelIsoIso false i => IsoOrSortAndRelIsoIso@{b a u v r} (iso_sym@{_ _|a b} i)
    | IsoOrSortAndRelIsoIsoTypeSProp false i => IsoOrSortAndRelIsoIsoSPropType@{b a u v r} (iso_sym@{_ _|a b} i)
    | IsoOrSortAndRelIsoIsoSPropType false i => IsoOrSortAndRelIsoIsoTypeSProp@{b a u v r} (iso_sym@{_ _|a b} i)
    | IsoOrSortAndRelIsoIsoSPropSProp false i => IsoOrSortAndRelIsoIsoSPropSProp@{b a u v r} (iso_sym@{_ _|a b} i)
    | IsoOrSortAndRelIsoPropProp false => IsoOrSortAndRelIsoPropProp@{b a u v r}
    | IsoOrSortAndRelIsoSPropSProp false => IsoOrSortAndRelIsoSPropSProp@{b a u v r}
    | IsoOrSortAndRelIsoTypeType false => IsoOrSortAndRelIsoTypeType@{b a u v r}
    | IsoOrSortAndRelIsoForall false isoA isoB =>
        IsoOrSortForall (isoA:=iso_sym isoA) _ _ (fun a' a e => @iso_or_sort_sym' _ _ _ (isoB a a' (rel_iso_unsym e)))
    end.

Definition iso_or_sort_sym@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B} (iso : @IsoOrSort@{a b u v r} A B) : @IsoOrSort@{b a u v r} B A :=
    @iso_or_sort_sym'@{a b u v r} A B _ iso.

Definition iso_or_sort_sym'_sym'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R)
  : (if allow_relaxed return @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R -> SProp then fun iso => forall x : SProp, x -> x else fun iso => IsomorphismDefinitions.eq@{_|u} (iso_or_sort_sym'@{b a u v r} (iso_or_sort_sym'@{a b u v r} iso)) iso) iso.
Proof.
  induction iso; cbn in *;
    try match goal with |- context[if ?b then _ else _] => is_var b; destruct b end;
    try exact (fun _ x => x);
    cbn in *;
    try constructor;
    cbv [IsoOrSortForall].
  all:
    lazymatch goal with
    | [ |- context[iso_sym (iso_sym ?i)] ] =>
        lazymatch goal with
        | [ |- context[@rel_iso_unsym _ _ i] ] =>
          generalize (@rel_iso_unsym_unsym _ _ i);
          generalize (@rel_iso_unsym _ _ i); generalize (@rel_iso_unsym _ _ (iso_sym i))
        | _ => idtac
        end;
        generalize (iso_sym_sym@{_ _|a b u} i);
        generalize (iso_sym i)
    | _ => idtac
    end.
  all: intros.
  all: repeat match goal with H : eq _ ?x |- _ => is_var x; destruct H end.
  all: [ > constructor .. | ].
  { let f := fresh "f" in
    let g := fresh "g" in
    let H' := fresh "H'" in
    lazymatch goal with
    | [ H : forall a a' e, eq (iso_or_sort_sym' (IsoOrSort_iso (iso_or_sort_sym' (?i a a' e)))) (@?rhs a a' e) |- _ ] =>
        set (f := fun a a' e => iso_or_sort_sym'@{b a u v r} (IsoOrSort_iso (iso_or_sort_sym'@{a b u v r} (i a a' e)))) in *;
        set (g := rhs) in *;
        assert (H' : eq@{_|u} f g) by (do 3 (apply functional_extensionality_dep@{_ _|u u u}; intro); apply H)
        (* assert (H'' : eq (fun a a' e => f_equal (fun H => H a a' e) H') H) by reflexivity;
        destruct H'' *)
    end;
    lazymatch goal with
    | [ |- context G[{| rel_iso_sort := fun f' g' => forall a a' e, rel_iso_sort (iso_or_sort_sym' (IsoOrSort_iso (iso_or_sort_sym' (?i a a' _)))) (f' a) (g' a')
    ; IsoOrSort_iso := IsoOrSortAndRelIsoForall (iso_sym ?i') (fun b b' e' => IsoOrSort_iso (iso_or_sort_sym' (IsoOrSort_iso (iso_or_sort_sym' (?i b b' _)))))
     |}]] =>
        let G' := context G[{| rel_iso_sort := fun f' g' => forall a a' e, rel_iso_sort (f a a' e) (f' a) (g' a')
    ; IsoOrSort_iso := IsoOrSortAndRelIsoForall@{a b u v r} (iso_sym@{_ _|b a} i') (fun a a' e => IsoOrSort_iso (f a a' e)) |}] in
        change G';
        clearbody f;
        apply eq_sym@{_|u} in H';
        destruct H'; subst g
    end.
    reflexivity. }
Defined.

Definition iso_or_sort_sym_sym@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B} (iso : @IsoOrSort@{a b u v r} A B)
  : IsomorphismDefinitions.eq@{_|u} (iso_or_sort_sym@{b a u v r} (iso_or_sort_sym@{a b u v r} iso)) iso.
Proof. exact (@iso_or_sort_sym'_sym'@{a b u v r} false A B _ iso). Defined.

Fixpoint rel_iso_sort_sym'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R) : forall {x y}, (if allow_relaxed return Type@{u} then IDProp else R x y) -> (if allow_relaxed return @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R -> Type@{u} then fun _ => IDProp else fun iso => rel_iso_sort (iso_or_sort_sym' iso) y x) iso.
Proof.
  refine
    match iso as iso in @IsoOrSortAndRelIso allow_relaxed A B R return forall x y, (if allow_relaxed return Type@{u} then IDProp else R x y) -> (if allow_relaxed return @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R -> Type@{u} then fun _ => IDProp else fun iso => rel_iso_sort (iso_or_sort_sym' iso) y x) iso with
    | IsoOrSortAndRelIsoIso false i => fun x y r => wrap_sprop (rel_iso_sym (unwrap_sprop r))
    | IsoOrSortAndRelIsoIsoTypeSProp false i => fun x y r => wrap_sprop (rel_iso_sym (unwrap_sprop r))
    | IsoOrSortAndRelIsoIsoSPropType false i => fun x y r => wrap_sprop (rel_iso_sym (unwrap_sprop r))
    | IsoOrSortAndRelIsoIsoSPropSProp false i => fun x y r => wrap_sprop (rel_iso_sym (unwrap_sprop r))
    | IsoOrSortAndRelIsoPropProp false => fun x y => iso_sym@{_ _|a b}
    | IsoOrSortAndRelIsoSPropSProp false => fun x y => iso_sym@{_ _|a b}
    | IsoOrSortAndRelIsoTypeType false => fun x y => iso_sym@{_ _|a b}
    | IsoOrSortAndRelIsoForall allow_relaxed isoA isoB =>
        let recr := fun a a' e => @rel_iso_sort_sym' allow_relaxed _ _ _ (isoB a a' e) in
        (* IsoOrSortForall (isoA:=iso_sym isoA) _ _ (fun a' a e => @iso_or_sort_sym' _ _ _ (isoB a a' (rel_iso_unsym e))) *)
        _
    | IsoOrSortAndRelIsoIso true _
    | IsoOrSortAndRelIsoIsoTypeSProp true _
    | IsoOrSortAndRelIsoIsoSPropType true _
    | IsoOrSortAndRelIsoIsoSPropSProp true _
    | IsoOrSortAndRelIsoPropProp true
    | IsoOrSortAndRelIsoSPropSProp true
    | IsoOrSortAndRelIsoTypeType true
    | IsoOrSortAndRelIsoPropType
    | IsoOrSortAndRelIsoPropSProp
        => fun _ _ r => r
    end;
    cbn.
  { clearbody recr.
    clear rel_iso_sort_sym'.
    destruct allow_relaxed.
    { intros; auto. }
    cbn in *.
    intros; apply recr.
    auto. }
Defined.

Lemma rel_iso_sort_sym@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B} (iso : @IsoOrSort@{a b u v r} A B) {x y} (H : rel_iso_sort iso x y) : rel_iso_sort (iso_or_sort_sym iso) y x.
Proof. exact (@rel_iso_sort_sym'@{a b u v r} false A B _ iso x y H). Defined.

Fixpoint rel_iso_sort_unsym'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed A B R} (iso : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R) : forall {x y}, (if allow_relaxed return @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R -> Type@{u} then fun _ => IDProp else fun iso => rel_iso_sort (iso_or_sort_sym' iso) y x) iso -> if allow_relaxed return Type@{u} then IDProp else R x y.
Proof.
  refine
    match iso as iso in @IsoOrSortAndRelIso allow_relaxed A B R return forall x y, (if allow_relaxed return @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R -> Type@{u} then fun _ => IDProp else fun iso => rel_iso_sort (iso_or_sort_sym' iso) y x) iso -> if allow_relaxed return Type@{u} then IDProp else R x y with
    | IsoOrSortAndRelIsoIso false i => fun x y r => wrap_sprop (rel_iso_unsym (unwrap_sprop r))
    | IsoOrSortAndRelIsoIsoTypeSProp false i => fun x y r => wrap_sprop (rel_iso_unsym (unwrap_sprop r))
    | IsoOrSortAndRelIsoIsoSPropType false i => fun x y r => wrap_sprop (rel_iso_unsym (unwrap_sprop r))
    | IsoOrSortAndRelIsoIsoSPropSProp false i => fun x y r => wrap_sprop (rel_iso_unsym (unwrap_sprop r))
    | IsoOrSortAndRelIsoPropProp false => fun x y => iso_sym@{_ _|a b}
    | IsoOrSortAndRelIsoSPropSProp false => fun x y => iso_sym@{_ _|a b}
    | IsoOrSortAndRelIsoTypeType false => fun x y => iso_sym@{_ _|a b}
    | IsoOrSortAndRelIsoForall allow_relaxed isoA isoB =>
        let recr := fun a a' e => @rel_iso_sort_unsym' allow_relaxed _ _ _ (isoB a a' e) in
        (* IsoOrSortForall (isoA:=iso_sym isoA) _ _ (fun a' a e => @iso_or_sort_sym' _ _ _ (isoB a a' (rel_iso_unsym e))) *)
        _
    | IsoOrSortAndRelIsoIso true _
    | IsoOrSortAndRelIsoIsoTypeSProp true _
    | IsoOrSortAndRelIsoIsoSPropType true _
    | IsoOrSortAndRelIsoIsoSPropSProp true _
    | IsoOrSortAndRelIsoPropProp true
    | IsoOrSortAndRelIsoSPropSProp true
    | IsoOrSortAndRelIsoTypeType true
    | IsoOrSortAndRelIsoPropType
    | IsoOrSortAndRelIsoPropSProp
        => fun _ _ r => r
    end;
    cbn.
  { clearbody recr.
    clear rel_iso_sort_unsym'.
    destruct allow_relaxed.
    { intros; auto. }
    cbn in *.
    intros ?? H' a a' e; apply recr.
    specialize (H' a' a (rel_iso_sym e)).
    apply H'. }
Defined.

Lemma rel_iso_sort_unsym@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B} (iso : @IsoOrSort@{a b u v r} A B) {x y} (H : rel_iso_sort (iso_or_sort_sym iso) y x) : rel_iso_sort iso x y.
Proof. exact (@rel_iso_sort_unsym'@{a b u v r} false A B _ iso x y H). Defined.

(* Definition rel_iso_sort_unsym'_unsym'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {allow_relaxed A B R} {iso : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R} {x y} H
: eq@{_|u} (@rel_iso_sort_unsym' allow_relaxed _ _ _ _ _ _ (@rel_iso_sort_sym' allow_relaxed A B R iso x y H)) (match iso_or_sort_unsym_sym iso in eq _ i return rel_iso_sort i x y with eq_refl => H end).
Proof. reflexivity. Qed.

Definition rel_iso_sort_unsym_unsym@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B} {iso : @IsoOrSort@{a b u v r} A B} {x y} (H : rel_iso_sort (iso_or_sort_sym (iso_or_sort_sym iso)) y x)
: eq@{_|u} (rel_iso_sort_unsym (rel_iso_sort_unsym H)) (match iso_or_sort_sym_sym iso in eq _ i return rel_iso_sort i x y with eq_refl => H end).
Proof. reflexivity. Qed.

Definition rel_iso_sort_unsym_sym@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  {A B} {iso : @IsoOrSort@{a b u v r} A B} {x y} (H : rel_iso_sort (iso_or_sort_sym (iso_or_sort_sym iso)) y x)
: eq@{_|u} (rel_iso_sort_unsym (rel_iso_sort_sym H)) (match iso_or_sort_sym_sym iso in eq _ i return rel_iso_sort i x y with eq_refl => H end).
Proof. reflexivity. Qed. *)

Definition iso_trans@{s s' s''|u u' u''|} {A B C} (iso : Iso@{s s'|u u'} A B) (iso' : Iso@{s' s''|u' u''} B C) : Iso@{s s''|u u''} A C
  := {| to x := iso'.(to) (iso.(to) x);
        from x := iso.(from) (iso'.(from) x);
        to_from x := eq_trans (f_equal iso'.(to) (iso.(to_from) (iso'.(from) x))) (iso'.(to_from) x);
        from_to x := eq_trans (f_equal iso.(from) (iso'.(from_to) (iso.(to) x))) (iso.(from_to) x) |}.

(* Definition rel_iso_trans@{s0 s1 s2|u0 u1 u2|} {A B C} {i : Iso@{s0 s1|u0 u1} A B} {j : Iso@{s1 s2|u1 u2} B C} {x y z} (H1 : rel_iso i x y) (H2 : rel_iso j y z) :
  rel_iso ( *)

Fixpoint iterate1@{s|u|} {A : Type@{s|u}} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S n => @iterate1 A f n (f x)
  end.
Fixpoint iterate1D2@{s1 s2 s3|u1 u2 u3|} {A : Type@{s1|u1}} {B : Type@{s2|u2}} {C : A -> B -> Type@{s3|u3}} (f1 : A -> A) (f2 : B -> B) (f3 : forall a b, C a b -> C (f1 a) (f2 b)) (n : nat) (a : A) (b : B) (c : C a b) : C (iterate1 f1 n a) (iterate1 f2 n b) :=
  match n return C (iterate1 f1 n a) (iterate1 f2 n b) with
  | O => c
  | S n => @iterate1D2 A B C f1 f2 f3 n (f1 a) (f2 b) (f3 a b c)
  end.

Import Ltac2.Ltac2.
Import IsomorphismChecker.Ltac2Utils.

#[local] Ltac2 solve_iso_of_rel_iso_iso_sort () :=
  let h := Fresh.in_goal @h in
  intro $h; let hv := Control.hyp h in
  destruct $hv as [h];
  (unshelve eexists; hnf in $h;
  destruct $hv; cbv [iso_Sort iso_Prop_SProp to from])
  > [ first [ exact (fun x => x) | exact sinhabits ]
    | first [ exact (fun x => x) | exact sinhabitant ]
    | cbv beta; constructor
    | cbv beta; first [ constructor | intro; apply seq_of_peq_t, proof_irrelevance ] ].

#[local] Ltac2 solve_iso_of_rel_iso_iso_sort_careful () :=
  let h := Fresh.in_goal @h in
  intro $h; let hv := Control.hyp h in
  destruct $hv as [h];
  hnf in $h;
  (unshelve eexists)
  > [ refine '(match $hv in (eq _ t2) return _ -> t2 with eq_refl => _ end); exact (fun x => x)
  | refine '(match $hv in (eq _ t2) return t2 -> _ with eq_refl => _ end); exact (fun x => x)
  | | ];
  cbn; try (let x := Fresh.in_goal @x in intro $x; apply IsoEq.seq_p_of_t; revert $x);
  cbv [iso_Sort to from] in *;
  try (destruct $hv; constructor).

Definition iso_of_rel_iso_iso_sort@{s|u v v'|u < v, u < v'} {t1 t2}
  : rel_iso iso_Sort@{s|u v v'} t1 t2 -> Iso t1 t2.
Proof. solve_iso_of_rel_iso_iso_sort (). Defined.

Definition iso_of_rel_iso_iso_sort_PP_TT@{s|u v v' u' u''|u < v, u < v'} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Prop|u v v'} t1 t2 -> Iso@{Type Type|u' u''} t1 t2.
Proof. solve_iso_of_rel_iso_iso_sort (). Defined.
Definition iso_of_rel_iso_iso_sort_PP_TP@{s|u v v' u' u''|u < v, u < v'} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Prop|u v v'} t1 t2 -> Iso@{Type Prop|u' u''} t1 t2.
Proof. solve_iso_of_rel_iso_iso_sort (). Defined.
Definition iso_of_rel_iso_iso_sort_PP_PT@{s|u v v' u' u''|u < v, u < v'} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Prop|u v v'} t1 t2 -> Iso@{Prop Type|u' u''} t1 t2.
Proof. solve_iso_of_rel_iso_iso_sort (). Defined.
Definition iso_of_rel_iso_iso_sort_PP_PP@{s|u v v' u' u''|u < v, u < v'} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Prop|u v v'} t1 t2 -> Iso@{Prop Prop|u' u''} t1 t2.
Proof. solve_iso_of_rel_iso_iso_sort (). Defined.

Definition iso_of_rel_iso_iso_sort_TP_TT@{s|u v v' u' u''|u < v, u < v', u <= u'} {t1 : Type@{u}} {t2 : Prop}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Type Type|u' u''} t1 t2
  := iso_of_rel_iso_iso_sort.
Definition iso_of_rel_iso_iso_sort_PT_TT@{s|u v v' u' u''|u < v, u < v', u <= u''} {t1 : Prop} {t2 : Type@{u}}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Type Type|u' u''} t1 t2
  := iso_of_rel_iso_iso_sort.
Definition iso_of_rel_iso_iso_sort_TP_TP@{s|u v v' u' u''|u < v, u < v', u <= u', u <= u''} {t1 : Type@{u}} {t2 : Prop}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Type Prop|u' u''} t1 t2.
Proof.
  intros [h].
  unshelve eexists; hnf in h.
  1: refine '(match h in (eq _ t2) return t1 -> t2 with eq_refl => _ end).
  2: refine '(match h in (eq _ t2) return t2 -> t1 with eq_refl => _ end).
  1: exact (fun x => x).
  1: exact (fun x => x).
  all: cbn; try (intro x; apply IsoEq.seq_p_of_t; revert x).
  all: destruct h.
  all: constructor.
Defined.
Definition iso_of_rel_iso_iso_sort_PT_PT@{s|u v v' u' u''|u < v, u < v', u <= u', u <= u''} {t1 : Prop} {t2 : Type@{u}}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Prop Type|u' u''} t1 t2.
Proof.
  intros [h].
  unshelve eexists; hnf in h.
  1: refine '(match h in (eq _ t2) return t1 -> t2 with eq_refl => _ end).
  2: refine '(match h in (eq _ t2) return t2 -> t1 with eq_refl => _ end).
  1: exact (fun x => x).
  1: exact (fun x => x).
  all: cbn; try (intro x; apply IsoEq.seq_p_of_t; revert x).
  all: destruct h.
  all: constructor.
Defined.
Definition iso_of_rel_iso_iso_sort_TPP_PP@{s|u v v' u' u''|u < v, u < v', u <= u', u <= u''} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Prop Prop|u' u''} t1 t2.
Proof.
  intros [h].
  unshelve eexists; hnf in h.
  1: refine '(match h in (eq _ t2) return t1 -> t2 with eq_refl => _ end).
  2: refine '(match h in (eq _ t2) return t2 -> t1 with eq_refl => _ end).
  1: exact (fun x => x).
  1: exact (fun x => x).
  all: cbn; try (intro x; apply IsoEq.seq_p_of_t; revert x).
  all: destruct h.
  all: constructor.
Defined.
Definition iso_of_rel_iso_iso_sort_TPP_TP@{s|u v v' u' u''|u < v, u < v', u <= u', u <= u''} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Type Prop|u' u''} t1 t2.
Proof.
  intros [h].
  unshelve eexists; hnf in h.
  1: refine '(match h in (eq _ t2) return t1 -> t2 with eq_refl => _ end).
  2: refine '(match h in (eq _ t2) return t2 -> t1 with eq_refl => _ end).
  1: exact (fun x => x).
  1: exact (fun x => x).
  all: cbn; try (intro x; apply IsoEq.seq_p_of_t; revert x).
  all: destruct h.
  all: constructor.
Defined.
Definition iso_of_rel_iso_iso_sort_TPP_PT@{s|u v v' u' u''|u < v, u < v', u <= u', u <= u''} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Prop Type|u' u''} t1 t2.
Proof.
  intros [h].
  unshelve eexists; hnf in h.
  1: refine '(match h in (eq _ t2) return t1 -> t2 with eq_refl => _ end).
  2: refine '(match h in (eq _ t2) return t2 -> t1 with eq_refl => _ end).
  1: exact (fun x => x).
  1: exact (fun x => x).
  all: cbn; try (intro x; apply IsoEq.seq_p_of_t; revert x).
  all: destruct h.
  all: constructor.
Defined.
Definition iso_of_rel_iso_iso_sort_TPP_TT@{s|u v v' u' u''|u < v, u < v', u <= u', u <= u''} {t1 t2 : Prop}
  : rel_iso iso_Sort@{Type|u v v'} t1 t2 -> Iso@{Type Type|u' u''} t1 t2.
Proof.
  intros [h].
  unshelve eexists; hnf in h.
  1: refine '(match h in (eq _ t2) return t1 -> t2 with eq_refl => _ end).
  2: refine '(match h in (eq _ t2) return t2 -> t1 with eq_refl => _ end).
  1: exact (fun x => x).
  1: exact (fun x => x).
  all: cbn; try (intro x; apply IsoEq.seq_p_of_t; revert x).
  all: destruct h.
  all: constructor.
Defined.

Definition iso_of_rel_iso_iso_sort_PropSProp_T@{u1 u2 u} {t1 t2}
  : rel_iso iso_Prop_SProp@{u1 u2} t1 t2 -> Iso@{Type SProp|u Set} t1 t2.
Proof. solve_iso_of_rel_iso_iso_sort (). Defined.
Definition iso_of_rel_iso_iso_sort_PropSProp_P@{u1 u2} {t1 t2}
  : rel_iso iso_Prop_SProp@{u1 u2} t1 t2 -> Iso@{Prop SProp|Set Set} t1 t2.
Proof. intro h; apply relax_Iso_Ts_Ps, iso_of_rel_iso_iso_sort_PropSProp_T, h. Defined.

Definition rel_iso_sort_of_rel_iso_PP_PP@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov'} {allow_relaxed : bool}
  : forall {a b : Prop}, rel_iso iso_Sort@{Prop|ou ov ov'} a b -> rel_iso_sort@{a b u v r} (@IsoPropProp@{a b u v r} allow_relaxed) a b
  := @iso_of_rel_iso_iso_sort_PP_PP.
Definition rel_iso_sort_of_rel_iso_PP_TT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov'} {allow_relaxed : bool}
  : forall {a b : Prop}, rel_iso iso_Sort@{Prop|ou ov ov'} a b -> rel_iso_sort@{a b u v r} (@IsoTypeType@{a b u v r} allow_relaxed) a b
  := @iso_of_rel_iso_iso_sort_PP_TT.
Definition rel_iso_sort_of_rel_iso_TPP_PP@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov',ou <= a, ou <= b} {allow_relaxed : bool}
  : forall {a b : Prop}, rel_iso iso_Sort@{Type|ou ov ov'} a b -> rel_iso_sort@{a b u v r} (@IsoPropProp@{a b u v r} allow_relaxed) a b
  := @iso_of_rel_iso_iso_sort_TPP_PP.
Definition rel_iso_sort_of_rel_iso_TPP_TT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov',ou <= v} {allow_relaxed : bool}
  : forall {a b : Prop}, rel_iso iso_Sort@{Type|ou ov ov'} a b -> rel_iso_sort@{a b u v r} (@IsoTypeType@{a b u v r} allow_relaxed) a b
  := @iso_of_rel_iso_iso_sort_TPP_TT.
Definition rel_iso_sort_of_rel_iso_TP_TT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov',ou <= v} {allow_relaxed : bool}
  : forall {a : Type@{ou}} {b : Prop}, rel_iso iso_Sort@{Type|ou ov ov'} a b -> rel_iso_sort@{a b u v r} (@IsoTypeType@{a b u v r} allow_relaxed) a b
  := @iso_of_rel_iso_iso_sort_TP_TT.
Definition rel_iso_sort_of_rel_iso_PT_TT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov',ou <= v} {allow_relaxed : bool}
  : forall {a : Prop} {b : Type@{ou}}, rel_iso iso_Sort@{Type|ou ov ov'} a b -> rel_iso_sort@{a b u v r} (@IsoTypeType@{a b u v r} allow_relaxed) a b
  := @iso_of_rel_iso_iso_sort_PT_TT.

Definition rel_iso_sort_of_rel_iso_PP_PT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov'}
  : forall {a b : Prop}, rel_iso iso_Sort@{Prop|ou ov ov'} a b -> rel_iso_sort@{a b u v r} IsoPropType@{a b u v r} a b
  := @iso_of_rel_iso_iso_sort_PP_PT.
Definition rel_iso_sort_of_rel_iso_TPP_PT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov',ou <= a, ou <= b,ou<=v}
  : forall {a b : Prop}, rel_iso iso_Sort@{Type|ou ov ov'} a b -> rel_iso_sort@{a b u v r} IsoPropType@{a b u v r} a b
  := @iso_of_rel_iso_iso_sort_TPP_PT.
Definition rel_iso_sort_of_rel_iso_TP_PT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov',ou <= v}
  : forall {a b : Prop}, rel_iso iso_Sort@{Type|ou ov ov'} a b -> rel_iso_sort@{a b u v r} IsoPropType@{a b u v r} a b
  := @iso_of_rel_iso_iso_sort_TPP_PT.
Definition rel_iso_sort_of_rel_iso_PT_PT@{a b u v r ou ov ov'|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u,Set < ov,Set < ov',ou < ov,ou < ov',ou <= v}
  : forall {a : Prop} {b : Type@{ou}}, rel_iso iso_Sort@{Type|ou ov ov'} a b -> rel_iso_sort@{a b u v r} IsoPropType@{a b u v r} a b
  := @iso_of_rel_iso_iso_sort_PT_PT.

Definition iso_rel_iso_Sort_refl@{s|u v v'|u < v, u < v'} {x}
  : rel_iso iso_Sort@{s|u v v'} x x := eq_refl.

(** Dealing with propositional extensionality *)
Definition propositional_extensionality_Logic_eq : Prop :=
  forall (P Q : Prop), (P <-> Q) -> Logic.eq P Q.

(** Dealing with predicate extensionality *)
Definition predicate_extensionality_Logic_eq@{s|u|} : Prop :=
  forall (A : Type@{s|u}) (P Q : A -> Prop), (forall x : A, P x <-> Q x) -> Logic.eq P Q.

Existing Class propositional_extensionality_Logic_eq.
Existing Class predicate_extensionality_Logic_eq.

Definition rel_iso_iso_sort_of_iso_TT_PP_pe@{s|u v v' u' u''|u < v, u < v'} {pe : propositional_extensionality_Logic_eq} {t1 t2 : Prop}
  : Iso@{Type Type|u' u''} t1 t2 -> rel_iso iso_Sort@{Prop|u v v'} t1 t2.
Proof. intro i; constructor; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pe. split; apply i. Defined.
Definition rel_iso_iso_sort_of_iso_TP_PP_pe@{s|u v v' u' u''|u < v, u < v'} {pe : propositional_extensionality_Logic_eq} {t1 t2 : Prop}
  : Iso@{Type Prop|u' u''} t1 t2 -> rel_iso iso_Sort@{Prop|u v v'} t1 t2.
Proof. intro i; constructor; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pe. split; apply i. Defined.
Definition rel_iso_iso_sort_of_iso_PT_PP_pe@{s|u v v' u' u''|u < v, u < v'} {pe : propositional_extensionality_Logic_eq} {t1 t2 : Prop}
  : Iso@{Prop Type|u' u''} t1 t2 -> rel_iso iso_Sort@{Prop|u v v'} t1 t2.
Proof. intro i; constructor; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pe. split; apply i. Defined.
Definition rel_iso_iso_sort_of_iso_PP_PP_pe@{s|u v v' u' u''|u < v, u < v'} {pe : propositional_extensionality_Logic_eq} {t1 t2 : Prop}
  : Iso@{Prop Prop|u' u''} t1 t2 -> rel_iso iso_Sort@{Prop|u v v'} t1 t2.
Proof. intro i; constructor; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pe. split; apply i. Defined.

Definition iso_inhabited_p@{} {A : SProp} : Iso@{SProp Prop|Set Set} A (inhabited@{SProp|Set} A) :=
  {| to := inhabits@{SProp|Set} ; from := inhabitant ; to_from x := match x with inhabits _ => eq_refl end ; from_to x := eq_refl |}.

(* Definition iso_inhabited@{s|u|} {A : Type@{s|u}} {B : SProp} : Iso@{s SProp|u Set} A B -> Iso@{s Prop|u Set} A (inhabited@{SProp|Set} B).
Proof. *)
Definition rel_iso_iso_sort_of_iso_Ps_Ps_pe@{u u'} {pe : propositional_extensionality_Logic_eq} {t1 t2}
  : Iso@{Prop SProp|Set Set} t1 t2 -> rel_iso iso_Prop_SProp@{u u'} t1 t2.
Proof.
  intro i; constructor; hnf; cbv [iso_Prop_SProp to from].
  assert (h : eq (SInhabited t1) (SInhabited (inhabited t2))).
  2: { eapply eq_trans > [ apply h | ]. apply seq_of_eq, eq_SInhabited_inhabited. }
  apply f_equal. apply IsoEq.seq_of_eq. apply pe.
  pose (iso_trans i iso_inhabited_p) as i'.
  split; apply i'.
Defined.

Definition rel_iso_iso_sort_of_iso_Ts_Ps_pe@{u u' u''} {pe : propositional_extensionality_Logic_eq} {t1 : Prop} {t2}
  : Iso@{Type SProp|u'' Set} t1 t2 -> rel_iso iso_Prop_SProp@{u u'} t1 t2.
Proof. intro i; apply rel_iso_iso_sort_of_iso_Ps_Ps_pe, relax_Iso_Ts_Ps, i. Defined.

(*
Definition rel_iso_iso_sort_of_iso_TT_PP_pre@{sp s|up u v v' u' u''|u < v, u < v'} {pre : predicate_extensionality_Logic_eq@{sp|up}} {A : Type@{s|up}} {t1 t2 : A -> Prop} {t1' t2' : Prop} {x y : A}
  : Iso@{Type Type|u' u''} (t1 x) (t2 y) -> rel_iso iso_Sort@{Prop|u v v'} (t1 x) (t2 y).
Proof. intro i; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pre. split; apply i. Defined.
Definition rel_iso_iso_sort_of_iso_TP_PP_pre@{sp s|up u v v' u' u''|u < v, u < v'} {pre : predicate_extensionality_Logic_eq@{sp|up}} {A : Type@{s|up}} {t1 t2 : A -> Prop} {t1' t2' : Prop}
  : Iso@{Type Prop|u' u''} (t1 x) (t2 y) -> rel_iso iso_Sort@{Prop|u v v'} (t1 x) (t2 y).
Proof. intro i; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pre. split; apply i. Defined.
Definition rel_iso_iso_sort_of_iso_PT_PP_pre@{sp s|up u v v' u' u''|u < v, u < v'} {pre : predicate_extensionality_Logic_eq@{sp|up}} {A : Type@{s|up}} {t1 t2 : A -> Prop} {t1' t2' : Prop}
  : Iso@{Prop Type|u' u''} (t1 x) (t2 y) -> rel_iso iso_Sort@{Prop|u v v'} (t1 x) (t2 y).
Proof. intro i; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pre. split; apply i. Defined.
Definition rel_iso_iso_sort_of_iso_PP_PP_pre@{sp s|up u v v' u' u''|u < v, u < v'} {pre : predicate_extensionality_Logic_eq@{sp|up}} {A : Type@{s|up}} {t1 t2 : A -> Prop} {t1' t2' : Prop}
  : Iso@{Prop Prop|u' u''} (t1 x) (t2 y) -> rel_iso iso_Sort@{Prop|u v v'} (t1 x) (t2 y).
Proof. intro i; hnf; cbv [iso_Sort to from]. apply IsoEq.seq_of_eq. apply pre. split; apply i. Defined. *)
