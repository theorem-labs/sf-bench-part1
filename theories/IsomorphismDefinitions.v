From LeanImport Require Import Lean.
#[local] Close Scope lean_scope.
#[export]
Set Universe Polymorphism.
#[export]
Set Polymorphic Inductive Cumulativity.
Record WrapSProp (A : SProp) : Set := wrap_sprop { unwrap_sprop : A }.
#[global] Arguments wrap_sprop {A} _.
#[global] Arguments unwrap_sprop {A} _.
#[local] Set Primitive Projections.
#[local] Set Warnings "-notation-overridden".
Inductive eq@{s|u|} {α:Type@{s|u}} (a:α) : α -> SProp
  := eq_refl : eq a a.
(* Notation "x = y" := (eq x y) : lean_scope. *)
#[local] Notation "x = y" := (eq x y) : type_scope.
#[export]
Hint Resolve eq_refl: core.
Arguments eq {α} a _.
Arguments eq_refl {α a} , [α] a.

Arguments eq_ind [α] a P _ y _ : rename.
Arguments eq_rec [α] a P _ y _ : rename.
Arguments eq_rect [α] a P _ y _ : rename.

Inductive sFalse : SProp := .
Definition not@{u|s|} (A : Type@{u|s}) := A -> sFalse.
#[local] Notation "x <> y" := (not@{SProp|Set} (eq x y)) : type_scope.

From Stdlib Require Import CMorphisms.
#[export]
Set Implicit Arguments.
Record Iso@{s s'|u u'|} (A : Type@{s|u}) (B : Type@{s'|u'}) := {
    to :> A -> B;
    from : B -> A;
    to_from : forall x, to (from x) = x;
    from_to : forall x, from (to x) = x;
}.

(* Record to work around COQBUG(https://github.com/rocq-prover/rocq/issues/21496) *)
#[export] Set Warnings "-ambiguous-paths,-uniform-inheritance".
Record > rel_iso@{s s'|u u'|} {A B} (i : Iso@{s s'|u u'} A B) (x : A) (y : B) : SProp := { proj_rel_iso :> i.(to) x = y }.
#[export] Set Warnings "uniform-inheritance".
#[global] Arguments proj_rel_iso _ _ _ _ _ !_ / .
#[global] Arguments Build_rel_iso & {_ _ _ _ _}.

Inductive IsoOrSortAndRelIso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} : forall (allow_relaxed : bool) (A : Type@{a}) (B : Type@{b}), (A -> B -> Type@{r}) -> Type@{u} :=
| IsoOrSortAndRelIsoIso {allow_relaxed : bool} {A : Type@{a}} {B : Type@{b}} (i : Iso@{Type Type|a b} A B) : @IsoOrSortAndRelIso allow_relaxed A B (fun a b => WrapSProp (rel_iso i a b))
| IsoOrSortAndRelIsoIsoTypeSProp {allow_relaxed : bool} {A : Type@{a}} {B : SProp} (i : Iso@{Type SProp|a b} A B) : @IsoOrSortAndRelIso allow_relaxed A (WrapSProp B) (fun a b => WrapSProp (rel_iso i a (unwrap_sprop b)))
| IsoOrSortAndRelIsoIsoSPropType {allow_relaxed : bool} {A : SProp} {B : Type@{b}} (i : Iso@{SProp Type|a b} A B) : @IsoOrSortAndRelIso allow_relaxed (WrapSProp A) B (fun a b => WrapSProp (rel_iso i (unwrap_sprop a) b))
| IsoOrSortAndRelIsoIsoSPropSProp {allow_relaxed : bool} {A : SProp} {B : SProp} (i : Iso@{SProp SProp|a b} A B) : @IsoOrSortAndRelIso allow_relaxed (WrapSProp A) (WrapSProp B) (fun a b => WrapSProp (rel_iso i (unwrap_sprop a) (unwrap_sprop b)))
| IsoOrSortAndRelIsoPropProp {allow_relaxed : bool} : @IsoOrSortAndRelIso allow_relaxed Prop Prop Iso@{Prop Prop|a b}
| IsoOrSortAndRelIsoSPropSProp {allow_relaxed : bool} : @IsoOrSortAndRelIso allow_relaxed SProp SProp Iso@{SProp SProp|a b}
| IsoOrSortAndRelIsoTypeType {allow_relaxed : bool} : @IsoOrSortAndRelIso allow_relaxed Type@{v} Type@{v} Iso@{Type Type|v v}
(* Having to : Prop -> Type allows us to actually define to, and hence the rel_iso version.  This is pretty kldugy, but so is allowing isos between Coq-side Prop and Lean-side Type in general *)
| IsoOrSortAndRelIsoPropType : @IsoOrSortAndRelIso true Prop Type@{v} Iso@{Prop Type|v v}
| IsoOrSortAndRelIsoPropSProp : @IsoOrSortAndRelIso true Prop SProp Iso@{Prop SProp|a b}
(* N.B. Without univalence, functions in general do not respect Iso, so we need equality on the input *)
(* N.B. We make S take the rel_iso as an argument even though it ought not be used, so that we can define IsoOrSortForall easily *)
| IsoOrSortAndRelIsoForall {allow_relaxed : bool} {A : Type@{a}} {A' : Type@{b}} {B : A -> Type@{a}} {B' : A' -> Type@{b}} (isoA : Iso@{Type Type|a b} A A') {S} : (forall a a' (e : rel_iso isoA a a'), @IsoOrSortAndRelIso allow_relaxed (B a) (B' a') (S a a' e)) -> @IsoOrSortAndRelIso allow_relaxed (forall a, B a) (forall a', B' a') (fun f g => forall a a' (e : rel_iso isoA a a'), S a a' e (f a) (g a'))
.
Global Arguments IsoOrSortAndRelIsoIso {allow_relaxed A B} i, allow_relaxed [A B] i, allow_relaxed A B i.
Global Arguments IsoOrSortAndRelIsoIsoTypeSProp {allow_relaxed A B} i, allow_relaxed [A B] i, allow_relaxed A B i.
Global Arguments IsoOrSortAndRelIsoIsoSPropType {allow_relaxed A B} i, allow_relaxed [A B] i, allow_relaxed A B i.
Global Arguments IsoOrSortAndRelIsoIsoSPropSProp {allow_relaxed A B} i, allow_relaxed [A B] i, allow_relaxed A B i.
Global Arguments IsoOrSortAndRelIsoPropProp {allow_relaxed}, allow_relaxed.
Global Arguments IsoOrSortAndRelIsoSPropSProp {allow_relaxed}, allow_relaxed.
Global Arguments IsoOrSortAndRelIsoTypeType {allow_relaxed}, allow_relaxed.
Global Arguments IsoOrSortAndRelIsoForall {allow_relaxed A A' B B'} isoA {S} _, allow_relaxed [A A' B B'] isoA {S} _, allow_relaxed A A' B B' isoA S _.

Record > IsoOrSort'@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} (allow_relaxed : bool) (A : Type@{a}) (B : Type@{b}) : Type@{u} := Build_IsoOrSort {
   rel_iso_sort : A -> B -> Type@{r};
   IsoOrSort_iso :> @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B rel_iso_sort;
}.

Notation IsoOrSort := (@IsoOrSort' false).
Notation IsoOrSortRelaxed := (@IsoOrSort' true).

Arguments rel_iso_sort {allow_relaxed A B} i a b.
Arguments IsoOrSort_iso {allow_relaxed A B} i.
Arguments Build_IsoOrSort {allow_relaxed A B _} _.

Fixpoint RelaxIsoOrSortAndRelIso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B R} (i : @IsoOrSortAndRelIso@{a b u v r} allow_relaxed A B R) : @IsoOrSortAndRelIso@{a b u v r} true A B R :=
  match i in @IsoOrSortAndRelIso allow_relaxed A B R return @IsoOrSortAndRelIso@{a b u v r} true A B R with
  | IsoOrSortAndRelIsoIso i => IsoOrSortAndRelIsoIso@{a b u v r} i
  | IsoOrSortAndRelIsoIsoTypeSProp i => IsoOrSortAndRelIsoIsoTypeSProp@{a b u v r} i
  | IsoOrSortAndRelIsoIsoSPropType i => IsoOrSortAndRelIsoIsoSPropType@{a b u v r} i
  | IsoOrSortAndRelIsoIsoSPropSProp i => IsoOrSortAndRelIsoIsoSPropSProp@{a b u v r} i
  | IsoOrSortAndRelIsoPropProp => IsoOrSortAndRelIsoPropProp@{a b u v r}
  | IsoOrSortAndRelIsoSPropSProp => IsoOrSortAndRelIsoSPropSProp@{a b u v r}
  | IsoOrSortAndRelIsoTypeType => IsoOrSortAndRelIsoTypeType@{a b u v r}
  | IsoOrSortAndRelIsoPropType => IsoOrSortAndRelIsoPropType@{a b u v r}
  | IsoOrSortAndRelIsoPropSProp => IsoOrSortAndRelIsoPropSProp@{a b u v r}
  | IsoOrSortAndRelIsoForall isoA isoB => IsoOrSortAndRelIsoForall@{a b u v r} isoA (fun a a' r => RelaxIsoOrSortAndRelIso (isoB _ _ r))
  end.

Definition RelaxIsoOrSort@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} (i : @IsoOrSort'@{a b u v r} allow_relaxed A B) : @IsoOrSortRelaxed@{a b u v r} A B := RelaxIsoOrSortAndRelIso i.
Definition Relax'IsoOrSort@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} (i : @IsoOrSort@{a b u v r} A B) : @IsoOrSort'@{a b u v r} allow_relaxed A B :=
  if allow_relaxed return @IsoOrSort'@{a b u v r} allow_relaxed A B then RelaxIsoOrSortAndRelIso i else i.

Definition IsoIso@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} i
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoIso@{a b u v r} allow_relaxed A B i).
Definition IsoIsoTypeSProp@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} i
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoIsoTypeSProp@{a b u v r} allow_relaxed A B i).
Definition IsoIsoSPropType@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} i
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoIsoSPropType@{a b u v r} allow_relaxed A B i).
Definition IsoIsoSPropSProp@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed A B} i
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoIsoSPropSProp@{a b u v r} allow_relaxed A B i).
Definition IsoPropProp@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed}
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoPropProp@{a b u v r} allow_relaxed).
Definition IsoSPropSProp@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed}
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoSPropSProp@{a b u v r} allow_relaxed).
Definition IsoTypeType@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u} {allow_relaxed}
  := Build_IsoOrSort@{a b u v r} (@IsoOrSortAndRelIsoTypeType@{a b u v r} allow_relaxed).
Definition IsoPropType@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  := Build_IsoOrSort@{a b u v r} IsoOrSortAndRelIsoPropType@{a b u v r}.
Definition IsoPropSProp@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  := Build_IsoOrSort@{a b u v r} IsoOrSortAndRelIsoPropSProp@{a b u v r}.
(* Definition IsoTypeProp@{a b u v r|Set < a, Set < b, v < a, v < b, a <= r, b <= r, r < u}
  := Build_IsoOrSortRelaxed@{a b u v r} IsoOrSortRelaxedAndRelIsoTypeProp@{a b u v r}. *)

(*
Definition rel_iso_sort@{u v v'|v < u, v' < u} {A B} (i : IsoOrSort@{u v v'} A B) : A -> B -> Type@{max(v,v')} :=
  match i in IsoOrSort A B return A -> B -> Type@{max(v,v')} with
  | IsoOrSortAndRelIsoIso i => fun a b => WrapSProp (rel_iso i a b)
  | IsoOrSortAndRelIsoPropProp => Iso@{Prop Prop|v v'}
  (* | IsoPropSProp => Iso@{Prop SProp|v v'} *)
  (* | IsoPropType => Iso@{Prop Type|v v'} *)
  (* | IsoSPropProp => Iso@{SProp Prop|v v'} *)
  | IsoOrSortAndRelIsoSPropSProp => Iso@{SProp SProp|v v'}
  (* | IsoSPropType => Iso@{SProp Type|v v'} *)
  (* | IsoTypeProp => Iso@{Type Prop|v v'} *)
  (* | IsoTypeSProp => Iso@{Type SProp|v v'} *)
  | IsoOrSortAndRelIsoTypeType => Iso@{Type Type|v v}
  end. *)

Existing Class Iso.
Existing Class rel_iso.
Existing Class IsoOrSort'.
Existing Class rel_iso_sort.
(* Existing Class rel_iso_sort. *)

(* Record IsoSProp (A : Prop) (B : SProp) := { to' : A -> B ; from' : B -> A }.
Notation iff A B := (and (A -> B) (B -> A)) (only parsing). *)
