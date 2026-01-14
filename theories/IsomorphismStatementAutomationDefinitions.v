From Coq Require Import NArith.
From Coq Require String Ascii.
From Ltac2 Require Import Ltac2.
Import Ltac2.Bool.BoolNotations Ltac2.Printf.
From Stdlib Require List.
Set Warnings "+not-unit".
From IsomorphismChecker Require Import IsomorphismDefinitions Ltac2Utils EqualityLemmas.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Module HList.
  Inductive hlist@{u} :=
  | nil
  | const {A : Type@{u}} (hd : A) (tl : hlist)
  | consp {A : Prop} (hd : A) (tl : hlist)
  | conss {A : SProp} (hd : A) (tl : hlist).

  Ltac2 precons (c : constr) :=
    let a := Constr.type c in
    let s := Constr.type a in
    lazy_match! s with
    | Prop => preterm:(@consp _ $c)
    | SProp => preterm:(@conss _ $c)
    | _ => preterm:(@const _ $c)
    end.

  Ltac2 cons (c : constr) := let cons_c := precons c in '($preterm:cons_c).

  Ltac2 rec pre_of_list (l : constr list) :=
    match l with
    | [] => preterm:(nil)
    | c :: l => let cons_c := precons c in let tl := pre_of_list l in preterm:($preterm:cons_c $preterm:tl)
    end.
  Ltac2 of_list (l : constr list) := let of_list_l := pre_of_list l in '($preterm:of_list_l).

  Ltac2 rec to_list (h : constr) :=
    lazy_match! h with
    | nil => []
    | const ?hd ?tl => hd :: to_list tl
    | consp ?hd ?tl => hd :: to_list tl
    | conss ?hd ?tl => hd :: to_list tl
    end.

  Notation unsafe_cons hd tl := (ltac2:(let hd := Constr.pretype hd in let tl := Constr.pretype tl in let cons_hd := cons hd in Control.refine (fun () => '($cons_hd $tl)))) (only parsing).
  Notation cons hd tl := (match hd, tl return hlist with _, _ => unsafe_cons hd tl end) (only parsing).

  Module CommonHListNotations.
    Declare Scope hlist_scope.
    Delimit Scope hlist_scope with hlist.
    Bind Scope hlist_scope with hlist.
    Infix "::" := const (at level 60, right associativity, only printing) : hlist_scope.
    Infix "::" := conss (at level 60, right associativity, only printing) : hlist_scope.
    Infix "::" := consp (at level 60, right associativity, only printing) : hlist_scope.
    Notation "[ ]" := nil (format "[ ]") : hlist_scope.
    Notation "[ x ]" := (const x nil) (only printing) : hlist_scope.
    Notation "[ x ]" := (conss x nil) (only printing) : hlist_scope.
    Notation "[ x ]" := (consp x nil) (only printing) : hlist_scope.
    (* Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
      (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]", only parsing) : hlist_scope. *)
    Notation "[ x ; y ; .. ; z ]" :=  (const x (const y .. (const z nil) ..))
      (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]", only printing) : hlist_scope.
    Notation "[ x ; y ; .. ; z ]" :=  (conss x (conss y .. (conss z nil) ..))
      (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]", only printing) : hlist_scope.
    Notation "[ x ; y ; .. ; z ]" :=  (consp x (consp y .. (consp z nil) ..))
      (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]", only printing) : hlist_scope.
  End CommonHListNotations.
  Module SafeHListNotations.
    Notation "hd :: tl" := (cons hd tl) (at level 60, right associativity, only parsing) : hlist_scope.
    Notation "[ x ]" := (cons x nil) (only parsing) : hlist_scope.
    (* Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
      (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]", only parsing) : hlist_scope. *)
    Export CommonHListNotations.
  End SafeHListNotations.
  Module UnsafeHListNotations.
    Notation "hd :: tl" := (unsafe_cons hd tl) (at level 60, right associativity, only parsing) : hlist_scope.
    Notation "[ x ]" := (unsafe_cons x nil) (only parsing) : hlist_scope.
    (* Notation "[ x ; y ; .. ; z ]" :=  (unsafe_cons x (unsafe_cons y .. (unsafe_cons z nil) ..))
      (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]", only parsing) : hlist_scope. *)
    Export CommonHListNotations.
  End UnsafeHListNotations.
  (* SafeHListNotations is exponentially slow, cf https://github.com/JasonGross/autoformalization/issues/102 *)
  Module HListNotations := UnsafeHListNotations.
End HList.

Class MustUnfold@{s|u|} {A : Type@{s|u}} (a : A) := {}.
Class IsoStatementProofForMaybeWithSorts@{s s'|u u' us uo|Set < uo, us < uo} (sorts : PolymorphicSpecif.option@{uo} HList.hlist@{us}) {A : Type@{s|u}} (a : A) {isoT : Type@{s'|u'}} (iso : isoT) := {}.
Hint Mode IsoStatementProofForMaybeWithSorts + + + - - : typeclass_instances.
Notation IsoStatementProofFor := (@IsoStatementProofForMaybeWithSorts PolymorphicSpecif.None).
Notation IsoStatementProofForWithSorts sorts := (@IsoStatementProofForMaybeWithSorts (PolymorphicSpecif.Some sorts)).
Notation Build_IsoStatementProofFor := (@Build_IsoStatementProofForMaybeWithSorts PolymorphicSpecif.None).
Notation Build_IsoStatementProofForWithSorts sorts := (@Build_IsoStatementProofForMaybeWithSorts (PolymorphicSpecif.Some sorts)).
Class IsoStatementProofBetween@{s1 s2 s3|u1 u2 u3|} {A : Type@{s1|u1}} (a : A) {B : Type@{s2|u2}} (b : B) {isoT : Type@{s3|u3}} (iso : isoT) := {}.
Hint Mode IsoStatementProofBetween + + + + - - : typeclass_instances.
Variant DebugContext@{s s'|u u'|} {A : Type@{s|u}} {B : Type@{s'|u'}} (a : A) (b : B) : Prop := debug_context.
Variant NoShelve := no_shelve.
Variant Dummy := dummy.

Polymorphic Definition resolve_evar_marker@{s|u|} {T : Type@{s|u}} (t : T) := t.

Module StringOptimizations.
  Section __.
  Import Coq.Strings.String Coq.Strings.Ascii.
  Universes b a s.
  Context {ibool : Type@{b}}
          {itrue ifalse : ibool}
          {iascii : Type@{a}}
          {iAscii : forall (_ _ _ _ _ _ _ _ : ibool), iascii}
          {istring : Type@{s}}
          {iEmptyString : istring}
          {iString : iascii -> istring -> istring}
          (bool_iso : Iso bool ibool)
          (ascii_iso : Iso ascii iascii)
          (string_iso : Iso string istring)
          (true_iso : rel_iso bool_iso true itrue)
          (false_iso : rel_iso bool_iso false ifalse)
          (Ascii_iso : forall
            a1 b1 (_ : rel_iso bool_iso a1 b1)
            a2 b2 (_ : rel_iso bool_iso a2 b2)
            a3 b3 (_ : rel_iso bool_iso a3 b3)
            a4 b4 (_ : rel_iso bool_iso a4 b4)
            a5 b5 (_ : rel_iso bool_iso a5 b5)
            a6 b6 (_ : rel_iso bool_iso a6 b6)
            a7 b7 (_ : rel_iso bool_iso a7 b7)
            a8 b8 (_ : rel_iso bool_iso a8 b8),
            rel_iso ascii_iso (Ascii a1 a2 a3 a4 a5 a6 a7 a8) (iAscii b1 b2 b3 b4 b5 b6 b7 b8))
          (EmptyString_iso : rel_iso string_iso EmptyString iEmptyString)
          (String_iso : forall a1 b1 (_ : rel_iso ascii_iso a1 b1) a2 b2 (_ : rel_iso string_iso a2 b2), rel_iso string_iso (String a1 a2) (iString b1 b2)).

  Definition imported_bool (b : bool) : ibool := if b then itrue else ifalse.
  Definition imported_ascii (a : ascii) : iascii :=
    let (a1, a2, a3, a4, a5, a6, a7, a8) := a in
    iAscii (imported_bool a1) (imported_bool a2) (imported_bool a3) (imported_bool a4) (imported_bool a5) (imported_bool a6) (imported_bool a7) (imported_bool a8).
  Fixpoint imported_string (s : string) : istring :=
    match s with
    | EmptyString => iEmptyString
    | String a s => iString (imported_ascii a) (imported_string s)
    end.
  Definition imported_bool_iso (b : bool) : rel_iso bool_iso b (imported_bool b) := if b return rel_iso bool_iso b (imported_bool b) then true_iso else false_iso.
  Definition imported_ascii_iso (a : ascii) : rel_iso ascii_iso a (imported_ascii a).
  Proof. destruct a. apply Ascii_iso; apply imported_bool_iso. Defined.
  Fixpoint imported_string_iso (s : string) : rel_iso string_iso s (imported_string s) :=
    match s return rel_iso string_iso s (imported_string s) with
    | EmptyString => EmptyString_iso
    | String a s => String_iso (imported_ascii_iso a) (imported_string_iso s)
    end.
  End __.
End StringOptimizations.
