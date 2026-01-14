From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev.

(* Convert ev from Original to Imported *)
Definition ev_to_imported : forall (n : Datatypes.nat), Original.LF_DOT_IndProp.LF.IndProp.ev n -> 
  Imported.Original_LF__DOT__IndProp_LF_IndProp_ev (nat_to_imported n) :=
  fix ev_to_imported (n : Datatypes.nat) (H : Original.LF_DOT_IndProp.LF.IndProp.ev n) 
    : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev (nat_to_imported n) :=
    match H in Original.LF_DOT_IndProp.LF.IndProp.ev k 
          return Imported.Original_LF__DOT__IndProp_LF_IndProp_ev (nat_to_imported k) with
    | Original.LF_DOT_IndProp.LF.IndProp.ev_0 => 
        Imported.Original_LF__DOT__IndProp_LF_IndProp_ev_ev_0
    | @Original.LF_DOT_IndProp.LF.IndProp.ev_SS n' H' => 
        Imported.Original_LF__DOT__IndProp_LF_IndProp_ev_ev_SS 
          (nat_to_imported n') (ev_to_imported n' H')
    end.
Arguments ev_to_imported : clear implicits.

(* For the inverse direction, we cannot eliminate SProp to Prop directly.
   However, we can use a wrapper type that lives in Type/Set to bridge the gap.
   The key insight is that we can recurse on the nat structure. *)

(* First, define a predicate to compute whether a nat has the right form for ev *)
Fixpoint has_ev_form (n : Imported.nat) : bool :=
  match n with
  | Imported.nat_O => true
  | Imported.nat_S Imported.nat_O => false
  | Imported.nat_S (Imported.nat_S n') => has_ev_form n'
  end.

(* Build ev proof from the nat structure alone when has_ev_form is true *)
(* Helper to handle the absurd case *)
Definition false_eq_true_absurd : false = true -> forall P : Type, P :=
  fun H => match H in Logic.eq _ b return (if b then forall P : Type, P else True) with
           | Logic.eq_refl => I
           end.

Fixpoint build_ev (n : Imported.nat) : Logic.eq (has_ev_form n) true -> 
  Original.LF_DOT_IndProp.LF.IndProp.ev (imported_to_nat n) :=
  match n return Logic.eq (has_ev_form n) true -> Original.LF_DOT_IndProp.LF.IndProp.ev (imported_to_nat n) with
  | Imported.nat_O => fun _ => Original.LF_DOT_IndProp.LF.IndProp.ev_0
  | Imported.nat_S Imported.nat_O => fun H => false_eq_true_absurd H _
  | Imported.nat_S (Imported.nat_S n') => fun H => 
      Original.LF_DOT_IndProp.LF.IndProp.ev_SS (imported_to_nat n') (build_ev n' H)
  end.

(* Now we need to show that if Imported.ev n, then has_ev_form n = true.
   We can use the SProp eliminator to prove this in SProp, then convert. *)
Definition imported_ev_implies_has_form : forall n, 
  Imported.Original_LF__DOT__IndProp_LF_IndProp_ev n -> 
  IsomorphismDefinitions.eq (has_ev_form n) true :=
  @Imported.Original_LF__DOT__IndProp_LF_IndProp_ev_sind
    (fun n _ => IsomorphismDefinitions.eq (has_ev_form n) true)
    IsomorphismDefinitions.eq_refl
    (fun n' _ IH => IH)
  .
Arguments imported_ev_implies_has_form : clear implicits.

(* We need a way to convert SProp equality to Prop equality for bools *)
(* Since bool is a decidable type, equality in SProp implies equality in Prop *)
(* Use the SProp eliminator directly with the return type in Prop *)
Definition sprop_eq_to_prop_eq_bool (b1 b2 : bool) 
  (H : IsomorphismDefinitions.eq b1 b2) : Logic.eq b1 b2 :=
  IsomorphismDefinitions.eq_rect b1 (fun y _ => Logic.eq b1 y) Logic.eq_refl b2 H.
Arguments sprop_eq_to_prop_eq_bool : clear implicits.

Definition ev_from_imported (n : Imported.nat) 
  (H : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev n) 
  : Original.LF_DOT_IndProp.LF.IndProp.ev (imported_to_nat n) :=
  let pf := imported_ev_implies_has_form n H in
  let pf_prop := sprop_eq_to_prop_eq_bool (has_ev_form n) true pf in
  build_ev n pf_prop.
Arguments ev_from_imported : clear implicits.

Definition transport_ev_forward (x1 : Datatypes.nat) (x2 : Imported.nat) 
  (Hrel : IsomorphismDefinitions.eq (nat_to_imported x1) x2) 
  (H : Original.LF_DOT_IndProp.LF.IndProp.ev x1) 
  : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev x2 :=
  @IsomorphismDefinitions.eq_sind Imported.nat (nat_to_imported x1) 
           (fun y _ => Imported.Original_LF__DOT__IndProp_LF_IndProp_ev y) 
           (ev_to_imported x1 H) x2 Hrel.
Arguments transport_ev_forward : clear implicits.

Definition transport_ev_backward (x1 : Datatypes.nat) (x2 : Imported.nat) 
  (Hrel : IsomorphismDefinitions.eq (nat_to_imported x1) x2) 
  (H : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev x2) 
  : Original.LF_DOT_IndProp.LF.IndProp.ev x1 :=
  (* First transport H : Imported.ev x2 to Imported.ev (nat_to_imported x1) *)
  let H' : Imported.Original_LF__DOT__IndProp_LF_IndProp_ev (nat_to_imported x1) :=
    @IsomorphismDefinitions.eq_sind Imported.nat x2 
       (fun y _ => Imported.Original_LF__DOT__IndProp_LF_IndProp_ev y) 
       H (nat_to_imported x1)
       (eq_sym Hrel) in
  (* Now apply ev_from_imported to get Original.ev (imported_to_nat (nat_to_imported x1)) *)
  let ev_result := ev_from_imported (nat_to_imported x1) H' in
  (* Transport using nat_round_trip: imported_to_nat (nat_to_imported x1) = x1 *)
  match nat_round_trip x1 in (Logic.eq _ m) return Original.LF_DOT_IndProp.LF.IndProp.ev m with
  | Logic.eq_refl => ev_result
  end.
Arguments transport_ev_backward : clear implicits.

From Stdlib Require Import ProofIrrelevance.

Instance Original_LF__DOT__IndProp_LF_IndProp_ev_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.ev x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev x2).
Proof.
  intros x1 x2 Hrel.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_ev.
  unfold rel_iso in Hrel. simpl in Hrel.
  (* Hrel : IsomorphismDefinitions.eq (nat_to_imported x1) x2 *)
  (* Use proof irrelevance for Prop (Original.ev x1) and SProp irrelevance for SProp (Imported.ev x2) *)
  refine (@Build_Iso 
    (Original.LF_DOT_IndProp.LF.IndProp.ev x1)
    (Imported.Original_LF__DOT__IndProp_LF_IndProp_ev x2)
    (transport_ev_forward x1 x2 Hrel)
    (transport_ev_backward x1 x2 Hrel)
    (fun H => IsomorphismDefinitions.eq_refl)  (* SProp irrelevance: any two values of the same SProp are equal *)
    (fun H => seq_of_eq (proof_irrelevance _ _ H))  (* Prop proof irrelevance *)
  ).
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev Original_LF__DOT__IndProp_LF_IndProp_ev_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev Imported.Original_LF__DOT__IndProp_LF_IndProp_ev Original_LF__DOT__IndProp_LF_IndProp_ev_iso := {}.