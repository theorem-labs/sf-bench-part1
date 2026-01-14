From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Import the nat and ev isomorphisms *)
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2' : SProp := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'.

(* Helper lemma: nat_add on imported corresponds to addition. *)
(* nat_add (nat_succ n) m = nat_succ (nat_add n m) is definitionally equal *)
(* nat_add nat_zero m = m is definitionally equal *)
Fixpoint nat_add_to_imported (n : Datatypes.nat) (m : Datatypes.nat) {struct n} :
  IsomorphismDefinitions.eq 
    (nat_to_imported (Nat.add n m)) 
    (Imported.nat_add (nat_to_imported n) (nat_to_imported m)) :=
  match n as n0 return 
    IsomorphismDefinitions.eq 
      (nat_to_imported (Nat.add n0 m)) 
      (Imported.nat_add (nat_to_imported n0) (nat_to_imported m)) with
  | O => IsomorphismDefinitions.eq_refl
  | S n' => 
      (* Goal: eq (nat_succ (nat_to_imported (n' + m))) 
                  (nat_add (nat_succ (nat_to_imported n')) (nat_to_imported m))
         By def equality: nat_add (nat_succ x) y = nat_succ (nat_add x y)
         So goal becomes: eq (nat_succ (nat_to_imported (n' + m)))
                             (nat_succ (nat_add (nat_to_imported n') (nat_to_imported m)))
         Using f_equal on IH: eq (nat_to_imported (n' + m)) 
                                 (nat_add (nat_to_imported n') (nat_to_imported m)) *)
      f_equal Imported.nat_succ (nat_add_to_imported n' m)
  end.

(* ev_plus2' is: forall n, ev n -> ev (n + 2) *)
(* Original: forall n : nat, Original.ev n -> Original.ev (n + 2)  : Prop *)
(* Imported: forall n : Imported.nat, Imported.ev n -> Imported.ev (nat_add n (succ (succ zero))) : SProp *)

(* Key lemma: S (S n) = nat_add n 2 (reverse direction for transport) *)
Fixpoint nat_add_n_2_rev (n : Imported.nat) : 
  IsomorphismDefinitions.eq 
    (Imported.nat_succ (Imported.nat_succ n))
    (Imported.nat_add n (Imported.nat_succ (Imported.nat_succ Imported.nat_zero))) :=
  match n as n0 return 
    IsomorphismDefinitions.eq 
      (Imported.nat_succ (Imported.nat_succ n0))
      (Imported.nat_add n0 (Imported.nat_succ (Imported.nat_succ Imported.nat_zero))) with
  | Imported.nat_zero => IsomorphismDefinitions.eq_refl
  | Imported.nat_succ n' => f_equal Imported.nat_succ (nat_add_n_2_rev n')
  end.

(* The to function: Original -> Imported *)
Definition ev_plus2'_to : 
  Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2' -> 
  Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'.
Proof.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'.
  unfold Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'.
  intros _ n Hn.
  (* n : Imported.nat, Hn : Imported.ev n *)
  (* Goal: Imported.ev (nat_add n (S (S 0))) *)
  (* We have: ev_SS : ev n -> ev (S (S n)) *)
  pose proof (Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_ev_SS n Hn) as HevSS.
  (* HevSS : ev (S (S n)) *)
  (* nat_add_n_2_rev : eq (S (S n)) (nat_add n 2) *)
  (* Transport HevSS along nat_add_n_2_rev to ev (nat_add n 2) *)
  exact (match nat_add_n_2_rev n in IsomorphismDefinitions.eq _ b 
         return Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev b with
         | IsomorphismDefinitions.eq_refl => HevSS
         end).
Defined.

(* For the from direction, we need: Datatypes.nat + 2 = S (S n) *)
(* In standard Coq, n + 2 = S (S n) by computation since + is defined by recursion on first arg *)
(* Use Logic.eq (the standard Coq equality) *)
Fixpoint nat_add_n_2_std (n : Datatypes.nat) : Logic.eq (n + 2) (S (S n)) :=
  match n as n0 return Logic.eq (n0 + 2) (S (S n0)) with
  | O => Logic.eq_refl
  | S n' => Logic.f_equal S (nat_add_n_2_std n')
  end.

(* The from function: Imported -> Original *)
Definition ev_plus2'_from :
  Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2' ->
  Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'.
Proof.
  unfold Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'.
  unfold Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'.
  intros _ n Hn.
  (* n : nat, Hn : Original.ev n *)
  (* Goal: Original.ev (n + 2) *)
  (* We have ev_SS : ev n -> ev (S (S n)) *)
  pose proof (Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_SS n Hn) as HevSS.
  (* HevSS : Original.ev (S (S n)) *)
  (* Transport along: n + 2 = S (S n), so we need reverse: S (S n) = n + 2 *)
  exact (match Logic.eq_sym (nat_add_n_2_std n) in Logic.eq _ b 
         return Original.LF_DOT_ProofObjects.LF.ProofObjects.ev b with
         | Logic.eq_refl => HevSS
         end).
Defined.

Require Import Stdlib.Logic.ProofIrrelevance.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'.
Proof.
  unfold imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'.
  refine (@Build_Iso 
           Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'
           Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'
           ev_plus2'_to
           ev_plus2'_from
           (fun _ => IsomorphismDefinitions.eq_refl)
           _).
  (* from_to: need eq (ev_plus2'_from (ev_plus2'_to e)) e *)
  intro e.
  (* Use proof irrelevance: both are proofs of ev_plus2' *)
  pose proof (proof_irrelevance _ (ev_plus2'_from (ev_plus2'_to e)) e) as H.
  destruct H.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2' Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2' Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2' Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'_iso := {}.