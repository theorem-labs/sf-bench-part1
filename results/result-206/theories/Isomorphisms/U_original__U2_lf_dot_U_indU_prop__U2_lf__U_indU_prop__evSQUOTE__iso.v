From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_ev' : imported_nat -> SProp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'.

(* Short names for convenience *)
Definition ev'_orig := Original.LF_DOT_IndProp.LF.IndProp.ev'.
Definition ev'_imp := Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'.

(* Prove that nat_add corresponds to Nat.add *)
Lemma nat_add_correct : forall (n m : Datatypes.nat),
  nat_to_imported (n + m) = Imported.nat_add (nat_to_imported n) (nat_to_imported m).
Proof.
  induction n; intros m.
  - simpl. reflexivity.
  - simpl. 
    change (Imported.nat_S (nat_to_imported (n + m)) = 
            Imported.nat_S (Imported.nat_add (nat_to_imported n) (nat_to_imported m))).
    f_equal. apply IHn.
Qed.

(* Convert ev'_orig to ev'_imp *)
Definition ev'_to_imported : forall n : Datatypes.nat, ev'_orig n -> ev'_imp (nat_to_imported n).
Proof.
  refine (fix F n H {struct H} := _).
  destruct H as [| | n' m' Hn' Hm'].
  - (* ev'_0 *)
    exact Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_0.
  - (* ev'_2 *)
    exact Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_2.
  - (* ev'_sum *)
    rewrite nat_add_correct.
    exact (Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_sum 
             (nat_to_imported n') (nat_to_imported m') (F n' Hn') (F m' Hm')).
Defined.

(* For the reverse direction: we use decidability of ev' *)
Fixpoint is_even_imported (n : Imported.nat) : bool :=
  match n with
  | Imported.nat_O => true
  | Imported.nat_S Imported.nat_O => false
  | Imported.nat_S (Imported.nat_S n') => is_even_imported n'
  end.

(* Construct ev'_orig from the is_even predicate *)
Definition ev'_of_is_even : forall (n : Datatypes.nat), 
  is_even_imported (nat_to_imported n) = true -> ev'_orig n.
Proof.
  fix IH 1.
  intros n H.
  destruct n as [|[|n']].
  - exact Original.LF_DOT_IndProp.LF.IndProp.ev'_0.
  - (* n = 1, impossible *)
    simpl in H. discriminate H.
  - (* n = S (S n') *)
    simpl in H.
    (* We use ev'_sum with 2 and n' *)
    assert (Hn' : ev'_orig n') by exact (IH n' H).
    (* S (S n') = 2 + n', but we use transport directly *)
    exact (Original.LF_DOT_IndProp.LF.IndProp.ev'_sum 2 n' 
             Original.LF_DOT_IndProp.LF.IndProp.ev'_2 Hn').
Defined.

(* Helper to convert SProp eq to Prop eq for bool *)
Definition sprop_eq_to_prop_eq_bool (x y : bool) (H : @IsomorphismDefinitions.eq bool x y) : x = y :=
  match H in (IsomorphismDefinitions.eq _ z) return x = z with
  | IsomorphismDefinitions.eq_refl => Logic.eq_refl
  end.



(* Lemma: nat_add preserves evenness *)
Lemma is_even_nat_add : forall n m : Imported.nat,
  is_even_imported n = true -> is_even_imported m = true ->
  is_even_imported (Imported.nat_add n m) = true.
Proof.
  fix IH 1.
  intros n m Hn Hm.
  destruct n as [|[|n']].
  - simpl. exact Hm.
  - simpl in Hn. discriminate Hn.
  - simpl. simpl in Hn. exact (IH n' m Hn Hm).
Qed.

(* Convert Prop eq to SProp eq *)
Definition eq_to_seq_bool (x y : bool) (H : x = y) : @IsomorphismDefinitions.eq bool x y :=
  match H in (_ = z) return IsomorphismDefinitions.eq x z with
  | Logic.eq_refl => IsomorphismDefinitions.eq_refl
  end.

(* Now prove that ev'_imp n implies is_even_imported n = true (as SProp first) *)
Definition ev'_imp_implies_even_sprop : forall n : Imported.nat, 
  ev'_imp n -> @IsomorphismDefinitions.eq bool (is_even_imported n) true.
Proof.
  intros n H.
  refine (Imported.Original_LF__DOT__IndProp_LF_IndProp_ev'_sind
            (fun m _ => @IsomorphismDefinitions.eq bool (is_even_imported m) true)
            _ _ _ n H).
  - (* ev'_0 *) exact IsomorphismDefinitions.eq_refl.
  - (* ev'_2 *) exact IsomorphismDefinitions.eq_refl.
  - (* ev'_sum *)
    intros n' m' Hn' IHn Hm' IHm.
    (* Need to show is_even_imported (nat_add n' m') = true *)
    apply eq_to_seq_bool.
    apply is_even_nat_add.
    + exact (@sprop_eq_to_prop_eq_bool (is_even_imported n') true IHn).
    + exact (@sprop_eq_to_prop_eq_bool (is_even_imported m') true IHm).
Defined.

(* Convert to Prop eq *)
Definition ev'_imp_implies_even (n : Imported.nat) (H : ev'_imp n) : is_even_imported n = true :=
  @sprop_eq_to_prop_eq_bool (is_even_imported n) true (@ev'_imp_implies_even_sprop n H).

(* Transport is_even along the round-trip *)
Definition ev'_from_imported (n : Imported.nat) (H : ev'_imp n) : ev'_orig (imported_to_nat n) :=
  ev'_of_is_even (imported_to_nat n) 
    (match imported_round_trip n as Heq in (@Logic.eq _ _ m) 
           return is_even_imported m = true -> 
                  is_even_imported (nat_to_imported (imported_to_nat n)) = true
     with
     | Logic.eq_refl => fun x => x
     end (@ev'_imp_implies_even n H)).

(* Build the isomorphism as a direct definition *)
Definition ev'_iso_to (x1 : nat) (x2 : imported_nat) 
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2) 
  (Hev : ev'_orig x1) : ev'_imp x2 :=
  match Hx in (IsomorphismDefinitions.eq _ y) return ev'_imp y with
  | IsomorphismDefinitions.eq_refl => @ev'_to_imported x1 Hev
  end.

Definition ev'_iso_from (x1 : nat) (x2 : imported_nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : ev'_imp x2) : ev'_orig x1 :=
  let H' := match Hx in (IsomorphismDefinitions.eq _ y) return ev'_imp y -> ev'_imp (nat_to_imported x1) with
            | IsomorphismDefinitions.eq_refl => fun h => h
            end H in
  let H'' := @ev'_from_imported (nat_to_imported x1) H' in
  match nat_round_trip x1 in (_ = m) return ev'_orig m with
  | Logic.eq_refl => H''
  end.

Require Import Stdlib.Logic.ProofIrrelevance.

(* Convert proof irrelevance to SProp equality for Prop types *)
Definition prop_proof_irrel_to_seq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

Instance Original_LF__DOT__IndProp_LF_IndProp_ev'_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2), Iso (Original.LF_DOT_IndProp.LF.IndProp.ev' x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev' x2)).
Proof.
  intros x1 x2 Hx.
  unfold rel_iso in Hx. simpl in Hx.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_ev'.
  refine {|
    to := @ev'_iso_to x1 x2 Hx;
    from := @ev'_iso_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := _
  |}.
  intro e.
  apply prop_proof_irrel_to_seq.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.ev' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev' Original_LF__DOT__IndProp_LF_IndProp_ev'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev' Imported.Original_LF__DOT__IndProp_LF_IndProp_ev' Original_LF__DOT__IndProp_LF_IndProp_ev'_iso := {}.