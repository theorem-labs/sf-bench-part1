From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.
Require Import Stdlib.Logic.ProofIrrelevance.

Definition imported_Original_LF__DOT__Logic_LF_Logic_Even : imported_nat -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

Definition Even_orig := Original.LF_DOT_Logic.LF.Logic.Even.
Definition Even_imp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

(* Convert Prop proof irrelevance to SProp eq *)
Definition prop_proof_irrel_to_seq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

(* Helper: convert Logic.eq to Imported.MyEq *)
Definition logic_eq_to_imported_myeq {A : Type} {x y : A} (H : @Logic.eq A x y) : Imported.MyEq A x y :=
  match H in (@Logic.eq _ _ z) return Imported.MyEq A x z with
  | Logic.eq_refl => Imported.MyEq_refl A x
  end.

(* Use nat_to_imported from double_iso *)
Definition nat_to_imported : nat -> imported_nat := U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.nat_to_imported.
Definition imported_to_nat : imported_nat -> nat := from nat_iso.

(* Convert SProp eq to Prop eq for nat *)
Definition sprop_eq_to_prop_eq_nat (x y : nat) (H : @IsomorphismDefinitions.eq nat x y) : @Logic.eq nat x y :=
  match H in (IsomorphismDefinitions.eq _ z) return @Logic.eq nat x z with
  | IsomorphismDefinitions.eq_refl => Logic.eq_refl
  end.

(* Round-trip lemma *)
Lemma nat_round_trip : forall n : nat, imported_to_nat (nat_to_imported n) = n.
Proof.
  intro n.
  unfold nat_to_imported, imported_to_nat.
  apply sprop_eq_to_prop_eq_nat.
  apply (from_to nat_iso n).
Qed.

(* Convert SProp eq to Prop eq for imported_nat *)
Definition sprop_eq_to_prop_eq_imported_nat (x y : imported_nat) (H : @IsomorphismDefinitions.eq imported_nat x y) : @Logic.eq imported_nat x y :=
  match H in (IsomorphismDefinitions.eq _ z) return @Logic.eq imported_nat x z with
  | IsomorphismDefinitions.eq_refl => Logic.eq_refl
  end.

(* to: Even_orig x1 -> Even_imp x2 *)
Definition Even_to (x1 : nat) (x2 : imported_nat) 
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_orig x1) : Even_imp x2.
Proof.
  unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even in H.
  destruct H as [n Hn].
  unfold Even_imp, Imported.Original_LF__DOT__Logic_LF_Logic_Even.
  apply Imported.Original_LF__DOT__Logic_LF_Logic_Even_ex_intro with (x := nat_to_imported n).
  destruct Hx.
  rewrite Hn.
  apply logic_eq_to_imported_myeq.
  unfold nat_to_imported, U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.nat_to_imported.
  pose proof (double_commutes n) as Hdc.
  unfold imported_Original_LF__DOT__Induction_LF_Induction_double, U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.nat_to_imported in Hdc.
  symmetry. apply sprop_eq_to_prop_eq_imported_nat. apply IsoEq.eq_sym. exact Hdc.
Defined.

(* Check if imported n is even *)
Fixpoint is_even_imported (n : Imported.nat) : bool :=
  match n with
  | Imported.nat_O => true
  | Imported.nat_S Imported.nat_O => false
  | Imported.nat_S (Imported.nat_S n') => is_even_imported n'
  end.

(* Prove double m is always even *)
Fixpoint double_is_even (m : Imported.nat) : 
  @IsomorphismDefinitions.eq bool (is_even_imported (Imported.Original_LF__DOT__Induction_LF_Induction_double m)) true :=
  match m return @IsomorphismDefinitions.eq bool (is_even_imported (Imported.Original_LF__DOT__Induction_LF_Induction_double m)) true with
  | Imported.nat_O => IsomorphismDefinitions.eq_refl
  | Imported.nat_S m' => double_is_even m'
  end.

(* Even_imp n implies is_even_imported n = true (via SProp induction) *)
Definition ev_imp_implies_even_sprop : forall n : Imported.nat, 
  Imported.Original_LF__DOT__Logic_LF_Logic_Even n -> @IsomorphismDefinitions.eq bool (is_even_imported n) true.
Proof.
  intros n H.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_Even in H.
  refine (Imported.Original_LF__DOT__Logic_LF_Logic_Even_ex_indl
            _
            (fun _ => @IsomorphismDefinitions.eq bool (is_even_imported n) true)
            _ H).
  intros m Hm.
  pose proof (double_is_even m) as Hdm.
  assert (Heqn : @IsomorphismDefinitions.eq bool (is_even_imported n) (is_even_imported (Imported.Original_LF__DOT__Induction_LF_Induction_double m))).
  {
    refine (Imported.MyEq_indl Imported.nat n 
              (fun z _ => @IsomorphismDefinitions.eq bool (is_even_imported n) (is_even_imported z))
              IsomorphismDefinitions.eq_refl
              (Imported.Original_LF__DOT__Induction_LF_Induction_double m) Hm).
  }
  refine (match Heqn in (IsomorphismDefinitions.eq _ y) return @IsomorphismDefinitions.eq bool y true -> @IsomorphismDefinitions.eq bool (is_even_imported n) true with
          | IsomorphismDefinitions.eq_refl => fun x => x
          end Hdm).
Defined.

(* Convert SProp eq to Logic.eq for bools *)
Definition sprop_eq_to_prop_eq_bool (x y : bool) (H : @IsomorphismDefinitions.eq bool x y) : @Logic.eq bool x y :=
  match H in (IsomorphismDefinitions.eq _ z) return @Logic.eq bool x z with
  | IsomorphismDefinitions.eq_refl => Logic.eq_refl
  end.

Definition ev_imp_implies_even (n : Imported.nat) (H : Imported.Original_LF__DOT__Logic_LF_Logic_Even n) : @Logic.eq bool (is_even_imported n) true.
Proof.
  apply sprop_eq_to_prop_eq_bool.
  apply ev_imp_implies_even_sprop.
  exact H.
Defined.

(* Prove that if is_even_imported n = true, then there's a witness m with imported_to_nat n = double m *)
Lemma is_even_has_witness : forall n : Imported.nat,
  @Logic.eq bool (is_even_imported n) true ->
  @ex nat (fun m => @Logic.eq nat (imported_to_nat n) (Original.LF_DOT_Induction.LF.Induction.double m)).
Proof.
  fix IH 1.
  intro n.
  destruct n as [|[|n']].
  - simpl. intros _. exists O. exact (@Logic.eq_refl nat O).
  - simpl. intros H. discriminate H.
  - simpl. intros H.
    destruct (IH n' H) as [m Hm].
    exists (S m).
    simpl.
    exact (match Hm in (@Logic.eq _ _ z) return @Logic.eq nat (S (S (imported_to_nat n'))) (S (S z)) with
           | Logic.eq_refl => Logic.eq_refl
           end).
Defined.

Definition Even_from (x1 : nat) (x2 : imported_nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_imp x2) : Even_orig x1.
Proof.
  unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even.
  destruct Hx.
  (* After destruct, H : Even_imp (nat_to_imported x1) *)
  pose proof (@ev_imp_implies_even (nat_to_imported x1) H) as Heven.
  destruct (@is_even_has_witness (nat_to_imported x1) Heven) as [m Hm].
  exists m.
  rewrite <- (nat_round_trip x1).
  exact Hm.
Defined.

Instance Original_LF__DOT__Logic_LF_Logic_Even_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2), Iso (Original.LF_DOT_Logic.LF.Logic.Even x1) (imported_Original_LF__DOT__Logic_LF_Logic_Even x2)).
Proof.
  intros x1 x2 Hx.
  unfold rel_iso in Hx. simpl in Hx.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_Even.
  refine {|
    to := @Even_to x1 x2 Hx;
    from := @Even_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := _
  |}.
  intro e.
  apply prop_proof_irrel_to_seq.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.Even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_Even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.Even Imported.Original_LF__DOT__Logic_LF_Logic_Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.