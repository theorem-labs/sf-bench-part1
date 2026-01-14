-- Lean translation of Rocq definitions for dist_exists_or

-- Define the logical connectives in Prop (will map to SProp in Rocq)

structure and (A B : Prop) : Prop where
  intro ::
  fst : A
  snd : B

inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

def iff (A B : Prop) : Prop := and (A → B) (B → A)

inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro : ∀ (x : A), P x → ex P

-- The main axiom: exists distributes over or
axiom Original_LF__DOT__Logic_LF_Logic_dist__exists__or :
  ∀ (X : Type) (P Q : X → Prop), iff (ex (fun x => or (P x) (Q x))) (or (ex (fun x => P x)) (ex (fun x => Q x)))
