-- Lean 4 translation of auto_example_2
-- Original Rocq definition:
-- Example auto_example_2 : forall P Q R S T U : Prop,
--   (P -> Q) ->
--   (P -> R) ->
--   (T -> R) ->
--   (S -> T -> U) ->
--   ((P -> Q) -> (P -> S)) ->
--   T ->
--   P ->
--   U.
-- Admitted.

axiom Original_LF__DOT__Auto_LF_Auto_auto__example__2 :
  ∀ (P Q R S T U : Prop),
    (P → Q) →
    (P → R) →
    (T → R) →
    (S → T → U) →
    ((P → Q) → (P → S)) →
    T →
    P →
    U
