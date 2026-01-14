Set Universe Polymorphism.
Class KnownConstant@{s|u|} {A : Type@{s|u}} (a : A) := {}.
Definition recur_on@{s s'|u u'|} {A : Type@{s|u}} (a : A) (B : Type@{s'|u'}) := B.

Variant SkipInduction := skip_induction.
Variant DebugContextPrinted := debug_context_printed.
Variant MarkHyp@{s|u|} {A : Type@{s|u}} (hyp : A) : Prop := mark_hyp.
