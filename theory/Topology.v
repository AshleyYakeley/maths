Require Import Ashley.Axioms.
Require Import Ashley.Logic.
Require Import Ashley.Set.

Class topology {A : Type} (open : set (set A)) : Type :=
{
  top_empty : open empty;
  top_full : open full;
  top_intersect : all a:open, all b:open, open (intersect a b);
  top_union : forall ff, ff <= open -> open (Union ff)
}.

Instance discrete {A : Type} : topology (full : set (set A)) :=  {}.
apply all_full.
apply all_full.
intros.
apply all_full.
intros.
apply all_full.
Save.

Instance indiscrete {A : Type} : topology ({s : set A | not_empty s -> is_full s}) := {}.
firstorder.
firstorder.
firstorder.
firstorder.
Save.

Instance particular_point {A : Type} (p:A) : topology ({s : set A | not_empty s -> s p}) := {}.
firstorder.
firstorder.
firstorder.
firstorder.
Save.

Definition sierpinski := particular_point True.

Class continuous_function {A} {B} {openA : set (set A)} {openB : set (set B)} (TA : topology openA) (TB : topology openB) (f : A -> B) : Type :=
{
  cf_continuous: all sb: openB, openA {a : A|sb (f a)}
}.

Lemma not_noncontinuous: ~ continuous_function sierpinski sierpinski not.
unfold sierpinski.
intro.
specialize (cf_continuous {b:Prop|b}).
firstorder.
contradiction (H False).
intro.
contradiction H0.
trivial.
Qed.
