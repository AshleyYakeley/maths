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

Instance discrete_topology {A : Type} : topology (full : set (set A)) :=  {}.
apply all_full.
apply all_full.
intros.
apply all_full.
intros.
apply all_full.
Save.

Instance indiscrete_topology {A : Type} : topology ({s : set A | not_empty s -> is_full s}) := {}.
firstorder.
firstorder.
firstorder.
firstorder.
Save.

Instance point_topology {A : Type} (p:A) : topology ({s : set A | not_empty s -> s p}) := {}.
firstorder.
firstorder.
firstorder.
firstorder.
Save.
