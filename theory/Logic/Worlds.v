Require Import Ashley.Logic.
Require Import Ashley.Logic.Indexed.
Require Import Ashley.Logic.Modal.
Require Import Ashley.Logic.Prop.

Instance Worlds_Modal (I:Type): Modal (I -> Prop) :=
{
  necessarily s i := forall (j:I), judge (s j)
}.
unfold judge.
unfold indexed_Judge.
unfold judge.
unfold Prop_Judge.
intros.
apply (H j).

unfold implies.
unfold indexed_Implication.
unfold implies.
unfold Prop_Implication.
unfold judge.
unfold indexed_Judge.
unfold judge.
unfold Prop_Judge.
intros.
apply (H j).
apply (H0 j).
Defined.
