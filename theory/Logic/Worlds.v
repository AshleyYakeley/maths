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

Require Import Ashley.Proposition.
Require Import Ashley.Logic.Bool.

Lemma bool_Worlds_Robust: ~ modal_collapse (bool -> Prop).
unfold modal_collapse.
unfold necessarily.
unfold Worlds_Modal.
unfold implies.
unfold indexed_Implication.
unfold implies.
unfold Prop_Implication.
unfold judge.
unfold indexed_Judge.
unfold judge.
unfold Prop_Judge.

apply exists_not.
exists (fun (x:bool) => if x then True else False).
apply exists_not.
exists (true:bool).
simpl.
intro.
firstorder.
destruct (H false).
Save.