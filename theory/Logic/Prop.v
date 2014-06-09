Require Import Ashley.Logic.

Instance Prop_Judge: Judge Prop :=
{
  judge p := p;
  true := True
}.
trivial.
Defined.

Instance Prop_Implication : Implication Prop :=
{
  implies p1 p2 := p1 -> p2
}.
firstorder.
firstorder.
firstorder.
Defined.

Instance Prop_HasFalse: HasFalse Prop :=
{
  false:= False
}.
firstorder.
Defined.
