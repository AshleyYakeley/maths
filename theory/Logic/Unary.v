Require Import Ashley.Logic.

Inductive Unary := True1.

Instance Unary_Judge: Judge Unary :=
{
  judge True1 := True;
  true := True1
}.
trivial.
Defined.

Instance Unary_Implication: Implication Unary :=
{
  implies True1 True1 := True1
}.
firstorder.
firstorder.
firstorder.
firstorder.
Defined.

Instance Unary_HasFalse: HasFalse Unary :=
{
  false := True1
}.
firstorder.
Defined.