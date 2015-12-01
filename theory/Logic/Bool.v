Definition trueb : bool := true.
Definition falseb : bool := false.

Require Import Ashley.Logic.

Instance Bool_Judge: Judge bool :=
{
  judge p := if p then True else False;
  true := trueb
}.
unfold trueb.
trivial.
Defined.

Instance Bool_Implication : Implication bool :=
{
  implies p1 p2 := if p1 then p2 else true
}.
unfold judge.
unfold Bool_Judge.
firstorder.
destruct p.
firstorder.
firstorder.

unfold judge.
unfold Bool_Judge.
destruct p.
destruct q.
firstorder.
firstorder.
destruct q.
firstorder.
firstorder.

firstorder.
unfold judge.
unfold Bool_Judge.
destruct p.
firstorder.
firstorder.
unfold judge.
unfold Bool_Judge.
firstorder.
destruct p.
destruct q.
firstorder.
firstorder.
firstorder.
Defined.

Instance Bool_HasFalse: HasFalse bool :=
{
  false:= falseb
}.
firstorder.
Defined.

Instance Bool_Consistent: Consistent bool :=
{
}.
firstorder.
Defined.
