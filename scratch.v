Require Import Ashley.Logic.
Require Import Ashley.Set.
Require Import Ashley.Topology.

Check O.
Check nat.
Check Set.
Check Type.
Check Prop.
Check gt.
Check S.
Check 34.
Check (3 > 0).
Check (0 = 0).
Check ((0 = 0) = (0 = 1)).
Check True.

Section Test.

Variables A B C : Prop.

Lemma abbcac: (A -> B) -> (B -> C) -> A -> C.
intro ab.
intro bc.
intro a.
apply bc.
apply ab.
apply a.
Save.

Lemma orc: A \/ B -> B \/ A.
intro ab.
elim ab.
clear ab.
right.
apply H.
left.
apply H.
Save.

Check orc.
Print orc.


Check bool.
Print bool.



