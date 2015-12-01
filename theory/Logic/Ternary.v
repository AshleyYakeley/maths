Require Import Ashley.Logic.

Inductive Ternary := True3 | False3 | Maybe3.

Instance Ternary_Judge: Judge Ternary:=
{
  judge p :=
    match p with
    | True3 => True
    | _ => False
    end;
  true := True3
}.
trivial.
Defined.

Instance Ternary_Implication: Implication Ternary :=
{
  implies p1 p2:=
  match p1 with
  | False3 => True3
  | True3 => p2
  | Maybe3 =>
  match p2 with
  | True3 => True3
  | Maybe3 => True3
  | False3 => False3
  end end
}.
firstorder.
destruct p.
firstorder.
firstorder.
firstorder.

destruct p.
destruct q.
firstorder.
firstorder.
firstorder.
destruct q.
firstorder.
firstorder.
firstorder.
destruct q.
firstorder.
firstorder.
firstorder.

destruct p.
firstorder.
firstorder.
firstorder.
intros.
destruct p.
destruct q.
firstorder.
firstorder.
firstorder.
firstorder.
destruct q.
destruct r.
firstorder.
firstorder.
firstorder.
firstorder.
firstorder.
Defined.

Lemma Ternary_not_binary: ~ peirce Ternary.
unfold peirce.
intro.
specialize (H Maybe3 False3).
unfold implies in H.
unfold Ternary_Implication in H.
firstorder.
Qed. 
