Class Judge (prop:Type) : Type :=
{
  judge: prop -> Prop;
  true: prop;
  judge_true: judge true
}.

Instance Prop_Judge: Judge Prop :=
{
  judge p := p;
  true := True
}.
trivial.
Defined.

Class Implication (prop:Type) `{Judge prop} : Type :=
{
  implies: prop -> prop -> prop;
  implication: forall p q : prop, judge (implies p q) -> judge p -> judge q;
  implies_compose: forall p q r: prop, judge (implies p q) -> judge (implies q r) -> judge (implies p r)
}.

Instance Prop_Implication : Implication Prop :=
{
  implies p1 p2 := p1 -> p2
}.
firstorder.
firstorder.
Defined.

Class HasFalse (prop:Type) `{Judge prop} : Type :=
{
  false: prop;
  judge_false: ~ judge false
}.

Instance Prop_HasFalse: HasFalse Prop :=
{
  false:= False
}.
firstorder.
Defined.


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

Definition notL {prop} `{Implication prop} `{HasFalse prop} (p:prop) : prop := implies p false.

Definition Peirce (prop:Type) `{Implication prop} := forall a b:prop, judge (implies (implies (implies a b) a) a).

Lemma Ternary_not_binary: ~ Peirce Ternary.
unfold Peirce.
intro.
specialize (H Maybe3 False3).
unfold implies in H.
unfold Ternary_Implication in H.
firstorder.
Qed. 
