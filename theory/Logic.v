Require Import Ashley.Axioms.

Class Judge (prop:Type) : Type :=
{
  judge: prop -> Prop;
  true: prop;
  judge_true: judge true
}.

Class Implication (prop:Type) `{Judge prop} : Type :=
{
  implies: prop -> prop -> prop;
  implication: forall {p q : prop}, judge (implies p q) -> judge p -> judge q;
  implies_identity: forall {p: prop}, judge (implies p p);
  implies_compose: forall {p q r: prop}, judge (implies p q) -> judge (implies q r) -> judge (implies p r)
}.

Definition peirce (prop:Type) `{Implication prop} := forall a b:prop, judge (implies (implies (implies a b) a) a).

Class HasFalse (prop:Type) `{Judge prop} : Type :=
{
  false: prop;
  judge_false: ~ judge false
}.

Definition notL {prop} `{Implication prop} `{HasFalse prop} (p:prop) : prop := implies p false.

Require Import Ashley.Category.

Instance Logic_Category (prop:Type) `{Implication prop}: Category prop :=
{
  hom a b := judge (implies a b);
  id A := implies_identity;
  compose A B C x y := implies_compose y x
}.
intros.
apply proof_irrelevance.
intros.
apply proof_irrelevance.
intros.
apply proof_irrelevance.
Defined.