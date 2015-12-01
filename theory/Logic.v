(* See http://math.andrej.com/2015/07/30/intermediate-truth-values/ *)
Theorem no_intermediate: ~ exists p:Prop, ~ (p <-> True) /\ ~ (p <-> False).
intro.
destruct H.
destruct H.
apply H0. clear H0.
split.
intro.
apply H.
split.
intro.
trivial.
intro.
apply H0.
intro.
contradiction H0.
Save.

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
  implication: forall {p q: prop}, judge (implies p q) -> judge p -> judge q;
  implies_lift: forall {p q: prop}, judge q -> judge (implies p q);
  implies_identity: forall {p: prop}, judge (implies p p);
  implies_compose: forall {p q r: prop}, judge (implies p q) -> judge (implies q r) -> judge (implies p r)
}.

Definition peirce (prop:Type) `{Implication prop} := forall a b:prop, judge (implies (implies (implies a b) a) a).

Class HasFalse (prop:Type) `{Implication prop} : Type :=
{
  false: prop;
  ex_falso: forall {p: prop}, judge (implies false p)
}.

Definition notL {prop} `{HasFalse prop} (p:prop) : prop := implies p false.

Class Consistent (prop:Type) `{HasFalse prop} : Type :=
{
  consistent: ~ judge false
}.

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