Require Import Ashley.Set.

Class Equivalence (A:Type) : Type :=
{
  eqv : A -> A -> Prop;
  equiv_reflexive : forall a, eqv a a;
  equiv_symmetric : forall a b, eqv a b -> eqv b a;
  equiv_transitive : forall a b c, (eqv a b /\ eqv b c) -> eqv a c
}.

Definition equivalence_class {A} (E : Equivalence A) (p : A) : set A := {a : A|eqv p a}.

Lemma in_equivalence_class : forall A (e : Equivalence A) (p : A), equivalence_class e p p.
intros.
unfold equivalence_class.
apply equiv_reflexive.
Save.

Definition quotient {A} (e : Equivalence A) : set (set A) :=
  {sa : set A| exists a1, (sa = equivalence_class e a1)}.

Lemma quotient_disjoint : forall A (e : Equivalence A), all p1 : quotient e, all p2 : quotient e,
  (undisjoint p1 p2 -> p1 = p2).
firstorder.
rewrite H.
rewrite H0.
apply member_ext.
rewrite H in H1.
rewrite H0 in H2.
firstorder.
apply (equiv_transitive x0 x x2).
split.
apply (equiv_transitive x0 x1 x).
split.
apply H2.
apply equiv_symmetric.
apply H1.
apply H3.
apply (equiv_transitive x x1 x2).
split.
apply H1.
apply (equiv_transitive x1 x0 x2).
split.
apply equiv_symmetric.
apply H2.
apply H3.
Save.

Lemma quotient_Union : forall A (e : Equivalence A), is_full (Union (quotient e)).
intros.
unfold Union.
unfold quotient.
unfold is_full.
intros.
exists (equivalence_class e x).
split.
exists x.
trivial.
unfold equivalence_class.
apply equiv_reflexive.
Save.

Lemma quotient_no_empty : forall A (e : Equivalence A) (s : set A), quotient e s -> not_empty s.
unfold quotient.
unfold not_empty.
intros.
destruct H.
exists x.
rewrite H.
apply in_equivalence_class.
Save.

Require Import Ashley.SetFunction.

Definition quotient_type {A:Type} (e: Equivalence A) : Type :=  set_type (quotient e).

