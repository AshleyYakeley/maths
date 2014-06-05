Require Import Ashley.Axioms.
Require Import Ashley.Logic.
Require Import Ashley.Set.

Definition injective {A} {B} (f : A -> B) : Prop := forall a1 a2, (f a1 = f a2 -> a1 = a2).
Definition surjective {A} {B} (f : A -> B) : Prop := forall b, exists a, b = f a.

(*
injective A -> B implies n(B) >= n(A)
surjective A -> B implies n(A) >= n(B) and n(B) > 0
*)

Definition as_big A B := exists (f : B -> A), injective f.

Theorem cantor : forall A, ~ as_big A (set A).
unfold as_big.
intros.
intro.
destruct H as [f injf].
unfold injective in injf.
set (G := {a : A | exists s, (a = f s /\ ~ s a)}).
destruct (lem (G (f G))) as [GfG|nGfG].
assert (H := GfG).
unfold G at 1 in H.
destruct H as [s H].
destruct H.
elim H0. clear H0.
cut (G = s).
intro.
rewrite <- H0.
apply GfG.
apply injf.
apply H.
elim nGfG.
unfold G at 1.
exists G.
split.
trivial.
apply nGfG.
Save.

Class Equivalence (A:Type) : Type :=
{
  eqv : A -> A -> Prop;
  equiv_reflexive : forall a, eqv a a;
  equiv_symmetric : forall a b, eqv a b -> eqv b a;
  equiv_transitive : forall a b c, (eqv a b /\ eqv b c) -> eqv a c
}.

Definition quotient {A} (E : Equivalence A) : set (set A) :=
  {sa : set A| some a1 : sa, (sa = {a2 : A|eqv a1 a2})}.

Definition disjoint {A} (a:set A) b : Prop := intersect a b = empty.

Lemma quotient_disjoint : forall A (e : Equivalence A), all p1 : quotient e, all p2 : quotient e,
  (p1 = p2 \/ disjoint p1 p2).
intros.
unfold quotient in H.
destruct H as [a11 H].
destruct H.
rewrite H1. clear H1 H p1.

unfold quotient in H0.
destruct H0 as [a12 H].
destruct H.
rewrite H0. clear H0 H p2.

destruct (lem (disjoint {a2 : A | eqv a11 a2} {a2 : A | eqv a12 a2})) as [Hd|Hnd].
right.
apply Hd.
left.
apply func_prop_ext.
intros.
unfold disjoint in Hnd.
unfold intersect in Hnd.
unfold empty in Hnd.
assume_not.
elim Hnd. clear Hnd.
apply func_prop_ext.
intros.
split.
intros.
destruct H0.
cut (eqv a11 a12).
intro.
elim H. clear H.
split.
intro.
apply (equiv_transitive a12 a11 x).
split.
apply equiv_symmetric.
apply H2.
apply H.
intro.
apply (equiv_transitive a11 a12 x).
split.
apply H2.
apply H.
apply (equiv_transitive a11 x0 a12).
split.
apply H0.
apply equiv_symmetric.
apply H1.
intro.
contradiction H0.
Save.

