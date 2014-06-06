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

Lemma quotient_disjoint : forall A (e : Equivalence A), all p1 : quotient e, all p2 : quotient e,
  (undisjoint p1 p2 -> p1 = p2).
firstorder.
rewrite H2.
rewrite H3.
apply func_prop_ext.
rewrite H2 in H1.
rewrite H3 in H4.
firstorder.
apply (equiv_transitive x0 x x2).
split.
apply (equiv_transitive x0 x1 x).
split.
apply H4.
apply equiv_symmetric.
apply H1.
apply H5.
apply (equiv_transitive x x1 x2).
split.
apply H1.
apply (equiv_transitive x1 x0 x2).
split.
apply equiv_symmetric.
apply H4.
apply H5.
Save.
