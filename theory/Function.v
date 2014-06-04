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