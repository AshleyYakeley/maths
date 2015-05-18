Require Import Ashley.Axioms.
Require Import Ashley.Set.
Require Import Ashley.Function.
Require Import Ashley.PartialOrder.

(*
injective A -> B implies n(B) >= n(A)
surjective A -> B implies n(A) >= n(B) and n(B) > 0
*)

Instance cardinality_Preorder: Preorder Type:=
{
  within P Q := exists (f : P -> Q), injective f
}.
intros.
exists (fun x => x).
unfold injective.
intros.
exact H.

intros.
destruct H.
destruct H0.
exists (fun p => x (x0 p)).
unfold injective.
unfold injective in H.
unfold injective in H0.
intros.
apply H0.
apply H.
exact H1.
Defined.

Lemma surjective_as_big : forall A B (g : A->B), surjective g -> A >= B.
intros.
unfold within. unfold cardinality_Preorder.
apply sur_right_inverse in H.
destruct H.
destruct H.
exists x.
exact H.
Qed.

Theorem cantor : forall A, A < set A.
unfold within. unfold cardinality_Preorder.
intros.
intro.
destruct H as [f injf].
unfold injective in injf.
set (G := {a : A | exists s, (a = f s /\ ~ s a)}).
destruct (exclude_middle (G (f G))) as [GfG|nGfG].
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
