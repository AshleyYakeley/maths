Require Import Ashley.Axioms.
Require Import Ashley.Set.

Definition injective {A} {B} (f : A -> B) : Prop := forall a1 a2, (f a1 = f a2 -> a1 = a2).
Definition surjective {A} {B} (f : A -> B) : Prop := forall b, exists a, f a = b.

Definition retraction {A} {B} (f : A -> B) (g : B -> A) : Prop := forall a:A, g (f a) = a.

Lemma sur_right_inverse: forall {A B} (f: A -> B), surjective f -> exists ff, (injective ff /\ retraction ff f).
intros.
destruct choice with (A:=B) (B:=A) (p:= fun x ffx => f ffx = x).
intros.
unfold surjective in H.
destruct (H a).
exists x.
exact H0.
exists x.
split.
unfold injective.
intros.
unfold surjective in H.
rewrite <- (H0 a1).
rewrite <- (H0 a2).
rewrite H1.
trivial.
exact H0.
Qed.

