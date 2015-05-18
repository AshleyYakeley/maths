Require Import Ashley.Axioms.
Require Import Ashley.Set.

Definition injective {A} {B} (f : A -> B) : Prop := forall a1 a2, (f a1 = f a2 -> a1 = a2).
Definition surjective {A} {B} (f : A -> B) : Prop := forall b, exists a, f a = b.

Lemma sur_right_inverse: forall {A B} (f: A -> B), surjective f -> exists ff, (injective ff /\ forall b:B, f (ff b) = b).
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


(*
injective A -> B implies n(B) >= n(A)
surjective A -> B implies n(A) >= n(B) and n(B) > 0
*)

Definition as_big A B := exists (f : B -> A), injective f.

Lemma surjective_as_big : forall A B (g : A->B), surjective g -> as_big A B.
intros.
unfold as_big.
apply sur_right_inverse in H.
destruct H.
destruct H.
exists x.
exact H.
Qed.

Theorem cantor : forall A, ~ as_big A (set A).
unfold as_big.
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
