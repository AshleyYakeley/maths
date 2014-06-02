(*
Axiom extensionality : forall (A:Type) (B:Type) (f:A->B)(g:A ->B), (forall x:A, f x = g x) -> f = g.
*)

Axiom funky : forall (A:Type) (f:A -> Prop) (g:A -> Prop), (forall x:A, f x <-> g x) -> f = g.

Lemma not_or : forall a b, ~ (a \/ b) <-> (~a) /\ (~b).
intros.
split.
auto.
unfold not.
intros.
destruct H as [Ha Hb].
elim H0.
apply Ha.
apply Hb.
Save.
