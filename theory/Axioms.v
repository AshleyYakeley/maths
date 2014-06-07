Axiom prop_ext : forall A B:Prop, (A <-> B) -> A = B.
Axiom fun_ext : forall (A:Type) (B:Type) (f:A -> B) (g:A -> B), (forall x:A, f x = g x) -> f = g.

Lemma func_prop_ext : forall (A:Type) (f:A -> Prop) (g:A -> Prop), (forall x:A, f x <-> g x) -> f = g.
intros.
apply fun_ext.
intros.
apply prop_ext.
apply H.
Qed.

Axiom lem : forall (p : Prop), p \/ ~p.

Axiom choice_skolemize : forall A B (p: A -> B -> Prop), (forall a, exists b, p a b) -> exists f, forall a, p a (f a).
