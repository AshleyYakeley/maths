Class Group {A : Type} (op : A -> A -> A): Type :=
{
  ident : A;
  inverse : A -> A;
  group_left_identity : forall x:A, op ident x = x;
  group_right_identity : forall x:A, op x ident = x;
  group_left_inverse : forall x:A, op (inverse x) x = ident;
  group_right_inverse : forall x:A, op x (inverse x) = ident;
  group_associative : forall x y z : A, op x (op y z) = op (op x y) z
}.

Instance unit_group: Group (fun _ _ => tt) :=
{
  ident := tt;
  inverse := fun _ => tt
}.
intro.
case x.
trivial.
intro.
case x.
trivial.
trivial.
trivial.
trivial.
Qed.


Section Properties.

Context `{G : Group}.

Lemma group_inverse_identity : inverse ident = ident.
transitivity (op (inverse ident) ident).
symmetry.
rewrite group_right_identity.
trivial.
rewrite group_left_inverse.
trivial.
Save.

Lemma group_inverse_inverse : forall x:A, inverse (inverse x) = x.
intro.
transitivity (op (inverse (inverse x)) (op (inverse x) x)).
rewrite group_left_inverse.
rewrite group_right_identity.
trivial.
rewrite group_associative.
rewrite group_left_inverse.
rewrite group_left_identity.
trivial.
Save.

Lemma group_unique_unop : forall x y z:A, op x y = z -> x = op z (inverse y).
intros.
rewrite <- H.
rewrite <- group_associative.
rewrite group_right_inverse.
rewrite group_right_identity.
trivial.
Save.

Lemma group_unique_identity : forall x i:A, op i x = x -> i = ident.
intros.
rewrite (group_unique_unop i x x).
rewrite group_right_inverse.
trivial.
assumption.
Save.

End Properties.
