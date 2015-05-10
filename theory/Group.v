Class Semigroup (A: Type): Type :=
{
  op: A -> A -> A;
  associative : forall x y z : A, op x (op y z) = op (op x y) z
}.

Class Monoid (A: Type) `{Semigroup A}: Type :=
{
  ident : A;
  left_identity : forall x:A, op ident x = x;
  right_identity : forall x:A, op x ident = x
}.

Class Group (A: Type) `{Monoid A}: Type :=
{
  inverse : A -> A;
  left_inverse : forall x:A, op (inverse x) x = ident;
  right_inverse : forall x:A, op x (inverse x) = ident
}.

Instance unit_Semigroup: Semigroup unit :=
{
  op := fun _ _ => tt
}.
intros.
trivial.
Defined.

Instance unit_Monoid: Monoid unit :=
{
  ident := tt
}.
intros.
destruct x.
unfold op.
unfold unit_Semigroup.
trivial.
intros.
unfold op.
unfold unit_Semigroup.
destruct x.
trivial.
Defined.

Instance unit_Group: Group unit :=
{
  inverse := fun _ => tt
}.
intros.
destruct x.
unfold op.
unfold ident.
unfold unit_Semigroup.
unfold unit_Monoid.
trivial.
intros.
unfold op.
unfold ident.
unfold unit_Semigroup.
unfold unit_Monoid.
trivial.
Defined.

Section Properties.

Context `{G : Group}.

Lemma inverse_identity : inverse ident = ident.
transitivity (op (inverse ident) ident).
symmetry.
rewrite right_identity.
trivial.
rewrite left_inverse.
trivial.
Save.

Lemma inverse_inverse : forall x:A, inverse (inverse x) = x.
intro.
transitivity (op (inverse (inverse x)) (op (inverse x) x)).
rewrite left_inverse.
rewrite right_identity.
trivial.
rewrite associative.
rewrite left_inverse.
rewrite left_identity.
trivial.
Save.

Lemma unique_unop : forall x y z:A, op x y = z -> x = op z (inverse y).
intros.
rewrite <- H1.
rewrite <- associative.
rewrite right_inverse.
rewrite right_identity.
trivial.
Save.

Lemma unique_identity : forall x i:A, op i x = x -> i = ident.
intros.
rewrite (unique_unop i x x).
rewrite right_inverse.
trivial.
assumption.
Save.

End Properties.
