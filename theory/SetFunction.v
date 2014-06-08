Require Import Ashley.Axioms.
Require Import Ashley.Set.
Require Import Ashley.Category.

Record sval {A : Type} (sa : set A) : Type := Build_sval
{
  val : A;
  ins : sa val
}.

Definition sfun {A} {B} (sa:set A) (sb:set B) := sval sa -> sval sb.

Instance subset_category A : Category (set A) sfun :=
{
  id A := (fun p => p);
  compose A B C mbc mab a := mbc (mab a)
}.
intros.
apply fun_ext.
trivial.
intros.
apply fun_ext.
trivial.
intros.
apply fun_ext.
trivial.
Qed.

Lemma not_in_empty : forall A, forall a : sval (empty : set A), False.
firstorder.
Qed.

Lemma subset_transitive : forall {A} {a b c: set A}, b <= c -> a <= b -> a <= c.
unfold subset.
intros.
apply H.
apply H0.
apply H1.
Qed.

Instance inclusion_category {A} (open : set (set A)) : Category (sval open) (fun sv1 sv2 => (val open sv1) <= (val open sv2)) :=
{
  id P Q := fun x => x;
  compose P Q R := subset_transitive
}.
intros.
apply proof_irrelevance.
intros.
apply proof_irrelevance.
intros.
apply proof_irrelevance.
Qed.