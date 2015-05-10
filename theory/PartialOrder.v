Require Import Ashley.Axioms.
Require Import Ashley.Category.

Class PartialOrder (A:Type) :=
{
  within: A -> A -> Prop;
  within_reflex: forall p, within p p;
  within_antisym: forall p q, within p q -> within q p -> p = q;
  within_trans: forall p q r, within q r -> within p q -> within p r
}.
Notation "a >= b" := (within b a).
Notation "a <= b" := (within a b).

Instance indexed_PartialOrder (I:Type) (A:Type) `{PartialOrder A} : PartialOrder (I -> A) :=
{
  within p q := forall i, within (p i) (q i)
}.
intros.
apply within_reflex.
intros.
apply fun_ext.
intros.
apply within_antisym.
apply H0.
apply H1.
intros.
apply (within_trans (p i) (q i) (r i)).
apply H0.
apply H1.
Defined.

Instance within_Category (A:Type) `{PartialOrder A}: Category A :=
{
  hom := within;
  id := within_reflex;
  compose := within_trans
}.
intros.
apply proof_irrelevance.
intros.
apply proof_irrelevance.
intros.
apply proof_irrelevance.
Defined.

Definition PartialOrder_Category {A} (po: PartialOrder A): Category A := @within_Category A po.

Class BoundedPartialOrder (A:Type) `{PartialOrder A} :=
{
  bottom: A;
  bottom_within: forall (p:A), bottom <= p;
  top: A;
  top_without: forall (p:A), p <= top
}.

Instance indexed_BoundedPartialOrder (I:Type) (A:Type) `{BoundedPartialOrder A} : BoundedPartialOrder (I -> A) :=
{
  bottom i := bottom;
  top i := top
}.
intros.
unfold within.
unfold indexed_PartialOrder.
intros.
apply bottom_within.
intros.
unfold within.
unfold indexed_PartialOrder.
intros.
apply top_without.
Defined.


Require Import Ashley.Proposition.

Instance prop_PartialOrder: PartialOrder Prop :=
{
  within p q := p -> q
}.
intros.
exact H.
intros.
apply prop_ext.
firstorder.
intros.
firstorder.
Defined.

Instance prop_BoundedPartialOrder: BoundedPartialOrder Prop :=
{
  bottom := False;
  top := True
}.
unfold within.
unfold prop_PartialOrder.
firstorder.
unfold within.
unfold prop_PartialOrder.
firstorder.
Defined.