Require Import Ashley.Axioms.
Require Import Ashley.Category.

Class Preorder (A:Type) :=
{
  within: A -> A -> Prop;
  within_reflex: forall p, within p p;
  within_trans: forall p q r, within q r -> within p q -> within p r
}.
Notation "a >= b" := (within b a).
Notation "a <= b" := (within a b).
Notation "a > b" := (~ within a b).
Notation "a < b" := (~ within b a).

Instance indexed_Preorder (I:Type) (A:Type) `{Preorder A} : Preorder (I -> A) :=
{
  within p q := forall i, within (p i) (q i)
}.
intros.
apply within_reflex.
intros.
apply (within_trans (p i) (q i) (r i)).
apply H0.
apply H1.
Defined.

Instance within_Category (A:Type) `{Preorder A}: Category A :=
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

Definition Preorder_Category {A} (po: Preorder A): Category A := @within_Category A po.

Class PartialOrder (A:Type) `{Preorder A} :=
{
  within_antisym: forall p q, within p q -> within q p -> p = q
}.

Instance indexed_PartialOrder (I:Type) (A:Type) `{PartialOrder A} : PartialOrder (I -> A) :=
{
}.
intros.
apply fun_ext.
intros.
apply within_antisym.
apply H1.
apply H2.
Defined.

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
unfold indexed_Preorder.
intros.
apply bottom_within.
intros.
unfold within.
unfold indexed_Preorder.
intros.
apply top_without.
Defined.


Require Import Ashley.Proposition.

Instance prop_Preorder: Preorder Prop :=
{
  within p q := p -> q
}.
intros.
exact H.
intros.
firstorder.
Defined.

Instance prop_PartialOrder: PartialOrder Prop :=
{
}.
intros.
apply prop_ext.
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