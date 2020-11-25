Require Import Ashley.Axioms.
Require Import Ashley.PartialOrder.
Require Import Ashley.Set.
Require Import Ashley.SetFunction.
Require Import Ashley.Category.

Class Pointed: Type :=
{
  pSet: Type;
  point: pSet
}.

Definition PointedMap (A B: Pointed) := set_type (fun (f: @pSet A -> @pSet B) => f (@point A) = (@point B)).

Definition identity_PointedMap (p: Pointed): PointedMap p p.
apply (stc' (fun x => x)).
trivial.
Defined.

Definition compose_PointedMap (p1 p2 p3: Pointed):
  PointedMap p2 p3 -> PointedMap p1 p2 -> PointedMap p1 p3.
intros.
apply (stc' (fun a1 => val X (val X0 a1))).
rewrite (struct X0).
apply (struct X).
Defined.

Instance pointed_Category: Category Pointed:=
{
  hom:= PointedMap;
  id:= identity_PointedMap;
  compose:= compose_PointedMap
}.
intros.
unfold compose_PointedMap.
apply set_type_ext.
unfold val.
unfold stc'.
destruct x.
destruct y.
destruct z.
trivial.
intros.
unfold compose_PointedMap.
unfold identity_PointedMap.
apply set_type_ext.
unfold val.
unfold stc'.
destruct x.
apply fun_ext.
intros.
trivial.
intros.
unfold compose_PointedMap.
unfold identity_PointedMap.
apply set_type_ext.
unfold val.
unfold stc'.
destruct x.
apply fun_ext.
intros.
trivial.
Defined.

