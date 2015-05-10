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

Class PointedMap (A B: Pointed) :=
{
  mapPointed: @pSet A -> @pSet B;
  mapsPoint: mapPointed (@point A) = (@point B)
}.

(*
Lemma equal_PointedMap: forall (A B: Pointed) (P1 P2: PointedMap A B), (@mapPointed A B P1 = @mapPointed A B P2) -> P1 = P2.
intros.
unfold P1.
Check 
f_equal.
*)

Instance identity_PointedMap (p: Pointed): PointedMap p p:=
{
  mapPointed x:= x
}.
trivial.
Defined.

Instance compose_PointedMap (p1 p2 p3: Pointed):
  PointedMap p2 p3 -> PointedMap p1 p2 -> PointedMap p1 p3:=
{
  mapPointed x := mapPointed (mapPointed x)
}.
rewrite mapsPoint.
exact mapsPoint.
Defined.

(*
Instance pointed_Category: Category Pointed:=
{
  hom:= PointedMap;
  id:= identity_PointedMap;
  compose:= compose_PointedMap
}.
*)

Definition PointedMap1 (A B: Pointed) := set_type (fun (f: @pSet A -> @pSet B) => f (@point A) = (@point B)).

Definition identity_PointedMap1 (p: Pointed): PointedMap1 p p.
apply (stc' (fun x => x)).
trivial.
Defined.

Definition compose_PointedMap1 (p1 p2 p3: Pointed):
  PointedMap1 p2 p3 -> PointedMap1 p1 p2 -> PointedMap1 p1 p3.
intros.
apply (stc' (fun a1 => val X (val X0 a1))).
rewrite (struct X0).
apply (struct X).
Defined.

Instance pointed_Category: Category Pointed:=
{
  hom:= PointedMap1;
  id:= identity_PointedMap1;
  compose:= compose_PointedMap1
}.
intros.
unfold compose_PointedMap1.
apply set_type_ext.
unfold val.
unfold stc'.
destruct x.
destruct y.
destruct z.
trivial.
intros.
unfold compose_PointedMap1.
unfold identity_PointedMap1.
apply set_type_ext.
unfold val.
unfold stc'.
destruct x.
apply fun_ext.
intros.
trivial.
intros.
unfold compose_PointedMap1.
unfold identity_PointedMap1.
apply set_type_ext.
unfold val.
unfold stc'.
destruct x.
apply fun_ext.
intros.
trivial.
Defined.

