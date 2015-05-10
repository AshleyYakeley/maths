Require Import Ashley.Axioms.
Require Import Ashley.Category.

Record AnyCategory: Type := MkAnyCategory
{
  acObj: Type;
  acCat: Category acObj
}.

Definition mapHomOff `(f: Functor) := @mapHom _ _ _ _ f.


Check @mapHom.
Definition mapHomOf1 `(A: Category) `(B: Category) (f: Functor A B) (o1 o2: objOf A) (m: homOf A o1 o2) : homOf B (mapObjOf f o1) (mapObjOf f o2) := @mapHom (objOf A) A (objOf B) B f o1 o2 m.

Check mapHomOf1.

Record R: Type := MkR {rT: Type; rV: rT}.

Lemma test: forall (a b: R), a = b.
intros.
apply R_ind.
intros.
symmetry.
apply R_ind.
intros.
f_equal.



Lemma functor_equal: forall `(A: Category) `(B: Category) (f1: Functor A B) (f2: Functor A B),
    (mapObjOf f1 = mapObjOf f2) -> (forall (o1: objOf A) (o2: objOf A) (m : homOf A o1 o2), mapHomOf1 A B f1 o1 o2 m = mapHomOf1 A B f2 o1 o2 m) -> f1 = f2.


Instance category_category : Category AnyCategory :=
{
  hom A B := Functor (acCat A) (acCat B);
  id A := identity_functor (acCat A);
  compose A B C mbc mab := compose_functor mbc mab
}.
intros.
unfold compose_functor.
f_equal.






