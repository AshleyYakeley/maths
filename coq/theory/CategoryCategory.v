Require Import Ashley.Axioms.
Require Import Ashley.Category.
Require Import Ashley.SetFunction.






Instance Category_Category: Category (set_type Category) :=
{
  hom cat1 cat2 := Functor (struct cat1) (struct cat2);
  id cat := identity_functor (struct cat);
  compose c1 c2 c3 := compose_functor
}.
intros.

unfold compose_functor.
f_equal.




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
