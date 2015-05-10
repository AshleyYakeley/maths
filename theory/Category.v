Require Import Ashley.Axioms.

Class Category (Obj: Type): Type :=
{
  hom: Obj -> Obj -> Type;
  id: forall {a:Obj}, hom a a;
  compose: forall {a:Obj} {b:Obj} {c:Obj}, hom b c -> hom a b -> hom a c;
  compose_assoc: forall {a:Obj} {b:Obj} {c:Obj} {d:Obj} {x:hom c d} {y:hom b c} {z:hom a b},  compose x (compose y z) = compose (compose x y) z;
  compose_left_id: forall {a:Obj} {b:Obj} {x : hom a b}, compose id x = x;
  compose_right_id: forall {a:Obj} {b:Obj} {x : hom a b}, compose x id = x
}.
Definition objOf {Obj: Type} (cat: Category Obj) := Obj.
Definition homOf `(cat: Category) := @hom _ cat.
Definition idOf `(cat: Category) := @id _ cat.
Definition composeOf `(cat: Category) {a: objOf cat} {b: objOf cat} {c: objOf cat} := @compose _ cat a b c.

Instance prop_category: Category Prop :=
{
  hom a b := a -> b;
  id A := (fun p => p);
  compose A B C mbc mab a := mbc (mab a)
}.
intros.
trivial.
intros.
apply fun_ext.
trivial.
intros.
apply fun_ext.
trivial.
Defined.

Instance type_category: Category Type :=
{
  hom a b := a -> b;
  id A := (fun p => p);
  compose A B C mbc mab a := mbc (mab a)
}.
intros.
trivial.
intros.
apply fun_ext.
trivial.
intros.
apply fun_ext.
trivial.
Defined.

Instance opposite_category `(cat: Category): Category (objOf cat) :=
{
  hom a b := homOf cat b a;
  id a := idOf cat a;
  compose a b c cb ba := (composeOf cat ba cb)
}.
intros.
rewrite compose_assoc. trivial.
intros.
apply compose_right_id.
intros.
apply compose_left_id.
Defined.

Class Functor `(A: Category) `(B: Category) :=
{
  mapObj: objOf A -> objOf B;
  mapHom: forall {o1 o2}, homOf A o1 o2 -> homOf B (mapObj o1) (mapObj o2);
  mapsIdentity: forall o, mapHom (idOf A o) = idOf B (mapObj o);
  mapsCompose: forall o1 o2 o3 (m1 : homOf A o2 o3) (m2 : homOf A o1 o2), mapHom (composeOf A m1 m2) = composeOf B (mapHom m1) (mapHom m2)
}.
Definition functor_source `{A: Category} `{B: Category} (f: Functor A B) := A.
Definition functor_dest `{A: Category} `{B: Category} (f: Functor A B) := B.
Definition functor_mapObj `(f: Functor) := @mapObj _ _ _ _ f.
Definition functor_mapHom `(f: Functor) {o1 o2} := @mapHom _ _ _ _ f o1 o2.

Class ContraFunctor `(A: Category) `(B: Category) :=
{
  comapObj: objOf A -> objOf B;
  comapHom: forall {o1 o2}, homOf A o1 o2 -> homOf B (comapObj o2) (comapObj o1);
  comapsIdentity: forall o, comapHom (idOf A o) = idOf B (comapObj o);
  comapsCompose: forall o1 o2 o3 (m1 : homOf A o2 o3) (m2 : homOf A o1 o2), comapHom (composeOf A m1 m2) = composeOf B (comapHom m2) (comapHom m1)
}.

Definition contrafunctor_source `{A: Category} `{B: Category} (f: ContraFunctor A B) := A.
Definition contrafunctor_dest `{A: Category} `{B: Category} (f: ContraFunctor A B) := B.
Definition contrafunctor_comapObj `(f: ContraFunctor) := @comapObj _ _ _ _ f.
Definition contrafunctor_comapHom `(f: ContraFunctor) {o1 o2} := @comapHom _ _ _ _ f o1 o2.

Instance identity_functor `(Cat : Category) : Functor Cat Cat :=
{
  mapObj o := o;
  mapHom o1 o2 m := m
}.
intros. trivial.
intros. trivial.
Defined.

Instance compose_functor `{Cat1 : Category} `{Cat2 : Category} `{Cat3 : Category}
 (F23 : Functor Cat2 Cat3) (F12 : Functor Cat1 Cat2) : Functor Cat1 Cat3 :=
{
  mapObj o1 := functor_mapObj F23 (functor_mapObj F12 o1);
  mapHom oa ob m1 := functor_mapHom F23 (functor_mapHom F12 m1)
}.
intros. unfold functor_mapHom. rewrite mapsIdentity. rewrite mapsIdentity. trivial.
intros. unfold functor_mapHom. rewrite mapsCompose. rewrite mapsCompose. trivial.
Defined.
