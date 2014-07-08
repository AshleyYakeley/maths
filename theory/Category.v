Require Import Ashley.Axioms.

Class Category (Obj : Type) (M : Obj -> Obj -> Type): Type :=
{
  id: forall {a:Obj}, M a a;
  compose: forall {a:Obj} {b:Obj} {c:Obj}, M b c -> M a b -> M a c;
  compose_assoc: forall {a:Obj} {b:Obj} {c:Obj} {d:Obj} {x:M c d} {y:M b c} {z:M a b},  compose x (compose y z) = compose (compose x y) z;
  compose_left_id: forall {a:Obj} {b:Obj} {x : M a b}, compose id x = x;
  compose_right_id: forall {a:Obj} {b:Obj} {x : M a b}, compose x id = x
}.

Instance prop_category : Category Prop (fun a b => a -> b) :=
{
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

Instance type_category : Category Type (fun a b => a -> b) :=
{
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

Instance opposite_category {obj} {m} (cat : Category obj m) : Category obj (fun a b => m b a) :=
{
  id A := id : m A A;
  compose A B C mcb mba := (compose (mba : m B A) (mcb : m C B) : m C A)
}.
intros.
rewrite compose_assoc. trivial.
intros.
apply compose_right_id.
intros.
apply compose_left_id.
Defined.

Class Functor {OA} {MA} {OB} {MB} (CatA : Category OA MA) (CatB : Category OB MB) :=
{
  mapO: OA -> OB;
  mapM: forall {o1 o2 : OA}, MA o1 o2 -> MB (mapO o1) (mapO o2);
  mapsIdentity: forall {o : OA}, mapM (id : MA o o) = (id : MB (mapO o) (mapO o));
  mapsCompose: forall {o1 o2 o3: OA} {m1 : MA o2 o3} {m2 : MA o1 o2}, mapM (compose m1 m2) = compose (mapM m1) (mapM m2)
}.

Class ContraFunctor {OA} {MA} {OB} {MB} (CatA : Category OA MA) (CatB : Category OB MB) :=
{
  comapO: OA -> OB;
  comapM: forall (o1 o2 : OA), MA o1 o2 -> MB (comapO o2) (comapO o1);
  comapsIdentity: forall {o : OA}, comapM o o (id : MA o o) = (id : MB (comapO o) (comapO o));
  comapsCompose: forall {o1 o2 o3: OA} {m1 : MA o2 o3} {m2 : MA o1 o2}, comapM o1 o3 (compose m1 m2) = compose (comapM o1 o2 m2) (comapM o2 o3 m1)
}.

Instance identity_functor {O} {M} {Cat : Category O M} : Functor Cat Cat :=
{
  mapO o := o;
  mapM o1 o2 m := m
}.
intros. trivial.
intros. trivial.
Defined.

Instance compose_functor {O1} {M1} {Cat1 : Category O1 M1} {O2} {M2} {Cat2 : Category O2 M2} {O3} {M3} {Cat3 : Category O3 M3}
 (F23 : Functor Cat2 Cat3) (F12 : Functor Cat1 Cat2) : Functor Cat1 Cat3 :=
{
  mapO o1 := mapO (mapO o1 : O2);
  mapM oa ob m1 := mapM (mapM m1 : M2 (mapO oa) (mapO ob))
}.
intros. rewrite mapsIdentity. rewrite mapsIdentity. trivial.
intros. rewrite mapsCompose. rewrite mapsCompose. trivial.
Defined.

Record AnyCategory : Type := MkAnyCategory
{
  acObj : Type;
  acM : acObj -> acObj -> Type;
  acCat : Category acObj acM
}.

Definition AnyFunctor (A : AnyCategory) (B : AnyCategory) : Type := Functor (acCat A) (acCat B).

Instance category_category : Category AnyCategory AnyFunctor :=
{
  id A := identity_functor;
  compose A B C mbc mab := compose_functor mbc mab
}.
intros. unfold compose_functor.
f_equal (* slow! *).
apply proof_irrelevance.
apply proof_irrelevance.
intros. unfold compose_functor. unfold identity_functor.


Defined.
