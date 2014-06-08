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
Qed.

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
Qed.

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
Qed.

Class Functor {OA} {MA} {OB} {MB} (CatA : Category OA MA) (CatB : Category OB MB) :=
{
  mapO: OA -> OB;
  mapM: forall {o1 o2 : OA}, MA o1 o2 -> MB (mapO o1) (mapO o2);
  mapsIdentity: forall {o : OA}, mapM (id : MA o o) = (id : MB (mapO o) (mapO o));
  mapsCompose: forall {o1 o2 o3: OA} {m1 : MA o2 o3} {m2 : MA o1 o2}, mapM (compose m1 m2) = compose (mapM m1) (mapM m2)
}.
