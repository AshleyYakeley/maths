Require Import Ashley.Axioms.

Class Category {Obj : Type} (M : Obj -> Obj -> Type): Type :=
{
  id: forall {a:Obj}, M a a;
  compose: forall {a:Obj} {b:Obj} {c:Obj}, M b c -> M a b -> M a c;
  compose_assoc: forall {a:Obj} {b:Obj} {c:Obj} {d:Obj} {x:M c d} {y:M b c} {z:M a b},  compose x (compose y z) = compose (compose x y) z;
  compose_left_id: forall {a:Obj} {b:Obj} {x : M a b}, compose id x = x;
  compose_right_id: forall {a:Obj} {b:Obj} {x : M a b}, compose x id = x
}.

Instance prop_category : Category (fun a b => a -> b) :=
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


