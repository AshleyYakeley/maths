Inductive T := TA | TB | TC.
Definition tset x := match x with | TA => True | TB => True | TC => False end.

Class PointedSetC0 X :=
{
  set0 : X -> Prop;
  val0 : X;
  val_in_set0 : set0 val0
}.

Instance ips0A : PointedSetC0 T :=
{
  set0 := tset;
  val0 := TA
}.
unfold tset.
trivial.
Defined.

Lemma val0A: val0 = TA.
trivial.
Defined.

Instance ips0B : PointedSetC0 T :=
{
  set0 := tset;
  val0 := TB
}.
unfold tset.
trivial.
Defined.

Lemma val0B: val0 = TB.
trivial.
Defined.

Lemma bad: TA = TB.
rewrite <- val0A.
rewrite <- val0B.
trivial.
(* The goal is still "val0 = val0", but those are, confusingly, different values. *)
Abort.

Class PointedSetC2 {X} (set2 : X -> Prop) (val2 : X) :=
{
  val_in_set2 : set2 val2
}.

Instance ips2A : PointedSetC2 tset TA := {}.
unfold tset.
trivial.
Defined.

Instance ips2B : PointedSetC2 tset TB := {}.
unfold tset.
trivial.
Defined.

Record TR:=
{
  mR: nat
}.

Class CR:=
{
  mC: nat
}.

Instance iC1: CR := {}.
apply 0.
Defined.



Definition injection {A B: Type} (f: A -> B) := forall (p q:A), f p = f q -> p = q.
Definition surjection {A B: Type} (f: A -> B) := forall x:B, exists p:A, f p = x. 
Axiom choice: forall (A B: Type) (p: A -> B -> Prop), (forall a, exists b, p a b) -> exists f, forall a, p a (f a).


set p := .
apply choice.


Check fun f => fun q:surjection f => choice (fun x p => f p = x) q.

forall A B (r: A -> B -> Prop), (forall x, exists p, r x p) -> exists f, forall a, r a (f a).

Definition vC1: CR.

Check CR.


apply CR.

Definition vR1: TR.
apply 1.
destruct TR.



Lemma thing: forall (a b: PointedR), a = b.
intros.
f_equal.