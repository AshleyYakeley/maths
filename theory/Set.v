Require Import Ashley.Axioms.
Require Import Ashley.Logic.

Definition set (A : Type) := A -> Prop.

Notation "{ x : A | P }" := (fun x : A => P).

Lemma member_ext :  forall {A} a b, (forall x:A, a x <-> b x) -> a = b.
intros.
apply func_prop_ext.
apply H.
Save.

Definition empty {A} := {x:A|False}.
Definition full {A} := {x:A|True}.
Definition singleton {A} p : set A := {x:A|x=p}.
Definition invert {A} p := {x:A|~ p x}.
Definition intersect {A} a b := {x:A|a x /\ b x}.
Definition union {A} a b := {x:A|a x \/ b x}.
Definition subset {A} (p : set A) (q : set A) := forall x, p x -> q x.
Notation "a <= b" := (subset a b).
Definition superset {A} (p : set A) (q : set A) := subset q p.
Notation "a >= b" := (superset a b).
Definition powerset {A} (p : set A) := {x:set A|x <= p}.

Lemma all_full : forall A (p : A), full p.
intros.
firstorder.
Save.

Lemma intersect_left_empty: forall A (p:set A), intersect empty p = empty.
intros.
apply func_prop_ext.
firstorder.
Save.

Lemma intersect_right_empty: forall A (p:set A), intersect p empty = empty.
intros.
apply func_prop_ext.
firstorder.
Save.

Lemma intersect_full_full : forall A, intersect (full:set A) full = full.
intros.
apply func_prop_ext.
firstorder.
Save.

Lemma invert_union : forall (A:Type) (p : set A) (q : set A), invert (union p q) = intersect (invert p) (invert q).
intros.
apply func_prop_ext.
firstorder.
Save.

Notation "'all' x : s , P" := (forall x, s x -> P) (at level 20, x at level 99).
Notation "'some' x : s , P" := (exists x, s x /\ P) (at level 20, x at level 99).

Definition Union {A} (p : set (set A)) : set A := fun (x:A) => some s:p, s x.


Lemma member_powerset : forall A (a:set A) b, (powerset b) a <-> a <= b.
firstorder.
Save.

Definition comap {A} {B} (f : B -> A) (sa : set A) := {b:B | sa (f b)}.

Definition map {A} {B} (f : A -> B) (sa : set A) := {b:B| some a:sa, (f a = b)}.

Lemma map_union_powerset : forall A (a : set (set A)) (b : set (set A)), a <= b -> (map Union (powerset b)) (Union a).
firstorder.
Save.

