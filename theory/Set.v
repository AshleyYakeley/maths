Require Import Ashley.Axioms.
Require Import Ashley.Proposition.
Require Import Ashley.PartialOrder.

Definition set (A : Type) := A -> Prop.

Notation "{ x : A | P }" := (fun x : A => P).

Lemma member_ext :  forall {A} a b, (forall x:A, a x <-> b x) -> a = b.
intros.
apply fun_ext.
intros.
apply prop_ext.
apply H.
Save.

Definition empty {A} := {x:A|False}.
Definition full {A} := {x:A|True}.
Definition singleton {A} p : set A := {x:A|x=p}.
Definition invert {A} p := {x:A|~ p x}.
Definition intersect {A} a b := {x:A|a x /\ b x}.
Definition union {A} a b := {x:A|a x \/ b x}.
Definition subset {A} (p : set A) (q : set A) := forall x, p x -> q x.

Definition superset {A} (p : set A) (q : set A) := subset q p.
Definition powerset {A} (p : set A) := {x:set A|x <= p}.

Definition not_empty {A} (p : set A) : Prop := exists x, p x.
Definition is_full {A} (p : set A) : Prop := forall x, p x.

Definition undisjoint {A} (a:set A) b : Prop := not_empty (intersect a b).
Definition disjoint {A} (a:set A) b : Prop := ~ undisjoint a b.

Lemma all_full : forall A (p : A), full p.
intros.
firstorder.
Save.

Lemma intersect_left_empty: forall A (p:set A), intersect empty p = empty.
intros.
apply member_ext.
firstorder.
Save.

Lemma intersect_right_empty: forall A (p:set A), intersect p empty = empty.
intros.
apply member_ext.
firstorder.
Save.

Lemma intersect_full_full : forall A, intersect (full:set A) full = full.
intros.
apply member_ext.
firstorder.
Save.

Lemma invert_union : forall (A:Type) (p : set A) (q : set A), invert (union p q) = intersect (invert p) (invert q).
intros.
apply member_ext.
firstorder.
Save.

Notation "'all' x : s , P" := (forall x, s x -> P) (at level 20, x at level 99).
Notation "'some' x : s , P" := (exists x, s x /\ P) (at level 20, x at level 99).

Definition Union {A} (p : set (set A)) : set A := {x:A|some s:p, s x}.

Lemma Union0: forall {A}, Union empty = (empty: set A).
intros.
unfold Union.
unfold empty.
apply member_ext.
firstorder.
Save.

Lemma Union1: forall {A} {p: set A}, Union (singleton p) = p.
intros.
apply member_ext.
unfold singleton.
firstorder.
rewrite <- H.
apply H0.
Save.
(*
Lemma UnionP1: forall {A} {pp: set (set A)} {q: set A}, Union (union pp (singleton q)) = union (Union pp) q.
intros.
unfold Union.
unfold union.
unfold singleton.
apply member_ext.
intros.
split.
intros.
destruct H.
destruct H.
firstorder.
exists x0.


left.

unfold some.
*)

Lemma Union2: forall {A} {p: set A} {q: set A}, Union {a : set A | a = p \/ a = q} = union p q.
intros.
unfold Union.
unfold union.
apply member_ext.
split.
intros.
destruct H.
destruct H.
destruct H.
left.
rewrite <- H.
apply H0.
right.
rewrite <- H.
apply H0.
intros.
destruct H.
exists p.
split.
left.
trivial.
apply H.
exists q.
split.
right.
trivial.
apply H.
Save.

Lemma member_powerset : forall A (a:set A) b, (powerset b) a <-> a <= b.
firstorder.
Save.

Definition comap {A} {B} (f : B -> A) (sa : set A): set B := {b:B | sa (f b)}.

Definition map {A} {B} (f : A -> B) (sa : set A): set B := {b:B| some a:sa, (f a = b)}.

Lemma map_union_powerset : forall A (a : set (set A)) (b : set (set A)), a <= b -> (map Union (powerset b)) (Union a).
firstorder.
Save.

Definition pair {A} p q: set A := {x:A|x=p \/ x=q}.

Lemma Union_pair: forall {A} (p q: set A), Union (pair p q) = union p q.
intros.
unfold Union.
unfold union.
unfold pair.
apply member_ext.
intros.
split.
intros.
destruct H.
destruct H.
case H.
intros.
left.
rewrite <- H1.
exact H0.
intros.
right.
rewrite <- H1.
exact H0.
intros.
case H.
intros.
exists p.
split.
left.
trivial.
exact H0.
intros.
exists q.
split.
right.
trivial.
exact H0.
Qed.

Lemma map_pair: forall {A} {B} (f: A -> B) (p q: A), map f (pair p q) = pair (f p) (f q).
intros.
unfold map.
unfold pair.
apply member_ext.
intros.
split.
intros.
destruct H.
destruct H.
case H.
intros.
left.
rewrite <- H0.
rewrite <- H1.
trivial.
intros.
right.
rewrite <- H0.
rewrite <- H1.
trivial.
intros.
case H.
intros.
exists p.
split.
left.
trivial.
rewrite <- H0.
trivial.
intros.
exists q.
split.
right.
trivial.
rewrite <- H0.
trivial.
Qed.

Lemma pair_same: forall {A} (x:A), pair x x = singleton x.
intros.
unfold pair.
unfold singleton.
apply member_ext.
intros.
firstorder.
Qed.
