Require Import Ashley.Axioms.
Require Import Ashley.PartialOrder.
Require Import Ashley.Lattice.
Require Import Ashley.Set.


(*
Class BoundedJoinSemilattice (A:Type) `{JoinSemilattice A} :=
{
  bottom: A;
  join_bottom: forall (p:A), join bottom p = p
}.

Class BoundedMeetSemilattice (A:Type) `{MeetSemilattice A} :=
{
  top: A;
  meet_top: forall (p:A), meet top p = p
}.

Class BoundedLattice (A:Type) `{BoundedJoinSemilattice A} `{BoundedMeetSemilattice A} `{Lattice A} :=
{
}.
*)

Class BoundedLattice (A:Type) `{Lattice A} {bl_bpo:BoundedPartialOrder A}.
(* need to name BoundedPartialOrder parameter to avoid death by diamond *)

Lemma join_bottom: forall {A:Type} `{BoundedLattice A} (p:A), join bottom p = p.
intros.
rewrite <- join_within.
apply bottom_within.
Qed.

Lemma meet_top: forall {A:Type} `{BoundedLattice A} (p:A), meet top p = p.
intros.
rewrite meet_commutes.
rewrite <- meet_within.
apply top_without.
Qed.

Lemma join_top: forall {A:Type} `{BoundedLattice A} (p:A), join top p = top.
intros.
rewrite <- (meet_top p).
apply join_meet_absorbs.
Qed.

Lemma meet_bottom: forall (A:Type) `{BoundedLattice A} (p:A), meet bottom p = bottom.
intros.
rewrite <- (join_bottom p).
apply meet_join_absorbs.
Qed.

Instance indexed_BoundedLattice (I:Type) (A:Type) `{BoundedLattice A} : BoundedLattice (I -> A) :=
{
}.

Class SemicompleteBoundedLattice (A:Type) `{BoundedLattice A} :=
{
  Join: set A -> A;
  Join_bound: forall (f: set A), all a: f, (a <= Join f);
  Join_least: forall (f: set A), forall (p:A), all a: f, (a <= p) -> Join f <= p
}.
(*
Lemma join_least: forall `{Lattice} p q r, (p <= r) /\ (q <= r) -> (join p q <= r).
Lemma Join_least: forall `{Lattice} p q r, (q <= p) /\ (r <= p) -> (Join f <= p).

  Join_least: forall (f: set A), forall (p:A), p <= Join f -> (all a: f, (a <= p)) -> Join f = p
*)


Lemma Join_empty: forall `{SemicompleteBoundedLattice}, Join empty = bottom.
intros.
apply within_antisym.
apply Join_least.
intros.
unfold empty in H6.
contradiction H6.
apply bottom_within.
Qed.

Lemma Join_single: forall `{SemicompleteBoundedLattice} (x: A), Join (singleton x) = x.
intros.
apply within_antisym.
apply Join_least.
unfold singleton.
intros.
rewrite H6.
apply within_reflex.
apply Join_bound.
unfold singleton.
trivial.
Qed.

Lemma Join_union: forall `{SemicompleteBoundedLattice} p q, Join (union p q) = join (Join p) (Join q).
intros.
apply within_antisym.
apply Join_least.
unfold union.
intros.
destruct H6.
apply join_left. apply Join_bound. exact H6.
apply join_right. apply Join_bound. exact H6.
apply join_least.
split.
apply Join_least.
intros.
apply Join_bound.
unfold union.
left.
exact H6.
apply Join_least.
intros.
apply Join_bound.
unfold union.
right.
exact H6.
Qed.

Instance indexed_SemicompleteBoundedLattice (I:Type) (A:Type) `{SemicompleteBoundedLattice A} : SemicompleteBoundedLattice (I -> A) :=
{
  Join ss i := Join (map (fun ia => ia i) ss)
}.
intros.
unfold map.
unfold within.
unfold indexed_Preorder.
intros.
apply Join_bound.
exists a.
split.
exact H6.
trivial.
intros.
unfold map.
unfold within.
unfold indexed_Preorder.
intros.
apply Join_least.
intros.
destruct H7.
destruct H7.
rewrite <- H8.
unfold within in H6.
unfold indexed_PartialOrder in H6.
exact (H6 x H7 i).
Defined.


Require Import Ashley.Proposition.

Instance prop_BoundedLattice: BoundedLattice Prop :=
{
}.

Lemma isTrue : forall {a:Prop} (proof:a), a = True.
intros.
apply prop_ext.
firstorder.
Qed.

Instance prop_SemicompleteBoundedLattice: SemicompleteBoundedLattice Prop :=
{
  Join f := f True
}.
unfold within. unfold prop_Preorder.
intros.
rewrite <- (isTrue H0).
exact H.

unfold within. unfold prop_Preorder.
intros.
apply (H True).
exact H0.

trivial.
Defined.