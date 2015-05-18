Require Import Ashley.Axioms.
Require Import Ashley.PartialOrder.

Class JoinSemilattice (A:Type) :=
{
  join: A -> A -> A;
  join_associates: forall (p q r: A), join p (join q r) = join (join p q) r;
  join_commutes: forall (p q: A), join p q = join q p;
  join_idem: forall (p: A), join p p = p
}.

Class MeetSemilattice (A:Type) :=
{
  meet: A -> A -> A;
  meet_associates: forall (p q r: A), meet p (meet q r) = meet (meet p q) r;
  meet_commutes: forall (p q: A), meet p q = meet q p;
  meet_idem: forall (p: A), meet p p = p
}.

Class Lattice (A:Type) `{PartialOrder A} `{JoinSemilattice A} `{MeetSemilattice A}:=
{
  join_within: forall (p q: A), (p <= q) = (join p q = q);
  meet_join_absorbs: forall (p q: A), meet p (join p q) = p;
  join_meet_absorbs: forall (p q: A), join p (meet p q) = p
}.

Lemma meet_within_left: forall `{Lattice} {p q}, meet p q <= p.
intros.
rewrite join_within.
rewrite join_commutes.
apply join_meet_absorbs.
Qed.

Lemma meet_within_right: forall `{Lattice} {p q}, meet p q <= q.
intros.
rewrite meet_commutes.
apply meet_within_left.
Qed.

Lemma within_join_left: forall `{Lattice} {p q}, p <= join p q.
intros.
rewrite join_within.
rewrite join_associates.
rewrite join_idem.
trivial.
Qed.

Lemma within_join_right: forall `{Lattice} {p q}, q <= join p q.
intros.
rewrite join_commutes.
apply within_join_left.
Qed.

Lemma meet_within: forall {A} `{Lattice A} (p q: A), (p <= q) = (meet p q = p).
intros.
rewrite join_within.
apply prop_ext.
split.
intro.
rewrite <- H4.
apply meet_join_absorbs.
intro.
rewrite <- H4.
rewrite join_commutes.
rewrite meet_commutes.
apply join_meet_absorbs.
Qed.

Lemma join_least: forall `{Lattice} p q r, (p <= r) /\ (q <= r) -> (join p q <= r).
intros.
destruct H4.
rewrite join_within.
rewrite <- join_associates.
rewrite join_within in H4.
rewrite join_within in H5.
rewrite H5.
exact H4.
Qed.

Lemma meet_least: forall `{Lattice} p q r, (r <= p) /\ (r <= q) -> (r <= meet p q).
intros.
destruct H4.
rewrite meet_within.
rewrite meet_associates.
rewrite meet_within in H4.
rewrite meet_within in H5.
rewrite H4.
exact H5.
Qed.

Lemma join_left: forall `{Lattice} p q r, (r <= p) -> (r <= join p q).
intros.
rewrite join_within.
rewrite join_within in H4.
rewrite join_associates.
rewrite H4.
trivial.
Qed.

Lemma join_right: forall `{Lattice} p q r, (r <= q) -> (r <= join p q).
intros.
rewrite join_commutes.
apply join_left.
exact H4.
Qed.


Instance indexed_JoinSemilattice (I:Type) (A:Type) `{JoinSemilattice A} : JoinSemilattice (I -> A) :=
{
  join p q i := join (p i) (q i)
}.
intros.
apply fun_ext.
intros.
apply join_associates.
intros.
apply fun_ext.
intros.
apply join_commutes.
intros.
apply fun_ext.
intros.
apply join_idem.
Defined.

Instance indexed_MeetSemilattice (I:Type) (A:Type) `{MeetSemilattice A} : MeetSemilattice (I -> A) :=
{
  meet p q i := meet (p i) (q i)
}.
intros.
apply fun_ext.
intros.
apply meet_associates.
intros.
apply fun_ext.
intros.
apply meet_commutes.
intros.
apply fun_ext.
intros.
apply meet_idem.
Defined.

Instance indexed_Lattice (I:Type) (A:Type) `{Lattice A} : Lattice (I -> A) :=
{
}.
intros.
unfold join.
unfold indexed_JoinSemilattice.
unfold within.
unfold indexed_Preorder.
apply prop_ext.
split.
intros.
apply fun_ext.
intros.
rewrite <- join_within.
apply H4.
intros.
rewrite join_within.
rewrite <- H4.
rewrite join_associates.
rewrite join_idem.
trivial.
intros.
apply fun_ext.
intros.
apply meet_join_absorbs.
intros.
apply fun_ext.
intros.
apply join_meet_absorbs.
Defined.


Require Import Ashley.Proposition.

Instance prop_JoinSemilattice: JoinSemilattice Prop :=
{
  join p q := p \/ q
}.
intros.
apply prop_ext.
firstorder.
intros.
apply prop_ext.
firstorder.
intros.
apply prop_ext.
firstorder.
Defined.

Instance prop_MeetSemilattice: MeetSemilattice Prop :=
{
  meet p q := p /\ q
}.
intros.
apply prop_ext.
firstorder.
intros.
apply prop_ext.
firstorder.
intros.
apply prop_ext.
firstorder.
Defined.

Instance prop_Lattice: Lattice Prop :=
{
}.
intros.
apply prop_ext.
split.
intros.
unfold join. unfold prop_JoinSemilattice.
unfold within in H. unfold prop_PartialOrder in H.
apply prop_ext.
firstorder.
intros.
unfold within. unfold prop_PartialOrder.
unfold join in H. unfold prop_JoinSemilattice in H.
firstorder.
rewrite <- H.
left.
exact H0.
intros.
unfold meet. unfold join.
unfold prop_MeetSemilattice. unfold prop_JoinSemilattice.
apply prop_ext.
firstorder.
intros.
unfold meet. unfold join.
unfold prop_MeetSemilattice. unfold prop_JoinSemilattice.
apply prop_ext.
firstorder.
Defined.
