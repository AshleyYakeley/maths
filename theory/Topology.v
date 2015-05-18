Require Import Ashley.Axioms.
Require Import Ashley.PartialOrder.
Require Import Ashley.Set.
Require Import Ashley.SetFunction.
Require Import Ashley.Lattice.

Class Topology (A : Type) : Type :=
{
  open : set (set A);
  top_empty_is_open : open empty;
  top_full_is_open : open full;
  top_intersect_is_open : all a:open, all b:open, open (intersect a b);
  top_Union_is_open : forall ff, ff <= open -> open (Union ff)
}.

Definition topology_open {A} (top: Topology A) : set (set A) := @open _ top.

Definition open_type {A} (top: Topology A) := set_type open.

Definition open_val {A} {t: Topology A} (x: set A): open x -> open_type t := stc open x.

Definition topology_union {A} {top: Topology A} (u v: open_type top): open_type top.
apply (open_val (join (val u) (val v))).
case u.
case v.
intros.
unfold val.
unfold join.
unfold indexed_JoinSemilattice.
unfold join.
unfold prop_JoinSemilattice.
fold (union x0 x).
rewrite <- Union2.
apply top_Union_is_open.
unfold within. unfold indexed_Preorder.
unfold within. unfold prop_Preorder.
intros.
destruct H.
rewrite H.
apply o0.
rewrite H.
apply o.
Defined.


Instance open_JoinSemilattice `(top: Topology) : JoinSemilattice (open_type top) :=
{
  join := topology_union
}.
intros.
apply set_type_ext.
unfold topology_union.
unfold open_val.
unfold val.
case p.
case q.
case r.
intros.
firstorder.
apply join_associates.
intros.
apply set_type_ext.
unfold topology_union.
unfold open_val.
unfold val.
case p.
case q.
firstorder.
apply join_commutes.
intros.
apply set_type_ext.
unfold topology_union.
unfold open_val.
unfold val.
case p.
firstorder.
apply join_idem.
Defined.

Definition topology_intersect {A} {top: Topology A} (u v: open_type top): open_type top.
apply (open_val (meet (val u) (val v))).
case u.
case v.
unfold val.
intros.
apply top_intersect_is_open.
exact o0.
exact o.
Defined.

Instance open_MeetSemilattice `(top: Topology) : MeetSemilattice (open_type top) :=
{
  meet := topology_intersect
}.
intros.
apply set_type_ext.
unfold topology_intersect. unfold open_val. unfold val.
case p. case q. case r.
intros.
apply meet_associates.
intros.
apply set_type_ext.
unfold topology_intersect. unfold open_val. unfold val.
case p. case q.
intros.
apply meet_commutes.
intros.
apply set_type_ext.
unfold topology_intersect. unfold open_val. unfold val.
case p.
intros.
apply meet_idem.
Defined.

Instance open_Preorder `(top: Topology) : Preorder (open_type top) :=
{
  within a b := within (val a) (val b)
}.
intros.
apply within_reflex.
intros.
apply (within_trans (val p) (val q) (val r)).
exact H.
exact H0.
Defined.

Instance open_PartialOrder `(top: Topology) : PartialOrder (open_type top) :=
{
}.
intros.
apply within_antisym.
exact H.
exact H0.
Defined.



Lemma feq : forall {A} {B} {p q:A} (f:A -> B), p = q -> f p = f q.
intros.
rewrite H.
trivial.
Qed.


Lemma val_open: forall {A:Type} `{Topology A} (v:set A) (st:open v), val (open_val v st) = v.
intros.
unfold open_val.
apply val_stc.
Qed.


Instance open_Lattice `(top: Topology) : Lattice (open_type top) :=
{
}.
intros.
unfold within. unfold open_Preorder.
unfold join. unfold open_JoinSemilattice.
replace (topology_union p q = q) with (val (topology_union p q) = val q).
unfold topology_union. rewrite val_open.
apply join_within.
apply set_type_ext_eq.

intros.
unfold join. unfold open_JoinSemilattice.
unfold meet. unfold open_MeetSemilattice.
apply set_type_ext.
unfold topology_union.
unfold topology_intersect.
rewrite !val_open.
apply meet_join_absorbs.

intros.
unfold join. unfold open_JoinSemilattice.
unfold meet. unfold open_MeetSemilattice.
apply set_type_ext.
unfold topology_union.
unfold topology_intersect.
rewrite !val_open.
apply join_meet_absorbs.
Defined.

Definition topology_bottom {A} {t: Topology A}: open_type t.
apply (open_val bottom).
unfold bottom. unfold indexed_BoundedPartialOrder.
unfold bottom. unfold prop_BoundedPartialOrder.
apply top_empty_is_open.
Defined.

Definition topology_top {A} {t: Topology A}: open_type t.
apply (open_val top).
unfold top. unfold indexed_BoundedPartialOrder.
unfold top. unfold prop_BoundedPartialOrder.
apply top_full_is_open.
Defined.

Instance open_BoundedPartialOrder `(t: Topology) : BoundedPartialOrder (open_type t) :=
{
  bottom := topology_bottom;
  top := topology_top
}.
intros.
unfold within. unfold open_Preorder.
apply bottom_within.

intros.
unfold within. unfold open_Preorder.
apply top_without.
Defined.


Require Import Ashley.BoundedLattice.

Instance open_BoundedLattice `(t: Topology) : BoundedLattice (open_type t) :=
{
}.

Definition topology_Join {A} {t: Topology A} (uu: set (open_type t)): open_type t.
apply (open_val (Union (map val uu))).
apply top_Union_is_open.
unfold within. unfold indexed_Preorder.
unfold within. unfold prop_Preorder.
unfold map.
intros.
destruct H.
destruct H.
rewrite <- H0.
apply struct.
Defined.

Lemma Join_is_Union: forall {A} (f:set (set A)), Join f = Union f.
intros.
unfold Join. unfold indexed_SemicompleteBoundedLattice.
unfold Join. unfold prop_SemicompleteBoundedLattice.
unfold Union.
apply member_ext.
intros.
unfold map.
split.
intros.
destruct H.
exists x0.
destruct H.
split.
exact H.
rewrite H0.
trivial.
intros.
destruct H.
destruct H.
exists x0.
split.
exact H.
apply prop_ext.
firstorder.
Qed.

Instance open_SemicompleteBoundedLattice `(t: Topology) : SemicompleteBoundedLattice (open_type t) :=
{
  Join := topology_Join
}.
intros.
unfold within. unfold open_Preorder.
unfold topology_Join. rewrite val_open.
rewrite <- Join_is_Union.
apply Join_bound.
unfold map.
exists a.
firstorder.

intros.
unfold within. unfold open_Preorder.
unfold topology_Join. rewrite val_open.
unfold within in H. unfold open_Preorder in H.
rewrite <- Join_is_Union.
apply Join_least.
intros.
unfold map in H0.
destruct H0.
destruct H0.
rewrite <- H1.
apply (H x).
exact H0.
Defined.



(*
Instance top_empty {A} {top: Topology A}: set_type open :=
*)
Definition tunion {A} {top: Topology A} (u v: open_type top): open_type top := topology_union u v.

Instance discrete {A} : Topology A :=
{
  open := full
}.
apply all_full.
apply all_full.
intros.
apply all_full.
intros.
apply all_full.
Defined.

Instance indiscrete {A} : Topology A :=
{
  open := {s : set A | not_empty s -> is_full s}
}.
firstorder.
firstorder.
firstorder.
firstorder.
Defined.

Instance particular_point {A} (p:A) : Topology A :=
{
  open := {s : set A | not_empty s -> s p}
}.
firstorder.
firstorder.
firstorder.
firstorder.
Defined.

Definition sierpinski := particular_point True.

Notation "'all_open' x : t , P" := (all x : topology_open t, P) (at level 20, x at level 99).
Notation "'some_open' x : t , P" := (some x : topology_open t, P) (at level 20, x at level 99).

Class Continuous {A} {B} (TA : Topology A) (TB : Topology B) : Type :=
{
  f: A -> B;
  is_continuous: all_open sb: TB, topology_open TA {a : A|sb (f a)}
}.

Definition continuous_f {A} {B} {TA:Topology A} {TB:Topology B} (c: Continuous TA TB) := @f _ _ _ _ c.

Require Import Ashley.Proposition.

Lemma not_noncontinuous: forall (cont: Continuous sierpinski sierpinski), ~ continuous_f cont = not.
unfold sierpinski.
intro.
intro.
destruct cont.
unfold continuous_f in H.
unfold f in H.
unfold topology_open in is_continuous0.
rewrite H in is_continuous0.
clear H f0.
specialize (is_continuous0 {b:Prop|b}).
firstorder.
specialize (H False).
firstorder.
Defined.

Class Cover {A} `{SemicompleteBoundedLattice A} (s : A) : Type :=
{
  cover_sets : set A;
  covering : Join cover_sets >= s
}.

Definition OpenCover {A} (top : Topology A) (s : open_type top) : Type := Cover s.
