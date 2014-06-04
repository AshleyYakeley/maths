Require Import Ashley.Axioms.
Require Import Ashley.Logic.
Require Import Ashley.Set.

Class topology {A : Type} (open : set (set A)) : Type :=
{
  top_empty : open empty;
  top_full : open full;
  top_intersect : all a:open, all b:open, open (intersect a b);
  top_union : forall ff, ff <= open -> open (Union ff)
}.

Instance discrete_topology (A : Type) : topology (full : set (set A)) :=  {}.
apply all_full.
apply all_full.
intros.
apply all_full.
intros.
apply all_full.
Save.

Instance indiscrete_topology (A : Type) : topology ({s : set A | s = empty \/ s = full}) := {}.
left.
trivial.
right. trivial.
intros.
destruct H as [Hae|Haf].
left.
rewrite Hae.
apply intersect_left_empty.
rewrite Haf.
destruct H0 as [Hbe|Hbf].
left.
rewrite Hbe.
apply intersect_right_empty.
right.
rewrite Hbf.
apply intersect_full_full.

unfold subset.
intros.

unfold empty.
unfold full.
assume_not.

cut ((exists a, Union ff a) /\ (exists b, ~ Union ff b)).
clear H0.
intros.
destruct H0 as [Hm Hnm].
destruct Hm as [a Hma].
destruct Hnm as [b Hnb].
unfold Union in Hma.
destruct Hma as [s Hffssa].
destruct Hffssa as [Hffs Hsa].
unfold Union in Hnb.
cut (s = empty \/ s = full).
intro.
destruct H0 as [Hse|Hsf].
rewrite Hse in Hsa.
unfold empty in Hsa.
contradiction Hsa.
firstorder.
apply (H0 s).
split.
apply Hffs.
rewrite Hsf.
unfold full.
trivial.
apply H.
apply Hffs.

clear H.
firstorder.
clear H0.
assume_not.
elim H. clear H.
apply func_prop_ext.
firstorder.
clear H.
assume_not.
elim H0. clear H0.
apply func_prop_ext.
split.
trivial.
intro.
firstorder.
assume_not.
apply (H x).
apply H1.
Save.

Instance point_topology (A : Type) (p:A) : topology ({s : set A | s = empty \/ s p}) := {}.
firstorder.
firstorder.
firstorder.
left.
rewrite H.
apply intersect_left_empty.
left.
rewrite H.
apply intersect_left_empty.
left.
rewrite H0.
apply intersect_right_empty.
firstorder.
unfold subset in H.
destruct (lem (all x : ff, (x = empty))).
clear H.
left.
unfold Union.
apply func_prop_ext.
firstorder.
cut (x0 = empty).
intro.
rewrite H2 in H1.
apply H1.
apply (H0 x0).
apply H.

right.
unfold Union.
assume_not.
elim H0. clear H0.
intros.
destruct (H x).
apply H0.
apply H2.
clear H.
elim H1. clear H1.
exists x.
split.
apply H0.
apply H2.
Save.




