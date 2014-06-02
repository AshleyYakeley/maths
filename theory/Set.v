Require Import Ashley.Logic.

Inductive set (A : Type) : Type := mk_set (is_member : A -> Prop).
Definition member {A : Type} (x : A) (p : set A) := let (im) := p in im x.

Lemma unmember : forall A im x, member x (mk_set A im) = im x.
intros.
unfold member.
trivial.
Save.

Definition empty {A} := mk_set A (fun x => False).
Definition full {A} := mk_set A (fun x => True).
Definition invert {A} p := mk_set A (fun x => not (member x p)).
Definition intersect {A} a b := mk_set A (fun x => and (member x a) (member x b)).
Definition union {A} a b := mk_set A (fun x => or (member x a) (member x b)).
Definition superset {A} (p : set A) (q : set A) := forall x, member x p -> member x q.
Definition subset {A} (p : set A) (q : set A) := forall x, member x q -> member x p.
Definition powerset {A} (p : set A) := mk_set (set A) (superset p).

Lemma invert_union : forall (A:Type) (p : set A) (q : set A), invert (union p q) = intersect (invert p) (invert q).
intros.
unfold invert.
unfold intersect.
unfold union.
assert (forall m n, m = n -> mk_set A m = mk_set A n).
intros.
rewrite H.
trivial.
apply H.
clear H.
apply funky.
intro.
rewrite unmember.
rewrite unmember.
rewrite unmember.
apply not_or.
Save.

Definition Union {A} (p : set (set A)) : set A := mk_set A (fun x => exists (s : set A), member s p /\ member x s).