Require Import Ashley.Logic.

Instance indexed_Judge (I:Type) (A:Type) `{Judge A}: Judge (I -> A) :=
{
  judge s := forall (i:I), judge (s i);
  true i := true
}.
destruct H.
firstorder.
Defined.

Instance indexed_Implication (I:Type) (A:Type) `{Implication A}: Implication (I -> A) :=
{
  implies p q i := implies (p i) (q i)
}.
destruct H.
destruct H0.
unfold Logic.judge.
unfold indexed_Judge.
intros.
apply (implication (p i) (q i)).
apply (H i).
apply (H0 i).

destruct H.
destruct H0.
unfold Logic.judge.
unfold indexed_Judge.
intros.
apply (implies_lift (p i) (q i)).
apply (H i).

destruct H.
destruct H0.
unfold Logic.judge.
unfold indexed_Judge.
intros.
apply (implies_identity (p i)).

destruct H.
destruct H0.
unfold Logic.judge.
unfold indexed_Judge.
intros.
apply (implies_compose (p i) (q i) (r i)).
apply (H i).
apply (H0 i).

Defined.

Instance indexed_HasFalse (I:Type) (A:Type) `{HasFalse A}: HasFalse (I -> A) :=
{
  false i := false
}.
destruct H1.
unfold judge.
unfold indexed_Judge.
unfold implies.
unfold indexed_Implication.
unfold Logic.false.
intros.
apply (ex_falso (p i)).
Defined.
