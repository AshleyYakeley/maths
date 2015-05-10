Require Import Ashley.Axioms.

Lemma not_or : forall a b, ~ (a \/ b) <-> (~a) /\ (~b).
firstorder.
Save.

Lemma and_true_true : True /\ True <-> True.
firstorder.
Save.

Lemma and_left_false : forall a, False /\ a <-> False.
firstorder.
Save.

Lemma and_right_false : forall a, a /\ False <-> False.
firstorder.
Save.

Lemma not_not : forall a, ~~a <-> a.
firstorder.
destruct (exclude_middle a).
firstorder.
firstorder.
Save.

Ltac assume_not := apply not_not; intro.

Lemma imply_or_left : forall p q x : Prop, (p -> q) /\ (p \/ x) -> q \/ x.
firstorder.
Save.

Lemma not_and : forall p q, ~ (p /\ q) <-> (~p \/ ~q).
firstorder.
assume_not.
firstorder.
Save.

Lemma imply_left_or : forall {p : Prop} {q : Prop} (a : p -> q) x, p \/ x -> q \/ x.
firstorder.
Save.

Lemma imply_or_right : forall p q x : Prop, (p -> q) /\ (x \/ p) -> x \/ q.
firstorder.
Save.

Lemma imply_right_or : forall {p : Prop} {q : Prop} (a : p -> q) x, x \/ p -> x \/ q.
firstorder.
Save.

Lemma equiv_not : forall p q, (~p <-> ~q) <-> (p <-> q).
intros.
split.
destruct (exclude_middle p) as [Hp|Hnp].
destruct (exclude_middle q) as [Hq|Hnq].
firstorder.
firstorder.
firstorder.
firstorder.
Save.

Lemma prop_true_or_false: forall (p : Prop), (p = True) \/ (p = False).
intros.
apply (imply_or_left p).
split.
intros.
apply prop_ext.
firstorder.
apply (imply_or_right (~ p)).
split.
intros.
apply prop_ext.
firstorder.
apply exclude_middle.
Save.

Lemma exists_not : forall A (p:A -> Prop), (exists b : A, ~ p b) -> ~ (forall a : A, p a).
firstorder.
Save.

Lemma forall_not : forall A (p:A -> Prop), (forall a : A, ~ p a) -> ~ (exists b : A, p b).
firstorder.
Save.

Lemma not_exists : forall A (p:A -> Prop), ~ (exists b : A, p b) -> (forall a : A, ~ p a).
firstorder.
Save.

Lemma not_forall_not : forall A (p:A -> Prop), ~ (forall a : A, ~ p a) -> (exists b : A, p b).
firstorder.
assume_not.
firstorder.
Save.

Lemma not_forall : forall A (p:A -> Prop), ~ (forall a : A, p a) -> (exists b : A, ~ p b).
intros.
apply not_forall_not.
intro.
elim H.
intro.
apply not_not.
apply H0.
Save.
