Require Import Ashley.Axioms.
Require Import Ashley.Logic.
(*
Require Import Ashley.Set.
Require Import Ashley.Topology.
Require Import Ashley.Function.
*)
Check O.
Check nat.
Check Set.
Check Type.
Check Prop.
Check gt.
Check S.
Check 34.
Check (3 > 0).
Check (0 = 0).
Check ((0 = 0) = (0 = 1)).
Check True.

Section Test.

Variables A B C : Prop.

Lemma abbcac: (A -> B) -> (B -> C) -> A -> C.
intro ab.
intro bc.
intro a.
apply bc.
apply ab.
apply a.
Save.

Lemma orc: A \/ B -> B \/ A.
intro ab.
elim ab.
clear ab.
right.
apply H.
left.
apply H.
Save.

Check orc.
Print orc.


Check bool.
Print bool.

End Test.


Parameter Other : Prop.
Axiom Tertium : ~~Other.

Lemma Tertium_collapse: Other.
assume_not.
apply Tertium.
apply H.
Save.

Definition pqr : Prop -> Prop -> Prop := fun a b => a \/ b.
Definition pqr1 : nat -> nat -> nat := fun a b => a + b.





Require Import Coq.Reals.Reals.

Print R.

Local Open Scope R_scope.

Definition zz : R := 0.

Check Rmax.
Print Rmax.

Class Fuzzy (F : Prop -> R) (very : Prop -> Prop) : Type :=
{
  fuzzy_lower_bound : forall a, F a >= 0;
  fuzzy_upper_bound : forall a, F a <= 1;
  fuzzy_false : F False = 0;
  fuzzy_implies : forall a b : Prop, F (a -> b) = 1 + (Rmin (F b - F a) 0);
  fuzzy_very: forall a, F (very a) = (F a) * (F a)
}.

Section Fuzzy.
Context `{fuzzy:Fuzzy}.

Lemma fuzzy_true : F True = 1.
transitivity (F (True -> True)).
cut ((True -> True) = True).
intros.
rewrite H.
trivial.
apply prop_ext.
split.
intros.
trivial.
intros.
trivial.
rewrite fuzzy_implies.

????.

auto.

Lemma fuzzy_not : forall a:Prop, F(~a) = 1 - F(a).
intros.
rewrite (fuzzy_implies a False).
rewrite fuzzy_false.
unfold Rmin.
auto.

Lemma fuzzy_and : forall a b:Prop, F(a /\ b) = Rmin (F a) (F b).
intros.



End Fuzzy.




Class Modal (U : Prop -> Prop) : Type :=
{
  modal_N1 : U True;
  modal_N2 : forall a b, (U a -> U b) -> U (a -> b);
  modal_K : forall (a:Prop) (b:Prop), U (a -> b) -> U a -> U b
}.

Section Modal.

Context `{M:Modal}.

Lemma thing: U (False -> True).

Lemma modal_collapse_with_prop_ext : forall a:Prop, a -> U a.
intros.
cut (a = True).
intros.
rewrite H0.
apply modal_N.
apply prop_ext.
split.
trivial.
intro.
apply H.
Save.


End Modal.
