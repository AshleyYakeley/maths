Require Import Ashley.Logic.
Require Import Ashley.Logic.Indexed.
Require Import Ashley.Logic.Modal.
Require Import Ashley.Logic.Prop.

Class Worlds  {I:Type} (rel: I -> I -> Prop): Type :=
{
  wval: I -> Prop
}.

Instance toWorlds {I:Type} {rel: I -> I -> Prop} (v:I -> Prop) : Worlds rel :=
{
  wval:= v
}.

Definition fromWorlds {I:Type} {rel: I -> I -> Prop} (worlds: Worlds rel) : I -> Prop := @wval I rel worlds.

Instance Worlds_Judge {I:Type} (rel: I -> I -> Prop) : Judge (Worlds rel) :=
{
  judge s := judge (fromWorlds s);
  true := toWorlds true
}.
apply judge_true.
Defined.

Lemma fromToWorlds: forall {I:Type} (rel: I -> I -> Prop) (v: I -> Prop), fromWorlds ((toWorlds v) : Worlds rel) = v.
intros.
unfold fromWorlds.
unfold wval.
unfold toWorlds.
trivial.
Save.

Lemma judgeToWorlds: forall {I:Type} (rel: I -> I -> Prop) (v: I -> Prop), judge ((toWorlds v) : Worlds rel) = judge v.
intros.
unfold judge at 1. unfold Worlds_Judge.
rewrite fromToWorlds.
trivial.
Save.

Instance Worlds_Implication {I:Type} (rel: I -> I -> Prop) : Implication (Worlds rel) :=
{
  implies p q := toWorlds (implies (fromWorlds p) (fromWorlds q))
}.
intros.
rewrite judgeToWorlds in H.
apply (implication (fromWorlds p)).
exact H.
exact H0.

intros.
rewrite judgeToWorlds.
apply implies_lift.
exact H.

intros.
rewrite judgeToWorlds.
apply implies_identity.

intros.
rewrite judgeToWorlds.
rewrite judgeToWorlds in H.
rewrite judgeToWorlds in H0.
apply (implies_compose (fromWorlds p) (fromWorlds q) (fromWorlds r)).
exact H.
exact H0.
Defined.

Instance Worlds_HasFalse {I:Type} (rel: I -> I -> Prop) : HasFalse (Worlds rel) :=
{
  false := toWorlds false
}.
intros.
unfold judge. unfold Worlds_Judge.
unfold implies. unfold Worlds_Implication.
rewrite fromToWorlds.
rewrite fromToWorlds.
apply ex_falso.
Defined.

Instance Worlds_Consistent {I:Type} (i:I) (rel: I -> I -> Prop) : Consistent (Worlds rel) :=
{
}.
unfold judge. unfold Worlds_Judge.
unfold false. unfold Worlds_HasFalse.
rewrite fromToWorlds.
apply @consistent.
apply indexed_Consistent.
apply i.
apply Prop_Consistent.
Defined.

Instance indexed_ModalK {I:Type} (rel: I -> I -> Prop): ModalK (I -> Prop) :=
{
  necessarily s i := forall (j:I), rel i j -> judge (s j)
}.
unfold judge.
unfold indexed_Judge.
unfold judge.
unfold Prop_Judge.
intros.
apply (H j).

unfold implies.
unfold indexed_Implication.
unfold implies.
unfold Prop_Implication.
unfold judge.
unfold indexed_Judge.
unfold judge.
unfold Prop_Judge.
intros.
apply (H j).
apply H1.
apply (H0 j).
apply H1.
Defined.

Variable I:Type.
Variable rel: I -> I -> Prop.
Variable s: Worlds rel.
Check fromWorlds s.
Check toWorlds (@necessarily (I -> Prop) (indexed_Judge I Prop) (indexed_Implication I Prop) (indexed_HasFalse I Prop) (indexed_ModalK rel) (fromWorlds s)).

(*
Check @necessarily.
Print Implicit (necessarily (prop := I -> Prop)).


 (Worlds_Judge rel) (Worlds_Implication rel) (Worlds_HasFalse rel).


Check @fromWorlds.
Check @toWorlds.

Check @necessarily.
*)

Instance Worlds_ModalK {I:Type} (rel: I -> I -> Prop): ModalK (Worlds rel) :=
{
  necessarily s := toWorlds (@necessarily (I -> Prop) (indexed_Judge I Prop) (indexed_Implication I Prop) (indexed_HasFalse I Prop) (indexed_ModalK rel)necessarily (fromWorlds s))
}.



Require Import Ashley.Proposition.
Require Import Ashley.Logic.Bool.

Variable I:Type.
Definition rel_all : I -> I -> Prop := fun (_:I) _ => true.
Check @modal_collapse (Worlds rel_all) (Worlds_Judge rel_all) (Worlds_Implication rel_all) (Worlds_HasFalse rel_all) (Worlds_ModalK rel_all).

Lemma bool_Worlds_Robust: forall {I:Type}, ~ modal_collapse (Worlds (fun (_:I) _ => true)).
unfold modal_collapse.
unfold necessarily.
unfold Worlds_ModalK.
unfold implies.
unfold indexed_Implication.
unfold implies.
unfold Prop_Implication.
unfold judge.
unfold indexed_Judge.
unfold judge.
unfold Prop_Judge.

apply exists_not.
exists (fun (x:bool) => if x then True else False).
apply exists_not.
exists (true:bool).
simpl.
intro.
firstorder.
destruct (H false).
Save.