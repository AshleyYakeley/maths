Require Import Ashley.Logic.

Class ModalK (prop:Type) `{HasFalse prop} : Type :=
{
  necessarily: prop -> prop;
  ruleN: forall (p: prop), judge p -> judge (necessarily p);
  ruleK: forall (p q: prop), judge (implies (necessarily (implies p q)) (implies (necessarily p) (necessarily q)))
}.

Definition possibly {prop: Type} `{ModalK prop} (p: prop) : prop := notL (necessarily (notL p)).

(* model logic collapses when "p" and "necessarily p" are the same. *)
Definition modal_collapse (prop:Type) `{ModalK prop} := forall (p: prop), judge (implies p (necessarily p)).

(*
Lemma functorish_n_collapse: forall (prop:Type) `{ModalK prop},
  (forall (a b:prop), judge (implies (implies a b) (implies (necessarily a) (necessarily b)))) -> modal_collapse prop.
intros.
unfold modal_collapse.
intros.
destruct H0.
*)

Class ModalT (prop:Type) `{ModalK prop} : Type :=
{
  ruleT: forall (p:prop), judge (implies (necessarily p) p)
}.

Class ModalS4 (prop:Type) `{ModalT prop} : Type :=
{
  rule4: forall (p:prop), judge (implies (necessarily p) (necessarily (necessarily p)))
}.

Class ModalS5 (prop:Type) `{ModalS4 prop} : Type :=
{
  rule5: forall (p:prop), judge (implies (possibly p) (necessarily (possibly p)))
}.

Class ModalD (prop:Type) `{ModalK prop} : Type :=
{
  ruleD: forall (p:prop), judge (implies (necessarily p) (possibly p))
}.