Require Import Ashley.Logic.

Class Modal (prop:Type) `{Implication prop} `{HasFalse prop} : Type :=
{
  necessarily: prop -> prop;
  ruleN: forall (p: prop), judge p -> judge (necessarily p);
  ruleK: forall (p q: prop), judge (implies (necessarily (implies p q)) (implies (necessarily p) (necessarily q)))
}.

Definition possibly {prop: Type} `{Modal prop} (p: prop) : prop := notL (necessarily (notL p)).

(* model logic collapses when "p" and "necessarily p" are the same. *)
Definition modal_collapse (prop:Type) `{Modal prop} := forall (p: prop), judge (implies p (necessarily p)).

(*
Lemma functorish_n_collapse: forall (prop:Type) `{Modal prop},
  (forall (a b:prop), judge (implies (implies a b) (implies (necessarily a) (necessarily b)))) -> modal_collapse prop.
intros.
unfold modal_collapse.
intros.
destruct H0.
*)