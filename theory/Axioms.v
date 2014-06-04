(*
Axiom extensionality : forall (A:Type) (B:Type) (f:A->B)(g:A ->B), (forall x:A, f x = g x) -> f = g.
*)

Axiom func_prop_ext : forall (A:Type) (f:A -> Prop) (g:A -> Prop), (forall x:A, f x <-> g x) -> f = g.

Lemma prop_ext : forall A B:Prop, (A <-> B) -> A = B.
intros.
assert ((fun _ : unit => A) = (fun _ : unit => B)).
apply (func_prop_ext unit (fun x => A) (fun x => B)).
intro.
apply H.
assert (forall (f : unit -> Prop) g, f = g -> f tt = g tt).
intros.
rewrite H1.
trivial.
rewrite (H1 (fun _ : unit => A) (fun _ : unit => B)).
trivial.
apply H0.
Save.

Axiom lem : forall (p : Prop), p \/ ~p.