Axiom prop_ext: forall A B:Prop, (A <-> B) -> A = B.
Axiom fun_ext: forall (A:Type) (B:Type) (f:A -> B) (g:A -> B), (forall x:A, f x = g x) -> f = g.
Axiom exclude_middle: forall (p : Prop), p \/ ~p.
Axiom choice: forall A B (p: A -> B -> Prop), (forall a, exists b, p a b) -> exists f, forall a, p a (f a).
Axiom proof_irrelevance: forall (P:Prop) (p1:P) (p2:P), p1 = p2.
