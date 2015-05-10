Require Import Ashley.Axioms.
Require Import Ashley.PartialOrder.
Require Import Ashley.Set.
Require Import Ashley.Category.


(* set_type takes a set and turns it into a type *)
Inductive set_type {A:Type} (s:A -> Type) : Type :=
  stc : forall (x:A), s x -> set_type s.

Definition val {A: Type} {s: A -> Type} (sv: set_type s): A.
destruct sv.
exact x.
Defined.

Definition stc' : forall {A:Type} {s:A -> Type} (x:A), s x -> set_type s.
intros.
apply (stc s x X).
Defined.

Definition struct {A} {s:A -> Type} (st:set_type s): s (val st).
unfold val.
destruct st.
exact s0.
Defined.

(*
Inductive same (A B: Type) (a:A) (b:B): Type:=
  is_same: forall (T:Type) (a' b':A), a' = b' -> same T T a' b'.
*)
Definition converter: forall {T:Type} {A B: T} {f: T -> Type}, (A = B) -> f A -> f B.
intros.
rewrite <- H.
exact X.
Defined.

Lemma converter_eq: forall {T} {A} {f: T -> Type} {proof} (x: f A), converter proof x = x.
intros.
unfold converter. unfold eq_rect.
cut (proof = eq_refl).
intro.
rewrite H.
trivial.
apply proof_irrelevance.
Qed.

Lemma exist_ext: forall {A} (s: A -> Type) (p q: set_type s) (proof: val p = val q),
  ((converter proof (struct p)) = struct q) -> p = q.
intros.
destruct p.
destruct q.
unfold val in proof.
subst x.
unfold converter in H.
unfold struct in H.
unfold val in H.
unfold eq_rect in H.
rewrite H.
trivial.
Defined.

Lemma set_type_ext: forall {A} (s: A -> Prop) (p q: set_type s), (val p = val q) -> p = q.
intros.
apply (exist_ext s p q H).
apply proof_irrelevance.
Defined.


Variable Te : Type.
Variable Ve : Te.
Definition Se : set Te := fun x => x = Ve.

Definition eConstruct: set_type Se.
apply (stc Se Ve).
unfold Se.
trivial.
Defined.

Lemma eCheck: val eConstruct = Ve.
unfold eConstruct.
unfold val.
trivial.
Qed.



Instance subset_category A : Category (set A) :=
{
  hom sA sB := set_type sA -> set_type sB;
  id A := (fun p => p);
  compose A B C mbc mab a := mbc (mab a)
}.
intros.
apply fun_ext.
trivial.
intros.
apply fun_ext.
trivial.
intros.
apply fun_ext.
trivial.
Defined.

Lemma not_in_empty : forall A, forall a : set_type (empty : set A), False.
firstorder.
Qed.

Lemma subset_transitive : forall {A} {a b c: set A}, b <= c -> a <= b -> a <= c.
unfold subset.
intro.
intro.
intro.
intro.
apply within_trans.
Qed.

Instance inclusion_PartialOrder {A} (open : set (set A)) : PartialOrder (set_type open) :=
{
  within sv1 sv2 := (val sv1) <= (val sv2)
}.
intros.
apply within_reflex.
intros.
apply set_type_ext.
apply within_antisym.
exact H.
exact H0.
intros.
apply (within_trans (val p) (val q) (val r)).
exact H.
exact H0.
Defined.

Definition inclusion_category {A} (open : set (set A)) : Category (set_type open) :=
  PartialOrder_Category (inclusion_PartialOrder open).

Definition subset_type {A} (s : set A) : Type := set_type (superset s).
