Require Import Ashley.Set.
Require Import Ashley.Category.
Require Import Ashley.SetFunction.
Require Import Ashley.Topology.

Definition Presheaf {A} {open : set (set A)} (top : topology open) {O} {M} (cat : Category O M) :=
 ContraFunctor (inclusion_category open) cat.
(*
Class Sheaf {A} {open : set (set A)} (top : topology open) {O} {M} (cat : Category O M) `{Presheaf top cat} : Type :=
*)

Definition topology_union {A} {open : set (set A)} {top : topology open} (u : stype open) (v : stype open) : stype open.
apply (sval (set A) open (union (val open u) (val open v))).
apply top_union.
apply (ins open u).
apply (ins open v).
Defined.


Category A
O = stype open, objects are pairs
M o1 o2 = Prop



Class SetSheaf {A} {open : set (set A)} (top : topology open) (B : Type) `{Presheaf top (subset_category B)} : Type :=
{
  sheaf_locality:
forall u v : stype open,
forall s t : comapO (topology_union u v),
(
(comapM (sval u) (sval (union u v)) (u <= union u v) s = comapM (sval u) (sval (union u v)) (u <= union u v) t)
 /\ 
(comapM (sval v) (sval (union u v) )(v <= union u v) s = comapM (sval v) (sval (union u v)) (v <= union u v) t)
) -> s = t
(*
uv := union u v

comapM (u <= uv) : M (comapO uv) (comapO u)


s = t;
  sheaf_condition:
    forall (o1, o2 :O) (m : M o1 o2), 

comapM m : comapO o2 -> comapO o1
comapO o1 : set S
comapO o2 : set S
*)
}.
