Require Import Ashley.Set.

Class topology {A : Type} (open_sets : set (set A)) : Type :=
{
  top_empty : member empty open_sets;
  top_full : member full open_sets;
  top_intersect : forall a b, member a open_sets -> member b open_sets -> member (intersect a b) open_sets;
  top_union : forall ff, subset ff open_sets -> member (Union ff) open_sets
}.

