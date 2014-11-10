Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Wf.
Require Import Arith.Wf_nat.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import Recdef.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

Inductive node := Node : nat -> node.

Definition node_eq_dec : forall (x y:node), {x = y} + {x <> y}.
  decide equality. apply eq_nat_dec.
Qed.
Definition node_in_dec := in_dec node_eq_dec.

Definition adj := (node * list node)%type.
Definition graph := list adj.

Definition edgeStarts (g:graph) : list node := map (@fst node (list node)) g.
Definition GoodGraph g := NoDup (edgeStarts g).
Definition parent_t := list (node * node).

Definition edgesFrom (g:graph) (v:node) := find (fun a => if node_eq_dec (fst a) v then true else false) g.

Definition isNone {A:Type} (oa:option A) := match oa with None => true | _ => false end.

Fixpoint filterSome {A:Type} (xs:list (option A)): list A :=
  match xs with
  | nil => nil
  | ox::xs' => match ox with
    | None => filterSome xs'
    | Some x => x::filterSome xs'
  end
end.

Fixpoint bfs (g:graph) (frontier : list node) (parent:parent_t) : parent_t. refine(
    let frontierAdjs := filterSome (map (edgesFrom g) frontier) in
    match frontierAdjs with nil => parent | adjv::frontierAdjs' =>
        let (v, neighbours) := adjv in
        let frontier' := map (@fst node (list node)) frontierAdjs ++ _ in
        let parent' := _ ++ parent in
        bfs g frontier' parent'
    end
).