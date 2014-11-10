Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Wf.
Require Import Arith.Wf_nat.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import Recdef.
Require Import Coq.Arith.Peano_dec.
Require Import Program.
Import ListNotations.

Inductive node : Type := Node : nat -> node.
Inductive edge : Type := Edge : node -> node -> edge.

Definition fst (e : edge) : node :=
  match e with (Edge n _) => n end.

Definition snd (e : edge) : node :=
  match e with (Edge _ n) => n end.

Definition node_eq_dec : forall (x y:node), {x = y} + {x <> y}.
  decide equality. apply eq_nat_dec.
Qed.

Definition graph := list edge.

Definition undirected (g : graph) : Prop :=
  forall (e:edge), In e g -> match e with (Edge n1 n2) => In (Edge n2 n1) g end.

Fixpoint nodes_in_graph (g : graph) : list node :=
  match g with
    | [] => []
    | (Edge n1 n2)::t => n1::n2::(nodes_in_graph t)
  end.

Inductive path : Type :=
  | Starts : node -> path
  | Cons : path -> node -> path.

Fixpoint path_in_graph (p : path) (g : graph) : Prop :=
  match p with
    | Starts n => In n (nodes_in_graph g)
    | Cons p' n => match p' with
                     | Starts n' => In (Edge n' n) g
                     | Cons _ n'   => In (Edge n' n) g /\ path_in_graph p' g
                   end
  end.

Fixpoint length (p : path) : nat :=
  match p with
    | Starts _ => 0
    | Cons p' _ => 1 + length p'
  end.

Definition cost (p : path) : nat := length p.

Fixpoint startnode (p : path) : node :=
  match p with
    | Starts n => n
    | Cons p' _ => startnode p'
  end.

Fixpoint endnode (p : path) : node :=
  match p with
    | Starts n => n
    | Cons _ n => n
  end.

Definition reachable (n1 : node) (n2 : node) (g : graph) : Prop :=
  exists (p : path), path_in_graph p g /\ startnode p = n1 /\ endnode p = n2.

Definition queue (A:Type) : Type := list A.

Definition push {A:Type} (a : A) (q : queue A) : queue A := q ++ [a].
Definition top {A:Type} (q : queue A) : option A :=
  match q with
    | [] => None
    | h::_ => Some h
  end.
Definition pop {A:Type} (q : queue A) : option (queue A) :=
  match q with
    | [] => None
    | _::t => Some t
  end.

Fixpoint in_list (i : node) (ns : list node) : bool :=
  match ns with
    | [] => false
    | h::t => if node_eq_dec h i then true else in_list i t
  end.

Definition BFS_step (g : graph) (ps : list path) : list path :=
  let is_next_step (p : path) (e : edge) :=
    if node_eq_dec (endnode p) (fst e) then true else false
  in

  let extend_path (p : path) (e : edge) :=
    Cons p (snd e)
  in
  
  let extend_path_to_paths (g : graph) (p : path) :=
    map (extend_path p) (filter (is_next_step p) g)
  in
  
  flat_map (extend_path_to_paths g) ps.

Fixpoint BFS_n_steps (g : graph) (n : node) (i : nat) : list path :=
  let is_beginning_in_graph :=
    fold_right (fun x => orb (if node_eq_dec x n then true else false))
      false (nodes_in_graph g)
  in
  
  match i with
    | 0 => match is_beginning_in_graph with
             | true => [Starts n]
             | _ => []
           end
    | S i' => BFS_step g (BFS_n_steps g n i')
  end.

