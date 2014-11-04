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
  | Starts : node -> node -> path
  | Cons : path -> node -> path.

Fixpoint path_in_graph (p : path) (g : graph) : Prop :=
  match p with
    | Starts n1 n2 => In (Edge n1 n2) g
    | Cons p' n => match p' with
                     | Starts _ n' => In (Edge n' n) g /\ path_in_graph p' g
                     | Cons _ n'   => In (Edge n' n) g /\ path_in_graph p' g
                   end
  end.

Fixpoint length (p : path) : nat :=
  match p with
    | Starts _ _ => 1
    | Cons p' _ => 1 + length p'
  end.

Definition cost (p : path) : nat := length p.

Fixpoint startnode (p : path) : node :=
  match p with
    | Starts n _ => n
    | Cons p' _ => startnode p'
  end.

Fixpoint endnode (p : path) : node :=
  match p with
    | Starts _ n => n
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

Fixpoint in_list (i : node) (n : list node) : bool :=
  match n with
    | [] => false
    | h::t => if node_eq_dec h i then true else in_list i t
  end.

Fixpoint BFS' (g : graph) (target : node) (q : queue path) (visited : list node) : option path :=
  match (top q) with
    | None => None
    | Some p => if node_eq_dec (endnode p) target then Some p
                else BFS' g target
                  (q ++ fold_right (filter (fun (x:edge) =>
                   match x with Edge n1 n2 =>
                   if (node_eq_dec n1 (endnode p)) then
                     if negb (in_list n2 (n1::visited)) then true else false
                   else false
                   end) g))
                   []
                  ((endnode p)::visited)
  end.










