Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Wf.
Require Import Arith.Wf_nat.
Require Import Recdef.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

Inductive Node := Node_ : nat -> Node.
Inductive Adj := Adj_ : Node -> list Node -> Adj.
Definition Graph := list Adj.

Definition node_eq_dec : forall (x y:Node), {x = y} + {x <> y}.
  decide equality. apply eq_nat_dec.
Qed.

Definition nodes (G:Graph) : list Node :=
    map (fun adj => match adj with Adj_ v _ => v end) G.

Lemma len_nodes_gen_g : forall G, length (nodes G) = length G.
    unfold nodes. apply map_length .
Qed.

(* Do we need this??
Definition GoodGraph G :=
    (forall v A, In (Adj_ v A) G -> forall u, In u A -> In u (nodes G)).
Example EmptyGraphGood : GoodGraph []. unfold GoodGraph; auto. Qed.
*)

Definition getOutgoing (v:Node) (G:Graph) : option Adj :=
    find (fun a => match a with Adj_ u _ =>
        if node_eq_dec u v then true else false
    end) G.

Definition removeOutgoing (v:Node) (G:Graph) : Graph :=
    filter (fun a => match a with Adj_ u _ =>
        if node_eq_dec u v then true else false
    end) G.

Lemma nodes_removeOutgoing : forall v G,
    nodes (removeOutgoing v G) = filter (fun u => if node_eq_dec u v then fa.
    unfold nodes. apply map_length .
Qed.


(* The graph, the frontier, the mapping from a node to its parent *)
Definition BFSState := (Graph * list Node * list (Node * Node))%type.
Definition BFSmeasure (s:BFSState) := (* |V| + |E| unexpanded *)
    let (ss, parent) := s in let (G, frontier) := ss in
    let adjEdges := fun a => match a with Adj_ v l => length l end in
    length frontier +
    length G +
    fold_right plus 0 (map adjEdges G).

Function bfs (s:BFSState) {measure BFSmeasure} : list (Node * Node) :=
    let (ss, parents) := s in let (G, frontier) := ss in
    match frontier with nil => parents | v::frontier' =>
    if in_dec node_eq_dec v (nodes G) then
        let G' := removeOutgoing v G in
        let W := getOutgoing v G in
        match W with None => [] | Some (Adj_ _ dstNodes) =>
        let set_parent := fun u prnts => prnts ++ [(u,v)] in (* only if not present? *)
        let parents' := fold_right set_parent parents dstNodes in
        bfs(G', (frontier' ++ dstNodes), parents')
        end
    else bfs(G, frontier', parents)
end.

(* Proof that the recursion terminates *)
intros.
assert (  In v (nodes G)) by auto.
assert (~ In v (nodes (removeOutgoing v G))).
    unfold removeOutgoing. unfold nodes. filter_In.
assert (length (removeOutgoing v G) < length G). auto.
auto.
