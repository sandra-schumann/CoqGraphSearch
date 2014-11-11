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

Fixpoint lookupEdgesAndRemove (g:graph) (v:node) {struct g} : option (adj * graph) :=
  match g with
  | nil => None
  | x::g'' => if node_eq_dec (fst x) v
      then Some (x, g'')
      else match lookupEdgesAndRemove g'' v with
      | None => None
      | Some p => let (y, g') := p in Some (y, x::g')
      end
  end.

Lemma remove_length' : forall g a v neighbors g',
    lookupEdgesAndRemove g a = Some (v, neighbors, g') -> length g = S (length g').
  induction g; intros; [inversion H|].
  simpl in *. destruct (node_eq_dec (fst a) a0).
  - injection H; intros; subst; clear H. trivial.
  - case_eq (lookupEdgesAndRemove g a0); intros; rewrite H0 in *; [|inversion H].
    destruct p.
    injection H; intros; subst; clear H.
    apply f_equal; simpl.
    apply (IHg _ _ _ _ H0).
Qed.

Fixpoint firstForWhichSomeAndTail {A B:Type} (f:A->option B) (xs:list A) {struct xs} : option (B * list A) :=
  match xs with
  | nil => None
  | ox::xs' => match (f ox) with
    | None => firstForWhichSomeAndTail f xs'
    | Some x => Some (x, xs')
    end
  end. 

Lemma remove_length : forall g v neighbors frontier g' frontier',
  firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier = Some (v, neighbors, g', frontier') ->
  length g = S (length g').
  intros; subst; simpl.
  generalize dependent v. generalize dependent neighbors.
  induction frontier; intros; inversion H.
  case_eq (lookupEdgesAndRemove g a); intros.
  - rewrite H0 in H1.
    injection H1; clear H1; intros; subst.
    clear IHfrontier H.
    rewrite (remove_length' _ _ _ _ _ H0); auto.
  - eapply IHfrontier; clear IHfrontier.
    rewrite H0 in H1. rewrite H1. auto.
Qed.

Function bfs'''' (args : graph * list node * parent_t)
    {measure (fun args => length (fst (fst (args))))} : parent_t := 
  let (args', parent) := args in let (g, frontier) := args' in
  match firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier
      with None => parent | Some (v, neighbors, g', frontier') =>
  let parent' := map (fun u => (u,v)) neighbors ++ parent in
  bfs'''' (g', frontier', parent')
end.
  intros; subst; simpl.
  rewrite (remove_length _ _ _ _ _ _ teq1); auto.
Qed.
Definition bfs' g frontier := bfs'''' (g, frontier, nil).

Fixpoint bfs'' (len_g:nat) (g:graph) (frontier : list node) (parent:parent_t)
    {struct len_g} : option parent_t := 
  match firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier
    with None => Some parent | Some (((v, neighbors), g'), frontier') =>
  let parent' := map (fun u => (u,v)) neighbors ++ parent in
  match len_g with 0 => None | S len_g' => bfs'' len_g' g' frontier' parent'
end end.
Definition bfs''' g frontier := bfs'' (length g) g frontier nil.

Ltac neqConstructor := simpl; unfold not; intro H_; inversion H_.

Lemma bfs_terminates : forall g frontier, bfs''' g frontier <> None.
  unfold bfs'''.
  intros g frontier.
  remember ([]) as parent; clear Heqparent.
  remember (length g) as l.
  generalize Heql; clear Heql.
  generalize dependent parent.
  generalize dependent frontier.
  generalize dependent g.
  induction l; intros; subst.
    Focus 1. destruct g; [|inversion Heql]. simpl. induction frontier; neqConstructor. auto.
  simpl.
  case_eq (firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier); intros; [|neqConstructor].
  destruct p; destruct p; destruct a.
  eapply IHl.
  specialize (remove_length _ _ _ _ _ _ H); intro H'.
  rewrite <- Heql in H'.
  auto.
Qed.

Definition bfs (g:graph) (frontier:list node) : parent_t.
  remember (bfs''' g frontier) as ret.
  destruct ret.
  - apply p.
  - destruct (bfs_terminates _ _ (eq_sym Heqret)).
Qed.

Example ex1 : (bfs [(Node 0,[Node 1])] [Node 0]) = [(Node 1, Node 0)].
  compute. (* Why does it not work? *)
Abort.

Inductive path : Type :=
  | Starts : node -> path
  | Cons : path -> node -> path.

Definition hasEdge (g : graph) (n1 n2 : node) : Prop :=
  exists (neighbors : list node), In (n1, neighbors) g /\ In n2 neighbors.

Fixpoint length (p : path) : nat :=
  match p with
    | Starts _ => 0
    | Cons p' _ => S(length p')
  end.

Fixpoint startNode (p : path) : node :=
  match p with
    | Starts n => n
    | Cons p' _ => startNode p'
  end.

Definition endNode (p : path) : node :=
  match p with
    | Starts n => n
    | Cons _ n => n
  end.

Definition nodes (g : graph) := edgeStarts g. (* TODO: dummy *)

(* Fixpoint hasPath (g : graph) (p : path) : Prop :=
     match p with
       | Starts n => In n (nodes g)
       | Cons p' n => match p' with
                        | Starts n' => hasEdge g n' n
                        | Cons _ n' => hasEdge g n' n /\ hasPath g p'
                      end
     end.*)

Inductive hasPath : graph -> path -> Prop :=
| IdPath : forall g n, In n (nodes g) -> hasPath g (Starts n)
| ConsPath : forall g n n' p', hasPath g p' ->
             endNode p' = n -> hasEdge g n n' -> hasPath g (Cons p' n').

Definition reachable (startn : node) (endn : node) (g : graph) : Prop :=
  exists (p : path), hasPath g p /\ startNode p = startn /\ endNode p = endn.

Definition paths_from_parents (p:parent_t) : list path :=
  nil. (* TODO: put the real def in *)

(* Tõestada: kui paths_from_parents väljastab pathi, siis path_in_graph.
   Tõestada: kui paths_from_parents väljastab pathi, siis In frontier (startNode p) *)

(* Pseudocode:
bfs is correct if
  for all graphs g, initial frontiers, two nodes n1 and n2 in g
    if n1 is in the initial frontier and n2 is reachable from n1
    then exists a path p such that bfs finds this path
      and the startnode is n1 and endnode n2
      and for all other paths p' in this graph with same start and end
        the length (cost) of p' is greater or equal to the length of p
(also note that the path found by bfs is in g by above)
*)

Definition bfs_finds_shortest : Prop :=
  forall (g : graph) (frontier : list node) (n1 : node) (n2 : node),
    In n1 frontier -> reachable n1 n2 g ->
    exists (p : path), In p (paths_from_parents (bfs g frontier)) /\
      n1 = startNode p /\ n2 = endNode p /\
      (forall (p' : path), n1 = startNode p' ->
         n2 = endNode p' -> path_in_graph p' g ->
         length p' >= length p).

(* Tõestada: kõik, mis BFS leiab, on lühimad *)