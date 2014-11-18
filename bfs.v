Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Wf.
Require Import Arith.Wf_nat.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import Recdef.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

(** Defining a way of representing a graph. First we define a node, which will
    be uniquely identified by a natural number. The way nodes are represented
    in a graph is by a structure called adj, which includes a node and
    additionally the list of nodes adjacent to it. A graph is a list of adjs. **)

Inductive node := Node : nat -> node.

Definition node_eq_dec : forall (x y:node), {x = y} + {x <> y}.
  decide equality. apply eq_nat_dec.
Defined.
Definition node_in_dec := in_dec node_eq_dec.

Definition adj := (node * list node)%type.
Definition graph := list adj.

(** nodes g gives all the first parts of adjs in a graph g (list of nodes) **)
Definition nodes (g:graph) : list node := map (@fst node (list node)) g.

(** hasEdge says that in graph g, there exists an edge between nodes n1 and n2 **)
Definition hasEdge (g : graph) (n1 n2 : node) : Prop :=
  exists (neighbors : list node), In (n1, neighbors) g /\ In n2 neighbors.

(** Graph is a GoodGraph, if it has no two adjs that correspond to the same node
    and if there is an edge from node u to v  in a graph, then there exists
    an adj construction for v in g. **)
Definition GoodGraph g := NoDup (nodes g) /\ forall u v, hasEdge g u v -> In v (nodes g).

(** parent_t is a data structure for indicating for a list of nodes their "parents".
    A "parent" of a node will be used in the bfs function: essentially if bfs
    finds some node v by looking at nodes adjacent to some node u, then u is the
    parent of v. **)
Definition parent_t := list (node * node).

(** [lookupEdgesAndRemove] locates the adjacency list of node [v] in graph [g]
 and removes it from the graph. If [v]'s adjacency list is not a part of [g]
 (possibly because a previous call to this function removed it), [None] is
 returned. **)
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

(** A graph with an adjacency list removed is smaller than the original **)
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

(** [firstForWhichSomeAndTail] computes the following two expressions (or [None] if [head] fails):
    -  [fromMybe (head (dropWhile isNone (map f xs)))]
    -  [tail (dropWhile (isNone . f) xs)]
**)
Fixpoint firstForWhichSomeAndTail {A B:Type} (f:A->option B) (xs:list A) {struct xs} : option (B * list A) :=
  match xs with
  | nil => None
  | ox::xs' => match (f ox) with
    | None => firstForWhichSomeAndTail f xs'
    | Some x => Some (x, xs')
    end
  end. 

(** A graph with any adjacency list removed is smaller than the original **)
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

Definition bfs_funcstep (args : graph * list node * parent_t) :
  option (graph * list node * parent_t) :=
  let (args', parent) := args in let (g, frontier) := args' in
  match firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier with
  | None => None
  | Some (v, neighbors, g', frontier') => Some (g', frontier',
               fold_right (fun u pr => (u,v)::pr) parent neighbors)
end.

Function bfs_function' (args : graph * list node * parent_t)
    {measure (fun args => length (fst (fst (args))))} : parent_t :=
  let oargs := bfs_funcstep args in
  match bfs_funcstep args with
  | None => let (_, parent) := args in parent
  | Some args' => bfs_function' args'
end.



(** One [bfs] iteration takes a node from the frontier, removes its adjecency
 list from the graph and adds all nodes in that list to the frontier while also
 remembering the current node as their parent. **)
(** This implementation uses [Coq]'s [Function] to define BFS, but as the body
   is not a tree of matches, we still don't get [functional induction], so it
   may not be worthwhile **)
Function bfs_function' (args : graph * list node * parent_t)
    {measure (fun args => length (fst (fst (args))))} : parent_t := 
  let (args', parent) := args in let (g, frontier) := args' in
  match firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier with
  | None => parent
  | Some (v, neighbors, g', frontier') => bfs_function' (g', frontier',
               fold_right (fun u pr => (u,v)::pr) parent neighbors)
end.
  intros; subst; simpl.
  rewrite (remove_length _ _ _ _ _ _ teq1); auto.
Qed.
Definition bfs_function g frontier := bfs_function' (g, frontier, nil).

(** This implementation uses defines BFS using fuel. Later, we prove that the
  length of the graph is sufficient fuel and thus the return type does not need
  to be [option]. **)
Fixpoint bfs' (len_g:nat) (g:graph) (frontier : list node) (parent:parent_t)
    {struct len_g} : option parent_t := 
  match firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier with
  | None => Some parent
  | Some (((v, neighbors), g'), frontier') =>
      match len_g with
      | 0 => None
      | S len_g' => bfs' len_g' g' frontier'
               (fold_right (fun u pr => (u,v)::pr) parent neighbors)
end end.

Ltac neqConstructor := simpl; unfold not; intro H_; inversion H_.
Lemma bfs_terminates : forall g frontier, bfs' (length g) g frontier nil <> None.
  intros g frontier.
  remember ([]) as parent; clear Heqparent.
  remember (length g) as l.
  generalize Heql; clear Heql.
  generalize dependent parent.
  generalize dependent frontier.
  generalize dependent g.
  induction l; intros; subst. {
    Focus 1. destruct g; [|inversion Heql]. simpl.
    induction frontier; neqConstructor. auto.
  } {
    simpl.
    case_eq (firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier);
      intros; [|neqConstructor].
    destruct p; destruct p; destruct a.
    eapply IHl.
    specialize (remove_length _ _ _ _ _ _ H); intro H'.
    rewrite <- Heql in H'.
    auto.
  }
Qed.

Definition bfs (g:graph) (frontier:list node) : parent_t.
  remember (bfs' (length g) g frontier nil) as ret.
  destruct ret.
  - apply p.
  - destruct (bfs_terminates _ _ (eq_sym Heqret)).
Defined.

Example ex1 : (bfs [(Node 0,[Node 1])] [Node 0]) = [(Node 1, Node 0)].
  reflexivity.
Qed.

Lemma no_aliens : forall g s parent, bfs g s = parent ->
    forall u v, In (u, v) parent -> hasEdge g u v.
Abort.

(** A path is essentially a list of nodes representing a series of edges
    leading from one node (the origin) to another (the destination).
    The part of the path leading up to the destination (meaning all of
    it without the last node) is in this implementation called the route.
    The length of a path is the number of edges in the path, or alternatively
    the number of nodes minus one. This way the length of a path leading
    from a node to itself is 0, a path with just two nodes on it has length 1
    and so on. **)
Definition path := (node * list node)%type.
Definition destination (p:path) := fst p.
Definition route (p:path) := snd p.
Definition length (p : path) : nat := length (route p).
Definition origin (p : path) : node := last (route p) (destination p).

(** This assumes that the statement (u's parent is v) comes before any statement
 about v's parents. This is true in out BFS implementation, and will probably
 remain true for any extension of it, but it is not an integral property of BFS
 -- it is just a requirement on the output format. We could get rid of this
 requirement, but then the termination argument for traceParent would depend on
 the assumption that parsing the parent map does not lead to cyclic paths.  We
 plan to prove things about the output of traceParent when it is run on the
 output of bfs, so the division of labor between the two should not matter a
 whole lot. **)
Fixpoint traceParent' (parent:parent_t) (u:node) {struct parent} : list node :=
  match parent with
  | nil => []
  | p::parent' =>
    if node_eq_dec (fst p) u
    then (snd p)::(traceParent' parent' (snd p))
    else traceParent' parent' u
end.
Definition traceParent (parent:parent_t) (u:node) := (u, traceParent' parent u).
Definition bfsAllPaths g s := let parent := bfs_function g s in map (fun p => traceParent parent (fst p)) parent. 

Example ex2 :
  traceParent' [(Node 3, Node 2); (Node 2, Node 0); (Node 1, Node 0)] (Node 3) =
  [Node 2; Node 0].
  reflexivity.
Qed.

(** hasPath indicates that a path p is a valid path in a graph g **)
Inductive hasPath : graph -> path -> Prop :=
| IdPath : forall g n, In n (nodes g) -> hasPath g (n, [])
| ConsPath : forall g n n' r', hasEdge g n n' -> hasPath g (n, r') -> hasPath g (n', n::r').

(** node endn is reachable from node startn if there exists a path from
    startn to endn in a graph g **)
Definition reachable (startn : node) (endn : node) (g : graph) : Prop :=
  exists (p : path), hasPath g p /\ origin p = startn /\ destination p = endn.


(** The following section defines the correctness of BFS. **)

(** For every good graph g and starting frontier,
    if bfs finds path p, then this path exists in g
    and its origin is one of the nodes in the frontier. **)
Definition finds_legit_paths : Prop :=
  forall (g : graph), GoodGraph g ->
    forall (frontier : list node) (p : path), In p (bfsAllPaths g frontier) ->
      hasPath g p /\ In (origin p) frontier.

(** For every good graph g and two nodes s and d,
    if d is not reachable from s in g
    then there does not exist a way for bfs to find a path from s to d.
    More specifically, we can say that if we run bfs with some frontier
    and it finds some path, then if this path starts from s,
    it cannot possibly end in d. **)
Definition does_not_find_nonlegit_paths : Prop :=
  forall (g : graph), GoodGraph g ->
    forall (s : node) (d : node), ~(reachable s d g) ->
      forall (frontier : list node) (p : path),
        In p (bfsAllPaths g frontier) -> s = origin p -> d <> destination p.

(** For every good graph g and two nodes s and d,
    if d is reachable from s in g
    then if we run bfs with some frontier and get out a path p from s to d
    then bfs does not find some different path p' from s to d.
    That is, bfs finds maximum of one path from s to d. **)
Definition finds_max_one_path_per_pair : Prop :=
  forall (g : graph), GoodGraph g ->
    forall (s : node) (d : node), reachable s d g ->
      forall (frontier : list node) (p : path),
        In p (bfsAllPaths g frontier) -> s = origin p -> d = destination p ->
        forall (p' : path), s = origin p' -> d = destination p' ->
          p <> p' -> ~(In p' (bfsAllPaths g frontier)).

(** For every good graph g and initial frontier and node s,
    if s is in the frontier
    then for every node d, if d is reachable from s in g
    then bfs finds some path p from s to d. **)
Definition finds_min_one_path_from_frontier_if_reachable : Prop :=
  forall (g : graph), GoodGraph g ->
    forall (s : node) (frontier : list node), In s frontier ->
      forall (d : node), reachable s d g ->
        exists (p : path), s = origin p /\ d = destination p /\
          In p (bfsAllPaths g frontier).

(** For every good graph g and two nodes s and d,
    if d is reachable from s in g
    then for every initial frontier and path p,
    if bfs finds p given that frontier and g
    and the origin of path is s and destination d
    then every path in g from s to d is longer or same length than p. **)
Definition finds_the_shortest_path : Prop :=
  forall (g : graph), GoodGraph g ->
    forall (s : node) (d : node), reachable s d g ->
      forall (frontier : list node) (p : path),
        In p (bfsAllPaths g frontier) -> s = origin p -> d = destination p ->
        forall (p' : path), hasPath g p' -> s = origin p' -> d = destination p'
          -> length p' >= length p.

(** In order for bfs to be correct, all of the above conditions must hold. **)
Definition bfs_correct : Prop :=
  finds_legit_paths /\ does_not_find_nonlegit_paths /\
  finds_max_one_path_per_pair /\ finds_min_one_path_from_frontier_if_reachable
  /\ finds_the_shortest_path.
