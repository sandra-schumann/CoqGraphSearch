(** vim: set ts=2 sw=2 et : **)
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

Functional Scheme lookupEdgesAndRemove_ind := Induction for lookupEdgesAndRemove Sort Prop.

Ltac myinj H := injection H; clear H; intros; try subst.

Ltac mysimp := intros;
  match goal with 
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : None = Some _ |- _ ] => inversion H ; clear H ; subst
    | [ H : Some _ = Some _ |- _ ] => myinj H
    | [ H : (_, _) = (_, _) |- _ ] => myinj H
    | [ H : context[(fst ?x, snd ?x)] |- _ ] => destruct x
    | [ H : ?x <> ?x |- _ ] => destruct H
    | [ H : ?x = (_, _) |- _ ] => destruct x
  end.

Ltac pve :=
  match goal with 
    | [ H : _ |- _ ] => assumption
    | [ H : False |- _ ] => destruct H
    | [ H : ?P, H' : ~?P |- _ ] => destruct (H' H)
    | [ H : context[node_eq_dec ?x ?y] |- _ ] => destruct (node_eq_dec x y); repeat (mysimp; simpl in *; subst; eauto)
    | [ H : ?A |- ?A /\ _  ] => split; [apply A|]
    | [ H : ?A |- _  /\ ?A ] => split; [|apply A]
    | [ H : ?A |- ?A \/  _ ] => left; apply A
    | [ H : ?A |-  _ \/ ?A ] => right; apply A
    | [ H : context[let (_, _) := ?x in _] |- _ ] => destruct x
    (*| [ H : (match ?x with _ => Some _ | _ => None end = Some _) |- _ ] => destruct x*)
  end.

Ltac pv := repeat (
  intros; simpl in *;
  intros; try pve;
  intros; try mysimp;
  intros; eauto).

Lemma lookupEdgesAndRemove_node :
  forall (g:graph) (u v:node) (neighbors:list node) (g':graph),
  lookupEdgesAndRemove g u = Some (v, neighbors, g') -> u = v.
  intros until u.
  functional induction (lookupEdgesAndRemove g u); pv.
Qed.

Lemma lookupEdgesAndRemove_hasEdge :
  forall (g:graph) (u:node) (neighbors:list node) (g':graph),
  lookupEdgesAndRemove g u = Some (u, neighbors, g') ->
  forall v, In v neighbors -> hasEdge g u v.
  intros until u.
  functional induction (lookupEdgesAndRemove g u); pv.
  - unfold hasEdge; exists neighbors. pv.
  - unfold hasEdge; pv. elim (IHo _ _ e1 v0); pv.
Qed.

Lemma in_nodes : forall u vs g,  In (u, vs) g -> In u (nodes g).
  induction g; pv.
  destruct H; pv.
Qed.

Lemma lookupEdgesAndRemove_subgraph':
  forall (g:graph), NoDup (nodes g) ->
  forall u ret, lookupEdgesAndRemove g u = ret ->
  forall (g':graph) (neighbors:list node), ret = Some (u, neighbors, g') ->
  exists gBefore gAfter, g' = gBefore++gAfter /\ g = gBefore ++ [(u,neighbors)] ++ gAfter.
  intros until u.
  induction g. { exists [], []; subst; pv. }
  pv; subst; pv.
  - exists [], g'; pv.
  - destruct (lookupEdgesAndRemove g u); pv.
    assert (NoDup (nodes g)) as Hn by (
      replace (NoDup (nodes g)) with (NoDup ([]++nodes g)) by auto;
      eapply NoDup_remove_1; pv);
      elim (IHg Hn (Some (u,neighbors,g0)) eq_refl _ _ eq_refl); clear Hn IHg.
    intros x H0. destruct H0. destruct H0.
    exists (a::x), x0; subst; split; pv.
Qed.

Lemma lookupEdgesAndRemove_subgraph:
  forall (g:graph), NoDup (nodes g) ->
  forall (g':graph) (neighbors:list node),
  forall u, lookupEdgesAndRemove g u = Some (u, neighbors, g') ->
  exists gBefore gAfter, g' = gBefore++gAfter /\ g = gBefore ++ [(u,neighbors)] ++ gAfter.
  intros; elim (lookupEdgesAndRemove_subgraph' g H u (lookupEdgesAndRemove g u) eq_refl g' neighbors H0); pv.
Qed.

Lemma lookupEdgesAndRemove_NoDup:
  forall (g:graph), NoDup (nodes g) ->
  forall (g':graph) (neighbors:list node),
  forall u, lookupEdgesAndRemove g u = Some (u, neighbors, g') -> NoDup (nodes g').
  intros. elim (lookupEdgesAndRemove_subgraph g H g' neighbors u H0). intros.
  elim H1; clear H1; intros; destruct H1.
  specialize (NoDup_remove_1 (nodes x) (nodes x0) u); intro Hd; subst.
  replace (nodes (x ++ x0)) with (nodes x ++ nodes x0) by (symmetry; apply map_app).
  apply Hd.
  replace (nodes x ++ u :: nodes x0) with (nodes (x ++ [(u, neighbors)] ++ x0)); pv.
  apply map_app.
Qed.

Lemma hasEdge_lookupEdgesAndRemove:
  forall (g:graph), NoDup (nodes g) ->
  forall (u v:node), hasEdge g u v ->
  forall (neighbors:list node) (g':graph),
  lookupEdgesAndRemove g u = Some (u, neighbors, g') -> In v neighbors.
  induction g; [pv|].
  intros.
  assert (NoDup (nodes g)) by (
    replace (NoDup (nodes g)) with (NoDup ([]++nodes g)) by auto;
    eapply NoDup_remove_1; pv).
  simpl in H1. destruct (node_eq_dec (fst a) u). {
    pv. elim H0; clear H0; intros.
    destruct H0; destruct H0; [pv|].
    specialize (NoDup_remove_2 [] _ u H).
    specialize (in_nodes _ _ _ H0); pv.
  } {
    eapply IHg; clear IHg.
    - assumption.
    - elim H0; intros. destruct (lookupEdgesAndRemove g u); pv.
      destruct a; pv; simpl in *. destruct H3; pv.
      unfold hasEdge. exists x. apply (conj H1 H4).
    - destruct (lookupEdgesAndRemove g u); pv. repeat apply f_equal.
      (* FIXME: why does this not work??
      instantiate (1:=g0); reflexivity.
      *)
      instantiate (1:=nil); admit.
  }
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

Definition notSet (m:parent_t) (k:node) :=
    if node_in_dec k (map (@fst node node) m) then true else false.

Definition addToParent v neighbors parent :=
  fold_right (fun u pr => (u,v)::pr) parent (filter (notSet parent) neighbors).

Definition bfs_step (args : graph * list node * parent_t) :
  option (graph * list node * parent_t) :=
  let (args', parent) := args in let (g, frontier) := args' in
  match firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier with
  | None => None
  | Some (v, neighbors, g', frontier') => 
          Some (g', frontier', addToParent v neighbors parent)
end.

Function bfs (args : graph * list node * parent_t)
    {measure (fun args => length (fst (fst (args))))} : parent_t :=
  match bfs_step args with
  | None => let (_, parent) := args in parent
  | Some args' => bfs args'
end.
unfold bfs_step.
intros.
destruct args; destruct p; destruct args'; destruct p.
subst; simpl in *.
remember (firstForWhichSomeAndTail (lookupEdgesAndRemove g) l) as tup.
destruct tup; [|inversion teq].
destruct p; destruct p; destruct a.
injection teq; clear teq; intros; subst.
rewrite (remove_length _ _ _ _ _ _ (eq_sym Heqtup)); auto.
Defined.

Lemma bfs_parent_addonly :
  forall (g:graph) (frontier:list node) parent,
  forall args, args = (g,frontier, parent) ->
  forall ret, ret = bfs args ->
  forall u v, In (v, u) parent -> In (v, u) ret.
  intros until args. revert g frontier parent.
  functional induction (bfs args). {
    intros; destruct _x; myinj H. (* TODO: automate *)
    assumption.
  } {
    intros; subst.
    (* TODO: automate the following steps *)
    unfold bfs_step in e.
    remember ((firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier)) as stepOut.
    destruct stepOut. 
      Focus 2. inversion e.
    destruct p; destruct p; destruct a. myinj e.
    (* automate up to here *)
    eapply IHp; clear IHp; try reflexivity.
    assert (In (v, u) parent -> In (v, u) (addToParent n l0 parent)) by admit; auto.
  }
Qed.

Lemma bfs_no_alien_edges :
  forall (g0 g:graph) (frontier:list node) parent,
  forall args, args = (g,frontier, parent) ->
  forall ret, ret = bfs args ->
  forall u v, (In (v, u) parent -> hasEdge g0 u v) ->
              (In (v, u) ret    -> hasEdge g0 u v).
  intros until args. revert g frontier parent.
  functional induction (bfs args). {
    intros; destruct _x; myinj H; auto.
  } {
    intros; subst.
    (* TODO: automate something from here *)
    unfold bfs_step in e.
    remember ((firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier)) as stepOut.
    destruct stepOut. 
      Focus 2. inversion e.
    destruct p; destruct p; destruct a. myinj e.
    (* to here? *)
    eapply IHp; clear IHp; intros; try solve [reflexivity|auto].
    unfold firstForWhichSomeAndTail in *.
Abort.

Lemma bfs_graph_destruction' :
    forall g0  frontier0  parent0,  forall g1  frontier1  parent1,
 bfs_step (g0, frontier0, parent0) = Some (g1, frontier1, parent1) ->
  forall a, In a g1 -> In a g0.
Abort.

Lemma bfs_graph_destruction : forall (g:graph),
     forall g0  frontier0  parent0,  forall g1  frontier1  parent1,
  bfs_step (g0, frontier0, parent0) = Some (g1, frontier1, parent1) ->
  (forall a, In a g0 -> In a g) -> (forall a, In a g1 -> In a g).
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
Definition bfsAllPaths g s := let parent := bfs (g, s, []) in map (fun p => traceParent parent (fst p)) parent. 

Lemma bfs_parent_unchanged_after_done :
     forall g0  frontier0  parent0,  forall g1  frontier1  parent1,
  bfs_step (g0, frontier0, parent0) = Some (g1, frontier1, parent1) ->
  forall v, lookupEdgesAndRemove g0 v = None ->
  traceParent parent0 v = traceParent parent1 v.
Abort.

Lemma bfs_parent_new_edges_valid :
     forall g0  frontier0  parent0,  forall g1  frontier1  parent1,
  bfs_step (g0, frontier0, parent0) = Some (g1, frontier1, parent1) ->
  forall edge, ~ In edge parent0 -> In edge parent1 ->
  hasEdge g0 (fst edge) (snd edge).
Abort.

Lemma bfs_parent_all_edges_valid : forall g,
     forall g0  frontier0  parent0,  forall g1  frontier1  parent1,
  bfs_step (g0, frontier0, parent0) = Some (g1, frontier1, parent1) ->
  (forall e, In e parent0 -> hasEdge g (fst e) (snd e)) ->
  (forall e, In e parent1 -> hasEdge g (fst e) (snd e)).
Abort.

(** hasPath indicates that a path p is a valid path in a graph g **)
Inductive hasPath : graph -> path -> Prop :=
| IdPath : forall g n, In n (nodes g) -> hasPath g (n, [])
| ConsPath : forall g n n' r', hasEdge g n n' -> hasPath g (n, r') -> hasPath g (n', n::r').

Lemma bfs_parent_all_paths_valid : forall g,
     forall g0  frontier0  parent0,  forall g1  frontier1  parent1,
  bfs_step (g0, frontier0, parent0) = Some (g1, frontier1, parent1) ->
  (forall v, hasPath g (traceParent parent0 v)) -> 
  (forall v, hasPath g (traceParent parent1 v)).
Abort.

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

(** For every good graph g and initial frontier and node s,
    if s is in the frontier
    then for every node d, if d is reachable from s in g
    then bfs finds some path p from s to d. **)
Definition finds_path_from_frontier_if_reachable : Prop :=
  forall (g : graph), GoodGraph g ->
    exists (s : node) (frontier : list node), In s frontier ->
      forall (d : node), reachable s d g ->
        forall (p : path), p = traceParent (bfs (g, frontier, [])) d ->
          s = origin p /\ d = destination p.

Definition finds_the_shortest_path : Prop :=
  forall (g : graph), GoodGraph g ->
    forall (frontier : list node),
      forall (d : node) (p:path), p = traceParent (bfs (g, frontier, [])) d ->
        forall (p':path), In (origin p') frontier -> (destination p') = d ->
          length p <= length p'.

(** In order for bfs to be correct, all of the above conditions must hold. **)
Definition bfs_correct : Prop :=
  finds_legit_paths /\ finds_path_from_frontier_if_reachable  /\ finds_the_shortest_path.
