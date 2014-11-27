(** vim: set ts=2 sw=2 et : **)
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Wf.
Require Import Arith.Wf_nat.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import Recdef.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
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
Definition node_in_decb v vs := if in_dec node_eq_dec v vs then true else false.
Lemma node_in_decb_true : forall v vs, node_in_decb v vs = true -> In v vs.
  unfold node_in_decb; intros. destruct (in_dec node_eq_dec v vs); auto; inversion H. Qed.
Lemma node_in_decb_false : forall v vs, node_in_decb v vs = false -> ~ In v vs.
  unfold node_in_decb; intros. destruct (in_dec node_eq_dec v vs); auto; inversion H. Qed.

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
    | [ H : Some _ = None |- _ ] => inversion H ; clear H ; subst
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

Lemma lookupEdgesAndRemove_hasEdge' :
  forall (g:graph) (u:node) (neighbors:list node) (g':graph),
  lookupEdgesAndRemove g u = Some (u, neighbors, g') ->
  forall v, In v neighbors -> hasEdge g u v.
  intros until u.
  functional induction (lookupEdgesAndRemove g u); pv.
  - unfold hasEdge; exists neighbors. pv.
  - unfold hasEdge; pv. elim (IHo _ _ e1 v0); pv.
Qed.

Lemma lookupEdgesAndRemove_hasEdge :
  forall (g:graph) (u u':node) (neighbors:list node) (g':graph),
  lookupEdgesAndRemove g u = Some (u', neighbors, g') ->
  forall v, In v neighbors -> hasEdge g u v.
  intros.
  replace u' with u in *.
  apply (lookupEdgesAndRemove_hasEdge' _ _ _ _ H _ H0).
  apply (lookupEdgesAndRemove_node _ _ _ _ _ H).
Qed.

Lemma in_nodes : forall u vs g,  In (u, vs) g -> In u (nodes g).
  induction g; pv.
  destruct H; pv.
Qed.

Lemma lookupEdgesAndRemove_subgraph':
  forall (g:graph),
  forall u ret, lookupEdgesAndRemove g u = ret ->
  forall (g':graph) (neighbors:list node), ret = Some (u, neighbors, g') ->
  exists gBefore gAfter, g' = gBefore++gAfter /\ g = gBefore ++ [(u,neighbors)] ++ gAfter.
  intros until u.
  induction g. { exists [], []; subst; pv. }
  pv; subst; pv.
  - exists [], g'; pv.
  - destruct (lookupEdgesAndRemove g u); pv.
      elim (IHg (Some (u,neighbors,g0)) eq_refl _ _ eq_refl); clear IHg.
    intros x H0. destruct H0. destruct H.
    exists (a::x), x0; subst; split; pv.
Qed.

Lemma lookupEdgesAndRemove_subgraph:
  forall (g:graph),
  forall (g':graph) (neighbors:list node),
  forall u, lookupEdgesAndRemove g u = Some (u, neighbors, g') ->
  exists gBefore gAfter, g' = gBefore++gAfter /\ g = gBefore ++ [(u,neighbors)] ++ gAfter.
  intros; elim (lookupEdgesAndRemove_subgraph' g u (lookupEdgesAndRemove g u) eq_refl g' neighbors H); pv.
Qed.

Lemma lookupEdgesAndRemove_subgraph_hasEdge:
  forall (g:graph),
  forall (g':graph) (neighbors:list node),
  forall n, lookupEdgesAndRemove g n = Some (n, neighbors, g') ->
  (forall u v, hasEdge g' u v -> hasEdge g u v).
  intros.
  elim (lookupEdgesAndRemove_subgraph _ _ _ _ H); pv.
  elim H1; clear H1; intros.
  unfold hasEdge in *.
  elim H0; clear H0; intros.
  econstructor; split.
  destruct H1.
  subst.
  destruct H0.
  specialize (in_app_or _ _ _ H0); intros.
  apply in_or_app.
  destruct H2; [left|right;right]; eauto.
  destruct H0; pv.
Qed.

Lemma lookupEdgesAndRemove_NoDup:
  forall (g:graph), NoDup (nodes g) ->
  forall (g':graph) (neighbors:list node),
  forall u, lookupEdgesAndRemove g u = Some (u, neighbors, g') -> NoDup (nodes g').
  intros. elim (lookupEdgesAndRemove_subgraph g g' neighbors u H0). intros.
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

Lemma firstForWhichSomeAndTail_corr :
  forall {A B:Type} (f:A->option B) (xs xs':list A) (y:B),
  firstForWhichSomeAndTail f xs = Some (y, xs') ->
  exists x prefix,
    (forall x', In x' prefix -> f(x')=None)
    /\
    f(x)=Some y
    /\
    xs = prefix ++ [x] ++ xs'.
  intros until xs.
  induction xs; [pv|]; intros.
  remember (f a) as t.
  destruct t; intros; simpl in *; rewrite <- Heqt in H.
  - exists a, []. split; [|split]; pv.
  - elim (IHxs xs' y); clear IHxs; intros; subst.
    elim H0; clear H0; intros; subst. exists x, (a::x0).
    destruct H0; destruct H1. split; [|split]; pv.
    + destruct H3; subst; pv.
    + subst; pv.
    + pv.
Qed.

Definition hasParent parent (v:node) := node_in_decb v (map (@fst node node) parent).

Definition bfsPushFilter g parent neighbors :=
      filter (fun v => negb (hasParent parent v)) (
        filter (fun v => node_in_decb v (nodes g)) neighbors ).

Definition bfs_step (args : graph * list node * parent_t) :
  option (graph * list node * parent_t) :=
  let (args', parent) := args in let (g, frontier) := args' in
  match firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier with
  | None => None
  | Some (u, neighbors, g', frontier_remaining) => 
      let vs := bfsPushFilter g parent neighbors in
      Some (g',
            vs++frontier_remaining,
            map (fun v => (v,u)) vs ++ parent)
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

Eval compute in ( (* CLRS 3rd edition BFS example *)
  let r := Node 0 in
  let s := Node 1 in
  let t := Node 2 in
  let u := Node 3 in
  let v := Node 4 in
  let w := Node 5 in
  let x := Node 6 in
  let y := Node 7 in
  let g :=
  [ (v, [r])
  ; (r, [v; s])
  ; (s, [r; w])
  ; (w, [s; t; x])
  ; (t, [u; x; w])
  ; (u, [t; x; y])
  ; (x, [w; t; u; y])
  ; (y, [x; u])
  ] in
  bfs (g, [s], [])).

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
    rename l0 into neighbors.
    unfold fold_right; induction (bfsPushFilter g parent neighbors); pv.
  }
Qed.

Lemma addToParent_hasEdge:
  forall g0 n parent0 neighbors,
  (forall v, In v neighbors -> hasEdge g0 n v) ->
  (forall u v, In (v, u) parent0 -> hasEdge g0 u v) ->
  (forall g u v, In (v, u)
    (map (fun v => (v,n)) (bfsPushFilter g parent0 neighbors) ++ parent0)
    -> hasEdge g0 u v).
  intros.
  specialize (in_app_or _ _ _ H1); intro Hor; destruct Hor; auto; clear H1.
  induction neighbors; intros; simpl in H2; pv.
  unfold bfsPushFilter in H2; simpl in H2.
  destruct (node_in_decb a (nodes g)); simpl in H2; auto.
  destruct (hasParent parent0 a); simpl in H2; auto.
  destruct H2; auto. clear IHneighbors.
  myinj H1.
  eapply H.
  left; auto.
Qed.

Lemma bfs_no_alien_edges' :
  forall (g0 g:graph) (frontier:list node) parent,
  (forall u v, hasEdge g u v -> hasEdge g0 u v) ->
  (forall u v, In (v, u)                      parent -> hasEdge g0 u v) ->
  (forall u v, In (v, u) (bfs (g, frontier, parent)) -> hasEdge g0 u v).
  intros until parent.
  remember (g, frontier, parent) as args.
  replace parent with (snd args) in * by pv.
  replace frontier with (snd (fst args)) in * by pv.
  replace g with (fst (fst args)) in * by pv.
  clear parent frontier g Heqargs.
  functional induction (bfs args); pv.
  unfold bfs_step in *; pv.
  remember (firstForWhichSomeAndTail (lookupEdgesAndRemove g) l) as T.
  symmetry in HeqT; destruct T; pv.
  rename g1 into g'.
  rename l into frontier.
  rename l0 into frontier'.
  rename l1 into neighbors.
  rename p0 into parent.
  elim (firstForWhichSomeAndTail_corr _ _ _ _ HeqT); pv; subst; pv.
  elim H2; clear H2; pv; subst; pv.
  specialize (lookupEdgesAndRemove_node _ _ _ _ _ H3); intro Hnode; subst.
  eapply IHp.
  - specialize lookupEdgesAndRemove_subgraph_hasEdge; pv.
  - specialize (lookupEdgesAndRemove_hasEdge _ _ _ _ _ H3); intro Hnew.
    apply addToParent_hasEdge; pv.
  - assumption.
Qed.

Lemma bfs_no_alien_edges : forall (g:graph) (frontier:list node),
  forall u v : node, In (v, u) (bfs (g, frontier, [])) -> hasEdge g u v.
  intros.
  apply (bfs_no_alien_edges' g g frontier []); auto.
  unfold In; intros. pv.
Qed.

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
Definition pathLen (p : path) : nat := length (route p).
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

(** hasPath indicates that a path p is a valid path in a graph g **)
Inductive hasPath : graph -> path -> Prop :=
| IdPath : forall g n, In n (nodes g) -> hasPath g (n, [])
| ConsPath : forall g n n' r', hasEdge g n n' -> hasPath g (n, r') -> hasPath g (n', n::r').

(** node endn is reachable from node startn if there exists a path from
    startn to endn in a graph g **)
Definition reachable (startn : node) (endn : node) (g : graph) : Prop :=
  exists (p : path), hasPath g p /\ origin p = startn /\ destination p = endn.

Lemma bfs_path_riginate_from_initial_frontier:
   forall frontier0 args,
   forall g frontier parent, args = (g, frontier, parent) ->
   forall ret, ret = bfs args ->
  (forall v,   In v frontier -> In (origin (traceParent parent v)) frontier0) ->
  (forall u v, In (v, u) parent -> In (origin (traceParent parent v)) frontier0) ->
  (forall u v, In (v, u) ret    -> In (origin (traceParent ret    v)) frontier0).
  intros until args; functional induction (bfs args); pv.
  remember (firstForWhichSomeAndTail (lookupEdgesAndRemove g) frontier) as L.
  destruct L; [|pv]. pve; pve; pve. symmetry in HeqL.
  elim (firstForWhichSomeAndTail_corr _ _ _ _ HeqL); intros.
  elim H; intros; clear H. destruct H0. destruct H0. rename x0 into discarded.
  replace x with n in * by (apply (eq_sym (lookupEdgesAndRemove_node _ _ _ _ _ H0))).
  repeat mysimp.
  remember (bfsPushFilter g parent l0) as vs.
  rename l into frontier_remaining; rename l0 into neighbors.
  eapply (IHp _ _ _ eq_refl); clear IHp; [reflexivity| | |apply H3]; clear H3;
      clear u v H.
  (*
  - if In v frontier_remaining then H1 else unroll one step of traceParent (to n); H2
  - (if In (v,u) parent then parentAddOnly else unroll one step of traceParent (to n));H2
  *)
Abort.

Definition pathFromTo g ss d p := In (origin p) ss /\ destination p = d /\ hasPath g p.
Definition shortestPathFromTo g ss d p := pathFromTo g ss d p /\ forall p', pathFromTo g ss d p' -> pathLen p' >= pathLen p.
Lemma emptyPathShortest : forall g v ss,
  In v (nodes g) -> In v ss -> shortestPathFromTo g ss v (v,[]).
  intros; split; [split;[|split]|].
  - assumption.
  - reflexivity.
  - apply IdPath; assumption.
  - intros. unfold pathLen; simpl. induction (length (route p')); auto.
Qed.

(** The following section defines the correctness of BFS. **)

(** For every good graph g and starting frontier,
    if bfs finds path p, then this path exists in g
    and its origin is one of the nodes in the frontier. **)
Definition finds_legit_paths : Prop :=
  forall (g : graph), GoodGraph g ->
    forall (frontier : list node) (p : path), In p (bfsAllPaths g frontier) ->
      hasPath g p /\ In (origin p) frontier.

(* idea from stackoverflow *)
Theorem strong_induction_on_nats' :
  forall (P : nat -> Prop),
    (forall (n : nat), (forall (k : nat), k < n -> P k) -> P n) ->
      forall (n : nat), P n /\ (forall (k : nat), k < n -> P k).
Proof.
  intros P H n. induction n.
  - split; try (eapply H); intros k H0; inversion H0.
  - destruct IHn as [IHn1 IHn2].
    
    Lemma strong_ind_step :
      forall (P : nat -> Prop) (n : nat), P n ->
      (forall k : nat, k < n -> P k) ->
      (forall k : nat, k < S n -> P k).
    Proof.
      intros P n Hn Hk k H0. destruct (lt_eq_lt_dec k n). destruct s.
      - apply Hk. apply l.
      - rewrite e. eauto.
      - remember (lt_n_Sm_le _ _ H0) as H1.
        remember (lt_not_le n k l H1) as H2. inversion H2.
    Qed.
    
    remember (strong_ind_step _ _ IHn1 IHn2) as IHn3.
    split. eapply H. apply IHn3. apply IHn3.
Qed.

Theorem strong_induction_on_nats :
  forall (P : nat -> Prop),
    (forall (n : nat), (forall (k : nat), k < n -> P k) -> P n) ->
      forall (n : nat), P n.
Proof.
  intros. eapply strong_induction_on_nats'; eauto.
Qed.

Theorem if_path_then_shorter_path_to_antineighbour_of_dest :
  forall (g : graph) (p : path), hasPath g p -> 1 <= pathLen p ->
  exists (p' : path) (n : node), origin p = origin p' /\ destination p' = n /\
    hasEdge g n (destination p) /\ pathLen p = S (pathLen p').
Proof.
  intros. remember (route p) as rp. destruct rp.
  - unfold pathLen in H0. rewrite <- Heqrp in H0. simpl in H0. inversion H0.
Admitted.

Definition reachable_in_n_or_less (startn : node) (endn : node) (g : graph)
  (n : nat) : Prop :=
  exists (p : path), hasPath g p /\ origin p = startn /\ destination p = endn /\
    pathLen p <= n.

(* TODO: what happens to frontier nodes in parent array? *)
(* TODO: reachable in n or less? *)

Lemma path_0 :
  forall (p : path), pathLen p = 0 ->
    origin p = destination p.
Proof.
  intros p H.
  unfold origin. unfold destination. destruct p.
  simpl. unfold pathLen in H. unfold route in H. simpl in H.
  destruct l. simpl. auto. simpl in H. inversion H.
Qed.

Theorem finds_path_from_frontier_if_reachable_in_n :
  forall (g : graph), GoodGraph g ->
    forall (s : node) (frontier : list node), In s frontier -> forall (n : nat),
      let P := fun (n : nat) => (forall (d : node), reachable_in_n s d g n ->
        forall (p : path), p = traceParent (bfs (g, frontier, [])) d ->
          s = origin p /\ d = destination p) in P n.
Proof.
  intros g Hg s frontier Hs.
  eapply (strong_induction_on_nats).
  intros n Hind.
  intros d Hreach p ptrace.
  destruct n. Focus 2.
  unfold reachable_in_n in Hreach.
  elim Hreach. intros p' [H1 [H2 [H3 H4]]]. assert (1 <= pathLen p').
  rewrite H4. apply le_n_S. apply le_0_n.
  elim (if_path_then_shorter_path_to_antineighbour_of_dest g p' H1 H).
  intros p'' Hp''.
  remember (Hind n (lt_n_Sn n) _) as Hind_n.
Abort.
(* brain explode *)
  

(* May be useful
Theorem shortest_path_exists_for_reachables :
  forall (g : graph) (s : node) (d : node), reachable s d g ->
    exists (p : path), s = origin p /\ d = destination p /\
    forall (p : path), *)

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
          pathLen p <= pathLen p'.

(** In order for bfs to be correct, all of the above conditions must hold. **)
Definition bfs_correct : Prop :=
  finds_legit_paths /\ finds_path_from_frontier_if_reachable  /\ finds_the_shortest_path.
