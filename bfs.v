Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Wf.
Require Import Arith.Wf_nat.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import Recdef.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

(* Defining a way of representing a graph. First we define a node, which will
   be uniquely identified by a natural number. The way nodes are represented
   in a graph is by a structure called adj, which includes a node and
   additionally the list of nodes adjacent to it. A graph is a list of adjs. *)

Inductive node := Node : nat -> node.

Definition node_eq_dec : forall (x y:node), {x = y} + {x <> y}.
  decide equality. apply eq_nat_dec.
Defined.
Definition node_in_dec := in_dec node_eq_dec.

Definition adj := (node * list node)%type.
Definition graph := list adj.

(* nodes g gives a list of node... *)
Definition nodes (g:graph) : list node := map (@fst node (list node)) g.
Definition hasEdge (g : graph) (n1 n2 : node) : Prop :=
  exists (neighbors : list node), In (n1, neighbors) g /\ In n2 neighbors.
Definition GoodGraph g := NoDup (nodes g) /\ forall u v, hasEdge g u v -> In v (nodes g).

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
  compute.
  reflexivity.
Qed.

Lemma no_aliens : forall g s parent, bfs g s = parent ->
    forall u v, In (u, v) parent -> hasEdge g u v.
Abort.

Definition path := (node * list node)%type.
Definition destination (p:path) := fst p.
Definition route (p:path) := snd p.
Definition length (p : path) : nat := length (route p).
Definition origin (p : path) : node := last (route p) (destination p).

(* This assumes that the statement (u's parent is v) comes before any statement
 about v's parents. This is true in out BFS implementation, and will probably
 remain true for any extension of it, but it is not an integral property of BFS
 -- it is just a requirement on the output format. We could get rid of this
 requirement, but then the termination argument for traceParent would depend on
 the assumption that parsing the parent map does not lead to cyclic paths.  We
 plan to prove things about the output of traceParent when it is run on the
 output of bfs, so the division of labor between the two should not matter a
 whole lot. *)
Fixpoint traceParent' (parent:parent_t) (u:node) {struct parent} : list node :=
  match parent with
  | nil => []
  | p::parent' =>
    if node_eq_dec (fst p) u
    then (snd p)::(traceParent' parent' (snd p))
    else traceParent' parent' u
end.
Definition traceParent (parent:parent_t) (u:node) := (u, traceParent' parent u).
Definition bfsAllPaths g s := let parent := bfs g s in map (fun p => traceParent parent (fst p)) parent. 

Example ex2 :
  traceParent' [(Node 3, Node 2); (Node 2, Node 0); (Node 1, Node 0)] (Node 3) =
  [Node 2; Node 0].
  compute.
  reflexivity.
Qed.

Inductive hasPath : graph -> path -> Prop :=
| IdPath : forall g n, In n (nodes g) -> hasPath g (n, [])
| ConsPath : forall g n n' r', hasEdge g n n' -> hasPath g (n, r') -> hasPath g (n', n::r').

Definition reachable (startn : node) (endn : node) (g : graph) : Prop :=
  exists (p : path), hasPath g p /\ origin p = startn /\ destination p = endn.

(* Pseudocode:
bfs is corrent if
  for all good graphs g, initial frontiers, nodes n1 and n2 in g
    if bfs finds a path, this path is in g
      and the beginning node of this path is in the frontier
    and
    if n2 is reachable from n1 and n1 is in the frontier
      then there exists a path p that bfs finds
      that starts from n1 and ends in n2
      and
      for all paths p' that have same start and end
        (if p' is in g, then its length is greater or equal to the length of p)
        and
        (if p is not equal to p', then bfs does not find p')
      (a long way of saying "if n2 is reachable from n1 that is in frontier
       then bfs finds exactly one path from n1 to n2 and that is the shortest")
    and
    if n2 is not reachable from n1
      then for all paths p' that bfs finds
      if p' starts from n1, it cannot end in n2
      (a long way of saying "if n2 is not reachable from n1
       then bfs does not find a path from n1 to n2")
*)

Definition bfs_correct : Prop :=
  forall (g : graph), GoodGraph g ->
  forall (frontier : list node) (n1 : node) (n2 : node),
    (forall (p : path), In p (bfsAllPaths g frontier) ->
       hasPath g p /\ In (origin p) frontier)
    /\
    (reachable n1 n2 g -> In n1 frontier ->
      exists (p : path), In p (bfsAllPaths g frontier) /\
        n1 = origin p /\ n2 = destination p /\
        (forall (p' : path), n1 = origin p' ->
           n2 = destination p' ->
           (hasPath g p' -> length p' >= length p)
           /\ (p <> p' -> ~(In p (bfsAllPaths g frontier)))))
    /\
    (~(reachable n1 n2 g) ->
      forall (p' : path),
        In p' (bfsAllPaths g frontier) ->
        n1 = origin p' -> n2 <> destination p').
