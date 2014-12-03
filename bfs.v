(* vim: set filetype=coq ts=2 sw=2 et : *)
(************************************************************************)
(* Written by Andres Erbsen and Sandra Schumann in 2014                 *)
(* Public domain / CC0                                                  *)
(************************************************************************)
(** This library provides an implementation of a variant of Dijkstra's
single source shortest paths algorithm on directed graphs. The input graph is
represented as a mapping from nodes to the lists of their neighbors ([list
(node*list node)]). The output of the function [bfs] is a mapping from each
reachable node to its predcessor in the shortest path to it. The helper
[traceParent] can efficiently compute the shortest path to any node from that
mapping, or conclude that no path exists. Thus, the shortest path from node [s]
to node [d] in graph [g] with edge lengths [1] is [traceParent (bfs g s) d].
The path obtained by this method is a list of nodes that contains both the
start node and the end node, and the end node is first.*)

(* begin hide *)
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Wf.
Require Import Arith.Wf_nat.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import Recdef.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import CpdtTactics.
Require Import List.
Import ListNotations.
(* end hide *)
(* *)
Inductive node := Node : nat -> node.
Definition node_eq_dec : forall (x y:node), {x = y} + {x <> y}. repeat (decide equality). Defined.
Definition node_eq_decb a b := if node_eq_dec a b then true else false.

Definition graph := list (node * list node).

Definition lookup {A:Type} (ps:list(node*A)) (x:node) :=
  match find (fun p => node_eq_decb x (fst p)) ps with
  | Some p => Some (snd p)
  | None => None
  end.

(** Any input graph of the correct type will be interpreted as a graph, but one
graph has multiple valid and equivalent representations. When a node appears in
the adjacency list of some other node, but the graph contains no adjacency list
for that node, the node's adjacency list is assumed to be empty.*)

Definition lookupDefault {A:Type} (ps:list(node*A)) (default:A) (x:node) :=
  match lookup ps x with
  | None => default
  | Some y => y
  end.

Definition hasEdge (g:graph) u v := In v (lookupDefault g [] u).

Inductive hasPath : graph -> node -> node -> list node -> Prop :=
| IdPath : forall g s, hasPath g s s [s]
| ConsPath : forall g s u p,             hasPath g s u    p   ->
             forall v, hasEdge g u v ->  hasPath g s v  (v::p).

Notation shortestPath g s d p := (
               hasPath g s d p /\
    forall p', hasPath g s d p' -> length p' >= length p).

Definition found := (node * (option node*nat))%type.
Definition foundPathLen (p:found) : nat := snd (snd p).
Definition found_eq_dec : forall(x y:found), {x = y} + {x <> y}.
  repeat (decide equality).
Qed.

Definition node_in_dec := in_dec node_eq_dec.
Definition found_in_dec := in_dec found_eq_dec.

(** keys g gives all the first parts of adjs in a graph g (list of nodes) **)
Definition keys {A:Type} := map (@fst node A).

(** Here come tactics. Nothing innovative, but faster and tidier than crush (even though less effective). *)

Ltac myinj H := injection H; clear H; intros; try subst.
Ltac myinj' H :=
  injection H;
  repeat (let Heq := fresh "Heq" in intro Heq; rewrite Heq in *; clear Heq; simpl in *).

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
    | [ H : context[node_eq_dec ?x ?y] |- _ ] =>
      destruct (node_eq_dec x y); repeat (mysimp; simpl in *; subst; eauto)
    | [ H : ?A |- ?A /\ _  ] => split; [apply A|]
    | [ H : ?A |- _  /\ ?A ] => split; [|apply A]
    | [ H : ?A |- ?A \/  _ ] => left; apply A
    | [ H : ?A |-  _ \/ ?A ] => right; apply A
    | [ H : context[let (_, _) := ?x in _] |- _ ] => destruct x
    (*| [ H : (match ?x with _ => Some _ | _ => None end = Some _) |- _ ] =>
        destruct x*)
  end.

Ltac pv := repeat (
  intros; simpl in *;
  intros; try pve;
  intros; try mysimp;
  intros; eauto).

(** We use [list(node,A)] as a map from node to [A]. For a graph, [A] is [list(node)] **)

Lemma in_fst_in_keys :
  forall {A:Type} x (y:A) ps, In (x, y) ps -> In x (keys ps).
Proof.
  intros. induction ps.
  inversion H.
  simpl in *. destruct H as [H1 | H2].
  left. destruct a. inversion H1. subst. simpl. reflexivity.
  right. apply IHps. apply H2.
Qed.

Lemma lookup_in : forall {A:Type} ps x (y:A),
  lookup ps x = Some y -> In (x, y) ps.
Proof.
  intros. rename H into H0.
  unfold lookup in *.
  remember (find (fun p => node_eq_decb x (fst p)) ps)
  as findps. destruct findps; inversion H0. subst.
  induction ps. discriminate.
  simpl in *. unfold node_eq_decb in *.
  destruct (node_eq_dec x (fst a)).
  inversion Heqfindps. subst. destruct a. left; crush.
  right. crush.
Qed.

Lemma in_lookup : forall {A:Type} ps, NoDup (keys ps) ->
    forall x (y:A), In (x, y) ps -> lookup ps x = Some y.
Proof.
  intros.
  unfold lookup.
  induction ps. inversion H0.
  simpl in *. destruct H0 as [H1 | H2].
  subst. simpl. unfold node_eq_decb.
  destruct (node_eq_dec x x).
  auto. destruct n. reflexivity.
  remember (NoDup_remove_1 [] _ _ H) as H3. simpl in H3.
  unfold node_eq_decb. remember (node_eq_dec x (fst a)) as xisa.
  destruct xisa. subst.
  remember (NoDup_remove_2 [] _ _ H) as H1. simpl in H1.
  remember (H1 (in_fst_in_keys _ _ _ H2)) as F. inversion F.
  apply IHps. auto. auto.
Qed.

Lemma in_lookup' : forall {A:Type} ps,
    forall x (y:A), In (x, y) ps ->
    exists y', lookup ps x = Some y'.
Proof.
  intros. induction ps. inversion H.
  simpl in *. destruct H. unfold lookup.
  simpl in *. unfold node_eq_decb.
  destruct (node_eq_dec x (fst a)). exists (snd a). auto.
  destruct a. inversion H. crush.
  unfold lookup. simpl in *. unfold node_eq_decb.
  destruct (node_eq_dec x (fst a)). exists (snd a). auto.
  unfold lookup in *. apply IHps. auto.
Qed.

Lemma lookup_corr : forall {A:Type} ps, NoDup (keys ps) ->
    forall x (y:A), lookup ps x = Some y <-> In (x, y) ps.
Proof.
  intros. split. apply lookup_in. apply in_lookup; crush.
Qed.

(** On each iteration of an inner loop, our BFS removes one item from the
  frontier. The fact that the frontier indeed gets smaller as a result of
  that is necessary for showing termination. *)
Lemma remove_length' : forall v vs,
  length vs >= length (remove node_eq_dec v vs) /\
  (In v vs -> length vs > length (remove node_eq_dec v vs)).
Proof.
  intros; induction vs; split; intros; auto.
  inversion H.
  simpl. destruct IHvs as [H1 H2].
  remember (node_eq_dec v a) as visa. destruct visa; simpl; omega.
  simpl. destruct IHvs as [H1 H2]. destruct H as [H3 | H4].
  remember (node_eq_dec v a) as visa. destruct visa; simpl.
  omega.
  subst. destruct n. auto.
  remember (node_eq_dec v a) as visa. destruct visa; simpl.
  omega.
  remember (H2 H4) as H5. omega.
Qed.

Lemma remove_length : forall v vs, In v vs ->
  length vs > length (remove node_eq_dec v vs).
Proof.
  intros v vs. apply remove_length'.
Qed.

(** As appending to a list is not faster than a seek-and-insert, we keep the
 frontier sorted as in Dijkstra's algorithm. *)

Fixpoint insert {A:Type} (f:A->nat) (y:A) (xs:list A) : list A :=
  match xs with
  | nil => [y]
  | x::xs' => if le_gt_dec (f y) (f x) then y::xs
              else x::(insert f y xs')
  end.

Definition extractMin {A:Type} (f:A->nat) (frontier : list A) :
  option (A * list A) :=
    match frontier with
    | nil => None
    | p::frontier' => Some (p, frontier')
    end.

(** The following is a slight adaptation of the [sorted] property from lecture
 notes; a function which maps the container elements to a [nat]-s by which they are sorted is provided as an argumant. *)
Definition list_all {A:Type} (P:A->Prop) (xs:list A) : Prop := 
  fold_right (fun h t => P h /\ t) True xs.

Lemma in_list_all {A} (P:A->Prop) (xs:list A) : 
  (forall x, In x xs -> P x) <-> list_all P xs.
Proof.
  induction xs; crush.
Qed.

Lemma in_insert :
  forall {A} (f:A->nat) (xs:list A) (n:A), 
    forall x, In x (insert f n xs) -> x = n \/ In x xs.
Proof.
  induction xs ; crush.
  destruct (le_gt_dec (f n) (f a)) ; crush.
  specialize (IHxs _ _ H0). crush.
Qed.

(* The opposite fact will also be useful. *)
Lemma insert_in : 
  forall {A} (f:A->nat) (xs:list A) (n:A), 
    forall x, x = n \/ In x xs -> In x (insert f n xs).
Proof.
  induction xs ; crush.
  destruct (le_gt_dec (f n) (f a)) ; crush.
  destruct (le_gt_dec (f n) (f x)) ; crush.
  destruct (le_gt_dec (f n) (f a)) ; crush.
Qed.

Fixpoint sorted {A:Type} (f:A->nat) (xs : list A) : Prop :=
  match xs with
  | nil => True
  | h::t => sorted f t /\ list_all (fun x => le (f h) (f x)) t
  end.

Lemma if_all_then_x : forall {A:Type} (x:A) (xs:list A) (P:A->Prop),
  list_all P xs -> In x xs -> P x.
Proof.
  intros. induction xs.
  inversion H0.
  destruct H as [H1 H2]. destruct H0 as [H0 | H0].
  subst. auto.
  auto.
Qed.

Lemma list_all_imp{A}: 
  forall (P Q : A -> Prop),
    (forall (x:A), P x -> Q x) -> 
  (forall (xs:list A), list_all P xs -> list_all Q xs).
Proof.
  intros P Q H.
  induction xs ; crush.
Qed.

(* If n <= m and m <= each element of xs, then n <= each element of xs. *)
Lemma list_lte_nm {A:Type} (f:A->nat) (n m:A) (xs:list A) : 
  (f n) <= (f m) -> list_all (fun x => le (f m) (f x)) xs ->
  list_all (fun x => le (f n) (f x)) xs.
Proof.
  intros.
  (* Aha!  Now we can use the list_all_imp lemma to avoid
    reasining about the list, and reduce this to a single element. *)
  eapply (list_all_imp (fun x => le (f m) (f x)) (fun x => le (f n) (f x)));
  [ intros ; omega | auto ].
Qed.

Lemma insert_sorted : forall {A} f (n:A) xs,
  sorted f xs -> sorted f (insert f n xs).
Proof.
  induction xs ; crush.
  destruct (le_gt_dec (f n) (f a)) ; simpl.
  crush.
  eapply list_lte_nm ; eauto.
  crush.
  (* here's where in_list_all comes into play -- we turn the
     list_all into reasoning about a particular element in 
     (insert n xs) which has to be either n or one of the xs. *)
  apply in_list_all.
  intros.
  generalize (in_insert f xs n x H2). intro.
  destruct H3.
  crush.
  (* here's where the opposite lemma comes into play. *)
  rewrite <- in_list_all in H1.
  crush.
Qed.

Lemma insert_corr : forall {A:Type} (f:A->nat) (x:A) (xs : list A) (ys : list A),
  insert f x xs = ys -> sorted f xs -> In x ys /\ sorted f ys.
Proof.
  intros; split; subst.
  apply insert_in; crush.
  apply insert_sorted; crush.
Qed.

(** Frontier decreases in size -- our termination argument *)
Lemma extractMin_shorter : forall {A:Type} (f:A->nat) (frontier : list A),
  forall x xs, extractMin f frontier = Some (x,xs) ->
  length frontier = S (length xs).
Proof.
  intros. unfold extractMin in *. destruct frontier.
  crush.
  inversion H. crush.
Qed.

(** Other relevant properties of taking the first element from a sorted list *)
Lemma extractMin_corr : forall {A:Type} (f:A->nat) (frontier : list A),
  sorted f frontier ->
    match extractMin f frontier with
    | None => frontier = nil
    | Some ret => forall p, In p frontier -> 
            (f p >= f (fst ret) /\ (p <> (fst ret) -> In p (snd ret)))
    end.
Proof.
  intros. unfold extractMin. destruct frontier. auto.
  destruct H as[H1 H2]. intros. split.
  simpl in *. destruct H as [H | H].
  subst. auto. remember (if_all_then_x _ _ _ H2 H) as H3. simpl in H3.
  omega.
  simpl in *. intros. destruct H as [H | H]. destruct H0. auto.
  auto.
Qed.

  
(** Textbook imperative BFS processes one node from the frontier on each iteration.
    Encoding the algorithm this way would make the termination argument more
    complicated; instead we separate out an inner loop. On each iteration of
    the outer loop, our BFS loops through the elements in the frontier until
    it finds one that is not yet expanded. That node is removed from the list of
    unexpanded nodes before continuing with the outer loop. This provides a
    convenient termination argument. [closestUnexpanded] implements the
    said inner loop and returns the first node from the frontier for which
    has not yet been expanded.*)
Function closestUnexpanded
    (f:found->nat) (unexpanded : list node) (frontier : list found)
    {measure length frontier}
    : option (found * list found)
    :=
    match extractMin f frontier with
    | None => None
    | Some ret => let (p, frontier') := ret in
            if node_in_dec (fst p) unexpanded
            then Some ret
            else closestUnexpanded f unexpanded frontier'
    end.
intros. remember (extractMin_shorter _ _ _ _ teq) as H. omega.
Defined.

Lemma extractMin_as_sum : forall {A:Type} (f:A->nat) (frontier : list A) x xs,
  extractMin f frontier = Some (x,xs) -> frontier = x::xs.
Proof.
  intros. unfold extractMin in *. destruct frontier; crush.
Qed.

Lemma sorted_tail : forall {A} (f:A->nat) (xs:list A) (y:A) (ys:list A),
  sorted f xs -> xs = y::ys -> sorted f ys.
Proof.
  crush.
Qed.

Lemma closestUnexpanded_unexpanded : forall f unexpanded frontier ret,
  closestUnexpanded f unexpanded frontier = Some ret ->
  In (fst (fst ret)) unexpanded.
Proof.
  intros. functional induction (closestUnexpanded f unexpanded frontier).
  inversion H.
  inversion H. simpl. auto.
  apply IHo. auto.
Qed.

Lemma closestUnexpanded_corr : forall f unexpanded frontier,
  sorted f frontier ->
    match closestUnexpanded f unexpanded frontier with
    | None => forall p, In p frontier -> ~ In (fst p) unexpanded
    | Some ret =>
        exists discarded, frontier = discarded ++ [fst ret] ++ snd ret
        (* it would suffice if frontier was just a permutation of the above *)
        /\ (forall p, In p discarded -> ~ In (fst p) unexpanded)
        /\ (forall p, In p (snd ret) ->   In p frontier /\ f p >= f (fst ret))
        /\ In (fst (fst ret)) unexpanded
    end.
Proof.
  intros. remember (closestUnexpanded f unexpanded frontier) as oret.
  destruct oret.

  functional induction (closestUnexpanded f unexpanded frontier).
  crush.
  myinj Heqoret. remember (extractMin_as_sum _ _ _ _ e) as H1; clear HeqH1.
  exists []. split. simpl. auto. split. auto. split.
  intros. split. simpl in *. crush. simpl.
  remember (extractMin_corr _ _ H) as H2; clear HeqH2.
  remember (extractMin f frontier) as Hmin in *. destruct Hmin.
  inversion e. simpl in *. destruct p1. myinj H4.
  simpl in *. apply H2. right. auto.
  simpl in *. inversion e.
  simpl in *. auto.

  eelim IHo; [..|eauto]. clear IHo.
  intros. destruct H0 as [H1 [H2 H3]].
  exists (p0::x).
  split. simpl in *. apply (extractMin_as_sum f). subst. auto.
  split; intros.
  simpl in *. destruct H0 as [H0 | H0].
  subst; auto.
  apply H2. apply H0. split.
  remember (extractMin_as_sum f _ _ _ e) as H4; clear HeqH4.
  subst. split. simpl. right. apply H3. apply H0.
  apply H3. apply H0.
  simpl in *. apply H3. eapply sorted_tail. apply H.
  apply (extractMin_as_sum f). apply e.

  intros. functional induction (closestUnexpanded f unexpanded frontier).
  destruct frontier. auto.
  unfold extractMin in *. inversion e.
  inversion Heqoret.
  remember (extractMin_as_sum f _ _ _ e) as H4; clear HeqH4.
  rewrite H4 in *. simpl in *.
  destruct H0 as [H0 | H0].
  rewrite <- H0 in *. auto.
  apply IHo. destruct H as [H1 H2].
  auto. auto. auto.
Qed.

(** Properties of [remove] will be used to show that various invariants are preserved
    bteween iterations of the main loop. It's a pity that we didn't find these from
    the standard library...*)
Lemma remove_does_not_add' : forall (u:node) (xs:list node) (ys:list node),
  remove node_eq_dec u xs = ys ->
  forall (v:node), In v ys -> In v xs.
Proof.
  intro u; induction xs; crush.
  remember (node_eq_dec u a) as uisa. destruct uisa.
  right. eapply IHxs. remember (remove node_eq_dec u xs) as xsu.
  crush. crush.
  simpl in *. destruct H0 as [H0 | H0].
  left; auto.
  right; eapply IHxs. remember (remove node_eq_dec u xs) as xsu.
  crush. crush.
Qed.

Lemma remove_does_not_add : forall a xs xs', remove node_eq_dec a xs = xs' ->
  forall b, ~ In b xs -> ~ In b xs'.
Proof.
  intros. unfold not. intros.
  remember (remove_does_not_add' _ _ _ H _ H1) as H2.
  crush.
Qed.

Lemma remove_preserves: forall a xs xs', remove node_eq_dec a xs = xs' ->
  forall b, a<>b -> In b xs -> In b xs'.
Proof.
  intros a xs. induction xs; intros; simpl in *; [crush|].
  destruct H1 as [H1 | H1].
  - destruct (node_eq_dec a a0). apply IHxs; crush.
    subst; left; auto.
  - destruct (node_eq_dec a a0). apply IHxs; crush.
    subst; simpl in *. destruct (node_eq_dec a0 b).
    left; auto. right; apply IHxs; auto.
Qed.

Lemma in_notin_notsame : forall {A} (a:A) b xs, ~In a xs -> In b xs -> a <> b.
Proof.
  intros. induction xs. auto. simpl in *.
  destruct H0 as [H0 | H0]; crush.
Qed.

(** [find] is used in [lookup] (our map accessor operation) *)
Lemma find_head : forall {A} (f:A->bool) x xs,
  (if f x then True else False) -> (find f (x::xs) = Some x).
Proof.
  intros; remember (f x) as fx; destruct fx; [|crush].
  unfold find. rewrite <- Heqfx. auto. 
Qed.

Lemma find_head_not : forall {A} (f:A->bool) x xs,
  (if f x then False else True) -> (find f (x::xs) = find f xs).
Proof.
  intros; remember (f x) as fx; destruct fx; [crush|].
  unfold find. rewrite <- Heqfx. auto.
Qed.

Lemma lookup_head : forall {A} frontierRem u (pu:A) xs,
  (forall x, In x xs -> fst x <> u) -> lookup (xs ++ (u, pu) :: frontierRem) u = Some pu.
Proof.
  induction xs; simpl in *. intros.
  unfold lookup. assert (find (fun p : node * A =>
  node_eq_decb u (fst p)) ((u, pu) :: frontierRem) = Some (u,pu)).
  apply find_head. simpl in *. unfold node_eq_decb. destruct (node_eq_dec u u).
  crush. crush.
  unfold node_eq_decb. simpl in *. destruct (node_eq_dec u u).
  simpl in *. reflexivity. crush.
  intros. unfold lookup in *. unfold node_eq_decb in *. simpl in *.
  assert (fst a <> u). apply H; left; auto.
  destruct (node_eq_dec u (fst a)); [crush|].
  apply IHxs. intros. apply H. right. auto.
Qed.

(** On each iteration, BFS pushes the neighbors of the node it expanded into the frontier. The following lemmas describe the non-surprising properties of inserting multiple items. *)
Lemma insert_many_in : forall {A} (f:A->nat) (xs:list A) (ys:list A) (zs:list A),
  fold_right (insert f) ys xs = zs ->
  forall (z:A), (In z xs \/ In z ys) -> In z zs.
Proof.
  induction xs; intros; simpl in *.
  crush.
  destruct H0 as [[H0 | H0] | H0].
  rewrite <- H. apply insert_in. left. auto.
  rewrite <- H. apply insert_in. right. apply (IHxs ys).
  auto. left. auto.
  remember (fold_right (insert f) ys xs) as xsys. symmetry in Heqxsys.
  remember (IHxs _ _ Heqxsys) as H1.
  rewrite <- H. apply insert_in.
  right. apply H1. right. auto.
Qed.

Lemma in_many_insert : forall {A} (f:A->nat) (xs:list A) (ys:list A) (zs:list A),
  fold_right (insert f) ys xs = zs ->
  forall (z:A), In z zs -> (In z xs \/ In z ys).
Proof.
  induction xs; intros; simpl in *.
  crush.
  remember (fold_right (insert f) ys xs) as xsys. symmetry in Heqxsys.
  remember (IHxs _ _ Heqxsys z) as H1.
  rewrite <- H in *.
  remember (in_insert f _ _ _ H0) as H2.
  destruct H2 as [H2 | H2]. left. left. auto.
  remember (H1 H2) as H3. destruct H3 as [H3|]; auto.
Qed.

Lemma extractMin_sorted : forall {A} (f:A->nat) (xs:list A) (xxs':A*list A),
  sorted f xs -> extractMin f xs = Some xxs' -> sorted f (snd xxs').
Proof.
  intros. unfold extractMin in *. destruct xs; crush.
Qed.

Lemma insert_many_sorted:
  forall {A:Type} (f:A->nat) olds news, 
    sorted f olds -> sorted f (fold_right (insert f) olds news).
  Hint Resolve insert_sorted.
  induction news; crush.
  Remove Hints insert_sorted.
Qed.

Lemma app_right_sorted:
  forall {A:Type} (f:A->nat) xs ys, sorted f (xs ++ ys) -> sorted f ys.
  Hint Resolve sorted_tail.
  induction xs; crush.
  Remove Hints sorted_tail.
Qed.

Lemma frontieradd_keeps_old :
  forall frontierRemaining frontier' u pu neighbors v res,
  fold_right (insert foundPathLen) frontierRemaining
       (map (fun v : node => (v, (Some u, S (foundPathLen (u, pu)))))
          neighbors) = frontier' ->
  In (v, res) frontierRemaining -> In (v, res) frontier'.
Proof.
  intros.
  eapply insert_many_in. apply H. right. auto.
Qed.

(** [bfs_step] contains most of the algorithm logic. If the output is [None], the [bfs] terminates; otherwise the output is the input to the next step. Curiously, inlining the definition of [bfs_step] into [bfs] did not give us [functional induction], but the code here did. [parent] is the output accululator, the graph [g] is never modified. The start node is specified by setting it as the only element in the frontier on the top-level call. *)
Definition bfs_step
  (g:graph) (unexpanded:list node) (frontier:list found) (parent:list found)
  := match closestUnexpanded foundPathLen unexpanded frontier with
  | None => None
  | Some p => let (found_u, frontierRemaining) := p in
      let u := fst found_u in
      let l := foundPathLen found_u in
      let parent' := found_u::parent in
      let unexpanded' := remove node_eq_dec u unexpanded in
      let neighbors := lookupDefault g [] u in
      let frontierNew := map (fun v => (v, (Some u, 1+l))) neighbors in
      let frontier' := fold_right (insert foundPathLen) frontierRemaining frontierNew in
          Some (unexpanded', frontier', parent')
  end.

(** [expandBFS] operates on a proof state that contains a call to [bfs_step]
  that returned [Some] and [remember]-s the local variables defined using [let] in the body of [bfs_step] *)
Ltac splitHs := repeat (match goal with [ H : _ /\ _ |- _ ] => destruct H end).
Ltac expandBFS := 
    match goal with
      [ H : context[bfs_step ?g ?u ?f ?p] |- _ ]
          =>unfold bfs_step in H
          ; remember (closestUnexpanded foundPathLen u f) as c in *
          ; destruct c; [|inversion H]
          ; match goal with [ H : context[let (_, _) := ?x in _] |- _ ]
              =>let fu := fresh "found_u" in let fr := fresh "frontierRemaining" in
                  destruct x as [fu fr]; simpl in H
            end
          ; match goal with [H : context[lookupDefault g [] (fst ?found_u)] |- _ ]
              =>remember (lookupDefault g [] (fst found_u)) as neighbors
              ; let uu := fresh "u" in let pu := fresh "pu" in
                  destruct found_u as [uu pu]
            end
          ; match goal with [H : Some _ = closestUnexpanded _ _ _ |- _ ]
              =>simpl in H; symmetry in H
            end
          ; injection H; clear H; intro; intro; intro
    end.

Function bfs
  (g:graph) (unexpanded:list node) (frontier:list found) (parent:list found)
  {measure length unexpanded}
  : list found
  :=
  match bfs_step g unexpanded frontier parent with
  | None => parent
  | Some args =>
      let (args', parent') := args in let (unexpanded', frontier') := args' in
      bfs g unexpanded' frontier' parent'
  end.
intros. expandBFS. remember (closestUnexpanded_unexpanded _ _ _ _ Heqc) as H2.
simpl in *. specialize (remove_length _ _ H2). intros. subst. omega.
Defined.

(** [traceParent] operates on the output of [bfs]. Given a node to which there exists a path from the start node, it reconstructs the shortest path from start to that node. If no such path exists, [traceParent] returns [None]. The first element in the returned list represents the last node in the path and so on. *)
Fixpoint traceParent
  (parent:list found) (v:node)
  {struct parent}
  : option (list node)
  :=
  match parent with
  | nil => None
  | entry::parent' =>
      let (v', value) := entry in
      if node_eq_dec v v'
      then let (parentPointer, l) := value in
           match parentPointer with
           | None => Some [v]
           | Some u => match traceParent parent' u with
                       | None => None
                       | Some path => Some (v::path)
                       end
           end
      else match traceParent parent' v with
           | None => None
           | Some path => Some path
           end
  end.

(** Setting the parent of a new node does not modify the parent of any other node *)
Lemma parents_dont_disappear: forall parent parent' pu u d p,
  (u,pu)::parent = parent' -> u <> d -> traceParent parent d = Some p ->
  traceParent parent' d = Some p.
Proof.
  induction parent; intros; [crush|].
  destruct a. unfold traceParent in H1.
  destruct (node_eq_dec d n).
  fold traceParent in H1. destruct p0; crush.
  destruct (node_eq_dec n u); crush.
  destruct (node_eq_dec n n); crush.
  fold traceParent in H1. remember (traceParent parent d) as dpar.
  destruct dpar.
  subst. unfold traceParent.
  destruct (node_eq_dec d u); [crush|].
  destruct (node_eq_dec d n); [crush|].
  fold traceParent. remember (traceParent parent d) as dpar. destruct dpar.
  subst. crush. crush. crush.
Qed.

Lemma contains_sth_is_not_empty : forall {A} xs (x:A) ys, xs++(x::ys) <> [].
Proof. induction xs; crush. Qed.

Lemma singleton_is_list : forall {A} y xs (x:A) xs',
  [y] = xs++x::xs' -> y = x /\ xs = [] /\ xs' = [].
Proof.
  intros. destruct xs.
  - repeat split; crush.
  - inversion H. remember (contains_sth_is_not_empty xs x xs') as H3. crush.
Qed.

(** * Proof of correctness of [bfs] *)

(** [HextendFrontier] and is used to prove that all when BFS expands a node and
inserts its neighbors to the frontier, then the frontier is still a valid
boundary between expanded and unexpanded nodes: every path from the start node
to an unexpanded node must go through the frontier. [ws] is the part of the
path that previously connected the frontier to the destination node [d], and
[u] is the node being expanded.*)
Lemma HextendFrontier' :
  forall (v:node) u ws,
  Some u <> hd_error (ws++[v]) -> (* u is not destination *)
  ((exists pre v' post, ws++[v] = post ++ v'::u::pre /\ v' <> u
    /\ forall w, In w post -> u <> w)
  \/
  (forall w, In w (ws++[v]) -> w <> u)).
Proof.
  induction ws; intros; simpl in *.
  - right; intros; crush.
  - destruct (ws++[v]).
    + right. intros. destruct H0 as [H0 | H0]; crush.
    + simpl in *. destruct (node_eq_dec u n).
      * rewrite <- e in *. left. exists l; exists a; exists []. repeat split.
        { unfold not; intros. rewrite H0 in *; crush. }
        { intros. inversion H0. } 
      * assert (Some u <> value n).
          { unfold not; intros. inversion H0; crush. }
        destruct (IHws H0) as [IHws' | IHws'].
        {
          elim IHws'; clear IHws'; intros pre IHws'.
          elim IHws'; clear IHws'; intros v' IHws'.
          elim IHws'; clear IHws'; intros post IHws'.
          left. exists pre; exists v'; exists (a::post).
          repeat split; [crush|crush|].
          intros. destruct H1 as [H1 | H1].
          - unfold not; intro Heq; rewrite Heq in *; crush.
          - apply IHws'; crush.
        }
        {
          right; intros. destruct H1 as [H1 | H1].
          - rewrite H1 in *. unfold not in *; intros.
            apply H; crush.
          - apply IHws'; crush.
        }
Qed.

Lemma HextendFrontier'' : forall ws v post v' pre unexpanded,
  ws ++ [v] = post ++ v'::pre ->
  (forall w : node, In w (ws++[v]) -> In w unexpanded) ->
  In v' unexpanded /\ (forall w : node, In w post -> In w unexpanded).
Proof.
  induction ws; intros; simpl in *; split.
  - destruct (singleton_is_list v post v' pre H) as [H2 [H3 H4]].
    apply H0; left; crush.
  - destruct (singleton_is_list v post v' pre H) as [H2 [H3 H4]].
    crush.
  - destruct post; simpl in *; inversion H; apply H0; auto.
    inversion H. assert (forall w, In w (ws++[v]) -> In w unexpanded) by crush.
    destruct (IHws _ _ _ _ _ H3 H1) as [IH _]. crush.
  - destruct post; simpl in *; intros.
    + inversion H1.
    + inversion H. destruct H1 as [H1 | H1]; crush. eapply IHws.
      * apply H4.
      * intros; apply H0; right; auto.
      * crush.
Qed.

Lemma HextendFrontier :
  forall ws (v:node) u,
  Some u <> hd_error (ws++[v]) -> (* u is not destination *)
  forall unexpanded,
  (forall w : node, In w (ws++[v]) -> In w unexpanded) -> (* everything unexpanded *)
  
  (exists pre v' post, ws++[v] = post ++ v'::u::pre
    /\ (In v' unexpanded /\ forall w, In w post -> In w unexpanded)
    /\ v' <> u /\ (forall w, In w post -> u <> w))
  \/
  (forall w, In w (ws++[v]) -> u <> w /\ In w unexpanded).
Proof.
  intros.
  destruct (HextendFrontier' _ _ _ H).
  - elim H1; clear H1; intros pre H1.
    elim H1; clear H1; intros v' H1.
    elim H1; clear H1; intros post H1.
    left. exists pre; exists v'; exists post.
    destruct H1 as [H1 [H2 H3]]. repeat split; auto.
    + apply H0. crush.
    + intros. apply H0. crush.
  - right; split; [|crush].
    unfold not in *; intros; eapply H1.
    apply H2. rewrite H3; auto.
Qed.

(** Yet another property of [remove]... *)
Lemma removing_corr_item : forall x xs xs',
  remove node_eq_dec x xs = xs' ->
  forall x', ~(In x' xs') -> In x' xs -> x = x'.
Proof.
  induction xs; intros; auto.
  - inversion H1.
  - simpl in *. destruct H1 as [H1 | H1].
    destruct (node_eq_dec x a). crush. rewrite <- H in *.
    simpl in *. assert False. apply H0. auto.
    inversion H2.
    destruct (node_eq_dec x a). eapply IHxs; crush.
    eapply IHxs. remember (remove node_eq_dec x xs) as xsx.
    apply (Heqxsx). unfold not in *. intros.
    apply H0. rewrite <- H in *. simpl in *.
    right. auto. auto.
Qed.

(* Using [lookupDefault] indeed returns the neighbors of a node *)
Lemma lookup_neighbors: 
  forall g u neighbors, lookupDefault g [] u = neighbors ->
  forall v, In v neighbors -> hasEdge g u v.
Proof.
  intros. unfold hasEdge in *. unfold lookupDefault in *.
  rewrite H; auto.
Qed.

(** If an invariant holds, then all nodes that for which there is an entry in the parent map are expanded *)
Lemma parent_means_expanded : forall parent u p unexpanded,
  traceParent parent u = Some p ->
  (forall (n : node) (np : option node * nat),
          In (n, np) parent -> ~ In n unexpanded) ->
  ~ In u unexpanded.
Proof.
  intros. induction parent.
  apply (H0 u (Some u,0)). simpl in *. inversion H.
  simpl in *. destruct a. destruct (node_eq_dec u n).
  eapply (H0 u p0).
  left. rewrite e. apply f_equal. reflexivity.
  eapply IHparent. destruct (traceParent parent u); crush.
  intros. apply (H0 n1 np). right. auto.
Qed.

(** Everything to which one can find a path from the parent map must be in there *)
Lemma traceparent_in : forall parent u p,
  traceParent parent u = Some p -> exists pu, In (u, pu) parent.
Proof.
  induction parent; intros; simpl in *. inversion H.
  destruct a. destruct (node_eq_dec u n). exists p0.
  left. rewrite e. apply f_equal. auto.
  remember (traceParent parent u) as pu. destruct pu.
  symmetry in Heqpu. rewrite H in Heqpu.
  elim (IHparent _ _ Heqpu); intros. exists x. right. auto.
  inversion H.
Qed.

(** List manipulation. *)
Lemma hasPath_head: forall g s d p, hasPath g s d p ->
  p <> [] -> exists t, p = d::t.
Proof.
  induction p; intros; simpl in *.
  - crush.
  - exists p. assert (a = d). inversion H. crush. crush. crush.
Qed.

Lemma last_subst_into' : forall {A} a (x:A) y b, a++[x] = y::b ->
  forall c, a++(x::c) = y::(b++c).
Proof. induction a; intros; crush. Qed.

Lemma last_subst_into : forall {A} a (x:A) b, a++[x] = b ->
  forall c, a++(x::c) = b++c.
Proof. induction a; intros; crush. Qed.

Lemma nonempty_has_last : forall {A} (xs : list A), xs <> [] ->
  exists x xs', xs = xs' ++ [x].
Proof.
  induction xs; intros. unfold not in H. assert False. apply H. auto. inversion H0.
  destruct xs. exists a. exists []. auto.
  assert (a0::xs <> []). unfold not; intros. inversion H0.
  elim (IHxs H0); intros. elim H1; intros.
  rewrite H2.
  exists x. exists (a::x0). auto.
Qed.

Lemma dest_different_end_nonempty : forall p_out' g s d p',
  hasPath g s d p' ->
  forall u, u <> d ->
  forall p_out v p_in, p' = p_out ++ v :: p_in ->
  forall p_skip, p_out ++ [v] = p_out' ++ u :: p_skip ->
  exists v'' p_out'', p_out' = p_out'' ++ [v''].
Proof.
  intros.
  assert (p_out <> []). unfold not; intros. rewrite H3 in *; clear H3.
    simpl in *.
    assert (p' <> []). rewrite H1. unfold not; intros. inversion H3.
    elim (hasPath_head _ _ _ _ H H3); intros.
    destruct p_out'. inversion H2. subst. inversion H1. crush.
    inversion H2. remember (contains_sth_is_not_empty p_out' u p_skip) as H8.
    crush.
  destruct p_out; crush.
  assert (p_out' <> []). unfold not; intros. rewrite H1 in *; clear H1.
    simpl in *.
    inversion H2.
    assert (n :: p_out ++ v :: p_in <> []).
      unfold not; intros. inversion H1.
    elim (hasPath_head _ _ _ _ H H1); intros.
    inversion H6. subst. apply H0; auto.
  apply nonempty_has_last. auto.
Qed.

(** If [a] and [b] are adjacent in a path, there must be an edge between them. *)
Lemma in_path_edge :
  forall p' p a b p'' p''', p = ((p' ++ [a]) ++ b :: p'') ++ p''' ->
  forall g s d, hasPath g s d p ->
  hasEdge g b a.
Proof.
  induction p'; intros; simpl in *.
  - inversion H0; subst.
    + inversion H0; subst. inversion H6; subst; auto.
    + inversion H1; [subst; inversion H6; subst; auto|].
      inversion H6; subst. inversion H0; subst.
      inversion H6; subst. auto.
  - destruct p; inversion H. inversion H0; subst.
    + remember (contains_sth_is_not_empty (p' ++ [a0]) b (p''++p''')) as H1.
      rewrite <- app_assoc in H8. rewrite <- app_comm_cons in H8.
      clear HeqH1. rewrite <- H8 in H1. crush.
    + eapply IHp'. Focus 2. apply H8. crush.
Qed.

(** More list and map manipulation *)
Lemma edge_in_neigh : forall g a neigh,
  lookupDefault g [] a = neigh -> forall b, hasEdge g a b -> In b neigh.
Proof.
  intros. unfold hasEdge in *. unfold lookupDefault in *.
  rewrite H in *. auto.
Qed.

Lemma last_means_in : forall {A} a b (x:A), a = b++[x] -> In x a.
Proof. induction b; crush. Qed.

Lemma not_last_in_front : forall {A} xs (x:A) ys y ys',
  xs ++ [x] = ys ++ (y::ys') -> forall a, In a ys -> In a xs.
Proof.
  induction xs; induction ys; intros; simpl in *.
  - inversion H0.
  - inversion H. remember (contains_sth_is_not_empty ys y ys') as H4.
    crush.
  - inversion H0.
  - inversion H. destruct H0 as [H0 | H0].
    left. auto.
    right. eapply IHxs. apply H3. auto.
Qed.

Lemma in_with_map : forall {A} v neighs, In (v:A) neighs ->
  forall {B} (w:B), In (v,w) (map (fun x => (x,w)) neighs).
Proof.
  induction neighs; intros; crush.
Qed.

Lemma in_neigh_in_map : forall {A B:Type} (w:A) (pv:B) neigh,
  In w neigh -> In (w,pv) (map (fun w => (w,pv)) neigh).
Proof.
  induction neigh; intros; simpl in *.
  - inversion H.
  - destruct H as [H | H]; auto.
    left; rewrite H in *; apply f_equal; auto.
Qed.

Lemma in_map_in_keys : forall {A:Type} w (pv:A) fr', In (w,pv) fr' ->
  In w (keys fr').
Proof.
  induction fr'; intros; simpl in *.
  - inversion H.
  - destruct H as [H | H]; auto.
    inversion H; left; auto.
Qed.

Lemma in_neigh_in_frontier' : forall {A} f fr (pv:A) neigh fr' v,
  In v neigh ->
  fold_right (insert f) fr (map (fun w => (w,pv)) neigh) = fr' ->
  In v (keys fr').
Proof.
  intros. eapply in_map_in_keys.
  eapply insert_many_in; eauto.
  left; apply in_neigh_in_map; auto.
Qed.

(** Finally, the frontier indeed separates the expanded nodes from the unexpanded nodes (if it did on the previous step) *)
Lemma HextendFrontier_not_u :
  forall v' u g neighbors pu frontierRemaining frontier'
  unexpanded unexpanded' d p' s p_out v p_in p_out' p_skip,
  v' = u ->
  (forall w : node, In w p_out' -> ~ In w (keys frontier')) ->
  p_out ++ [v] = p_out' ++ v' :: p_skip ->
  (forall w : node, In w p_out -> In w unexpanded) ->
  p' = p_out ++ v :: p_in ->
  u <> d -> 
  hasPath g s d p' ->
  remove node_eq_dec u unexpanded = unexpanded' ->
  fold_right (insert foundPathLen) frontierRemaining
    (map
      (fun v : node =>
        (v, (Some u, S (foundPathLen (u, pu))))) neighbors) =
    frontier' ->
  lookupDefault g [] u = neighbors ->
  False.
Proof.
  intros.
  rename H into e.
  rename H0 into Hws'.
  rename H1 into Hp_split'.
  rename H2 into HwUnexpanded.
  rename H3 into Hp_split.
  rename H4 into n1.
  rename H5 into Hp'.
  rename H6 into HunepandedRemove.
  rename H7 into HfrontierInsert.
  rename H8 into Heqk.

  rewrite e in *.
  assert (exists v'' p_out'', p_out' = p_out'' ++ [v'']).
  eapply dest_different_end_nonempty; eauto.
  elim H; clear H; intros v'' H; elim H; clear H; intros p_out'' H.
  rewrite H in Hp_split'.
  rewrite (last_subst_into _ _ _ Hp_split') in Hp_split.
  (* Hp_split' in this form means edge between u and v'' *)
  remember (in_path_edge _ _ _ _ _ _ Hp_split _ _ _ Hp') as Hedge.
  (* edge from u to v'' means In v'' neighbors *)
  remember (edge_in_neigh _ _ _ Heqk _ Hedge) as Hneigh.
  (* v'' is in p_out' *)
  assert (In v'' p_out'). eapply last_means_in. eauto.
  (* v'' is in keys frontier' *)
  remember (in_neigh_in_frontier' _ _ _ _ _ _ Hneigh HfrontierInsert)
    as Hkeys.
  (* contradiction from Hws' *)
  remember (Hws' _ H0 Hkeys) as Hcontra. auto.
Qed.

(** ...and even more list manipulation... *)
Lemma list_last_next_first : forall {A} a (x:A) b, (a ++ [x]) ++ b = a ++ x::b.
Proof.
  induction a; intros; simpl in *; auto.
  rewrite IHa. auto.
Qed.

Lemma hd_of_sublist : forall {A} b a c (x:A),
  a = b ++ x::c -> hd_error a = hd_error (b ++ [x]).
Proof.
  induction b; intros; simpl in *.
  - destruct a; crush.
  - destruct a0; crush.
Qed.

Lemma d_head_path : forall g s d p,
  hasPath g s d p -> hd_error p = Some d.
Proof.
  intros. inversion H; crush.
Qed.

(** If a path leads from [s] to [y] and then to [x], the relevant part of it leads from [s] to [y].*)
Lemma reachable_halfway : forall g s xs x y ys,
  hasPath g s x (xs ++ y :: ys) -> hasPath g s y (y :: ys).
Proof.
  induction xs; intros; simpl in *.
  - inversion H; crush.
  - inversion H; subst.
    + remember (contains_sth_is_not_empty xs y ys) as H6.
      clear HeqH6. rewrite <- H5 in H6. crush.
    + apply (IHxs _ _ _ H5).
Qed.

(** The following lemma describes the evolution of BFS state at an arbitrary time during its execution. *)
Lemma bfs_corr:
  forall (g:graph) (s:node),
  forall (unexpanded:list node) (frontier:list found) (parent:list found),
  ((
  (** [H]: The most important invariant: to get from the start node to an unexpanded node, a path *must* go through the frontier. To get to an expended node, just look it up the path to it from the parent map. *)
    forall (d:node) (p':list node), hasPath g s d p' ->
      if node_in_dec d unexpanded
      then exists p_in v p_out, p' = p_out ++ v::p_in
           /\ In v unexpanded
           /\ (forall w, In w (p_out) -> In w unexpanded)
           /\ exists l, In (v, (hd_error p_in, l)) frontier
      else exists p, traceParent parent d = Some p
  ) /\ (
  (** [HfrontierParents]: Almost every node in the frontier has its parent already registered in the parent array. The exception is the start node, which does not have a parent. *)
    forall v parentPointer l, In (v, (parentPointer, l)) frontier ->
      match parentPointer with
      | None => v = s /\ l = 1
      | Some u => exists p,
          traceParent parent u = Some p /\ hasPath g s v (v::p) /\ length (v::p) = l
                                        (*todo: replace with hasEdge ? *)
      end
  ) /\ (
  (** [HfrontierSorted]: [extractMin]'s precondition holds. *)
    sorted foundPathLen frontier
  ) /\ (
  (** [HparentExpanded]: Everything that has a parent set is already expanded. *)
    forall n np, In (n, np) parent -> ~In n unexpanded
  ) /\ (
  (** [HparentPaths]: Each parent map entry either points to the start node or points to some node that points to the start node. *)
    forall n np, In (n, np) parent -> exists p, traceParent parent n = Some p
  ) /\ (
  (** [HparentPaths]: Every parent map entry represents a valid, shortest path to the specified node. *)
    forall n  p, traceParent parent n = Some p -> shortestPath g s n p
  ))
  (** The claim: when evaluated on an input that satisfies the said conditions  *)
    -> forall ret, bfs g unexpanded frontier parent = ret ->
  ((
  (** our [bfs] will find a path to each node to which there is a path  *)
    forall (d:node) (p':list node), hasPath g s d p' -> exists p, traceParent ret d = Some p
  ) /\ (
  (** and all paths our [bfs] finds will be valid shortest paths. *)
    forall (d:node) (p:list node), traceParent ret d = Some p -> shortestPath g s d p
  ))
.
  (* We prove the inductive case first and use the same names for the hypotheses as above. *)
  intros until parent.
  functional induction (bfs g unexpanded frontier parent). Focus 2.
  intros until ret; eapply IHl; clear IHl;
  splitHs; split; [|split;[|split;[|split;[|split]]]];
  rename H0 into HfrontierParents;
  rename H1 into HfrontierSorted;
  rename H2 into HparentExpanded;
  rename H3 into HparentSome;
  rename H4 into HparentPaths;
  (** The ways in which one iteration modifies the loop variables *)
  expandBFS;
  rename H0 into HparentPrepend;
  rename H1 into HfrontierInsert;
  rename H2 into HunepandedRemove;

  (specialize (closestUnexpanded_corr foundPathLen unexpanded frontier HfrontierSorted);
  destruct (closestUnexpanded foundPathLen unexpanded frontier); [|pv]; intro Hc;
  elim Hc; clear Hc; intros discarded Hc;
  destruct Hc as [Hfrontier_split [HdiscardedExpanded [HextractMin HminUnexpanded]]];
  destruct p; destruct f; myinj' Heqc; destruct p).

  { (** preservation of [H]: all paths to unexpanded nodes go through the frontier because every time [bfs] removes a node from the frontier it adds all nodes thtorugh which the path may have continued from it. *)
    remember H as Hd; clear HeqHd.
    intros d p' Hp'; specialize (Hd _ _ Hp').
    destruct (node_in_dec d unexpanded).

    Focus 2.
      destruct (node_in_dec d unexpanded');
        [assert (~ In d unexpanded') by (eapply remove_does_not_add; eauto); pv|].
      assert (In u unexpanded) by (
        specialize (closestUnexpanded_corr foundPathLen unexpanded frontier HfrontierSorted);
        destruct (closestUnexpanded foundPathLen unexpanded frontier); [|pv]; intro Hc;
        elim Hc; clear Hc; intros; splitHs; crush).
      assert (d <> u) by crush.
      elim Hd; intros p Hp; exists p.
      eauto using (parents_dont_disappear parent parent' _ _ d p HparentPrepend);
    fail "end Focus 2".
    destruct (node_eq_dec u d);
      [destruct (node_in_dec d unexpanded');
        [(specialize (remove_In node_eq_dec unexpanded d); crush)|]
      | destruct (node_in_dec d unexpanded');
        [|specialize (remove_preserves _ _ _ HunepandedRemove d); crush]].
    {
      rewrite <- e in *; clear e d.
      assert (forall x, In x discarded -> fst x <> u) by (
        intros x Hdiscarded; eapply in_notin_notsame; eauto).
      assert (In (u, pu) frontier) as Hfrontier_u.
        subst. eapply in_or_app; right; left; trivial.
      elim Hd; clear Hd; intros p_in  Hd;
      elim Hd; clear Hd; intros v     Hd;
      elim Hd; clear Hd; intros p_out Hd.
      destruct Hd as [Hp_split [HvUnexpanded [HwUnexpanded Hfrontier_v]]].
      elim Hfrontier_v; clear Hfrontier_v; intros vp Hfrontier_v.
      destruct pu as [[u_parent|] lu];
        elim (HfrontierParents _ _ _ Hfrontier_u); intros pu Hu_parent;
        [|splitHs; subst; exists [s]; simpl; destruct (node_eq_dec s s); [auto|congruence]].
      splitHs; repeat split; auto.
      subst. simpl. destruct (node_eq_dec u u); [|crush].
      destruct (traceParent parent u_parent); [|congruence].
      exists (u::l0); auto.
    } {
      elim Hd; clear Hd; intros p_in  Hd;
      elim Hd; clear Hd; intros v     Hd;
      elim Hd; clear Hd; intros p_out Hd.
      destruct Hd as [Hp_split [HvUnexpanded [HwUnexpanded Hfrontier_v]]].
      elim Hfrontier_v; clear Hfrontier_v; intros vp Hfrontier_v.
      remember Hfrontier_v as HIn; clear HeqHIn.
      remember HIn as HInFrontier; clear HeqHInFrontier.
      (* todo: separate this out *)
      rewrite Hfrontier_split in HIn; rename HIn into HIn';
        destruct (in_app_or _ _ (v, _) HIn') as [HIn|HIn]; clear HIn'. {
        specialize (HdiscardedExpanded (v, _) HIn); simpl in *.
        destruct vp; specialize (HfrontierParents _ _ _ Hfrontier_v); crush.
      } 
      (* *)

      assert (forall w, In w (p_out ++ [v]) -> In w unexpanded) as HwvUnexpanded by
        (subst; intros; destruct (in_app_or _ _ _ H0); eauto; inversion H1; crush).
      assert (Some u <> hd_error (p_out ++ [v])) as HhdOut by
        (rewrite <- (hd_of_sublist p_out p' p_in v Hp_split);
         rewrite (d_head_path g s d p' Hp');
         unfold not; intros Hud; apply n1; inversion Hud; crush).
      eelim (HextendFrontier _ v u HhdOut unexpanded HwvUnexpanded).
      {
        intros Hv'.
        elim Hv'; clear Hv'; intros p_skip Hv'.
        elim Hv'; clear Hv'; intros v' Hv'.
        elim Hv'; clear Hv'; intros p_out' Hv'.
        simpl in Hv'; destruct Hv' as [Hp_split' [[Hv' Hws'][Hu_neq_v Hu_neq_w]]].
        exists (u::p_skip ++ p_in). exists v'. exists p_out'. repeat split.
        - replace (p_out ++ v::p_in) with (p_out ++ [v] ++ p_in) in * by crush.
          rewrite app_assoc in *. rewrite Hp_split' in *.
          rewrite Hp_split. rewrite <- app_assoc. auto.
        - assert (In v unexpanded) by (eapply HwvUnexpanded; crush).
          eapply remove_preserves; eauto.
        - intros; eapply (remove_preserves _ _ _ HunepandedRemove); eauto.
        - rewrite <- HfrontierInsert. exists (S (foundPathLen (u, pu))).
          (* insert along with other things, and guess what, it is in there *)
          eapply insert_many_in. auto. left.
          rewrite Hp_split in Hp'.
          replace (p_out ++ v :: p_in) with (p_out ++ [v] ++ p_in) in * by crush.
          rewrite app_assoc in Hp'. rewrite Hp_split' in Hp'.
          assert (hasEdge g u v') as Hhas_u_v by
            (remember ((p_out' ++ v' :: u :: p_skip) ++ p_in) as g';
             rewrite <- (list_last_next_first) in Heqg';
             apply (in_path_edge _ _ _ _ _ _ Heqg' _ _ _ Hp')).
          generalize (edge_in_neigh _ _ _ (eq_sym Heqneighbors) _ Hhas_u_v); intro HuvInNeigh.
          exact (in_neigh_in_map _ _ _ HuvInNeigh).
      }

      intros HNoInterference.
      exists p_in; exists v; exists p_out.
      destruct (HNoInterference v) as [HvNequ _]; [crush|].
      repeat split; eauto.
      - eauto using remove_preserves.
      - intros; assert (In w (p_out ++ [v])) by crush. 
        destruct (HNoInterference w); eauto using remove_preserves.
      - exists vp. eapply insert_many_in; eauto; right.
        destruct HIn; [congruence|]. assumption.
    }
  }

  { (** Every parent of a node in [frontier] has an entry in [parent] because when [bfs] add a node's neighbors to [frontier] it also adds the node itself to [parent]. *)
    intros v vp vl.
    revert Hfrontier_split; intro; revert HfrontierInsert; intro.
    generalize (HfrontierParents v vp vl); intro Hfrontier.
    intros Hin.

    destruct (in_many_insert foundPathLen _ _ _ HfrontierInsert _ Hin) as [Hnew|Halready].
    Focus 2. (* if the node was already in the frontier *)
      assert (frontier = (discarded ++ [(u, pu)]) ++ frontierRemaining) as Hfrontier_split2 by crush.
      remember (in_or_app (discarded++[(u,pu)]) _ _ (or_intror Halready)) as Hbefore; clear HeqHbefore.
      rewrite <- Hfrontier_split2 in Hbefore.
      specialize (Hfrontier Hbefore); clear Hin Halready Hbefore Hfrontier_split2.
      destruct vp; [|auto].
      elim Hfrontier; clear Hfrontier; intros p Hfrontier.
      exists p. split; try solve [splitHs; eauto].
      destruct Hfrontier as [Hfrontier _].
      rewrite <- HparentPrepend; simpl.
      destruct (node_eq_dec n1 u); [|rewrite Hfrontier]; pv.
      replace n1 with u in * by assumption; clear e.
      assert False; [|pv].
      elim (traceparent_in _ _ _ Hfrontier); intros.
      apply (fun pf => HparentExpanded u x pf HminUnexpanded). auto;
    fail "end Focus 2".

    assert (In (u,pu) frontier) as HuInFrontier.
      rewrite Hfrontier_split; apply in_or_app; right; left; crush.
    destruct pu as [upptr ul].
    generalize (HfrontierParents _ _ _ HuInFrontier) as HuReachable; intro.
    generalize (lookup_neighbors _ _ _ (eq_sym Heqneighbors)) as HneighborEdges; intro.

    revert HuReachable Hnew HparentPrepend HneighborEdges; clear;
    intros HuReachable Hnew HparentPrepend HneighborEdges.
    induction neighbors; [pv|].
    simpl in Hnew; destruct Hnew as [HNow|Hbefore].
    Focus 2.
      eapply IHneighbors; clear IHneighbors; eauto.
      intros v0 Hv0. eapply HneighborEdges; right; eauto;
    fail "end Focus 2".
    clear IHneighbors.
    injection HNow; clear HNow; intros.
    destruct vp; [|pv].
    rewrite <- HparentPrepend.
    replace a with v in * by auto.
    replace n with u in * by (injection H0; auto).
    destruct upptr as [u_parent|]. {
      elim HuReachable; intros u_parent_path Hu_parent_path. exists (u::u_parent_path).
      repeat split; splitHs.
      - simpl. destruct (node_eq_dec u u); [|pv]. rewrite H2; reflexivity.
      - econstructor; eauto. eapply HneighborEdges; crush.
      - simpl. replace (S (length u_parent_path)) with ul by auto.
        unfold foundPathLen in *; auto.
    } {
      elim HuReachable; intros; splitHs; subst.
      exists [s]; repeat split; simpl; eauto.
      - destruct (node_eq_dec s s); pv.
      - econstructor. instantiate (1:=s). constructor. eapply HneighborEdges; crush.
    }
  }

  { (** Frontier is sorted due to the properties of [insert] and [extractMin] *)
    (* sorted frontier'*)
    rewrite <- HfrontierInsert.
    eapply insert_many_sorted; eauto.
    assert (sorted foundPathLen ((u, pu) :: frontierRemaining))
      by (subst; eauto using app_right_sorted).
    eauto using sorted_tail.
  }

  { (** Every node in parent is expanded because [bfs] marks a node expanded right when it adds that node to parent *)
    intros v vp Hv.
    assert ((v,vp)=(u,pu) \/ In (v,vp) parent) as Heither.
      assert (In (v, vp) ([(u, pu)] ++ parent)) as Hl by crush.
      specialize (in_app_or [(u,pu)] parent (v,vp) Hl); intro Hor.
      destruct Hor as [[Ha|Hf]|Hb]; [left|inversion Hf|]; auto.
    destruct Heither as [Heq|Hin]; [myinj' Heq; subst; apply remove_In|].
    generalize (HparentExpanded v vp Hin) as HwasExpanded; intro.
    eapply remove_does_not_add; eauto.
  }

  { (** [bfs] only adds paths to parent by extending a path that is already in parent, so all paths in parent start from the start node *)
    rewrite <- HparentPrepend.
    revert HparentPaths; intro.
    intros v vp Hvp.
    (* todo: refactor this out *)
    assert ((v,vp)=(u,pu) \/ In (v,vp) parent) as Heither.
      assert (In (v, vp) ([(u, pu)] ++ parent)) as Hl by crush.
      specialize (in_app_or [(u,pu)] parent (v,vp) Hl); intro Hor.
      destruct Hor as [[Ha|Hf]|Hb]; [left|inversion Hf|]; auto.
    (* *)
    destruct Heither as [Heq|Hin].
    Focus 2.
      eelim HparentSome; eauto; intros p Hp.
      exists p.
      simpl. destruct (node_eq_dec v); [|rewrite Hp; auto].
      rewrite e in *; clear e.
      assert False; [|pv].
      elim (traceparent_in _ _ _ Hp); intros.
      apply (fun pf => HparentExpanded u x pf HminUnexpanded). auto;
    fail "end Focus 2".

    myinj' Heq.
    assert (In (u,pu) frontier) as HuInFrontier.
      rewrite Hfrontier_split; apply in_or_app; right; left; crush.
    destruct pu as [upptr ul].
    generalize (HfrontierParents _ _ _ HuInFrontier) as HuReachable; intro.
    generalize (lookup_neighbors _ _ _ (eq_sym Heqneighbors)) as HneighborEdges; intro.
    destruct (node_eq_dec u u); [|pv].
    destruct upptr as [u_parent|]. {
      elim HuReachable; clear HuReachable; intros u_parent_path Hu_parent_path.
      exists (u::u_parent_path).
      destruct Hu_parent_path as [Hu_parent_lookup]; rewrite Hu_parent_lookup.
      splitHs; split; auto.
    } {
      exists [u].
      splitHs; subst; split; auto; constructor.
    }
  }
  
  { (** The paths added to [parent] are shortest paths to their destination because any alternative path would have to go through the frontier, the path to anything on the frontier is at least as long as the path to the parent of the node we are adding, and the path to the parent of the node in the frontier is known to be optimal because it is already in [parent]. *)
    intros v p Hvp.
    rewrite <- HparentPrepend in Hvp.
    revert HparentPaths; intro.
    simpl in Hvp.
    destruct (node_eq_dec v u). {
      assert (In (u,pu) frontier) as HuInFrontier.
        rewrite Hfrontier_split; apply in_or_app; right; left; crush.
      destruct pu as [upptr lu].
      generalize (HfrontierParents _ _ _ HuInFrontier) as HuReachable; intro.
      generalize (lookup_neighbors _ _ _ (eq_sym Heqneighbors)) as HneighborEdges; intro.
      rewrite e in *; clear e v.
      destruct upptr as [u_parent|]. {
        elim HuReachable; clear HuReachable; intros u_parent_path Hu_parent_path.
        destruct Hu_parent_path as [Hu_parent_Some [Hu_parent_reachable Hupp_length]].
        rewrite Hu_parent_Some in Hvp.
        injection Hvp; clear Hvp; intro Heq; rewrite <- Heq; clear Heq.
        split; auto.
        (* a new non-trivial path we add to parent is shortest *)
        intros p' Hp'.
        generalize (H u p' Hp') as He; intro.
        destruct (node_in_dec u unexpanded) as [HeuUnexpanded|]; [|congruence].
        elim He; clear He; intros p_in He.
        elim He; clear He; intros v He.
        elim He; clear He; intros p_out He.
        destruct He as [Hsplit_p [HvUnexpanded [Hp_out HvFrontier]]].
        rewrite Hsplit_p in *; clear Hsplit_p.
        elim HvFrontier; clear HvFrontier; intros lv HvFrontier.
        generalize HvFrontier; intro HIn.
        generalize (HfrontierParents _ _ _ HvFrontier); intro Hv_parent.
        (* todo: separate this out? HdiscardExpanded + Hfrontier_split *)
        rewrite Hfrontier_split in HIn; rename HIn into HIn'.
        destruct (in_app_or _ _ (v, _) HIn') as [HIn|HIn]; clear HIn'. {
          specialize (HdiscardedExpanded (v, _) HIn); crush.
        } 
        (* *)
        assert (lv >= lu) as Hge. {
          simpl in HIn. destruct HIn as [HIn | HIn].
            inversion HIn. omega.
            assert (foundPathLen (v,(hd_error p_in, lv)) >= foundPathLen (u, (Some u_parent, lu)))
              as Hge' by (apply HextractMin; simpl in *; auto).
            unfold foundPathLen in Hge'. simpl in Hge'. auto.
        }
        simpl; rewrite Hupp_length; clear Hupp_length.
        assert (length (p_out++v::p_in) >= lv); [|omega]; clear Hge.
        remember (hd_error p_in) as hd_p_in.
        destruct hd_p_in as [v_parent|]; [|induction p_out; crush].
        elim Hv_parent; clear Hv_parent; intros v_parent_path Hv_parent_path.
        destruct Hv_parent_path as [Hv_parent_Some [Hv_parent_reachable Hvpp_length]].
        destruct (HparentPaths _ _ Hv_parent_Some) as [_ Hv_parent_shortest].
        replace lv with (S (length v_parent_path)) by auto; clear Hvpp_length.
        assert (forall a b, a >= b -> S a >= S b) as HgeS by crush.
        assert (forall a b, a >= b -> forall a0, a0 + a >= b) as HgePlus by crush.
        assert (length p_in >= length v_parent_path);
          [|subst;rewrite app_length; rewrite plus_comm; simpl;
            rewrite plus_comm; apply HgeS; apply HgePlus; auto].
        eapply Hv_parent_shortest.
        destruct p_in as [|v_parent_]; [inversion Heqhd_p_in|].
        symmetry in Heqhd_p_in; myinj' Heqhd_p_in.
        assert (forall x xs y ys, hasPath g s x (xs ++ y :: ys)
                               -> hasPath g s y (      y :: ys))
          as HsubPath by
          (intros; apply (reachable_halfway g s xs x y ys); auto).
        replace ( p_out ++  v  :: v_parent :: p_in)
           with ((p_out ++ [v]) ++ v_parent :: p_in) in * by crush.
        eauto.
      } {
        destruct HuReachable.
        injection Hvp; intro; subst; split.
        - constructor.
        - intros. simpl. inversion H0; crush.
      }
    }
    remember (traceParent parent v) as tracePv; destruct tracePv; [|inversion Hvp].
    myinj' Hvp.
    symmetry in HeqtracePv.
    eapply HparentPaths; trivial.
  }

  (** Base case: our invariants imply the conclusion *)
  Unfocus.
  
  intros; splitHs;
  rewrite <- H0 in *; clear ret H0;
  rename H1 into HfrontierParents;
  rename H2 into HfrontierSorted;
  rename H3 into HparentExpanded;
  rename H4 into HparentSome;
  rename H5 into HparentPaths;
  split.

  { (** [parent] has a path to each reachable node, because all paths to reachable nodes which are not in [parent] must go through the frontier, and [frontier] only contains nodes that are already expanded. *)
    intros d p' Hp'.
    revert H; intro.
    specialize (H d p' Hp').
    destruct (node_in_dec d unexpanded). {
      unfold bfs_step in *.
      remember (closestUnexpanded foundPathLen unexpanded frontier) as c.
      destruct c; [pv|]; clear e.
      specialize (closestUnexpanded_corr _ unexpanded _ HfrontierSorted);
        intro HfrontierExpanded; rewrite <- Heqc in HfrontierExpanded.
      elim H; clear H; intros p_in H.
      elim H; clear H; intros v H.
      elim H; clear H; intros p_out H.
      destruct H as [_ [HvUnexpanded [_ HvFrontier]]].
      elim HvFrontier; clear HvFrontier; intros vp HvFrontier.
      specialize (HfrontierExpanded _ HvFrontier).
      destruct (HfrontierExpanded HvUnexpanded).
    }
    elim H; intros p Hp.
    exists p. splitHs; auto.
  }

  {
    (** All paths in [parent] are shortest, and we return [parent], so all paths in [ret] are shortest *)
    intros d p' Hp'.
    exact (HparentPaths d p' Hp').
  }

Qed.

(** * A wrapper that initializes the internal variables and calls [bfs] *)

(** All nodes in a graph, to be marked unexpanded before [bfs] starts *)
Fixpoint nodes (g:graph) : list node :=
  match g with
  | nil => nil
  | adj::g' =>  fst adj :: snd adj ++ nodes g'
  end.

Lemma hasEdge_in_nodes:
  forall g u v, hasEdge g u v -> In u (nodes g) /\ In v (nodes g).
Proof.
  unfold hasEdge; unfold lookupDefault.
  intros g u v H.
  remember (lookup g u) as lookupRes; destruct lookupRes; [|pv].
  specialize (lookup_in g u l (eq_sym HeqlookupRes)); intro H1.
  clear HeqlookupRes.
  split; generalize dependent l; induction g; [auto| |auto| ];
    (simpl; intros; destruct H1; [crush|right]; apply in_or_app; right; eauto).
Qed.

Lemma hasPath_in_nodes:
  forall g u v p, hasPath g u v p -> In u (nodes g) -> In v (nodes g).
Proof.
  induction 1; crush. specialize (hasEdge_in_nodes g u v); crush.
Qed.

Lemma hasPath_in_nodes':
  forall g u v p, hasPath g u v p -> u <> v -> In v (nodes g).
Proof.
  induction 1; crush. specialize (hasEdge_in_nodes g u v); crush.
Qed.

Lemma hasPath_path_in_nodes:
  forall g u v p, hasPath g u v p ->
  forall w, In w (removelast p) -> In w (nodes g).
Proof.
  induction 1; [crush|].
  intros.
  destruct p; [crush|].
  replace (removelast (v :: n :: p)) with (v::removelast (n :: p)) in * by crush.
  destruct H1; [|eauto]; clear IHhasPath.
  subst. eapply hasEdge_in_nodes; eauto.
Qed.

(** the wrapper *)
Definition bfs' g s := bfs g (s::nodes g) [(s,(None,1))] [].

Lemma hasPath_tail: forall g s d p, hasPath g s d p -> p = removelast p ++ [s].
  (* XXX: crush hangs here *)
  induction 1; [reflexivity|].
  simpl in *; destruct p; [unfold not; intros; subst; simpl in *; congruence|].
  rewrite <- app_comm_cons.
  apply f_equal; apply IHhasPath.
Qed.

(* Calling [bfs] from the outside satisfies its invariants with the initial conditions, therefore the output will satisfy the postcondition. *)
Lemma bfs_corr':
  forall (g:graph) (s:node) ret, bfs' g s = ret ->
  ((
    forall (d:node) (p':list node), hasPath g s d p' -> exists p, traceParent ret d = Some p
  ) /\ (
    forall (d:node) (p:list node), traceParent ret d = Some p -> shortestPath g s d p
  )).
  unfold bfs'.
  intros.
  eapply bfs_corr; [|apply H]; clear H; repeat split; intros; try solve [pv].
  { destruct (node_in_dec d (s::nodes g)).
    - exists []. exists s. exists (removelast p'). repeat split.
      + eapply hasPath_tail; eauto.
      + left; reflexivity.
      + intros. right. eapply hasPath_path_in_nodes; eauto.
      + exists 1. left; reflexivity.
    - assert False; [|pv]; apply n.
      destruct (node_eq_dec s d).
      + left; trivial.
      +  right. eapply hasPath_in_nodes'; eauto.
  }
  {
    destruct H; [|pv].
    destruct parentPointer.
    - assert False; [|pv]. assert (Some n = None) by crush; crush.
    - crush.
  }
Qed.

(** Example sanity-check *)
Section ex1. (* BFS example from CLRS 3rd edition *)
  Notation r := (Node 0). Notation v := (Node 4).
  Notation s := (Node 1). Notation w := (Node 5).
  Notation t := (Node 2). Notation x := (Node 6).
  Notation u := (Node 3). Notation y := (Node 7).
  Definition g :=
  [ (v, [r])
  ; (r, [v; s])
  ; (s, [r; w])
  ; (w, [s; t; x])
  ; (t, [u; x; w])
  ; (u, [t; x; y])
  ; (x, [w; t; u; y])
  ; (y, [x; u])
  ].

  Example bfs_ex1 : traceParent (bfs' g s) v = Some [v;r;s]. reflexivity. Qed.
  Eval compute in (bfs' g s).
End ex1.
