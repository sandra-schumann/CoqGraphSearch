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
  compute. (* Why does it not work? *)
Abort.

Lemma no_aliens : forall g s parent, bfs g s = parent ->
    forall u v, In (u, v) parent ->
    exists neighbors, In (v, neighbors) g /\ In u neighbors.
Admitted.

(* This assumes that the statement (u's parent is v) comes before any statement
 about v's parents. This is true in out BFS implementation, and will probably
 remain true for any extension of it, but it is not an integral property of BFS
 -- it is just a requirement on the output format. We could get id of this
 requirement, but then the termination argument for traceParent would depend on
 the assumption that parsing the parent map does not lead to cyclic paths. *)
Fixpoint traceParent (parent:parent_t) (u:node) {struct parent} : list node :=
  match parent with
  | nil => []
  | p::parent' =>
    if node_eq_dec (fst p) u
    then (snd p)::(traceParent parent' (snd p))
    else traceParent parent' u
end.

Example ex2 :
  traceParent [(Node 3, Node 2); (Node 2, Node 0); (Node 1, Node 0)] (Node 3) =
  [Node 2; Node 0].
Abort. (* Why does this not work again... *)
