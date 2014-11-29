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
Require Import Coq.omega.Omega.
Require Import CpdtTactics.
Require Import List.
Import ListNotations.

Inductive node := Node : nat -> node.

Definition node_eq_dec : forall (x y:node), {x = y} + {x <> y}.
  decide equality. apply eq_nat_dec.
Defined.
Definition node_eq_decb a b := if node_eq_dec a b then true else false.

Lemma node_eq_decb_corr : forall a b, a = b <-> node_eq_decb a b = true.
Proof.
  intros; split; intro H; unfold node_eq_decb in *;
  remember (node_eq_dec a b) as aisb; destruct aisb; auto.
  inversion H.
Qed.

Definition node_in_dec := in_dec node_eq_dec.

Definition adj := (node * list node)%type.
Definition graph := list adj.
Definition found := (node * (option node*nat))%type.
Definition foundPathLen (p:found) : nat := snd (snd p).

(** keys g gives all the first parts of adjs in a graph g (list of nodes) **)
Definition keys {A:Type} := map (@fst node A).

Definition lookup {A:Type} (ps:list(node*A)) (x:node) :=
    match find (fun p => node_eq_decb x (fst p)) ps with
    | Some p => Some (snd p)
    | None => None
    end.

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
Admitted.

Lemma lookup_corr : forall {A:Type} ps, NoDup (keys ps) ->
    forall x (y:A), lookup ps x = Some y <-> In (x, y) ps.
Proof.
  intros. split. apply lookup_in. apply in_lookup; crush.
Qed.

Definition hasEdge (g:graph) u v := exists vs, lookup g u = Some vs /\ In v vs.

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

Lemma extractMin_shorter : forall {A:Type} (f:A->nat) (frontier : list A),
  forall x xs, extractMin f frontier = Some (x,xs) ->
  length frontier = S (length xs).
Proof.
  intros. unfold extractMin in *. destruct frontier.
  crush.
  inversion H. crush.
Qed.

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


(* inlining bfs_step to bfs did NOT give us functional induction, but
   separating it out did... *)
Definition bfs_step
  (g:graph) (unexpanded:list node) (frontier:list found) (parent:list found)
  := match closestUnexpanded foundPathLen unexpanded frontier with
  | None => None
  | Some p => let (found_u, frontierRemaining) := p in
          let u := fst found_u in
          let l := foundPathLen found_u in
          let parent' := found_u::parent in
          let unexpanded' := remove node_eq_dec u unexpanded in
          match lookup g u with
          | None => None (* invalid graph *)
          | Some neighbors =>
              let frontierNew := map (fun v => (v, (Some u, 1+l))) neighbors in
              let frontier' := fold_right (insert foundPathLen) frontierRemaining frontierNew in
              Some (unexpanded', frontier', parent')
          end
  end.

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
          ; match goal with [H : context[lookup g (fst ?found_u)] |- _ ]
              =>remember (lookup g (fst found_u)) as k
              ; let uu := fresh "u" in let pu := fresh "pu" in
                  destruct found_u as [uu pu]
              ; destruct k; [|inversion H]
            end
          ; match goal with [H : Some ?ns = lookup _ _ |- _ ]
              =>simpl in H; symmetry in H
              ; let neighs := fresh "neighbors" in rename ns into neighs
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

Functional Scheme bfs_ind := Induction for bfs Sort Prop.

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
           | None => Some nil
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

Inductive reachableUsing : graph -> node -> node -> list node -> Prop :=
| IdPath : forall g s, reachableUsing g s s []
| ConsPath : forall g s d p,               reachableUsing g s d    p   ->
             forall d', hasEdge g d d' ->  reachableUsing g s d' (d'::p).

Lemma removing_corr_item : forall x xs xs',
  remove node_eq_dec x xs = xs' ->
  forall x', ~(In x' xs') -> In x' xs -> x = x'.
Proof.
Admitted.

Lemma not_None : forall {A:Type} (sx:option A), sx <> None -> exists x, sx = Some x.
  intros. destruct sx; [|congruence]. eauto.
Qed.

Notation shortestPath g s d p := (
  reachableUsing g s d p
  /\
  (forall p', reachableUsing g s d p' -> length p' >= length p)).

Lemma bfs_corr:
  forall (g:graph) (s:node),
  forall (unexpanded:list node) (frontier:list found) (parent:list found),
  ((
    forall (d:node) (p':list node), reachableUsing g s d p' ->
      if node_in_dec d unexpanded
      then exists v, In v p' /\ exists vp, lookup frontier v = Some vp
      else exists p, traceParent parent d = Some p /\ shortestPath g s d p
  ) /\ (
    forall v parentPointer l, lookup frontier v = Some (parentPointer, l) ->
      In v unexpanded /\
      match parentPointer with
      | None => v = s /\ l = 1
      | Some u => exists p, traceParent parent u = Some p /\ shortestPath g s v (v::p)
      end
  ) /\ (
    forall v p, traceParent parent v = Some p -> ~ In v unexpanded
  ) /\ (
    sorted foundPathLen frontier
  ) /\ (
    forall v, In v unexpanded -> In v (keys g)
  ))
    -> forall ret, bfs g unexpanded frontier parent = ret ->
  ((
    forall (d:node) (p':list node), reachableUsing g s d p' ->
    exists p, traceParent ret d = Some p /\ shortestPath g s d p
  ))
.
  intros until parent.
  functional induction (bfs g unexpanded frontier parent). Focus 2.
  intros; eelim IHl; clear IHl; repeat split; [..|eauto]; auto; splitHs;
    [intro x; exists x; subst; assumption|..];
  rename H2 into HfrontierParents;
  rename H3 into HparentExpanded;
  rename H4 into HfrontierSorted;
  rename H5 into HunexpandedNodes;
  clear dependent p'; clear dependent d; clear dependent ret.

  {
  expandBFS.
    rename H0 into HparentPrepend;
    rename H1 into HfrontierInsert;
    rename H2 into HfrontierRemove.

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
    elim Hd; intros p Hp; exists p; destruct Hp.
    split; [apply (parents_dont_disappear parent parent' _ _ d p HparentPrepend)|]; auto;
  fail "end Focus 2".

  specialize (closestUnexpanded_corr foundPathLen unexpanded frontier HfrontierSorted);
  destruct (closestUnexpanded foundPathLen unexpanded frontier); [|pv]; intro Hc;
  elim Hc; clear Hc; intros; splitHs.
  destruct p; destruct f; myinj' Heqc. destruct p.
  destruct (node_eq_dec u d);
    [destruct (node_in_dec d unexpanded');
      [(specialize (remove_In node_eq_dec unexpanded d); crush)|]
    | destruct (node_in_dec d unexpanded');
      [|specialize (remove_preserves _ _ _ HfrontierRemove d); crush]].
  {
    rewrite <- e in *; clear e d.
    rename x into discarded.
    assert (forall x, In x discarded -> fst x <> u) by (
      intros x Hdiscarded; specialize (H1 x Hdiscarded);
      eapply in_notin_notsame; eauto).
    assert (lookup frontier u = Some pu) as Hlookup_u by (
      subst; eapply lookup_head; eauto).
    elim Hd; clear Hd; intros v Hv.
    destruct Hv as [HvInp' Hlookup_v]; elim Hlookup_v; clear Hlookup_v; intros pv Hlookup_v.
    destruct pu as [[u_parent|] lu];
        generalize (HfrontierParents _ _ _ Hlookup_u); intro; splitHs.
    Focus 2. subst; exists []; simpl; destruct (node_eq_dec s s); repeat split;
      [constructor
      |intros; destruct p'0; simpl; omega
      |congruence
      |constructor
      |intros; destruct p'0; simpl; omega
      ];
    fail "end Focus 2".
    destruct pv as [vpp lv];
        generalize (HfrontierParents _ _ _ Hlookup_v) as Hv_parent;
          intro; destruct Hv_parent as [HvUnexpanded Hvpp].
    unfold foundPathLen in *; simpl in *.
    assert (~ In (v,(vpp,lv)) discarded) by
      admit.
    assert (In (v,(vpp,lv)) ((u, (Some u_parent, lu)) :: frontierRemaining)) as HvI by
      admit.
    assert (lv >= lu) by
      admit.
    elim H6; clear H6; intros p Hp; exists (u::p).
    splitHs; repeat split; auto.
    revert H6; subst. simpl. destruct (node_eq_dec u u); [|crush].
    destruct (traceParent parent u_parent); [|congruence]. intro. myinj H6. auto.
  } {
    elim Hd; intro v; intro Hv; destruct Hv as [Hvp Hv].
    assert (exists ff, lookup frontier v = Some ff) as HexSome by
      (destruct (lookup frontier v) as [px|]; [exists px; auto|congruence]);
    elim HexSome; clear HexSome; intros res Hres.
    remember (lookup_in frontier v res Hres) as Hin; clear HeqHin.
    remember Hin as HinFrontier; clear HeqHinFrontier.
    rewrite H0 in Hin; destruct (in_app_or _ _ (v, res) Hin) as [Hswh|Hswh]. {
      specialize (H1 (v, res) Hswh); simpl in *.
      destruct res; destruct (HfrontierParents _ _ _ Hres) as [Hunexpanded _]; pv.
    } simpl Hswh; destruct Hswh.
    Focus 2.
      exists v. split; [auto|].
      assert (In (v, res) frontier') as HinFrontier' by admit.
      elim (in_lookup' frontier' v res HinFrontier'); intros.
      exists x0; trivial;
    fail "end Focus1".
    symmetry in H4; myinj' H4; clear H4.
    destruct pu as [[v_parent|] vl]; destruct (HfrontierParents _ _ _ Hres).
    elim H11; clear H11; intros v_path Hv_path; splitHs.
    subst.
    }
    }

      (* end of reasonable region *)


  (*
      elim (in_lookup' frontier _ _ HinFrontier); intros res' H12;
        destruct res' as [[u'|] lv].
      destruct (H3 _ _ _ H12) as [_ Hupto].
      destruct parentPointer


       elim H; clear H; intros v H; exists v; intro Hv; specialize (H Hv).
       subst.
       Focus 2.
       elim H; clear H; intros s H; exists s.
       elim H; clear H; intros p H; exists p.
  *)

         (* probably bogus attempt at length p' >= length (u_parent :: p)
         assert (~ In u_parent unexpanded) by (apply (HparentExpanded u_parent p); auto).
         generalize (Hcopy u_parent); destruct (node_in_dec u_parent unexpanded); [pv|].
         intro H'.
         rewrite H10 in H'.
         assert (forall s'' p'', In s'' start -> reachableUsing g s'' u_parent p'' ->
          length p'' >= length p
         ). {
           intros s'' p'' Hs'' Hp''; elim (H' s'' p'' Hs'' Hp''); clear H'.
           intros s_ H'; elim H'; clear H'; intros p_; intros.
           splitHs.
           replace p_ with p in * by
              (destruct (list_eq_dec node_eq_dec p p_); congruence).
           auto.
         }
         generalize dependent p'.
         generalize dependent s'.
        *)

  (*
    replace d with u in *; subst.
    assert (~ In u (remove node_eq_dec u unexpanded)) by (apply remove_In);
      destruct (node_in_dec u (remove node_eq_dec u unexpanded)); [pv|].
    Check (closestUnexpanded_corr foundPathLen unexpanded frontier).
    destruct (node_in_dec d unexpanded); [|pv].
  *)
  (*
    Focus 2.
      destruct (node_in_dec d unexpanded);
        [assert (In d unexpanded') by (eapply remove_preserves; eauto)
        |assert (~ In d unexpanded') by (eapply remove_does_not_add; eauto)];
       destruct (node_in_dec d unexpanded'); try solve [pv];
       intros s' p' Hs' Hp'; specialize (H s' p' Hs' Hp');
       revert H; intro H.
       elim H; clear H; intros v H; exists v; intro Hv; specialize (H Hv).
       Focus 2.
       elim H; clear H; intros s H; exists s.
       elim H; clear H; intros p H; exists p.
       splitHs; repeat split; try assumption.
   *)
Qed.
