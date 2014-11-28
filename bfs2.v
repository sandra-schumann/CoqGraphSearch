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
Definition keys := map (@fst node (list node)).

Definition lookup {A:Type} (ps:list(node*A)) (x:node) :=
    match find (fun p => node_eq_decb x (fst p)) ps with
    | Some p => Some (snd p)
    | None => None
    end.

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

Lemma in_fst_in_keys :
  forall x y ps, In (x, y) ps -> In x (keys ps).
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

Lemma in_lookup : forall ps, NoDup (keys ps) ->
    forall x y, In (x, y) ps -> lookup ps x = Some y.
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

Lemma lookup_corr : forall ps, NoDup (keys ps) ->
    forall x y, lookup ps x = Some y <-> In (x, y) ps.
Proof.
  intros. split. apply lookup_in. apply in_lookup; crush.
Qed.

Definition hasEdge (g:graph) u v := exists vs, lookup g u = Some vs /\ In v vs.

Lemma remove_length' : forall v vs, length vs >= length (remove node_eq_dec v vs) /\
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

Lemma closestUnexpanded_corr : forall f unexpanded frontier,
  sorted f frontier ->
    match closestUnexpanded f unexpanded frontier with
    | None => forall p, In p frontier -> ~ In (fst p) unexpanded
    | Some ret =>
        exists discarded, frontier = discarded ++ [fst ret] ++ snd ret
        (* it would suffice if frontier was just a permutation of the above *)
        /\ (forall p, In p discarded -> ~ In (fst p) unexpanded)
        /\ (forall p, In p (snd ret) ->   In p frontier /\ f p >= f (fst ret))
    end.
Proof.
  intros. remember (closestUnexpanded f unexpanded frontier) as oret.
  destruct oret.

  functional induction (closestUnexpanded f unexpanded frontier).
  crush.
  myinj Heqoret. remember (extractMin_as_sum _ _ _ _ e) as H1; clear HeqH1.
  exists []. split. simpl. auto. split. auto.
  intros. split. simpl in *. crush. simpl.
  remember (extractMin_corr _ _ H) as H2; clear HeqH2.
  remember (extractMin f frontier) as Hmin in *. destruct Hmin.
  inversion e. simpl in *. destruct p1. myinj H4.
  simpl in *. apply H2. right. auto.
  simpl in *. inversion e.
  eelim IHo; [..|eauto]. clear IHo.
  intros. destruct H0 as [H1 [H2 H3]].
  exists (p0::x).
  split. simpl in *. apply (extractMin_as_sum f). subst. auto.
  split; intros.
  simpl in *. destruct H0 as [H0 | H0].
  subst; auto.
  apply H2. apply H0.
  remember (extractMin_as_sum f _ _ _ e) as H4; clear HeqH4.
  subst. split. simpl. right. apply H3. apply H0.
  apply H3. apply H0. remember (extractMin_as_sum f _ _ _ e) as H4; clear HeqH4.
  eapply sorted_tail. apply H. apply H4.

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

Lemma remove_does_not_add : forall (u:node) (xs:list node) (ys:list node),
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
Admitted.

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
                       | Some path => Some (u::path)
                       end
           end
      else match traceParent parent' v with
           | None => None
           | Some path => Some path
           end
  end.

Inductive reachableUsing : graph -> node -> node -> list node -> Prop :=
| IdPath : forall g s, reachableUsing g s s []
| ConsPath : forall g s d p,               reachableUsing g s d    p   ->
             forall d', hasEdge g d d' ->  reachableUsing g s d' (d::p).

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

Lemma bfs_corr:
  forall (start:list node),
  forall (g:graph) (unexpanded:list node) (frontier:list found) (parent:list found),
  ((
    forall (s:node), In s start ->
    forall (d:node),
      if node_in_dec d unexpanded
      then forall p, reachableUsing g s d p ->
           exists v, In v p -> lookup frontier v <> None
      else forall p', reachableUsing g s d p' ->
           exists p,  traceParent parent d = Some p /\
                      reachableUsing g s d p /\ length p' >= length p
  ) /\ (
    forall v parentPointer l, lookup frontier v = Some (parentPointer, l) ->
      match parentPointer with
      | None => In v start
      | Some u => hasEdge g u v
           (* we need more here:
                - the path is as long as it says on the tin
                - the path is described in parent
           *)
      end
      (* we probably don't need another copy of this claim for parent because
        [reachableUsing] already requires that the edge exists *)
  ) /\ (
    forall v, In v unexpanded -> In v (keys g)
  ))
    -> forall ret, bfs g unexpanded frontier parent = ret ->
  ((
    forall (s:node), In s start -> forall d,
    forall p', reachableUsing g s d p' ->
    exists p , traceParent ret d = Some p /\
               reachableUsing g s d p /\ length p' >= length p
  ))
.
  intros until parent.
  functional induction (bfs g unexpanded frontier parent).
  Focus 1. admit.
  intros.
  eelim IHl; clear IHl; repeat split; [..|eauto]; auto; splitHs.
  Focus 1. intros. exists x. subst. assumption.
  Focus 1. expandBFS.
    intros s' Hs' d'.
    destruct (node_in_dec d' unexpanded'). {
     specialize (remove_does_not_add _ unexpanded unexpanded' H7 d' i); intro.
     specialize (H s' Hs' d').
     destruct (node_in_dec d' unexpanded); [|pv].
     revert H6 H; (*clear;*) intros H6 H.
     (*  all paths cross frontier -> all paths cross frontier' *)
     intros p Hp; specialize (H p Hp).
     elim H; intros.
     (* the things taken out of frontier are not in unexpanded: red H8 or red i *)
     admit.
    } destruct (node_in_dec d' unexpanded). {
      replace d' with u in * by admit.
      specialize (H s' Hs' u). destruct (node_in_dec u unexpanded); [|pv].
      subst. simpl. destruct (node_eq_dec u u); [|pv]. destruct pu; simpl in *.
      admit.
    } {
      eapply H3.
    }
Qed.
