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
Definition found := (node * (node*nat))%type.
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

Lemma lookup_corr : forall ps, NoDup (keys ps) ->
    forall x y, lookup ps x = Some y <-> In (x, y) ps.
Proof.
  intros; split; intro H0.
  unfold lookup in *.
  remember (find (fun p : node * list node => node_eq_decb x (fst p)) ps)
  as findps. destruct findps; inversion H0. subst.
  induction ps. discriminate.
  simpl in H. clear H0. SearchAbout (NoDup _).
  remember (NoDup_remove_1 [] _ _ H) as H1. simpl in H1.
  remember (IHps H1) as H2.
  simpl in Heqfindps. remember (node_eq_decb x (fst a)) as xisfsta.
  destruct xisfsta.
  myinj Heqfindps.
  symmetry in Heqxisfsta.
  destruct (node_eq_decb_corr x (fst a)) as [_ H1].
  rewrite (H1 Heqxisfsta) in *.
  simpl. left. destruct a. reflexivity.
  simpl. right. apply H2. auto.
  unfold lookup.
  induction ps. inversion H0.
  simpl in *. destruct H0 as [H1 | H2].
  subst. simpl. unfold node_eq_decb.
  remember (node_eq_dec x x) as xisx. destruct xisx.
  auto. destruct n. reflexivity.
  remember (NoDup_remove_1 [] _ _ H) as H3. simpl in H3.
  unfold node_eq_decb. remember (node_eq_dec x (fst a)) as xisa.
  destruct xisa. subst. SearchAbout (NoDup _).
  remember (NoDup_remove_2 [] _ _ H) as H1. simpl in H1.
  remember (H1 (in_fst_in_keys _ _ _ H2)) as F. inversion F.
  apply IHps. auto. auto.
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

Fixpoint extractMin (f:found->nat) (frontier : list found) :
  option (found * list found) :=
    match frontier with
    | nil => None
    | p::frontier' =>
            match extractMin f frontier' with
            | None => Some (p, nil)
            | Some ret => let (p', remaining') := ret in
                    if le_gt_dec (f p) (f p') 
                         then Some (p, frontier')
                         else Some (p', p::remaining')
            end
    end.

Lemma extractMin_corr : forall f frontier,
    match extractMin f frontier with
    | None => frontier = nil
    | Some ret => forall p, In p frontier -> 
            f p >= f (fst ret) /\ p <> (fst ret) <-> In p (snd ret)
    end.
Admitted.

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
Admitted.

Lemma closestUnexpanded_corr : forall f unexpanded frontier,
    match extractMin f frontier with
    | None => forall p, In p frontier -> ~ In (fst p) unexpanded
    | Some ret => forall p, In p frontier -> 
        if node_in_dec (fst p) unexpanded
        then f p >= f (fst ret) /\ p <> (fst ret) <-> In p (snd ret)
        else ~ In p (snd ret)
    end.
Admitted.

Definition insert {A:Type} (x:A) (xs:list A) := x::xs.

Function bfs
    (g:graph) (unexpanded:list node) (frontier : list found)
    (parent : list found) {measure length unexpanded}
    : list found
    :=
    match closestUnexpanded foundPathLen unexpanded frontier with
    | None => parent
    | Some p => let (found_u, frontierRemaining) := p in
            let u := fst found_u in
            let l := foundPathLen found_u in
            let parent' := found_u::parent in
            let unexpanded' := remove node_eq_dec u unexpanded in
            match lookup g u with
            | None => nil (* invalid graph *)
            | Some neighbors =>
                let frontierNew := map (fun v => (v, (u, 1+l))) neighbors in
                let frontier' := fold_right insert frontierRemaining frontierNew in
                bfs g unexpanded' frontier' parent'
            end
    end.
Admitted.
