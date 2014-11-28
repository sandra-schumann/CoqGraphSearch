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

Inductive node := Node : nat -> node.

Definition node_eq_dec : forall (x y:node), {x = y} + {x <> y}.
  decide equality. apply eq_nat_dec.
Defined.
Definition node_eq_decb a b := if node_eq_dec a b then true else false.
Lemma node_eq_decb_corr : forall a b, a = b <-> node_eq_decb a b = true. Admitted.
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
Lemma lookup_corr : forall ps, NoDup (keys ps) ->
    forall x y, lookup ps x = Some y <-> In (x, y) ps.
Admitted.

Definition hasEdge (g:graph) u v := exists vs, lookup g u = Some vs /\ In v vs.

Lemma remove_length : forall v vs, In v vs -> length vs = S (length (remove node_eq_dec v vs)).
Admitted.

Fixpoint extractMin (f:found->nat) (frontier : list found) : option (found * list found) :=
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
    (g:graph) (unexpanded:list node) (frontier : list found) (parent : list found)
    {measure length unexpanded}
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
