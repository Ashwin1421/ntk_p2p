Require Import Arith.
Require Import Bool.
Require Import NAxioms NSub NZDiv.

(* group size *)
Variable gs : nat.

(* max_lvl = number of levels - 1 (so nl=0 means one level).  The "highest" level
   (i.e., the one numbered max_lvl) consists of a single group comprising the entire graph.
   The "lowest" level (numbered 0) conceptually consists of gs^max_lvl groups, all of size 1. *)
Variable max_lvl : nat.

(* Graphs are assumed to have gs^max_lvl nodes numbered from 0 to gs^max_lvl - 1.
   We represent them as boolean functions on pairs of nodes. *)
Definition node := nat.
Definition graph:= node -> node -> bool.
 
 
(* has_path g n x y:  Graph g has a path of length n from node x to node y. *)
Inductive has_path (g:graph) : nat -> node -> node -> Prop :=
| HP_Self (x:node): has_path g O x x
| HP_Step (n:nat) (x y z:node) (ST: g x y = true) (HP: has_path g n y z): has_path g (S n) x z.

(* number of level-v groups *)
Definition num_groups v := gs^(max_lvl-v).

(* level-v group number containing node x *)
Definition group_of v x := x/(gs^v).

(* Decide whether two groups are in the same super-group (one level up). *)
Definition same_supergroup p1 p2 := p1/gs = p2/gs.

(* Strongly connected Netsukuku property: For every level v, and every pair of groups p1
   and p2 at level v contained within the same supergroup (at level v+1), there exists a
   path (having some length n) from a node x within p1 to a node y within p2. *)
Definition is_netsukuku_strong (g:graph) : Prop :=
  forall v p1 p2, v <= max_lvl -> p1 < num_groups v -> p2 < num_groups v ->
                  same_supergroup p1 p2 ->
    exists n x y, group_of v x = p1 /\ group_of v y = p2 /\ has_path g n x y.

(* Fully connected Netsukuku property: For every level v, and every pair of groups p1
   and p2 at level v contained within the same supergroup (at level v+1), there exists a
   direct link from a node x within p1 to a node y within p2. *)
Definition is_netsukuku_full (g:graph) : Prop :=
  forall v p1 p2, v <= max_lvl -> p1 < num_groups v -> p2 < num_groups v ->
                  same_supergroup p1 p2 ->
    exists x y, group_of v x = p1 /\ group_of v y = p2 /\ g x y = true.

Definition mygraph (x y:nat):bool:=
(Nat.eqb y (x+1) || Nat.eqb y (x-1)).

Lemma xyz:
  forall x n, has_path mygraph n x (x+n) -> has_path mygraph n (x+n) x.
Proof.
  induction n.
  intros.
  SearchAbout plus.
  rewrite <- plus_n_O in H.
  rewrite <- plus_n_O.
  assumption.
  intros.
  inversion H. subst.
  apply IHn with (n:=S n).
Admitted.
(* If all we know is that a graph obeys the strongly connected Netsukuku property, then
   there might exist nodes x and y such that the shortest path between them has length
   gs^max_lvl - 1. *)
Theorem strong_worst_case:
  exists g x y, is_netsukuku_strong g /\ x < gs^max_lvl /\ y < gs^max_lvl /\
    forall n, has_path g n x y -> n >= gs^max_lvl - 1.
Proof.
  exists mygraph.
  exists (gs-1).
  exists (gs-2).
  split.
    unfold is_netsukuku_strong.
    intros.
    exists (p2-p1).
    exists (p1).
    exists (p2).
    split.
    induction v.
    unfold group_of. simpl.
    
    inversion H0. destruct H0.
    inversion H1. destruct H1.
    inversion H2. destruct H2.
    
Admitted.



(* But if we know a graph obeys the fully connected Netsukuku property, then the worst
   path length is always less than 2^max_lvl. *)
Theorem full_worst_case:
  forall g x y, is_netsukuku_full g -> x < gs^max_lvl -> y < gs^max_lvl ->
      exists n, n < 2^max_lvl /\ has_path g n x y.
Proof.
  intros.
  exists O.
  split.
    induction max_lvl.
    simpl.
    apply Nat.lt_0_1.
    SearchPattern (_<_).
    admit.
Admitted.
