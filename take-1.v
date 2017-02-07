Require Import Arith.
Open Scope nat_scope.
Require Import Bool.
Open Scope bool_scope.
Require Import List.
Require Import Coq.Setoids.Setoid.

Variable topnode: nat.
(*Graph Definition*)
Definition g:= nat -> nat -> bool.

Inductive has_path (g: nat->nat->bool) : nat->nat->Prop :=
| HP0 x : has_path g x x
| HP1 x y z (Gxy: g x y = true) (HP: has_path g y z ) : has_path g x z.

Definition update {A B C:Type} (eqA: A -> A -> bool) (eqB: B->B->bool) (z: C) g x y (x': A) (y': B):=
if andb (eqA x' x) (eqB y' y) then z else g x' y'.

Definition addedge := update Nat.eqb Nat.eqb true.
Definition deledge := update Nat.eqb Nat.eqb false.

Definition is_in_graph (g: nat -> nat -> bool) (x: nat) : Prop :=
  exists y, g x y || g y x = true.

(* If any of the nodes in the graph 'g' are 256th node, then that will
  be considered as Level 1.
  subsequent levels would be multiples of 256.
  *)
Check Nat.leb.

Fixpoint count_trues (f:nat->bool) (n:nat) : nat :=
  match n with
  | 0 => 0
  | S n => if f n then S (count_trues f n) else count_trues f n
  end.
  
Definition has_out_edge (g':g) (x:nat) :=
  match count_trues (g' x) topnode with O => false | S _ => true end.

Definition has_in_edge (g':g) (y:nat) :=
  match count_trues (fun x => g' x y) topnode with O => false | S _ => true end.

Definition has_edge g x := orb (has_out_edge g x) (has_in_edge g x).

Definition nodes (g':g) := count_trues (has_edge g') topnode.

Definition valid_graph (g':g) : Prop:=
forall x y, topnode <= x -> orb (g' x y) (g' y x) = false.

Definition merge (g1 g2 : g) :=
  fun x y => orb (g1 x y) (g2 x y).

Lemma valid_merge:
  forall g1 g2, valid_graph g1 -> valid_graph g2 -> valid_graph (merge g1 g2).
Proof.
  unfold valid_graph,merge. intros.
  assert (H2:=H0 x y H1).
  apply (H x y) in H1.
  destruct (g1 x y). discriminate.
  destruct (g2 x y). discriminate.
  destruct (g1 y x). discriminate.
  destruct (g2 y x). discriminate.
  reflexivity.
Qed.

(*
  If 2 graphs are valid and their merge does not exist,
  then the two graphs are said to be disjoint graphs.
  In Netsukuku protocol, the disjoint graphs are not entirely
  disjoint, but they share one edge. So according to that
  definition, in here, if g1 has an out edge to x and g2 has an in edge to x,
  then that would mean that they are valid graphs, g1 and g2, and their
  merge is False, also they have one shared edge.
*)
Definition disjoint_graphs (g1 g2: g) (x:nat) :=
forall g1 g2, valid_graph g1 -> valid_graph g2 -> ~(valid_graph (merge g1 g2)) -> has_out_edge g1 x = true -> has_in_edge g2 x = true.

(*
  If two disjoint_graphs have a common edge to x and
  that x is less than the topnode, then we can say that 
  the two graphs are at the same level.
*)
Definition has_same_level (g1 g2: g) (x:nat) :=
forall g1 g2, x < topnode -> disjoint_graphs g1 g2 x.


Definition disjoint_graphs_1 (g1 g2: g) :=
forall x y, andb (g1 x y) (g2 x y) = false.

(*Definition boundry_node (g1 g2:g) (x:nat): bool:=

  if g1 has an out-going edge from say 'x' node, and g2 has in-coming 
  edge from the mentioned node 'x' to some other node 'y' which 
  exists only in g2. 
  This would probably require some different set of implementations for 
  the above definitions.
*)

Definition N:=256.
