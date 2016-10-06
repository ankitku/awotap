Require Import List Arith Bool.

Inductive Node : Set :=
| node : nat ->  Node.

Definition beq_node (a : Node) (b : Node) : bool :=
  match a,b with
  | node x, node y => beq_nat x y
  end.

(*
Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  intros.
  induction n.
  trivial.
  simpl in |- *; auto.
Qed. *given in the library*)

Lemma beq_node_refl : forall (n : nat), beq_node (node n) (node n) = true.
Proof.
  intros.
  unfold beq_node.
  symmetry.
  apply beq_nat_refl.
Qed.

Theorem beq_node_true_iff : forall n1 n2 : Node,
  beq_node n1 n2 = true <-> n1 = n2.
Proof.
   intros [n1] [n2].
   unfold beq_node.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

Theorem beq_node_false_iff : forall x y : Node,
  beq_node x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_node_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_node : forall x y : Node,
   x <> y
   -> beq_node x y = false.
Proof.
  intros x y. rewrite beq_node_false_iff.
  intros H. apply H. Qed.

  
Definition wt := nat.

Inductive Edge : Set :=
| edge : Node -> Node -> wt -> Edge.

Definition eq_edge (a : Edge) (b : Edge) : bool :=
  match a, b with
  | edge p q w1, edge r s w2 => andb (beq_nat w1 w2) (andb (beq_node p r) (beq_node q s))                                     
  end.


Definition edgeList := list Edge.
Definition nodeList := list Node.



Definition exGraph :=  (edge (node 1) (node 2) 2) ::  (edge (node 2) (node 3) 3) :: nil.
Check exGraph.





