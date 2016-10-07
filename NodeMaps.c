(** Total  Map *)

Require Import Arith Bool Graph List FunctionalExtensionality.

Definition adj_map := Node -> nodeList.

Definition adj_empty : Node -> nodeList :=
  (fun _ => nil).

Definition adj_update (m : adj_map)
                    (v : Node) (nl : nodeList) :=
  fun v' => if beq_node v v' then nl else m v'.

(** empty map returns default value*)
Lemma adj_apply_empty: forall v, adj_empty v = nil.
Proof.
  intros.
  trivial.
Qed.

(** set and get the same value for same keys*)
Lemma adj_update_eq : forall (m: adj_map) n nl,
  (adj_update m n nl) n = nl.
Proof.
  intros.
  unfold adj_update.
  destruct n.
  rewrite beq_node_refl.
  reflexivity.
Qed.

Theorem adj_update_neq : forall  nl n1 n2
                         (m : adj_map),
  n1 <> n2 ->
  (adj_update m n1 nl) n2 = m n2.
Proof.
  intros nl [n1] [n2] m H.
  unfold adj_update.
  rewrite -> false_beq_node.
  trivial.
  apply H.
Qed.

(** latest update stays *)
Lemma adj_update_shadow : forall (m: adj_map) nl1 nl2 n,
    adj_update (adj_update m n nl1) n nl2
  = adj_update m n nl2.
Proof.
  intros m nl1 nl2 n.
  unfold adj_update.
  extensionality x.
  remember (beq_node n x) as e; induction e.
  trivial.
  trivial.
Qed.

Print reflect.
Lemma beq_nodeP : forall x y, reflect (x = y) (beq_node x y).
Proof.
  intros.
  apply iff_reflect.
  rewrite beq_node_true_iff.
  reflexivity.
Qed.

(** if we update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)

Theorem t_update_same : forall n (m : adj_map),
  adj_update m n (m n) = m.
Proof.
  intros.
  unfold adj_update.
  extensionality x.
  remember (beq_node n x) as e; induction e.
  symmetry in Heqe.
  apply beq_node_true_iff in Heqe.
  rewrite Heqe.
  reflexivity.
  reflexivity.
Qed.

(** [] *)

(** If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)
Theorem t_update_permute : forall nl1 nl2 n1 n2
                             (m : adj_map),
  n2 <> n1 ->
    (adj_update (adj_update m n2 nl2) n1 nl1)
  = (adj_update (adj_update m n1 nl1) n2 nl2).
Proof.
  intros.
  unfold adj_update.
  extensionality x.
  remember (beq_node n1 x) as e; induction e.
  symmetry in Heqe.
  apply beq_node_true_iff in Heqe.
  rewrite <- Heqe.
  rewrite -> false_beq_node.
  reflexivity.
  exact H.
  reflexivity.
Qed.