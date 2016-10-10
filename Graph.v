Require Import List Arith Bool Maps FinFun.

Module Graph.

Inductive node : Set :=
| Node : nat ->  node.

(*
Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  intros.
  induction n.
  trivial.
  simpl in |- *; auto.
Qed. *given in the library*)

Definition ntk (n : node) : id :=
  match n with
  | Node n => Id n
  end.

Lemma injectivityOfNodeToKeyConverter : Injective ntk.
Proof.
  unfold Injective.
  intros.
  destruct x.
  destruct y.
  inversion H.
  reflexivity.
Qed.

Definition beq_node (a : node) (b : node) : bool := beq_id (ntk a) (ntk b).

Lemma beq_node_refl : forall (a : node), beq_node a a = true.
Proof.
  intros.
  unfold beq_node.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Theorem beq_node_true_iff : forall n1 n2 : node,
  beq_node n1 n2 = true <-> n1 = n2.
Proof.
   intros [n1] [n2].
   unfold beq_node.
   rewrite beq_id_true_iff.
   simpl.
   split.
   - (* -> *) intros H. rewrite injectivityOfNodeToKeyConverter. reflexivity. simpl. exact H.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

Theorem beq_node_false_iff : forall x y : node,
  beq_node x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_node_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_node : forall x y : node,
   x <> y
   -> beq_node x y = false.
Proof.
  intros x y. rewrite beq_node_false_iff.
  intros H. apply H. Qed.

  
Definition wt := nat.

Inductive edge : Set :=
| Edge : node -> node -> wt -> edge.

Definition eq_edge (a : edge) (b : edge) : bool :=
  match a, b with
  | Edge p q w1, Edge r s w2 => andb (beq_node p r) (beq_node q s)                
  end.


Definition edgeList := list edge.
Definition nodeList := list node.



Definition exGraph := (Edge (Node 1) (Node 2) 2) ::  (Edge (Node 2) (Node 3) 3) :: (Edge (Node 1) (Node 4) 1) :: (Edge (Node 4) (Node 3) 2) :: nil.
Check exGraph.

(* Define adjacency map, we go for total map as nil is the preferred choice for default rather than None in case of Partial Map*)
Definition adj_map_empty : total_map nodeList := t_empty nil.

Fixpoint edgeListToAdjMap (el : edgeList) (m : total_map nodeList) : total_map nodeList :=
  match el with
  | nil => m
  | (Edge p q w) :: tl => let pid := (ntk p) in
                           edgeListToAdjMap tl (t_update m pid (q::(m pid)))
end.

Eval compute in (edgeListToAdjMap exGraph adj_map_empty).

(* let's assume 1000 to be the largest weight in any graph *)
Fixpoint getEdgeWeight (el : edgeList) (e : edge) : wt :=
  match el with
  | nil => 1000
  |  hd :: tl => if eq_edge hd e then
                  match hd with
                  | Edge p q w => w
                  end
                else getEdgeWeight tl e
  end.

Definition empty_dist_map : total_map wt := t_empty 1000.

Fixpoint min_dist (dist_map : total_map wt) (minode : node) (q : nodeList) : node :=
  match q with
  | nil => minode
  | hd :: tl => min_dist dist_map (if (dist_map (ntk hd)) <? (dist_map (ntk minode)) then hd else minode) tl
  end.  

Check fold_left.

Fixpoint remove_node (n : node) (nl : nodeList) : nodeList :=
  match nl with
  | nil => nil
  | hd :: tl => if beq_node n hd then tl else hd :: nil ++ remove_node n tl
  end.


Fixpoint dijkstra (start_node end_node : node) (adj : total_map nodeList) (unvisited : nodeList) (visited : nodeList) (dist_map : total_map wt) (el : edgeList) (path : nodeList) : prod nodeList wt :=
  match visited with
  | nil => let udm := (t_update empty_dist_map (ntk start_node) 0) in
                let u_neighbours := adj (ntk start_node) in
                 let alt := fun (i : node) => (dist_map (ntk start_node)) + getEdgeWeight el (Edge start_node i 0) in
                 let updated_dist_map := fold_left (fun (dm : total_map wt) (n : node) => if alt n <? dm (ntk n) then t_update dm (ntk n) (alt n) else dm) u_neighbours udm in
                  dijkstra start_node end_node adj (remove_node start_node unvisited) (start_node::visited) updated_dist_map el (start_node::path)
  | h :: t =>
    
  match unvisited with
  | nil => pair path (dist_map (ntk end_node))
  | hd :: tl => let u := min_dist dist_map hd unvisited in
                let u_neighbours := adj (ntk u) in
                 let alt := fun (i : node) => (dist_map (ntk u)) + getEdgeWeight el (Edge u i 0) in
                 let updated_dist_map := fold_left (fun (dm : total_map wt) (n : node) => if alt n <? dm (ntk n) then t_update dm (ntk n) (alt n) else dm) u_neighbours dist_map in
                  dijkstra start_node end_node adj tl (u::visited) updated_dist_map el (u::path)
  end
  end.


Eval compute in dijkstra (Node 1) (Node 3) (edgeListToAdjMap exGraph adj_map_empty) (Node 1 :: Node 2 :: Node 3 :: Node 4 :: nil) (t_update dist_map (ntk (Node 1)) 0) exGraph nil.


Lemma A : forall (x : node)