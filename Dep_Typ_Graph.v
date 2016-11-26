Require Import List Arith Bool Maps FinFun Basics.


(** *We try to create a simple data structure to store Graphs, using dependent typing *)
Fixpoint f_maker (a b: nat) := fun (x:nat) => if beq_nat x a then b else 0.


(** let us represent edges of graphs using functions ( -> type for -> edges) *)
Definition edge_maker (x y:id) :=
  match x,y with Id x1,Id y1 => 
                 fun (a : id) => match a with Id a1 => Id ((f_maker x1 y1) a1) end
  end.

(** define some sample points *)
Definition V1 := Id 5.
Definition V2 := Id 6.
Definition V3 := Id 7.
Definition V4 := Id 8.

(** sample edges *)
Definition f := edge_maker V1 V2.
Definition g := edge_maker V2 V3.
Definition h := edge_maker V3 V4.

Eval compute in (f (Id 5)).     

Definition nodeList := list id.
Definition edgeList := list (id -> id).

Check compose.
(** similar to function composition, we get edge composition*)
Definition edge_compose (f g : id -> id) := compose g f.

Definition f_inv := edge_maker (Id 6) (Id 5).
Eval compute in  (edge_compose f f_inv) (Id 5).

(** and we can use edge_compose to get to the last connected vertex *)
Eval compute in ((edge_compose (edge_compose f g) h) (Id 5)).     

(** However the above representation was not very useful, let's put more data in types*)

Section phoas_graph.
(** a universal constructor for nodes *)
Inductive u (i : id) : Type := U.

Definition v1 := U (Id 5).
Check v1.

(** need a new definition for checking equality of nodes *)
Definition beq_U  {i j: id} (x : u i) (y : u j) := beq_id i j. 

(** need a new way to create edges *)
Definition edge_maker2 {i j: id} (x : u i) (y : u j) : u i -> u j :=
  fun (a : u i) => U j.

Definition edge_compose2 {i j k : id} (f : u i -> u j) (g : u j -> u k) :=
  compose g f.

Definition f1 := edge_maker2 (U V1) (U V2).
Definition g1 := edge_maker2 (U V2) (U V3).
Definition h1 := edge_maker2 (U V3) (U V4).

Check f1.

Check edge_compose2 (edge_compose2 f1 g1) h1.

(** inductive definition for a list of our new edge types. Note that we couldn't use the regular List as it wouldn't accept elements of different types*)
Inductive edge_list : Type :=
  | ni : edge_list
  | co {i j : id} : (u i -> u j) -> edge_list -> edge_list.

Definition ex_edge_list : edge_list := co f1 (co g1 (co h1 ni)).

(** better to use relations than functions, for pattern matching*)
Definition fromNode {i j : id} (e : u i -> u j) := i.

(** Now we can even write a function to convert list of edges to adjacency map *)
Fixpoint edgeListToAdjMap (el : edge_list) (m : total_map edge_list) : total_map edge_list :=
  match el with
  | ni => m
  | co hd tl => edgeListToAdjMap tl (t_update m (fromNode hd) tl)
  end. 

End phoas_graph.
