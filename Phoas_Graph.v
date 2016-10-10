Require Import List Arith Bool Maps FinFun Basics.

Fixpoint f_maker (a b: nat) := fun (x:nat) => if beq_nat x a then b else 0.

Definition edge_maker (x y:id) :=
  match x,y with Id x1,Id y1 => 
                 fun (a : id) => match a with Id a1 => Id ((f_maker x1 y1) a1) end
  end.

Definition V1 := Id 5.
Definition V2 := Id 6.
Definition V3 := Id 7.
Definition V4 := Id 8.
                    
Definition f := edge_maker V1 V2.
Definition g := edge_maker V2 V3.
Definition h := edge_maker V3 V4.

Eval compute in (f (Id 5)).     

Definition nodeList := list id.
Definition edgeList := list (id -> id).

Check compose.

Definition edge_compose (f g : id -> id) := compose g f.

Definition f_inv := edge_maker (Id 6) (Id 5).
Eval compute in  (edge_compose f f_inv) (Id 5).

Eval compute in ((edge_compose (edge_compose f g) h) (Id 5)).     

(*-------------------------------- not very useful, let's put more data in types*)

Section phoas_graph.
(* a universal constructor for nodes *)
Inductive u (i : id) : Type :=
  | U : u i.

Definition v1 := U (Id 5).
Check v1.

Definition beq_U  {i j: id} (x : u i) (y : u j) := beq_id i j. 

Definition edge_maker2 {i j: id} (x : u i) (y : u j) : u i -> u j :=
  fun (a : u i) => U j.

Definition edge_compose2 {i j k : id} (f : u i -> u j) (g : u j -> u k) :=
  compose g f.

Definition f1 := edge_maker2 (U V1) (U V2).
Definition g1 := edge_maker2 (U V2) (U V3).
Definition h1 := edge_maker2 (U V3) (U V4).

Check f1.

Check edge_compose2 (edge_compose2 f1 g1) h1.

Definition nodeList2 := list (forall i:id, u i).
Definition edgeList2 := list (forall i j:id, u i -> u j).


(*better to use relations than functions, for pattern matching*)

(*
Fixpoint edgeListToAdjMap (el : edgeList2) (m : total_map edgeList2) : total_map edgeList2 :=
  match el with
  | nil => m
  | hd :: tl => edgeListToAdjMap tl (t_update m i hd)
  end.

*)
                
  

end phoas_graph
