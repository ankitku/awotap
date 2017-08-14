Check 0.
Check nat.
Check Set.
Check Type.
Check forall T : Set, T.
Check forall T : Type, T.

Definition id (T : Type) (x : T) : T := x.

Set Printing Universes.

Inductive exp : Type -> Type :=
| Const : forall T, T -> exp T
| Pair : forall T1 T2, exp T1 -> exp T2 -> exp (T1 * T2)
| Eq : forall T, exp T -> exp T -> exp bool.

Print exp.

Check (nat, (Type, Set)).

Inductive prod' : Type -> Type -> Type :=
| pair' : forall A B : Type, A -> B -> prod' A B.

Inductive foo (A : Type) : Type :=
  | Foo : A -> foo A.

Check foo nat.
Check foo Set.
Check foo Type.
Check foo True.

Inductive bar : Type := Bar : bar.

Check Bar.
Check bar.

Print sig.
Print ex.


Definition projS A (P : A -> Prop) (x : sig P) : A :=
  match x with
    | exist _ v _ => v
  end.


Definition churchnat := forall X : Prop, (X -> X) -> X -> X.

Definition two : churchnat :=
  fun (X : Prop) (f : X -> X) (x : X) => f (f x).
Definition three : churchnat :=
  fun (X : Prop) (f : X -> X) (x : X) => f (f (f x)).

Definition succ (n : churchnat) : churchnat :=
   fun (X : Prop) (f : X -> X) (x : X) => f (n X f x).
 
 
Example succ_2 : succ two = three.
Proof.
  reflexivity.
Qed.

Definition plus (n m : churchnat) : churchnat := n _ succ m.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.


Definition projE A (P : A -> Prop) (x : ex P) : A :=
  match x with
    | ex_intro _ v _ => v
  end.
