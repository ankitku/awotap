(* TAL-0 control flow safety *)

Require Import Bool Arith Vector Maps.

(* 10 registers *)
Definition K := 10.
Definition registers := total_map nat.

(*
Check lt_0_Sn.
Check lt_n_Sn.
Check lt_n_S 1 7 (lt_n_S 0 6 (lt_0_Sn 5)).

Fixpoint prf_of_lt_n_m (n m : nat) : (n < m) :=
  match n , m with
  | S n', S m' => lt_n_S n' m' (prf_of_lt_n_m n' m')
  | 0 , S m' => lt_0_Sn m'
  | _,_ => 
  end.
*)
      
Inductive aexp : Type :=
| ANum : nat -> aexp
| AReg : nat -> aexp
| APlus : aexp -> aexp -> aexp.

Inductive instr : Type :=
| IAss : forall d : nat, (d < K) -> aexp -> instr
| IAdd : forall d s : nat, (d < K) /\ (s < K) -> instr
| IIf : forall d : nat, (d < K) -> aexp -> instr
| ISeq : instr -> instr -> instr
| IJmp : aexp -> instr.               

Definition heaps := partial_map instr.

(* Machine State *)
Inductive st : Type :=
| St : heaps -> registers -> instr -> st.

(*define relations for aeval , ieval*)
Fixpoint aeval (a : aexp) (R : registers) : nat :=
  match a with
  | ANum n => n
  | AReg d => R (Id d)
  | APlus a1 a2 => aeval a1 R + aeval a2 R                
  end.

Inductive ieval : instr -> st -> st -> Prop :=
| R_IAss : forall H R I d a1 pf, ieval (IAss d pf a1) (St H R I) (St H (t_update R (Id d) (aeval a1 R)) I)
|  R_IAdd : forall H R I d s pf, ieval (IAdd d s pf) (St H R I) (St H (t_update R (Id s) (aeval (AReg d) R + aeval (AReg s) R)) I)
.