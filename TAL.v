(* TAL-0 control flow safety *)

Require Import Bool Arith Vector Maps.

(* 10 registers *)
Definition K := 10.
Definition registers := total_map nat.
      
Inductive aexp : Type :=
| ANum : nat -> aexp
| AReg : nat -> aexp
| APlus : aexp -> aexp -> aexp
| ASub : aexp -> aexp -> aexp.

Inductive instr : Type :=
| IAss : forall d : nat, (d < K) -> aexp -> instr
| IAdd : forall d s : nat, (d < K) -> (s < K) -> instr
| ISub : forall d s : nat, (d < K) -> (s < K) -> instr
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
  | ASub a1 a2 => aeval a1 R - aeval a2 R                
  end.

Inductive ieval : instr -> st -> st -> Prop :=
| R_IAss : forall H R I d a1 pf, ieval (IAss d pf a1) (St H R (ISeq (IAss d pf a1) I)) (St H (t_update R (Id d) (aeval a1 R)) I)
| R_IAdd : forall H R I d s pf1 pf2, ieval (IAdd d s pf1 pf2) (St H R (ISeq (IAdd d s pf1 pf2) I)) (St H (t_update R (Id s) (aeval (AReg d) R + aeval (AReg s) R)) I)
| R_ISub : forall H R I d s pf1 pf2, ieval (ISub d s pf1 pf2) (St H R (ISeq (ISub d s pf1 pf2) I)) (St H (t_update R (Id s) (aeval (AReg d) R - aeval (ANum s) R)) I)
| R_IJmp_Succ : forall H R I I' v, H (Id (R (Id v))) = Some I' -> ieval (IJmp (AReg v)) (St H R I) (St H R I')
| R_IJmp_Fail : forall H R I v, H (Id (R (Id v))) = None -> ieval I (St H R I) (St H R I)
| R_IIf_EQ : forall H R I I' v r pf, aeval (AReg r) R = 0 -> (H (Id (R (Id v)))) = Some I' -> ieval (IIf r pf (AReg v)) (St H R I) (St H R I')
| R_IIf_NEQ : forall H R I v r pf, aeval (AReg r) R <> 0 -> ieval (IIf r pf (AReg v)) (St H R (ISeq (IIf r pf (AReg v)) I)) (St H R I)   
| R_ISeq : forall st st' st'' i1 i2, ieval i1 st st' -> ieval i2 st' st'' -> ieval (ISeq i1 i2) st st''
| R_IStuck : forall st i, ieval i st st
.

Definition empty_heap : heaps := empty.

Definition empty_regs : registers := t_empty 0.

Definition threeLEten := (lt_n_S 2 9 (lt_n_S 1 8 (lt_n_S 0 7 (lt_0_Sn 6)))).
Definition twoLEten :=  (lt_n_S 1 9 (lt_n_S 0 8 (lt_0_Sn 7))).
Definition oneLEten :=  (lt_n_S 0 9 (lt_0_Sn 8)).



Definition init_heap := (update (update (update empty_heap (Id 1) (ISeq (IAss 3 threeLEten (ANum 0)) (IJmp (ANum 2)))) (Id 2) (ISeq (IIf 1 oneLEten (ANum 3)) (ISeq (IAdd 2 3 twoLEten threeLEten) (ISeq (ISub 1 1 oneLEten oneLEten) (IJmp (ANum 2))) ))  )  (Id 3) (IJmp (AReg 4)) ).

Print init_heap.

Example ieval_example1 : ieval (IAss 3 threeLEten (ANum 0)) (St init_heap empty_regs I) .
