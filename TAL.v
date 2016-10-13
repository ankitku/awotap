(* TAL-0 control flow safety *)

Require Import Bool Arith Vector Maps.

(* 10 registers *)
Definition K := 10.
Definition registers := total_map nat.
Definition empty_regs : registers := t_empty 0.
      
Inductive aexp : Type :=
| ANum : nat -> aexp
| AReg : nat -> aexp
| APlus : aexp -> aexp -> aexp
| ASub : aexp -> aexp -> aexp.

(*define relations for aeval , ieval*)
Fixpoint aeval (a : aexp) (R : registers) : nat :=
  match a with
  | ANum n => n
  | AReg d => R (Id d)
  | APlus a1 a2 => aeval a1 R + aeval a2 R
  | ASub a1 a2 => aeval a1 R - aeval a2 R                
  end.

Inductive instr : Type :=
| IAss : forall d : nat, (d < K) -> aexp -> instr
| IAdd : forall d s : nat, (d < K) -> (s < K) -> instr
| ISub : forall d v : nat, (d < K) -> instr
| IIf : forall d : nat, (d < K) -> aexp -> instr
| ISeq : instr -> instr -> instr
| IJmp : aexp -> instr.

(* Unable to use notations as can't construct proof of d < K on the fly :(

Notation "'R(' d ')' '::=' a" :=
  (IAss d _ (ANum a)) (at level 60).
Notation "'R(' s ')' '+:=' 'R(' d ')'" :=
  (IAdd d s _ _) (at level 60).
Notation "'R(' s ')' '-:=' v" :=
  (ISub s v _ ) (at level 60).
Notation "i1 ;; i2" :=
  (ISeq i1 i2) (at level 80, right associativity).
Notation "'JIF' 'R(' d ')' v" :=
  (IIf d _ (ANum v)) (at level 70).
Notation "'JUMP' v" :=
  (IJmp (ANum v)) (at level 80).

Check JIF R(1) 2.
Check R(1) ::= 10.
Check R(2) +:= R(1).
Check R(2) -:= 1.
Check R(2) +:= R(1) ;; R(2) -:= 1.
Check JUMP 2.
*)

      
Definition heaps := partial_map instr.
Definition empty_heap : heaps := empty.

(* Machine State *)
Inductive st : Type :=
| St : heaps -> registers -> instr -> st.


Inductive ieval : instr -> st -> st -> Prop :=
| R_IAss : forall H R I d a1 pf, ieval (IAss d pf a1) (St H R (ISeq (IAss d pf a1) I)) (St H (t_update R (Id d) (aeval a1 R)) I)
| R_IAdd : forall H R I d s pf1 pf2, ieval (IAdd d s pf1 pf2) (St H R (ISeq (IAdd d s pf1 pf2) I)) (St H (t_update R (Id s) (aeval (AReg d) R + aeval (AReg s) R)) I)
| R_ISub : forall H R I d v pf1, ieval (ISub d v pf1) (St H R (ISeq (ISub d v pf1) I)) (St H (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)) I)
| R_IJmp_Succ : forall H R I' v, H (Id v) = Some I' -> ieval (IJmp (ANum v)) (St H R (IJmp (ANum v))) (St H R I')
| R_IJmp_Fail : forall H R I v, H (Id v) = None -> ieval I (St H R I) (St H R I)
| R_IIf_EQ : forall H R I I' v r pf, aeval (AReg r) R = 0 -> (H (Id (R (Id v)))) = Some I' -> ieval (IIf r pf (AReg v)) (St H R I) (St H R I')
| R_IIf_NEQ : forall H R I v r pf, aeval (AReg r) R <> 0 -> ieval (IIf r pf (AReg v)) (St H R (ISeq (IIf r pf (AReg v)) I)) (St H R I)   
| R_ISeq : forall st st' st'' i1 i2, ieval i1 st st' -> ieval i2 st' st'' -> ieval (ISeq i1 i2) st st''
| R_IStuck : forall st i, ieval i st st
.

Definition threeLEten := (lt_n_S 2 9 (lt_n_S 1 8 (lt_n_S 0 7 (lt_0_Sn 6)))).
Definition twoLEten :=  (lt_n_S 1 9 (lt_n_S 0 8 (lt_0_Sn 7))).
Definition oneLEten :=  (lt_n_S 0 9 (lt_0_Sn 8)).



Definition init_heap := (update (update (update empty_heap (Id 1) (ISeq (IAss 3 threeLEten (ANum 0)) (IJmp (ANum 2)))) (Id 2) (ISeq (IIf 1 oneLEten (ANum 3)) (ISeq (IAdd 2 3 twoLEten threeLEten) (ISeq (ISub 1 1 oneLEten) (IJmp (ANum 2))) ))  )  (Id 3) (IJmp (AReg 4)) ).

Definition init_regs :=  (t_update (t_update empty_regs (Id 1) 1) (Id 2) 2).
Definition final_regs := (t_update (t_update (t_update empty_regs (Id 1) 0) (Id 2) 2) (Id 3) 2).

Eval compute in init_heap (Id 2).

(* find product of numbers stored in R1 and R2, store in R3
*)
Example ieval_jmp_example1 : ieval (ISeq (IAss 3 threeLEten (ANum 0)) (IJmp (ANum 2))) (St init_heap init_regs (ISeq (IAss 3 threeLEten (ANum 0)) (IJmp (ANum 2)))) (St init_heap
                             (t_update init_regs (Id 3) 0)
                             (ISeq (IIf 1 oneLEten (ANum 3))
                                   (ISeq (IAdd 2 3 twoLEten threeLEten)
                                         (ISeq (ISub 1 1 oneLEten) (IJmp (ANum 2)))))).
Proof.
  apply R_ISeq with (St init_heap (t_update init_regs (Id 3) 0) (IJmp (ANum 2))).
  apply R_IAss.
  apply R_IJmp_Succ.
  trivial.
Qed.

