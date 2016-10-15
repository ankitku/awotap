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


Inductive ieval : st -> st -> Prop :=
| R_IAss : forall H R I d a1 pf, ieval (St H R (ISeq (IAss d pf a1) I)) (St H (t_update R (Id d) (aeval a1 R)) I)
| R_IAdd : forall H R I d s pf1 pf2, ieval (St H R (ISeq (IAdd d s pf1 pf2) I)) (St H (t_update R (Id s) (aeval (AReg d) R + aeval (AReg s) R)) I)
| R_ISub : forall H R I d v pf1, ieval (St H R (ISeq (ISub d v pf1) I)) (St H (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)) I)
| R_IJmp_Succ : forall H R I v, H (Id v) = Some I -> ieval (St H R (IJmp (ANum v))) (St H R I)
| R_IJmpR_Succ : forall H R I v, H (Id (R (Id v))) = Some I -> ieval (St H R (IJmp (ANum v))) (St H R I)
| R_IJmp_Fail : forall H R I v, H (Id v) = None -> ieval (St H R I) (St H R I)
| R_IIf_EQ : forall H R I I' v r, aeval (AReg r) R = 0 -> (H (Id (R (Id v)))) = Some I' -> ieval (St H R I) (St H R I')
| R_IIf_NEQ : forall H R I v r pf, aeval (AReg r) R <> 0 -> ieval (St H R (ISeq (IIf r pf (AReg v)) I)) (St H R I)   
| R_ISeq : forall st st' st'', ieval st st' -> ieval st' st'' -> ieval st st''
| R_IStuck : forall st, ieval st st
.
(* Proofs (n < K) for registers which are less than K = 10 in number *)
Definition oneLEten :=  (lt_n_S 0 9 (lt_0_Sn 8)).
Definition twoLEten :=  (lt_n_S 1 9 (lt_n_S 0 8 (lt_0_Sn 7))).
Definition threeLEten := (lt_n_S 2 9 (lt_n_S 1 8 (lt_n_S 0 7 (lt_0_Sn 6)))).
Definition fourLEten := (lt_n_S 3 9 (lt_n_S 2 8 (lt_n_S 1 7 (lt_n_S 0 6 (lt_0_Sn 5))))).
Definition fiveLEten := (lt_n_S 4 9 (lt_n_S 3 8 (lt_n_S 2 7 (lt_n_S 1 6 (lt_n_S 0 5 (lt_0_Sn 4)))))).
Definition sixLEten := (lt_n_S 5 9 (lt_n_S 4 8 (lt_n_S 3 7 (lt_n_S 2 6 (lt_n_S 1 5 (lt_n_S 0 4 (lt_0_Sn 3))))))).
Definition sevenLEten :=  (lt_n_S 6 9 (lt_n_S 5 8 (lt_n_S 4 7 (lt_n_S 3 6 (lt_n_S 2 5 (lt_n_S 1 4 (lt_n_S 0 3 (lt_0_Sn 2)))))))).

Definition init_heap := (update (update (update empty_heap (Id 1) (ISeq (IAss 3 threeLEten (ANum 0)) (IJmp (ANum 2)))) (Id 2) (ISeq (IIf 1 oneLEten (ANum 3)) (ISeq (IAdd 2 3 twoLEten threeLEten) (ISeq (ISub 1 1 oneLEten) (IJmp (ANum 2))) ))  )  (Id 3) (IJmp (AReg 4)) ).

Definition init_regs : registers :=  (t_update (t_update  (t_update (t_update (t_update empty_regs (Id 5) 1) (Id 6) 2) (Id 7) 3) (Id 1) 1) (Id 2) 2).
Definition final_regs : registers := (t_update (t_update (t_update  (t_update (t_update (t_update empty_regs (Id 5) 1) (Id 6) 2) (Id 4) 1) (Id 1) 0) (Id 2) 2) (Id 3) 2).

Eval compute in init_heap (Id (init_regs (Id 6))).

(* jump to a label proof *)

Example ieval_example1 : ieval (St init_heap init_regs (ISeq (IAss 3 threeLEten (ANum 0)) (IJmp (ANum 2)))) (St init_heap (t_update init_regs (Id 3) 0)
                          (ISeq (IIf 1 oneLEten (ANum 3))
                          (ISeq (IAdd 2 3 twoLEten threeLEten)
                          (ISeq (ISub 1 1 oneLEten) (IJmp (ANum 2)))))).
Proof.
  apply R_ISeq with (St init_heap (t_update init_regs (Id 3) 0) (IJmp (ANum 2))).
  apply R_IAss.
  apply R_IJmp_Succ.
  unfold init_heap.
  rewrite update_neq.
  rewrite update_eq.
  reflexivity.
  unfold t_update.
  rewrite <- beq_id_false_iff.
  simpl.
  trivial.
Qed.

Inductive var : Type :=
| alpha : var
| beta : var
| gam : var.
          
Inductive ty : Type :=
| int : ty
| code : partial_map ty -> ty
| arrow : partial_map ty -> partial_map ty -> ty                           
| tyvar : var -> ty
| poly : var -> ty -> ty.

Definition context := partial_map ty.

(* register file types *)
Definition empty_Gamma : context := empty.

(* heap types *)
Definition empty_Psi : context := empty.

(* typing rules for arithmetic expressions *)
Inductive ahas_type : context -> context -> aexp -> ty -> Prop :=
| S_Reg : forall Psi Gamma (r : nat) tau, r < K -> Gamma (Id r) = Some tau -> ahas_type Psi Gamma (AReg r) tau 
| S_Int : forall Psi Gamma (n : nat), ahas_type Psi Gamma (ANum n) int
| S_Lab : forall Psi Gamma (s : nat) tau, Psi (Id s) = Some tau -> ahas_type Psi Gamma (ANum s) tau.
    
  
Hint Constructors ahas_type.

(* typing rules for instructions *)
(* Jmp to Num v is for labels in heap.*)
Inductive ihas_type : context -> context -> instr -> ty -> Prop :=
| S_Mov : forall Psi Gamma v tau d pf, ahas_type Psi Gamma v tau -> ihas_type Psi (update Gamma (Id d) tau) (IAss d pf v) tau
| S_Add : forall Psi Gamma s d pf1 pf2, ahas_type Psi Gamma (AReg s) int -> ahas_type Psi Gamma (AReg d) int -> ihas_type Psi Gamma (IAdd d s pf1 pf2) (arrow Gamma Gamma)
| S_Sub : forall Psi Gamma s n pf, ahas_type Psi Gamma (AReg s) int -> ahas_type Psi Gamma (ANum n) int -> ihas_type Psi Gamma (ISub s n pf) (arrow Gamma Gamma)
| S_If :  forall Psi Gamma s v pf1, ahas_type Psi Gamma (AReg s) int -> ahas_type Psi Gamma (ANum v) (code Gamma) -> ihas_type Psi Gamma (IIf s pf1 (ANum v)) (arrow Gamma Gamma)
| S_Jmp :  forall Psi Gamma v,  ahas_type Psi Gamma (ANum v) (code Gamma) -> ihas_type Psi Gamma (IJmp (ANum v)) (code Gamma)
| S_JmpR :  forall Psi Gamma v,  ahas_type Psi Gamma (AReg v) (code Gamma) -> ihas_type Psi Gamma (IJmp (AReg v)) (code Gamma)
| S_Seq :  forall Psi i1 i2 Gamma Gamma2,  ihas_type Psi Gamma i1 (arrow Gamma Gamma2) -> ihas_type Psi Gamma i2 (code Gamma2) -> ihas_type Psi Gamma (ISeq i1 i2) (code Gamma).

Hint Constructors ihas_type.

(* typing rules for register file *)
Inductive Rhas_type : context -> registers -> context -> Prop :=
| S_Regfile : forall r Psi Gamma (R : registers) tau, r < K ->  (Gamma (Id r)) = Some tau -> ahas_type Psi Gamma (AReg r) tau -> Rhas_type Psi R Gamma.

Hint Constructors Rhas_type.

(* typing rules for heap*)
Inductive Hhas_type : heaps -> context -> Prop :=
  | S_Heap : forall Psi Gamma (H : heaps) l tau i, Psi (Id l) = Some tau -> H (Id l) = Some i -> ihas_type Psi Gamma i tau -> Hhas_type H Psi.

Hint Constructors Hhas_type.

(* typing rules for Machine State*)
Inductive M_ok : heaps -> registers -> instr -> Prop :=
| S_Mach : forall H R I Psi Gamma , Hhas_type H Psi -> Rhas_type Psi R Gamma -> ihas_type Psi Gamma I (code Gamma) -> M_ok H R I.

Hint Constructors M_ok.


Definition init_Gamma : context := update (update (update (update empty_Gamma (Id 1) int) (Id 2) int) (Id 3) int) (Id 4) (code ( update (update (update (update empty_Gamma (Id 1) int) (Id 2) int) (Id 3) int) (Id 4)  (tyvar alpha) ) ).
Check init_Gamma.

Definition init_Psi : context := update (update (update empty_Psi (Id 1) (code init_Gamma))(Id 3) (code init_Gamma)) (Id 2) (code init_Gamma).

Eval compute in   (init_heap (Id 2)).

Lemma heap_2_type : forall I, (init_heap (Id 2)) = Some I -> ihas_type init_Psi init_Gamma I (code init_Gamma).
Proof.
  intros.
  unfold init_heap in H.
  rewrite update_neq in H.
  rewrite update_eq in H.
  symmetry in H.
  inversion H.  
  apply S_Seq with (Gamma2 := init_Gamma).
  apply S_If.
  apply S_Reg.
  apply oneLEten.
  unfold init_Gamma.
  rewrite update_neq.
  rewrite update_neq.
  rewrite update_neq.
  rewrite update_eq.
  
  reflexivity.
  rewrite <- beq_id_false_iff.
  trivial.
  rewrite <- beq_id_false_iff.
  trivial.
  rewrite <- beq_id_false_iff.
  trivial.
  apply S_Lab.
  unfold init_Psi.
  rewrite update_neq.
  rewrite update_eq.
  reflexivity.
  rewrite <- beq_id_false_iff.
  trivial.
  
  apply S_Seq with (Gamma2 :=  init_Gamma).
  apply S_Add with (Gamma := init_Gamma).
  apply S_Reg.
  apply threeLEten.
  unfold init_Gamma.
  rewrite update_neq.
  rewrite update_eq.
  reflexivity.
  rewrite <- beq_id_false_iff.
  trivial.  
  apply S_Reg.
  apply twoLEten.
  unfold init_Gamma.
  rewrite update_neq.
  rewrite update_neq.
  rewrite update_eq.
  reflexivity.
  rewrite <- beq_id_false_iff.
  trivial.
  rewrite <- beq_id_false_iff.
  trivial.
  apply S_Seq with (Gamma2 := init_Gamma).
  apply S_Sub.
  apply S_Reg.
  apply oneLEten.
  unfold init_Gamma.
  rewrite update_neq.
  rewrite update_neq.
  rewrite update_neq.
  rewrite update_eq.  
  reflexivity.
  repeat (try rewrite <- beq_id_false_iff; trivial).
  repeat (try rewrite <- beq_id_false_iff; trivial).
  repeat (try rewrite <- beq_id_false_iff; trivial).
  apply S_Int.
  apply S_Jmp.
  apply S_Lab.
  unfold init_Psi.
  apply update_eq.
  rewrite <- beq_id_false_iff.
  trivial.  
Qed.

Lemma heap_1_type : forall I, (init_heap (Id 3)) = Some I -> ihas_type init_Psi init_Gamma I (code init_Gamma).
Proof.
  intros.
  unfold init_heap in H.
  rewrite update_eq in H.
  symmetry in H.
  inversion H.
  apply S_JmpR.
  apply S_Reg.
  apply fourLEten.
  unfold init_Gamma.
  rewrite update_eq.
  rewrite S_Inst.