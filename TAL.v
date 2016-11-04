(** * TAL-0 Typed Assembly Language *)

(** Based on paper by Greg Morrisett , TAL-0 is the design of a RISC-style typed assembly language which focuses on control-flow safety. This post provides a mechanized metatheory, particularly a machine checked proof of soundness of the TAL-0 type system as proposed by the author in section 4.2.10 of the book Advanced Topics in Types and Programming Languages.  *)

(** The TAL-0 language runs on an abstract machine which is represented by 3 components :

1. A heap H which is a finite, partial map from labels to heap values

2. a register file R which is a total map from registers to values, and 

3. a current instruction sequence I.  

Diagram : *)

Require Import Bool Arith Vector.
Require Import LibTactics.
Require Import Maps.

Definition registers := total_map nat.
Definition empty_regs : registers := t_empty 0.
      
Inductive aexp : Type :=
 | ANum : nat -> aexp
 | AReg : nat -> aexp
 | ALab : nat -> aexp.

(** We denote addresses of instructions stored in the heap as labels. Unlike a typical machine where labels are resolved to some machine address, which are integers, we maintain a distinction between labels and arbit integers, as this complies with our goal to state and prove the control-flow safety i.e. we can only branch to a valid label, and not to any arbit integer. This will ensure that the machine never gets stuck while trying to do some invalid operation. *)
(*define relations for aeval , ieval*)
Fixpoint aeval (a : aexp) (R : registers) : nat :=
  match a with
 | ANum n => n
 | AReg d => R (Id d)
 | ALab l => l
  end.


Inductive instr : Type :=
 | IMov : forall d : nat,
    aexp -> instr
 | IAdd : forall d s : nat,
    instr
 | ISub : forall d v : nat,
    instr
 | IIf : forall d : nat,
    aexp -> instr
 | ISeq : instr -> instr -> instr
 | IJmp : aexp -> instr.

(** Simple Notations are chosen for the sake of clarity while writing programs.*)
Notation "'R(' d ')' ':=' a" :=
  (IMov d (ANum a)) (at level 60).
Notation "'R(' d ')' '+:=' 'R(' s ')'" :=
  (IAdd d s) (at level 60).
Notation "'R(' s ')' '-:=' v" :=
  (ISub s v) (at level 60).
Notation "i1 ;; i2" :=
  (ISeq i1 i2) (at level 80, right associativity).
Notation "'JIF' 'R(' d ')' v" :=
  (IIf d (ANum v)) (at level 70).
Notation "'JMP' v" :=
  (IJmp (ALab v)) (at level 80).
Notation "'JMP' 'R(' r ')'" :=
  (IJmp (AReg r)) (at level 80).

Check JIF R(1) 2.
Check R(1) := 10.
Check R(2) +:= R(1).
Check R(2) -:= 1.
Check R(2) +:= R(1) ;; R(2) -:= 1.
Check JMP 2.
Check JMP R(2).

      
Definition heaps := partial_map instr.
Definition empty_heap : heaps := empty.

(* Machine State *)
Inductive st : Type :=
 | St : heaps -> registers -> instr -> st.

(** Evaluation of instructions is supposed to change the Machine State and thus some of its components H, R or I. These changes are recorded as relations between initial and final state of the machine. *)
Inductive ieval : st -> st -> Prop :=
 | R_IMov : forall H R I d a,
    ieval (St H R (R(d) := a ;; I)) (St H (t_update R (Id d) a) I)
 | R_IAdd : forall H R I d s,
     ieval (St H R (R(d) +:= R(s) ;; I)) (St H (t_update R (Id d) (aeval (AReg d) R + aeval (AReg s) R)) I)
 | R_ISub : forall H R I d v,
     ieval (St H R (R(d) -:= v ;; I)) (St H (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)) I)
 | R_IJmp_Succ : forall H R I' a l,
     l = (aeval a R) -> H (Id l) = Some I' -> ieval (St H R (JMP l)) (St H R I')
 | R_IJmpR_Succ : forall H R I' r,
     H (Id (R (Id r))) = Some I' -> ieval (St H R (JMP R(r))) (St H R I')
 | R_IJmp_Fail : forall H R I a,
     H (Id (aeval a R)) = None -> ieval (St H R I) (St H R I)
 | R_IIf_EQ : forall H R I I2 r v,
     aeval (AReg r) R = 0 -> (H (Id v)) = Some I2 -> ieval (St H R (JIF R(r) v ;; I)) (St H R I2)
 | R_IIf_NEQ : forall H R I r v,
     aeval (AReg r) R <> 0 -> ieval (St H R (JIF R(r) v ;; I)) (St H R I)   
 | R_ISeq : forall st st' st'',
     ieval st st' -> ieval st' st'' -> ieval st st''
 | R_IStuck : forall st, ieval st st.

(** Example of a program fragment that multiplies 2 numbers stored in registers 1 and 2 and stores their product in register 3, before finally looping in its final state register 4. *)
Definition init_heap := update (update (update empty_heap (Id 1) (R(3) := 0 ;; JMP 2)) (Id 2) (JIF R(1) 3 ;; R(2) +:= R(3) ;; R(1) -:= 1 ;; JMP 2) ) (Id 3) (JMP R(4)).


Definition init_regs : registers :=  (t_update (t_update  (t_update (t_update (t_update empty_regs (Id 5) 1) (Id 6) 2) (Id 7) 3) (Id 1) 1) (Id 2) 2).
Definition final_regs : registers := (t_update (t_update (t_update  (t_update (t_update (t_update empty_regs (Id 5) 1) (Id 6) 2) (Id 4) 1) (Id 1) 0) (Id 2) 2) (Id 3) 2).

Eval compute in init_heap (Id (init_regs (Id 6))).

(* jump to a label proof *)

Example ieval_example1 : ieval (St init_heap init_regs
                          (R(3) := 0 ;; JMP 2))
                               (St init_heap (t_update init_regs (Id 3) 0)
                          (JIF R(1) 3 ;; R(2) +:= R(3) ;; R(1) -:= 1 ;; JMP 2)).
Proof.
  apply R_ISeq with (St init_heap (t_update init_regs (Id 3) 0) (IJmp (ALab 2))).
  apply R_IMov.
  apply R_IJmp_Succ with (a := ALab 2).
  simpl.
  reflexivity.
  unfold init_heap.
  rewrite update_neq.
  rewrite update_eq.
  reflexivity.
  rewrite <- beq_id_false_iff; trivial.
Qed.


(** The types consist of
1. int -> represents arbit integer stored in a register

2. reg -> a type constructor. Takes as input, the type of the register, to which this register is pointing.

3. code -> takes as input a typing context Gamma, and gives type (code Gamma) which is the type of an instruction sequence that expects type of the Register file to be Gamma before it begins execution 

4. arrow -> represents type of a single instruction (excluding JMP), which expects register file of type Gamma1 before execution, and changes it to Gamma2 after it has executed.

5. T -> It is the super type. It is used to represent the type of a register in R, which contains the label of the instruction currently executing. Because in such a case, we have the equation : Gamma (r) = code Gamma, which in the absence of subtyping or polymorphic types can't be solved. Hence T is assigned the type for such a register as it subsumes all types including itself. When we jump through a register of type T, we forget the type assigned to it, and reassign T to it.

 *)

Inductive ty : Type :=
 | int : ty
 | reg : ty -> ty
 | code : partial_map ty -> ty
 | arrow : partial_map ty -> partial_map ty -> ty
 | True : ty.


Definition context := partial_map ty.

(* register file types *)
Definition empty_Gamma : context := empty.

(* heap types *)
Definition empty_Psi : context := empty.

(** The Typing Rules *)
(** Psi is a partial map containing types of instruction sequences. As all instruction sequences end in a JMP statement, all valid values in Psi are Some (code Gamma) where Gamma is the initial type state of register expected by that instruction sequence. Now, typing rules may require presence of either both Psi and Gamma, or only Psi or neither. Hence, we introduce a combined context structure, that handles all the 3 cases. *)
Inductive cmbnd_ctx :=
 | EmptyCtx : cmbnd_ctx
 | PsiCtx : context -> cmbnd_ctx
 | PsiGammaCtx : context -> context -> cmbnd_ctx.

(** Typing rules for arithmetic expressions *)
Inductive ahas_type : cmbnd_ctx -> aexp -> ty -> Prop :=
 | S_Int : forall Psi n,
     ahas_type (PsiCtx Psi) (ANum n) int
 | S_Lab : forall Psi Gamma l v R,
     Psi (Id l) = Some (code Gamma) -> l = aeval (ALab v) R -> ahas_type (PsiCtx Psi) (ALab v) (code Gamma)
 | S_Reg : forall Psi Gamma r,
     Gamma (Id r) = Some (reg int) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg int)
 | S_RegV : forall Psi Gamma r,
     (forall R, Psi (Id (R (Id r))) = Some (code Gamma)) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg (code Gamma))
 | S_RegT : forall Psi Gamma r,
     (forall R, Psi (Id (R (Id r))) = Some True) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) True
 | S_Val : forall Psi Gamma a tau,
     ahas_type (PsiCtx Psi) a tau -> ahas_type (PsiGammaCtx Psi Gamma) a tau.

Hint Constructors ahas_type.

(** Typing rules for instructions *)
Inductive ihas_type : cmbnd_ctx -> instr -> ty -> Prop :=
 | S_Jmp :  forall Psi Gamma v,
     ahas_type (PsiGammaCtx Psi Gamma) (ALab v) (code Gamma) -> ihas_type (PsiCtx Psi) (JMP v) (code Gamma)
 | S_JmpT :  forall Psi Gamma v,
     ahas_type (PsiGammaCtx Psi Gamma) (AReg v) True -> ihas_type (PsiCtx Psi) (JMP R(v)) (code Gamma)
 | S_Mov : forall Psi Gamma R d a tau,
    ahas_type (PsiGammaCtx Psi Gamma) a tau -> ahas_type (PsiGammaCtx Psi Gamma) (AReg d) (reg tau) -> (update Gamma (Id d) (reg tau)) = Gamma -> ihas_type (PsiCtx Psi) (R(d) := aeval a R) (arrow Gamma Gamma)
 | S_Add : forall Psi Gamma d s,
    ahas_type (PsiGammaCtx Psi Gamma) (AReg s) (reg int) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg d) (reg int) -> update Gamma (Id d) (reg int) = Gamma -> ihas_type (PsiCtx Psi) (R(d) +:= R(s)) (arrow Gamma Gamma)
 | S_Sub : forall Psi Gamma s a v,
      ahas_type (PsiGammaCtx Psi Gamma) a int -> ahas_type (PsiGammaCtx Psi Gamma) (AReg s) (reg int) -> a = ANum v -> ihas_type (PsiCtx Psi) (R(s) -:= v) (arrow Gamma Gamma)
 | S_If :  forall Psi Gamma r v,
     ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg int) -> ahas_type (PsiGammaCtx Psi Gamma) (ALab v) (code Gamma) -> ihas_type (PsiCtx Psi) (JIF R(r) v) (arrow Gamma Gamma)
 | S_Seq :  forall Psi i1 i2 Gamma Gamma2,
     ihas_type (PsiCtx Psi) i1 (arrow Gamma Gamma2) -> ihas_type (PsiCtx Psi) i2 (code Gamma2) -> ihas_type (PsiCtx Psi) (ISeq i1 i2) (code Gamma).

Hint Constructors ihas_type.


(** Typing rules for register file *)
Inductive Rhas_type : cmbnd_ctx -> registers -> context -> Prop :=
 | S_Regfile : forall Psi Gamma R r tau a, (Gamma (Id r)) = Some tau -> aeval a R = R (Id r) -> ahas_type (PsiGammaCtx Psi Gamma) a tau -> Rhas_type (PsiCtx Psi) R Gamma.

Hint Constructors Rhas_type.



Definition init_Gamma : context := update (update (update (update empty_Gamma (Id 1) (reg int)) (Id 2) (reg int)) (Id 3) (reg int)) (Id 4) True.
Check init_Gamma.

Definition init_Psi : context := update (update (update empty_Psi (Id 1) (code init_Gamma))(Id 3) (code init_Gamma)) (Id 2) (code init_Gamma).


Ltac match_map := repeat (try rewrite update_neq; try rewrite update_eq; try reflexivity).
Ltac inequality := (rewrite <- beq_id_false_iff; trivial).
Ltac crush_map := match_map ; inequality; try reflexivity.



Ltac crush_assumptions := repeat (try subst; try assumption).


Example heap_2_type : forall I (R : registers), (init_heap (Id 2)) = Some I -> ihas_type (PsiCtx init_Psi) I (code init_Gamma).
Proof.
  intros.
  unfold init_heap in H.
  rewrite update_neq in H.
  rewrite update_eq in H.
  symmetry in H.
  inverts H.
  apply S_Seq with (Gamma2 := init_Gamma).
  apply S_If.
  apply S_Reg.
  unfold init_Gamma.
  crush_map.
  apply S_Val.
  apply S_Lab with (l := 3) (R := R).
  unfold init_Psi.
  crush_map.
  trivial.
  apply S_Seq with (Gamma2 := init_Gamma).
  apply S_Add.
  apply S_Reg.
  unfold init_Gamma.
  crush_map.
  apply S_Reg.
  unfold init_Gamma.
  crush_map.
  apply update_same.
  unfold init_Gamma.
  crush_map.
  apply S_Seq with (Gamma2 := init_Gamma).
  unfold init_Psi.
  apply S_Sub with (a := ANum 1).
  unfold init_Psi.
  apply S_Val.
  apply S_Int.
  apply S_Reg.
  unfold init_Gamma.
  crush_map.
  reflexivity.
  apply S_Jmp.
  apply S_Val.
  apply S_Lab with (l := 2) (R := R).
  unfold init_Psi.
  trivial.
  trivial.
  rewrite <- beq_id_false_iff.
  trivial.
Qed.
                   


(** Typing rule for Heap *)
Inductive Hhas_type : cmbnd_ctx -> heaps -> context -> Prop :=
  | S_Heap : forall Psi H, (forall l tau, exists i, Psi (Id l) = Some tau /\ H (Id l) = Some i /\ ihas_type (PsiCtx Psi) i tau) -> Hhas_type EmptyCtx H Psi.

Hint Constructors Hhas_type.

(** Typing rule for a valid Machine State *)
Inductive M_ok : cmbnd_ctx -> heaps -> registers -> instr -> Prop :=
 | S_Mach : forall H R I Psi Gamma, Hhas_type EmptyCtx H Psi -> Rhas_type (PsiCtx Psi) R Gamma -> ihas_type (PsiCtx Psi) I (code Gamma) -> M_ok EmptyCtx H R I.

Hint Constructors M_ok.

(** We will require some Canonical Values Lemmas in our proof of Soundness *)
Lemma Canonical_Values_Int : forall H Psi Gamma v tau, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) v tau -> tau = int -> exists n, v = ANum n.
Proof.
  intros.
  subst.
  inverts H1.
  inverts H6.
  exists n.
  reflexivity.
Qed.


Lemma Canonical_Values_Reg :forall H Psi Gamma r R, Hhas_type EmptyCtx H Psi -> Rhas_type (PsiCtx Psi) R Gamma -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg int) -> exists (n : nat), R (Id r) = n.
Proof.
  intros.
  exists (R (Id r)).
  reflexivity.
Qed.

Lemma Canonical_Values_label1 : forall H Psi Gamma v, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) (ALab v) (code Gamma) ->  Psi (Id v) = Some (code Gamma) -> exists i, H (Id v) = Some i /\ ihas_type (PsiCtx Psi) i (code Gamma).
Proof.
  intros.
  inverts H0.
  inverts H1.
  inverts H7.
  simpl in H5.
  specialize H4 with ( l := v) (tau := code Gamma).
  destruct H4 as [i G].
  exists i.
  apply G.
Qed.

Lemma Canonical_Values_label3 : forall H Psi Gamma R r, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) True ->  Psi (Id (R (Id r))) = Some True -> exists i, H (Id (R (Id r))) = Some i /\ ihas_type (PsiCtx Psi) i (code Gamma).
Proof.
  intros.
  inversion H0.
  inversion H1.
  specialize H4 with ( l := R (Id r)) (tau := (code Gamma)).
  destruct H4 as [i G].
  exists i.
  apply G.
  specialize H4 with ( l := R (Id r)) (tau := (code Gamma)).
  destruct H4 as [i G].
  exists i.
  apply G.
 Qed.

(** Finally the proof of Soundness *)
Theorem Soundness : forall H R I, M_ok EmptyCtx H R I -> exists H' R' I', ieval (St H R I) (St H' R' I') /\ M_ok EmptyCtx H' R' I'.
Proof.
  intros.
  inversion H0.
  induction I.
  inversion H4...
  inversion H4...
  inversion H4...
  inversion H4...

  induction I1.

  (* ISeq IMov I *)
  inversion H4.
  inversion H12.
  
  symmetry in H18.
  rewrite H18 in H13.
  exists H.
  exists (t_update R (Id d) (aeval a0 R1)).
  exists I2.
  split.
  apply R_IMov.
  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  apply S_Regfile with (r := d) (tau := reg tau) (a := AReg d).
  
  rewrite H18 in H21.
  rewrite <- H21.
  intros.

  rewrite update_eq.
  reflexivity.
  crush_assumptions.
  trivial.
  crush_assumptions.
  crush_assumptions...

  
  (* ISeq IAdd I *)
  inversion H4.
  inversion H12.
  symmetry in H18.
  rewrite H18 in H13.
  exists H.
  exists (t_update R (Id d) (aeval (AReg d) R + aeval (AReg s) R)).
  exists I2.
  split.
  apply R_IAdd.
  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  apply S_Regfile with (a := AReg d) (r := d) (tau := reg int).
  subst.
  rewrite <- H21.
  apply update_eq.
  crush_assumptions.
  inversion H20.
  trivial.
  trivial.
  crush_assumptions.
  crush_assumptions...

  (* ISeq ISub I *)
  inversion H4.
  inversion H12.
  symmetry in H18.
  rewrite H18 in H13.
  exists H.
  exists (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)).
  exists I2.
  split.
  apply R_ISub.
  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  apply S_Regfile with (a := AReg d) (r := d) (tau := reg int).
  inversion H20.
  rewrite H18 in H23.
  crush_assumptions.
  inversion H26.
  trivial.
  
  crush_assumptions.
  crush_assumptions...
  
  (* ISeq IIf I *)
  inversion H4.
  inversion H12.
  symmetry in H19.
  rewrite H19 in H13.
  subst.
  inversion H20.
  inversion H8.
  subst.
  simpl in H14.
  remember (R (Id d)) as rd; destruct rd.
  pose proof Canonical_Values_label1 H Psi Gamma v H2 H20 H14 as CVL1.
  destruct CVL1 as [I' G].
  exists H.
  exists R.
  exists I'.
  split.
  apply R_IIf_EQ.
  simpl.
  symmetry in Heqrd; assumption.
  apply G.
  
  apply S_Mach with (Psi := Psi) (Gamma := Gamma). 
  assumption.
  assumption.
  apply G.

  exists H.
  exists R.
  exists I2.
  split.
  apply R_IIf_NEQ.
  simpl.
  symmetry in Heqrd; rewrite Heqrd.
  apply beq_nat_false_iff.
  trivial.
  apply S_Mach with (Psi := Psi) (Gamma := Gamma). 
  assumption.
  assumption.
  assumption...
  
  (*(I1_1;;I1_2);;I2*)
  inversion H4.
  inversion H12...

  (*IJmp a;; I2*)
  inversion H4.
  inversion H12...

  (*IJmp*)
  inversion H4.
  inversion H11.
  inversion H16.
  simpl in H21.
  subst.

  pose proof Canonical_Values_label1 H Psi Gamma v H2 H11 H20 as CVL1.
  destruct CVL1 as [i G].

  exists H.
  exists R.
  exists i.

  split.
  
  apply R_IJmp_Succ with (a := ALab v).
  simpl.
  reflexivity.
  apply G.

  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  assumption.

  apply G...

  

  (*IJmpT*)
  inversion H11.
  specialize H13 with (R := R).

  pose proof Canonical_Values_label3 H Psi Gamma R v H2 H11 H13 as CVL3.
  destruct CVL3 as [i G].

  exists H.
  exists R.
  exists i.

  split.
  
  apply R_IJmpR_Succ.
  apply G.

  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  assumption.
  apply G.

  (*S_Val applied to S_JmpT, impossible case.*)
  inversion H16...
Qed.  