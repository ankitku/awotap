(* TAL-0 control flow safety *)

Require Import Bool Arith Vector Maps.

Definition registers := total_map nat.
Definition empty_regs : registers := t_empty 0.
      
Inductive aexp : Type :=
 | ANum : nat -> aexp
 | AReg : nat -> aexp
 | ALab : nat -> aexp.


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


Notation "'R(' d ')' ':=' a" :=
  (IMov d (ANum a)) (at level 60).
Notation "'R(' s ')' '+:=' 'R(' d ')'" :=
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


Inductive ieval : st -> st -> Prop :=
 | R_IMov : forall H R I d a,
    ieval (St H R (R(d) := a ;; I)) (St H (t_update R (Id d) a) I)
 | R_IAdd : forall H R I d s,
     ieval (St H R (R(d) +:= R(s) ;; I)) (St H (t_update R (Id s) (aeval (AReg d) R + aeval (AReg s) R)) I)
 | R_ISub : forall H R I d v,
     ieval (St H R (R(d) -:= v ;; I)) (St H (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)) I)
 | R_IJmp_Succ : forall H R I' a,
     H (Id (aeval a R)) = Some I' -> ieval (St H R (JMP (aeval a R))) (St H R I')
 | R_IJmp_Fail : forall H R I a,
     H (Id (aeval a R)) = None -> ieval (St H R I) (St H R I)
 | R_IIf_EQ : forall H R I r v,
     aeval (AReg r) R = 0 -> (H (Id v)) = Some I -> ieval (St H R (JIF R(r) v)) (St H R I)
 | R_IIf_NEQ : forall H R I r v,
     aeval (AReg r) R <> 0 -> ieval (St H R (JIF R(r) v ;; I)) (St H R I)   
 | R_ISeq : forall st st' st'',
     ieval st st' -> ieval st' st'' -> ieval st st''
 | R_IStuck : forall st, ieval st st.

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
  reflexivity.
Qed.
     
Inductive ty : Type :=
 | int : ty
 | code : partial_map ty -> ty
 | arrow : partial_map ty -> partial_map ty -> ty
 | True : ty.


Definition context := partial_map ty.

(* register file types *)
Definition empty_Gamma : context := empty.

(* heap types *)
Definition empty_Psi : context := empty.

(* typing rules for arithmetic expressions *)
Inductive ahas_type : context -> context -> aexp -> ty -> Prop :=
 | S_Reg : forall Psi Gamma r tau,
    Gamma (Id r) = Some tau -> ahas_type Psi Gamma (AReg r) tau 
 | S_Int : forall Psi Gamma n,
    ahas_type Psi Gamma (ANum n) int
 | S_Lab : forall Psi Gamma l tau,
    Psi (Id l) = Some tau -> ahas_type Psi Gamma (ALab l) tau.

Hint Constructors ahas_type.

(* typing rules for instructions *)
Inductive ihas_type : context -> context -> instr -> ty -> Prop :=
 | S_Mov : forall Psi Gamma R a tau d,
    ahas_type Psi Gamma a tau -> ahas_type Psi Gamma (AReg d) tau -> (update Gamma (Id d) tau) = Gamma -> ihas_type Psi Gamma (R(d) := aeval a R) (arrow Gamma Gamma)
 | S_Add : forall Psi Gamma s d,
    ahas_type Psi Gamma (AReg s) int -> ahas_type Psi Gamma (AReg d) int -> update Gamma (Id d) int = Gamma -> ihas_type Psi Gamma (R(d) +:= R(s)) (arrow Gamma Gamma)
 | S_Sub : forall Psi Gamma s n,
     ahas_type Psi Gamma (AReg s) int -> ihas_type Psi Gamma (R(s) -:= n) (arrow Gamma Gamma)
 | S_If :  forall Psi Gamma r v,
     ahas_type Psi Gamma (AReg r) int -> ahas_type Psi Gamma (ALab v) (code Gamma) -> ihas_type Psi Gamma (JIF R(r) v) (arrow Gamma Gamma)
 | S_Jmp :  forall Psi Gamma a R v,
     ahas_type Psi Gamma a (code Gamma) -> aeval a R = v -> ihas_type Psi Gamma (JMP v) (code Gamma)
 | S_JmpT :  forall Psi Gamma v r,
     Gamma (Id r) = Some True -> update Gamma (Id r) True = Gamma -> ahas_type Psi Gamma (AReg v) True -> ihas_type Psi Gamma (IJmp (AReg v)) (code Gamma)
 | S_Seq :  forall Psi i1 i2 Gamma Gamma2,
     ihas_type Psi Gamma i1 (arrow Gamma Gamma2) -> ihas_type Psi Gamma i2 (code Gamma2) -> ihas_type Psi Gamma (ISeq i1 i2) (code Gamma).

Hint Constructors ihas_type.


(* typing rules for register file *)
Inductive Rhas_type : context -> registers -> context -> Prop :=
 | S_Regfile : forall Psi Gamma R r tau,
    (Gamma (Id r)) = Some tau -> ahas_type Psi Gamma (AReg r) tau -> Rhas_type Psi R Gamma.

Hint Constructors Rhas_type.

(* typing rules for heap*)
Inductive Hhas_type : heaps -> context -> Prop :=
  | S_Heap : forall Psi Gamma H l tau i, Psi (Id l) = Some tau -> H (Id l) = Some i -> ihas_type Psi Gamma i tau -> Hhas_type H Psi.

Hint Constructors Hhas_type.

(* typing rules for Machine State *)
Inductive M_ok : heaps -> registers -> instr -> Prop :=
 | S_Mach : forall H R I Psi Gamma, Hhas_type H Psi -> Rhas_type Psi R Gamma -> ihas_type Psi Gamma I (code Gamma) -> M_ok H R I.

Hint Constructors M_ok.


Definition init_Gamma : context := update (update (update (update empty_Gamma (Id 1) int) (Id 2) int) (Id 3) int) (Id 4) True.
Check init_Gamma.

Definition init_Psi : context := update (update (update empty_Psi (Id 1) (code init_Gamma))(Id 3) (code init_Gamma)) (Id 2) (code init_Gamma).


Ltac match_map := repeat (try rewrite update_neq; try rewrite update_eq; try reflexivity).
Ltac inequality := (rewrite <- beq_id_false_iff; trivial).
Ltac crush_map := match_map ; inequality.

Lemma heap_2_type : forall I (R : registers), (init_heap (Id 2)) = Some I -> ihas_type init_Psi init_Gamma I (code init_Gamma).
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
  unfold init_Gamma.
  crush_map.
  apply S_Lab.
  unfold init_Psi.
  crush_map.
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
  apply S_Sub.
  apply S_Reg.
  unfold init_Gamma.
  crush_map.
  apply S_Jmp with (a := ALab 2) (R := init_regs).
  apply S_Lab.
  unfold init_Psi.
  apply update_eq.
  crush_map.
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
  apply S_JmpT with (r := 4).
  unfold init_Gamma.
  apply update_eq.
  apply update_same.
  unfold init_Gamma.
  apply update_eq.
  apply S_Reg.
  unfold init_Gamma.
  apply update_eq.
Qed.

Lemma Canonical_Values_Int : forall H Psi Gamma v tau, Hhas_type H Psi -> ahas_type Psi Gamma v tau -> tau = int -> exists n, v = ANum n.
Proof.
  intros.
  inversion H1.
  subst.
  exists r.
  inversion H1.
  exists n; reflexivity.
  exists s; reflexivity.
Qed.

Lemma Canonical_Values_Reg :forall H Psi Gamma r R tau v, Hhas_type H Psi -> Rhas_type Psi R Gamma -> v = AReg r -> ahas_type Psi Gamma v tau -> tau = (reg int) -> exists n, R (Id r) = n.
Proof.
  intros.
  exists (R (Id r)).
  reflexivity.
Qed.

Lemma Canonical_Values_label1 : forall H Psi Gamma r R, Hhas_type H Psi -> ahas_type Psi Gamma (AReg r) (code Gamma) -> exists i, ihas_type Psi Gamma i (code Gamma) -> exists l, l = R (Id r) -> Some i = H (Id l).
Proof.
  intros.
  inversion H0.
  inversion H1.
Qed.

Lemma Canonical_Values_label2 : forall H Psi Gamma v, Hhas_type H Psi -> ahas_type Psi Gamma (ANum v) (code Gamma) -> exists i, ihas_type Psi Gamma i (code Gamma) -> exists l,  Some i = H (Id v) -> v = l.
Proof.
  intros.
  inversion H0.
  inversion H1.

  assumption.
Qed.

Ltac crush_assumptions := repeat (try subst; try assumption).  
  
Theorem Soundness : forall H R I, M_ok H R I -> exists H' R' I', ieval (St H R I) (St H' R' I') /\ M_ok H' R' I'.
Proof.
  intros.
  inversion H0.
  induction I.
  inversion H4.
  inversion H4.
  inversion H4.
  inversion H4.

  induction I1.

  (* ISeq IAss I *)
  inversion H4.
  inversion H12.
  
  symmetry in H16.
  rewrite H16 in H13.
  subst.
  exists H.
  exists (t_update R (Id d) (aeval a R)).
  exists I2.
  split.
  apply R_IAss.
  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  inversion H12.
  apply S_Regfile with (r := d) (tau := tau0).
  assumption.
  rewrite <- H10.
  rewrite update_eq.
  reflexivity.
  assumption.
  assumption.

  
  (* ISeq IAdd I *)
  inversion H4.
  inversion H12.
  symmetry in H16.
  rewrite H16 in H13.
  exists H.
  exists (t_update R (Id s) (aeval (AReg d) R + aeval (AReg s) R)).
  exists I2.
  split.
  apply R_IAdd.
  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  apply S_Regfile with (r := d) (tau := int).
  assumption.
  inversion H20.
  subst.
  assumption.
  crush_assumptions.
  assumption.

  (* ISeq ISub I *)
  inversion H4.
  inversion H12.
  rewrite H18 in H13.
  exists H.
  exists (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)).
  exists I2.
  split.
  apply R_ISub.
  apply S_Mach with (Psi := Psi) (Gamma := Gamma).
  assumption.
  apply S_Regfile with (r := d) (tau := int).
  assumption.
  inversion H19.
  crush_assumptions.
  crush_assumptions.
  crush_assumptions.


  Focus 4.
  (*IJmp*)
  inversion H4.
  exists H.
  exists R.
  pose proof Canonical_Values_label2 H Psi Gamma v H2 H11 as CVL2.
  destruct CVL2 as [I' CVL2'].
  destruct CVL2' as [l CVL'].
  exists I'.
  split.
  apply R_IJmp_Succ.
  symmetry.
  apply CVL'.
  

  
  (* ISeq IIf I *)
  inversion H4.
  inversion H12.
  symmetry in H18.
  rewrite H18 in H13.
  exists H.
  exists R.
  exists I2.
  split.
  subst.
  
  pose proof Canonical_Values_reg H Psi Gamma d R H2 H3 H19 as CVR.
  destruct CVR.
  induction x.
  apply R_IIf_EQ with (v := v) (r := d).
  unfold aeval.
  assumption.
  pose proof Canonical_Values_label2 H Psi Gamma v H2 H20 as CVL2.
  symmetry.
  