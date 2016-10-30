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

Inductive cmbnd_ctx :=
 | EmptyCtx : cmbnd_ctx
 | PsiCtx : context -> cmbnd_ctx
 | PsiGammaCtx : context -> context -> cmbnd_ctx.

(* typing rules for arithmetic expressions *)
Inductive ahas_type : cmbnd_ctx -> aexp -> ty -> Prop :=
 | S_Reg : forall Psi Gamma r,
     Gamma (Id r) = Some (reg int) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg int)
 | S_RegT : forall Psi Gamma r,
     Gamma (Id r) = Some True -> (forall R, Psi (Id (R (Id r))) = Some (code Gamma)) -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) True
 | S_Int : forall Psi n,
     ahas_type (PsiCtx Psi) (ANum n) int
 | S_Lab1 : forall Psi Gamma l v R,
     Psi (Id l) = Some (code Gamma) -> l = aeval (ALab v) R -> ahas_type (PsiCtx Psi) (ALab v) (code Gamma)
 | S_Lab2 : forall Psi Gamma1 Gamma2 l v R,
     Psi (Id l) = Some (arrow Gamma1 Gamma2) -> l = aeval (ALab v) R -> ahas_type (PsiCtx Psi) (ALab v) (arrow Gamma1 Gamma2)
 | S_Val : forall Psi Gamma a tau,
     ahas_type (PsiCtx Psi) a tau -> ahas_type (PsiGammaCtx Psi Gamma) a tau.

Hint Constructors ahas_type.

(* typing rules for instructions *)
Inductive ihas_type : cmbnd_ctx -> instr -> ty -> Prop :=
 | S_Jmp :  forall Psi Gamma v,
     ahas_type (PsiGammaCtx Psi Gamma) (ALab v) (code Gamma) -> ihas_type (PsiCtx Psi) (JMP v) (code Gamma)
 | S_JmpR :  forall Psi Gamma v (R : registers),
     ahas_type (PsiGammaCtx Psi Gamma) (AReg v) ( reg (code Gamma)) -> ihas_type (PsiCtx Psi) (JMP R(v)) (code Gamma)
 | S_JmpT :  forall Psi Gamma v r (R : registers),
     Gamma (Id r) = Some True -> update Gamma (Id r) True = Gamma -> ahas_type (PsiGammaCtx Psi Gamma) (AReg v) True -> ihas_type (PsiCtx Psi) (JMP R(v)) (code Gamma) 
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


(* typing rules for register file *)
Inductive Rhas_type : cmbnd_ctx -> registers -> context -> Prop :=
 | S_Regfile : forall Psi Gamma R r tau,
    (Gamma (Id r)) = Some tau -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) tau -> Rhas_type (PsiCtx Psi) R Gamma.

Hint Constructors Rhas_type.



(*
Definition init_Gamma : context := update (update (update (update empty_Gamma (Id 1) (reg int)) (Id 2) (reg int)) (Id 3) (reg int)) (Id 4) True.
Check init_Gamma.

Definition init_Psi : context := update (update (update empty_Psi (Id 1) (code init_Gamma))(Id 3) (code init_Gamma)) (Id 2) (code init_Gamma).


Ltac match_map := repeat (try rewrite update_neq; try rewrite update_eq; try reflexivity).
Ltac inequality := (rewrite <- beq_id_false_iff; trivial).
Ltac crush_map := match_map ; inequality; try reflexivity.

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
  apply S_Lab1 with (l := 3) (R := R).
  exact I.
  reflexivity.
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
  apply S_Int.
  apply S_Reg.
  unfold init_Gamma.
  crush_map.
  reflexivity.
  apply S_Jmp.
  apply S_Lab1 with (l := 2) (R := R).
  exact I.
  reflexivity.
  unfold init_Psi.
  trivial.
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
  apply S_RegT.
  unfold init_Gamma.
  apply update_eq.
Qed.
*)

(* typing rules for heap*)
Inductive Hhas_type : cmbnd_ctx -> heaps -> context -> Prop :=
  | S_Heap : forall Psi H, (forall Gamma l, exists i, Psi (Id l) = Some (code Gamma) /\ H (Id l) = Some i /\ ihas_type (PsiCtx Psi) i (code Gamma)) -> Hhas_type EmptyCtx H Psi.

Hint Constructors Hhas_type.

(* typing rules for Machine State *)
Inductive M_ok : cmbnd_ctx -> heaps -> registers -> instr -> Prop :=
 | S_Mach : forall H R I Psi Gamma, Hhas_type EmptyCtx H Psi -> Rhas_type (PsiCtx Psi) R Gamma -> ihas_type (PsiCtx Psi) I (code Gamma) -> M_ok EmptyCtx H R I.

Hint Constructors M_ok.

Lemma Canonical_Values_Int : forall H Psi Gamma v tau, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) v tau -> tau = int -> exists n, v = ANum n.
Proof.
  intros.
  subst.
  inversion H1.
  inversion H6.
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
  inversion H0.
  inversion H1.
  inversion H11.
  simpl in H16.
  subst.
  specialize H4 with (Gamma := Gamma) ( l := v).
  destruct H4 as [i G].
  exists i.
  apply G.
Qed.

Lemma Canonical_Values_label2 : forall H Psi Gamma R r, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) (reg (code Gamma)) ->  Psi (Id (R (Id r))) = Some (code Gamma) -> exists i, H (Id (R (Id r))) = Some i /\ ihas_type (PsiCtx Psi) i (code Gamma).
Proof.
  intros.
  inversion H0.
  inversion H1.
  specialize H4 with (Gamma := Gamma) ( l := R (Id r)).
  destruct H4 as [i G].
  exists i.
  apply G.
Qed.

Lemma Canonical_Values_label3 : forall H Psi Gamma R r, Hhas_type EmptyCtx H Psi -> ahas_type (PsiGammaCtx Psi Gamma) (AReg r) True ->  Psi (Id (R (Id r))) = Some (code Gamma) -> exists i, H (Id (R (Id r))) = Some i /\ ihas_type (PsiCtx Psi) i (code Gamma).
Proof.
  intros.
  inversion H0.
  inversion H1.
  specialize H4 with (Gamma := Gamma) ( l := R (Id r)).
  destruct H4 as [i G].
  exists i.
  apply G.
  specialize H4 with (Gamma := Gamma) ( l := R (Id r)).
  destruct H4 as [i G].
  exists i.
  apply G.
 Qed.

Ltac crush_assumptions := repeat (try subst; try assumption).  
  
Theorem Soundness : forall H R I, M_ok EmptyCtx H R I -> exists H' R' I', ieval (St H R I) (St H' R' I') /\ M_ok EmptyCtx H' R' I'.
Proof.
  intros.
  inversion H0.
  induction I.
  inversion H4.
  inversion H4.
  inversion H4.
  inversion H4.

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
  apply S_Regfile with (r := d) (tau := reg tau).
  rewrite H18 in H21.
  rewrite <- H21.
  rewrite update_eq.
  reflexivity.
  crush_assumptions.
  crush_assumptions.

  
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
  apply S_Regfile with (r := d) (tau := reg int).
  subst.
  rewrite <- H21.
  apply update_eq.
  crush_assumptions.
  inversion H20.
  crush_assumptions.
  crush_assumptions.

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
  apply S_Regfile with (r := d) (tau := reg int).
  inversion H20.
  rewrite H18 in H23.
  crush_assumptions.
  inversion H26.
  crush_assumptions.
  crush_assumptions.

  Focus 4.
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

  apply G.

  (*IJmpR*)

  inversion H11.
  inversion H16.
  inversion H13.
  specialize (H18 R).
  pose proof Canonical_Values_label3 H Psi Gamma R v H2 H13 H18 as CVL3.
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

  inversion H18. (*impossible case*)

  
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
  assumption.

  (*(I1_1;;I1_2);;I2*)
  inversion H4.
  inversion H12.

  (*IJmp a;; I2*)
  inversion H4.
  inversion H12.
Qed.  