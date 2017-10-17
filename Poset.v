Require Import Coq.Sets.Partial_Order.
Require Import Coq.Sets.Cpo.
Require Import Coq.Logic.Classical_Prop.

Section Poset_Properties.

  Variable U : Type.
  Variable P : PO U.

  Eval compute in (Carrier_of U P).

  Definition C := @Carrier_of U P.
  Definition R := @Rel_of U P.
  
  Definition Above (A:Ensemble U) : Ensemble U := fun x:U => In _ C x /\ (forall y:U, In _ A y -> R y x).
  
  Definition Below (A:Ensemble U) : Ensemble U := fun x:U => In _ C x /\ (forall y:U, In _ A y -> R x y).

  Definition Upper_Bounded_Subset (A : Ensemble U) := Inhabited _ (Above A).

  Definition Lower_Bounded_Subset (A : Ensemble U) := Inhabited _ (Below A).


  Ltac crush_generic :=
    repeat match goal with
           | [ H : ?T |- ?T    ] => exact T
           | [ |- ?T = ?T ] => reflexivity
           | [ |- True         ] => constructor
           | [ |- _ /\ _       ] => constructor
           | [ |- _ /\ _ -> _  ] => intro
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- nat -> _     ] => intro
           | [ H : Lower_Bounded_Subset _ |- _ ] => unfold Lower_Bounded_Subset in H
           | [ H : In _ _ |- _ ] => unfold In in H
           | _ =>tauto
           end.

  Ltac crush :=
    repeat (crush_generic; match goal with
                           | [ |- Lower_Bounded_Subset _ ] => unfold Lower_Bounded_Subset
                           | [ |- Upper_Bounded_Subset _ ] => unfold Upper_Bounded_Subset
                           | [ |- ?T -> False  ]  => assert T
                           | _ => try trivial
                           end).

  Lemma Below_In_C : forall  (A : Ensemble U), Included _ A C -> Included _ (Below A) C.
  Proof.
    unfold Included.
    unfold In.
    unfold Below.
    intros.

    crush.
  Qed.
  
  Lemma Bound_Invert : forall  (A : Ensemble U), Included _ A C /\ Inhabited _ A /\ Lower_Bounded_Subset A -> Upper_Bounded_Subset (Below A).
  Proof.
    intros.
    crush.

    inversion H0.
    inversion H1.
    
    apply Inhabited_intro with (x := x).
    unfold In.

    unfold Above.
    unfold Below.
    unfold In.
    split.
    
    unfold In in H2.

    unfold Included in H.
    apply H.
    tauto.
    
    intros.
    unfold In in H2.
    unfold In in H3.
    destruct H4.
    specialize H5 with x.
    tauto.
  Qed.

  (* If every nonempty upper-bounded subset has a least upper bound, then
every nonempty lower-bounded subset has a greatest lower bound. *)
  
  Theorem Th : (forall A : Ensemble U, Included _ A C /\ Inhabited _ A /\ Upper_Bounded_Subset A -> exists lub, Lub _ P A lub) -> (forall B : Ensemble U, Included _ B C /\ Inhabited _ B /\ Lower_Bounded_Subset B -> exists glb, Glb _ P B glb).
  Proof.
    intros.
    specialize H with (Below B).
    pose proof Bound_Invert B H0 as R.

    crush.
    pose proof Below_In_C B H0 as T.
    pose proof H (conj T (conj H2 R)) as S.
    destruct S.
    exists x.

    apply Glb_definition.
    inversion H2.

    inversion H3.
    apply Lower_Bound_definition.
    inversion H5.
    assumption.

    intros.
    specialize H6 with y.
    apply H6.

    apply Upper_Bound_definition.
    unfold Included in H0.
    specialize H0 with y.
    tauto.

    intros.
    unfold Below in H8.
    unfold In in H8.
    crush.
    apply H9.
    tauto.

    intros.
    inversion H3.
    inversion H5.
    specialize H8 with y.
    apply H8.

    unfold Below.
    unfold In.
    inversion H4.
    split.

    assumption.

    assumption.
  Qed.
  