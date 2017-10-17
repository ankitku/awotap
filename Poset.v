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
           | [ H : Upper_Bounded_Subset _ |- _ ] => unfold Upper_Bounded_Subset in H
           | [ H : In _ _ _ |- _ ] => unfold In in H
           | [ H : Included _ _ _ |- _ ] => unfold Included in H
           | _ => tauto
           end.

  Ltac unfold_all := try unfold Included;
                     try unfold Above;
                     try unfold Below;
                     try unfold In;
                     try unfold Lower_Bounded_Subset;
                     try unfold Upper_Bounded_Subset.
  
  Ltac crush :=
    repeat (crush_generic;
            unfold_all;
            match goal with
            | [ |- ?T -> False  ]  => assert T
            | _ => try trivial
            end).

  Lemma Below_In_Carrier : forall  (A : Ensemble U), Included _ A C -> Included _ (Below A) C.
  Proof.
    crush.
  Qed.

  Lemma Above_In_Carrier : forall  (A : Ensemble U), Included _ A C -> Included _ (Above A) C.
  Proof.
    crush.
  Qed.

  (** Lower Bound (Set) of a nonempty subset is Upper Bounded *)
  Lemma Bound_Invert : forall  (A : Ensemble U), Included _ A C /\ Inhabited _ A /\ Lower_Bounded_Subset A -> Upper_Bounded_Subset (Below A).
  Proof.
    crush.
    intros.

    crush. inversion H0. inversion H1.
    
    apply Inhabited_intro with (x := x).
    crush. apply H. tauto.
    
    intros. crush.
    specialize H6 with x. tauto.
  Qed.

  (** If every nonempty upper-bounded subset has a least upper bound, then
every nonempty lower-bounded subset has a greatest lower bound. *)
  Theorem Th : (forall A : Ensemble U, Included _ A C /\ Inhabited _ A /\ Upper_Bounded_Subset A -> exists lub, Lub _ P A lub) -> (forall B : Ensemble U, Included _ B C /\ Inhabited _ B /\ Lower_Bounded_Subset B -> exists glb, Glb _ P B glb).
  Proof.
    intros.
    specialize H with (Below B).
    pose proof Bound_Invert B H0 as R.

    crush.
    pose proof Below_In_Carrier B H0 as T.
    pose proof H (conj T (conj H2 R)) as S.
    destruct S.
    exists x.

    apply Glb_definition.

    inversion H3. apply Lower_Bound_definition.
    inversion H4. assumption.

    intros. specialize H5 with y. apply H5.
    apply Upper_Bound_definition.
    specialize H0 with y. tauto.

    intros. crush. unfold Below in H7.
    apply H7. tauto.

    intros. inversion H3. inversion H5.
    specialize H8 with y. apply H8.

    crush; inversion H4; assumption.
  Qed.
  