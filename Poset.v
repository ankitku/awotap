Require Import Coq.Sets.Partial_Order.

Section Poset_Properties.

  Variable U : Type.
  Variable P : PO U.

  Eval compute in (Carrier_of U P).

  Definition S := @Carrier_of U P.
  Definition R := @Rel_of U P.

  Definition Lower_bound (U:Type) (P': PO U) (y:U): Prop :=
    let C0:= Carrier_of _ P' in
    let R0:= Rel_of _ P' in
    (forall x:U, (In _ C0 x -> R0 x y) ).

  Definition Upper_bound (U:Type) (P': PO U) (y:U): Prop :=
    let C0:= Carrier_of _ P' in
    let R0:= Rel_of _ P' in
    (forall x:U, (In _ C0 x -> R0 y x) ).

  Definition Is_the_largest_element_in (U:Type) (P': PO U) (y:U): Prop :=
    let C0:= Carrier_of _ P' in
    let R0:= Rel_of _ P' in
    ( In _ C0 y /\ forall x:U, (In _ C0 x -> R0 y x) ).
  
  Definition Is_the_smallest_element_in (U:Type) (P': PO U) (y:U): Prop :=
    let C0:= Carrier_of _ P' in
    let R0:= Rel_of _ P' in
    ( In _ C0 y /\ forall x:U, (In _ C0 y -> R0 x y) ).

  Definition Inside (P1: PO U) (P2: PO U) : Prop :=
    Strict_Included _ (Carrier_of _ P1) (Carrier_of _ P2) /\
    Rel_of U P1 = Rel_of U P2.
  (*Notation "P1 '⊏' P2" := Inside P1 P2.*)

  Definition Included_in (P1: PO U) (P2: PO U) : Prop :=
    Included _ (Carrier_of _ P1) (Carrier_of _ P2) /\
    Rel_of U P1 = Rel_of U P2 .
  (* Notation "P1 ⊑ P2" := Included_in P1 P2.*)

  Definition Non_empty (P' : PO U) : Prop :=
    let C0 := Carrier_of _ P' in
    Inhabited _ C0.

  (*Upper Bounded Subset*)
  Definition UBSubset (P' : PO U) (UB : PO U) : Prop :=
    let C0 := Carrier_of _ UB in
    Included_in P' P /\
    Included_in UB P /\
    Non_empty UB /\
    (forall x : U, In _ C0 x -> Upper_bound _ P' x).

  (*Lower Bounded Subset*)
  Definition LBSubset (P' : PO U) (LB : PO U) : Prop :=
    let C0 := Carrier_of _ LB in
    Included_in P' P /\
    Included_in LB P /\
    Non_empty LB /\
    (forall x : U, In _ C0 x -> Lower_bound _ P' x). 

  (*LUB*)
  Definition LUB (P1 : PO U) (lub : U) : Prop :=
    forall UB : PO U, UBSubset P1 UB -> Is_the_smallest_element_in _ UB lub.

  (*GLB*)
  Definition GLB (P2 : PO U) (glb : U) : Prop :=
    forall LB : PO U, LBSubset P2 LB -> Is_the_largest_element_in _ LB glb.


  Ltac crush_generic :=
    repeat match goal with
           | [ H : ?T |- ?T    ] => exact T
           | [ |- ?T = ?T ] => reflexivity
           | [ |- True         ] => constructor
           | [ |- _ /\ _       ] => constructor
           | [ |- _ /\ _ -> _  ] => intro
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- nat -> _     ] => intro
           | _ => eauto
           end.

  Ltac unfold_all := repeat match goal with                 
                            | [ H : Included _ _ _ |- _ ] => unfold Included in H
                            | [ H : Included_in _ _ |- _ ] => unfold Included_in in H
                            | [ H : LBSubset _ _ |- _ ] => unfold LBSubset in H
                            | [ H : UBSubset _ _ |- _ ] => unfold UBSubset in H
                            end.
  
  Ltac crush :=
    repeat (crush_generic; unfold_all; match goal with
                                       | [ |- ?T -> False  ]  => assert T
                                       | _ => try subst; trivial
                                       end).

  Lemma Reversal1 : forall P1 P2, Non_empty P1 -> Non_empty P2 -> UBSubset P1 P2 -> LBSubset P2 P1.
  Proof.
    intros.
    inversion H; inversion H0; inversion H1.
    unfold LBSubset.
    crush.
    intros.
    specialize H10 with x1.
    unfold Lower_bound.
    intros.
    specialize H12 with x2.
    rewrite H8.
    specialize H7 with x2.
    unfold Upper_bound in H7.
    rewrite H9 in H7.
    specialize H7 with x1.
    apply H7.
    assumption.
    assumption.
  Qed.

    Lemma Reversal2 : forall P1 P2, Non_empty P1 -> Non_empty P2 -> LBSubset P1 P2 -> UBSubset P2 P1.
  Proof.
    intros.
    inversion H; inversion H0; inversion H1.
    unfold UBSubset.
    crush.
    intros.
    specialize H10 with x1.
    unfold Upper_bound.
    intros.
    specialize H12 with x2.
    rewrite H8.
    specialize H7 with x2.
    unfold Lower_bound in H7.
    rewrite H9 in H7.
    specialize H7 with x1.
    apply H7.
    assumption.
    assumption.
  Qed.
  
  (* If every nonempty upper-bounded subset has a least upper bound, then
every nonempty lower-bounded subset has a greatest lower bound. *)

  Theorem Th : (forall P' UB : PO U, Non_empty P' -> UBSubset P' UB -> exists lub, LUB P' lub) -> (forall P' LB : PO U, Non_empty P' -> LBSubset P' LB -> exists glb, GLB P' glb).
  Proof.
    intros.
    specialize H with LB P'.
    inversion H1.
    destruct H3; destruct H4.
    pose proof Reversal2 P' LB H0 H4 as R.
    pose proof R H1 as B.
    pose proof H H4 B as E.
    destruct E.
    
    unfold GLB.
    exists x.
    intros.

    unfold LUB in H6.
    specialize H6 with P'.
            pose proof H6 B as C.
    unfold Is_the_largest_element_in.
    split.
    unfold Is_the_smallest_element_in in C.
    destruct C.
    specialize H9 with x.
    