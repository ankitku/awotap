Require Import Coq.Sets.Partial_Order.
Require Import Coq.Sets.Cpo.
Require Import Coq.Logic.Classical_Prop.

Section Poset_Properties.

  Variable U : Type.
  Variable P : PO U.

  Eval compute in (Carrier_of U P).

  Definition C := @Carrier_of U P.
  Definition R := @Rel_of U P.
  
  Definition Above (A:Ensemble U) : Ensemble U := fun x:U =>  (~ In _ A x) /\ (forall y:U, In _ A y -> R y x).

  Definition Below (A:Ensemble U) : Ensemble U := fun x:U =>  (~ In _ A x) /\ (forall y:U, In _ A y -> R x y).

  Definition Upper_Bounded_Subset (A : Ensemble U) := Inhabited _ (Above A).

  Definition Lower_Bounded_Subset (A : Ensemble U) := Inhabited _ (Below A).

  (* If every nonempty upper-bounded subset has a least upper bound, then
every nonempty lower-bounded subset has a greatest lower bound. *)

  Lemma Bound_Invert : forall  (A : Ensemble U), Inhabited _ A /\ Lower_Bounded_Subset A -> Upper_Bounded_Subset (Below A).
  Proof.
    intros.
    unfold Lower_Bounded_Subset in H.
    destruct H.
    inversion H.
    unfold In in H1.
    unfold Upper_Bounded_Subset.
    apply Inhabited_intro with (x := x).
    unfold Above.
    unfold Below.
    unfold In.
    split.
    
    apply or_not_and.
    tauto.
    intros.
    destruct H2.
    specialize H3 with x.
    pose proof H3 H1 as R.
    assumption.
  Qed.
  
  Lemma rev : forall A : Ensemble U, Inhabited U A -> Inhabited U (Below A) ->  Upper_Bounded_Subset (Below A).
  Proof.
    intros.
    unfold Upper_Bounded_Subset.

    Theorem Th : (forall A : Ensemble U, Inhabited _ A -> Upper_Bounded_Subset A -> exists lub, Lub _ P A lub) -> (forall B : Ensemble U, Inhabited _ B -> Lower_Bounded_Subset B -> exists glb, Glb _ P B glb).
    Proof.
      intros.
      specialize H with (Below B).
      pose proof Bound_Invert B (conj H0 H1) as R.

      unfold  Lower_Bounded_Subset in H1.
      pose proof H H1 R as S.
      destruct S.
      exists x.

      apply Glb_definition.

      inversion H2.

      inversion H3.
      apply Lower_Bound_definition.
      assumption.

      intros.
      specialize H4 with y.
      apply H4.

      apply Upper_Bound_definition.
      
      
      pose proof H4 H3 as T.