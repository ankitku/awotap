(* The set of the group. *)
Parameter G : Set.

(* The binary operator. *)
Parameter f : G -> G -> G.

(* The group identity. *)
Parameter e : G.

(* The inverse operator. *)
Parameter i : G -> G.

(* For readability, we use infix <+> to stand for the binary operator. *)
Infix "<+>" := f (at level 50, left associativity).

(* The operator [f] is associative. *)
Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c).

(* [e] is the right-identity for all elements [a] *)
Axiom id_r : forall a, a <+> e = a.

(* [i a] is the right-inverse of [a]. *)
Axiom inv_r : forall a, a <+> i a = e.


Lemma mult_both : 
  forall a b c d1 d2, 
    a <+> c = d1
    -> b <+> c = d2
    -> a = b
    -> d1 = d2.
Proof.
  intros.
  subst.
  reflexivity.  
Qed.

Hint Extern 100 (_ = _) =>
match goal with
  | [ _ : True |- _ ] => fail 1
  | _ => assert True by constructor; eapply mult_both 
end.


(* The identity [e] is unique. *)
Theorem unique_id : forall a, a <+> a = a -> a = e.
Proof.
  intros.
  pose proof mult_both a (a <+> a) (i a) e a (inv_r a) as m.
  symmetry.
  apply m.
  rewrite assoc.
  rewrite inv_r.
  rewrite id_r.
  reflexivity.
  symmetry.
  assumption.
Qed.
Hint Resolve unique_id.

(* [i a] is the left-inverse of [a]. *)
Theorem inv_l : forall a, i a <+> a = e.
Proof.
  intros.
  pose proof mult_both (i a <+> a) e e (i a <+> a) e as m.
  apply m.
  rewrite assoc.
  rewrite id_r.
  reflexivity.
  rewrite id_r.
  reflexivity.
  
(* [e] is the left-identity. *)
Axiom id_l : forall a, e <+> a = a.

(* [x] can be cancelled on the right. *)
Axiom cancel_r : forall a b x, a <+> x = b <+> x -> a = b.

(* [x] can be cancelled on the left. *)
Axiom cancel_l: forall a b x, x <+> a = x <+> b -> a = b.

(* The left identity is unique. *)
Axiom e_uniq_l : forall a p, p <+> a = a -> p = e.

(* The left inverse is unique. *)
Axiom inv_uniq_l : forall a b, a <+> b = e -> a = i b.

(* The left identity is unique. *)
Axiom e_uniq_r : forall a p, a <+> p = a -> p = e.

(* The right inverse is unique. *)
Axiom inv_uniq_r : forall a b, a <+> b = e -> b = i a.

(* The inverse operator distributes over the group operator. *)
Axiom inv_distr : forall a b, i (a <+> b) = i b <+> i a.

(* The inverse of an inverse produces the original element. *)
Axiom double_inv : forall a, i (i a) = a.

(* The identity is its own inverse. *)
Axiom id_inv : i e = e.
