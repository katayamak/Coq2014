Module Ex2_10.

(* Problem 10 *)


Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* \u4f7f\u3063\u3066\u3082\u3088\u3044 *)


Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.


Lemma inv_r : forall x, x * / x = 1.
Proof.
  intros.
  assert (H: (/ / x * / x * x * /x) = 1).
    rewrite <- (mult_assoc (/ / x) (/ x) x).
    rewrite inv_l.
    rewrite <- (mult_assoc (/ / x) 1 (/ x)).
    rewrite -> one_unit_l.
    rewrite -> (inv_l (/ x)).
    reflexivity.
  rewrite -> (inv_l (/ x)) in H.
  rewrite one_unit_l in H.
  apply H.
Qed.


Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  intros.
  rewrite <- (inv_l x).
  rewrite <- (one_unit_l (x * (/ x * x))).
  assert (H: / / x * / x = 1).
    rewrite (inv_l (/ x)).
    reflexivity.
  rewrite <- H.
  rewrite mult_assoc.
  rewrite <- (mult_assoc (/ / x) (/ x) x).
  rewrite mult_assoc.
  rewrite inv_l.
  rewrite <- (mult_assoc (/ / x) 1 (/ x)).
  rewrite (one_unit_l (/ x)).
  rewrite -> (inv_l (/ x)).
  rewrite one_unit_l.
  reflexivity.
Qed.

End Ex2_10.




















