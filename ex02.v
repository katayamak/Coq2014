Module Ex2_7.

Require Import Arith.

(* Problem 6 *)

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
  intros.
  SearchAbout (_ + _ < _ + _).
  apply plus_lt_compat_r.
  apply H.
Qed.


(* Problem 7 *)
Goal forall P Q : nat -> Prop, P 0 -> (forall x, P x -> Q x) -> Q 0.
Proof.
  intros.
  apply (H0 0).
  apply H.
Qed.


Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
  intros.
  exists 1.
  apply H.
Qed.


Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
  intros.
  destruct H0.
  apply (H x q).
  apply H0.
Qed.

End Ex2_7.

Module Ex2_8.
Require Import Arith.

Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
Proof.
  intros.
  apply NPeano.Nat.add_cancel_r.
  apply mult_comm.
Qed.

End Ex2_8.

Module Ex2_9.

Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  SearchAbout (_+(_+_)).
  rewrite plus_assoc.
  rewrite plus_assoc.
  SearchAbout (_+_=_+_).
  apply NPeano.Nat.add_cancel_r.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  apply NPeano.Nat.add_cancel_l.
  apply plus_comm.
Qed.


Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  SearchAbout ((_+_)*_).
  rewrite NPeano.Nat.mul_add_distr_r.
  rewrite NPeano.Nat.mul_add_distr_l.
  rewrite NPeano.Nat.mul_add_distr_l.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  apply NPeano.Nat.add_cancel_l.
  rewrite plus_assoc.
  rewrite plus_comm.
  apply NPeano.Nat.add_cancel_l.
  simpl.
  SearchAbout (_ + 0).
  rewrite plus_0_r.
  rewrite mult_comm.
  rewrite mult_comm.
  SearchAbout ((_+_)*_).  
  rewrite mult_plus_distr_r.
  reflexivity.
Qed.

End Ex2_9.

