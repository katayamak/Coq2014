Module Ex03_1.

(* Problem 11 *)
Require Import Arith.

Fixpoint sum_odd(n:nat) : nat :=
  match n with
  | O => O
  | S m => 1 + m + m + sum_odd m
  end.

Goal forall n, sum_odd n = n * n.
Proof.
  intro.
  induction n.
    simpl.
    reflexivity.
    
    simpl.
    rewrite -> IHn.
    SearchAbout (_ * S _).
    rewrite mult_succ_r.
    rewrite (plus_comm (n * n) n).
    rewrite (plus_assoc).
    reflexivity.
Qed.

End Ex03_1.

