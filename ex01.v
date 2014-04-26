
(* Problem 0-2 *)

Theorem tautology : forall P : Prop, P -> P.
Proof.
  intros P H.
  assumption.
Qed.

(* 
Theorem wrong : forall P : Prop, P.
Proof.
  intros P.
Qed.

Error: Attempt to save an incomplete proof
*)

(* Problem 1 *)

Theorem Modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intro.
  intro.
  intro.
  intro.
  apply H0.
  apply H.
Qed.


(* Problem 2 *)
Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  intros.
  destruct H.
  intro.
  apply H0 in H1.
  apply H in H1.
  apply H1.
Qed.

(* Problem 3 *)

Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros.
  destruct H.
  apply H0 in H.
  destruct H.
  apply H.
Qed.




(* Problem 4 *)
Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros.
  intro.
  destruct H as [HA | HB].
  destruct H0 as [H0A H0B].
  apply HA in H0A. apply H0A.
  destruct H0 as [H0A H0B].
  apply HB in H0B. apply H0B.
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros.
  intro.
  destruct H0 as [H0A | H0B].
  destruct H as [HA HB].
  apply HA in H0A. apply H0A.
  destruct H as [HA HB].
  apply HB in H0B. apply H0B.
Qed.


Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  apply conj.
  intro.
  apply H.
  left. apply H0.
  intro.
  apply H.
  right.
  apply H0.
Qed.


(* Problem 5 *)
Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  intros.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  apply H0.
Qed.







