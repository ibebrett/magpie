Inductive nat : Type := 
  | O
  | S (n: nat).

Definition inc (n: nat): nat :=
  S n.

Definition dec (n: nat): nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint recur (n: nat): nat :=
  match n with
  | O => O
  | S n' => (recur n')
  end.

Compute (inc O).
Compute (dec (S (S O))).

Example arith:
  (inc O) = (dec (S (S O))).

Proof. simpl. reflexivity. Qed.

(* Prove that for all n, (recur n) = 0 by induction *)
Theorem recur_O: forall n : nat, recur n = O.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
  Qed.
