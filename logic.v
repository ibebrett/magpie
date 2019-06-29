Inductive bool : Type :=
  | true
  | false.


Definition opp (t: bool): bool :=
  match t with 
  | true => false
  | false => true
  end.


Compute (opp false).
Compute (opp true).

Example test_opp:
  opp true = true.

Proof. simpl. reflexivity. Qed.
