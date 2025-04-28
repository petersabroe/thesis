Fixpoint AdvantageD_sum P l Q A :=
  match l with
  | [::] => AdvantageD P Q A
  | R :: l => AdvantageD P R A + AdvantageD_sum R l Q A
  end.

Lemma AdvantageD_sum_chain {P Q A} l : AdvantageD P Q A <= AdvantageD_sum P l Q A.
  move: P. induction l => //= P.
  advantage_trans a.
  by apply lerD.
Qed.

Ltac nssprove_triangle l :=
  eapply le_trans; [ apply (AdvantageD_sum_chain l) | unfold AdvantageD_sum ].
