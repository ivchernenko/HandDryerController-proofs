Require Import extraInv.
Require Import verif_cond_8.

Theorem extra8: (commonStartnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ 
  cond8 -> False.

Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H0.
inversion_clear H3.
inversion_clear H4.
inversion_clear H5.
rewrite H4 in H.
rewrite get_set_same in H.
rewrite H4 in H2.
rewrite get_set_same in H2.
inversion_clear H1.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H10.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
inversion_clear H14.
(*Finding a contradiction*)
elim H13 with (timer1-1).
auto.
auto.
auto with zarith.
apply ctrlState_inf.
apply ctrlState_inf.
Qed.