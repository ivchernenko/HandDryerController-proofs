 Require Import extraInv.
Require Import verif_cond_3.
Local Open Scope Z.

Theorem extra3: (commonStartnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ 
 cond3 -> (extraInv hands1 dryer2 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H0.
inversion_clear H4.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
(*ctrlState0[i]=ctrlState1[i]*)
assert (HctrlState0_ctrlState1_same : (forall i, (0<=i /\ i<=timer0  -> ctrlState0.[of_Z i]=ctrlState1.[of_Z i]))).
intros.
apply arr_same_before_upd  with ctrlState0.[of_Z (timer1-1)] timer1.
split.
auto with zarith.
assumption.
(*split extraInv in the hypothesis*)
inversion_clear H2.
inversion_clear H9.
inversion_clear H10.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
inversion_clear H16.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
auto with zarith.
split.
auto with zarith.
split.
(*ctrlState[i]=ctrlWaiting \/ ctrlState[i]=ctrlDrying*)
intros.
elim Zle_lt_or_eq with i timer1.
(*case i<timer1*)
intros.
rewrite <- HctrlState0_ctrlState1_same.
apply H15.
auto with zarith.
auto with zarith.
(*case i=timer1*)
intros.
rewrite H18.
rewrite H5.
rewrite get_set_same.
apply H15.
auto with zarith.
apply ctrlState_inf.
inversion_clear H16.
assumption.
(*ctrlState[timer]=ctrlDrying -> ...*)
intros.
rewrite H in H16.
contradict H16.
discriminate.
Qed.