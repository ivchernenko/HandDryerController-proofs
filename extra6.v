Require Import extraInv.
Require Import verif_cond_6.
Local Open Scope Z.

Theorem extra6: (commonStartnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ 
 cond6 -> (extraInv hands1 dryer1 ctrlState2 ctrlTimer2 timer1).


Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H5.
inversion_clear H0.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H10.
(*ctrlState0[i]=ctrlState2[i]*)
assert (HctrlState0_ctrlState2_same : (forall i, (0<=i /\ i<=timer0  -> ctrlState0.[of_Z i]=ctrlState2.[of_Z i]))).
intros.
replace ctrlState2.[of_Z i] with ctrlState1.[of_Z i].
apply arr_same_before_upd  with ctrlState0.[of_Z (timer1-1)] timer1.
split.
auto with zarith.
assumption.
apply arr_same_before_upd with ctrlWaiting timer1.
split.
auto with zarith.
assumption.
(*split extraInv in the hypothesis*)
inversion_clear H5.
inversion_clear H12.
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
inversion_clear H16.
inversion_clear H17.
inversion_clear H18.
inversion_clear H19.
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
rewrite <- HctrlState0_ctrlState2_same.
repeat split.
auto with zarith.
auto with zarith.
(*ctrlState[i]=ctrlWaiting \/ ctrlState[i]=ctrlDrying*)
intros.
elim Zle_lt_or_eq with i timer1.
(*case i<timer1*)
intros.
rewrite <- HctrlState0_ctrlState2_same.
apply H18.
auto with zarith.
auto with zarith.
(*case i=timer1*)
intros.
rewrite H21.
left.
rewrite H6.
apply get_set_same.
rewrite H8.
rewrite length_set.
apply ctrlState_inf.
inversion_clear H19.
assumption.
inversion_clear H19.
assumption.
(*ctrlState[timer]=ctrlDrying ->...*)
intros.
rewrite H6 in H19.
rewrite get_set_same in H19.
contradict H19.
discriminate.
rewrite H8.
rewrite length_set.
apply ctrlState_inf.
Qed.
