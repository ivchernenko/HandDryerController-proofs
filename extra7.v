Require Import Coq.Bool.Bool.

Require Import extraInv.
Require Import verif_cond_7.
Local Open Scope Z.

Theorem extra7: (commonStartnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ 
 cond7 -> (extraInv hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H0.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H8.
(*ctrlState0[i]=ctrlState1[i]*)
assert (HctrlState0_ctrlState1_same : (forall i, (0<=i /\ i<=timer0  -> ctrlState0.[of_Z i]=ctrlState1.[of_Z i]))).
intros.
apply arr_same_before_upd  with ctrlState0.[of_Z (timer1-1)] timer1.
split.
auto with zarith.
assumption.
(*split extraInv in the hypothesis*)
inversion_clear H3.
inversion_clear H10.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
inversion_clear H16.
inversion_clear H17.
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
apply H16.
auto with zarith.
auto with zarith.
(*case i=timer1*)
intros.
rewrite H19.
right.
assumption.
inversion_clear H17.
assumption.
(*ctrlState[timer]=ctrlDrying -> ...*)
intros.
split.
assumption.  (*ctrlTimer<10*)
rewrite H6 in H1.
rewrite get_set_same in H1.
assert (Htimer0_timer1_1 : timer0=timer1-1).
apply Zeq_plus_swap.
rewrite H0.
reflexivity.
rewrite <- Htimer0_timer1_1 in H1.
apply H18 in H1.
inversion_clear H1.
inversion_clear H20.
inversion_clear H21.
assert (Hsub_timer_ctrlTimer_const : timer1 - ctrlTimer1=timer0 - ctrlTimer0).
auto with zarith.
(*hands[timer-ctrlTimer]=ON*)
split.
rewrite Hsub_timer_ctrlTimer_const.
replace hands1.[of_Z (timer0 - ctrlTimer0)] with hands0.[of_Z (timer0 - ctrlTimer0)].
assumption.
apply arr_same_before_upd with logvar  timer1.
split.
auto with zarith.
assumption.
(*dryer[timer-ctrlTimer]=ON*)
split.
rewrite Hsub_timer_ctrlTimer_const.
replace dryer1.[of_Z (timer0 - ctrlTimer0)] with dryer0.[of_Z (timer0 - ctrlTimer0)].
assumption.
apply arr_same_before_upd with dryer0.[of_Z (timer1-1)]  timer1.
split.
auto with zarith.
assumption.
(*hands[i]=OFF /\ dryer[i]=ON*)
intros.
elim Zle_lt_or_eq with i timer1.
intros.
replace hands1.[of_Z i] with hands0.[of_Z i].
replace dryer1.[of_Z i] with dryer0.[of_Z i].
apply H22.
auto with zarith.
apply arr_same_before_upd with dryer0.[of_Z (timer1-1)] timer1.
split; assumption.
apply arr_same_before_upd with logvar timer1.
split; assumption.
intros.
rewrite H23.
split.
(*hands [timer]=OFF*)
apply not_true_is_false.
assumption.
(*dryer [timer]=ON*)
rewrite H7.
rewrite get_set_same.
rewrite <- Htimer0_timer1_1.
apply Zcase_sign with ctrlTimer0.
intros.
rewrite H24 in H20.
rewrite Z.sub_0_r in H20.
assumption.
intros.
apply H22.
auto with zarith.
intros.
elimtype False.
auto with zarith.
apply dryer_inf.
inversion_clear H21.
assumption.
apply ctrlState_inf.
Qed.

