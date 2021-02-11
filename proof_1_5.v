Require Import propInv1.
Require Import verif_cond_5.
Local Open Scope Z.

Theorem t1_5: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond5 ->
 (propInv1 hands1 dryer1 ctrlState2 ctrlTimer2 timer1).

Proof.
intros.
unfold propInv1.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H5.
intros.
(*analysis of cases i<timer1 and i=timer1*)
elim Zle_lt_or_eq with i timer1.
intros.
apply startnewloop_to_propInv.
assumption.
split.
apply H5.
split.
inversion_clear H0.
auto with zarith.
apply H5.
(*analysis of case i=timer1*)
intros.
rewrite H7 in H5.
(*split startnewloop*)
inversion_clear H0.
inversion_clear H9.
inversion_clear H10.
inversion_clear H11.
inversion_clear H12.
rewrite H10 in H1.
rewrite get_set_same in H1.
inversion_clear H8.
(*split extraInv*)
inversion_clear H14.
inversion_clear H15.
inversion_clear H16.
inversion_clear H17.
inversion_clear H18.
inversion_clear H19.
inversion_clear H20.
inversion_clear H21.
inversion_clear H22.
replace (timer1-1) with timer0 in H1.
apply H23 in H1.
inversion_clear H5.
inversion_clear H24.
inversion_clear H25.
replace dryer1.[of_Z (timer1-1)] with dryer0.[of_Z (timer1-1)] in H24.
elimtype False.
inversion_clear H1.
inversion_clear H27.
inversion_clear H28.
replace (timer1-1) with timer0 in H24.
apply Zcase_sign with ctrlTimer0.
intros.
rewrite H28 in H27.
rewrite Z.sub_0_r in H27.
rewrite H24 in H27.
contradict H27.
discriminate.
intros.
elim H29 with timer0.
intros.
rewrite H31 in H24.
contradict H24.
discriminate.
auto with zarith.
intros.
auto with zarith.
auto with zarith.
apply arr_same_before_upd with dryer0.[of_Z (timer1-1)] timer1.
split.
auto with zarith.
assumption.
auto with zarith.
apply ctrlState_inf.
inversion_clear H5.
inversion_clear H8.
assumption.
Qed.


