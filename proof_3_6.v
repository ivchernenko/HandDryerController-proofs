Require Import propInv3.
Require Import verif_cond_6.
Local Open Scope Z.

Theorem t3_6: (startnewloop hands0  hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond6 -> 
 (propInv3 hands1 dryer1 ctrlState2 ctrlTimer2 timer1).

Proof.
intros.
unfold propInv3.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H5.
intros.
(*analysis of cases i<timer1-(11-1)  and i=timer1-(11-1)*)
elim Zle_lt_or_eq with i (timer1-(11-1)).
intros.
apply startnewloop_to_propInv.
assumption.
split.
apply H5.
inversion_clear H0.
split.
auto with zarith.
apply H5.
(*case i=timer-(11-1)*)
intros.
inversion_clear H0.
inversion_clear H8.
inversion_clear H10.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
inversion_clear H16.
inversion_clear H17.
inversion_clear H18.
inversion_clear H9.
inversion_clear H20.
inversion_clear H21.
inversion_clear H22.
rewrite H20 in H1.
rewrite get_set_same in H1.
replace (timer1-1) with timer0 in H1.
apply H19 in H1.
inversion_clear H5.
inversion_clear H24.
inversion_clear H25.
inversion_clear H1.
inversion_clear H27.
replace hands1.[of_Z i] with hands0.[of_Z i] in H26.
replace (timer0 - ctrlTimer0) with i in H1.
rewrite H26 in H1.
contradict H1.
discriminate.
auto with zarith.
(*hands0[i]=hands1[i]*)
apply arr_same_before_upd with logvar timer1.
split.
auto with zarith.
assumption.
auto with zarith.         (*timer0=timer1-1*)
apply ctrlState_inf.     (*timer1 < length ctrlState0*)
(*i<=timer1-(11-1)*)
inversion_clear H5.
inversion_clear H8.
assumption.
Qed.
