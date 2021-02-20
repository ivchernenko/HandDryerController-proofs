Require Import propInv2.
Require Import verif_cond_7.
Require Import extra7.
Local Open Scope Z.

Theorem proof2_7: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond7 -> 
 (inv hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
split.
unfold propInv2.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
intros.
(*analysis of cases i<timer1 and i=timer1*)
elim Zle_lt_or_eq with i timer1.
intros.
apply startnewloop_to_propInv.
assumption.
split.
apply H3.
inversion_clear H0.
auto with zarith.
assumption.
(*analysis of case i=timer1*)
intros.
rewrite H6.
rewrite H6 in H5.
inversion_clear H0.
inversion_clear H8.
inversion_clear H9.
inversion_clear H10.
inversion_clear H11.
rewrite H10.
rewrite get_set_same.
replace dryer1.[of_Z (timer1-1)] with dryer0.[of_Z (timer1-1)] in H5.
inversion_clear H5.
assumption.
apply arr_same_before_upd with dryer0.[of_Z (timer1-1)] timer1.
split.
auto with zarith.
assumption.
apply dryer_inf.
inversion_clear H3.
assumption.
apply extra7.
split.
inversion_clear H.
inversion_clear H0.
split.
apply H.
assumption.
apply H.
Qed.

