Require Import propInv4.
Require Import verif_cond_5.
Require Import extra5.
Local Open Scope Z.

Theorem proof4_5: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond5 ->
 (inv hands1 dryer1 ctrlState2 ctrlTimer2 timer1).

Proof.
intros.
split.
unfold propInv4.
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
inversion_clear H0.
auto with zarith.
assumption.
(*analysis of case i=timer1*)
intros.
rewrite H8.
rewrite H8 in H7.
inversion_clear H0.
inversion_clear H10.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
rewrite H12.
rewrite get_set_same.
replace dryer1.[of_Z (timer1-1)] with dryer0.[of_Z (timer1-1)] in H7.
inversion_clear H7.
assumption.
apply arr_same_before_upd with dryer0.[of_Z (timer1-1)] timer1.
split.
auto with zarith.
assumption.
apply dryer_inf.
inversion_clear H5.
assumption.
apply extra5.
split.
inversion_clear H.
inversion_clear H0.
split.
apply H.
assumption.
apply H.
Qed.