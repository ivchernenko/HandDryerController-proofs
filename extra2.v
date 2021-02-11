 Require Import extraInv.
Require Import verif_cond_2.
Local Open Scope Z.

Theorem extra2: (commonStartnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ 
 cond2 -> (extraInv hands1 dryer2 ctrlState2 ctrlTimer2 timer1).

Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H0.
inversion_clear H6.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
(*ctrlState0[i]=ctrlState2[i]*)
assert (HctrlState0_ctrlState2_same : (forall i, (0<=i /\ i<=timer0  -> ctrlState0.[of_Z i]=ctrlState2.[of_Z i]))).
intros.
replace ctrlState2.[of_Z i] with ctrlState1.[of_Z i].
apply arr_same_before_upd  with ctrlState0.[of_Z (timer1-1)] timer1.
split.
auto with zarith.
exact H7.
apply arr_same_before_upd with ctrlDrying timer1.
split.
auto with zarith.
exact H5.
(*split extraInv in the hypothesis*)
inversion_clear H4.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
inversion_clear H16.
inversion_clear H17.
inversion_clear H18.
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
apply H17.
auto with zarith.
auto with zarith.
(*case i=timer1*)
intros.
rewrite H20.
right.
rewrite H5.
apply get_set_same.
rewrite H7.
rewrite length_set.
apply ctrlState_inf.
inversion_clear H18.
assumption.
(*ctrlState[timer]=ctrlDrying -> ...*)
intros.
split.
auto with zarith. (*ctrlTimer<10*)
(*hands[timer-ctrlTimer]=ON*)
split.
rewrite H3.
rewrite Z.sub_0_r.
assumption.
(*dryer[timer-ctrlTimer]=ON*)
split.
rewrite H3.
rewrite Z.sub_0_r.
rewrite H2.
apply get_set_same.
rewrite H8.
rewrite length_set.
apply dryer_inf.
(*hands[i]=OFF /\ dryer[i]=ON*)
intros.
elimtype False.
auto with zarith.
Qed.

