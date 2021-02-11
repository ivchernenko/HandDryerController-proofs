Require Import propInv4.
Require Import verif_cond_2.
Local Open Scope Z.

Theorem t4_2: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond2-> 
 (propInv4 hands1 dryer2 ctrlState2 ctrlTimer2 timer1).

Proof.
intros.
unfold propInv4.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
intros.
(*analysis of cases i<timer1 and i=timer1*)
elim Zle_lt_or_eq with i timer1.
intros.
(*prove that dryer1 and dryer2 are equal in all indexes j<timer1*)
assert (Hdryer1_dryer2_same : (forall j, j<timer1 -> dryer1.[of_Z j]=dryer2.[of_Z j])).
intros.
apply arr_same_before_upd with ON timer1.
split; assumption.
rewrite <- Hdryer1_dryer2_same.
rewrite <- Hdryer1_dryer2_same in H5.
apply startnewloop_to_propInv.
assumption.
split.
apply H3.
inversion_clear H0.
auto with zarith.
assumption.
auto with zarith.
assumption.
(*analysis of case i=timer1*)
intros.
rewrite H6.
rewrite H2.
apply get_set_same.
inversion_clear H0.
inversion_clear H8.
inversion_clear H9.
inversion_clear H10.
inversion_clear H11.
rewrite H10.
rewrite length_set.
apply dryer_inf.
inversion_clear H3.
assumption.
Qed.
