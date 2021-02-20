Require Import propInv2.
Require Import verif_cond_3.
Require Import extra3.
Local Open Scope Z.

Theorem proof2_3: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond3 ->
 (inv hands1 dryer2 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
split.
unfold propInv2.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
intros.
(*analysis of cases i<timer1 and i=timer1*)
elim Zle_lt_or_eq with i timer1.
intros.
(*prove that dryer1 and dryer2 are equal in all indexes j<timer1*)
assert (Hdryer1_dryer2_same : (forall j, j<timer1 -> dryer1.[of_Z j]=dryer2.[of_Z j])).
intros.
apply arr_same_before_upd with OFF timer1.
split; assumption.
rewrite <- Hdryer1_dryer2_same.
rewrite <- Hdryer1_dryer2_same in H4.
apply startnewloop_to_propInv.
assumption.
split.
apply H2.
inversion_clear H0.
auto with zarith.
assumption.
auto with zarith.
assumption.
(*analysis of case i=timer1*)
intros.
rewrite H5.
rewrite H3.
apply get_set_same.
inversion_clear H0.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H10.
rewrite H9.
rewrite length_set.
apply dryer_inf.
inversion_clear H2.
assumption.
apply extra3.
split.
inversion_clear H.
inversion_clear H0.
split.
apply H.
assumption.
apply H.
Qed.