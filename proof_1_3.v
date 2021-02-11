Require Import propInv1.
Require Import verif_cond_3.
Local Open Scope Z.

Theorem t1_3: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond3 ->
 (propInv1 hands1 dryer2 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
unfold propInv1.
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
split.
assumption.
assumption.
rewrite <- Hdryer1_dryer2_same.
rewrite <- Hdryer1_dryer2_same in H2.
apply startnewloop_to_propInv.
assumption.
split.
apply H2.
split.
inversion_clear H0.
auto with zarith.
apply H2.
auto with zarith.
assumption.
(*analysis of case i=timer1*)
intros.
rewrite H4 in H2.
inversion_clear H2.
inversion_clear H6.
inversion_clear H7.
inversion_clear H8.
elimtype False.
auto.
inversion_clear H2.
inversion_clear H5.
assumption.
Qed.