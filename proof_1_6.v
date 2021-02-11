Require Import propInv1.
Require Import verif_cond_6.
Local Open Scope Z.

Theorem t1_6: (startnewloop hands0  hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond6 -> 
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
inversion_clear H5.
inversion_clear H9.
inversion_clear H10.
inversion_clear H11.
elimtype False.
auto.
inversion_clear H5.
inversion_clear H8.
assumption.
Qed.