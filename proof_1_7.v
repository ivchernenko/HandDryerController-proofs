Require Import propInv1.
Require Import verif_cond_7.
Require Import extra7.
Local Open Scope Z.

Theorem t1_7: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond7 -> 
 (inv hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
split.
unfold propInv1.
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
split.
inversion_clear H0.
auto with zarith.
apply H3.
(*analysis of case i=timer1*)
intros.
rewrite H5 in H3.
inversion_clear H3.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
elimtype False.
auto.
inversion_clear H3.
inversion_clear H6.
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