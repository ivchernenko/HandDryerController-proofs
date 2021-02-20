Require Import propInv2.
Require Import verif_cond_5.
Require Import extra5.
Local Open Scope Z.

Theorem proof2_5: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond5 ->
 (inv hands1 dryer1 ctrlState2 ctrlTimer2 timer1).

Proof.
intros.
split.
unfold propInv2.
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
rewrite H8 in H7.
inversion_clear H7.
rewrite H2 in H10.
elimtype False.
contradict H10.
discriminate.
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
