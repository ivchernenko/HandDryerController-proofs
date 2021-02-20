Require Import propInv3.
Require Import verif_cond_8.
Require Import extra8.
Local Open Scope Z.

Theorem proof3_8: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond8 ->
 (inv hands1 dryer2 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
elimtype False.
apply extra8.
inversion_clear H.
split.
inversion_clear H0.
split.
apply H.
assumption.
assumption.
Qed.