Require Import propInv3.
Require Import verif_cond_4.
Local Open Scope Z.

Theorem proof3_4: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond4 ->
 (inv hands1 dryer2 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
elimtype False.
apply no_timeout_if_hands_ON.
apply H.
Qed.