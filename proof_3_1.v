Require Import propInv3.
Require Import verif_cond_1.
Local Open Scope Z.

Theorem t2_1: cond1-> (propInv3 hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
unfold propInv3.
intros.
inversion_clear H.
rewrite H2 in H0.
elimtype False.
auto with zarith.
Qed.