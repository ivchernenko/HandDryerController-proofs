Require Import propInv1.
Require Import verif_cond_1.
Local Open Scope Z.

Theorem t1_1: cond1-> (propInv1 hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
unfold propInv1.
intros.
inversion_clear H.
rewrite H1 in H0.
elimtype False.
auto with zarith.
Qed.