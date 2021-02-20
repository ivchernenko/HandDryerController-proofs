Require Import propInv1.
Require Import verif_cond_1.
Require Import extra1.
Local Open Scope Z.

Theorem proof1_1: cond1-> (inv hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
split.
unfold propInv1.
intros.
inversion_clear H.
rewrite H1 in H0.
elimtype False.
auto with zarith.
apply extra1.
assumption.
Qed.