Require Import extraInv.
Require Import verif_cond_1.
Local Open Scope Z.

Theorem extra1: cond1-> (extraInv hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
auto with zarith.
split.
auto with zarith.
split.
(*ctrlState[i]=ctrlWaiting \/ ctrlState[i]=ctrlDrying*)
intros.
left.
rewrite H0 in H3.
replace i with 0.
rewrite H1.
apply get_set_same.
apply ctrlState_inf.
auto with zarith.
(*ctrlState[timer]=ctrlDrying -> ...*)
intros.
rewrite H1 in H3.
rewrite H0 in H3.
rewrite get_set_same in H3.
eontradict H3.
discriminate.
apply ctrlState_inf.
Qed.
