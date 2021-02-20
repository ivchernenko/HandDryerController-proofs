Require Import extraInv.
Local Open Scope Z.

Definition cond4 := 
 ctrlState1.[of_Z timer1]<>ctrlWaiting /\ ctrlState1.[of_Z timer1]=ctrlDrying /\ hands1.[of_Z timer1]=ON /\ ctrlTimer2=0 /\ 
 ctrlState2=ctrlState1.[of_Z timer1 <- ctrlDrying] /\ ctrlTimer2>=10 /\ ctrlTimer3=0 /\ 
 ctrlState3=ctrlState2.[of_Z timer1 <- ctrlWaiting].

(*Auxiliary theorem*)
Theorem no_timeout_if_hands_ON: cond4 -> False.

Proof.
intros.
unfold cond4 in H.
auto with zarith.
Qed.