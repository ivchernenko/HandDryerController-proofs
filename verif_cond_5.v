Require Import extraInv.
Local Open Scope Z.

Definition cond5 :=
ctrlState1.[of_Z timer1]<>ctrlWaiting /\ ctrlState1.[of_Z timer1]=ctrlDrying /\ hands1.[of_Z timer1]=ON /\ ctrlTimer2=0 /\ 
 ctrlState2=ctrlState1.[of_Z timer1 <- ctrlDrying] /\ ctrlTimer2<10.
