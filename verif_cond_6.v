Require Import extraInv.
Local Open Scope Z.

Definition cond6 := 
 ctrlState1.[of_Z timer1]<>ctrlWaiting /\ ctrlState1.[of_Z timer1]=ctrlDrying /\ hands1.[of_Z timer1]<>ON /\ ctrlTimer1>=10 /\ 
 ctrlTimer2=0 /\ ctrlState2=ctrlState1.[of_Z timer1 <- ctrlWaiting].
