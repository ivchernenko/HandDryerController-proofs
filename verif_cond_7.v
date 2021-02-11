Require Import extraInv.
Local Open Scope Z.

Definition cond7 := 
 ctrlState1.[of_Z timer1]<>ctrlWaiting /\ ctrlState1.[of_Z timer1]=ctrlDrying /\ hands1.[of_Z timer1]<>ON /\ ctrlTimer1<10.
