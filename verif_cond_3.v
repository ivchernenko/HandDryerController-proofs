Require Import extraInv.
Local Open Scope Z.

Definition cond3 := 
 ctrlState1.[of_Z timer1]=ctrlWaiting /\ hands1.[of_Z timer1]<>ON /\ dryer2=dryer1.[of_Z timer1 <- OFF].
