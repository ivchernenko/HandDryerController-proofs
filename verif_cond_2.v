Require Import extraInv.
Local Open Scope Z.

Definition cond2 := 
 ctrlState1.[of_Z timer1]=ctrlWaiting /\ hands1.[of_Z timer1]=ON /\ dryer2=dryer1.[of_Z timer1 <- ON] /\ ctrlTimer2=0 /\ 
ctrlState2=ctrlState1.[of_Z timer1 <- ctrlDrying].
