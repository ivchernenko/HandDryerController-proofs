Require Import extraInv.
Local Open Scope Z.

Definition cond1 :=
 timer1=0 /\  ctrlTimer1=0 /\ ctrlState1=ctrlState0.[0%int63 <- ctrlWaiting] /\hands1=hands0.[0%int63 <- OFF] /\ 
 dryer1=dryer0.[0%int63 <- OFF]. 
