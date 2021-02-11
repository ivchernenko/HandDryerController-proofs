Require Import extraInv.
Local Open Scope Z.

Definition cond8 := 
 ctrlState1.[of_Z timer1]<>ctrlWaiting /\ ctrlState1.[of_Z timer1]<>ctrlDrying.
