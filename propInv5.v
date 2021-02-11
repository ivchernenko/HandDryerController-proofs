Require Export extraInv.
Local Open Scope Z.

Definition propInv5 (hands dryer : array bool) (ctrlState : array nat) (ctrlTimer timer : Z) : Prop := 
 forall i, (0<i /\ i<=timer-(36000-1) /\ dryer.[of_Z i]=ON -> 
   exists j, (i<=j /\ j<i+(36000-1) /\ (forall k, (i<=k /\ k<j -> dryer.[of_Z k]=ON)) /\ dryer.[of_Z j]=OFF)).

Definition inv (hands dryer : array bool) (ctrlState : array nat) (ctrlTimer timer : Z) : Prop := 
 (propInv5 hands dryer ctrlState ctrlTimer timer) /\ (extraInv hands dryer ctrlState ctrlTimer timer).

Definition startnewloop (hands0 hands1 dryer0 dryer1 : array bool) (ctrlState0 ctrlState1 : array nat) 
(ctrlTimer0 ctrlTimer1 timer0 timer1 : Z) (logvar : bool) : Prop :=
(inv hands0 dryer0 ctrlState0 ctrlTimer0 timer0)  /\ timer1=timer0+1 /\ ctrlTimer1=ctrlTimer0+1 /\ 
ctrlState1=ctrlState0.[of_Z timer1 <- ctrlState0.[of_Z (timer1-1)]] /\ 
dryer1=dryer0.[of_Z timer1 <- dryer0.[of_Z (timer1-1)]] /\ hands1=hands0.[of_Z timer1 <- logvar].
