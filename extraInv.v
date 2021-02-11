Require Export HandDryerControllerBase.
Local Open Scope Z.

Definition extraInv (hands dryer : array bool) (ctrlState :array nat) (ctrlTimer timer : Z) :=
ON=true /\ OFF=false /\ stopState=0%nat /\ errorState=1%nat /\ ctrlWaiting=2%nat /\ ctrlDrying=3%nat /\ 
timer>=0 /\ ctrlTimer>=0 /\ 
 (forall i, (0<=i /\ i<=timer -> ctrlState.[of_Z i]=ctrlWaiting \/ ctrlState.[of_Z i]=ctrlDrying)) /\ 
 (ctrlState.[of_Z timer]=ctrlDrying -> ctrlTimer<10 /\ hands.[of_Z (timer - ctrlTimer)]=ON /\ dryer.[of_Z (timer - ctrlTimer)]=ON /\ 
 forall i, (timer - ctrlTimer+1 <=i /\ i<=timer -> hands.[of_Z i]=OFF /\  dryer.[of_Z i]=ON)).

Definition commonStartnewloop (hands0 hands1 dryer0 dryer1 : array bool) (ctrlState0 ctrlState1 : array nat) 
(ctrlTimer0 ctrlTimer1 timer0 timer1 : Z) : Prop :=
(extraInv hands0 dryer0 ctrlState0 ctrlTimer0 timer0)  /\ timer1=timer0+1 /\ ctrlTimer1=ctrlTimer0+1 /\ 
ctrlState1=ctrlState0.[of_Z timer1 <- ctrlState0.[of_Z (timer1-1)]] /\ 
dryer1=dryer0.[of_Z timer1 <- dryer0.[of_Z (timer1-1)]] /\ hands1=hands0.[of_Z timer1 <- logvar].
