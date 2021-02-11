Require Export extraInv.
Local Open Scope Z.

Definition propInv2 (hands dryer : array bool) (ctrlState : array nat) (ctrlTimer timer : Z) : Prop := 
 forall i, (0<i /\ i<=timer -> (dryer.[of_Z (i-1)]=OFF /\ hands.[of_Z i]=OFF -> dryer.[of_Z i]=OFF)).

Definition inv (hands dryer : array bool) (ctrlState : array nat) (ctrlTimer timer : Z) : Prop := 
 (propInv2 hands dryer ctrlState ctrlTimer timer) /\ (extraInv hands dryer ctrlState ctrlTimer timer).

Definition startnewloop (hands0 hands1 dryer0 dryer1 : array bool) (ctrlState0 ctrlState1 : array nat) 
(ctrlTimer0 ctrlTimer1 timer0 timer1 : Z) : Prop :=
(inv hands0 dryer0 ctrlState0 ctrlTimer0 timer0)  /\ timer1=timer0+1 /\ ctrlTimer1=ctrlTimer0+1 /\ 
ctrlState1=ctrlState0.[of_Z timer1 <- ctrlState0.[of_Z (timer1-1)]] /\ 
dryer1=dryer0.[of_Z timer1 <- dryer0.[of_Z (timer1-1)]] /\ hands1=hands0.[of_Z timer1 <- logvar].

Theorem startnewloop_to_propInv: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 
timer1) -> 
 (propInv2 hands1 dryer1 ctrlState1 ctrlTimer1 timer0).

Proof.
intros Hstartnewloop.
inversion_clear Hstartnewloop.
(*split invariant*)
inversion_clear H.
unfold propInv2.
intros.
inversion_clear H0.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
(*prove that dryer0 and dryer1 are equal in all indexes j<timer1*)
assert (Hdryer0_dryer1_same : (forall j, j<timer1 -> dryer0.[of_Z j]=dryer1.[of_Z j])).
intros.
apply arr_same_before_upd with dryer0.[of_Z (timer1-1)] timer1.
split; assumption.
rewrite <- Hdryer0_dryer1_same.
rewrite <- Hdryer0_dryer1_same in H3. 
replace hands1.[of_Z i] with hands0.[of_Z i] in H3.
apply H1.
assumption.
assumption.
apply arr_same_before_upd with logvar timer1.
split.
auto with zarith.
assumption.
auto with zarith.
auto with zarith.
Qed.