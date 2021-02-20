Require Import propInv5.
Local Open Scope Z.


Definition _timer1 :=36000.
Definition _timer0 := _timer1-1.
Definition _logvar := ON.
Definition _hands0 :=
 (make (of_Z (_timer1+1)) ON).[of_Z (_timer1-10) <- OFF].[of_Z (_timer1-9) <- OFF].[of_Z (_timer1- 8) <-OFF]
.[of_Z (_timer1-7) <- OFF].[of_Z (_timer1-6) <-OFF].[of_Z (_timer1-5)<- OFF].[of_Z (_timer1-4) <-OFF]
.[of_Z (_timer1-3)<-OFF].[of_Z (_timer1-2) <-OFF].[of_Z (_timer1-1)<-OFF].

Definition _hands1 := _hands0.[of_Z _timer1 <- _logvar].
Definition _dryer0 := make (of_Z (_timer1+1)) ON.
Definition _dryer1 := _dryer0.[of_Z _timer1 <- _dryer0.[of_Z (_timer1-1)]].
Definition _ctrlState0 := (make (of_Z (_timer1+1)) ctrlDrying).[of_Z (_timer1-1) <- ctrlWaiting].
Definition _ctrlState1 := _ctrlState0.[of_Z _timer1 <- _ctrlState0.[of_Z (_timer1-1)]].
Definition _ctrlTimer0 :=0.
Definition _ctrlTimer1 := _ctrlTimer0 + 1.
Definition _dryer2 := _dryer1.[of_Z _timer1 <- ON].
Definition _ctrlState2 := _ctrlState1.[of_Z _timer1 <- ctrlDrying].
Definition _ctrlTimer2 := 0.

Theorem proof5_2 : 
 exists hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1 dryer2 ctrlState2 ctrlTimer2 
(logvar : bool),
 ~((startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1 logvar) /\ 
    ctrlState1.[of_Z timer1]=ctrlWaiting /\ hands1.[of_Z timer1]=ON /\ dryer2=dryer1.[of_Z timer1 <- ON] /\ ctrlTimer2=0 /\ 
    ctrlState2=ctrlState1.[of_Z timer1 <- ctrlDrying] -> 
    (inv hands1 dryer2 ctrlState2 ctrlTimer2 timer1)).

Proof.
exists _hands0.
exists _hands1.
exists _dryer0.
exists _dryer1.
exists _ctrlState0.
exists _ctrlState1.
exists _ctrlTimer0.
exists _ctrlTimer1.
exists _timer0.
exists _timer1.
exists _dryer2.
exists _ctrlState2.
exists _ctrlTimer2.
exists _logvar.
unfold not.
intros.
assert (Hcond : 
 (startnewloop _hands0 _hands1 _dryer0 _dryer1 _ctrlState0 _ctrlState1 _ctrlTimer0 _ctrlTimer1 _timer0 _timer1 _logvar) /\ 
    _ctrlState1.[of_Z _timer1]=ctrlWaiting /\ _hands1.[of_Z _timer1]=ON /\ _dryer2=_dryer1.[of_Z _timer1 <- ON] /\ 
     _ctrlTimer2=0 /\ _ctrlState2=_ctrlState1.[of_Z _timer1 <- ctrlDrying]).

split.
split.
split.
(*proving propInv for timer0*)
unfold propInv5.
intros.
unfold _timer0 in H0.
unfold _timer1 in H0.
elimtype False.
auto with zarith.
(*proving extraInv for timer0*)
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
reflexivity.
split.
unfold _timer0.
unfold _timer1.
auto with zarith.
split.
unfold _ctrlTimer0.
auto with zarith.
split.
intros.
elim Zle_lt_or_eq with i _timer0.
intros.
right.

replace _ctrlState0.[of_Z i] with (make (of_Z (_timer1+1)) ctrlDrying).[of_Z i].

apply get_make.
 apply arr_same_before_upd with ctrlWaiting _timer0.
split.
assumption.
reflexivity.
intros.
rewrite H1.
left.
apply get_set_same.
rewrite length_make.
unfold _timer0.
unfold _timer1.
auto.
apply H0.
intros.
unfold _ctrlState0 in H0.
rewrite get_set_same in H0.
contradict H0.
discriminate.
unfold _timer0.
unfold _timer1.
auto.
split.
symmetry.
apply Zeq_plus_swap.
reflexivity.
repeat split.
repeat split.
unfold _ctrlState1.
rewrite get_set_same.
unfold _ctrlState0.
apply get_set_same.
auto.
auto.

(*proving negating requirement for timer1*)
apply H in Hcond.
inversion_clear Hcond.
unfold propInv5 in H0.
specialize (H0 (_timer1-(36000-1))).
assert (Hpremise : 
   0<(_timer1-(36000-1)) /\ (_timer1-(36000-1))<=(_timer1-(36000-1)) /\ _dryer2.[of_Z (_timer1-(36000-1))]=ON).
unfold _timer1.
auto with zarith.
apply H0 in Hpremise.
elim Hpremise.
intros.
inversion_clear H2.
inversion_clear H4.
inversion_clear H5.
replace _dryer2.[of_Z x] with _dryer0.[of_Z x] in H6.
unfold _dryer0 in H6.
rewrite get_make in H6.
contradict H6.
discriminate.
auto.
Qed.


