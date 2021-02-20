Require Import Bool.

Require Import propInv5.
Require Import to_array.
Local Open Scope Z.


Definition _timer1 :=36000.
Definition _timer0 := _timer1-1.
Definition _logvar := OFF.
Definition _ctrlTimer0 :=(10-1).
Definition _ctrlTimer1 := _ctrlTimer0 + 1.

Lemma _timer1_can_be_length : 0<=(_timer1+1) <=(to_Z max_length).
Proof.
split.
unfold _timer1.
auto with zarith.
replace (_timer1+1) with (to_Z (of_Z (_timer1 +1))).
apply leb_spec.
auto.
symmetry.
apply is_int.
split.
unfold _timer1.
auto with zarith.
unfold _timer1.
replace (2^(to_Z digits)) with wB.
unfold wB.
unfold size.
auto with zarith.
auto.
Qed.

Definition hands_fun (n : Z) := negb ((_timer0 - _ctrlTimer0+1 <=?n) && (n<=? _timer0))%bool.
Definition h := to_array hands_fun (_timer1+1) _timer1_can_be_length.
Definition _dryer0 := make (of_Z (_timer1+1)) ON.
Definition _dryer1 := _dryer0.[of_Z _timer1 <- _dryer0.[of_Z (_timer1-1)]].
Definition _ctrlState0 := (make (of_Z (_timer1+1)) ctrlDrying).
Definition _ctrlState1 := _ctrlState0.[of_Z _timer1 <- _ctrlState0.[of_Z (_timer1-1)]].
Definition _dryer2 := _dryer1.[of_Z _timer1 <- ON].
Definition _ctrlState2 := _ctrlState1.[of_Z _timer1 <- ctrlWaiting].
Definition _ctrlTimer2 := 0.

Theorem proof5_6 : 
 exists hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1 ctrlState2 ctrlTimer2 
(logvar : bool),
 ~((startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1 logvar) /\ 
    ctrlState1.[of_Z timer1]<>ctrlWaiting /\ ctrlState1.[of_Z timer1]=ctrlDrying /\ hands1.[of_Z timer1]<>ON /\ ctrlTimer1>=10 /\ 
 ctrlTimer2=0 /\ ctrlState2=ctrlState1.[of_Z timer1 <- ctrlWaiting] -> 
    (inv hands1 dryer1 ctrlState2 ctrlTimer2 timer1)).

Proof.
elim h.
intro _hands0.
intro.
exists _hands0.
exists  _hands0.[of_Z _timer1 <- _logvar].
exists _dryer0.
exists _dryer1.
exists _ctrlState0.
exists _ctrlState1.
exists _ctrlTimer0.
exists _ctrlTimer1.
exists _timer0.
exists _timer1.
exists _ctrlState2.
exists _ctrlTimer2.
exists _logvar.
unfold not.
intros.
assert (Hcond : 
 (startnewloop _hands0 _hands0.[of_Z _timer1 <- _logvar]  _dryer0 _dryer1 _ctrlState0 _ctrlState1 _ctrlTimer0 _ctrlTimer1 
   _timer0 _timer1 _logvar) /\ 
   _ctrlState1.[of_Z _timer1]<>ctrlWaiting /\ _ctrlState1.[of_Z _timer1]=ctrlDrying /\ 
   _hands0.[of_Z _timer1 <- _logvar].[of_Z _timer1]<>ON /\   _ctrlTimer1>=10 /\  _ctrlTimer2=0 /\ 
   _ctrlState2=_ctrlState1.[of_Z _timer1 <- ctrlWaiting]).

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
right.
unfold _ctrlState0.
apply get_make.
intros.
assert (hands_values : 
 (length _hands0 = of_Z (_timer1+1)) /\ 
 (forall i, _timer0-_ctrlTimer0+1<=i /\ i<=_timer0 -> _hands0.[of_Z i]=OFF) /\ 
  (forall i, 0<=i /\ i<= _timer0 - _ctrlTimer0 -> _hands0.[of_Z i]=ON)).
split.
apply p.
split.
intros.
inversion_clear p.
rewrite H3.
unfold hands_fun.
apply negb_false_iff.
apply andb_true_iff.
split; apply Z.leb_le; apply H1.
unfold _timer0 in H1.
unfold _ctrlTimer0 in H1.
unfold _timer1.
unfold _timer1 in H1.
auto with zarith.
intros.
inversion_clear p.
rewrite H3.
unfold hands_fun.
apply negb_true_iff.
apply andb_false_iff.
left.
apply not_true_is_false.
unfold not.
intro.
apply Z.leb_le in H4.
auto with zarith.
unfold _timer0 in H1.
unfold _ctrlTimer0 in H1.
auto with zarith.
inversion_clear hands_values.
inversion_clear H2.
repeat split.
apply H4.
unfold _timer0.
unfold _ctrlTimer0.
unfold _timer1.
auto with zarith.
apply H3.
assumption.
unfold _dryer0.
apply get_make.
repeat split.
repeat split.
unfold _ctrlState1.
rewrite get_set_same.
unfold _ctrlState0.
rewrite get_make.
discriminate.
auto.
unfold _ctrlState1.
rewrite get_set_same.
unfold _ctrlState0.
rewrite get_make.
reflexivity.
auto.
rewrite get_set_same.
discriminate.
inversion_clear p.
rewrite H0.
auto.
unfold _ctrlTimer1.
unfold _ctrlTimer0.
auto with zarith.

(*proving negating requirement for timer1*)
apply H in Hcond.
inversion_clear Hcond.
unfold propInv5 in H0.
specialize (H0 (_timer1-(36000-1))).
assert (Hpremise : 
  (0< (_timer1-(36000-1)) /\ (_timer1-(36000-1))<=(_timer1-(36000-1)) /\ _dryer1.[of_Z (_timer1-(36000-1))]=ON)).
unfold _timer1.
auto with zarith.
apply H0 in Hpremise.
elim Hpremise.
intros.
inversion_clear H2.
inversion_clear H4.
inversion_clear H5.
replace _dryer1.[of_Z x] with _dryer0.[of_Z x] in H6.
unfold _dryer0 in H6.
rewrite get_make in H6.
contradict H6.
discriminate.
auto.
Qed.




