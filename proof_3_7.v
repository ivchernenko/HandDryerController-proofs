Require Import propInv3.
Require Import verif_cond_7.
Require Import extra7.
Require Import ind_scheme.
Local Open Scope Z.

Theorem proof3_7: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond7 -> 
 (inv hands1 dryer1 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
split.
unfold propInv3.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
intros.
(*analysis of cases i<timer1 and i=timer1*)
elim Zle_lt_or_eq with i (timer1-(11-1)).
intros.
apply startnewloop_to_propInv.
assumption.
split.
apply H3.
split.
inversion_clear H0.
auto with zarith.
apply H3.

(*case i=timer1-(11-1)*)
intros.
(*inductive proof*)
assert (Hdryer_hands : (forall k, (i<=k /\ k<i -> dryer1.[of_Z k]=ON /\ hands1.[of_Z k]=OFF))).
intros.
elimtype False.
auto with zarith.
assert (Hi_in_interval : (i<=i<=i+(11-1))).
auto with zarith.
generalize Hdryer_hands.
generalize Hi_in_interval.
apply generalize_i.

(*induction base *)
assert (Hbase : (ind_prove_pred dryer1 i (i+(11-1)) (i+(11-1)))).
unfold ind_prove_pred.
intros.
inversion_clear H0.
inversion_clear H8.
inversion_clear H9.
inversion_clear H10.
inversion_clear H11.
rewrite H9 in H1.
rewrite get_set_same in H1.
replace (timer1-1) with timer0 in H1.
inversion_clear H7.
inversion_clear H13.
inversion_clear H14.
inversion_clear H15.
inversion_clear H16.
inversion_clear H17.
inversion_clear H18.
inversion_clear H19.
inversion_clear H20.
inversion_clear H21.
apply H22 in H1.
inversion_clear H1.
inversion_clear H23.
specialize (H6 (timer0 - ctrlTimer0)).
replace hands1.[of_Z (timer0 - ctrlTimer0)] with hands0.[of_Z (timer0 - ctrlTimer0)] in H6.
assert (Htimer0_ctrlTimer0 : i<= timer0 - ctrlTimer0 < i+(11-1)).
auto with zarith.
apply H6 in Htimer0_ctrlTimer0.
inversion_clear Htimer0_ctrlTimer0.
rewrite H1 in H25.
contradict H25.
discriminate.
apply arr_same_before_upd with logvar timer1.
split.
auto with zarith.
assumption.
auto with zarith.
apply ctrlState_inf.
(*apply inductive scheme*)
intro.
intro.
apply natlike_down_bound_ind with (fun z=> (ind_prove_pred dryer1 i (i+(11-1)) z)) (i+(11-1)) i l in Hbase.
apply Hbase.
(*inductive step*)
intros.
unfold ind_prove_pred.
intros.
assert (true_or_false : forall b : bool, b=true \/ b=false).
induction b.
left.
reflexivity.
right.
reflexivity.
(*induction on hands*)
elim true_or_false with hands1.[of_Z (Z.pred y)].
intro.
exists (Z.pred y).
split.
auto with zarith.
split.
auto with zarith.
split.
assumption.
right.
assumption.
intros.
(*induction on dryer*)
elim true_or_false with dryer1.[of_Z (Z.pred y)].
(*hands=OFF /\ dryer=ON*)
intros.
assert (Hpremise_y : (forall k, (i<=k /\ k<y -> dryer1.[of_Z k]=ON /\ hands1.[of_Z k]=OFF))).
intros.
elim Zle_lt_or_eq with k (Z.pred y).
intros.
apply H9.
split.
apply H12.
assumption.
intros.
rewrite H13.
split; assumption.
auto with zarith.
apply H8 in Hpremise_y.
elim Hpremise_y.
intros.
exists x.
split.
auto with zarith.
apply H12.
(*hands=OFF /\ dryer=OFF*)
intros.
exists (Z.pred y).
split.
auto with zarith.
split.
auto with zarith.
split.
assumption.
left.
assumption.
assumption.
apply H3.

apply extra7.
split.
inversion_clear H.
inversion_clear H0.
split.
apply H.
assumption.
apply H.
Qed.

