 Require Import propInv3.
Require Import verif_cond_3.
Require Import extra3.
Require Import ind_scheme.
Local Open Scope Z.

Theorem proof3_3: (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1) /\ cond3 ->
 (inv hands1 dryer2 ctrlState1 ctrlTimer1 timer1).

Proof.
intros.
split.
unfold propInv3.
inversion_clear H.
inversion_clear H1.
inversion_clear H2.
intros.
(*analysis of cases i<timer1 and i=timer1*)
elim Zle_lt_or_eq with i (timer1-(11-1)).
intros.
(*prove that dryer1 and dryer2 are equal in all indexes j<timer1*)
assert (Hdryer1_dryer2_same : (forall j, j<timer1 -> dryer1.[of_Z j]=dryer2.[of_Z j])).
intros.
apply arr_same_before_upd with OFF timer1.
split; assumption.
assert (Hstartnewloop : (startnewloop hands0 hands1 dryer0 dryer1 ctrlState0 ctrlState1 ctrlTimer0 ctrlTimer1 timer0 timer1)).
assumption.
apply startnewloop_to_propInv in H0.
elim H0 with i.
intros.
exists x.
split.
apply H5.
split.
apply H5.
split.
intros.
rewrite <- Hdryer1_dryer2_same.
apply H5.
assumption.
auto with zarith.
rewrite <- Hdryer1_dryer2_same.
apply H5.
auto with zarith.
split.
apply H2.
split.
inversion_clear Hstartnewloop.
auto with zarith.
apply H2.
(*case i=timer1-(11-1)*)
intros.
(*inductive proof*)
assert (Hdryer_hands : (forall k, (i<=k /\ k<i -> dryer2.[of_Z k]=ON /\ hands1.[of_Z k]=OFF))).
intros.
elimtype False.
auto with zarith.
assert (Hi_in_interval : (i<=i<=i+(11-1))).
auto with zarith.
generalize Hdryer_hands.
generalize Hi_in_interval.
apply generalize_i.

(*induction base *)
assert (Hbase : (ind_prove_pred dryer2 i (i+(11-1)) (i+(11-1)))).
unfold ind_prove_pred.
intros.
exists (i+(11-1)).
split.
auto with zarith.
split.
auto with zarith.
split.
assumption.
apply Zeq_plus_swap in H4.
rewrite H4.
left.
rewrite H3.
apply get_set_same.
inversion_clear H0.
inversion_clear H7.
inversion_clear H8.
inversion_clear H9.
inversion_clear H10.
rewrite H9.
rewrite length_set.
apply dryer_inf.
(*apply inductive scheme*)
intro.
intro.
apply natlike_down_bound_ind with (fun z=> (ind_prove_pred dryer2 i (i+(11-1)) z)) (i+(11-1)) i l in Hbase.
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
elim true_or_false with dryer2.[of_Z (Z.pred y)].
(*hands=OFF /\ dryer=ON*)
intros.
assert (Hpremise_y : (forall k, (i<=k /\ k<y -> dryer2.[of_Z k]=ON /\ hands1.[of_Z k]=OFF))).
intros.
elim Zle_lt_or_eq with k (Z.pred y).
intros.
apply H8.
split.
apply H11.
assumption.
intros.
rewrite H12.
split; assumption.
auto with zarith.
apply H7 in Hpremise_y.
elim Hpremise_y.
intros.
exists x.
split.
auto with zarith.
apply H11.
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
apply H2.

apply extra3.
split.
inversion_clear H.
inversion_clear H0.
split.
apply H.
assumption.
apply H.
Qed.
