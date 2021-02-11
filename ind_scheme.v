Require Import HandDryerControllerBase.
Local Open Scope Z.

Section NatlikeInd.
Variable P : Z->Prop.
Variable z : Z.
Definition Q (x : Z) := P (z-x).

Lemma P_through_Q: forall x : Z, P x = Q (z-x).
Proof.
intros.
unfold Q.
replace (z-(z-x)) with x.
reflexivity.
auto with zarith.
Qed.

Lemma natlike_down_bound_ind: 
forall x,
 P z  -> (forall y : Z, x<y<=z -> P y -> P (Z.pred y)) ->
 forall y : Z,  x<=y<=z -> P y.
Proof.
intros.
rewrite P_through_Q.
rewrite P_through_Q in H.
replace (z-z) with 0 in H.
inversion_clear H1.
assert (Hsub_z_y : z-y<=z-x).
auto with zarith.
generalize Hsub_z_y.
apply Zle_minus_le_0 in H3.
generalize H3.
generalize (z-y).
assert (Hind_step_Q : (forall z0 : Z,  0<=z0 -> z0<z-x -> Q z0 -> Q (Z.succ z0))).
intros.
unfold Q.
rewrite Z.sub_succ_r.
apply H0.
auto with zarith.
replace (P (z-z0)) with (Q z0).
assumption.
reflexivity.
clear   H0 y H2 H3 Hsub_z_y.
intro.
intro.
assert (Hle_0_z_x : 0<=z-x-> Q 0).
intros.
assumption.
apply natlike_ind with (fun w=> w<=z-x -> Q w) z0 in Hle_0_z_x.
assumption.
intros.
elim Zle_lt_or_eq with x0 (z-x).
intros.
apply Hind_step_Q.
assumption.
assumption.
apply H1.
auto with zarith.
intros.
elimtype False.
auto with zarith.
auto with zarith.
assumption.
auto with zarith.
Qed.
End NatlikeInd.

Lemma generalize_i : 
 forall (P Q: Z->Prop) (x y : Z) ,  (forall l, (x<=l<=y -> (forall k, (x<=k /\ 
k<l -> (P k))) -> exists j, (l<=j /\ j<=y /\ (Q j)))) ->
(x<=x<=y -> (forall k, (x<=k /\ k<x -> (P k))) -> exists j, (x<=j /\ j<=y /\ (Q j))).
Proof.
intro.
intro.
intro.
intro.
intro.
apply H.
Qed.

Definition ind_prove_pred (dryer : array bool) (x y l : Z) : Prop := 
(forall k, (x<=k /\ k<l -> dryer.[of_Z k]=ON /\ hands1.[of_Z k]=OFF)) -> 
 exists j, (l<=j /\ j <=y /\ (forall k, (x<=k /\ k<j -> dryer.[of_Z k]=ON /\  hands1.[of_Z k]=OFF)) /\   
    (dryer.[of_Z j]=OFF \/ hands1.[of_Z j]=ON)).

