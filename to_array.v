Require Import ZArith.
Require Import Int63.
Require Import PArray.
Require Import ind_scheme.
Require Import HandDryerControllerBase.
Local Open Scope Z.

Section FunArray.
Variable f : Z->bool.
Variable n : Z.


Definition larray (y : Z) :=  {a : array bool | ((length a = of_Z n) /\ (forall k, 0<=k<y -> a.[of_Z k]=(f k)))}.

Definition to_array_def (y : Z) : (0<=n<=to_Z max_length) ->0<=y<=n -> larray y.
intro.
assert (Hintn : ((of_Z n <=? max_length)%int63 = true)).
inversion_clear H.
replace n with (to_Z (of_Z n)) in H1.
apply leb_spec.
assumption.
symmetry.
apply is_int.
split.
assumption.
replace (2^(to_Z digits)) with wB.
apply Z.le_lt_trans with (to_Z max_length).
assumption.
apply to_Z_bounded.
auto.
apply natlike_upper_bound_rec.
unfold larray.
exists (make (of_Z n) (f 0)).
split.
rewrite length_make.
rewrite Hintn.
reflexivity.
intros.
elimtype False.
auto with zarith.
intros.
elim H1.
intros.
unfold larray.
exists x.[of_Z y0 <- (f y0)].
split.
rewrite length_set.
apply p.
intros.
elim Zle_lt_or_eq with k y0.
intro.
inversion_clear p.
replace x.[of_Z y0 <- f y0].[of_Z k] with x.[of_Z k].
apply H5.
split.
apply H2.
assumption.
apply arr_same_before_upd with (f y0) y0.
split.
assumption.
reflexivity.
intro.
rewrite H3.
apply get_set_same.
inversion_clear p.
rewrite H4.
apply ltb_spec.
rewrite <- is_int.
rewrite <- is_int.
inversion_clear H0.
assumption.
inversion_clear H.
split.
assumption.
replace (2^(to_Z digits)) with wB.
apply Z.le_lt_trans with (to_Z max_length).
assumption.
apply to_Z_bounded.
auto.
inversion_clear H.
inversion_clear H0.
split.
assumption.
replace (2^(to_Z digits)) with wB.
apply Z.lt_trans with n.
assumption.
apply Z.le_lt_trans with (to_Z max_length).
assumption.
apply to_Z_bounded.
auto.
apply Zlt_succ_le.
apply H2.
Defined.

End FunArray.

Definition to_array (f : Z-> bool) (n : Z) : 0<=n<=(to_Z max_length) -> larray f  n n.
intro.
apply to_array_def.
assumption.
auto with zarith.
Defined.

