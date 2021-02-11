Definition tact := 100.
Definition ON := true.
Definition OFF := false.
Definition stopState := 0.
Definition errorState := 1.
Definition ctrlWaiting := 2.
Definition ctrlDrying := 3.

Require Export Coq.Array.PArray.
Require Export ZArith.
Require Export Int63.
Local Open Scope Z_scope.

Parameter hands0 : array bool.
Parameter hands1 : array bool.
Parameter dryer0 : array bool.
Parameter dryer1 : array bool.
Parameter dryer2 : array bool.
Parameter ctrlState0 : array nat.
Parameter ctrlState1 : array nat.
Parameter ctrlState2 : array nat.
Parameter ctrlState3 : array nat.
Parameter ctrlTimer0 : Z.
Parameter ctrlTimer1 : Z.
Parameter ctrlTimer2 : Z.
Parameter ctrlTimer3 : Z.
Parameter timer0 : Z.
Parameter timer1 : Z.
Parameter logvar : bool.

(*Axioms that postulate the infinity of arrays dryer and ctrlState*)
Local Open Scope int63.
Axiom dryer_inf : forall n, (of_Z n <? (length dryer0))=true.
Axiom ctrlState_inf : forall n, (of_Z n <? (length ctrlState0))=true.
Axiom hands_inf : forall n, (of_Z n <? (length hands0))=true.
Local Open Scope Z.

(*we assume that if the numbers are equal in type int, then they are equal in 
 type Z*)
 Axiom mach_id_arith: forall n m : Z, of_Z n = of_Z m -> n=m.

 (*Auxiliary theorem*)
 (*updated array is  the same as the original one in all indexes smaller 
 than the update index*)
Section ArrayAuxiliary.
Variable A : Set.
Variable a b : array A.
Variable v : A.
Variable n m : Z.
Theorem arr_same_before_upd:  n<m /\ b=a.[of_Z m<-v]  -> a.[of_Z n]=b.[of_Z n].
Proof.
intro.
inversion_clear H.
rewrite H1.
symmetry.
apply get_set_other.
unfold not.
intro.
apply mach_id_arith in H.
rewrite H in H0.
auto with zarith.
Qed.
End ArrayAuxiliary.