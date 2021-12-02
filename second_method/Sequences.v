Require Import Classical.
Require Import FunctionalExtensionality.
Require Import IndefiniteDescription.
Require Import PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import  Wf_nat.
Require Import WfInf.
Require Import Lia.

Definition Seq{A:Type} := nat -> A.

Definition sin{A : Type}(a : A)(q: Seq(A:=A)) := exists i, a = q i.

Lemma sin_nth{A:Type}(q: Seq(A:=A)): forall n,  sin (q n) q.
Proof.
intro n.
now exists n.
Qed.

Definition increasing {A: Type} (R: A -> A -> Prop)(q : Seq) : Prop  :=
  forall n,  R (q n) (q (S n)).

Definition strictly_increasing{A : Type}(R: A -> A -> Prop)(q : Seq(A := A)) :=
  increasing R q /\
  forall n,  (q (S n)) <> (q n).

Definition stabilizing_to{A : Type}(q : Seq(A := A)) (a:A) :=
  exists n, forall m, n <= m -> q m = a.


Definition stabilizing{A : Type}(q : Seq(A := A)) :=
  exists a, stabilizing_to q a.

Definition ascending {A: Type} (R: A -> A -> Prop)(q : Seq) : Prop  :=
 increasing R q /\ ~stabilizing q.

Definition subsequence {A : Type}(q1 q2 : Seq(A := A)): Prop :=
  exists (f : Seq(A:=nat)),  strictly_increasing le f /\
                             forall n,  q1 n= q2 (f n).

Definition sup{A: Type} (R : A -> A-> Prop) (sup_val: A) (q : Seq(A:=A)) :=
  (forall a, sin a q -> R a sup_val) /\
  (forall sup_val',  (forall a, sin a q -> R a sup_val')  -> R sup_val sup_val').


Lemma increasing_alt{A:Type}(R: A -> A -> Prop)(R_refl : forall a,  R a a)
(R_trans : forall a b c,  R a b -> R b c ->  R a c) 
(R_antisym : forall a b,  R a b -> R b a -> a = b)
  : forall (q: Seq (A := A)),
    increasing R q  <-> forall (i j : nat),  i <= j -> R (q i) (q j).
Proof.
split.   
{
  intros Hr i j Hle.
  induction Hle.
  *
    apply R_refl.
  *
    specialize (Hr m).
    eapply R_trans  ; eauto.
}
{
  intros Hall.
  intro n.
  apply Hall; auto.
}
Qed.

Definition constant{A:Type}(q: Seq(A := A)) := exists(a:A), forall n, q n = a.  
  
Section NatSequences.
  
Fixpoint star(f: Seq(A:= nat))(n : nat):=
  match n with
    0 => f 0
    | S m =>   max (f n) (f (star f m))
  end.  

Lemma strictly_increasing_alt : forall f,
    strictly_increasing le f <-> (forall n m, n < m -> f n < f m).
Proof.  
split.
{
  intros Hs n m Hlt.
  induction Hlt.
  {
    destruct Hs as (Hi & Hall).
    specialize (Hi n).
    specialize (Hall n).
    lia.
  }
  {
    destruct Nat.lt_strorder as (_ & Hllt).
    eapply Hllt; eauto.
    destruct Hs as (Hi & Hall).
    specialize (Hi m).
    specialize (Hall m).
    lia.
  }  
}  
{
  intros Hall.
  split.
  *
    intros n.
    specialize (Hall n  _ (Nat.lt_succ_diag_r n)).
    lia.
  *
    intros n.
    specialize (Hall n  _ (Nat.lt_succ_diag_r n)).
    lia.
}  
Qed.

Definition above_diagonal (f: Seq(A:= nat)) := forall n,  n <= f n.

Lemma stringly_increasing_above_diag : forall (f :Seq(A:= nat)),
    strictly_increasing le f-> above_diagonal f.
Proof.
intros f Hs n.  
destruct Hs as (Hi & Hn).
unfold increasing in Hi.
assert(Hlt : forall n,  f n < f (S n)).
{
  intros m; specialize (Hi m); specialize (Hn m); lia.
}  
clear Hi Hn.
induction n; try lia.
specialize (Hlt n);  lia.
Qed.

Definition strictly_above_diagonal (f: Seq(A:= nat)) := forall n,  n < f n.


Lemma star_strictly_increasing : forall f,  strictly_above_diagonal f ->
                             strictly_increasing le (star f).
Proof.
intros f Hf.
rewrite strictly_increasing_alt.  
intros  i j Hle.
induction Hle.
*
  cbn.
  eapply Nat.le_trans with (m := f (star f i)); try lia.
  apply Hf.
*
  cbn.
  eapply Nat.le_trans; eauto.
  specialize (Hf (star f m)); lia.
Qed.


Lemma strictly_increasing_unbounded: forall f,  strictly_increasing le f ->
                                                forall N,  exists n, N <= f n.
Proof.  
intros f.
induction N.
*
  exists 0; lia.
*
  destruct IHN as (n & Hle).
  exists (S n).
  rewrite strictly_increasing_alt in H.
  apply Nat.le_trans with (m := S (f n)); try lia.
  apply H; lia.
Qed.


End NatSequences.


Section OrderedSequences.

Variable A  : Type.
Variable R : A -> A -> Prop.
Hypothesis R_refl : forall a,  R a a.
Hypothesis R_trans : forall a b c,  R a b -> R b c ->  R a c. 
Hypothesis R_antisym : forall a b,  R a b -> R b a -> a = b.



Lemma constant_intervals :
  forall (q : Seq(A:=A)) i j,  increasing R q ->  i <= j -> q j = q i ->
    forall  k, i <= k -> k <= j -> q k = q i.                         
Proof.                                                      
intros q i j Hi Hle Heq k Hlei Hlej.
apply R_antisym.
*
  rewrite <- Heq.
  rewrite increasing_alt in Hi; eauto.
*
  rewrite  increasing_alt in Hi; eauto.
Qed.



Lemma subsequence_increasing : forall (q' q :Seq(A := A)),
    increasing R q -> subsequence q' q -> increasing R q'.
Proof.
intros q' q Hi Hs.
destruct Hs as (f & Hf & Hall).
rewrite increasing_alt; auto.
intros i j Hle.
repeat rewrite Hall.
rewrite increasing_alt in Hi; auto.
apply Hi.
destruct Hf as (Hfi & _).
rewrite increasing_alt in Hfi; [apply Hfi ; auto | apply Nat.le_refl | apply Nat.le_trans | apply Nat.le_antisymm].
Qed.

Lemma ascending_subsequence : forall q  : Seq(A :=A),
    ascending R q -> exists q',  subsequence q' q /\ strictly_increasing R q'.
Proof.   
intros q Ha.
destruct Ha as (Hi & Hns). 
assert (Hex : forall n,  exists m,  n <= m /\  q m <>  q n).
{
  intro n.
  unfold stabilizing in Hns.
  generalize (not_ex_all_not _ _ Hns); intro Hns'.
  unfold stabilizing_to in Hns'.
  specialize (Hns' (q n)).
  clear Hns.
  generalize (not_ex_all_not _ _ Hns'); intro Hns.
  specialize (Hns n).
  clear Hns'.
  apply  not_all_ex_not in Hns.
  destruct Hns as (m & Hnim).
  apply imply_to_and in Hnim.
  now exists m.
}  
apply functional_choice in Hex.
clear Hns.
destruct Hex as (f & Hall).
exists (fun n => q (star f n)).
split.
*
  exists (star f); split; intros ; auto.
  apply star_strictly_increasing.
  intros n.
  destruct (Hall n) as (Ha1 & Ha2).
  case (Nat.eq_dec n (f n)); intros; subst; try lia.
  exfalso.
  apply Ha2.
    now rewrite <- e.
*
  split.
  +
    intros n.
    cbn.
    apply (increasing_alt R); auto.
    eapply Nat.le_trans with (m := f (star f n)); try lia.
    destruct (Hall (star f n)) as (Ha1 & _ ); auto.
  +
    intro n.
    destruct (Hall (star f n)) as (Ha1 & Ha2 ).
    intro Heq.
    apply Ha2; clear Ha2.
    assert (Hle : (star f n <= star f (S n))); cbn; try lia.    
    apply (constant_intervals _ _ _ Hi Hle Heq); auto; cbn; lia.
Qed.


Lemma subsequence_ascending : forall q' q : Seq(A :=A),
    increasing R q -> subsequence q' q ->
    strictly_increasing R q' -> ascending R q.
Proof.   
intros q' q Hi Hs Hsi.
split ; auto.
intros (a & n & Hst).
destruct Hsi as (Hi' & Hnq).
destruct Hs as (f & Hf1 & Hf2).
destruct (strictly_increasing_unbounded _ Hf1 n) as (m & Hle).
generalize (Hst _ Hle); intro Heq.
rewrite <- Hf2 in Heq.
apply (Hnq m).
rewrite Heq.
rewrite Hf2.
apply Hst.
apply Nat.le_trans with (m := f m); auto.
destruct Hf1 as (Hni & _).
apply Hni.
Qed.


Lemma subsequence_iff_ascending : forall q  : Seq(A :=A),
    ascending R q <-> increasing R q /\ exists q',  subsequence q' q /\ strictly_increasing R q'.
Proof.
split.
*
  intro Ha.
  split; destruct Ha; auto.
  apply ascending_subsequence; split; auto.
*
  intros (q' & q'' & Hs & Hsi).
  apply (subsequence_ascending q'' q); auto.
Qed.


End OrderedSequences.
