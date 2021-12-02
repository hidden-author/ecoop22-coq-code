Require Import Sequences.
Require Import CPO.
Require Import CoList.
Require Import TypeDecl.
Require Import Functional.
Require Import Lia.

Module FuncDefMod (TD: TypeDecl)(Func : FunctionalMod TD).
Import TD.
Import Func TD.



Definition _f := DTD._f  T F .
Definition _f_seq := DTD._f_seq T F.
Definition _f_seq_mono := DTD._f_seq_mono  T F F_mono.


Definition f  :=
  fun s => lim (_f_seq  s)  (fun n => _f_seq_mono n s)  .


   
Definition defined (D : T -> Prop) (f : T -> CoList) : Prop :=
  forall s,  D s -> sdefined (f s).

Lemma defined_les_bisim
      (D : T -> Prop) (f : T -> CoList) :
  defined D f -> forall f',  (forall sa,  D sa -> les (f sa) (f' sa)) -> forall sa,  D sa -> bisim (f sa) (f' sa).
Proof.
intros Hdef f' Hall sa HD.
eapply sdefined_les_bisim; eauto.   
Qed.




Lemma _f_les_S :  forall n s, les (_f n s)  ( F( _f  n) s).
Proof.
intros n  s.
revert s.
induction n.
*
  intro s.
  constructor.
*        
  apply F_mono.
  intro s.
  apply IHn.
Qed.



Lemma lef_fn_f : forall n,  lef T (_f n) f.
Proof.
intros n s.
eapply lim_upper; eauto.  
now exists n.
Qed.

Lemma lef_fn_Ff : forall n,  lef T (_f n) (F f).
Proof.  
intros n s.
eapply les_trans.
*
  apply _f_les_S.
*
  apply F_mono.
  apply lef_fn_f.
Qed.


Lemma lef_f_Ff : lef T  f (F f).
Proof.
intros s.
apply  lim_lower.
intros s' Hin.
destruct Hin as (i & Heqi).
rewrite Heqi.
apply lef_fn_Ff.
Qed.

Lemma f_if_defined_fix (D : T -> Prop) : defined D f  -> forall s,  D s -> bisim (f s) (F f s).
Proof.
intros Hdef s HDs.
eapply defined_les_bisim ; eauto.
intros.
apply lef_f_Ff.
Qed.

Definition F_prod_strong t (HD : D t) :=  forall m,  exists n, m <=  n /\ lts (_f  n  t) (_f   (S n) t).


Lemma _f_seq_mono_gen: forall m n s,  m <= n -> les (_f m s) (_f n s).
Proof.  
intros n m s Hle.
induction Hle.
*
  apply les_refl.
*
  eapply les_trans ; eauto.
  apply _f_les_S.
Qed.


Lemma defined_upto_any: 
    forall  s (HD  : D s), F_prod_strong s  HD ->
                           forall m , exists n,   m <= n /\defined_upto m (_f n s).
Proof.
 intros s HD HF.
induction m.
* 
  exists 1 ; split ; auto ; constructor.
*
 unfold F_prod_strong in HF.
 destruct IHm as (n & Hle & Hdef).
 destruct (HF n) as (n' & Hle' & Hlt).
 exists (S n') ; split ; try lia.
 eapply defined_upto_mono with (s2:= _f n' s) in Hdef.
 + 
   eapply  defined_upto_lts_mono ; eauto.
 +
   apply _f_seq_mono_gen ; lia.
Qed.



Lemma sdefined_or_defined_upto_any:
  forall  s,  D s ->  (exists n,  sdefined (F (_f n)  s))    \/  forall m, exists n,   m <= n /\defined_upto m (_f n s).
Proof.
intros s HD.
destruct  (F_prod _  HD) as [HF | HF]; [left; auto|].
right.
unshelve eapply defined_upto_any ; eauto.
Qed.



Lemma f_defined_upto_any : forall  s,  D s -> sdefined (f s) \/ forall n,  defined_upto n (f s).
Proof.
 intros s HD.
 destruct (sdefined_or_defined_upto_any   _ HD) as  [Hdef | Hdef].
 * left.
   destruct Hdef as (n & Hdef).
   eapply sdefined_les_mono  with (s0 :=(F (_f  n) s)) ; eauto. 
   apply  (lef_fn_f (S n) s); auto.
 *
   right.
   intro n.
   specialize (Hdef n).
   destruct Hdef as (N & Hle & Hdef).
   eapply defined_upto_mono ; eauto.
   apply lim_upper.
   now exists N.
Qed.

Lemma sdefined_approx : forall s,  (forall n,  defined_upto  n s) -> sdefined s.
Proof.
cofix sdefined_approx.  
intros s Hall.
destruct s.
*
  specialize (Hall 1).
  inversion Hall.  
*
  constructor.
*
  constructor.
  eapply sdefined_approx; eauto.
  intro n.
  specialize (Hall (S n)).
  inversion Hall; subst ; auto.
Qed.
  
Lemma f_sdefined : forall s,  D s -> sdefined (f s).
Proof.
intros s HD.
destruct (f_defined_upto_any _ HD) ; auto.
eapply  sdefined_approx; eauto.
Qed.

Lemma defining_defined : defined D f.
Proof.
intros s HDs.
apply f_sdefined; auto.
Qed.

Lemma f_fix: forall s,  D s -> bisim (f s) (F f s).
intros s HD.
apply f_if_defined_fix with (D := D); auto.
apply defining_defined.
Qed.

End FuncDefMod.


