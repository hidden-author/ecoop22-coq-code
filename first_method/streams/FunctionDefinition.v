Require Import Sequences.
Require Import CPO.
Require Import Flat.
Require Import MyStreams.
Require Import TypeDecl.
Require Import Functional.


Module FunctionDefinitionMod (TD: TypeDecl)(Func : FunctionalMod TD).
Import TD.
Import Func TD.



Definition _f := DTD._f  T F .
Definition _f_seq := DTD._f_seq T F.
Definition _f_seq_mono := DTD._f_seq_mono  T F F_mono.


Definition f  :=
  fun s => lim (_f_seq  s)  (fun n => _f_seq_mono n s)  .


CoInductive sdefined  : StreamO -> Prop :=
|sdefined_def : forall o s,  o <> None -> sdefined s -> sdefined (scons o s).

Lemma sdefined_les_bisim : forall s s',  sdefined s -> les s s' -> bisim s s'. 
Proof.
cofix sdefined_les_bisim.
intros s s' Hsd Hle.
inversion Hle; subst; clear Hle.
inversion Hsd ; subst ; clear Hsd.
inversion H ; subst; [exfalso ; apply H3 ; auto | clear H3].
constructor; auto.
Qed.

Lemma forall_sdefined : forall s,  (forall i,  nth s i <> None) -> sdefined s.
Proof.
cofix forall_sdefined.
intros s Hall.
destruct s.
constructor.
*
  apply (Hall 0).
*
  eapply forall_sdefined ; eauto.
  intro i.
  apply (Hall (S i)).
Qed.

   
Definition defined (f : T -> StreamO) : Prop :=
  forall s,  sdefined (f s).

Lemma defined_les_bisim
      (f : T -> StreamO) :
  defined  f -> forall f',  (forall sa,  les (f sa) (f' sa)) ->
                             forall sa,  bisim (f sa) (f' sa).
Proof.
intros Hdef f' Hall sa.
eapply sdefined_les_bisim; eauto.   
Qed.


Lemma _f_les_S :  forall n s, les (_f n s)  ( F( _f  n) s).
Proof.
intros n  s.
revert s.
induction n.
*
  intro s.
  apply bot_is_bottom.
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
apply  lim_smaller.
intros s' Hin.
destruct Hin as (i & Heqi).
unfold _f_seq, DTD._f_seq in Heqi.
rewrite Heqi.
apply lef_fn_Ff.
Qed.

Lemma f_if_defined_fix : defined f  -> forall s,  bisim (f s) (F f s).
Proof.
intros Hdef s.
eapply defined_les_bisim ; eauto.
intros.
apply lef_f_Ff.
Qed.

Lemma defined_upto_any: forall   m s,   exists n,  defined_upto m (_f n s).
Proof.
 induction m ; intros s.
 *
   exists 0; constructor.
 *
   destruct (IHm s) as (n & Hdef).
   destruct (F_prod s n) as (n' & Hle & Hlt).
   unfold _f in *.
   assert (Hle' : les ( (DTD._f T  F n s)) ( (DTD._f T F n' s))).
   {
     apply  (_f_seq_mono_gen T  F F_mono _ _ s Hle).
   }
   assert (Hdef' : defined_upto m (DTD._f T  F n' s)).
   {
     eapply defined_upto_mono ; eauto.
   }
   exists (S n').
   eapply defined_upto_lts_mono ; eauto.
Qed.   


Lemma f_defined_upto_any : forall n s,  defined_upto n (f s).
Proof.
 intros n s.
 destruct (defined_upto_any  n  s) as (N & Hdef).
 eapply defined_upto_mono ; eauto.
 apply lim_upper.
 now exists N.
Qed.

Lemma sdefined_approx : forall s,  (forall n,  defined_upto  n s) -> sdefined s.
Proof.
cofix sdefined_approx.  
intros s Hall.
destruct s.
constructor.
*
  destruct o ; [intro Hand; discriminate| exfalso].
  specialize (Hall 1).
  inversion Hall.
*
  eapply sdefined_approx; eauto.
  intro n.
  specialize (Hall (S n)).
  inversion Hall; subst ; auto.
Qed.
  
Lemma f_sdefined : forall s,  sdefined (f s).
Proof.
intros s.
eapply  sdefined_approx; eauto.
intro n.
 apply f_defined_upto_any; auto.
Qed.

Lemma defining_defined : defined f.
Proof.
intros s.
apply f_sdefined; auto.
Qed.

Lemma f_fix: forall s,  bisim (f s) (F f s).
intros s.
apply f_if_defined_fix; auto.
apply defining_defined.
Qed.


Lemma f_unique_fix_aux : forall f',
    (forall s',  bisim (f' s') (F f' s')) -> forall s,  les  (f s) (f' s).
Proof.
intros f' Hall s.
apply  lim_smaller.
intros s' Hsin.
destruct Hsin as (n & Hn).
subst.
revert  s.
induction n ; intros s.
*
  apply bot_is_bottom.
*
  assert (HF : forall s,  les ((_f_seq s) (S n)) (F f' s)).
  {
    intros s'.
    apply F_mono.
    intro s''.
    specialize (IHn s'').
    apply IHn.
  }
  specialize (HF s).
  eapply les_trans; eauto.
  specialize (Hall s).
  apply nth_les.
  intro i.
  apply bisim_nth with (n0:=i) in Hall.
  rewrite Hall.
  apply leo_refl.
Qed.


Lemma f_unique_fix : forall f',
    (forall s',  bisim (f' s') (F f' s')) -> forall s,  bisim  (f s) (f' s).
Proof.
intros f' Hall s.
apply sdefined_les_bisim.  
*
  apply f_sdefined.
*
  apply f_unique_fix_aux; auto.
Qed.

End FunctionDefinitionMod.


