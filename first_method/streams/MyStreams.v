Require Import Classical.
Require Import Sequences.
Require Import CPO.
Require Import Flat.
Require Import FunctionalExtensionality.

CoInductive Stream{A: Type} :=
 |scons : A -> Stream -> Stream.


Lemma stream_match{A: Type} (s : Stream(A := A)) :
s = match s with scons h t  => scons  h t end.
Proof.
  destruct s; reflexivity.
Qed.

CoInductive les{A : Type} : Stream(A := option A) -> Stream(A:= option A) -> Prop :=
|les_def : forall a1 s1 a2 s2,  leo a1 a2 -> les s1 s2 -> les (scons a1 s1) (scons a2 s2).  


Definition hd{A: Type} (s: Stream (A:= A)) := match s with (scons h _) => h end.
Definition tl{A: Type} (s: Stream (A:= A)) := match s with (scons  _ s) => s end.


Fixpoint nth{A : Type} (s : Stream (A:= A))(n : nat) :  A :=
  match n, s with
    0 , scons a _ => a
  | S m, scons _ s' => nth  s' m
  end.                         


Fixpoint firstn {A : Type} (n : nat) (s : Stream (A:= A)) :=
  match n, s with
    0,  _ => nil
  | S m, (scons a s')  => cons a (firstn m s')
  end.

Lemma nth_les{A : Type}  : forall (s1 s2 : Stream (A := option A)),
    (forall i, leo (nth s1 i) (nth s2 i)) ->  les s1 s2.
Proof.
cofix nth_les.
intros s1 s2 Hall.
destruct s1, s2.
constructor.
*
  apply (Hall 0).
*
  eapply nth_les ; eauto.
  intros i.
  apply (Hall (S i)).
Qed.


Lemma les_nth{A : Type}  : forall (s1 s2 : Stream (A :=option A)),   les s1 s2 ->
    forall i, leo (nth s1 i) (nth s2 i).
Proof.
intros s1 s2 Hle i.
revert s1 s2 Hle.
induction i; intros s1 s2 Hle.
*
  inversion Hle ; subst.
  apply H.
* inversion Hle ; subst.
   apply IHi; auto.
Qed.    




CoFixpoint bot{A : Type} := scons (A := option A) (None) bot.

Lemma bot_eta{A : Type} : bot = scons (A := option A) (None) bot.
Proof.
  rewrite (stream_match bot) at 1.
  reflexivity. 
Qed.

Lemma nth_bot{A:  Type} : forall i,  nth bot(A:= option A) i = None.
Proof.
  induction i; auto.
Qed.
  
  
Lemma bot_is_bottom{A : Type}  : forall (s :  Stream (A:=option A)), les bot s.
Proof.
  intros s.
  apply nth_les.
  intros i.
  rewrite nth_bot.
  constructor.
Qed.       


Lemma les_refl{A: Type} : forall (s : Stream (A := option A)) ,  les s s.
Proof.
  cofix les_refl.  
  intros s.
  destruct s.  
  constructor.
  * 
    apply leo_refl.
  *  
   eapply les_refl; eauto.  
Qed.


Lemma les_trans{A: Type} : forall (s1 s2 s3 : Stream (A := option A)),  les s1 s2 -> les s2 s3 -> les s1 s3.
Proof.
  cofix les_trans.
  intros s1 s2 s3 Hle1 Hle2. 
  inversion Hle1 ; inversion Hle2; subst.
  injection H5; intros; subst; clear H5.
  constructor.
  *
  eapply leo_trans ; eauto.
  *
  eapply les_trans ; eauto.  
Qed.

Lemma increasing_smap_hd {A: Type} : forall  (q : Seq (A := Stream (A:= option A))),
    increasing les q -> increasing leo (fun n => hd (q n)).
Proof.
intros q Hrel.
 intros n.
 specialize (Hrel n).
now   inversion Hrel.
Qed.


Lemma increasing_smap_tl {A: Type} : forall  (q : Seq (A := Stream (A:= option A))),
  increasing les q -> increasing les (fun n =>  tl (q n)).
Proof.
intros q Hs n.
specialize (Hs n).
now inversion Hs.
Qed.


CoFixpoint lim {A: Type} (q : Seq (A := Stream (A:=  option A)))(Hrel : increasing les q)  :=
      scons
        (proj1_sig  (limF (fun n => hd (q n))   (increasing_smap_hd q Hrel)))
        (lim (fun n => tl (q n)) (increasing_smap_tl   q Hrel )).


Lemma lim_eta{A: Type} : forall (q : Seq (A := Stream (A:=  option A)))(Hrel : increasing les q),
     lim q Hrel =
      scons
        (proj1_sig  (limF (fun n => hd (q n))   (increasing_smap_hd q Hrel)))
        (lim (fun n => tl (q n)) (increasing_smap_tl   q Hrel )).
 Proof. 
 intros q Hr.
 rewrite (stream_match (lim q Hr)).
reflexivity. 
Qed.

 
 
 Lemma  sin_smap_hd{A: Type} : forall  (o: option A) s q,  sin  (scons o s) q ->
                                                           sin o (fun n => hd (q n)).
Proof.
intros o s q Hin.
destruct Hin.
exists x.
now rewrite <- H.
Qed.
  
Lemma  sin_smap_tl{A: Type} :
  forall  (o: option A) s q,  sin  (scons o s) q ->  sin s (fun n => tl (q n)).
Proof.
intros o s q Hin. 
destruct Hin.
exists x.
now rewrite <- H.
Qed.

Lemma  sin_smap_hd_rev{A: Type} :
  forall  (o: option A)  q,  sin o (fun n => hd (q n)) -> exists s,  sin  (scons o s) q.
Proof.  
  intros o q Hin.
  remember (fun n => hd (q n)) as sq.
  destruct Hin as (n & Hin).
 exists (tl (q n)), n.
 rewrite Hin, Heqsq.
 now destruct (q n).
Qed.


Lemma  sin_smap_tl_rev{A: Type} :
  forall  s  (q: Seq (A := Stream (A := option A))),
    sin s (fun n => tl (q n)) -> exists o,  sin (scons o s) q.
Proof.
 intros o q Hin.
remember (fun n => tl (q n)) as sq.
destruct Hin as (n & Hin).
unfold sin.
exists (hd (q n)), n.
rewrite Hin, Heqsq.
 now destruct (q n).
Qed.  


Lemma lim_upper{A: Type} : forall  (q : Seq (A := Stream (A:= option A)))(Hr : increasing les q),
     forall s', sin s' q -> les s' (lim  q Hr).
cofix lim_upper.
intros q Hr s' Hin.
destruct s'.
rewrite lim_eta.  
constructor.
*
  remember  (limF (fun  n => hd (q n))   (increasing_smap_hd q Hr)) as p.
  destruct p as (o' & Ho').
  apply Ho'.
  eapply sin_smap_hd ; eauto.
*
  eapply lim_upper.
  eapply   sin_smap_tl ; eauto.
 Qed.


Lemma lim_smaller{A: Type} :
  forall  (q : Seq (A := Stream (A:= option A)))(Hr : increasing les q),
     forall sup',  (forall s',  sin s' q -> les s' sup') ->  les  (lim q Hr) sup'.
Proof.
cofix lim_smaller.
intros q Hr sup' Hall.
rewrite lim_eta.
destruct sup' as (o' & sup').
constructor.
*
  remember  (limF (fun n => hd (q n))   (increasing_smap_hd q Hr)) as p.
  destruct p as (o'' & (Ho''1 & Ho''2)).
  cbn.
  
  apply Ho''2.
  intros a Hin.
  destruct a ; [| constructor].
  generalize (Ho''1 _ Hin) ; intro Hbis.
  inversion Hbis; subst; clear Hbis.
  destruct o'.
  +
    destruct (classic (a0 = a)) ; subst.  
    - 
      apply leo_refl.
   -
     exfalso.
     apply H ; clear H.
     destruct (sin_smap_hd_rev _ _ Hin) as (s'  & Hs').
     apply Hall in Hs'.
     inversion Hs' ; subst.
     inversion H2 ; subst ; auto.
  +
    exfalso.       
    destruct (sin_smap_hd_rev _ _ Hin) as (s'  & Hs').
    apply Hall in Hs'.
    inversion Hs' ; subst.
    inversion H2.
*
  eapply lim_smaller ; eauto.
  intros s' Hin.
  destruct  (sin_smap_tl_rev _ _ Hin) as (a & Ha).
  apply Hall in Ha.
  inversion Ha ; auto.
Qed.

Lemma les_lub{A: Type} :
  forall (q: Seq (A := Stream (A:= option A)) ), increasing les q -> exists b, lub les b q.
Proof.
intros s Hs.
exists (lim _ Hs).
split.
*
  apply lim_upper.
*
  apply lim_smaller.
Qed.



CoInductive bisim{A: Type} : Stream(A := A) -> Stream (A := A) -> Prop :=
|bisim_def : forall a1 a2  s1 s2,  a1 = a2 -> bisim s1 s2 -> bisim (scons a1 s1) (scons a2 s2).      
  

Lemma nth_bisim{A:Type} : forall (s1 s2 :  Stream(A := A)),
    (forall n, nth s1 n=  nth s2 n) -> bisim s1 s2.
Proof.
  cofix nth_bisim.
  intros s1 s2 Hall.
  destruct s1; destruct s2.
  constructor.
  *
    apply (Hall 0).
  *
    apply nth_bisim.
    intro n.    
    apply (Hall (S n)).
Qed.



Lemma bisim_nth{A:Type} : forall (s1 s2 :  Stream(A := A)),
    bisim s1 s2 -> (forall n, nth s1 n =  nth s2 n).
Proof.
  intros s1 s2 Hbis n.
  revert s1 s2 Hbis.
  induction n;
    intros s1 s2 Hbis;
    inversion Hbis; subst; auto.
  apply IHn; auto.
Qed.

Lemma les_antisym{A:Type} :
  forall (s1 s2 :  Stream(A := option A)), les s1 s2 -> les s2 s1 -> bisim s1 s2.
Proof.                                                               
  intros s1 s2 Hle1 Hle2.
  apply nth_bisim.
  intro n.
  apply les_nth with (i:= n) in Hle1, Hle2.
  now apply leo_antisym.
Qed.

Definition stream_cpo {A: Type} : cpo (A:= Stream(A:= option A)) bisim  les :=
  {|
  bbot := bot;
  bbot_is_bottom := bot_is_bottom;
  bprefl := les_refl;
  bptrans := les_trans ;
  bpantisym := les_antisym;
  bpsup := les_lub
  |}.


Inductive lts{A : Type} : Stream(A := option A)  -> Stream(A := option A)  ->  Prop :=
|lts_now :  forall a s,  lts (scons None s) (scons (Some a) s)
|lts_later : forall a s1 s2,  lts s1 s2 -> lts (scons (Some a) s1) (scons (Some a) s2).

 
Lemma lim_lub{A:Type}(q:Seq(A:=Stream(A:=option A)))(H:increasing les q):
lub les (lim q H) q.
Proof.
split.
*  apply lim_upper.
*  apply lim_smaller.
Qed.   
