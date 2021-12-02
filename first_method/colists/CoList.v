Require Import Classical.
Require Import Sequences.
Require Import CPO.
Require Import WfInf.
Require Import Wf_nat.
Require Import ClassicalDescription.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.

Lemma or_orbool :  forall P Q : Prop, P \/ Q -> {P} + {Q}.
Proof.
intros P Q Hor.
destruct (excluded_middle_informative P) as [HP | HnP].
- now left.
- right; tauto.
Qed.

Lemma orbool_dec : forall P : Prop,  {P} + {~ P}.
Proof.
intro P.
apply or_orbool,classic.
Qed.
 
CoInductive CoList{A: Type} :=
  bot : CoList  
 | snil : CoList 
 |scons : A -> CoList-> CoList.



Lemma colist_match{A: Type} (s : CoList(A := A)) :
  s =
  match s with
   bot => bot 
   |  snil => snil      
   |scons h t  => scons  h t
  end.
Proof.
destruct s; reflexivity.
Qed.


CoInductive les{A : Type} : CoList(A :=A) -> CoList(A:=  A) -> Prop :=
|les_bot : forall s,  les  bot s  
|les_snil :  les snil snil 
|les_def : forall a s1 s2,  les s1 s2 -> les (scons a s1) (scons a s2).  


Definition hd{A: Type} (s: CoList (A:= A)) : option (option A)  :=
  match s with
  | bot => None  
  | snil => Some None
  |  (scons h _) => Some (Some h)
  end.


Definition tl{A: Type} (s: CoList (A:= A))  : CoList (A := A) :=
  match s with
  | bot => bot  
  |snil =>  bot 
  |  (scons  _ s) => s
  end.


Fixpoint nth{A : Type} (n : nat)(s : CoList (A:= A)):=
  match n, s with
  |_, bot => None  
  |  _, snil => Some None
  |  0 , scons a _ =>  Some (Some a)
  | S m, scons _ s' => nth m s'  
  end.                         


Lemma nth_bot{A: Type} : forall n,  nth(A:=A)  n bot  = None.
Proof.
intros [| n]  ; reflexivity. 
Qed.


Lemma nth_nil{A : Type} : forall n ,  nth(A :=A) n snil   = Some None.
Proof.
  intros [| n]  ;  reflexivity.
Qed.




Lemma nth_scons{A : Type} :
  forall n s a,   nth(A := A) n s  =  Some (Some a) ->
                       forall i, i <= n -> exists a' ,  nth i s  = Some (Some a' ).
Proof.
induction n; intros s.
*
  intros a  Heq i Hle.  
  exists a .
  assert (i = 0) ; try lia; subst; auto.
*
  intros   a'  Heq i Hle.
  destruct s.
  +
    rewrite nth_bot in Heq ; discriminate.
  +
    rewrite nth_nil in Heq ; discriminate.
  +
    cbn in Heq.
    specialize (IHn  _ _ Heq).
    destruct i.
    -
      exists a; auto.
    -
      eapply IHn ; eauto; lia.
Qed.

Lemma les_refl{A: Type} : forall (s : CoList(A := A)) ,  les s s.
Proof.
cofix les_refl.  
intros s.
destruct s.
* constructor.
* 
   constructor ; intro Habs; discriminate.
*
  constructor.
   eapply les_refl; eauto.  
Qed.


Lemma les_trans{A: Type} : forall (s1 s2 s3 : CoList (A := A)),  les s1 s2 -> les s2 s3 -> les s1 s3.
Proof.
cofix les_trans.
intros s1 s2 s3 Hle1 Hle2. 
inversion Hle1 ; inversion Hle2; subst; auto; try discriminate ; try constructor.   
injection H3; intros; subst; clear H3.
constructor.
eapply les_trans ; eauto.  
Qed.



Lemma increasing_smap_tl {A: Type} : forall  (q : Seq (A := CoList (A:=  A))),
    increasing les q -> increasing les (fun n =>  tl (q n)).
Proof. 
intros q Hmon n.
specialize (Hmon n).
now inversion Hmon; subst; try constructor.
Qed.


CoFixpoint lim {A: Type}
           (q : Seq (A := CoList (A:=  A)))(Hmon : increasing les q) : CoList (A:= A) :=
  match  orbool_dec (exists a k s,  q k = scons a s) with
  | left  w   =>
    let (a, _) :=
   constructive_indefinite_description _  w in
     scons a
            (lim (fun n => tl (q n))
                     (increasing_smap_tl q Hmon))
  | right _ =>
      match  orbool_dec (exists k, q k = snil) with
      | left _ => snil
      | right _ => bot
      end
  end.

Lemma lim_eta{A: Type} :
forall (q : Seq (A := CoList (A:= A)))(Hmon : increasing les q),
  lim q Hmon =
   match  orbool_dec (exists a k s,  q k = scons a s) with
  | left  w   =>
    let (a, _) :=
   constructive_indefinite_description _  w in
     scons a
            (lim (fun n => tl (q n))
                     (increasing_smap_tl q Hmon))
  | right _ =>
      match  orbool_dec (exists k, q k = snil) with
      | left _ => snil
      | right _ => bot
      end
  end.
Proof.
intros q Hmon.
rewrite (colist_match (lim q Hmon)).
cbn.
remember (orbool_dec
      (exists (a : A) (k : nat) (s : CoList),
          q k = scons a s)) as x.
destruct x.
* remember (constructive_indefinite_description _ e) as y.
  destruct y ; auto.
*
  remember (orbool_dec (exists k : nat, q k = snil)) as z.
  destruct z; auto.
Qed.

Lemma increasing_gen {A: Type} : forall (q : Seq (A := CoList (A:= A))),
    increasing les q -> forall m n,  m <= n -> les (q m) (q n).
Proof.
intros q Hmon m n Hle.
induction Hle.
*
  apply les_refl.
*
  eapply les_trans ; eauto.
Qed.

Lemma lim_eta_snil{A: Type} :
forall (q : Seq (A := CoList (A:= A)))(Hmon : increasing les q),
  sin snil q -> lim q Hmon = snil.
Proof.
intros q Hmon Hin.
rewrite lim_eta.
remember ( orbool_dec
      (exists (a : A) (k : nat) (s : CoList),
         q k = scons a s)) as x.
destruct x.
*
  exfalso.
  destruct e as (a & k & s & Heq).
  clear Heqx.
  destruct Hin as (i & Heq').
  case (le_lt_dec i k); intro Hcas.
  +   
    apply increasing_gen with (m := i) (n := k) in Hmon; auto.
    rewrite  Heq,  <- Heq' in Hmon.
    inversion Hmon.    
  +
    apply increasing_gen with (m := k) (n := i) in Hmon; try lia.
    rewrite  Heq,  <- Heq' in Hmon.
    inversion Hmon.    
 *
   
   remember  (orbool_dec (exists k : nat, q k = snil)) as x.
   destruct x ; auto.
   exfalso.
   apply n0.
   destruct Hin as (i & Heq).
   exists i ; rewrite Heq; auto.
Qed.

Lemma increasing_scons_eq{A: Type} : forall  (q : Seq (A := CoList (A:= A))),
    increasing les q ->
    forall m n a s a' s',  q m = (scons a s) -> q n = (scons a' s') -> a = a'. 
Proof.
intros q Hmon  m n a s a' s' Heq1 Heq2.
case (le_lt_dec m n); intro Hcas.
*
  eapply  increasing_gen in Hmon ; eauto.
  rewrite Heq1, Heq2  in Hmon.
  inversion Hmon ; auto.
*
  assert (Hle  : n <= m) ; [lia| clear Hcas].
  eapply  increasing_gen in Hmon ; eauto.
  rewrite Heq1, Heq2  in Hmon.
  inversion Hmon ; auto.
Qed.

 Lemma lim_eta_scons{A: Type} :
forall (q : Seq (A := CoList (A:= A)))(Hmon : increasing les q) a s,
  sin (scons a s)  q -> lim q Hmon = scons a ((lim (fun n =>  tl (q n))
                       (increasing_smap_tl q Hmon))).
Proof.
intros q Hmon a s Hin.
rewrite lim_eta.
remember ( orbool_dec
      (exists (a : A) (k : nat) (s : CoList),
         q k= scons a s)) as x.
destruct x.
*
  remember (constructive_indefinite_description  _ e) as y.
  destruct y as (a' & k' & s' & Heq').
  clear Heqy Heqx.
  destruct e as (a'' & k'' & s'' & Heq'').
  destruct  Hin as (i & Heq).
  symmetry in Heq.
  generalize (increasing_scons_eq _ Hmon _ _ _ _ _ _ Heq' Heq); intros.
  rewrite H ; auto.
*
  exfalso.
  clear Heqx.
  apply n; clear n.
  destruct Hin as (i & Heq).
  exists a, i, s ; rewrite Heq ; auto.  
Qed.



Lemma lim_eta_bot{A: Type} :
forall (q : Seq (A := CoList (A:= A)))(Hmon : increasing les q),
  (forall s,  sin s q -> s = bot)  -> lim q Hmon = bot.
Proof.
intros q Hmon Hall.
rewrite lim_eta.
remember ( orbool_dec
      (exists (a : A) (k : nat) (s : CoList),
         q k = scons a s)) as x.
destruct x.
clear Heqx.
*
  exfalso.
  destruct e as (a & k & s & Heq).
  symmetry in Heq.
  rewrite (Hall _ (sin_nth q k)) in Heq ; discriminate.
*
  clear n Heqx.
  remember (orbool_dec  (exists k : nat, q k= snil)) as x.
  destruct x ; auto.
  exfalso.
  destruct e as (k & Heq).
  clear Heqx.
  symmetry in Heq.
  rewrite (Hall _ (sin_nth q k)) in Heq ; discriminate.
Qed.


Lemma  sin_smap_tl{A: Type} : forall  (a : A) s q,  sin  (scons a s) q ->  sin s (fun n => tl (q n)).
Proof.
intros a s q Hin. 
destruct Hin.
exists x.
now rewrite <- H.
Qed.  

Lemma lim_upper{A: Type} :
  forall  (q : Seq (A := CoList (A:=  A)))(Hm : increasing les q),
     forall s', sin s' q -> les s' (lim q Hm).
Proof.
cofix lim_upper.
intros q Hm s' Hin.
destruct s'.
*
  constructor.
*
 rewrite lim_eta_snil ; auto.
 apply les_refl.
*
  erewrite  lim_eta_scons ; eauto.
  constructor.
  eapply lim_upper; eauto.
  eapply sin_smap_tl; eauto.
Qed.

Lemma lim_lower_aux1{A : Type}  : forall  (q : Seq (A := CoList(A:= A))),
    increasing les q -> (forall s,  sin s q -> les s snil) -> ( (forall s, sin s q  -> s = bot)\/ exists s, sin s q /\ s = snil ).
Proof.
intros q Hmon Hall.
case (classic (forall s' : CoList, sin s' q -> les s' bot)) ; intros Hcas.
*
  left.
  intros s Hin.
  specialize (Hcas _ Hin).
  inversion Hcas ; auto.
*
  right.
  apply not_all_not_ex.
  intro Hall'.
  apply Hcas; clear Hcas.
  intros s' Hin.
  specialize (Hall' s').
  intuition.
  specialize (Hall _ Hin).
  inversion Hall; subst.
 + 
   constructor.
 +
   exfalso ; apply H0; auto.
Qed.

Lemma lim_lower_aux2{A : Type}  :
  forall  (q : Seq (A := CoList(A:= A))) a s,
    increasing les q ->
    (forall s',  sin s' q -> les s' (scons a s)) ->
    ( (forall s', sin s' q  -> s' = bot)\/ exists s' s'', sin s' q /\ s' =  scons a s'' /\ les s'' s).
Proof.
intros q a s Hmon Hall.
case (classic (forall s' : CoList, sin s' q -> les s' bot)) ; intros Hcas.
*
  left.
  intros s' Hin.
  specialize (Hcas _ Hin).
  inversion Hcas ; auto.
*
  right.
  apply not_all_ex_not in Hcas.
  destruct Hcas as (s' & Hn).
  apply imply_to_and  in Hn.
 destruct Hn as (Hin & Hnle).
  exists s'.
  destruct s'.   
  +
    exfalso ; apply Hnle ; constructor.
  +
    exfalso.
    specialize (Hall _ Hin).
    inversion Hall.
 + 
   specialize (Hall _ Hin).
   inversion Hall; subst.
   exists s'; repeat split ; auto.
Qed.


Lemma lim_lower_aux3{A : Type}  : forall  (q : Seq (A := CoList(A:= A))),
increasing les q ->
    forall a s, 
      sin (scons a s) q ->
         exists i, forall j, ((i <= j -> exists s'',  q j= scons a s'')  /\ (j < i -> q j= bot)  ) .

Proof.
intros q Hmon a s Hin.  
assert (Hin' : exists i s, q i  = scons a s).
{
  destruct Hin as (i & Heq).
  now exists i, s.  
}  
clear Hin.
destruct (nonempty_inf _ _  lt_wf _ Hin') as (i & Hi).
clear Hin' s.
destruct Hi as ((s & Heq ) &Hall).
assert (Hall' : forall b,  b < i  -> forall s, q b <> scons a s).
{
  intros b Hbi s' Heq'.
  apply (Hall b); auto.
  now exists s'.
}
clear Hall.
exists i.
intros j .
split ; intro Hcas.
*
  clear Hall'.
  eapply increasing_gen with (m := i) (n := j) in Hmon ; [| lia].
  rewrite Heq in Hmon.
  inversion Hmon ; subst.
  now exists s2.
*
  specialize (Hall' _ Hcas).
  eapply increasing_gen with (m := j) (n := i) in Hmon ; [| lia].
  rewrite Heq in Hmon.
  inversion Hmon; subst; auto.
  exfalso.
  apply (Hall' s1).
  rewrite H; auto.
Qed.

Lemma lim_lower{A: Type} :  forall  (q : Seq (A := CoList(A:= A)))
  (Hm : increasing les q),
     forall sup',  (forall s',  sin s' q -> les s' sup') ->  les  (lim q Hm) sup'.
Proof.
cofix lim_lower.
intros q Hm sup' Hall.
destruct sup'.
*
  rewrite lim_eta_bot.
  +
    apply les_refl.
  +
    intros s Hin.
    specialize (Hall _ Hin).
    inversion Hall ; auto.    
*  
  apply lim_lower_aux1 in Hall; auto.
  destruct Hall as [Hall | Hall]. 
  +
    rewrite lim_eta_bot.
    -
      constructor.
    -
      intros s Hin.
      apply Hall ; auto.
  +
    destruct Hall as (s & Hin & Heq).
    rewrite Heq in Hin.
    rewrite lim_eta_snil ; auto.
    apply les_refl.    
 *
  generalize Hall ; intro Hall'.
  apply lim_lower_aux2 in Hall ; [| apply Hm].
  destruct Hall as [Hall | Hall]. 
  +
    rewrite lim_eta_bot.
    -
      constructor.
    -
      intros s Hin.
      apply Hall ; auto.
  +
    destruct Hall as (s & s' & Hin & Heq & Hle).
    rewrite Heq in *.
    clear Heq.
    erewrite lim_eta_scons ; eauto.
    constructor.
    clear s.
    eapply lim_lower ; eauto.
    clear lim_lower.
    intros s Hin'.
    generalize Hin ; intro Hin''.
    apply lim_lower_aux3 in Hin ; [| apply Hm].
    destruct Hin as (fbn & Hfnb).
    destruct Hin' as (i & Heq).
    case  (le_lt_dec fbn i) ; intros Hcas.
    -
      destruct  (Hfnb  i) as (Hc & _).
      destruct (Hc Hcas) as (s'' & Heq'').
      specialize (Hall' _ (sin_nth q i)).
      rewrite Heq'' in Hall'.
      inversion Hall'; subst.        
      now rewrite Heq''.
    -
      destruct  (Hfnb  i) as (_ & Hb).
      specialize (Hb Hcas).
      rewrite Heq, Hb.
      constructor.        
Qed.

   

Lemma les_sup{A: Type} :
  forall (q: Seq (A := CoList(A:= A)) ), increasing les q -> exists b, sup les b q.
Proof.
intros s Hs.
exists (lim _ Hs).
split.
*
  apply lim_upper.
*
  apply lim_lower.
Qed.


CoInductive bisim{A: Type} : CoList(A := A) -> CoList (A := A) -> Prop :=
|bisim_bot : bisim bot bot
|bisim_snil : bisim snil snil                   
|bisim_scons : forall a1 a2  s1 s2,  a1 = a2 -> bisim s1 s2 -> bisim (scons a1 s1) (scons a2 s2).      


Lemma les_antisym{A: Type} :
  forall (s1 s2:  CoList (A:= A)), les s1 s2 -> les s2 s1 -> bisim s1 s2.
Proof.                                                           
cofix les_antisym.
intros s1 s2 Hle1 Hle2.
inversion Hle1; subst; clear Hle1 ;  inversion Hle2; subst; clear Hle2;
  try constructor; try reflexivity.
apply les_antisym ; auto.
Qed.

 Definition les_omega_cpo {A: Type} : cpo (A:= CoList(A:= A)) bisim les :=
  {|
  bbot := bot;
  bbot_is_bottom := les_bot;
  bprefl := les_refl;
  bptrans := les_trans ;
  bpantisym := les_antisym;
  bpsup := les_sup
  |}.



Inductive lts{A : Type} : CoList(A := A)  -> CoList(A :=  A)  ->  Prop :=
|lts_now : forall s,  s <> bot -> lts bot s   
|lts_later : forall a s1 s2,  lts s1 s2 -> lts (scons a s1) (scons a s2).



CoInductive sdefined{A: Type} : CoList(A:= A) -> Prop :=
|sdefined_snil  : sdefined snil  
|sdefined_scons : forall a s,  sdefined s -> sdefined (scons a s).


Lemma sdefined_les_mono{A: Type} : forall (s s' :  CoList(A:= A) ),  sdefined s -> les s s' -> sdefined s'. 
Proof.
cofix sdefined_les_mono.
intros s s' Hsd Hle.
inversion Hle; subst; clear Hle; auto.
*
  inversion Hsd .
*
  constructor.  
  inversion Hsd ; subst ; clear Hsd.
  eapply sdefined_les_mono ; eauto.
Qed.

Lemma sdefined_les_bisim{A: Type} : forall (s s' :  CoList(A:= A) ),  sdefined s -> les s s' -> bisim s s'. 
Proof.
cofix sdefined_les_bisim.
intros s s' Hsd Hle.
inversion Hle; subst; clear Hle.
*
  inversion Hsd ; subst ; clear Hsd.
*
  constructor.
*
  inversion Hsd ; subst ; clear Hsd.
  constructor; auto.
Qed.
