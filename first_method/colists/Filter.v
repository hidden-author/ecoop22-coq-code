Require Import TypeDecl.
Require Import Sequences.
Require Import CoList.
Require Import Functional.
Require Import FuncDef.
Require Import WfInf.
Require Import  Wf_nat.
Require Import Lia.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Compare_dec.

Module NatType <: TypeDecl.

Definition A := nat.

End NatType.

Module FilterFunctional <: FunctionalMod NatType.

Import NatType.
Module DTD :=  (DefinednessMod NatType).
Import DTD.


Parameter p : A -> bool.

Definition P (o : option (option A)) : bool :=
  match o with
    Some o' =>
    match o' with
      Some a => p a
     |None => false             
    end
  |None => false
  end.

Lemma P_true : forall o,  P o = true -> exists a,  o = Some (Some a) /\ p a = true.
Proof.
intros o Hp.
do 2 (destruct o ; try discriminate).
now exists a.
Qed.
     
Definition nth := CoList.nth(A := A).
Definition hd := CoList.hd(A := A).
Definition tl := CoList.tl(A := A).

Definition T := CoList.

Definition D := sdefined (A := A).


Definition  max_true_or_zero (s: CoList) :
  (exists  n,  forall m,  n <= m  ->  P (nth  m s) = false) ->
  {n : nat |   ( n > 0 /\ P (nth (pred n) s ) = true \/  n = 0)  /\ forall m, n<= m ->  P (nth  m  s) = false }.
Proof.
intros Hex.
apply constructive_indefinite_description.
generalize  (nonempty_inf _ _ lt_wf   (fun n =>(  forall m : nat,
                                                   n <= m -> P (nth m s) = false)) Hex); intro Hex'.
clear Hex.
destruct Hex' as (x & (Hx & Hy)).
exists x ; repeat split ; auto.
destruct x.
* 
  right; split ; auto.
*
  left; split ; try lia.
  cbn [pred].
  specialize (Hy x).
  assert (Hn : ~ ( (forall m : nat,
         x <= m ->
        P (nth m s) = false) )).
   {
     intro Hn'.
     apply Hy; auto.
   }
   clear Hy.
   apply not_all_ex_not in Hn.
   destruct Hn as (n & Hn).
   apply  imply_to_and  in Hn.
   destruct Hn as (Hle & Hp).
   inversion Hle ; subst.
   +
     destruct (P (nth n s))  ; auto.
   +  
     exfalso.
     rewrite Hx in Hp; try lia.
Qed.

Inductive List : Type :=
| lbot  : List  
| lnil :  List
|lcons : A -> List -> List.
                        

Fixpoint sapp (l : List) (s : CoList) : CoList :=
  match l with
    lbot => bot
    |lnil => s
    | lcons  a l' => scons a(sapp l' s)
  end.                     


Fixpoint firstn(n : nat) (s: T) : List :=
  match n, s with
  | _, bot  => lbot
  | _,  snil => lnil
  | 0, _ => lnil
  |S m, scons a s'  => lcons a (firstn m s')
  end .


Fixpoint lfilter (l : List) : List  :=
  match l with
    | lbot => lbot
    | lnil => lnil
    | lcons a l' => if  p a then lcons a  (lfilter l') else lfilter l'
  end.   


 Definition F(f : T -> CoList) (s: T): CoList :=
  if (orbool_dec (forall m,  P (nth m s) = false))
  then  snil
  else
     match  s  with
       scons a s' => 
       if p a  then  scons a  (f s') else f s'
     | _ => bot
   end .   

Lemma F_mono :  forall f1 f2, lef T  f1 f2 -> lef T (F f1) (F f2).
Proof.
intros f1 f2 Hle s.
unfold F.
remember (orbool_dec (forall m : nat, P (nth m s) = false) ) as d.
destruct d.
*
  apply les_refl.
*  
  destruct s ; cbn ; try constructor.
  destruct (p a).
  +
    constructor; apply Hle.
  +
      apply Hle.
Qed.


Definition D' : T  -> Prop :=
 fun s   => forall m, P  (nth m s) = false. 

Lemma F_if_DD' : forall s f,  D s -> D' s -> F f s = snil.
Proof.
intros s f HD HD'.     
unfold F.
remember (orbool_dec
            (forall m : nat, P (nth m s) = false)) as d.
destruct d ; auto.
exfalso.
apply n ; auto.
Qed.

Lemma _f_form1_aux1 :  forall s
         (Hd : sdefined s)
         (Hb :  (exists m,  forall n,  m <= n -> P (nth n s) = false)),
    proj1_sig (max_true_or_zero s Hb) = 0 -> forall n, P (nth n s) = false.
Proof.                                           
intros s Hded Hb Heq n.
remember (max_true_or_zero s Hb) as m.
destruct m as (n' & Hor & Hall).
cbn in Heq.
clear Heqm  Hor.
apply Hall ; lia.
Qed.

Lemma _f_form1_aux2 :  forall a s
         (Hd : sdefined s)
         (Hb :  (exists m,  forall n,  m <= n -> P (nth n (scons a s)) = false)) n,
    proj1_sig (max_true_or_zero (scons a s) Hb) = S n ->
    (
      (n = 0 /\  forall k,  P (nth  k s) = false) \/
      (n > 0 /\  exists Hb',  proj1_sig (max_true_or_zero s Hb') = n)).
Proof.
intros a s Hdef Hb n Heq.  
remember (max_true_or_zero (scons a s) Hb) as m.
destruct m as (n' & [(Hgt & Hp) | Hr] & Hall).
*
  cbn in Heq.
  clear Heqm.
  rewrite Heq in* ; clear Heq Hgt.
  destruct n.
  +
    left ; repeat split; auto.
    intro k ; apply (Hall (S k)); lia.
  +
    right; repeat split; auto; try lia.
    cbn in *.
    destruct Hb as (m & Hall').
     assert (Hall'' :  exists n0 : nat,
            forall m0 : nat,
            n0 <= m0 -> P (nth m0 s) = false).
     {
       exists (S m); intros m' Hle'.
       apply (Hall' (S m')); lia.
     }  
     exists Hall''.
     remember (max_true_or_zero s Hall'').
     destruct s0 as (n'' & [(Hgt & Hpg) | Hr]& Hall''') ; cbn.        
     ** 
       clear Heqs0.
       destruct n'' ; try lia.
       cbn in Hpg.
       f_equal.
       destruct (lt_eq_lt_dec n'' n) as [[Hlt | Heq] | Hgt']; auto; exfalso.
       ++
         rewrite Hall''' in Hp ; try lia.
       ++
         specialize (Hall (S n'')); cbn in Hall.
         rewrite Hall in Hpg; try lia.
     **
       clear Heqs0.
       rewrite Hr in *.
       exfalso.
       rewrite (Hall''' n) in Hp; try lia; discriminate.
  * cbn in Heq.
     lia.
Qed.
 
    
 Lemma _f_form1_sdef  :
  forall s
         (Hd : sdefined s)
         (Hb :  (exists m,  forall n,  m <= n -> P (nth n s) = false)),
    sdefined (F(_f T F ( proj1_sig (max_true_or_zero s Hb))) s).
Proof.
intros s Hdef  Hb.
remember  ( proj1_sig (max_true_or_zero s Hb))  as n.
revert s Hdef Hb Heqn.
induction n ; intros s Hdef  Hb Heqn.
*  
    inversion Hdef; subst.
  +
    cbn.
    rewrite  F_if_DD'; auto.
    intros m.
    unfold nth; rewrite nth_nil ; auto.
  +
    cbn.   
    symmetry in Heqn.
    generalize (_f_form1_aux1 _ Hdef Hb Heqn); intro Hall2.
    unfold F.
    remember (orbool_dec
        (forall m : nat,
            P (nth m (scons a s0)) = false))  as d.
    destruct d ;  try constructor.
    exfalso ; apply n ; auto.
*
  cbn.
  destruct Hb as (N & Hall).
  remember (fun t : T => F (_f T F n) t) as phi.
  unfold F.
  remember (orbool_dec
        (forall m0 : nat,
            P (nth m0 s) = false)) as d.
  destruct d.
  +
    constructor.
  +  
    inversion Hdef ; subst.
    -
      exfalso; apply n0 ; intro x.
      unfold nth ; rewrite nth_nil ; auto.
    -
      assert (Hd : (sdefined   (F (_f T F n) s0 ))).
      {
        symmetry in Heqn.
        apply  _f_form1_aux2 in Heqn; auto.
        destruct Heqn as [(Hn0 & Halp) |(HnS & Hex) ]; auto.
        *
          subst.
          cbn.
          unfold F.
          remember ( orbool_dec
                       (forall m0 : nat,
                           P (nth m0 s0) = false)) as d.
          destruct d ; auto.
          +
            constructor.
          +
            exfalso ; apply n ; auto.
       *
         destruct Hex as (Hb' & Hpre).
         symmetry in Hpre.
         eapply IHn; eauto.
       }
      destruct (p a); auto.
      constructor ; auto.
Qed.

Definition D'' : T  -> Prop :=
 fun s   => forall m, exists n , m <= n /\ P  (nth n s) = true. 


Lemma D''_sdefined : forall s,  D'' s -> exists a s',  s = scons a s' /\ D'' s'.
intros s Hd'.
unfold D'' in Hd'.
destruct s.
*
  exfalso.
  specialize (Hd' 0).
  destruct Hd' as (N & _ & HP).
  unfold nth in HP.
  rewrite nth_bot in HP.
  discriminate.
*
 exfalso.
  specialize (Hd' 0).
  destruct Hd' as (N & _ & HP).
  unfold nth in HP.
  rewrite nth_nil in HP.
  apply P_true in HP.
  destruct HP as (a & Heq & _).
  discriminate.
*
  generalize (Hd' 0) ; intro Hd.
  destruct Hd as (N & _ & HP).
  clear HP N.
  exists a, s  ; split ; auto.
  intros n.
  specialize (Hd' (S n)).
  destruct Hd' as (N & Hlt & Ht).
  destruct N ; try lia.
   exists N ; split; auto ; lia.  
Qed.

Lemma D''_nD'  : forall s,  D'' s -> ~ D' s.
Proof.
intros s HD'' HD'.
unfold D'' ,  D' in *.
specialize (HD'' 0).
destruct HD'' as (n & _ & Hp).
rewrite HD' in Hp; discriminate.
Qed.

Lemma D''_closed : forall a s,  D'' (scons a s) -> D'' s.
Proof.
unfold D'' in *.  
intros.
specialize (H (S m)).
destruct H as (n & Hle & Hp).
destruct n ; try lia.
cbn in Hp.
exists n; split; auto; lia.
Qed.

Lemma _f_form2  : forall n s ,  D s -> D'' s ->    _f T F n s =  sapp (lfilter (firstn n s))  bot.
Proof.
induction n ;  intros s Hd Hd'.
*
  cbn.
  destruct (D''_sdefined _ Hd') as (a & s' &  Heq & Hdef).
  rewrite Heq; auto.
*
  cbn [_f].
  remember (_f T F n) as phi.
  unfold F.
  remember (orbool_dec
              (forall m : nat, P (nth m s) = false)) as d.
  destruct d.
  +
    exfalso.
    apply D''_nD'  in Hd'.
    apply Hd'; auto.
  +
    inversion Hd; subst.
   -  
     exfalso.
     unfold D'' in Hd'.
     destruct (Hd' 0) as (x & _ & Hp).    
     unfold nth in Hp.
     rewrite nth_nil in Hp; discriminate.
   -
     cbn.
     remember (p a) as pa.
     destruct pa.
     **
       cbn.
       f_equal.
       eapply  IHn ; eauto.
       eapply D''_closed ; eauto.
    **   
      eapply IHn ; eauto.
      eapply D''_closed ; eauto.
Qed.


Lemma F_prod_aux : forall n s, 
P (nth n s) = true
->
  lts (sapp (lfilter (firstn n s)) bot)
    (sapp (lfilter (firstn (S n) s)) bot).
Proof.
induction n; intros s  Hp; destruct s;  cbn in * ; try discriminate.
*
  rewrite Hp.
  cbn.
  constructor.
  intro ; discriminate.
*
  remember (p a) as pa.
  destruct pa.
 +
   cbn.
   constructor.
   apply IHn ; auto.
 + 
   apply IHn ; auto.
Qed.


Lemma F_prod :
  forall t, D t ->
            (exists n,  sdefined (F (_f T F n)  t))  \/
            forall m,  exists n, m <=  n /\ lts (_f T F n  t) (_f  T F (S n) t).
Proof.
intros s Hd. 
destruct (classic (D'' s)).
*
  right.
  intro m.
  destruct (H m) as   (n & Hle & Hp).
  exists n ; split ; auto.
  rewrite _f_form2 ; auto.
  rewrite _f_form2; auto.
  apply F_prod_aux; auto.
*
  left.
  unfold D'' in H.
  assert (   Hb : exists m : nat,
            forall n : nat,
            m <= n -> P (nth n s) = false).
  {
    apply  not_all_ex_not in H.
    destruct H as (n & Hnex).
    exists n.
    intros m Hle.
    generalize (not_ex_all_not _ _ Hnex); intro Hnex' ; clear Hnex.
    specialize (Hnex' m).
    apply not_and_or in Hnex'.
    intuition.
    destruct ( P (nth m s) ); auto.
    exfalso ; apply H ; auto.               
   } 
  generalize (_f_form1_sdef _ Hd Hb); intro Hdef.
  firstorder.
Qed.

End FilterFunctional.  

Import FilterFunctional.  


Module filter_def :=
  FuncDefMod NatType FilterFunctional.

Import filter_def.

Definition filter := f.

Theorem filter_sdefined :   forall s,  sdefined s -> sdefined (filter s).
Proof.
intros s Hd.
apply f_sdefined ; auto.
Qed.

Theorem filter_fix :
  forall s,
    sdefined s ->
    bisim
      (filter s)
      (if (orbool_dec (forall m, P (nth m s) = false))
       then  snil
       else
         match s  with
           scons a s' => if p a  then  scons a  (filter s')  else  filter s'
         | _ => bot
         end).  
Proof.
intros s HD.
generalize (f_fix _ HD) ; intros; auto. 
Qed.
 



