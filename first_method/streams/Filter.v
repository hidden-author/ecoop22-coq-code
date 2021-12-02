Require Import TypeDecl.
Require Import Sequences.
Require Import Flat.
Require Import MyStreams.
Require Import Functional.
Require Import FunctionDefinition.
Require Import Lia.
Require Import List.
Import ListNotations.


Module NatType <: TypeDecl.

Definition A := nat.

End NatType.

Module FilterFunctional <: FunctionalMod NatType.

Import NatType.
Module DTD :=  (DefinednessMod NatType).
Import DTD.


Parameter p : A -> bool.

Definition nth := MyStreams.nth(A := option A).
Definition firstn := MyStreams.firstn(A := option A).
Definition hd := MyStreams.hd(A := option A).
Definition tl := MyStreams.tl(A := option A).
Definition scons := MyStreams.scons(A := option A).

Definition P : option A -> bool :=
  fun o =>  match o with (Some a) => p a | _ => false end.

Definition infp (s :  StreamO ) := forall n, exists N , n <= N /\ P (nth s N) = true.

Lemma tl_preserves_infp : forall s, infp s -> infp (tl s).
Proof.
  intros s Hi n.
  unfold infp in Hi.
  destruct  (Hi (S n)) as (N & Hle & Hp).
  exists (pred N); split; try lia.
  destruct N; try lia.
  rewrite <- pred_Sn.
  destruct s; auto.
Qed.  
   
Definition T := { s : StreamO |  infp s}.

Definition head(t: T) := hd (proj1_sig t).

Definition tail (t: T) : T := exist _ (tl (proj1_sig t)) (tl_preserves_infp _  (proj2_sig t)).


Definition F(f : T -> StreamO) (s: T): StreamO :=
  if P (head s)
then
scons (head s) (f (tail s))
else f (tail s).


Lemma F_mono :  forall f1 f2, lef T  f1 f2 -> lef T (F f1) (F f2).
Proof.
intros f1 f2 Hle s.
destruct s ; destruct x.
case_eq (P o); intros Hcas.
*
  unfold F.
  cbn.
  rewrite Hcas.
  constructor.
  +
    apply leo_refl.
  +
    apply Hle.
*  
  unfold F.
  cbn.
  rewrite Hcas.
  apply Hle.
Qed.

Fixpoint sapp (l : list (option A) ) (s : StreamO) : StreamO :=
  match l with
    [] => s
  | cons  a l' => scons a(sapp l' s)
  end.                     

            
Fixpoint lfilter (l : list (option A)) : list (option A)  :=
  match l with
    [] => []
  |a :: l' => if P a then a  :: lfilter l' else lfilter l'
  end.   
                                                              

Lemma _f_form : forall n s ,   _f T F n s =  sapp (lfilter (firstn n (proj1_sig s)))  bot.
Proof.
induction n ; intros s ; auto.
destruct s.
destruct x .
unfold F.
cbn.
case_eq (P o) ; intro Hcas.
*
  cbn.
  f_equal.
  apply IHn ; auto.
*
  cbn.
  apply IHn ; auto.
Qed.

Lemma F_prod_aux : forall n s, 
P (nth s n) = true
->
  lts (sapp (lfilter (firstn n s)) bot)
    (sapp (lfilter (firstn (S n) s)) bot).
Proof.
induction n; intros s  Hp; destruct s;  cbn in *.
*
  rewrite Hp.
  cbn.
  rewrite bot_eta at 1.
  destruct o; try constructor.
  inversion Hp.
*
  destruct o.
  +
    cbn.  
    remember (p a) as pa.
    destruct pa.
    -
      constructor.
      fold sapp.
      apply IHn; auto.     
    -
      apply IHn; auto.
 +
   cbn.
   apply IHn ; auto.
Qed.   

Lemma F_prod  : forall s m, exists n, m <= n /\  lts (_f T F n  s) (_f T F (S n) s).
Proof.  
  intros s m.
  destruct s.
  unfold infp in i.
  destruct (i m)  as (n & Hle & Hp).
exists n ; split ; auto.
do 2 rewrite _f_form.
apply F_prod_aux; auto.
Qed.

End FilterFunctional.  

Import FilterFunctional.  


Module filter_def :=
  FunctionDefinitionMod NatType FilterFunctional.

Import filter_def.

Definition filter := f.

Theorem filter_fix :  forall   s,  
                                   bisim
                                     (filter s)
                                     (if P (head s)
                                      then
                                        scons (head s) (filter(tail s))
                                      else filter(tail s)).
Proof.
  intros s.
  apply f_fix.
Qed.


(*    -> forall s,  bisim  (f s) (f' s).*)
Theorem filter_fix_unique :
  forall f',
    (forall s,  bisim (f' s) (F f' s)) ->
    forall s,
      bisim  (filter s) (f' s).                               
  intros.
  apply f_unique_fix; auto.
Qed.



