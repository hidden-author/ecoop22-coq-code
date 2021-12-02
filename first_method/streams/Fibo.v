Require Import FunctionalExtensionality.
Require Import TypeDecl.
Require Import Sequences.
Require Import Flat.
Require Import MyStreams.
Require Import Functional.
Require Import FunctionDefinition.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Arith.Compare_dec.

Module NatType <: TypeDecl.

  Definition A := nat.

End NatType.


Import NatType.


Module FiboFunctional <: FunctionalMod NatType.

Import NatType.

Definition nth := MyStreams.nth(A := option nat).
Module DTD :=  (DefinednessMod NatType).
Import DTD.

Definition T := unit.

(*
Definition  D : T  -> Prop := fun _ => True.
*)
CoFixpoint ssum (s1 s2 : Stream) : Stream :=
match s1, s2 with
  scons o1 s'1, scons o2 s'2 =>
  match o1, o2 with
    Some n1, Some n2 => scons (Some (n1 + n2)) (ssum s'1 s'2)
    | _, _=> bot                         
  end  
end.

Lemma ssum_eta : forall s1 s2,
ssum s1 s2 =
match s1, s2 with
  scons o1 s'1, scons o2 s'2 =>
  match o1, o2 with
    Some n1, Some n2 => scons (Some (n1 + n2)) (ssum s'1 s'2)
    | _, _=> bot                         
  end  
end.
Proof.
intros s1 s2.
rewrite (stream_match (ssum s1 s2)).
destruct s1, s2.
destruct o, o0; try reflexivity.
* 
  rewrite bot_eta ; reflexivity.
*
  rewrite bot_eta ; reflexivity.
*
  rewrite bot_eta ; reflexivity.
Qed.


Definition F(f : T -> StreamO) (_: T): StreamO :=
  scons (Some 0) (ssum (f tt) (scons (Some 1) (f tt))).
  
  
Lemma les_mono : forall s1 s2 s'1 s'2,
    les s1 s'1 -> les s2 s'2 ->  les (ssum  s1 s2 ) (ssum s'1 s'2).
Proof.
cofix les_mono.
intros s1 s2 s'1 s'2 Hle1 Hle2.
inversion Hle1; inversion Hle2 ; subst.
inversion H  ; inversion H3 ; subst.
* 
  rewrite ssum_eta.
  apply bot_is_bottom.
*
  rewrite ssum_eta.
  apply bot_is_bottom.
*
  rewrite ssum_eta.
  apply bot_is_bottom.
*
  rewrite ssum_eta.
  replace ((ssum (scons (Some a) s3) (scons (Some a4) s5))) with
      (scons (Some (a + a4)) (ssum s3 s5)).
  +
    constructor.
    -
      apply leo_refl.
    -
      eapply les_mono ; eauto.
  +
    symmetry.
    rewrite ssum_eta; auto.
Qed.    


Lemma F_mono :  forall f1 f2, lef T  f1 f2 -> lef T (F f1) (F f2).
Proof.
intros f1 f2 Hle s.
destruct s.
unfold F.
constructor.
*
  apply leo_refl.
*
  eapply les_mono ; eauto.
  constructor.
  +
    apply leo_refl.
  +
    apply Hle.
Qed.

Lemma nat_ind2 (P : nat -> Prop) :
P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) ->
forall n, P n.
Proof.
intros H0 H1 Hstep n.
assert (P n /\ P (S n)); [ | tauto].
induction n as [ | n IH]; [tauto | ].
split; [tauto | ].
apply Hstep; tauto.
Qed.

Fixpoint firstn (n: nat)(s: StreamO) : list (option A) :=
  match n, s with
    0,  _ => []
  |S m, scons o s' => cons o (firstn m s')
  end.                     

Fixpoint lsum (l1 l2 : list (option A))  :=
match l1, l2 with
  cons o1 s'1, cons o2 s'2 =>
  match o1, o2 with
    Some n1, Some n2 => cons (Some (n1 + n2)) (lsum s'1 s'2)
    | _, _=> cons None (lsum s'1 s'2)                      
  end
 | [], l => [] 
 | l, [] => []
end.           

Fixpoint lfibo (n : nat) : list (option A)  :=
  match n with
    0 => []
  |S m =>
   match m with
     0 =>[Some 0]
   | S k  => cons(Some 0) (lsum (lfibo m)  (cons (Some 1) (lfibo k)))
   end              
  end.
  
 
Lemma lfibo_ssn : forall n,
    lfibo (S (S n)) = cons(Some 0) (lsum (lfibo (S n))  (cons (Some 1) (lfibo n))).
Proof.  
intro n; reflexivity.
Qed.

Fixpoint sapp (l : list (option A) ) (s : StreamO) : StreamO :=
  match l with
    [] => s
  | cons  a l' => scons a(sapp l' s)
  end.                     


Fixpoint fibo (n : nat) : nat  :=
  match n with
    0 => 0
  |S m =>
   match m with
     0 =>  1 
   | S k  => fibo m + fibo k
   end              
  end.


Lemma fibo_ssn : forall n,
    fibo (S (S n)) = fibo (S n) + fibo n.
Proof.  
intro n; reflexivity.
Qed.

Lemma ssum_sapp_lsum :
    forall (l1 l2 : list (option A)),
      (forall x,  In x l1 -> x<> None) ->
      (forall x,  In x l2 -> x<> None) ->
    ssum (sapp l1  bot)
              (sapp l2  bot)  =
  sapp (lsum l1 l2) bot.
Proof.  
induction l1; intros l2 Hall1 Hall2.
* 
  cbn.
  rewrite bot_eta at 1.
  destruct l2.
  +
    cbn.
    rewrite bot_eta at 1.
    rewrite ssum_eta ; auto.
  +
    cbn.
    rewrite ssum_eta  ; auto.
*
  destruct l2.
  +
    cbn.
    rewrite bot_eta at 2.
    rewrite ssum_eta.
    destruct a ; auto.
  +
    destruct a, o.
    - 
      cbn[sapp].
      rewrite ssum_eta.
      cbn [lsum sapp].
      f_equal.
      apply IHl1; auto.
      **
        intros x Hin Habs.
        apply (Hall1 x); auto.
        constructor 2; auto.
      **
        intros x Hin Habs.
        apply (Hall2 x); auto.
        constructor 2; auto.
   -
     exfalso.
     apply (Hall2 None); auto.
     constructor; auto.
  -
     exfalso.
     apply (Hall1 None); auto.
     constructor; auto.    
  -
    exfalso.
    apply (Hall1 None); auto.
     constructor; auto.     
Qed.



Lemma lsum_Some :  forall (l1 l2 : list (option A)),
      (forall x,  In x l1 -> x<> None) ->
      (forall x,  In x l2 -> x<> None) ->
      forall x, In x (lsum l1 l2) -> x <> None.
Proof.
induction l1; intros l2 Hall1 Hall2 x Hin.
*
  intro Habs.
  rewrite Habs in Hin.
  inversion Hin.
*
 destruct l2.
 +
  inversion Hin. 
 +   
   destruct a, o.
   -
     inversion Hin; [intro Habs; rewrite Habs in * ; discriminate |].
     
     apply IHl1 with (l2 := l2); auto.
     **
       intros y Hiny Habsy.
       apply (Hall1 y); auto.
       rewrite Habsy in *.     
       constructor 2; auto.
     **
       intros y Hiny Habsy.
       apply (Hall2 y); auto.
       rewrite Habsy in *.     
       constructor 2; auto.
   -
    exfalso.
    apply (Hall2 None); constructor ; auto.
   -  
     exfalso.
    apply (Hall1 None); constructor ; auto.
   -  
     exfalso.
    apply (Hall1 None); constructor ; auto.
Qed.


Lemma  _f_form_aux' : forall n o, In o (lfibo n) -> o <> None.
Proof.
induction n as [ | | n IHn IHSn] using nat_ind2; intros o Hin.
*
  inversion Hin.
*
  cbn in Hin.
  destruct Hin ; intuition ; rewrite H0 in * ; discriminate.
*
  rewrite lfibo_ssn in Hin.
  inversion Hin ; subst; clear Hin.
  +
    intro ; discriminate.
  +
    intro Habs ; rewrite Habs in *.
    apply  lsum_Some in H; auto.
    intros x Hin Habs' ; rewrite Habs' in *.
    inversion Hin; try discriminate.
    apply (IHn _ H0); auto.
Qed.
    
Lemma lts_sapp_app :
  forall( l : list (option A))  (a: A),
    (forall x,  In x l -> x <> None) ->
    lts (sapp l bot) (sapp ( l ++  [Some a]) bot).
Proof.
induction l; intros a' Hall.
*
  cbn.
  rewrite bot_eta at 1.
  constructor.
*
  cbn.
  destruct a.
  +
    constructor.
    eapply IHl ; eauto.
    intros x Hin.
    apply Hall.
    constructor 2; auto.
  +
    exfalso.
    apply (Hall None) ; auto.
    constructor 1 ; auto.
Qed.

Lemma eqlist  : forall (l1 l2 : list (option A)),
    length l1 = length l2 -> (forall i,  i < length l1 -> List.nth i l1 None = List.nth i l2 None)
    -> l1 = l2.
Proof.                                                                                                                     
induction l1; intros l2 Heql Hall.
*
  destruct l2 ; auto.
  discriminate.
*
   destruct l2 ; try discriminate.  
   f_equal.
  +
    apply (Hall 0).
    cbn ; lia.
  +
    erewrite IHl1 ; eauto.
    intros i Hlt.
    apply (Hall (S i)).
    cbn ; lia.
Qed.

Lemma length_lsum :
  forall l1 l2,  length l1 = length l2 ->
                  (forall x,  In x l1 -> x<> None) ->
                  (forall x,  In x l2 -> x<> None) ->
                  length (lsum l1 l2) = length l1.
Proof.
induction l1; intros l2 Heq Hall1 Hall2.
*
  destruct l2; try discriminate ; auto.
*
  destruct l2; try discriminate.
  cbn in Heq.
  destruct  a, o.
  +
    cbn.
    rewrite IHl1; auto.
    -
      intros x Hin.
      apply (Hall1 x).
      constructor 2 ; auto.
   -
     intros x Hin.
      apply (Hall2 x).
      constructor 2 ; auto.
  +     
    exfalso.
    eapply Hall2 ; eauto.
    constructor; auto.   
  +     
    exfalso.
    eapply Hall1 ; eauto.
    constructor; auto.   
  +     
    exfalso.
    eapply Hall1 ; eauto.
    constructor; auto.   
Qed.  
   

Lemma nth_lsum :
  forall l1 l2,  length l1 = length l2 ->
                  (forall x,  In x l1 -> x<> None) ->
                  (forall x,  In x l2 -> x<> None) ->
                  forall i a1 a2, i < length l1 ->
                       List.nth i l1 None = Some a1  -> List.nth i l2 None = Some a2->
                   List.nth i (lsum l1 l2)  None =Some (a1 + a2).
Proof.
induction l1; intros l2 Heq Hall1 Hall2 i a1 a2 Hlt Heq1 Heq2.
*
  inversion Hlt.
*
 destruct l2.  
+
  destruct i ; discriminate.
+
  destruct i.
  -
    destruct a, o; try discriminate.
    cbn in *.
    injection Heq1; intros ; subst.
    injection Heq2; intros ; subst ; auto.
  - 
      destruct a, o.
      **
        cbn in *.
        eapply IHl1; eauto ; lia.
      **
        cbn in *.
        eapply IHl1; eauto ; lia.
      **
         cbn in *.
         eapply IHl1; eauto ; lia.
      **
         cbn in *.
         eapply IHl1; eauto ; lia.
Qed.


Fixpoint fibol (n : nat) : list (option nat) :=
  match n  with
    0 => []
   |S k => fibol k ++ [Some (fibo k)]
  end.
                   
Lemma fibol_sn : forall n,  fibol (S n) = fibol n ++ [Some (fibo n)].
Proof.
intro ; reflexivity.
Qed.

Lemma fibol_length : forall n, length (fibol n) = n.
Proof.
induction n; auto.
rewrite fibol_sn.
rewrite app_length.
rewrite IHn ; cbn ; lia.
Qed.


Lemma fibol_last : forall n,  List.nth n (fibol (S n)) None =  Some (fibo n).
Proof.
induction n ; auto.
rewrite fibol_sn in *.
erewrite <- nth_middle  with (l' := []) (l:= fibol (S n)) (d := None); eauto.
f_equal.
rewrite fibol_length ; auto.
Qed.


Lemma fibol_fibo : forall n i ,  i <  n -> List.nth i (fibol n) None = Some (fibo i).
Proof.
induction n.
*
  intros i Hlt ; lia.
*
  intros i Hlt.
  destruct (le_lt_eq_dec _ _ Hlt).
 +
   rewrite fibol_sn.
   rewrite app_nth1.
   -
     eapply IHn; eauto ; lia.
  -
    rewrite fibol_length ; lia.
 + 
   injection e ; intros ; subst.
   apply fibol_last.   
Qed.



Lemma lfibo_length : forall n, length (lfibo n) = n.
Proof.
induction n as [ | | n IHn IHSn] using nat_ind2; [reflexivity | auto | ].
rewrite lfibo_ssn.
cbn [length].
f_equal.
rewrite length_lsum; auto.
* 
  cbn [length].
  rewrite IHn, IHSn ; auto.
*
  intros x Hin.
  eapply _f_form_aux' ; eauto.
*  
  intros x Hin.
  inversion Hin.
  +
    rewrite <- H ; intro ; discriminate.
  +
    eapply _f_form_aux' ; eauto.
Qed.




Lemma lfibo_fibo : forall n i ,  i <  n -> List.nth i (lfibo n) None = Some (fibo i).
Proof.
  intros n i ; revert n;
  induction i as [ | | i IHi IHSu] using nat_ind2; intros n Hlt.
*
 cbn.
 destruct n; try lia.
destruct n ; auto.
*
  destruct n ; try lia.
  destruct n ; try lia.
  destruct n ; auto.  
*
  do 2 (destruct n ; try lia).
  rewrite lfibo_ssn.
  cbn [List.nth].
  erewrite nth_lsum
    with (a1 := fibo (S i))(a2 := fibo i) ; auto.
  +
    cbn [length].
    do 2 rewrite lfibo_length ; auto.
  +
    eapply _f_form_aux' ; eauto.
  +
    intros x Hin.
    inversion Hin.
     -
       rewrite <- H ; intro ; discriminate.
    -
      eapply _f_form_aux' ; eauto.
  +
    rewrite lfibo_length ; lia.
  +
    eapply IHSu; lia.
  +
    cbn.
    eapply IHi; lia.
Qed.
    
Lemma lfibo_fibol : forall n,  lfibo n = fibol n.
Proof.
 intro n.
eapply eqlist ; eauto.
* 
  rewrite lfibo_length, fibol_length; auto.
*
  intro i .
  rewrite lfibo_length.
  intro Hlt.
  rewrite  lfibo_fibo; auto.
  rewrite fibol_fibo ; auto.  
Qed.


Lemma lsum_cons_Some_r (l : list (option nat)) (o : option nat) :
lsum l (o :: l) = lsum l (o :: removelast l).
Proof.
revert o.
induction l as [ | o' l IH]; intros o; trivial.
cbn [lsum].
rewrite IH.
destruct l; reflexivity.
Qed.

Lemma removelast_app  (A : Type) (l : list A) (x y : A) : removelast (l ++ [x]) = l.
Proof.
induction l ; auto.
remember (l++ [x]) as lpx.
destruct lpx.
*
  exfalso.
  eapply app_cons_not_nil; eauto.
*
  cbn.
   rewrite <- Heqlpx.
   f_equal ; auto.
Qed.
   
Lemma removelast_lfibo (n : nat) : removelast (lfibo (S n)) = lfibo n.
Proof.
do 2 rewrite lfibo_fibol.
rewrite fibol_sn.
rewrite removelast_app; auto.
exact (Some 0).
Qed.

  
 Lemma  _f_form_aux : forall n,
 ssum (sapp (lfibo (S n)) bot)  (scons (Some 1) (sapp (lfibo (S n)) bot)) =
 sapp (lsum (lfibo (S n)) (Some 1 :: lfibo(S  n))) bot.
Proof.
intro n.
replace  (scons (Some 1) (sapp (lfibo (S n)) bot)) with (sapp (cons (Some 1) (lfibo (S n))) bot) ; auto.
rewrite  ssum_sapp_lsum ; auto.
*
 intro x.
 apply _f_form_aux'.
*
 intros x Hin Habs.
 rewrite Habs in *. 
 inversion Hin ; try discriminate.
 apply _f_form_aux' in H; apply H ; auto.
Qed.


Lemma _f_form : forall n ,   _f T F n tt = sapp (lfibo n) bot.
Proof.
intro n.
enough (_f T F n = fun _ => sapp (lfibo n) bot) by now rewrite H.
induction n as [ | | n IHn IHSn] using nat_ind2; [reflexivity | | ].
- cbn.
  unfold F.
  rewrite ssum_eta.
  reflexivity.
- cbn [_f] in IHSn |- *.
  rewrite IHn in IHSn |- *.
  extensionality t.
  assert (IHSn2 := f_equal (fun f => f t) IHSn).
  cbn beta in IHSn2.
  unfold F in IHSn2 |- *.
  rewrite IHSn2.
  rewrite lfibo_ssn.
  cbn [sapp].
  f_equal.
  rewrite _f_form_aux.
  clear.
  rewrite lsum_cons_Some_r , removelast_lfibo ; auto.
Qed.


Lemma lts_fibo : forall n, lts (sapp (lfibo n) bot) (sapp (lfibo (S n)) bot).
Proof.
intro n.
do 2 rewrite lfibo_fibol.
apply lts_sapp_app.
rewrite <- lfibo_fibol.
apply  _f_form_aux'.
Qed.

Lemma F_prod  : forall s m, exists n, m <= n /\  lts (_f T F n  s) (_f T F (S n) s).
Proof.  
intros s m.
destruct s.  
exists m  ; split ; auto.
do 2 rewrite _f_form.
apply  lts_fibo.
Qed.


End FiboFunctional.  

Import FiboFunctional.  


Module fibo_def :=
  FunctionDefinitionMod NatType FiboFunctional.

Import fibo_def.

Definition fibo := f.

Theorem fix_fibo :
  bisim (fibo tt)
             (scons (Some 0)
                    (ssum
                       (fibo tt)
                       (scons (Some 1)
                              (fibo tt)))).
Proof.
eapply f_fix ; eauto.
Qed.


Lemma fibo_unique_fix : forall f',
    (forall s',  bisim (f' s') (F f' s')) ->
      forall s,  bisim  (fibo s) (f' s).
Proof.
  intros f' Hall s.
  apply f_unique_fix ; auto.
Qed.
