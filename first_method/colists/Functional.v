Require Import Sequences.
Require Import CoList.
Require Import TypeDecl.

Module DefinednessMod (TD : TypeDecl).
Import TD.

Definition CoList := CoList (A :=  A).



Inductive defined_upto: nat -> CoList-> Prop :=
|all_upto_0 : forall s,  defined_upto 0 s  
|snil_upto_1 :   defined_upto 1 snil
|scons_upto_S : forall n s a,  defined_upto n s -> defined_upto (S n)(scons a s).



Lemma defined_upto_mono : forall s1 s2 n,defined_upto n s1 -> les s1 s2 -> defined_upto n s2.
Proof.
intros s1 s2 n Hd.  
revert s2.
induction Hd; intros s2 Hle.
*
  constructor.
*
  inversion Hle; subst.
  constructor 2.
*  
  inversion Hle ; subst.
  constructor.
  apply IHHd; auto.
Qed.


Lemma defined_upto_lts_mono : forall s1 s2 n,defined_upto n s1 -> lts s1 s2 -> defined_upto (S n)  s2.
Proof.
intros s1 s2 n Hd.  
revert s2.
induction Hd; intros s2 Hle.
*
  inversion Hle; subst.
  +
    destruct s2; [exfalso ; apply H; auto|   constructor| do 2 constructor].
   + 
     do 2 constructor.
*
   inversion Hle.
 *
   inversion Hle; subst.
   constructor.
   apply IHHd  ; auto.
Qed.

Section Functional.

Variable T : Type.

Variable D : T  -> Prop.

Definition lef (f1 f2 : T -> CoList) := forall s,  les (f1 s) (f2 s). 


Variable  F : (T -> CoList) -> T -> CoList.
Hypothesis F_mono :  forall f1 f2, lef f1 f2-> lef (F f1)(F f2).

Fixpoint _f (n : nat)(t : T) : CoList:=
  match n with
  | 0 =>  bot
  | S m =>  F ( _f m) t
end.



Definition _f_seq (t: T) :  Seq (A := CoList) :=
    (fun n => _f n t).


Lemma  _f_seq_mono :  forall n s, les ((_f_seq s) n) ((_f_seq s) (S n)).
Proof.
intros n  s.
unfold _f_seq.  
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


Lemma  _f_seq_mono_gen :
  forall n n' s, n <= n' -> les ((_f_seq s) n) ((_f_seq s) n').
Proof.
intros n  n' s Hle.
induction Hle.
*
  apply les_refl.
*
  eapply les_trans ; eauto.
  apply _f_seq_mono.
Qed.

End Functional.

End DefinednessMod.


Module Type FunctionalMod(TD: TypeDecl).

Import TD.
Module DTD :=  (DefinednessMod TD).
Export DTD.

Parameter T : Type.
Parameter  D : T  -> Prop.

Parameter F : (T-> CoList) ->  T-> CoList.

Axiom F_mono : forall f1 f2, lef T f1 f2-> lef T  (F f1)(F f2).

Axiom F_prod  :
  forall t, D t ->   (exists n,  sdefined (F (_f T F n)  t))  \/ forall m,  exists n, m <= n /\ lts (_f T F n  t) (_f  T F (S n) t).

End FunctionalMod.

