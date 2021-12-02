Require Import Sequences.
Require Import MyStreams.
Require Import TypeDecl.

Module DefinednessMod (TD : TypeDecl).
Import TD.

Definition StreamO := Stream (A := option A).



Inductive defined_upto: nat -> StreamO -> Prop :=
|all_upto_0 :  forall s, defined_upto 0 s
|scons_upto_S : forall n s a,  defined_upto n s -> defined_upto (S n)(scons (Some a) s).



Lemma defined_upto_mono : forall s1 s2 n,defined_upto n s1 -> les s1 s2 -> defined_upto n s2.
Proof.
intros s1 s2 n Hd.  
revert s2.
induction Hd; intros s2 Hle.
* 
  constructor.
*
  inversion Hle; subst.
   inversion H1; subst.
   constructor 2.
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
    do 2 constructor.
   + 
     do 2 constructor.
 *
   inversion Hle; subst.
   constructor.
   inversion H2; subst.
   +
      inversion Hd; subst.
      do 2 constructor.
   +
     eapply IHHd.
     constructor; auto.
Qed.

Section Functional.

Variable T : Type.

Definition lef (f1 f2 : T -> StreamO) := forall s,  les (f1 s) (f2 s). 


Variable  F : (T -> StreamO) -> T -> StreamO.
Hypothesis F_mono :  forall f1 f2, lef f1 f2-> lef (F f1)(F f2).

Fixpoint _f (n : nat)(t : T) :  StreamO:=
  match n with
  | 0 =>  bot
  | S m =>  F ( _f m) t
end.



Definition _f_seq (t: T) :  Seq (A := StreamO) :=
  (fun n => _f n t).


Lemma  _f_seq_mono :  forall n s, les ((_f_seq s) n) ((_f_seq s) (S n) ).
Proof.
intros n  s.
unfold _f_seq.  
revert s.
induction n.
*
  intro s.
  apply bot_is_bottom.
*
  intro s.
  repeat rewrite snth_eq in *.
  revert s.
  apply F_mono.
  cbn.
  fold _f.
  intro s.
  specialize (IHn s).
   repeat rewrite snth_eq in IHn.
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

Parameter F : (T-> StreamO) ->  T-> StreamO.

Axiom F_mono : forall f1 f2, lef T f1 f2-> lef T  (F f1)(F f2).

Axiom F_prod  : forall t m, exists n, m <= n /\  lts (_f T F n  t) (_f  T F (S n) t).

End FunctionalMod.

