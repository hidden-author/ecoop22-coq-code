Require Import Sequences.
Require Import FiniteOrderMeasure.
Require Import CPO.

Module Type ProductiveFuncMod (C1 C2 : FiniteOrderMeasureMod).

Module Export CPO1 :=CPOMod C1.
Module Export CPO2 :=CPOMod C2.
 
Parameter fc : C1.Cc -> C2.Cc.

Parameter fc_mono :
  forall x y,  C1.ordc x y -> C2.ordc (fc x) (fc y).

Lemma increasing_image :
  forall q,  increasing C1.ordc q ->
               increasing  C2.ordc (fun n =>  fc (q n)).
Proof.
intros q Hi n.
apply fc_mono, Hi.  
Qed.


Parameter fc_prod : forall (q: Seq (A := C1.Cc))(Hi : increasing C1.ordc q),
    CPO1.is_cls(CPO1.lim (fun n => CPO1.elt (q n))
                         (CPO1.map_elt_increasing _ Hi)) ->
    CPO2.is_cls(CPO2.lim (fun n => CPO2.elt (fc (q n)))
               (CPO2.map_elt_increasing  _ (increasing_image _ Hi))).


End ProductiveFuncMod.

Module FuncDefMod(C1 C2: FiniteOrderMeasureMod)
       (PF : ProductiveFuncMod C1 C2).
Import PF.                                

Lemma fc_prod_asc : forall (q: Seq (A := C1.Cc)), ascending C1.ordc q ->
                            ascending C2.ordc (fun n => fc (q n)).
Proof.
intros q Hasc.
destruct Hasc as (Hi & Hns).
apply (CPO1.lim_ascending_is_cls _ Hi) in Hns.                                          
apply fc_prod in Hns.
now apply CPO2.lim_is_cls_ascending  in Hns.
Qed.
  

Theorem indep_rep : forall (q1 q2 : Seq(A := C1.Cc)),
    ascending C1.ordc q1-> ascending C1.ordc q2 -> CPO1.SEM.ssim q1 q2 ->
    CPO2.SEM.ssim (fun n => fc (q1 n))  (fun n => fc (q2 n)). 
Proof.    
intros q1 q2 Ha1 Ha2 Hs.
apply CPO2.sovertaken_ssim.
*
  now apply fc_prod_asc.
*
  now apply fc_prod_asc.
*
  intro n.
  generalize Ha1; intros (Hi1  & _).
  remember (CPO1.lim (fun n => CPO1.elt (q1 n)) (CPO1.map_elt_increasing _ Hi1))
    as l1.
  generalize Ha2; intros (Hi2  & _).
  remember (CPO1.lim (fun n => CPO1.elt (q2 n)) (CPO1.map_elt_increasing _ Hi2))
    as l2.
  assert(Heq : l1 = l2).
  {
    rewrite Heql1, Heql2.
    erewrite (CPO1.eqv_same_lim) with (q2 := q2) (Hi2:= Hi2); auto.
    *
      now destruct Ha1 as ( _ & Hs1).
    *
      now destruct Ha2 as ( _ & Hs2).
  }
  assert (Hc : CPO1.is_cls l1).
  {
    rewrite Heql1.
    apply  CPO1.lim_ascending_is_cls.
     now destruct Ha1 as ( _ & Hs1).
  }
  assert (Hex: exists n0 : nat, C1.ordc (q1 n) (q2 n0)).
  {
    eapply CPO1.same_lim_overtakes.
    *
      now destruct Ha1 as (_ & Hn).
    *
      now destruct Ha2 as (_ & Hn).
    *
      now rewrite <- Heql1, <- Heql2.
  }  
  destruct Hex as (m & Hord).
  exists m.
  now apply fc_mono.
Qed.


Definition f (x : CPO1.C) : CPO2.C :=
  match x with
    CPO1.elt e => CPO2.elt (fc e)
  | CPO1.cls c => let (q,Ha) := CPO1.EC.representative c in
                  (CPO2.cls (CPO2.EC.class_of
                               (exist  _
                                       (fun n => fc (q n))
                                (fc_prod_asc _ Ha))))
  end.
End FuncDefMod.
