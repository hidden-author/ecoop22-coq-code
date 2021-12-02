Require Import Lia.
Require Import List.
Require Import PeanoNat.
Import Nat Le Lt.
Import ListNotations.
Require Import Compare_dec.
Require Import Coq.Program.Wf.
Require Import Wf_nat.
Require Import IndefiniteDescription.
Require Import ClassicalDescription.
Require Import Sequences.
Require Import Tree.
Require Import CPO.
Require Import FuncDef.

Fixpoint f2l{A : Type} (n : nat)( f : nat -> A) : list A :=
match n with
|0 => []
|S m => (f 0) :: (f2l m (fun i => f (S i)))
end.

Lemma f2l_length{A: Type} : forall n (f : nat ->A),  length (f2l n f) = n.
Proof.
induction n; intro f; auto.
cbn.
rewrite IHn; auto.
Qed.

Lemma f2l_elts{A : Type} : forall n (f: nat -> A) i d,
    i < n -> nth i (f2l n f) d = f i.
Proof.
induction n; intros f i d Hlt; try lia.
destruct i; auto.
cbn.
rewrite IHn; auto ; lia.
Qed.

Definition f2l_dep{A : Type} (n : nat)(f  : forall i,  i < n -> A)(d:A) : list A :=
f2l n
    (fun k =>
       match (le_lt_dec n k ) with
         |left _   => d
         |right p => f k p
       end).


Lemma f2l_dep_length{A: Type} :
  forall n (f  : forall i,  i < n -> A) d,   length (f2l_dep n f d) = n.
Proof.
intros n f d.
unfold f2l_dep.
rewrite f2l_length; auto.
Qed.

Lemma f2l_dep_elts{A : Type} :
  forall n (f:  forall i,  i < n -> A) i d(Hlt:   i < n),
    nth i (f2l_dep n f d) d = f i Hlt.
Proof.
intros n f i d Hlt.
unfold f2l_dep.
rewrite f2l_elts; auto.
destruct ( le_lt_dec n i) ; try lia.
f_equal.
erewrite proof_irrelevance; eauto.
Qed.


Lemma list_max_rev : forall l, list_max l = list_max (rev l).
Proof.  
induction l ; auto.
cbn [rev].
replace (a :: l) with ([a] ++ l); auto.
do 2 rewrite list_max_app.
rewrite IHl.
apply Max.max_comm.
Qed.


Module FmirrorMod(TM : TypeMod).
Import TM.  
Module F := FtreeMod TM.
Import F.
Import Tree.

Obligation Tactic := idtac.
Program Fixpoint fmirror (t : (Ftree(A :=A))) {measure (height t)}: Ftree(A :=A) :=
  match t with
     | ftree a l =>  ftree a (
                          f2l_dep (length l)
                                  (fun n _ => fmirror (nth n (rev l) F.bot))
                                  F.bot )
    |  bot => bot  
  end.  
Next Obligation.
intros t Hall a l Heq n Hlt.
rewrite <- Heq.
cbn.
apply le_n_S.
rewrite rev_nth; auto.
apply max_list_max; lia.
Qed.

Next Obligation.
intros.
apply well_founded_ltof.
Qed.

Lemma fmirror_eta : forall t, fmirror t =
    match t with
     | ftree a l =>  ftree a (
                             f2l_dep (length l)
                                     (fun n _ => fmirror (nth n (rev l ) bot))
                                     bot )
  |  bot => bot
 
  end.
Proof.  
intro t.
destruct t.  
*
  unfold fmirror.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; auto.
*
  unfold fmirror.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; auto.
Qed.

Lemma f2l_dep_map :
forall l (f : Ftree(A:=A) -> Ftree(A :=A)), f2l_dep (length l) (fun n _ =>  f (nth n l bot)) bot = map f l.
intros l f.  
eapply nth_ext with (d := bot) (d' := f bot).
*
  rewrite f2l_dep_length.
  rewrite map_length; auto.
*
  rewrite f2l_dep_length.
  intros n Hlt.
  rewrite f2l_dep_elts ; auto.
  rewrite map_nth; auto.
Qed.

Lemma fmirror_eta_plus : forall t, fmirror t =
  match t with
  | ftree a l =>ftree a (map fmirror (rev l))
  |  bot => bot                         
  end.
Proof.  
intro t.
rewrite fmirror_eta.
destruct t ; auto.
f_equal.
rewrite <- rev_length.
rewrite f2l_dep_map; auto.
Qed.

Lemma fmirror_eta_bot : fmirror bot = bot.
Proof.  
rewrite fmirror_eta; auto.
Qed.

Lemma fmirror_eta_plus_ftree : forall a l,
    fmirror (ftree a l) = ftree a (map fmirror (rev l)).
Proof.
intros a l.
rewrite fmirror_eta_plus; auto.
Qed.

Lemma fmirror_height : forall t,  height (fmirror t) = height t.
Proof.
induction t0 using Ftree_induct.
*
  cbn.
  rewrite fmirror_eta_bot; auto.
*
  rewrite fmirror_eta_plus_ftree.
  cbn.
  f_equal.
  rewrite map_map.
  rewrite map_rev.
  rewrite <- list_max_rev.
  induction l; auto.
  cbn [map height].
  replace ((height (fmirror a0)
     :: map (fun x : Ftree => height (fmirror x))
          l)) with ([height (fmirror a0)]
      ++ map (fun x : Ftree => height (fmirror x))
          l); auto.
  replace (height a0 :: map height l) with ([height a0] ++ map height l); auto.
  do 2 rewrite list_max_app.
  rewrite IHl; auto.
  +
    specialize (H 0).
    cbn in H.
    rewrite H; lia.
  +
    intros n Hlt.
    specialize (H  (S n)).
    cbn in H.
    rewrite H; lia.
Qed.

Lemma fmirror_cut : forall n t,  cut n (fmirror t) = fmirror (cut n t).
Proof.  
induction n; intro t; cbn.
*
  rewrite fmirror_eta_bot ; auto.
*
  destruct t.
  +
    rewrite fmirror_eta_bot ; auto.
  +
    do 2 rewrite fmirror_eta_plus_ftree.
    f_equal.
    rewrite map_map.
    repeat rewrite map_rev.
    f_equal.
   induction l ; auto.
   cbn.
   f_equal.
   -
     apply IHn.
   -
     apply IHl.
Qed.


Lemma fmirror_inv : forall t, fmirror (fmirror t) = t.
Proof.
  eapply well_founded_ind with
      (R := fun t1 t2 => height t1 < height t2); [apply well_founded_ltof |].
intros t Hind.
destruct t.
*
  do  2 rewrite fmirror_eta_bot; auto.
*
   do 2 rewrite fmirror_eta_plus_ftree.
   f_equal.
   rewrite map_rev .
   rewrite map_map.
   rewrite map_rev.
   rewrite rev_involutive.
   induction l; auto.
   cbn.
   f_equal.
   +
    apply Hind; cbn; lia.
   +
     rewrite IHl ; auto.
     intros y Hlt.
     apply Hind.
     eapply Nat.lt_le_trans; eauto.
     cbn [height].
     apply le_n_S.
     replace (a0 :: l) with ([a0] ++l); auto.
     rewrite map_app, list_max_app.
     lia.
Qed.

Lemma fmirror_mono : forall t1 t2,  fprefix t1 t2 -> fprefix (fmirror t1) (fmirror t2).
Proof.
intros t1 t2 Hpre.
generalize Hpre; intro Hpre'.
apply fprefix_height in Hpre'.
unfold fprefix in *.
rewrite fmirror_height.
rewrite Hpre at 1.
rewrite fmirror_cut; auto.
Qed.


Lemma fmirror_asc : forall (q : Seq (A := Ftree)),
    ascending fprefix q -> ascending fprefix (fun n => fmirror (q n)).
Proof.
intros q Hasc.
rewrite  subsequence_iff_ascending;
  [| apply fprefix_refl | apply fprefix_trans | apply fprefix_antisym].
rewrite  subsequence_iff_ascending in Hasc;
  [| apply fprefix_refl | apply fprefix_trans | apply fprefix_antisym].
destruct Hasc as (Hinc & (q' & (f & Hfi & Hall) & Hsi)).
split.
*
  intro n.
  apply fmirror_mono, Hinc.
*
  exists (fun n => fmirror (q' n)).
  split.
  +
    exists f; split; auto.
    intro n.
    now rewrite Hall.
  +
    destruct Hsi as (Hi & Hn).
    split.
    - 
      intro n.
      apply fmirror_mono, Hi.
   -
     intros n Heq.
     apply (Hn n).
     apply f_equal with (f := fmirror) in Heq.
     now do 2 rewrite fmirror_inv in Heq.
Qed.

 Fixpoint fpos (p : list nat) (t : Ftree) : option A :=
match p with
  [] =>
  match t with
    bot => None
   | ftree a _ => Some a            
  end  
| n :: p' =>
   match t with
    bot => None
   | ftree _ l =>
     if le_lt_dec (length l) n then None else
     fpos p' (nth n l bot)  
  end     
end.


Fixpoint fpos_sym (p : list nat) (t : Ftree) : option A :=
match p with
  [] =>
  match t with
    bot => None
   | ftree a _ => Some a            
  end  
| n :: p' =>
   match t with
    bot => None
   | ftree _ l =>
     if  le_lt_dec (length l) n then None else
       fpos_sym p' (nth (length l - (S n)) l bot)         
  end     
end.    


Lemma fmirror_fpos : forall p t,  fpos p (fmirror t) = fpos_sym p t.
Proof.
induction p; intros t.
*
  destruct t.
  +
    rewrite fmirror_eta_bot ; auto.
  +
    rewrite fmirror_eta_plus_ftree; auto.
 *
   destruct t.
   +
     rewrite fmirror_eta_bot ; auto.
   +
      rewrite fmirror_eta_plus_ftree.
      cbn.
      rewrite map_length, rev_length.
      destruct (le_lt_dec (length l) a); auto.
      rewrite <- IHp.
      replace (nth a (map fmirror (rev l)) bot) with
          (nth a (map fmirror (rev l)) (fmirror bot)) ; [| rewrite fmirror_eta_bot; auto].
      rewrite map_nth.
      rewrite rev_nth; auto.
Qed.


Lemma fpos_fprefix :
  forall p t t',  length p < height t ->  fprefix t t' ->
                  fpos p t' = fpos p t.
Proof.  
induction p ; intros t t' Hle1 Hle2.
*
  generalize Hle2 ; intros Hh; apply fprefix_height in Hh.
  unfold fprefix in Hle2.
  rewrite Hle2.
  destruct t; cbn in Hle1; try lia.
  destruct t'; cbn in Hh; try lia; auto.
*
  generalize Hle2 ; intros Hh; apply fprefix_height in Hh.
  destruct t; cbn in Hle1; try lia.
  destruct t'; cbn in Hh; try lia.
  inversion Hle2; subst.
  cbn.
  rewrite map_length.
  destruct (le_lt_dec (length l0) a); auto.
  replace  (nth a
       (map
          (cut
             (list_max (map height l)))
          l0) bot) with  (nth a
       (map
          (cut
             (list_max (map height l)))
          l0) (cut (list_max (map height l)) bot));
    [|destruct (list_max (map height l)); auto].
  rewrite map_nth.
  apply lt_S_n in Hle1.
  apply le_S_n in Hh.
  destruct (le_lt_dec ((list_max (map height l))) (height (nth a l0 bot))).
  +
    eapply IHp.
    -
      rewrite cut_below_height; auto.
    -
      unfold fprefix.
      rewrite cut_below_height; auto.
  +
    rewrite cut_above_height; auto ; lia.
Qed.



Lemma fpos_sym_fprefix :
  forall p t t',  length p < height t ->  fprefix t t' ->
                  fpos_sym p t' = fpos_sym p t.
Proof.
intros p t t' Hlt Hle.
do 2 rewrite <- fmirror_fpos.
apply fpos_fprefix.
*
  rewrite fmirror_height; auto.
*
  apply fmirror_mono; auto.
Qed.


End FmirrorMod.

Module NatTypeMod <: TypeMod.
Definition A := nat.
End NatTypeMod.  

Module TreeDom := FtreeMod NatTypeMod.
Module TreeRan := FtreeMod NatTypeMod.


Module ProductiveMirrorMod <: ProductiveFuncMod TreeDom TreeRan.

Module Export CPO1 :=CPOMod TreeDom.
Module Export CPO2 :=CPOMod TreeRan.

Module FM := FmirrorMod NatTypeMod.
Import FM.

Definition fc : TreeDom.Cc -> TreeDom.Cc := fmirror.

Lemma fc_mono :
  forall x y,  TreeDom.ordc x y -> TreeRan.ordc (fc x) (fc y).
Proof.
intros x y HD.  
now apply fmirror_mono.
Qed.

Lemma increasing_image :
  forall q,  increasing TreeDom.ordc q ->
               increasing  TreeRan.ordc (fun n =>  fc (q n)).
Proof.
intros q Hi n.
apply fc_mono, Hi.  
Qed.

Lemma fc_prod : forall (q: Seq (A := TreeDom.Cc))
                       (Hi : increasing TreeDom.ordc q),
    CPO1.is_cls(CPO1.lim (fun n => CPO1.elt (q n))
                         (CPO1.map_elt_increasing _ Hi)) ->
    CPO2.is_cls(CPO2.lim (fun n => CPO2.elt (fc (q n)))
               (CPO2.map_elt_increasing  _ (increasing_image _ Hi))).
intros q Hi Hc. 
unfold fc.  
remember ((lim (fun n : nat => elt (fmirror (q n)))
       (map_elt_increasing
          (fun n : nat => fmirror (q n))
          (increasing_image q Hi)))) as c.
destruct c; try constructor.
exfalso.
unfold lim in Heqc.
destruct (excluded_middle_informative
             (stabilizing
                (fun n : nat =>
                   elt (fmirror (q n))))) ; try discriminate.
clear Heqc.
unfold CPO1.lim in Hc.
destruct (excluded_middle_informative
             (stabilizing (fun n : nat => CPO1.elt (q n)))).
*
  destruct ( constructive_indefinite_description _ s0).
  destruct x; try inversion Hc.
  destruct s1 as (n & Hall).
  specialize (Hall _ (le_refl _)).
  discriminate.
*
  clear Hc.
  apply n; clear n.
  destruct s as (a & n & Hall).
  destruct a.
  +
    unfold stabilizing.
    exists (CPO1.elt (fmirror e0)), n.
    intros m Hle.
    f_equal.
    specialize (Hall _ Hle).
    injection Hall; clear Hall; intro Hall; subst.
    now rewrite fmirror_inv.
  +
    specialize (Hall _ (le_refl _)).
    discriminate.
Qed.

End ProductiveMirrorMod.


Module MirrorProperties.
Module MD := FuncDefMod TreeDom TreeRan ProductiveMirrorMod.
Import MD.
Import TreeDom TreeRan ProductiveMirrorMod.
Module FM := FmirrorMod NatTypeMod.
Import FM.
Definition mirror := f.

Definition rpos (p : list nat) (c : CPO2.EC.EqClass) : option nat:=
  fpos p (proj1_sig (CPO2.EC.representative c) 
         (proj1_sig (constructive_indefinite_description _
                                          (CPO2.SEM.ascending_mu_unbounded_alt
                                            (CPO2.EC.representative c)   (S (length p)))))).

Lemma rpos_fpos :
  forall p c,  exists k,  mu (proj1_sig (CPO2.EC.representative c) k) >= S (length p) /\
                rpos p c = fpos p (proj1_sig (CPO2.EC.representative c) k).
Proof.
intros p c.
remember  (EC.representative c) as q.
destruct q as (q & Ha).
cbn.
unfold rpos.
cbn.
exists
         (proj1_sig
            (constructive_indefinite_description
               (fun n : nat =>
                mu
                  (proj1_sig
                     (EC.representative
                     c) n) >=
                S (length p))
               (SEM.ascending_mu_unbounded_alt
                  (EC.representative
                     c)
                  (S (length p))))).
split; auto.
*
  remember ((constructive_indefinite_description
       (fun n : nat =>
        mu (proj1_sig (EC.representative c) n) >=
        S (length p))
       (SEM.ascending_mu_unbounded_alt
          (EC.representative c) 
          (S (length p))))) as c'.
  destruct c' as (k & Hk).
  cbn.
  clear Heqc'.
  now rewrite <- Heqq in Hk.
*
  now rewrite <- Heqq.
Qed.
  
Definition pos (p : list nat) (c:CPO2.C) : option nat :=
  match c with
  | CPO2.elt e => fpos p e
  | CPO2.cls c => rpos p c                
  end.  


Definition rpos_sym (p : list nat) (c : CPO1.EC.EqClass) : option nat:=
  fpos_sym p ((proj1_sig (CPO1.EC.representative c))
             (proj1_sig (constructive_indefinite_description _
                                                             (CPO1.SEM.ascending_mu_unbounded_alt
                                                                (CPO1.EC.representative c) (S (length p)))))). 

Lemma rpos_sym_fpos_sym :
  forall p c,  exists k,  mu (proj1_sig (CPO1.EC.representative c) k) >= S (length p) /\
                rpos_sym p c = fpos_sym p (proj1_sig (CPO1.EC.representative c) k).
Proof.
intros p c.
remember  (CPO1.EC.representative c) as q.
destruct q as (q & Ha).
cbn.
unfold rpos_sym.
cbn.
exists
         (proj1_sig
            (constructive_indefinite_description
               (fun n : nat =>
                mu
                  (proj1_sig
                     (CPO1.EC.representative
                     c) n) >=
                S (length p))
               (CPO1.SEM.ascending_mu_unbounded_alt
                  (CPO1.EC.representative
                     c)
                  (S (length p))))).
split; auto.
*
  remember ((constructive_indefinite_description
       (fun n : nat =>
        mu (proj1_sig (CPO1.EC.representative c) n) >=
        S (length p))
       (CPO1.SEM.ascending_mu_unbounded_alt
          (CPO1.EC.representative c) 
          (S (length p))))) as c'.
  destruct c' as (k & Hk).
  cbn.
  clear Heqc'.
  now rewrite <- Heqq in Hk.
*
   now rewrite <- Heqq.
Qed.

Definition pos_sym (p : list nat) (c:CPO1.C) : option nat :=
  match c with
  | CPO1.elt e => fpos_sym p e
  | CPO1.cls c => rpos_sym p c                
  end.  

Lemma mirror_pos : forall p t,  pos p (mirror t) = pos_sym p t.
Proof.
intros p t.
destruct t.
*
  cbn.
  apply ProductiveMirrorMod.FM.fmirror_fpos.
*
  cbn.
 remember (CPO1.EC.representative ec) as q.
 destruct q as (q & Ha).
 cbn.
 destruct (rpos_fpos p  (CPO2.EC.class_of
       (exist (ascending ordc)
          (fun n : nat => fc (q n))
          (fc_prod_asc q Ha)))) as (k1 & Hm1 & Heq1).
 
 unfold Cc, Seq in *.
 rewrite Heq1.
 destruct (rpos_sym_fpos_sym  p ec) as (k1' & Hm1' & Heq'1).
 rewrite <-  Heqq in *.
 cbn in *.
 rewrite Heq'1.
 unfold fc in *.
 clear Heq1 Heq'1 Heqq.
 generalize (EC.sim_representative   (exist 
                                (ascending ordc)
                                (fun n : nat =>
                                 ProductiveMirrorMod.FM.fmirror
                                   (q n))
                                (fc_prod_asc q Ha))); intro Hsim.
 unfold Cc, Seq in *.
 cbn.
remember   (EC.representative
              (EC.class_of
                 (@exist
                    (forall _ : nat,
                     @Ftree NatTypeMod.A)
                    (@ascending (@Ftree NatTypeMod.A)
                       ordc)
                    (fun n : nat =>
                     ProductiveMirrorMod.FM.fmirror
                       (q n)) (fc_prod_asc q Ha)))) as r.
destruct r  as (r & Har).
cbn in *.
destruct  (Hsim (S (length p))) as (x & (n & Ho1 & Ho2 & Hge)).
remember (k1 + k1' + n) as N.
unfold ordc, mu in *.
replace height with F.height in *; auto.   
assert (Heq1 : fpos p (r N) = fpos p (r k1)).
{
  eapply fpos_fprefix; try lia.
  apply increasing_alt;
    [apply fprefix_refl | apply fprefix_trans | apply fprefix_antisym | now destruct Har | lia ].
}
rewrite <- Heq1.
assert (Heq2 : fpos p (r N) = fpos p x ).
{
  eapply fpos_fprefix; try lia.
  apply fprefix_trans with (t2 := r n); auto.
  apply increasing_alt;
    [apply fprefix_refl | apply fprefix_trans | apply fprefix_antisym | now destruct Har | lia ].
}
rewrite Heq2.
assert (Heq3 : fpos p (ProductiveMirrorMod.FM.fmirror (q N)) = fpos p x).
{
  eapply fpos_fprefix; try lia.
  apply fprefix_trans with (t2 := (ProductiveMirrorMod.FM.fmirror
             (q n))); auto.
  eapply increasing_alt with (q0:= fun n => (ProductiveMirrorMod.FM.fmirror (q n)))(i := n)(j := N);
    [apply fprefix_refl | apply fprefix_trans | apply fprefix_antisym |  | lia ].
  intro z.
  replace fprefix with ProductiveMirrorMod.FM.F.fprefix; auto.
  apply ProductiveMirrorMod.FM.fmirror_mono.
  destruct Ha as (Hi & Hns).
  apply Hi.
}
rewrite <- Heq3.
rewrite ProductiveMirrorMod.FM.fmirror_fpos.
replace (ProductiveMirrorMod.FM.fpos_sym) with fpos_sym in *; auto.
eapply fpos_sym_fprefix; try lia.
  apply increasing_alt;
    [apply fprefix_refl | apply fprefix_trans | apply fprefix_antisym | now destruct Ha | lia].
Qed.
  
End MirrorProperties.
