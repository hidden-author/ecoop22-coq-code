Require Import FiniteOrderMeasure.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.
Require Import PeanoNat.
Import Nat Lt Le.
Require Import List.
Import ListNotations.


Module Type TypeMod.
Parameter A : Type.
End TypeMod.

(* needs to be outside the FtreeMod module because of a limitation of the Coq module system *)

Inductive Ftree{A:Type} : Type   :=
|bot : Ftree 
|ftree : A-> list Ftree -> Ftree.

  
Module FtreeMod (TM : TypeMod) <: FiniteOrderMeasureMod.
Import TM.


Lemma Ftree_induct : forall (P : Ftree (A:=A)-> Prop),
    P bot ->
    (forall a l,
            (forall n, n < length l ->  P (nth n l bot))
            -> P (ftree a l))  ->
    forall t,  P t.
Proof.
intros P Hn Hall.
fix Ftree_induct_t 1.
intro t.
destruct t.
*
 apply Hn.
*
  apply Hall.
  induction l; intros n Hlt;  cbn in Hlt ; [lia|].
  destruct n; cbn.
  +
    apply  Ftree_induct_t.
  +
    apply IHl ; lia.
Qed.

Fixpoint cut (n : nat) (t : Ftree(A:=A)) : Ftree(A:=A) :=
match n with
| 0 => bot    
|S m =>
 match t with
 |bot => bot
 |ftree a l => ftree a (map (cut m) l)
 end  
end.

Fixpoint height (t : Ftree(A:=A)) : nat :=
match t with
bot => 0
| ftree a l => S (list_max (map height l))
end.

Lemma cut_above_height : forall  t n, height t <= n -> cut n t = t.
Proof.
induction t0 using Ftree_induct; intros n Hle ; auto.
*
  destruct n ; auto.
*
  revert l H n Hle.
  induction l; intros H n Hle; auto; cbn.
  +
    destruct n ;  cbn in Hle ; try lia; auto.
  +
    destruct n ;  cbn in Hle ; try lia.
    apply le_S_n in Hle.
    cbn.
    f_equal.
    f_equal.
    - 
      generalize (H _ (Nat.lt_0_succ _)); intro Ha0.
      cbn [nth] in Ha0.
      apply Ha0.
      apply le_trans with (m := max (height a0)
          (fold_right Init.Nat.max
                      0 (map height l))); auto.
      apply Max.le_max_l.
   -   
      assert (Hl :  forall n : nat,
        height (ftree a l) <= n ->
        cut n (ftree a l) =
        ftree a l).
      {
        eapply IHl ; eauto.
        intros j Hlt i Hh.
        specialize (H (S j)).
        apply H; auto.
        cbn ; lia.
      }
      specialize (Hl (S n)).
      cbn in Hl.
      assert (Heqtree :  ftree a (map (cut n) l) = ftree a l).
      {
        apply Hl,  le_n_S .
        apply le_trans with (m := max (height a0)
          (fold_right max 0
                      (map height l))); auto.
        apply Max.le_max_r.
      }
     injection Heqtree; intros; auto.
Qed.      


Lemma max_list_max :
  forall l n, n < length l -> height (nth n l bot) <=   list_max (map height l).
Proof.
induction l; intros n Hlt; cbn in Hlt ; try lia.
destruct n; cbn; try lia.
replace ((fold_right Init.Nat.max 0
                     (map height l))) with (list_max (map height l)); auto.

apply lt_S_n in Hlt.
specialize (IHl _  Hlt).
eapply le_trans ; eauto.
apply Max.le_max_r.
Qed.

Lemma map_cut : forall l n,
    list_max (map height l) <= n -> map (cut n) l = l.
Proof.
induction l; intros n Hle; auto.
cbn.  
f_equal.
{
  rewrite cut_above_height; auto.
  apply le_trans  with (m := list_max
                               (map height (a :: l))); eauto.
 apply Max.le_max_l.
}  
{
  eapply IHl; eauto.
  apply le_trans with (m := list_max
                              (map height (a :: l))); eauto.
  apply Max.le_max_r.
} 
Qed.


Lemma cut_reaches_max :
  forall l, (forall n : nat,
      n < length l ->
      forall k : nat,
      (k < height (nth n l bot) ->
       height (cut k (nth n l bot)) = k)) ->
            forall n,  n < list_max (map height l) ->
                       list_max (map height (map (cut n) l)) = n.
Proof.
induction l; intros Hall n Hlt; cbn in Hlt; try lia.
cbn [map].
unfold list_max.
cbn.
replace ( (fold_right Init.Nat.max 0
                      (map height (map (cut n) l)))) with
    (list_max (map height (map (cut n) l))) ; auto.
replace ((fold_right Init.Nat.max 0
                     (map height l))) with (
                                          list_max (map height l)) in Hlt; auto.
specialize (Hall _ (Nat.lt_0_succ _) n) as Ha.
cbn in Ha.
 case (le_lt_dec (height a) ((list_max (map height l)))  ); intro Hcas.
{
   assert (Hrn : n <  list_max (map height l)); [lia|].
  remember   (list_max (map height (map (cut n) l)))  as max_rest.
  assert (Hmr : max_rest = n).
  {
    subst.
    eapply IHl; eauto.
    intros.
    specialize (Hall (S n0)); cbn in Hall.
    apply Hall; auto.
    cbn; lia.
  }
  rewrite Hmr.
  apply Nat.max_r.  
  case (le_lt_dec (height a) n); intro Hcas'.
  *
    now rewrite cut_above_height.
  *
    now rewrite Ha.
}
{
  assert (Hrn : n <  height a); [lia|].
  rewrite Ha; auto.
  remember   (list_max (map height (map (cut n) l)))  as max_rest.
  apply Nat.max_l.
  case(le_lt_dec (list_max (map height l)) n); intro Hcas''.
  2 :
    {
    assert (Hmr : max_rest = n).
    {
      subst.
      eapply IHl; eauto.
      intros.
      specialize (Hall (S n0)); cbn in Hall.
      apply Hall; auto.
      cbn ; lia.
    }
    rewrite Hmr; auto.  
  }
  subst.
  rewrite map_cut; auto.
}
Qed.

Lemma cut_below_height : forall  t n,
   n <= height t -> height (cut n t) = n.
Proof.
intros t n Hle.
destruct (le_lt_eq_dec _ _ Hle).  
*
  clear Hle; revert n l.
  induction t using Ftree_induct;  intro n.
  +
    intro Hlt;  cbn in Hlt ; destruct n; try lia; auto.
  +
    intro Hlt.
    destruct n; auto.
    cbn in Hlt.
    cbn.
    f_equal.
    apply lt_S_n in Hlt.
    now apply cut_reaches_max.
*
  rewrite cut_above_height; auto; lia.
Qed.


Lemma cut_n_Sn : forall n t, n < height t -> cut n t = cut n (cut (S n) t).
Proof.
induction n as [ | n IHn]; [reflexivity | ].
intros [ | a l] Hlt; cbn in Hlt; [lia | ].
cbn.
f_equal.
revert n IHn Hlt.
induction l as [ | t l IHl]; intros n IHn Hlt; [reflexivity | ].
cbn [map] in Hlt.
change (height t :: map height l) with ([height t] ++ map height l) in Hlt.
rewrite list_max_app in Hlt.
cbn.
f_equal.
- apply lt_S_n, Nat.max_le in Hlt.
  destruct Hlt as [Hlt | Hlt].
  + cbn in Hlt.
    rewrite Nat.max_0_r in Hlt.
    apply IHn.
    lia.
  + change (match t with
  | bot => bot
  | ftree a l0 => ftree a (map (cut n) l0)
  end) with (cut (S n) t).
  destruct (le_lt_dec (height t) n) as [Hle | Hlt'].
  * f_equal.
    rewrite cut_above_height; [reflexivity | lia].
  * apply IHn, Hlt'.
- apply lt_S_n in Hlt.
  destruct (le_lt_dec (list_max (map height l)) (list_max [height t]))
   as [Hle | Hlt'].
  + cbn in Hlt, Hle.
    rewrite Nat.max_0_r in Hlt, Hle.
    change (fun t0 : Ftree =>
      match t0 with
      | bot => bot
      | ftree a0 l0 => ftree a0 (map (cut n) l0)
      end) with (cut (S n)).
    (* Search (_ <= _ -> max _ _ = _). *)
    rewrite max_l in Hlt by apply Hle.
    clear a IHl.
    induction l as [ | t' l IH]; [reflexivity | ].
    cbn [map].
    f_equal.
    * destruct (le_lt_dec (height t') (S n)) as [Hle' | Hlt'].
      -- f_equal.
         rewrite cut_above_height; [reflexivity | exact Hle'].
      -- apply IHn.
         lia.
    * apply IH.
      cbn [map] in Hle.
      change (height t' :: map height l) with ([height t'] ++ map height l) in Hle.
      rewrite list_max_app in Hle.
      lia.
  + apply IHl; [exact IHn | lia].
Qed.

Definition fprefix (t1 t2: Ftree) :Prop := t1 = cut (height t1) t2.

Lemma fprefix_refl : forall t,  fprefix t t.
Proof.
intro t.
unfold fprefix.
rewrite cut_above_height; auto.
Qed.


Lemma fprefix_height : forall t1 t2,  fprefix t1 t2 -> height t1 <= height t2.
Proof.
unfold fprefix ; intros t1 t2 Hpre.
case (le_lt_dec (height t1) (height t2)); intros Hcas; auto.
exfalso.
rewrite cut_above_height in Hpre; try lia.
rewrite Hpre in Hcas; lia.
Qed.

Definition cut_last (t : Ftree) : Ftree := cut (pred (height t)) t.

Lemma cut_last_S  : forall n t, n < height t -> cut n t = cut_last (cut (S n) t).
Proof.
intros n t Hle.
unfold cut_last.
rewrite cut_below_height; auto.
rewrite Nat.pred_succ; try lia.
rewrite cut_n_Sn; auto.
Qed.


Lemma cut_twice : forall n m t, n <= m -> 
cut n (cut m t) = cut n t.
intros n m t Hle.
revert t.
induction Hle; intro t.
*
  case (le_lt_dec n (height t)); intros Hcas.
  +
    assert (Hc : height (cut n t) = n); [apply cut_below_height; auto |].
    apply cut_above_height; lia.
  +
    assert (Heq: cut n t = t).
    {
      rewrite cut_above_height; auto ; lia.
    }
    repeat rewrite Heq ; auto.
*
  destruct t; auto.
  cbn.
  destruct n; auto.
  cbn.
  f_equal.
  revert n m Hle IHHle a.
  induction l; intros n m Hle IHHle a'; auto.
  cbn.
  f_equal.
  +
    specialize (IHHle a).
    case (le_lt_dec (height a) m); intros Hcas.
    {
      rewrite (cut_above_height _ m); auto.
    }
    rewrite cut_last_S; auto.
    {
      rewrite IHHle.
      replace (cut n a) with (cut_last (cut (S n) a)); [rewrite <- IHHle; auto |].
      symmetry.
      apply  cut_last_S; lia.
    }
    {
      rewrite cut_below_height; auto; lia.
    }  
  +
    rewrite IHl; auto.
Qed.


Lemma fprefix_trans : forall t1 t2 t3, fprefix t1 t2 -> fprefix t2 t3 -> fprefix t1 t3.
Proof.
unfold fprefix; intros t1 t2 t3 Hpre1 Hpre2.
remember (height t1) as h1.  
rewrite Hpre1; subst.
rewrite Hpre2.
apply fprefix_height in Hpre1, Hpre2.
apply cut_twice; auto.
Qed.

Lemma fprefix_antisym :
  forall t1 t2,  fprefix t1 t2 -> fprefix t2 t1 -> t1 = t2.
Proof.
intros t1 t2 Hpre1 Hpre2.
unfold fprefix in *.  
case (le_lt_dec (height t1) (height t2)); intros Hcas.
*
  rewrite cut_above_height in Hpre2; auto.
*
  rewrite cut_above_height in Hpre1; auto; lia.
Qed.


Lemma fprefix_wtotal_l :
  forall t t1 t2,
    fprefix t1 t -> fprefix t2 t ->
    height t1  <= height t2 ->
    fprefix t1 t2.
Proof.  
intros t t1 t2 Hpre1 Hpre2 Hle.
unfold fprefix in *.
rewrite Hpre2.
rewrite cut_twice; auto.
Qed.

Lemma fprefix_wtotal_r :
  forall t t1 t2,
    fprefix t1 t -> fprefix t2 t ->
    height t2  <= height t1 ->
    fprefix t2 t1.
Proof.  
intros t t1 t2 Hpre1 Hpre2 Hle.
unfold fprefix in *.
rewrite Hpre1.
rewrite cut_twice; auto.
Qed.

Lemma fprefix_wtotal : forall t1 t2 t,
    fprefix t1 t -> fprefix t2 t -> (fprefix t1 t2 \/ fprefix t2 t1).
Proof.
intros t1 t2 t Hp1 Hp2.
destruct (le_gt_dec (height t1) (height t2)).
*
  left.
  eapply fprefix_wtotal_l; eauto.
*
  right.
  eapply fprefix_wtotal_r; eauto; lia.
Qed.


Lemma fprefix_height_eq_or_lt :
  forall t1 t2, fprefix t1 t2 -> t1 = t2 \/ height t1 < height t2.
Proof.
induction t1 using Ftree_induct.
*
  intros t2 Hpre.
  destruct t2; [left ; auto| right; cbn; lia].
*
  intros t2 Hpre.
  destruct t2.
  +
    exfalso.
    unfold fprefix in Hpre.
    discriminate.
  +
    unfold fprefix in Hpre.
    destruct (le_gt_dec (height (ftree a0 l0)) (height (ftree a l))).
    -
      rewrite cut_above_height in Hpre; auto.
    -
      right; lia.
Qed.



Definition Cc : Type := Ftree(A:=A).

Definition bot := bot (A:=A).

Definition ordc := fprefix.

Definition sordc x y := ordc x y /\ x <> y.

Lemma bot_is_bot : forall x, ordc bot x.
Proof.
intro x; constructor.
Qed.

Definition ordc_refl := fprefix_refl.

Definition ordc_trans := fprefix_trans.

Definition ordc_antisym := fprefix_antisym.

Definition  ordc_wtotal := fprefix_wtotal.

Definition mu := height.

Lemma mu_sordc : forall x y, ordc x y -> x <> y ->  mu x < mu y.
Proof.
intros x y Ho Hne.
apply fprefix_height_eq_or_lt in Ho.
destruct Ho as [Ho |Ho]; auto.
exfalso; now apply Hne.
Qed.

End FtreeMod.
