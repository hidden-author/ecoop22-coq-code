Require Import IndefiniteDescription.
Require Import ClassicalDescription.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.
Require Import PeanoNat.
Require Import Sequences.
Require Import FiniteOrderMeasure.
Require Import EqvClasses.


Module SeqEqvMod (FOM : FiniteOrderMeasureMod) <: EqvMod.
Import FOM.
  
Lemma mu_ordc : forall x y,  ordc x y -> mu x <= mu y.
Proof.
intros x y Hord.
destruct (excluded_middle_informative (x = y)); subst; try lia.
apply mu_sordc in Hord; auto; lia.
Qed.

Definition asc_subs :=
  (ascending_subsequence Cc ordc ordc_refl ordc_trans ordc_antisym).  

Definition incr_alt := (increasing_alt  ordc ordc_refl ordc_trans ordc_antisym).

Lemma strictly_increasing_mu : forall(q : Seq(A :=Cc)),
  strictly_increasing ordc q -> forall n,  mu (q n) >= n + mu (q 0). 
intros q Hsi.
induction n; try lia.
destruct Hsi as (Hi & Hne).
assert (Hso : ordc (q n) (q (S n)) /\ q n <> q (S n)).
{
  split ; [apply Hi | ].
  intro Heq.
  apply (Hne n); congruence.
}
destruct Hso as (Hso1 & Hso2).
apply mu_sordc in Hso1; try lia; auto.
Qed.

Lemma ascending_mu_unbounded :forall(q : Seq(A :=Cc)),
  ascending ordc q -> forall N,  exists n,  mu (q n) >= N.
Proof.
intros q Ha N.
destruct (asc_subs  _ Ha) as (q' & Hs & Hsi).  
destruct Hs as (f & Hf & Haf).
generalize (strictly_increasing_mu _ Hsi) ; intro Hsi'. 
exists (f N).
rewrite <- Haf.
specialize (Hsi' N).
lia.
Qed.
 
Lemma ascending_mu_unbounded_alt :forall(q : { q : Seq(A :=Cc) | ascending ordc q}) N,
  exists n,  mu ((proj1_sig q) n) >= N.
Proof.
intros (q & Ha) N.
now apply  ascending_mu_unbounded.  
Qed.

Definition ssim (q1 q2 :  Seq(A := Cc)) :=
  forall N,  exists x n,  ordc x (q1 n) /\ ordc x (q2 n) /\ mu x >= N.

Lemma ssim_refl :
  forall(q : Seq(A :=Cc)),  ascending ordc q -> ssim q q.
Proof.  
intros q Ha N.
destruct (ascending_mu_unbounded _ Ha N) as (m & Hm).
exists (q m), m; repeat split; auto; apply ordc_refl.  
Qed.

Lemma ssim_sym :  forall (q1 q2 :  Seq(A := Cc)), ssim q1 q2 -> ssim q2 q1.
Proof.
intros q1 q2 Hsim N.
destruct (Hsim N) as (x & n & Ho1 & Hoq & Hle).
exists x, n ; repeat split; auto.
Qed.

Lemma ssim_trans :  forall (q1 q2 q3 :  Seq(A := Cc)),
    ascending ordc q1 -> ascending ordc q2 -> ascending ordc q3 ->
    ssim q1 q2 -> ssim q2 q3 -> ssim q1 q3.
Proof.
intros q1 q2 q3 Ha1 Ha2 Ha3 Hs1 Hs2 N.
destruct (Hs1 N) as (y & m & Ho1 & Ho2 & Hge).
destruct (Hs2 N) as (y' & m' & Ho1' & Ho2' & Hge').
assert(Hom  : ordc y (q2 (max m m'))).
{
  apply ordc_trans with (y := (q2 m)); auto.
  destruct Ha2 as (Hi2 & _).
  rewrite incr_alt in Hi2.
  apply Hi2; lia.  
}
assert(Hom'  : ordc y' (q2 (max m m'))).
{
  apply ordc_trans with (y := (q2 m')); auto.
  destruct Ha2 as (Hi2 & _).
  rewrite incr_alt in Hi2.
  apply Hi2; lia.  
}  
destruct (ordc_wtotal _ _ _ Hom Hom'). 
*
  exists y, (max m  m'); repeat split; auto.
  +
    apply ordc_trans with ( y := (q1 m)); auto.
    destruct Ha1 as (Hi1 & _).
    rewrite incr_alt in Hi1.
    apply Hi1; lia.
  +
    apply ordc_trans with (y := y'); auto.
    apply ordc_trans with (y := (q3 m')); auto.
    destruct Ha3 as (Hi3 & _).
    rewrite incr_alt in Hi3.
    apply Hi3; lia.
*
  exists y', (max m  m'); repeat split; auto.
  +
    apply ordc_trans with ( y :=  y); auto.
    apply ordc_trans with (y := (q1 m)); auto.
    destruct Ha1 as (Hi1 & _).
    rewrite incr_alt in Hi1.
    apply Hi1; lia.
  +
    apply ordc_trans with (y := (q3 m')); auto.
    destruct Ha3 as (Hi3 & _).
    rewrite incr_alt in Hi3.
    apply Hi3; lia.
Qed.

Definition T := {q : Seq(A := Cc) | ascending ordc q}.

Definition sim (t1 t2 : T) := ssim (proj1_sig t1) (proj1_sig t2).

Lemma sim_refl : forall t, sim t t.
intro t.
destruct t as (q & Ha).
now apply ssim_refl.
Qed.

Lemma sim_sym : forall t1 t2, sim t1 t2 -> sim t2 t1.
intros t1 t2 Hs.
destruct t1 as (q1 & Ha1).
destruct t2 as (q2 & Ha2).
now apply ssim_sym.
Qed.

Lemma sim_trans : forall t1 t2 t3, sim t1 t2 -> sim t2 t3 -> sim t1 t3.
intros t1 t2 t3 Hs1 Hs2.
destruct t1 as (q1 & Ha1).
destruct t2 as (q2 & Ha2).
destruct t3 as (q3 & Ha3).
apply ssim_trans with (q2 := q2); eauto.
Qed.
End SeqEqvMod.

Module CPOMod (FOM : FiniteOrderMeasureMod).
Module SEM := SeqEqvMod FOM.
Import FOM.
Import SEM.
Module EC := EqvClassesMod SEM.
Import EC.

Definition sovertaken (q1 q2: Seq (A := Cc)) :=
  forall n,  exists m,  ordc (q1 n) (q2 m).

Lemma sovertaken_ssim : forall (q1 q2: Seq (A := Cc)),
    ascending ordc q1 -> ascending ordc q2 -> sovertaken q1 q2 ->
    ssim q1 q2.
Proof.
intros q1 q2 Ha1 Ha2 Ho N.
destruct (ascending_mu_unbounded  _ Ha1 N) as (n & Hle).
destruct (Ho n) as (m & Ho').
exists (q1 n), (max m n) ; repeat split; auto.
*
  destruct Ha1 as (Hi1 & _).
  rewrite incr_alt in Hi1.
  apply Hi1; lia.
*
  apply ordc_trans with (y := (q2 m)); auto.
  destruct Ha2 as (Hi2 & _).
  rewrite incr_alt in Hi2.
  apply Hi2; lia.
Qed.

Definition overtaken (t1 t2 : T) := sovertaken (proj1_sig t1) (proj1_sig t2).

Lemma  overtaken_sim : forall t1 t2, overtaken t1 t2 -> sim t1 t2.
Proof.
intros (q1 & Ha1) (q2 & Ha2) Ho.  
apply sovertaken_ssim; auto.
Qed.

Inductive C : Type :=
|elt : forall (e : Cc), C
|cls : forall (ec : EqClass), C.

Definition extract_elt(c : C) : Cc :=
  match  c with
    elt e => e
    | _ => bot           
  end .

Definition is_cls(c: C) : Prop :=
  match c with
  | cls _=> True
  | _ => False              
  end.  

Definition cin (t : T)(ec : EqClass) := (proj1_sig ec) t.
Definition tnth(t : T) (n: nat) := (proj1_sig t) n.

Inductive ord : C -> C -> Prop :=
|elt_elt : forall  e1 e2,  ordc e1 e2 -> ord (elt e1) (elt e2)
|elt_cls : forall e ec,
    (forall t,  cin t ec -> exists n,  ordc e (tnth t n) ) ->
    ord (elt e) (cls ec)
|cls_cls : forall ec, ord (cls ec) (cls ec).

Lemma ord_refl : forall c,  ord c c.
Proof.
intro c ; destruct c.  
*
  constructor; apply ordc_refl.
*  
  constructor ; auto.
Qed.

Lemma ord_trans : forall c1 c2 c3,  ord c1 c2 -> ord c2 c3 -> ord c1 c3.
Proof.
intros c1 c2 c3 Ho1 Ho2.  
inversion Ho1 ; inversion Ho2 ; subst ;  try discriminate.
* 
  constructor.
  inversion Ho1; inversion Ho2 ; subst.
  eapply ordc_trans; eauto.
*
  constructor.
  intros t Hc.
  destruct (H2 _ Hc) as (n & Ho).
  exists n.
  injection H3 ; intros ; subst.
  eapply ordc_trans; eauto.
*
  injection H2 ; intros ; subst.
  constructor; auto.
*
  injection H1 ; intros; subst ; constructor.
Qed.

Lemma ord_antisym :
  forall c1 c2,  ord c1 c2 -> ord c2 c1 ->  c1 = c2.
Proof.
intros c1 c2 Ho1 Ho2.
inversion Ho1 ; inversion Ho2 ; subst ;  try discriminate; auto.
injection H3; intros; subst; injection H4; intros ; subst.
f_equal.
apply ordc_antisym; auto.   
Qed.

Lemma ord_elt_cls : forall e t,
    (exists n,  ordc e (tnth t n)) <-> ord (elt e) (cls (class_of t)).
Proof.
split.
*   
  intros (n & Ho).
  constructor.
  intros t' Hin.
  destruct t as (q & Hq), t' as (q' & Hq').
  cbn in *.
  unfold sim in Hin.
  cbn in Hin.
  destruct (Hin (S (mu e))) as (e' & n' & Ho1 & Ho2 & Hmu) .
  assert (Ho' : ordc e e' \/ ordc e' e).
  {
    apply ordc_wtotal with (z := q (max n n')).
    +
      eapply ordc_trans; eauto.
      destruct Hq as (Hi & _).
      rewrite incr_alt in Hi.
      apply Hi; lia.
    +
      apply ordc_trans with (y := q n'); eauto.
      destruct Hq as (Hi & _).
      rewrite incr_alt in Hi.
      apply Hi; lia.
  }  
  destruct Ho' as [Ho' | Ho'].
  +
    exists n'.
    eapply ordc_trans ; eauto.
  +
    apply mu_ordc in Ho'; lia.
*
  intro Hord.
  inversion Hord; intros; subst.
  apply H1.
  apply sim_refl.
Qed.

Lemma map_elt_increasing : forall (q : Seq(A:=Cc)), increasing ordc q
                                                    -> increasing ord (fun n =>  elt (q n)).
Proof.
intros q Hi n.  
constructor.
now apply Hi.
Qed.


Lemma map_elt_strictly_increasing : forall (q : Seq(A:=Cc)), strictly_increasing ordc q
                                                    -> strictly_increasing ord (fun n =>  elt (q n)).
Proof.
intros q Hi.
destruct Hi as (Hi & Hall).
split.
*
  now apply map_elt_increasing.
*
  intros n Heq.
  apply (Hall n).
  now injection Heq; intros;  subst.
Qed.

Definition asc_subs :=
  ascending_subsequence  Cc ordc ordc_refl ordc_trans ordc_antisym.

Definition subs_iff_asc  :=
  subsequence_iff_ascending  C ord  ord_refl ord_trans ord_antisym.

Lemma map_elt_ascending : forall (q : Seq(A:=Cc)), ascending ordc q
                                                    -> ascending ord (fun n =>  elt (q n)).
Proof.
intros q Hi.
destruct (asc_subs _ Hi) as (q' & Hs' & Hsi').
rewrite subs_iff_asc.
split.
*
  apply map_elt_increasing.
  now destruct Hi as (Hi & _).
*
  destruct Hs'  as (f & Hf & Hall).
  exists (fun n => elt (q' n )).
  split.
  +
    exists  f; split; auto.
    intro n.
    now rewrite Hall.
  +
    now apply map_elt_strictly_increasing.
Qed.

Definition incr_altr :=   (increasing_alt  ord ord_refl ord_trans ord_antisym).

Lemma not_stabilizing_no_cls :
  forall t,  increasing ord t -> ~stabilizing t -> forall c, sin c t ->  exists e,  c = elt e .
Proof.
intros  t Hinc Hn c Hin.
destruct c.
*
  now exists e.
*                   
   exfalso.
   apply Hn ; clear Hn.
   destruct Hin as (i & Heq).
   exists (cls ec) , i.
   intros n Hle.
   rewrite Heq .
   assert (Hlo : ord (t i) (t n)).
   {
     rewrite incr_altr in Hinc.
     apply Hinc; auto.
   }
   rewrite <- Heq in Hlo.
   inversion Hlo; congruence.
Qed.   

Lemma extract_elt_incr: forall t,  increasing ord t -> ~stabilizing t  ->
                                     increasing ordc (fun n => extract_elt (t n)).
Proof.
intros t Hinc Hns.
generalize (not_stabilizing_no_cls _ Hinc Hns) ; intro Hall'.  
intro n.
specialize (Hinc n).
cbn.
inversion Hinc; subst; cbn ; auto; try apply ordc_refl.
exfalso.
specialize (Hall' (cls ec)).
rewrite H0 in Hall'.
destruct (Hall' (sin_nth _ _ )) as (e' & He').
rewrite He' in H0.
discriminate.
Qed. 

Lemma incr_nostab_nostab : forall t, increasing ord  t -> ~ stabilizing t ->
                                  ~ stabilizing (fun n =>  extract_elt (t n)).
Proof.
intros q Hinc Hns Hs.
destruct Hs as (t & (m & Hall)).
apply Hns.
exists (elt t); exists m.
intros n Hle'.
destruct (not_stabilizing_no_cls _ Hinc Hns (q n) (sin_nth _ _  ))
  as (e' & He').
rewrite <- (Hall _ Hle').
now rewrite He'.
Qed.

Definition lim (t: Seq (A := C))(Hinc : increasing ord t) : C := 
  match (excluded_middle_informative (stabilizing t)) with
  | left stab =>
    let (c, _) := constructive_indefinite_description _ stab in c
    |right nostab =>
     (cls (class_of (exist _ (fun n => extract_elt (t n))
                           (conj  ( extract_elt_incr _ Hinc nostab)
                                  ( incr_nostab_nostab _ Hinc nostab))
                                  )))
  end.

Theorem lim_is_upper_bound : forall t c (Hinc : increasing ord t),
    sin c t ->   ord c (lim t Hinc).
Proof.
intros t c incr (n & Heq).
rewrite Heq; clear Heq.
unfold lim.
case (excluded_middle_informative (stabilizing t)); intros Hcas.
*
  cbn.
  destruct (constructive_indefinite_description _ Hcas).
  destruct s as  (m & Hall).
  case (le_gt_dec m n) ; intros Hcas'.
  +
    erewrite <- Hall ; auto.
  +
    apply ord_trans with (c2 :=  t m).
    -
      rewrite incr_altr in incr.
      apply incr ; lia.
    -
      rewrite Hall; auto.
      apply ord_refl.
*
  cbn.
  remember (t n) as c'.
  destruct c'.
  +
    rewrite <- ord_elt_cls.    cbn.
    exists n.
    rewrite <- Heqc'.
    apply ordc_refl.
  +
    exfalso.
    generalize ( not_stabilizing_no_cls _ incr Hcas) ; intros Hall.
    destruct (Hall (t n) (sin_nth _ _)) as (e & Heq).
    rewrite Heq in Heqc'.
    discriminate.
Qed.

Theorem lim_is_least_upper_bound:
  forall t (Hinc : increasing ord t),
    forall w,  (forall c,  sin c t ->   ord c w) ->  ord (lim t Hinc)  w.
Proof.
intros t Hinc w Hsupw.
unfold lim.  
case (excluded_middle_informative (stabilizing t)); intros Hcas.
*
  destruct (constructive_indefinite_description _ Hcas).
  destruct s as (n & Hall).
  specialize (Hall n (Nat.le_refl _)).
  rewrite <- Hall.
  apply Hsupw.
  now exists n.
*
  destruct w as [w | w].
  +
    exfalso.
    generalize (extract_elt_incr _ Hinc Hcas); intro Hinc'.
    generalize(incr_nostab_nostab _ Hinc Hcas); intro Hns'.
    destruct
      (ascending_mu_unbounded _
                              (conj Hinc' Hns') (S (mu w))) as (n & Hn).
    specialize (Hsupw (t n) (sin_nth _ _)).
    inversion Hsupw; subst.
    rewrite <- H in *; cbn in *; clear H.
    apply mu_ordc in H1; lia.
  +
    cbn.
    destruct (class_of_surjective w) as ((s' & Hasc) & Hs') .
    remember ((class_of (exist _ (fun n : nat => extract_elt (t n)) _))) as z.
    assert (Heq : w =z ); [| rewrite Heq ; constructor].
    rewrite <- Hs' , Heqz, <- class_of_compatible.
    apply sim_sym, overtaken_sim.
    intro n.
    specialize (Hsupw (t n) (sin_nth _ _)).
    destruct (not_stabilizing_no_cls _ Hinc Hcas (t n)
                                      (sin_nth _ _)) as (e & Heq).
    cbn.
    rewrite Heq in *.
    now rewrite <- Hs', <-  ord_elt_cls in Hsupw.
Qed.


Section OtherLimProperties.

Lemma lim_ascending_is_cls :
  forall (q : Seq(A := Cc))(Hi : increasing ordc q), ~stabilizing  q ->
            is_cls (lim (fun n => elt (q n)) (map_elt_increasing _ Hi)).
Proof.  
intros q Hi Hns.
generalize (map_elt_ascending _ (conj Hi Hns)); intro Ha.
unfold lim.
destruct (excluded_middle_informative
        (stabilizing
           (fun n : nat =>
              elt (q n)))).
*
  now destruct Ha as (_ & Hs).
*
  constructor.
Qed.


Lemma lim_is_cls_ascending :
  forall (q : Seq(A := Cc))(Hi : increasing ordc q),
    is_cls (lim (fun n => elt (q n)) (map_elt_increasing _ Hi)) ->
    ascending ordc q.
Proof.  
intros q Hi Hcls.
split; auto.  
intro Hs.
unfold lim in Hcls. 
destruct (excluded_middle_informative
        (stabilizing
           (fun n : nat =>
              elt (q n)))).
*
  destruct (constructive_indefinite_description _ s).
  destruct s0 as (m & Hall).
  specialize (Hall _ (Nat.le_refl _)).
  rewrite <- Hall in Hcls.
  inversion Hcls.
*
  clear Hcls.
  apply incr_nostab_nostab in n.
  +
    now apply n.
  +
    now apply map_elt_increasing.
Qed.



Lemma eqv_same_lim :
  forall (q1 q2 : Seq(A := Cc))
         (Hi1 : increasing ordc q1)(Hi2 : increasing ordc q2),
    ~stabilizing  q1 -> ~stabilizing  q2 -> ssim q1 q2 ->
                                   (lim (fun n => elt (q1 n)) (map_elt_increasing _ Hi1)) =
                                   (lim (fun n => elt (q2 n)) (map_elt_increasing _ Hi2)).
Proof.
intros  q1 q2 Hi1 Hi2 Hns1 Hns2 Hs.
unfold  lim.
destruct (excluded_middle_informative
      (stabilizing
         (fun n : nat =>
          elt (q1 n)))); destruct (excluded_middle_informative
      (stabilizing
         (fun n : nat =>
            elt (q2 n)))).
*
  exfalso.
  apply Hns1.
  destruct s as (a & m & Hall).
  exists (extract_elt a), m.
  intros n Hle.
  now erewrite <- Hall; eauto.
*  
  exfalso.
  apply Hns1.
  destruct s as (a & m & Hall).
  exists (extract_elt a), m.
  intros k Hle.
  now erewrite <- Hall; eauto.
*  
  exfalso.
  apply Hns2.
  destruct s as (a & m & Hall).
  exists (extract_elt a), m.
  intros k Hle.
  now erewrite <- Hall; eauto.
*
  f_equal.
  now rewrite <- class_of_compatible.
Qed.

(*
Lemma cls_eq : forall c1 c2,  cls (class_of c1) = cls (class_of c2)
                                   ->   sim c1 c2.
Proof.
intros c1 c2 Heq.
injection Heq ; intros ; subst.
rewrite H.
apply sim_refl.
Qed.
*)

Lemma same_lim_overtakes :
  forall (q1 q2 : Seq(A := Cc))
         (Hi1 : increasing ordc q1)(Hi2 : increasing ordc q2),
    ~stabilizing  q1 -> ~stabilizing  q2 -> 
                                   (lim (fun n => elt (q1 n)) (map_elt_increasing _ Hi1)) =
                                   (lim (fun n => elt (q2 n)) (map_elt_increasing _ Hi2)) ->
                                   forall n, exists m,  ordc (q1 n) (q2 m).
Proof.
intros q1 q2 Hi1 Hi2 Hns1 Hns2 Heqlim n.
remember  (lim (fun n : nat => elt (q1 n))
               (map_elt_increasing q1 Hi1)) as l1.
remember ( lim (fun n : nat => elt (q2 n))
               (map_elt_increasing q2 Hi2)) as l2.
assert (Ho : ord (elt (q1 n)) l2).
{
  rewrite <- Heqlim.
  rewrite Heql1.  
  apply lim_is_upper_bound.
  now exists n.
}
(*generalize  (lim_ascending_is_cls _ Hi1 Hns1); intro Hcls.
destruct Hcls.
intros (ec & Heqec).*)
unfold lim in Heql2.
destruct (excluded_middle_informative
              (stabilizing
                 (fun n : nat => elt (q2 n))));
  [now destruct (map_elt_ascending _ (conj Hi2 Hns2 )) | ].
rewrite Heql2 in Ho.
now rewrite <-  ord_elt_cls in Ho.
Qed.

End OtherLimProperties.

End CPOMod.
