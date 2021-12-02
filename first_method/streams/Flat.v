Require Import Classical.
Require Import Classical_Pred_Type.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Arith.Compare.


Require Import Sequences.
Require Import CPO.

 
Inductive leo{A : Type} : option A -> option A -> Prop :=
 leo_None : forall o, leo None o
| leo_Some_Some : forall a,  leo (Some a) (Some a).                                                                      

Lemma leo_refl{A: Type} : forall (a:option A),  leo a a. 
Proof.
  intro a ; destruct a; constructor.
Qed.

Lemma leo_trans{A: Type} : forall (a b c: option A), leo a b -> leo b c -> leo a c.
Proof.
  intros a b c Hl1 Hl2.
  destruct Hl1, Hl2;  constructor.
Qed.

Lemma leo_antisym{A: Type} : forall (a b: option A), leo a b -> leo b a ->  a = b.
Proof.
  intros a b Hl1 Hl2.
  inversion Hl1 ; subst; clear Hl1; inversion Hl2 ; subst; auto.
Qed.

Lemma leo_increasing_snth{A : Type}: forall q ,  increasing leo q  -> forall (i j : nat)(a: A),  i <= j -> q i  = Some a -> q j = Some a.
Proof.
  intros q Hr i j a Hle Hnth.
  eapply increasing_snth in Hle ; eauto ;  [| apply leo_refl | apply leo_trans].
  rewrite Hnth in Hle.
  inversion Hle; auto.
Qed.

Lemma leo_lub{A: Type} :
  forall (q : Seq (A := option A)) , increasing leo q -> exists b,  lub leo b q.
Proof.
intros q Hr.
destruct (classic (forall o,  sin o q -> o = None)).
 *
  exists None.
  split.
  +
    intros a Hin.
    erewrite <- H; eauto.
    apply leo_refl.
  +
    intros s' Hall.
    constructor.
*
  apply not_all_ex_not in H.
  destruct H as (o & Hn).
  apply imply_to_and in Hn.
  destruct Hn as (Hin & Hs).
  destruct o.
  +
    exists (Some a).
    clear Hs.
    split.
    -
      intros o' Hin'.
      destruct o'; try constructor.
      rename a0 into a'.
      destruct Hin as (i & Hsi).
      destruct Hin' as (i' & Hsi').
      case (le_dec i' i) ; intro Hcas.
      **
        rewrite Hsi, Hsi'.
        eapply  increasing_snth ; eauto;
          [apply leo_refl | apply leo_trans ].
      **
        eapply  leo_increasing_snth in Hr;  eauto.
        rewrite Hr in Hsi'.
        rewrite Hsi'.
        apply leo_refl.
    -
      intros s' Hall.
      eapply Hall ; eauto.
  +   
    exfalso ; apply Hs ; auto.
Qed.


Lemma limF{A: Type} :
  forall (q: Seq(A := option A)), increasing leo q -> {b | lub leo b q}.
Proof.
intros.
apply constructive_indefinite_description.
apply leo_lub; auto.
Defined.

Definition flat_cpo {A: Type} :  cpo (A:= option A) eq leo :=
  {|
  bbot := None;
  bbot_is_bottom := leo_None;
  bprefl := leo_refl;
  bptrans := leo_trans ;
  bpantisym := leo_antisym;
  bpsup := leo_lub
  |}.


Inductive lto{A : Type} : option A -> option A -> Prop :=
 lto_None : forall a, lto None (Some a).
