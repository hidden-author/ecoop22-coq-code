Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import IndefiniteDescription.


Module Type EqvMod.
Parameter T : Type.
Parameter sim : T -> T -> Prop.

Parameter sim_refl : forall x,  sim x x.
Parameter sim_sym : forall x y, sim x y -> sim y x.
Parameter sim_trans : forall x y z, sim x y -> sim y z ->  sim x z.

End EqvMod.


Module EqvClassesMod (Eqv : EqvMod).
Import Eqv.

Definition EqClass : Type :=
{c : T -> Prop |
  (exists x, c x) /\
  (forall x y, c x -> c y -> sim x y) /\
  (forall x y, c x -> sim x y -> c y)
}.
 
Definition class_of (x : T) : EqClass :=
exist
  (fun c : T -> Prop =>
    (exists x, c x) /\
    (forall x y : T, c x -> c y -> sim x y) /\
    (forall x y, c x -> sim x y -> c y))
  (sim x)
  (conj
    (ex_intro (fun y => sim x y) x (sim_refl x))
    (conj
      (fun y z Hxy => sim_trans y x z (sim_sym x y Hxy))
      (sim_trans x))).


Lemma class_of_compatible : forall x y, sim x y <-> class_of x = class_of y.
Proof.
intros x y.
unfold class_of.
  split.
- intro Hxy.
  apply eq_exist_uncurried.
  unshelve eexists; [ | apply proof_irrelevance].
  extensionality z.
  apply propositional_extensionality.
  split.
  + intro Hxz.
    apply sim_trans with x; [apply sim_sym, Hxy | apply Hxz].
  + intro Hyz.
    apply sim_trans with y; [apply Hxy | apply Hyz].
- intro Heq.
  injection Heq.
  clear Heq.
  intro Heq.
  rewrite Heq.
  apply sim_refl.
Qed.

Lemma class_of_surjective : forall c, exists x, class_of x = c.
Proof.
intros (c & [x Hx] & Hrelated & Hfull).
exists x.
unfold class_of.
apply eq_exist_uncurried.
unshelve eexists; [ | apply proof_irrelevance].
extensionality y.
apply propositional_extensionality.
split.
- intro Hequiv.
  apply Hfull with x; [exact Hx | exact Hequiv].
- intro Hy.
  apply Hrelated; [exact Hx | exact Hy].
Qed.

Program Definition representative (x : EqClass) : Eqv.T :=
proj1_sig (constructive_indefinite_description (proj1_sig x) _).
Next Obligation.
destruct (proj2_sig x) as [H _].
exact H.
Qed.

Lemma sim_representative : forall x,
                           sim (representative (class_of x))  x.
Proof.
intro x.
unfold representative.
cbn.
remember (constructive_indefinite_description 
          (sim x)
          (representative_obligation_1 (class_of x))) as y.
destruct y.
now apply sim_sym.
Qed.
     
End EqvClassesMod.      

