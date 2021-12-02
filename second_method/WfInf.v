Require Import Classical.
Require Import  Wf_nat.

Section Wf_inf.
  Variable A : Type.
  Variable ltA : A -> A -> Prop.
  Hypothesis wf_ltA : well_founded ltA.

  Definition sat (P:A-> Prop) := exists b, P b.
  Definition inf(a:A)(P:A-> Prop) := P a /\ forall b,  P b -> ~ ltA b a.

  Lemma nonempty_inf : forall P, sat P -> exists a, inf a P.
  Proof.
    unfold sat, inf.
    intros.
    destruct H as [b Hex].
    unfold well_founded in *.
    specialize (wf_ltA b).
    induction wf_ltA.
    destruct (classic (exists y, ltA y x /\ P y)).
    * destruct H1 as [y [Hlt HP]]. 
      apply H0 with y ; auto.
    * exists x ; split ; intuition.
      apply H1.
      exists b; intuition.
  Qed.
End Wf_inf.

