Definition Seq{A:Type} := nat -> A.


Definition sin{A : Type}(a : A)(q: Seq(A:=A)) := exists i, a = q i.

Lemma sin_nth{A:Type}(q: Seq(A:=A)): forall n,  sin (q n) q.
Proof.
intro n.
now exists n.
Qed.

Definition increasing {A: Type} (R: A -> A -> Prop)(q : Seq) : Prop  :=
  forall n,  R (q n) (q (S n)).


Definition strictly_increasing{A : Type}(R: A -> A -> Prop)(q : Seq(A := A)) :=
  increasing R q /\
forall n,  ~R (q (S n)) (q n).


Lemma increasing_snth{A : Type}
      (R : A -> A -> Prop)
      (RRefl : forall a,  R a a)
      (Rtrans : forall a b c,  R a b -> R b c -> R a c)
  : forall (q: Seq (A := A)),
    increasing R q  -> forall (i j : nat),  i <= j -> R (q i) (q j).
Proof.
intros q Hr i j Hle.
induction Hle.
*
  apply RRefl.
*
  specialize (Hr m).
  eapply Rtrans  ; eauto.
Qed.


Definition sup{A: Type} (R : A -> A-> Prop) (sup_val: A) (q : Seq(A:=A)) :=
  (forall a, sin a q -> R a sup_val) /\
  (forall sup_val',  (forall a, sin a q -> R a sup_val')  -> R sup_val sup_val').
