Require Import Sequences.

Record cpo{A : Type}(eqR : A -> A -> Prop)(R: A -> A -> Prop) :=
  {
  bbot : A ;
  bbot_is_bottom : forall a,  R bbot a ;
  bprefl : forall a,  R a a ;
  bptrans : forall a b c,  R a b -> R b c -> R a c ;
  bpantisym : forall a b,  R a b -> R b a -> eqR a b ;
  bpsup :  forall q, increasing R q -> exists b,  sup R b q
 }.
