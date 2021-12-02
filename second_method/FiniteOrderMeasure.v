Module Type FiniteOrderMeasureMod.

Parameter Cc : Type.

Parameter bot : Cc.
                  
Parameter ordc : Cc -> Cc -> Prop. 

Parameter bot_is_bot : forall x, ordc bot x.

Parameter ordc_refl : forall x, ordc x x.

Parameter ordc_trans : forall x y z,  ordc x y -> ordc y z -> ordc x z.

Parameter ordc_antisym : forall x y,  ordc x y -> ordc  y x -> x = y.

Parameter ordc_wtotal : forall x y z,  ordc x z -> ordc y z -> (ordc x y \/ ordc y x).

Parameter mu : Cc -> nat.

Parameter mu_sordc : forall x y, ordc x y -> x <> y -> mu x < mu y.

End FiniteOrderMeasureMod.
