Require Export Category.
Require Export Functor.

Generalizable Variables objC C objD D F G.

Definition NaturalTransformation
  `{Category objC C} `{Category objD D} 
  (F : objC -> objD) `{F :: C ~> D}
  (G : objC -> objD) `{G :: C ~> D}
  (eta: forall (X:objC), D (F X) (G X))
  := forall {X Y:objC} (f: C X Y), eta Y ∘ map f == map f ∘ eta X.
Notation "eta :: F ≈> G" := (@NaturalTransformation _ _ _ _ _ _ F _ G _ eta) (at level 40, left associativity).