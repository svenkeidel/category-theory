Require Export Category.
Require Export Functor.

Generalizable Variables objC C objD D F G.

Definition natural `{Category objC C} `{Category objD D} 
  `{@Functor objC objD F C D _ _} `{@Functor objC objD G C D _ _}
  (component: forall X, D (F X) (G X))
  :=
  forall {X Y:objC} (f: C X Y), component Y ∘ map f == map f ∘ component X.

Class NaturalTransformation `{Category objC C} `{Category objD D} 
  `{@Functor objC objD F C D _ _} `{@Functor objC objD G C D _ _} 
  := {
  component: forall X, D (F X) (G X);
  isNatural: natural component
}.
