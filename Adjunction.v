Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Isomorphism.
Require Export HomFunctor.

Definition Adjunction
  {C D: Category} (F: Functor C D) (G: Functor D C)
  := Isomorphism (Hom (F X) Y) (HomD X (G Y))).


