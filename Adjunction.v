Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Cat.

Set Universe Polymorphism.

Class UnitCounitAdjunction {C D: Category} (F: Functor C D) (G: Functor D C) := {
  unit: NaturalTransformation (identity_functor C) (G ∘[Cat] F);
  counit: NaturalTransformation (F ∘[Cat] G) (identity_functor D);
  left_identity_law: forall X, counit⟦F[X]⟧ ∘ map[F](unit⟦X⟧) ≈ id[F[X]];
  right_identity_law: forall X, map[G](counit⟦X⟧) ∘ unit⟦G[X]⟧ ≈ id[G[X]]
}.

Class HomsetAdjunction := {
  {C D: Category} (F: Functor C D) (G: Functor D C)
  := (Hom F id[D]) ≅[ (op C ×[Cat] C) \ Sets ] (Hom id[C] G).
}.

