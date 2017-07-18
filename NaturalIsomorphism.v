Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Isomorphism.

Generalizable Variables objC C objD D F G.

Definition NaturalIsomorphism
  `{Category objC C} `{Category objD D} 
  `{F :: C ~> D} `{G :: C ~> D}
  (eta: forall X, D (F X) (G X))
  (theta: forall X, D (G X) (F X))
  := (eta :: F ≈> G) /\ (theta :: G ≈> F)
     /\ forall X, Isomorphism (eta X) (theta X).

Program Instance FunctorSetoid
  `{C': Category objC C} `{D': Category objD D}
  : Setoid ({ F : objC -> objD & F :: C ~> D }) :=
{ equiv := fun X Y =>
  match X, Y with
  | existT _ F F', existT _ G G' =>
      exists f g, @NaturalIsomorphism objC C C' objD D D' F F' G G' f g
  end
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros [F F_].
    exists (forall X, (id (F X))).