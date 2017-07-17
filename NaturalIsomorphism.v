Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Isomorphism.

Generalizable Variables objC C objD D F G.

Definition natural_iso
  `{Category objC C} `{Category objD D} 
  `{@Functor objC objD F C D _ _} `{@Functor objC objD G C D _ _}
  (left_component: forall X, D (F X) (G X))
  (right_component: forall X, D (G X) (F X))
  := natural left_component /\ natural right_component
     /\ forall X, iso (left_component X) (right_component X).

Class NaturalIsomorphism
  `{Category objC C} `{Category objD D} 
  `{@Functor objC objD F C D _ _} `{@Functor objC objD G C D _ _} 
  := {
  left_component: forall X, D (F X) (G X);
  right_component: forall X, D (G X) (F X);
  isNaturalIso: natural_iso left_component right_component
}.

Program Instance FunctorSetoid `{Category objC C} `{Category objD D}
  : Setoid ({ F : objC -> objD & @Functor objC objD F C D _ _ }) :=
{ equiv := fun F_ G_ =>
  match F_, G_ with
  | existT _ F FN, existT _ G GN =>
    exists (_:@NaturalIsomorphism objC C _ objD D _ F FN G GN), True
  end
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros [F F_].
    destruct.