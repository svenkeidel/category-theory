Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Isomorphism.

Generalizable Variables objC HomC C objD HomD D objE HomE E F₀ G₀ H₀ J₀ eta₁ theta₁.

Definition NaturalIsomorphism
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D}
  `{eta: eta₁ :: F ≈> G} `{theta: theta₁ :: G ≈> F}
  := forall X, Isomorphism (eta₁ X) (theta₁ X).

Notation "[ eta ] F <≈> G [ theta ]"
  := (@NaturalIsomorphism _ _ _ _ _ _ _ F _ G _ eta _ theta)
       (at level 40, left associativity) : category_scope.

Notation "F ≊ G" :=
  ({ f : prod (∃ F ≈> G) (∃ G ≈> F) &
         @NaturalIsomorphism _ _ _ _ _ _ _ F _ G
                             (projT1 (fst f)) (projT2 (fst f))
                             (projT1 (snd f)) (projT2 (snd f)) })
    (at level 40, left associativity) : category_scope.

Definition natural_iso_symmetry
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D}
  `{eta: eta₁ :: F ≈> G} `{theta: theta₁ :: G ≈> F}
  (I: [ eta ] F <≈> G [ theta ])
  : [ theta ] G <≈> F [ eta ].
Proof.
  unfold NaturalIsomorphism in *.
  intros X.
  apply (iso_symmetry (I X)).
Defined.

Definition id_natural_isomorphism
  `{C: Category objC HomC}
  `{D: Category objD HomD}
  `{F: F₀ :: C ~> D}
  : [ id_natural_transformation F ] F <≈> F [ id_natural_transformation F ].
Proof.
  unfold NaturalIsomorphism.
  intros X.
  unfold Isomorphism.
  repeat split;
    rewrite <- (preserves_composition (id X) (id X));
    rewrite right_identity;
    rewrite preserves_identity;
    reflexivity.
Defined.
Arguments id_natural_isomorphism
          {objC HomC C} {objD HomD D} {F₀} F _ : assert.

Definition vertical_composition_iso
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D} `{H: H₀ :: C ~> D}
  `{eta: eta₁ :: G ≈> H} `{eta': eta₁' :: H ≈> G}
  `{theta: theta₁ :: F ≈> G} `{theta': theta₁' :: G ≈> F}
  (I: [ eta ] G <≈> H [ eta' ])
  (J: [ theta ] F <≈> G [ theta' ])
  :  [ vertical_composition eta theta ]
     F <≈> H
     [ vertical_composition theta' eta' ].
Proof.
  unfold NaturalIsomorphism in *.
  intros X.
  apply (compose_iso (I X) (J X)).
Defined.
Arguments vertical_composition_iso
          {objC HomC C} {objD HomD D}
          {F₀ F} {G₀ G} {H₀ H}
          {eta₁ eta} {eta₁' eta'}
          {theta₁ theta} {theta₁' theta'}
          I J _ : assert.

Definition horizontal_composition_iso
  `{C: Category objC HomC} `{D: Category objD HomD} `{E: Category objE HomE}
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D} `{H: H₀ :: D ~> E} `{J: J₀ :: D ~> E}
  `{eta: eta₁ :: F ≈> G} `{eta': eta₁' :: G ≈> F}
  `{theta: theta₁ :: H ≈> J} `{theta': theta₁' :: J ≈> H}
  (N: [ eta ] F <≈> G [ eta' ]) (M: [ theta ] H <≈> J [ theta' ]) :
  [ horizontal_composition eta theta ] (Compose H F) <≈> (Compose J G) [ horizontal_composition eta' theta' ].
Proof.
  unfold NaturalIsomorphism.
  unfold Isomorphism.
  intros X.
  split.
  - rewrite theta'.
    rewrite compose_associative.
    rewrite <- (compose_associative (map H (eta₁ X)) (map H (eta₁' X)) (theta₁' (G₀ X))).
    rewrite <- (preserves_composition (Functor:=H)).
    rewrite -> (left_inversion (N X)).
    rewrite preserves_identity.
    rewrite left_identity.
    rewrite -> (left_inversion (M (G₀ X))).
    reflexivity.
  - rewrite theta.
    rewrite compose_associative.
    rewrite <- (compose_associative (map J (eta₁' X)) (map J (eta₁ X)) (theta₁ (F₀ X))).
    rewrite <- (preserves_composition (Functor:=J)).
    rewrite -> (right_inversion (N X)).
    rewrite preserves_identity.
    rewrite left_identity.
    rewrite -> (right_inversion (M (F₀ X))).
    reflexivity.
Defined.

Definition exists_natural_iso
  `{C: Category objC HomC} `{D: Category objD HomD}
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D}
  `{eta: ∃ F ≈> G} `{theta: ∃ G ≈> F}
  (I: forall X, Isomorphism (projT1 eta X) (projT1 theta X))
  : F ≊ G.
  destruct eta as [eta₁ eta].
  destruct theta as [theta₁ theta].
  simpl in I.
  exists (exists_natural_trans eta,
          exists_natural_trans theta).
  unfold NaturalIsomorphism.
  intros X.
  simpl.
  apply (I X).
Defined.

Program Instance FunctorSetoid
  `{C: Category objC HomC} `{D: Category objD HomD}
  : Setoid (∃ C ~> D) :=
{ equiv := fun X Y =>
  match X, Y with
  | existT _ F₀ F, existT _ G₀ G =>
    exists (f : prod (∃ F ≈> G) (∃ G ≈> F)),
    @NaturalIsomorphism objC HomC C objD HomD D F₀ F G₀ G
                        (projT1 (fst f)) (projT2 (fst f))
                        (projT1 (snd f)) (projT2 (snd f))
  end
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros [F₀ F].
    exists (exists_natural_trans (id_natural_transformation (F₀:=F₀) F),
            exists_natural_trans (id_natural_transformation (F₀:=F₀) F)).
    apply (id_natural_isomorphism (F₀:=F₀) F).
  - unfold Symmetric.
    intros [F₀ F] [G₀ G] [[eta theta] I].
    exists (theta, eta).
    apply (natural_iso_symmetry I).
  - unfold Transitive.
    intros [F₀ F] [G₀ G] [H₀ H] [[[eta₁ eta] [eta₁' eta']] I].
    intros [[[theta₁ theta] [theta₁' theta']] J].
    simpl in *.
    exists (exists_natural_trans (vertical_composition theta eta),
            exists_natural_trans (vertical_composition eta' theta')).
    apply (vertical_composition_iso (F₀:=F₀) J I).
Defined.