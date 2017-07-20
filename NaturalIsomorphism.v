Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Isomorphism.

Definition natural_isomorphic
  {C D: Category} {F G: Functor C D}
  (eta : NaturalTransformation F G)
  (theta: NaturalTransformation G F)
  := forall X, isomorphic (eta⟦X⟧) (theta⟦X⟧).

Lemma id_natural_isomorphism
  {C D: Category} (F: Functor C D)
  : natural_isomorphic (id_natural_transformation F)
                       (id_natural_transformation F).
Proof.
  unfold natural_isomorphic; unfold isomorphic; simpl.
  intros X.
  rewrite <- (preserves_composition (id[X]) (id[X])).
  rewrite right_identity.
  rewrite preserves_identity.
  split; reflexivity.
Qed.

Lemma natural_isomorphic_symmetry
  {C D: Category} {F G: Functor C D}
  (eta : NaturalTransformation F G)
  (theta : NaturalTransformation G F)
  (I: natural_isomorphic eta theta)
  : natural_isomorphic theta eta.
Proof.
  unfold natural_isomorphic in *; unfold isomorphic.
  intros X.
  rewrite (proj1 (I X)).
  rewrite (proj2 (I X)).
  split; reflexivity.
Qed.

Lemma natural_iso_preserved_under_vertical_composition
  {C D: Category}
  {F G H: Functor C D}
  {eta : NaturalTransformation F G}
  {theta : NaturalTransformation G F}
  {eta' : NaturalTransformation G H}
  {theta' : NaturalTransformation H G}
  (I: natural_isomorphic eta theta)
  (J: natural_isomorphic eta' theta')
  : natural_isomorphic (vertical_composition eta' eta)
                       (vertical_composition theta theta').
Proof.
  unfold natural_isomorphic in *; simpl.
  intros X.
  apply (iso (compose_iso (Iso (J X)) (Iso (I X)))).
Qed.