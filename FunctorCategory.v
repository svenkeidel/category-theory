Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.

Program Instance functor_category (C D: Category) :
  Category :=
{
  Obj := Functor C D;
  Hom := NaturalTransformation;
  id := id_natural_transformation;
  compose := fun _ _ _ => vertical_composition 
}.
Next Obligation.
  unfold Proper; unfold respectful.
  rename X into F.
  rename Y into G.
  rename Z into H.
  intros eta eta' eq theta theta' eq' X.
  simpl.
  rewrite (eq X).
  rewrite (eq' X).
  reflexivity.
Defined.
Next Obligation.
  rewrite preserves_identity.
  rewrite right_identity.
  reflexivity.
Defined.
Next Obligation.
  rewrite preserves_identity.
  rewrite left_identity.
  reflexivity.
Defined.
Next Obligation.
  rewrite compose_associative.
  reflexivity.
Defined.

Notation "C \ D" := (functor_category C%category D%category)
  (at level 40, left associativity) : category_scope.