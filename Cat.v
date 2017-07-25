Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export FunctorCategory.

Set Universe Polymorphism.

(* Cat, the category of all categories *)

Ltac build_iso C D F G eta :=
  simple refine (@Build_Isomorphism (functor_category C D) F G
                   (@Build_NaturalTransformation C D F G eta _)
                   (@Build_NaturalTransformation C D G F eta _)
                   _);
  [ unfold natural;
    intros;
    rewrite left_identity;
    rewrite right_identity;
    reflexivity
  | unfold natural;
    intros;
    rewrite left_identity;
    rewrite right_identity;
    reflexivity
  | unfold isomorphic;
    simpl;
    split;
    intros;
    rewrite left_identity;
    repeat (rewrite preserves_identity);
    reflexivity
  ].

Program Instance natural_iso_preserved_under_horizontal_composition
  {C D E: Category}
  {F G: Functor D E}
  {H J: Functor C D}
  (I: F ≅[functor_category D E] G)
  (K: H ≅[functor_category C D] J)
  : compose_functor F H ≅[functor_category C E] compose_functor G J :=
{
  left_inverse := horizontal_composition (left_inverse K) (left_inverse I);
  right_inverse := horizontal_composition (right_inverse K) (right_inverse I)
}.
Next Obligation.
  unfold isomorphic.
  unfold horizontal_composition.
  simpl.
  split.
  - intros X.
    rewrite (natural[right_inverse I]).
    rewrite compose_associative.
    rewrite <- (compose_associative  (map[F] (left_inverse K⟦X⟧))
                                     (map[F] (right_inverse K⟦X⟧))
                                     (right_inverse I⟦J[X]⟧)).
    rewrite <- preserves_composition.
    rewrite (left_inversion K X).
    simpl.
    repeat (rewrite -> preserves_identity).
    rewrite left_identity.
    rewrite (left_inversion I (J[X])).
    simpl.
    rewrite -> preserves_identity.
    reflexivity.
  - intros X.
    rewrite (natural[left_inverse I]).
    rewrite compose_associative.
    rewrite <- (compose_associative  (map[G] (right_inverse K⟦X⟧))
                                     (map[G] (left_inverse K⟦X⟧))
                                     (left_inverse I⟦H[X]⟧)).
    rewrite <- preserves_composition.
    rewrite (right_inversion K X).
    simpl.
    repeat (rewrite -> preserves_identity).
    rewrite left_identity.
    rewrite (right_inversion I (H[X])).
    simpl.
    rewrite -> preserves_identity.
    reflexivity.
Defined.

Program Instance Cat : Category :=
{
  Obj := Category;
  Hom := Functor;
  id := identity_functor;
  hom_setoid := fun C D => obj_setoid (functor_category C D);
  compose := fun _ _ _ => compose_functor
}.
Next Obligation.
  rename X into C.
  rename Y into D.
  rename Z into E.
  unfold Proper; unfold respectful.
  intros F G I.
  intros H J K.
  apply (natural_iso_preserved_under_horizontal_composition I K).
Defined.
Next Obligation.
  rename X into C.
  rename Y into D.
  rename f into F.
  build_iso C D (compose_functor F (identity_functor C)) F (fun X => id[F[X]]).
Defined.
Next Obligation.
  rename X into C.
  rename Y into D.
  rename f into F.
  build_iso C D (compose_functor (identity_functor D) F) F (fun X => id[F[X]]).
Defined. 
Next Obligation.
  rename X into A.
  rename Y into B.
  rename Z into C.
  rename U into D.
  rename f into F.
  rename g into G.
  rename h into H.
  build_iso A D (compose_functor (compose_functor F G) H)
                (compose_functor F (compose_functor G H))
                (fun X => id[F[G[H[X]]]]).
Defined.