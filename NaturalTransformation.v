Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export Isomorphism.

Set Universe Polymorphism.

Definition natural
  {C D: Category} {F G : Functor C D}
  (eta: forall (X: Obj[C]), Hom[D] (F[X]) (G[X]))
  := forall {X Y: Obj[C]} (f: Hom[C] X Y),
       eta Y ∘ map[F] f ≈ map[G] f ∘ eta X.

(* A natural transformation between two functors F and G is a bundle
of arrows connecting the image of F and G. While functors send
commuting diagrams between categories, natural transformations connect
these diagrams in the image of functors. *)
Class NaturalTransformation {C D: Category} (F G : Functor C D) : Type :=
{
  component X : Hom[D] (F[X]) (G[X]);
  is_natural : natural component
}.

Notation "eta ⟦ X ⟧" :=
  (@component _ _ _ _ eta X%object)
    (at level 35, format "eta ⟦ X ⟧") : arrow_scope.

Notation "natural[ eta ]" :=
  (@is_natural _ _ _ _ eta)
  (at level 35).

Program Instance id_natural_transformation
  {C D: Category}
  (F: Functor C D)
  : NaturalTransformation F F :=
{
  component := fun X => map[F] id[X]
}.
Next Obligation.
  unfold natural.
  intros X Y f.
  repeat (rewrite <- preserves_composition).
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Defined.

Program Instance vertical_composition
  {C D: Category} {F G H: Functor C D}
  (eta: NaturalTransformation G H)
  (theta: NaturalTransformation F G)
  : NaturalTransformation F H :=
{
  component := fun X => eta⟦X⟧ ∘ theta⟦X⟧
}.
Next Obligation.
  unfold natural.
  intros X Y f.
  repeat (rewrite <- preserves_composition).
  rewrite -> compose_associative.
  rewrite (natural[theta]).
  rewrite <- compose_associative.
  rewrite (natural[eta]).
  rewrite -> compose_associative.
  reflexivity.
Defined.

Program Instance horizontal_composition
  {C D E: Category} {F G: Functor C D} {H J: Functor D E}
  (eta: NaturalTransformation F G) (theta: NaturalTransformation H J)
  : NaturalTransformation (compose_functor H F) (compose_functor J G) :=
{
  component := fun X => theta⟦G[X]⟧ ∘ map[H] (eta⟦X⟧)
}.
Next Obligation.
  unfold natural.
  intros X Y f.
  simpl.
  rewrite compose_associative.
  rewrite <- (preserves_composition H (eta⟦Y⟧) (map[F] f)).
  rewrite (natural[eta]).
  rewrite -> preserves_composition.
  rewrite <- compose_associative.
  rewrite (natural[theta]).
  rewrite compose_associative.
  reflexivity.
Defined.

Program Instance natural_setoid
  {C D: Category} {F G: Functor C D}
  : Setoid (NaturalTransformation F G) :=
{
  equiv := fun eta theta => forall X, eta⟦X⟧ ≈ theta⟦X⟧
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros eta X.
    simpl.
    reflexivity.
  - unfold Symmetric.
    intros eta theta eq X.
    rewrite (eq X).
    reflexivity.
  - unfold Transitive.
    intros eta theta iota eq1 eq2 X.
    rewrite (eq1 X).
    rewrite (eq2 X).
    reflexivity.
Defined.