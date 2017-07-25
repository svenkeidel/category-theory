Set Warnings "-notation-overridden".

Require Export Category.

Set Universe Polymorphism.

(* Functors are mappings between categories that preserve the structure of categories, i.e. identities and composition. *)
Class Functor (C: Category) (D: Category) :=
{
  map_obj :> Obj[C] -> Obj[D];
  map_arr : forall {X Y}, Hom[C] X Y -> Hom[D] (map_obj X) (map_obj Y);

  map_respects :> forall X Y, Proper (equiv ==> equiv) (map_arr (X:=X) (Y:=Y));

  preserves_identity: forall X, map_arr (id[X]) ≈ id[map_obj X];
  preserves_composition:
    forall {X Y Z} (f : Hom[C] Y Z) (g : Hom[C] X Y),
      map_arr (f ∘ g) ≈ map_arr f ∘ map_arr g
}.

Arguments preserves_identity {C D} _ {X} : assert.

Notation "F [ X ]" := (@map_obj _%category _%category F X)
  (at level 0, format "F [ X ]") : object_scope.

Notation "map[ F ]" := (@map_arr _%category _%category F _ _)
  (at level 0, format "map[ F ]") : arrow_scope.

Program Instance identity_functor (C:Category) : Functor C C :=
{ map_obj := fun x => x;
  map_arr := fun X Y f => f
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros x y eq.
  apply eq.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Instance compose_functor
  {C D E:Category} (F: Functor D E) (G: Functor C D)
  : Functor C E :=
{
  map_obj := fun X => F[G[X]];
  map_arr := fun x y f => map[F] (map[G] f)
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros f g eq.
  enough (forall (X Y:Obj[D]) (f g : Hom[D] X Y), f ≈ g -> map[F] f ≈ map[F] g) as H.
  apply H.
  rewrite eq.
  apply reflexivity.
  intros X' Y' f' g' eq'.
  rewrite eq'.
  apply reflexivity.
Defined.
Next Obligation.
  rewrite preserves_identity.
  rewrite preserves_identity.
  reflexivity.
Defined.
Next Obligation.
  rewrite preserves_composition.
  rewrite preserves_composition.
  reflexivity.
Defined.
