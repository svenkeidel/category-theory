Set Warnings "-notation-overridden".

Require Export CSetoid.

Set Universe Polymorphism.

Reserved Infix "∘" (at level 40, left associativity).

(* A category is a collection of objects and a collection of arrows
between these objects. *)
Class Category : Type :=
{
  Obj : Type;
  Hom : Obj -> Obj -> Type;

  id {X} : Hom X X;
  compose { X Y Z } : Hom Y Z -> Hom X Y -> Hom X Z
    where "f ∘ g" := (compose f g);

  hom_setoid :> forall X Y, Setoid (Hom X Y);
  compose_respects {X Y Z} :> Proper (equiv ==> equiv ==> equiv) (@compose X Y Z);

  right_identity {X Y} (f: Hom X Y) : f ∘ id ≈ f;

  left_identity {X Y} (f: Hom X Y) : id ∘ f ≈ f;

  compose_associative {X Y Z U} (f: Hom Z U) (g: Hom Y Z) (h: Hom X Y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
}.

Bind Scope category_scope with Category.
Bind Scope object_scope with Obj.
Bind Scope homset_scope with Hom.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope homset_scope with homset.
Delimit Scope arrow_scope with arrow.



Notation "Obj[ C ]" := (@Obj C%category)
  (at level 0, format "Obj[ C ]") : object_scope.

Notation "Hom[ C ]" := (@Hom C%category)
  (at level 0, format "Hom[ C ]") : homset_scope.

Notation "id[ X ]" := (@id _%category X%object)
  (at level 9, format "id[ X ]") : arrow_scope.

Notation "f ∘ g" :=
  (@compose _%category _%object _%object _%object f%arrow g%arrow)
  : arrow_scope.

Notation "f ∘[ C ] g" :=
  (@compose C%category _%object _%object _%object f%arrow g%arrow)
  (at level 40, left associativity, only parsing) : arrow_scope.

Open Scope category_scope.
Open Scope object_scope.
Open Scope homset_scope.
Open Scope arrow_scope.

Hint Rewrite @right_identity.
Hint Rewrite @left_identity.
Hint Resolve right_identity.
Hint Resolve left_identity.
Hint Resolve compose_associative.