Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.RelationClasses.

Reserved Infix "∘" (at level 40, left associativity).

Class Category {obj : Type} (Hom : obj -> obj -> Type) : Type :=
{
  c_oid :> forall X Y, Setoid (Hom X Y);

  id : forall (X: obj), Hom X X;
  compose : forall {X Y Z : obj}, Hom Y Z -> Hom X Y -> Hom X Z
    where "f ∘ g" := (compose f g);

  compose_oid :> forall X Y Z, Proper (equiv ==> equiv ==> equiv) (@compose X Y Z);

  right_identity: forall (X Y:obj) (f: Hom X Y),
    f ∘ id X == f;

  left_identity: forall X Y (f: Hom X Y),
    id Y ∘ f == f;

  compose_associative: forall {X Y Z U} (f: Hom Z U) (g: Hom Y Z) (h: Hom X Y),
    (f ∘ g) ∘ h == f ∘ (g ∘ h)
}.

Notation "f ∘ g" := (@compose _ _ _ _ _ _ f g) (at level 40, left associativity) : category_scope.
Open Scope category_scope.

Hint Resolve right_identity.
Hint Resolve left_identity.
Hint Resolve compose_associative.