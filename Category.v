Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.RelationClasses.

Reserved Infix "∘" (at level 40, left associativity).

Class Category {obj : Type} (C : obj -> obj -> Type) : Type :=
{
  c_oid :> forall X Y, Setoid (C X Y);

  id : forall (X: obj), C X X;
  compose : forall {X Y Z : obj}, C Y Z -> C X Y -> C X Z
    where "f ∘ g" := (compose f g);

  compose_oid :> forall X Y Z, Proper (equiv ==> equiv ==> equiv) (@compose X Y Z);

  right_identity: forall (X Y:obj) (f: C X Y),
    f ∘ id X == f;

  left_identity: forall X Y (f: C X Y),
    id Y ∘ f == f;

  compose_associative: forall {X Y Z U} (f: C Z U) (g:C Y Z) (h: C X Y),
    (f ∘ g) ∘ h == f ∘ (g ∘ h)
}.

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Hint Resolve right_identity.
Hint Resolve left_identity.
Hint Resolve compose_associative.