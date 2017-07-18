Require Export Category.

Class Functor
 {objC : Type} (C : objC -> objC -> Type) `{Category objC C}
 {objD : Type} (D : objD -> objD -> Type) `{Category objD D}
 (F : objC -> objD) :=
{
  map : forall {X Y}, C X Y -> D (F X) (F Y);
  map_oid :> forall X Y, Proper (equiv ==> equiv) (map (X:=X) (Y:=Y));
  preserves_identity: forall X, map (id X) == id (F X);
  preserves_composition: forall {X Y Z} (f : C Y Z) (g : C X Y), map (f ∘ g) == map f ∘ map g
}.
Notation "F :: C ~> D" := (@Functor _ C _ _ D _ F) (at level 40, left associativity).