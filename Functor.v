Require Export Category.

Class Functor {objC objD : Type} (F : objC -> objD) (C : objC -> objC -> Type) (D: objD -> objD -> Type) `{Category objC C} `{Category objD D} :=
{
  map : forall {X Y}, C X Y -> D (F X) (F Y);
  map_oid :> forall X Y, Proper (equiv ==> equiv) (map (X:=X) (Y:=Y));
  preserves_identity: forall X, map (id X) == id (F X);
  preserves_composition: forall {X Y Z} (f : C Y Z) (g : C X Y), map (f ∘ g) == map f ∘ map g
}.

(* Arguments map {objC objD F C D H H0} Functor {X Y} _. *)
(* Arguments preserves_identity {objC objD F C D H H0} Functor X. *)
(* Arguments preserves_composition {objC objD F C D H H0} Functor {X Y Z}. *)
      