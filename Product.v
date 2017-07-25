Set Warnings "-notation-overridden".
Require Export Category.

Definition exists_unique (A : Type) `{Setoid A} (P : A -> Type) :=
  ({ x : A & P x & forall x' : A, P x' -> x ≈ x'}).

Class Product {C:Category} (X Y: Obj[C]) := {
  product : Obj[C];
  pi1 : Hom[C] product X;
  pi2 : Hom[C] product Y;
  product_ump :
    forall (Z:Obj[C]) (f: Hom[C] Z X) (g: Hom[C] Z Y),
      exists_unique (Hom[C] Z product)
        (fun h => pi1 ∘ h ≈ f ∧ pi2 ∘ h ≈ g)
}.

Notation "X × Y" := (@Product _ X Y)
  (at level 40, left associativity).
