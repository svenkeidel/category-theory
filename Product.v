Set Warnings "-notation-overridden".

Require Export Category.

Set Universe Polymorphism.

Reserved Notation "〈 f , g 〉" (at level 40, left associativity).

Class Product {C:Category} (X Y: Obj[C]) := {
                                             
  product :> Obj[C];

  pi1 : Hom[C] product X;
  pi2 : Hom[C] product Y;

  product_mapping {Z} : Hom[C] Z X -> Hom[C] Z Y -> Hom[C] Z product
    where "〈 f , g 〉" := (product_mapping f g);
  
  product_mapping_respects {Z} : Proper (equiv ==> equiv ==> equiv) (product_mapping (Z:=Z));

  product_ump {Z} (h: Hom[C] Z product) (f: Hom[C] Z X) (g: Hom[C] Z Y) :
    h ≈ 〈f,g〉 ↔ (pi1 ∘ h ≈ f) * (pi2 ∘ h ≈ g)
}.

Notation "〈 f , g 〉" := (product_mapping f g).

Notation "X × Y" := (@product _ X Y _)
  (at level 40, left associativity).

Notation "X ×[ C ] Y" := (@product C X Y _)
  (at level 40, left associativity, only parsing).
