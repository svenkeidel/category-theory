Set Warnings "-notation-overridden".

Require Export Category.
Require Export Isomorphism.

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

Lemma product_unique_up_to_iso
  {C:Category}
  {X Y: Obj[C]}
  (p q: Product X Y)
  : product (Product:= p) ≅ product (Product:= q).
Proof.
  simple refine (@Build_Isomorphism _ _ _ _ _ _).
  - apply (product_mapping (Product:=q) (pi1 (Product:=p)) (pi2 (Product:=p))).
  - apply (product_mapping (Product:=p) (pi1 (Product:=q)) (pi2 (Product:=q))).
  - unfold isomorphic.
    simpl.
    split.
    + Unset Printing Notations.
      Set Printing Implicit.
      Check product_ump.
      idtac.
      