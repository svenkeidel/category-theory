Set Warnings "-notation-overridden".

Require Export Category.
Require Export Sets.
Require Export Isomorphism.
Require Export Cat.
Require Export HomFunctor.
Require Export DiagonalFunctor.
Require Export ConstantFunctor.

Set Universe Polymorphism.

Class Product {C:Category} (X Y: Obj[C]) := {
  product :> Obj[C];
  product_mapping:
    HomOp (diag C) (constant (D:=product_category C C) (X,Y))
    ≅[ product_category (op C) C \ Sets]
    HomOp (identity_functor _) (constant product);
}.

Definition pi1 {C:Category} {X Y: Obj[C]} {P:Product X Y} : Hom[C] product X
  := fst (function (right_inverse product_mapping ⟦(@product _ _ _ P,X)⟧) id[product]).

Definition pi2 {C:Category} {X Y: Obj[C]} {P:Product X Y} : Hom[C] product Y
  := snd (function (right_inverse product_mapping ⟦(@product _ _ _ P,X)⟧) id[product]).

Notation "X × Y" := (@product _ X Y _)
  (at level 40, left associativity).

Notation "X ×[ C ] Y" := (@product C X Y _)
  (at level 40, left associativity, only parsing).
