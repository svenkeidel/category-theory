Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export Opposite.
Require Export ProductCategory.
Require Export Sets.
Require Export Cat.
Require Export Simplify.

Set Universe Polymorphism.

Program Instance Hom {C:Category}
  : Functor (product_category (op C) C) Sets :=
{
  map_obj := fun X => {| carrier := Hom[C] (fst X) (snd X) |};
  map_arr := fun _ _ f => {| function := fun h => snd f ∘ h ∘ fst f |}
}.
Next Obligation.
  simplify.
Defined.
Next Obligation.
  simplify.
Defined.
Next Obligation.
  simplify.
Defined.
Next Obligation.
  simplify.
Defined.

Definition HomF {A B C:Category}
  (F:Functor A (op C)) (G:Functor B C)
  : Functor (product_category A B) Sets
  := Hom ∘[Cat] product_functor F G.

Definition HomOp {A B C:Category}
  (F:Functor A C) (G:Functor B C)
  : Functor (product_category (op A) B) Sets
  := HomF (Op F) G.