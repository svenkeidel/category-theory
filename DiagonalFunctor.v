Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export FunctorCategory.
Require Export ConstantFunctor.
Require Export ProductCategory.
Require Export Simplify.

Set Universe Polymorphism.

Program Instance diagonal {J C:Category}
  : Functor C (C \ J) :=
{ map_obj := fun X => constant X;
  map_arr := fun _ _ f => constant_nat f
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

Program Instance diag (C:Category) : Functor C (product_category C C) :=
{
  map_obj := fun X => (X,X);
  map_arr := fun _ _ f => (f,f)
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
