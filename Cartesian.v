Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export Product.
Require Export ProductCategory.
Require Export Cat.

Set Universe Polymorphism.

Class Cartesian (C:Category) : Type := {
  cartesian X Y : Product X Y
}.

Program Instance product_functor (C:Category) {R:Cartesian C}
  : Functor (C ×[Cat] C) C :=
{ map_obj := fun X =>
    @product C _ _ (@cartesian C R (pi1_functor[X]) (pi2_functor[X]));
  map_arr := fun X Y f =>
      (product_mapping (@cartesian C R (pi1_functor[Y]) (pi2_functor[Y]))
        (map[pi1_functor] f ∘ pi1)
        (map[pi2_functor] f ∘ pi2))
}.
Next Obligation.
  unfold Proper; unfold respectful.
  rename o1 into X1.
  rename o2 into Y1.
  rename o into X2.
  rename o0 into Y2.
  intros [f1 f2] [g1 g2] [eq1 eq2].
  simpl in *.
  rewrite eq1.

