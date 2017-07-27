Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export Simplify.

Set Universe Polymorphism.

Program Instance op (C: Category) : Category :=
{
  Obj := Obj[C];
  Hom := fun X Y => Hom[C] Y X;

  id  := fun X => id[X];
  compose := fun _ _ _ f g => g ∘ f;
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

Program Instance Op {C D: Category} (F: Functor C D)
  : Functor (op C) (op D) :=
{
  map_obj := fun X => F[X];
  map_arr := fun _ _ f => map[F] f
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

