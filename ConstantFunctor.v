Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.

Set Universe Polymorphism.

Program Instance constant {C D:Category} (X: Obj[D])
  : Functor C D :=
{
  map_obj := fun _ => X;
  map_arr := fun _ _ _ => id[X]
}.
Next Obligation.
  unfold Proper; unfold respectful. intros. reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  rewrite right_identity.
  reflexivity.
Defined.

Program Instance constant_nat {C D:Category}
  {X Y} (f: Hom[D] X Y)
  : NaturalTransformation (C:=C) (constant X) (constant Y)
  :=
{
  component := fun _ => f
}.
Next Obligation.
  unfold natural.
  intros.
  simpl.
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Defined.
