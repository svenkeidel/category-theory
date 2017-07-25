Require Export Category.

Program Instance op (C: Category) : Category :=
{
  Obj := Obj[C];
  Hom := fun X Y => Hom[C] Y X;
  id  := fun X => id[X];
  compose := fun _ _ _ f g => g ∘ f
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros f f' eq1 g g' eq2.
  rewrite eq1; rewrite eq2.
  reflexivity.
Defined.
Next Obligation.
  rewrite compose_associative.
  reflexivity.
Defined.
