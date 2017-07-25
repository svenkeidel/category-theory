Require Export Category.
Require Export Functor.
Require Export Opposite.
Require Export ProductCategory.
Require Export Sets.

Program Instance Hom
  `{C:Category}
  : Functor (op C × C) Sets :=
{
  map_obj := fun X => Build_SomeSet (Hom[C] (fst X) (snd X)) hom_setoid;
  map_arr := fun _ _ f => {| function := fun h => snd f ∘ h ∘ fst f |}
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros f f' eq1. simpl. rewrite eq1.
  reflexivity.
Defined.
Next Obligation.
  unfold Proper; unfold respectful.
  intros f f' [eq1 eq2] h.
  simpl in *.
  rewrite eq1. rewrite eq2.
  reflexivity.
Defined.
Next Obligation.
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Defined.
Next Obligation.
  simpl in *.
  repeat (rewrite compose_associative).
  reflexivity.
Defined.
  
