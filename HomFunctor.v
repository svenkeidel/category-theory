Require Export Category.
Require Export Functor.
Require Export Opposite.
Require Export ProductCategory.
Require Export Sets.

Generalizable Variables objC HomC C F₀.

Program Instance Hom
  `{C:Category objC HomC}
  : (fun X => HomC (fst X) (snd X)) :: op C × C ~> Sets :=
{
  map := fun _ _ f h => snd f ∘ h ∘ fst f
}.
Next Obligation.
  unfold Proper. unfold respectful.
  intros [f f'] [g g'] [eq1 eq2] h.
  simpl in *.
  Set Printing Implicit.
  Unset Printing Notations.
  idtac.
  rewrite eq1.
  
