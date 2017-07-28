Set Warnings "-notation-overridden".

Require Export Category.
Require Export Simplify.

Set Universe Polymorphism.

Global Program Instance product_category (C D : Category) : Category :=
{
  Obj := (Obj[C] * Obj[D])%type;
  Hom := fun X Y => (Hom[C] (fst X) (fst Y) * Hom[D] (snd X) (snd Y))%type;

  id := fun X => (id[fst X], id[snd X]);
  compose := fun X Y Z f g => (fst f ∘ fst g, snd f ∘ snd g);
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros [f f'] [g g'] [eq1 eq1'] [h h'] [j j'] [eq2 eq2'].
  simpl in *.
  split; [rewrite eq1; rewrite eq2 | rewrite eq1'; rewrite eq2' ]; reflexivity.
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

Program Instance product_functor {A B C D: Category}
  (F:Functor A C) (G:Functor B D) :
  Functor (product_category A B) (product_category C D)  :=
{
  map_obj := fun X => (F[fst X], G[snd X]);
  map_arr := fun _ _ f => (map[F](fst f),map[G](snd f))
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros [f1 f2] [g1 g2] [eq1 eq2].
  simpl in *.
  split; [rewrite eq1 | rewrite eq2]; reflexivity.
Defined.
Next Obligation.
  simplify.
Defined.
Next Obligation.
  simplify.
Defined.

