Require Export Category.

Generalizable Variables objC HomC C objD HomD D.

Program Instance product_setoid
  `{C: Category objC HomC} `{D: Category objD HomD}
  (X Y : objC) (X' Y' : objD)
  : Setoid (HomC X Y * HomD X' Y') :=
{
  equiv := fun f g => fst f == fst g /\ snd f == snd g
}.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive.
    intros [f g].
    simpl.
    split; reflexivity.
  - unfold Symmetric.
    intros [f g] [f' g'] [eq1 eq2].
    simpl.
    rewrite eq1; rewrite eq2.
    simpl.
    split; reflexivity.
  - unfold Transitive.
    intros [f g] [f' g'] [f'' g''] [eq1 eq2] [eq1' eq2'].
    simpl in *.
    rewrite eq1. rewrite eq1'.
    rewrite eq2. rewrite eq2'.
    split; reflexivity.
Defined.

Program Instance product_category
  `{C: Category objC HomC} `{D: Category objD HomD}
  : Category (obj:= (objC * objD)%type)
             (fun X Y => (HomC (fst X) (fst Y) * HomD (snd X) (snd Y))%type) :=
{
  c_oid := fun X Y => product_setoid (C:=C) (D:=D) (fst X) (fst Y) (snd X) (snd Y);
  id := fun X => (id (fst X), id (snd X));
  compose := fun X Y Z f g => (fst f ∘ fst g, snd f ∘ snd g)
}.
Next Obligation.
  unfold Proper. unfold respectful.
  intros [f f'] [g g'] [eq1 eq1'] [h h'] [j j'] [eq2 eq2'].
  simpl in *.
  rewrite eq1.
  rewrite eq2.
  rewrite eq1'.
  rewrite eq2'.
  split; reflexivity.
Defined.

Notation "C × D" := (@product_category _ _ C _ _ D) (at level 40, left associativity) : category_scope.

