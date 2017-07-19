Require Export Category.

Class Functor
 {objC : Type} {HomC : objC -> objC -> Type} `{C: Category objC HomC}
 {objD : Type} {HomD : objD -> objD -> Type} `{D: Category objD HomD}
 (F₀ : objC -> objD) :=
{
  map : forall {X Y}, HomC X Y -> HomD (F₀ X) (F₀ Y);
  map_oid :> forall X Y, Proper (equiv ==> equiv) (map (X:=X) (Y:=Y));
  preserves_identity: forall X, map (id X) == id (F₀ X);
  preserves_composition: forall {X Y Z} (f : HomC Y Z) (g : HomC X Y), map (f ∘ g) == map f ∘ map g
}.
Notation "F :: C ~> D" := (@Functor _ _ C _ _ D F) (at level 40, left associativity) : category_scope.
Notation "∃ C ~> D" := ({ F : _ & F :: C ~> D}) (at level 50, left associativity) : category_scope.
Arguments map {objC HomC C objD HomD D F₀ } Functor { X Y } _: assert.

Generalizable Variables objC HomC C objD HomD D objE HomE E F₀ G₀ H₀ eta theta.

Definition Id₀ {obj} (X:obj) := X.

Program Instance Id `{C:Category objC HomC} : Id₀ :: C ~> C :=
{ map := fun X Y f => f
}.
Next Obligation.
  unfold Proper.
  unfold respectful.
  intros x y eq. rewrite eq.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Definition Compose₀ {objC objD objE} (F: objD -> objE) (G: objC -> objD) (X:objC) : objE :=
  F (G X).

Program Instance Compose
  `{C:Category objC HomC} `{D: Category objD HomD} `{E: Category objE HomE}
  `{F: F₀ :: D ~> E} `{G: G₀ :: C ~> D}
  : (Compose₀ F₀ G₀) :: C ~> E :=
{ map := fun x y f => map F (map G f) }.
Next Obligation.
  unfold Proper.
  unfold respectful.
  intros f g eq.
  enough (forall (X Y:objD) (f g : HomD X Y), f == g -> map F f == map F g).
  apply H.
  rewrite eq.
  reflexivity.
  intros.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  rewrite preserves_identity.
  rewrite preserves_identity.
  reflexivity.
Defined.
Next Obligation.
  rewrite preserves_composition.
  rewrite preserves_composition.
  reflexivity.
Defined.
Arguments Compose {objC HomC C objD HomD D objE HomE E}
          {F₀} F {G₀} G : assert.

Definition exists_functor
  `{C: Category objC HomC}
  `{D: Category objD HomD}
  `{F: F₀ :: C ~> D}
  : ∃ C ~> D.
  exists F₀.
  apply F.
Defined.

Arguments exists_functor {objC C C' objD D D'} F F' : rename.