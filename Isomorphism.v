Require Export Category.

Generalizable Variables objC C.

Definition iso `{Category objC C}
  {X Y:objC} (f: C X Y) (g:C Y X) : Prop :=
  f ∘ g == id Y /\ g ∘ f == id X.

Lemma left_inversion `{Category objC C} {X Y: objC} {f: C X Y} {g: C Y X} :
  iso f g -> f ∘ g == id Y.
Proof. unfold iso. intros [l r]. apply l. Qed.

Lemma right_inversion `{Category objC C} {X Y: objC} {f: C X Y} {g: C Y X} :
  iso f g -> g ∘ f == id X.
Proof. unfold iso. intros [l r]. apply r. Qed.

Class Isomorphism {objC:Type} (C:objC -> objC -> Type) `{Category objC C} (X Y: objC) := MkIso {
  left_inverse: C X Y;
  right_inverse: C Y X;
  isIso: iso left_inverse right_inverse
}.
Arguments left_inverse {objC C _ X Y}.
Arguments right_inverse {objC C _ X Y}.
Arguments isIso {objC C _ X Y}.

Program Definition idIso `{Category objC C} (X:objC) : Isomorphism C X X := {|
  left_inverse := id X;
  right_inverse := id X
|}.
Next Obligation.
  unfold iso.
  rewrite left_identity.
  split; reflexivity.
Defined.

Program Definition composeIso `{Category objC C} (X Y Z: objC) (I: Isomorphism C Y Z) (J: Isomorphism C X Y) : Isomorphism C X Z := {|
  left_inverse := left_inverse I ∘ left_inverse J;
  right_inverse := right_inverse J ∘ right_inverse I;
|}.
Next Obligation.
  unfold iso.
  split.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative (left_inverse J) (right_inverse J) (right_inverse I)).
    rewrite (left_inversion (isIso J)).
    rewrite left_identity.
    rewrite (left_inversion (isIso I)).
    reflexivity.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative (right_inverse I) (left_inverse I) (left_inverse J)).
    rewrite (right_inversion (isIso I)).
    rewrite left_identity.
    rewrite (right_inversion (isIso J)).
    reflexivity.
Defined.

Program Instance IsoSetoid `{Category objC C} (X Y : objC) : Setoid (Isomorphism C X Y) := {
  equiv := fun a b => left_inverse a == left_inverse b /\ right_inverse a == right_inverse b
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros f.
    split; reflexivity.
  - unfold Symmetric.
    intros f g [left_eq right_eq].
    split; [ rewrite left_eq | rewrite right_eq ]; reflexivity.
  - unfold Transitive.
    intros f g h [left_f_g right_f_g] [left_g_h right_g_h].
    split;
      [ rewrite left_f_g; rewrite left_g_h | rewrite right_f_g; rewrite right_g_h ];
      reflexivity.
Defined.

Program Instance IsoCat `{Category objC C} : Category (Isomorphism C) :=
{
  c_oid := IsoSetoid;
  id := idIso;
  compose := fun x y z f g => composeIso x y z f g
}.
Next Obligation.
    unfold Proper; unfold respectful; simpl.
    intros I J [left_I_J right_I_J].
    intros K L [left_K_L right_K_L].
    split.
      * rewrite left_I_J.
        rewrite left_K_L.
        reflexivity.
      * rewrite right_I_J.
        rewrite right_K_L.
        reflexivity.
Defined.
Next Obligation.
  split; rewrite compose_associative; reflexivity.
Defined.
