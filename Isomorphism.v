Require Export Category.

Generalizable Variables objC C.

Definition Isomorphism `{Category objC C}
  {X Y:objC} (f: C X Y) (g:C Y X) : Prop :=
  f ∘ g == id Y /\ g ∘ f == id X.

Notation "X ≅ Y" := ({ f : _ & @Isomorphism _ _ _ X Y (fst f) (snd f) }) (at level 40, left associativity).

Definition left_inverse `{Category objC C} {X Y: objC} (I: X ≅ Y) : C X Y :=
  fst (projT1 I).

Definition right_inverse `{Category objC C} {X Y: objC} (I: X ≅ Y) : C Y X :=
  snd (projT1 I).

Lemma left_inversion `{Category objC C} {X Y: objC} (I: X ≅ Y) :
  left_inverse I ∘ right_inverse I == id Y.
Proof. unfold Isomorphism in I.
       destruct I as [[f g] [l r]].
       apply l.
Qed.

Lemma right_inversion `{Category objC C} {X Y: objC} (I: X ≅ Y) :
  right_inverse I ∘ left_inverse I == id X.
Proof. unfold Isomorphism in I.
       destruct I as [[f g] [l r]].
       apply r.
Qed.

Program Definition idIso `{Category objC C} (X:objC) : X ≅ X.
  exists (id X, id X).
  unfold Isomorphism.
  simpl.
  rewrite left_identity.
  split; reflexivity.
Defined.

Program Definition composeIso `{Category objC C}
  {X Y Z: objC} (I: Y ≅ Z) (J: X ≅ Y) : X ≅ Z.
  exists (left_inverse I ∘ left_inverse J, right_inverse J ∘ right_inverse I).
  unfold Isomorphism.
  simpl.
  split.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative (left_inverse J) (right_inverse J) (right_inverse I)).
    rewrite (left_inversion J).
    rewrite left_identity.
    rewrite (left_inversion I).
    reflexivity.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative (right_inverse I) (left_inverse I) (left_inverse J)).
    rewrite (right_inversion I).
    rewrite left_identity.
    rewrite (right_inversion J).
    reflexivity.
Defined.

Program Instance IsoSetoid `{Category objC C} (X Y : objC) : Setoid (X ≅ Y) := {
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

Ltac simplify_iso :=
  repeat (
    unfold left_inverse;
    unfold right_inverse;
    simpl
  ).

Program Instance IsoCat `{Category objC C} : Category (fun X Y => X ≅ Y) :=
{
  c_oid := IsoSetoid;
  id := idIso;
  compose := fun _ _ _ => composeIso
}.
Next Obligation.
    unfold Proper. unfold respectful.
    intros I J [left_I_J right_I_J].
    intros K L [left_K_L right_K_L].
    simplify_iso.
    split.
      * rewrite left_I_J.
        rewrite left_K_L.
        reflexivity.
      * rewrite right_I_J.
        rewrite right_K_L.
        reflexivity.
Defined.
Next Obligation.
  simplify_iso.
  rewrite left_identity.
  rewrite right_identity.
  split; reflexivity.
Defined.
Next Obligation.
  simplify_iso.
  rewrite left_identity.
  rewrite right_identity.
  split; reflexivity.
Defined.
Next Obligation.
  simplify_iso.
  split; rewrite compose_associative; reflexivity.
Defined.
