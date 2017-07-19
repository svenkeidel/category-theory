Require Export Category.

Generalizable Variables objC HomC C X Y.

Definition Isomorphism
  `{C:Category objC HomC}
  `(f: HomC X Y) `(g: HomC Y X) : Prop :=
  f ∘ g == id Y /\ g ∘ f == id X.

Notation "X ≅ Y" := ({ f : _ & @Isomorphism _ _ _ X Y (fst f) (snd f) }) (at level 40, left associativity) : category_scope.

Definition left_inversion `{C: Category objC HomC} {X Y: objC} {f: HomC X Y} {g: HomC Y X}
  (I: Isomorphism f g) : f ∘ g == id Y := proj1 I.

Definition right_inversion `{Category objC C} {X Y: objC} {f: C X Y} {g:C Y X}
  (I: Isomorphism f g) : g ∘ f == id X := proj2 I.

Definition iso_symmetry
  `{C: Category objC HomC}
  {X Y: objC} {f: HomC X Y} {g: HomC Y X}
  (I: Isomorphism f g) : Isomorphism g f.
  unfold Isomorphism in *.
  destruct I as [r l].
  rewrite l.
  rewrite r.
  split; reflexivity.
Qed.
Definition exists_iso
  `{C:Category objC HomC}
  `{f: HomC X Y} `{g: HomC Y X}
  (I: Isomorphism f g)
  : X ≅ Y.
Proof.
  exists (f,g).
  simpl.
  apply I.
Defined.

Definition left_inverse `{C: Category objC HomC} {X Y: objC} (I: X ≅ Y) : HomC X Y :=
  fst (projT1 I).

Definition right_inverse `{C: Category objC HomC} {X Y: objC} (I: X ≅ Y) : HomC Y X :=
  snd (projT1 I).

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

Lemma idIso `{Category objC C} (X:objC) : Isomorphism (id X) (id X).
Proof.
  unfold Isomorphism.
  rewrite left_identity.
  split; reflexivity.
Qed.

Lemma composeIso `{Category objC C}
  {X Y Z: objC}
  {f: C Y Z} {f': C Z Y} {g: C X Y} {g': C Y X}
  (I: Isomorphism f f') (J: Isomorphism g g') :
  Isomorphism (f ∘ g) (g' ∘ f').
Proof.
  unfold Isomorphism.
  split.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative g g' f').
    rewrite (left_inversion J).
    rewrite left_identity.
    rewrite (left_inversion I).
    reflexivity.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative f' f g).
    rewrite (right_inversion I).
    rewrite left_identity.
    rewrite (right_inversion J).
    reflexivity.
Qed.
  
Ltac simplify_iso :=
  repeat (
    unfold left_inverse in *;
    unfold right_inverse in *;
    simpl in *
  ).

Program Instance IsoCat `{Category objC C} : Category (fun X Y => X ≅ Y) :=
{
  c_oid := IsoSetoid;
  id := fun X => exists_iso (idIso X);
  compose := fun _ _ _ I J => exists_iso (composeIso (projT2 I) (projT2 J))
}.
Next Obligation.
    unfold Proper. unfold respectful.
    intros [[i i'] I] [[j j'] J] [left_I_J right_I_J] [[k k'] K] [[l l'] L].
    intros [left_K_L right_K_L].
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
