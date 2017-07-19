Require Export Category.

Generalizable Variables objC HomC C X Y.

Definition Isomorphism
  `{C:Category objC HomC}
  `(f: HomC X Y) `(g: HomC Y X) : Prop :=
  f ∘ g == id Y /\ g ∘ f == id X.

Notation "X ≅ Y" :=
  ({ f : _ & @Isomorphism _ _ _ X Y (fst f) (snd f) })
    (at level 40, left associativity) : category_scope.

Definition left_inversion
  `{C: Category objC HomC}
  `{f: HomC X Y} `{g: HomC Y X}
  (I: Isomorphism f g) : f ∘ g == id Y := proj1 I.

Definition right_inversion
  `{C: Category objC HomC}
  `{f: HomC X Y} `{g: HomC Y X}
  (I: Isomorphism f g) : g ∘ f == id X := proj2 I.

Definition iso_symmetry
  `{C: Category objC HomC}
  `{f: HomC X Y} `{g: HomC Y X}
  (I: Isomorphism f g) : Isomorphism g f.
  unfold Isomorphism in *.
  destruct I as [r l].
  rewrite l.
  rewrite r.
  split; reflexivity.
Qed.

Program Instance iso_setoid `{Category objC C} (X Y : objC) : Setoid (X ≅ Y) := {
  equiv := fun a b => fst (projT1 a) == fst (projT1 b)
    /\ snd (projT1 a) == snd (projT1 b)
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

Lemma id_iso `{Category objC C} (X:objC) : Isomorphism (id X) (id X).
Proof.
  unfold Isomorphism.
  rewrite left_identity.
  split; reflexivity.
Qed.

Lemma compose_iso `{Category objC C}
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

Program Instance iso_cat `{Category objC C} : Category (fun X Y => X ≅ Y) :=
{
  id := fun X => exists_iso (id_iso X);
  compose := fun _ _ _ I J => exists_iso (compose_iso (projT2 I) (projT2 J))
}.
Next Obligation.
    unfold Proper. unfold respectful.
    intros [[i i'] I] [[j j'] J] [left_I_J right_I_J] [[k k'] K] [[l l'] L].
    intros [left_K_L right_K_L].
    simpl in *.
    split.
      * rewrite left_I_J.
        rewrite left_K_L.
        reflexivity.
      * rewrite right_I_J.
        rewrite right_K_L.
        reflexivity.
Defined.
Next Obligation.
  simpl in *.
  split; rewrite compose_associative; reflexivity.
Defined.
