Require Export Category.

Definition isomorphic {C:Category} {X Y}
  (f: Hom[C] X Y) (g: Hom[C] Y X) 
  := f ∘ g == id /\ g ∘ f == id.

(* An isomorphism is pairs of arrows in a category that cancle each
other, i.e. their composition is identity. *)
Class Isomorphism {C:Category} (X Y: Obj[C]) : Type :=
{
  left_inverse : Hom[C] X Y;
  right_inverse : Hom[C] Y X;
  iso : isomorphic left_inverse right_inverse
}.
Arguments left_inverse {C X Y} Isomorphism: assert.
Arguments right_inverse {C X Y} Isomorphism: assert.
Arguments iso {C X Y} Isomorphism: assert.

Notation "X ≅ Y" := (@Isomorphism _ X Y)
    (at level 40, left associativity) : object_scope.

Program Instance Iso {C:Category} {X Y}
  {f: Hom[C] X Y} {g: Hom[C] Y X}
  (I: isomorphic f g) : X ≅ Y
:= {
  left_inverse := f;
  right_inverse := g;
  iso := I
}.

Lemma left_inversion {C:Category} {X Y} (I: X ≅ Y)
  : left_inverse I ∘ right_inverse I == id.
Proof.
  apply (proj1 (iso I)).
Qed.

Lemma right_inversion {C:Category} {X Y} (I: X ≅ Y)
  : right_inverse I ∘ left_inverse I == id.
Proof.
  apply (proj2 (iso I)).
Qed.

Program Instance iso_symmetry
  `{C: Category} {X Y : Obj[C]} (I: X ≅ Y) : Y ≅ X :=
{
  left_inverse := right_inverse I;
  right_inverse := left_inverse I
}.
Next Obligation.
  unfold isomorphic.
  rewrite (right_inversion I).
  rewrite (left_inversion I).
  split; reflexivity.
Defined.

Program Instance iso_setoid {C:Category} (X Y : Obj[C]) : Setoid (X ≅ Y) :=
{
  equiv := fun I J =>
    left_inverse I == left_inverse J /\ right_inverse I == right_inverse J
}.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive; intros f; split; reflexivity.
  - unfold Symmetric;
    intros f g [eq1 eq2];
    split; [ rewrite eq1 | rewrite eq2 ]; reflexivity.
  - unfold Transitive;
    intros f g h [eq1 eq1'] [eq2 eq2'];
    split;
      [ rewrite eq1; rewrite eq2 | rewrite eq1'; rewrite eq2' ];
      reflexivity.
Defined.

Program Instance id_iso {C:Category} (X:Obj[C]) : X ≅ X :=
{
  left_inverse := id[X];
  right_inverse := id[X]
}.
Next Obligation.
  unfold isomorphic.
  rewrite left_identity.
  split; reflexivity.
Defined.

Program Instance compose_iso
  {C: Category} {X Y Z: Obj[C]}
  (I: Y ≅ Z) (J: X ≅ Y) : X ≅ Z :=
{
  left_inverse := left_inverse I ∘ left_inverse J;
  right_inverse := right_inverse J ∘ right_inverse I
}.
Next Obligation.
  unfold isomorphic.
  split.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative (left_inverse J)
                (right_inverse J) (right_inverse I)).
    rewrite (left_inversion J).
    rewrite left_identity.
    rewrite (left_inversion I).
    reflexivity.
  - rewrite -> compose_associative.
    rewrite <- (compose_associative (right_inverse I)
                (left_inverse I) (left_inverse J)).
    rewrite (right_inversion I).
    rewrite left_identity.
    rewrite (right_inversion J).
    reflexivity.
Defined.

Program Instance isomorphism_category {C:Category} : Category :=
{
  Obj := Obj[C];
  Hom := fun X Y => X ≅ Y;
  id := id_iso;
  compose := fun _ _ _ I J => compose_iso I J
}.
Next Obligation.
    unfold Proper. unfold respectful.
    intros I J [left_I_J right_I_J] K L [left_K_L right_K_L].
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
  split; rewrite compose_associative; reflexivity.
Defined.
