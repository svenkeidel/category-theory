Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.

Set Universe Polymorphism.

Definition refl (A:Type) (S:Setoid A) (x:A) : x ≈ x := reflexivity x.
Definition trans (A:Type) (S:Setoid A) (x y z:A) : y ≈ z -> x ≈ y -> x ≈ z
  := fun g f => transitivity f g.

Program Instance setoidSetoid (A:Type) (S:Setoid A) (x y:A) : Setoid (x ≈ y) :=
{
  equiv := fun _ _ => unit
}.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive; intros; apply ().
  - unfold Symmetric; intros; apply ().
  - unfold Transitive; intros; apply ().
Defined.

Program Instance discrete (A:Type) {S:Setoid A} : Category :=
{
  Obj := A;
  Hom := fun x y => x ≈ y;
  id := refl A S;
  compose := trans A S;
  hom_setoid := setoidSetoid A S
}.
Next Obligation.
  unfold Proper; unfold respectful.
  trivial.
Defined.
Next Obligation.
  apply ().
Defined.
Next Obligation.
  apply ().
Defined.
Next Obligation.
  apply ().
Defined.

Inductive Two : Type :=
| one: Two
| two: Two
.

Inductive EqTwo (x: Two) : Two -> Type :=
| eqTwoRefl : EqTwo x x.

Program Instance two_setoid : Setoid Two :=
{
  equiv := fun x y =>
    match x, y with
    | one, one => unit
    | two, two => unit
    | _, _ => Empty_set
    end
}.
Next Obligation.
  intuition.
  discriminate.
  discriminate.
Defined.
Next Obligation.
  intuition.
  discriminate.
  discriminate.
Defined.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive. intros. destruct x; constructor.
  - unfold Symmetric. intros X Y eq. destruct X, Y; intuition.
  - unfold Transitive. intros X Y Z eq1 eq2.
    destruct X, Y, Z; intuition.
Defined.

Definition map_two_obj {C:Category} (X Y:Obj[C]) (n:Two) :=
  match n with
  | one => X
  | two => Y
  end.

Definition map_two_arr {C:Category} (X Y:Obj[C])
(n1 n2:Two) (eq:n1 ≈ n2) : Hom[C] (map_two_obj X Y n1) (map_two_obj X Y n2).
Proof.
  destruct n1, n2.
  - simpl; apply (id[X]).
  - inversion eq.
  - inversion eq.
  - simpl; apply (id[Y]).
Defined.

Program Instance two_functor {C:Category} (X Y:Obj[C])
  : Functor (discrete Two) C :=
{
  map_obj := map_two_obj X Y;
  map_arr := map_two_arr X Y
}.
Next Obligation.
  unfold Proper. unfold respectful.
  intros eq1 eq2 _.
  destruct X0, Y0; simpl.
  - reflexivity.
  - inversion eq1.
  - inversion eq1.
  - reflexivity.
Defined.
Next Obligation.
  destruct X0.
  - simpl; reflexivity.
  - simpl; reflexivity.
Defined.
Next Obligation.
  destruct X0, Y0, Z; simpl; try (rewrite left_identity; reflexivity); inversion f; inversion g.
Defined.

Program Instance two_nat {C:Category} {X1 Y1 X2 Y2:Obj[C]} (f: Hom[C] X1 X2) (g: Hom[C] Y1 Y2) :
  NaturalTransformation (two_functor X1 Y1) (two_functor X2 Y2).
Next Obligation.
  destruct X.
  - simpl. apply f.
  - simpl. apply g.
Defined.
Next Obligation.
  unfold natural.
  intros X Y h.
  destruct X,Y; simpl in *; try (rewrite left_identity; rewrite right_identity; reflexivity); inversion h.
Defined.