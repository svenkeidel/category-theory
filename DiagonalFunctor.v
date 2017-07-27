Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export FunctorCategory.
Require Export ConstantFunctor.
Require Export DiscreteCategory.
Require Export Isomorphism.
Require Export ProductCategory.
Require Export Simplify.

Set Universe Polymorphism.

Program Instance diagonal {J C:Category}
  : Functor C (J \ C) :=
{ map_obj := fun X => constant X;
  map_arr := fun _ _ f => constant_nat f
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros f g eq Z.
  trivial.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Instance squared {C:Category}
  : Functor (product_category C C) (discrete Two \ C) :=
{ map_obj := fun X => two_functor (fst X) (snd X);
  map_arr := fun X Y f => two_nat (fst f) (snd f)
}.
Next Obligation.
  unfold Proper. unfold respectful.
  intros [f1 f2] [g1 g2] [eq1 eq2] X.
  simpl in *.
  destruct X; simpl.
  apply eq1.
  apply eq2.
Defined.
Next Obligation.
  destruct X0; simpl; reflexivity.
Defined.
Next Obligation.
  destruct X0; simpl in *; reflexivity.
Defined.

Program Instance squared_inverse {C:Category}
  : Functor (discrete Two \ C) (product_category C C) :=
{
  map_obj := fun F => (F[one],F[two]);
  map_arr := fun _ _ eta => (eta⟦one⟧,eta⟦two⟧)
}.
Next Obligation.
  unfold Proper. unfold respectful.
  intros eta theta eq.
  simpl in *.
  split.
  - rewrite (eq one).
    reflexivity.
  - rewrite (eq two).
    reflexivity.
Defined.
Next Obligation.
  split; rewrite <- (preserves_identity X); apply map_respects; simpl; intuition.
Defined.
Next Obligation.
  simplify.
Defined.

Ltac construct_iso C D F G :=
  simple refine (@Build_Isomorphism (functor_category C D) F G
                   (@Build_NaturalTransformation C D F G _ _)
                   (@Build_NaturalTransformation C D G F _ _)
                   _).

Program Instance squared_iso {C:Category}
  : product_category C C ≅[Cat] (discrete Two \ C) :=
{
  left_inverse := squared;
  right_inverse := squared_inverse
}.
Next Obligation.
  unfold isomorphic.
  split.
  construct_iso (discrete Two \ C) (discrete Two \ C) (squared ∘[Cat] squared_inverse) (identity_functor (discrete Two \ C)).
  - intros F. simpl.
    simple refine (@Build_NaturalTransformation _ _ _ _ _ _).
    * intros Y. destruct Y; simpl.
      + apply (id[F[one]]).
      + apply (id[F[two]]).
    * unfold natural; intros X Y f; destruct X, Y;
      match goal with
      | [ H: Hom[discrete Two] ?x ?x |- _ ] => 
          assert (f ≈ id (Category:=discrete Two) (X:=x)) as eq;
          simpl; intuition;
          rewrite eq
      | _ => inversion f
      end;
      simplify.
  - unfold natural; intros F G eta X; destruct X; simplify.
  - intros F. simpl.
    simple refine (@Build_NaturalTransformation _ _ _ _ _ _).
    * intros Y; destruct Y; simpl.
      + apply (id[F[one]]).
      + apply (id[F[two]]).
    * unfold natural; intros X Y f; destruct X, Y;
      match goal with
      | [ H: Hom[discrete Two] ?x ?x |- _ ] => 
          assert (f ≈ id (Category:=discrete Two) (X:=x)) as eq;
          simpl; intuition;
          rewrite eq
      | _ => inversion f
      end;
      simplify.
  - unfold natural; intros F G eta X; destruct X; simplify.
  - unfold isomorphic; simpl. split; intros F X; destruct X; simplify.
  - construct_iso (product_category C C) (product_category C C) (squared_inverse ∘[Cat] squared) (identity_functor (product_category C C)).
    * intros X; simpl. apply (id[fst X],id[snd X]).
    * simplify.
    * intros X; simpl. apply (id[fst X],id[snd X]).
    * simplify.
    * unfold isomorphic. simpl; split; intros; simplify.
Defined.

Program Instance diag (C:Category) : Functor C (product_category C C) :=
{
  map_obj := fun X => (X,X);
  map_arr := fun _ _ f => (f,f)
}.
Next Obligation.
  simplify.
Defined.
Next Obligation.
  simplify.
Defined.
Next Obligation.
  simplify.
Defined.
