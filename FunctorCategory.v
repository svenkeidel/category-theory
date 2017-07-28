Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Simplify.

Set Universe Polymorphism.

Local Obligation Tactic := simplify.

Program Instance functor_category (C D: Category) : Category :=
{
  Obj := Functor C D;
  Hom := NaturalTransformation;
  id := id_natural_transformation;
  compose := fun _ _ _ => vertical_composition 
}.
Next Obligation.
  rewrite (X0 X2).
  rewrite (X1 X2).
  reflexivity.
Defined.

Notation "D \ C" := (functor_category C%category D%category)
  (at level 40, left associativity) : category_scope.

Ltac nat_iso C D eta :=
  match goal with
  | [ |- ?F ≅ ?G ] =>
      simple refine (@Build_Isomorphism (functor_category C D) F G
                      (@Build_NaturalTransformation C D F G eta _)
                      (@Build_NaturalTransformation C D G F eta _)
                      _);
      [ simplify
      | simplify
      | simplify
      ]
  end.

Ltac build_nat_iso C D :=
  match goal with
  | [ |- ?F ≅ ?G ] =>
      simple refine (@Build_Isomorphism (functor_category C D) F G
                      (@Build_NaturalTransformation C D F G _ _)
                      (@Build_NaturalTransformation C D G F _ _)
                      _)
  end.


