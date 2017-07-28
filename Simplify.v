Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Isomorphism.

Ltac simplify :=
  repeat
  ( simpl in *;
    match goal with
    | [ |- ?x ≈ ?x ] => reflexivity
    | [ H: ?P |- ?P ] => apply H
    | [ |- _ ∧ _ ] => split
    | [ H: _ ∧ _ |- _ ] => destruct H
    | [ |- natural _ ] => unfold natural
    | [ |- isomorphic _ _ ] => unfold isomorphic
    | [ |- Proper _ _ ] => unfold Proper; unfold respectful
    | [ |- ∀ _ , _ ] => intros
    | [ |- context[ id[?X] ∘ _ ] ] => rewrite left_identity
    | [ |- context[ _ ∘ id[_] ] ] => rewrite right_identity
    | [ |- context[ map[?F] _ ] ] => rewrite -> (preserves_identity F)
    | [ |- context[ map[?F] (?f ∘ ?g) ] ] => rewrite -> (preserves_composition F f g)
    | [ |- context[ left_inverse ?I ∘ right_inverse ?I ] ] => rewrite (left_inversion I)
    | [ |- context[ right_inverse ?I ∘ left_inverse ?I ] ] => rewrite (right_inversion I)
    | [ |- context[ (?f ∘ ?g) ∘ ?h ] ] => rewrite -> (compose_associative f g h)
    | [ eq: ?f ≈ ?g |- context[ ?f ] ] => rewrite -> eq; clear eq
    end
  ).
