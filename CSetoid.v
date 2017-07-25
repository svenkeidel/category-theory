Set Warnings "-notation-overridden".

Require Export
  Coq.Init.Datatypes
  Coq.Program.Program
  Coq.Classes.CEquivalence
  Coq.Classes.CRelationClasses
  Coq.Classes.CMorphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Close Scope nat_scope.
Delimit Scope category_theory_scope with category_theory.
Open Scope category_theory_scope.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.

Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.
Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity) : category_theory_scope.
Notation "¬ x" := (~x)
  (at level 75, right associativity) : category_theory_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.

Notation "P ∨ Q" := ({ P } + { Q })
  (at level 85, right associativity) : category_theory_scope.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :> Equivalence equiv
}.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

Program Instance setoid_refl `(sa : Setoid A) :
  Reflexive equiv.
Obligation 1. apply setoid_equiv. Qed.

Program Instance setoid_sym `(sa : Setoid A) :
  Symmetric equiv.
Obligation 1. apply setoid_equiv; auto. Qed.

Program Instance setoid_trans `(sa : Setoid A) :
  Transitive equiv.
Obligation 1.
  apply setoid_equiv.
  destruct sa; simpl in *.
  destruct setoid_equiv0.
  eapply Equivalence_Transitive; eauto.
Qed.

Delimit Scope signature_scope with signature.

Notation "f ++> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f ==> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f --> g" := (respectful (Basics.flip f) g)%signature
  (right associativity, at level 55) : signature_scope.

Arguments Proper {A}%type R%signature m.
Arguments respectful {A B}%type (R R')%signature _ _.

Program Instance prod_setoid `{Setoid A} `{Setoid B} : Setoid (A * B) := {
  equiv := fun x y => equiv (fst x) (fst y) * equiv (snd x) (snd y)
}.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive; intros; simpl; split; reflexivity.
  - unfold Symmetric. intros x y [eq1 eq2].
    split; [rewrite eq1|rewrite eq2]; reflexivity.
  - unfold Transitive. intros [x1 x2] [y1 y2] [z1 z2] [eq1 eq2] [eq3 eq4].
    split; [rewrite eq1; rewrite eq3 | rewrite eq2; rewrite eq4]; reflexivity.
Defined.

Program Instance pair_respects `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv ==> equiv) (@pair A B).
Next Obligation.
  unfold Proper; unfold respectful.
  intros x1 x2 eq1 y1 y2 eq2.
  simpl.
  split; [rewrite eq1 | rewrite eq2]; reflexivity.
Defined.

Program Instance fst_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@fst A B).
Next Obligation.
  unfold Proper; unfold respectful.
  intros x y [eq1 eq2]. rewrite eq1; reflexivity.
Defined.

Program Instance snd_respects {A B} `{Setoid A} `{Setoid B} :
  Proper (equiv ==> equiv) (@snd A B).
Next Obligation.
  unfold Proper; unfold respectful.
  intros x y [eq1 eq2]. rewrite eq2; reflexivity.
Defined.

