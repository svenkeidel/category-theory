Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Cat.
Require Export Sets.
Require Export Opposite.
Require Export HomFunctor.

Set Universe Polymorphism.

Class UnitCounitAdjunction
  {C D: Category} (F: Functor C D) (G: Functor D C) := {
  unit: NaturalTransformation (identity_functor C) (G ∘[Cat] F);
  counit: NaturalTransformation (F ∘[Cat] G) (identity_functor D);
  left_identity_law: forall X, counit⟦F[X]⟧ ∘ map[F](unit⟦X⟧) ≈ id[F[X]];
  right_identity_law: forall X, map[G](counit⟦X⟧) ∘ unit⟦G[X]⟧ ≈ id[G[X]]
}.

Definition HomsetAdjunction
  {C D: Category} (F: Functor C D) (G: Functor D C)
  := (HomOp F (identity_functor D))
     ≅[ Sets \ product_category (op C) D ]
     (HomOp (identity_functor C) G).

Definition phi
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X:Obj[C]} {Y:Obj[D]}
  : Hom[Sets] {| carrier := Hom[D] F[X] Y |} {| carrier := Hom[C] X G[Y] |}
  := left_inverse H ⟦(X,Y)⟧.

Program Instance phi_respects 
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X:Obj[C]} {Y:Obj[D]}
  : Proper (equiv ==> equiv) (phi H (X:=X) (Y:=Y)) :=
  function_respects (left_inverse H ⟦(X,Y)⟧).

Lemma phi_natural
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X Y X' Y'}
  (f: Hom[product_category (op C) D] (X,Y) (X',Y'))
  : phi H ∘ map[HomOp F (identity_functor D)] f ≈
    map[HomOp (identity_functor C) G] f ∘ phi H.
  Proof. apply (natural[left_inverse H] _ _ f). Qed.

Definition psi
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X: Obj[C]} {Y: Obj[D]}
  : Hom[Sets] {| carrier := Hom[C] X G[Y] |} {| carrier := Hom[D] F[X] Y |}
  := right_inverse H ⟦(X,Y)⟧.

Lemma psi_natural
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X Y X' Y'}
  (f: Hom[product_category (op C) D] (X,Y) (X',Y'))
  : psi H ∘ map[HomOp (identity_functor C) G] f ≈
    map[HomOp F (identity_functor D)] f ∘ psi H.
  Proof. apply (natural[right_inverse H] _ _ f). Qed.

Program Instance psi_respects 
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X:Obj[C]} {Y:Obj[D]}
  : Proper (equiv ==> equiv) (psi H (X:=X) (Y:=Y)) :=
  function_respects (right_inverse H ⟦(X,Y)⟧).

Lemma phi_psi_id
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X:Obj[C]} {Y:Obj[D]}
  : phi H (X:=X) (Y:=Y) ∘ psi H (X:=X) (Y:=Y) ≈ id.
  Proof. unfold phi, psi. rewrite (left_inversion H (X, Y)).
   simplify. Qed.


Lemma psi_phi_id
  {C D: Category} {F: Functor C D} {G: Functor D C}
  (H: HomsetAdjunction F G) {X:Obj[C]} {Y:Obj[D]}
  : psi H (X:=X) (Y:=Y) ∘ phi H (X:=X) (Y:=Y) ≈ id.
  Proof. unfold phi, psi. rewrite (right_inversion H (X, Y)).
   simplify. Qed.

Program Instance from_homset_adjunction 
  {C D: Category} (F: Functor C D) (G: Functor D C)
  (H: HomsetAdjunction F G) :
  UnitCounitAdjunction F G :=
{
  unit := {| component := fun X => phi H (id[F[X]]) |};
  counit := {| component := fun Y => psi H (id[G[Y]]) |}
}.
Next Obligation.
  unfold natural. intros X Y f.
  pose proof (phi_natural H (id[X],map[F] f) id[F[X]]) as N.
  simpl in *.
  rewrite (@compose_associative C) in N.
  rewrite (right_identity (phi H id[(F)[X]])) in N.
  rewrite <- N.
  clear N.
  simplify.
  pose proof (phi_natural H (f,id[F[Y]]) id[F[Y]]) as N.
  simpl in *.
  rewrite left_identity in N.
  rewrite left_identity in N.
  rewrite N.
  simplify.
Defined.
Next Obligation.
  unfold natural. intros X Y f.
  pose proof (psi_natural H (map[G] f,id[Y]) id[G[Y]]) as N.
  simpl in *.
  rewrite (@compose_associative D) in N.
  rewrite left_identity in N.
  rewrite <- N.
  clear N.
  simplify.
  pose proof (psi_natural H (id[G[X]],f) id[G[X]]) as N.
  simpl in *.
  rewrite right_identity in N.
  rewrite right_identity in N.
  rewrite N.
  simplify.
Defined.
Next Obligation.
  pose proof (psi_natural H (phi H (id[F[X]]), id[F[X]]) id[G[F[X]]]) as N.
  simpl in N.
  rewrite left_identity in N.
  rewrite <- N.
  simplify.
  apply (psi_phi_id H).
Defined.
Next Obligation.
  pose proof (phi_natural H (id[G[X]], psi H (id[G[X]])) id[F[G[X]]]) as N.
  simpl in N.
  rewrite right_identity in N.
  rewrite right_identity in N.
  rewrite <- N.
  simplify.
  apply (phi_psi_id H).
Defined.

Program Definition to_homset_adjunction 
  {C D: Category} (F: Functor C D) (G: Functor D C)
  (H: UnitCounitAdjunction F G)
  : HomsetAdjunction F G.
Proof.
  unfold HomsetAdjunction.
  simple refine (Build_Isomorphism _ _ _ _ _ _).
  - simple refine (@Build_NaturalTransformation _ _ _ _ _ _).
    + intros [X Y].
      simple refine (Build_Function _ _ _ _ _ _).
      intros f.
      simpl in *.
      apply (map[G] f ∘ unit⟦X⟧).
      simplify.
    + unfold natural. simpl.
      intros [X1 X2] [Y1 Y2] [f1 f2] g.
      simpl in *.
      rewrite preserves_composition.
      rewrite compose_associative.
      pose proof (natural[unit] _ _ f1) as P.
      simpl in P.
      rewrite <- P.
      simplify.
 - simple refine (@Build_NaturalTransformation _ _ _ _ _ _).
    + intros [X Y].
      simple refine (Build_Function _ _ _ _ _ _).
      intros f.
      simpl in *.
      apply (counit⟦Y⟧ ∘ map[F] f).
      simplify.
    + unfold natural. simpl.
      intros [X1 X2] [Y1 Y2] [f1 f2] g.
      simpl in *.
      rewrite preserves_composition.
      rewrite preserves_composition.
      rewrite <- compose_associative.
      rewrite <- compose_associative.
      pose proof (natural[@counit _ _ _ _ H] _ _ f2) as P.
      simpl in P.
      rewrite -> P.
      simplify.
  - unfold isomorphic.
    split; simpl; intros [X Y] f; simpl in *;
    rewrite preserves_composition;
    rewrite -> compose_associative.
    + pose proof (natural[unit] _ _ f) as P.
      simpl in P.
      rewrite <- P.
      rewrite <- compose_associative.
      rewrite -> (@right_identity_law _ _ _ _ H Y).
      simplify.
    + pose proof (natural[@counit _ _ _ _ H] _ _ f) as P.
      simpl in P.
      rewrite <- compose_associative.
      rewrite -> P.
      rewrite -> compose_associative.
      rewrite -> (@left_identity_law _ _ _ _ H X).
      simplify.
Qed.

