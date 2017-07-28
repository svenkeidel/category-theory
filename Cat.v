Set Warnings "-notation-overridden".

Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export FunctorCategory.
Require Export ProductCategory.
Require Export Product.
Require Export Simplify.

Set Universe Polymorphism.

(* Cat, the category of all categories *)

Section Cat.

  Program Instance natural_iso_preserved_under_horizontal_composition
    {C D E: Category}
    {F G: Functor D E}
    {H J: Functor C D}
    (I: F ≅[functor_category D E] G)
    (K: H ≅[functor_category C D] J)
    : compose_functor F H ≅[functor_category C E] compose_functor G J :=
  {
    left_inverse := horizontal_composition (left_inverse K) (left_inverse I);
    right_inverse := horizontal_composition (right_inverse K) (right_inverse I)
  }.
  Next Obligation.
    unfold isomorphic.
    unfold horizontal_composition.
    simpl.
    split.
    - intros X.
      rewrite (natural[right_inverse I]).
      rewrite compose_associative.
      rewrite <- (compose_associative  (map[F] (left_inverse K⟦X⟧))
                                       (map[F] (right_inverse K⟦X⟧))
                                       (right_inverse I⟦J[X]⟧)).
      rewrite <- preserves_composition.
      rewrite (left_inversion K X).
      simpl.
      repeat (rewrite -> preserves_identity).
      rewrite left_identity.
      rewrite (left_inversion I (J[X])).
      simpl.
      rewrite -> preserves_identity.
      reflexivity.
    - intros X.
      rewrite (natural[left_inverse I]).
      rewrite compose_associative.
      rewrite <- (compose_associative  (map[G] (right_inverse K⟦X⟧))
                                       (map[G] (left_inverse K⟦X⟧))
                                       (left_inverse I⟦H[X]⟧)).
      rewrite <- preserves_composition.
      rewrite (right_inversion K X).
      simpl.
      repeat (rewrite -> preserves_identity).
      rewrite left_identity.
      rewrite (right_inversion I (H[X])).
      simpl.
      rewrite -> preserves_identity.
      reflexivity.
  Defined.
  
  Program Instance Cat : Category :=
  {
    Obj := Category;
    Hom := Functor;
    id := identity_functor;
    hom_setoid := fun C D => obj_setoid (functor_category C D);
    compose := fun _ _ _ => compose_functor
  }.
  Next Obligation.
    simplify.
    apply natural_iso_preserved_under_horizontal_composition;
    assumption.
  Defined.
  Next Obligation.
    rename X into C.
    rename Y into D.
    rename f into F.
    nat_iso C D (fun X => id[F[X]]).
  Defined.
  Next Obligation.
    rename X into C.
    rename Y into D.
    rename f into F.
    nat_iso C D (fun X => id[F[X]]).
  Defined. 
  Next Obligation.
    rename X into A.
    rename Y into B.
    rename Z into C.
    rename U into D.
    rename f into F.
    rename g into G.
    rename h into H.
    nat_iso A D (fun X => id[F[G[H[X]]]]).
  Defined.

End Cat.

Section products_in_cat.

  Program Instance pi1_functor {C D: Category} :
    Functor (product_category C D) C :=
  {
    map_obj := fun X => (fst X);
    map_arr := fun _ _ f => (fst f)
  }.
  Solve All Obligations with simplify.
  
  Program Instance pi2_functor {C D: Category} :
    Functor (product_category C D) D :=
  {
    map_obj := fun X => (snd X);
    map_arr := fun _ _ f => (snd f)
  }.
  Solve All Obligations with simplify.
  
  Program Instance ump_functor
    {X C D: Category} (F: Functor X C) (G: Functor X D) :
    Functor X (product_category C D) :=
  {
    map_obj := fun X => (F[X],G[X]);
    map_arr := fun _ _ f => (map[F] f, map[G] f)
  }.
  Solve All Obligations with simplify.
  
  Program Instance lift_iso
    {C D: Category} {X1 X2 Y1 Y2}
    (I: X1 ≅[C] Y1) (J: X2 ≅[D] Y2) :
    (X1,X2) ≅[product_category C D] (Y1,Y2) :=
  { left_inverse := (left_inverse I,left_inverse J);
    right_inverse := (right_inverse I,right_inverse J)
  }.
  Solve All Obligations with simplify.
  
  Program Instance lift_nat
    {C D E: Category}
    {F1 G1: Functor C D}
    {F2 G2: Functor C E}
    (eta: NaturalTransformation F1 G1)
    (theta: NaturalTransformation F2 G2)
    : NaturalTransformation (ump_functor F1 F2) (ump_functor G1 G2) :=
  {
    component := fun X => (eta⟦X⟧,theta⟦X⟧)
  }.
  Next Obligation.
    simplify.
    - rewrite (natural[eta]). reflexivity.
    - rewrite (natural[theta]); reflexivity.
  Defined.
  
  Program Instance lift_nat_iso
    {C D E: Category}
    {F1 G1: Functor C D}
    {F2 G2: Functor C E}
    (eta: F1 ≅[functor_category C D] G1)
    (theta: F2 ≅[functor_category C E] G2)
    : ump_functor F1 F2
      ≅[functor_category C (product_category D E)]
      ump_functor G1 G2 :=
  { left_inverse := lift_nat (left_inverse eta) (left_inverse theta);
    right_inverse := lift_nat (right_inverse eta) (right_inverse theta)
  }.
  Next Obligation.
    pose proof (iso (lift_iso eta theta)) as I.
    unfold isomorphic in *.
    simpl in *.
    destruct I as [[I1 I2] [I3 I4]].
    split; intros X; [ apply (I1 X, I2 X) | apply (I3 X, I4 X) ].
  Defined.
  
  Program Instance ump_pi1_pi2_id
    {Z C D: Category}
    (F : Functor Z (product_category C D)) :
    ump_functor (pi1_functor ∘[Cat] F) (pi2_functor ∘[Cat] F)
     ≅[product_category C D \ Z] F.
  Next Obligation.
    apply Build_NaturalTransformation with
    (component := fun X => (id[pi1_functor[F[X]]],
                            id[pi2_functor[F[X]]])).
    simplify.
  Defined.
  Next Obligation.
    apply Build_NaturalTransformation with
    (component := fun X => (id[pi1_functor[F[X]]],
                            id[pi2_functor[F[X]]])).
    simplify.
  Defined.
  Next Obligation.
    simplify.
  Defined.

  Instance pi1_ump
    {Z C D: Category}
    {F : Functor Z C}
    {G : Functor Z D}
    : pi1_functor ∘[Cat] (ump_functor F G) ≅[C \ Z] F.
  Proof.
    build_nat_iso Z C.
    - intros; simpl; apply (id[F[X]]).
    - simplify.
    - intros; simpl; apply (id[F[X]]).
    - simplify.
    - simplify.
  Defined.
  
  Instance pi2_ump
    {Z C D: Category}
    {F : Functor Z C}
    {G : Functor Z D}
    : pi2_functor ∘[Cat] (ump_functor F G) ≅[D \ Z] G.
  Proof.
    build_nat_iso Z D.
    - intros; simpl; apply (id[G[X]]).
    - simplify.
    - intros; simpl; apply (id[G[X]]).
    - simplify.
    - simplify.
  Defined.

  Program Instance ump_proper {X C D : Category}
    : Proper ((@equiv (Hom[Cat] X C) _) ==> (@equiv (Hom[Cat] X D) _) ==> (@equiv (Hom[Cat] X (product_category C D)) _)) ump_functor.
  Next Obligation.
    unfold respectful.
    intros F1 G1 eq1 F2 G2 eq2.
    simpl.
    build_nat_iso X (product_category C D).
    intros.
    simplify.
    apply (left_inverse eq1).
    apply (left_inverse eq2).
    simplify.
    apply (natural[left_inverse eq1]).
    apply (natural[left_inverse eq2]).
    intros.
    simplify.
    apply (right_inverse eq1).
    apply (right_inverse eq2).
    simplify.
    apply (natural[right_inverse eq1]).
    apply (natural[right_inverse eq2]).
    unfold isomorphic.
    simplify.
    rewrite (left_inversion eq1 X0); simplify.
    rewrite (left_inversion eq2 X0); simplify.
    rewrite (right_inversion eq1 X0); simplify.
    rewrite (right_inversion eq2 X0); simplify.
  Defined.

  Local Obligation Tactic := idtac.

  Program Instance product_in_cat (C D : Category) : Product (C:=Cat) C D :=
  {
    product := product_category C D;
    pi1 := pi1_functor;
    pi2 := pi2_functor;
    product_mapping := fun _ => ump_functor;
    product_mapping_respects := fun _ => ump_proper
  }.
  Next Obligation.
    intros C D Z H F G.
    split.
    - intros eq.
      split; rewrite eq.
      + apply pi1_ump.
      + apply pi2_ump.
    - intros [eq1 eq2].
      rewrite <- eq1.
      rewrite <- eq2.
      rewrite (ump_pi1_pi2_id H).
      reflexivity.
  Defined.

End products_in_cat.