Set Warnings "-notation-overridden".

Require Export Category.
Require Export Product.
Require Export Cat.
Require Export Isomorphism.

Program Instance product_setoid
  {C D: Category} (X Y: Obj[C]) (X' Y': Obj[D])
  : Setoid (Hom[C] X Y * Hom[D] X' Y') :=
{
  equiv := fun f g => fst f ≈ fst g ∧ snd f ≈ snd g
}.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive.
    intros [f g].
    simpl.
    split; reflexivity.
  - unfold Symmetric.
    intros [f g] [f' g'] [eq1 eq2].
    simpl.
    split; [rewrite eq1| rewrite eq2]; reflexivity.
  - unfold Transitive.
    intros [f g] [f' g'] [f'' g''] [eq1 eq2] [eq1' eq2'].
    simpl in *.
    split; [rewrite eq1; rewrite eq1' | rewrite eq2; rewrite eq2' ]; reflexivity.
Defined.

Program Instance product_category (C D : Category) : Category :=
{
  Obj := (Obj[C] * Obj[D])%type;
  Hom := fun X Y => (Hom[C] (fst X) (fst Y) * Hom[D] (snd X) (snd Y))%type;

  id := fun X => (id[fst X], id[snd X]);
  compose := fun X Y Z f g => (fst f ∘ fst g, snd f ∘ snd g);

  hom_setoid := fun X Y => product_setoid (fst X) (fst Y) (snd X) (snd Y)
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros [f f'] [g g'] [eq1 eq1'] [h h'] [j j'] [eq2 eq2'].
  simpl in *.
  split; [rewrite eq1; rewrite eq2 | rewrite eq1'; rewrite eq2' ]; reflexivity.
Defined.
Next Obligation.
  split; auto.
Defined.
Next Obligation.
  split; auto.
Defined.
Next Obligation.
  simpl in *.
  split; auto.
Defined.

Program Instance pi1_functor {C D: Category} :
  Functor (product_category C D) C :=
{
  map_obj := fun X => (fst X);
  map_arr := fun _ _ f => (fst f)
}.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Instance pi2_functor {C D: Category} :
  Functor (product_category C D) D :=
{
  map_obj := fun X => (snd X);
  map_arr := fun _ _ f => (snd f)
}.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Instance ump_functor
  {X C D: Category} (F: Functor X C) (G: Functor X D) :
  Functor X (product_category C D) :=
{
  map_obj := fun X => (F[X],G[X]);
  map_arr := fun _ _ f => (map[F] f, map[G] f)
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros f g eq.
  simpl.
  split; rewrite eq; reflexivity.
Defined.
Next Obligation.
  split; rewrite preserves_identity; reflexivity.
Defined.
Next Obligation.
  split; rewrite preserves_composition; reflexivity.
Defined.

Ltac construct_iso C D F G :=
  simple refine (@Build_Isomorphism (functor_category C D) F G
                   (@Build_NaturalTransformation C D F G _ _)
                   (@Build_NaturalTransformation C D G F _ _)
                   _).

Program Instance lift_iso
  {C D: Category} {X1 X2 Y1 Y2}
  (I: X1 ≅[C] Y1) (J: X2 ≅[D] Y2) :
  (X1,X2) ≅[product_category C D] (Y1,Y2) :=
{ left_inverse := (left_inverse I,left_inverse J);
  right_inverse := (right_inverse I,right_inverse J)
}.
Next Obligation.
  unfold isomorphic; simpl.
  repeat split; [ rewrite (left_inversion I)
                | rewrite (left_inversion J)
                | rewrite (right_inversion I)
                | rewrite (right_inversion J)
                ]; reflexivity.
Defined.

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
  unfold natural.
  intros X Y f.
  simpl.
  split; [ rewrite (natural[eta]) | rewrite (natural[theta]) ]; reflexivity.
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
  split; intros; [ apply (I1 X, I2 X)
                 | apply (I3 X, I4 X)
                 ].
Defined.

Program Instance ump_pi1_pi2_id
  {C D E: Category} 
  {F : Functor C D}
  {G : Functor C E}
  {H : Functor C (product_category D E)} :
  H ≅[C \ product_category D E] ump_functor (pi1_functor ∘[Cat] H) (pi2_functor ∘[Cat] H).
Next Obligation.
  apply Build_NaturalTransformation with
  (component := fun X => (id[pi1_functor[H[X]]],
                          id[pi2_functor[H[X]]])).
  unfold natural; intros X Y f.
  simpl.
  split; rewrite left_identity; rewrite right_identity; reflexivity.
Defined.
Next Obligation.
  apply Build_NaturalTransformation with
  (component := fun X => (id[pi1_functor[H[X]]],
                          id[pi2_functor[H[X]]])).
  unfold natural; intros X Y f.
  simpl.
  split; rewrite left_identity; rewrite right_identity; reflexivity.
Defined.
Next Obligation.
  unfold isomorphic.
  simpl.
  split; intros X; split;
    rewrite left_identity;
    rewrite preserves_identity;
    simpl;
    reflexivity.
Defined.

Program Instance product_in_cat {C D : Category} : Product (C:=Cat) C D :=
{
  product := product_category C D;
  pi1 := pi1_functor;
  pi2 := pi2_functor
}.
Next Obligation.
  rename f into F.
  rename g into G.
  exists (ump_functor F G).
  repeat split.
  - build_iso Z C (pi1_functor ∘[Cat] ump_functor F G) F
                  (fun X => id[F[X]]).
  -  build_iso Z D (pi2_functor ∘[Cat] ump_functor F G) G
                  (fun X => id[G[X]]).
  - intros H.
    intros [eq1 eq2].
    rename D into E.
    rename C into D.
    rename Z into C.
    pose proof (lift_nat_iso eq1 eq2) as I.
    symmetry.
    apply (fun J => I ∘[isomorphism_category] J).
    clear eq1 eq2 I.
    simpl.
    apply ump_pi1_pi2_id.
Defined.