Require Export Category.
Require Export Functor.

Generalizable Variables objC HomC C objD HomD D objE HomE E F₀ G₀ H₀ J₀ eta₁ theta₁.

Definition NaturalTransformation
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D}
  (eta: forall (X:objC), HomD (F₀ X) (G₀ X))
  := forall {X Y:objC} (f: HomC X Y), eta Y ∘ map F f == map G f ∘ eta X.

(* The notation (eta: eta₁ :: F ≈> G) denotes a natural transformation
  eta from the functor F to G where eta₁ is the bundle of arrows of
  the natural transformation. Components of the natural transformation
  can be obtained by appling eta₁ to objects of the codomain of F. *)
Notation "eta :: F ≈> G" :=
  (@NaturalTransformation _ _ _ _ _ _ _ F _ G eta)
    (at level 40, left associativity) : category_scope.

Notation "∃ F ≈> G" :=
  ({ eta : _ & eta :: F ≈> G })
    (at level 50, left associativity) : category_scope.

Definition exists_natural_trans
  `{C: Category objC HomC} `{D: Category objD HomD}
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D}
  `{eta: eta₁ :: F ≈> G}
  : ∃ F ≈> G.
  exists eta₁.
  apply eta.
Defined.
Arguments exists_natural_trans
  {objC HomC C objD HomD D F₀ F G₀ G eta₁} eta : assert.

Program Instance natural_setoid
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D}
  : Setoid (∃ F ≈> G) :=
{
  equiv := fun eta theta => forall X, (projT1 eta) X == (projT1 theta) X
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros [eta eta_natural] X.
    simpl.
    reflexivity.
  - unfold Symmetric.
    intros [eta eta_natural] [theta theta_natural].
    simpl.
    intros eq_eta_theta X.
    rewrite (eq_eta_theta X).
    reflexivity.
  - unfold Transitive.
    intros [eta eta_natural] [theta theta_natural] [iota iota_natural].
    simpl.
    intros eq_eta_theta eq_theta_iota X.
    rewrite (eq_eta_theta X).
    rewrite (eq_theta_iota X).
    reflexivity.
Defined.

Definition id_natural_transformation
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D}
  : (fun X => map F (id X)) :: F ≈> F.
Proof.
  intros U V f.
  repeat (rewrite <- preserves_composition).
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Defined.
Arguments id_natural_transformation {objC HomC C objD HomD D F₀} F _ _ _ : assert.

Definition vertical_composition
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D} `{H: H₀ :: C ~> D}
  `{eta: eta₁ :: G ≈> H}
  `{theta: theta₁ :: F ≈> G}
  : (fun X => eta₁ X ∘ theta₁ X) :: F ≈> H.
Proof.
  unfold NaturalTransformation.
  intros X Y f.
  repeat (rewrite <- preserves_composition).
  rewrite -> compose_associative.
  rewrite (theta X Y f).
  rewrite <- compose_associative.
  rewrite (eta X Y f).
  rewrite -> compose_associative.
  reflexivity.
Defined.
Arguments vertical_composition {objC HomC C objD HomD D F₀ F G₀ G H₀ H}
          {eta₁} eta
          {theta₁} theta
          _ _ _ : assert.

Definition horizontal_composition
  `{C: Category objC HomC} `{D: Category objD HomD} `{E: Category objE HomE}
  `{F: F₀ :: C ~> D} `{G: G₀ :: C ~> D} `{H: H₀ :: D ~> E} `{J: J₀ :: D ~> E}
  `(eta: eta₁ :: F ≈> G)
  `(theta: theta₁ :: H ≈> J)
  : (fun X => theta₁ (G₀ X) ∘ map H (eta₁ X)) ::
     Compose H F ≈> Compose J G.
Proof.
  unfold NaturalTransformation.
  intros X Y f.
  unfold Compose.
  simpl.
  rewrite compose_associative.
  rewrite <- (preserves_composition (Functor:=H) (eta₁ Y) (map F f)).
  rewrite eta.
  rewrite -> preserves_composition.
  rewrite <- compose_associative.
  rewrite (theta _ _ (map G f)).
  rewrite compose_associative.
  reflexivity.
Defined.

Program Instance functor_category
  `{C: Category objC HomC} `{D: Category objD HomD} 
  : Category (obj := ∃ C ~> D)
             (fun F G => { eta : _ & @NaturalTransformation objC HomC C objD HomD D (projT1 F) (projT2 F) (projT1 G) (projT2 G) eta }).
Next Obligation.
  simpl.
  apply (exists_natural_trans (id_natural_transformation X0)).
Defined.
Next Obligation.
  simpl in *.
  apply (exists_natural_trans (vertical_composition X3 X2)).
Defined.
Next Obligation.
  unfold Proper.
  unfold respectful.
  simpl.
  rename X into F.
  rename X2 into F'.
  rename Y into G.
  rename X1 into G'.
  rename Z into H.
  rename X0 into H'.
  intros [eta eta_natural] [eta' eta'_natural].
  simpl.
  intros eq_eta_eta' [theta theta_natural] [theta' theta'_natural].
  simpl.
  intros eq_theta_theta'.
  intros X.
  rewrite (eq_eta_eta' X).
  rewrite (eq_theta_theta' X).
  reflexivity.
Defined.
Next Obligation.
  simpl in *.
  rewrite preserves_identity.
  rewrite right_identity.
  reflexivity.
Defined.
Next Obligation.
  simpl in *.
  rewrite preserves_identity.
  rewrite left_identity.
  reflexivity.
Defined.
Next Obligation.
  simpl in *.
  rewrite compose_associative.
  reflexivity.
Defined.

Notation "D \ C" := (@functor_category _ _ C _ _ D) (at level 40, left associativity) : category_scope.