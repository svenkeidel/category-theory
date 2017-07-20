Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export NaturalIsomorphism.

(* Cat, the category of all categories *)

(* Ltac id_nat := *)
(*   unfold NaturalTransformation; *)
(*   intros X Y f; *)
(*   rewrite left_identity; *)
(*   rewrite right_identity; *)
(*   reflexivity. *)

(* Ltac id_nat_iso := *)
(*   unfold NaturalIsomorphism; *)
(*   intros X; *)
(*   unfold Isomorphism; *)
(*   unfold Compose₀; *)
(*   unfold Id₀; *)
(*   rewrite left_identity; *)
(*   split; *)
(*   reflexivity. *)

(* Natural transformations that proof identity and associativity laws of Cat. *)
(* Definition compose_id *)
(*   `{C: Category objC HomC} `{D: Category objD HomD}  *)
(*   `{F: F₀ :: C ~> D} *)
(*   : ((fun X => id (F₀ X)) :: Compose F Id ≈> F). *)
(* Proof.  *)
(*   id_nat. *)
(* Defined. *)

(* Definition compose_id_inverse *)
(*   `{C: Category objC HomC} `{D: Category objD HomD}  *)
(*   `{F: F₀ :: C ~> D} *)
(*   : ((fun X => id (F₀ X)) :: F ≈> Compose F Id). *)
(* Proof.  *)
(*   id_nat. *)
(* Defined. *)

(* Definition compose_id_iso *)
(*   `{C: Category objC HomC} `{D: Category objD HomD}  *)
(*   `{F: F₀ :: C ~> D} *)
(*   : [ compose_id ] Compose F Id <≈> F [ compose_id_inverse ]. *)
(* Proof. *)
(*   id_nat_iso. *)
(* Defined. *)

(* Definition id_compose *)
(*   `{C: Category objC HomC} `{D: Category objD HomD}  *)
(*   `{F: F₀ :: C ~> D} *)
(*   : ((fun X => id (F₀ X)) :: Compose Id F ≈> F). *)
(* Proof.  *)
(*   id_nat. *)
(* Defined. *)

(* Definition id_compose_inverse *)
(*   `{C: Category objC HomC} `{D: Category objD HomD}  *)
(*   `{F: F₀ :: C ~> D} *)
(*   : ((fun X => id (F₀ X)) :: F ≈> Compose Id F). *)
(* Proof.  *)
(*   id_nat. *)
(* Defined. *)

(* Definition id_compose_iso *)
(*   `{C: Category objC HomC} `{D: Category objD HomD}  *)
(*   `{F: F₀ :: C ~> D} *)
(*   : [ id_compose ] Compose Id F <≈> F [ id_compose_inverse ]. *)
(* Proof. *)
(*   id_nat_iso. *)
(* Defined. *)

(* Definition compose_assoc *)
(*   `{A: Category objA HomA} `{B: Category objB HomB} *)
(*   `{C: Category objC HomC} `{D: Category objD HomD} *)
(*   `{F: F₀ :: C ~> D} `{G: G₀ :: B ~> C} `{H: H₀ :: A ~> B} *)
(*   : ((fun X => id (F₀ (G₀ (H₀ X)))) :: *)
(*      Compose (Compose F G) H ≈> Compose F (Compose G H)). *)
(* Proof. *)
(*   id_nat. *)
(* Defined. *)

(* Definition compose_assoc_inverse *)
(*   `{A: Category objA HomA} `{B: Category objB HomB} *)
(*   `{C: Category objC HomC} `{D: Category objD HomD} *)
(*   `{F: F₀ :: C ~> D} `{G: G₀ :: B ~> C} `{H: H₀ :: A ~> B} *)
(*   : ((fun X => id (F₀ (G₀ (H₀ X)))) :: *)
(*      Compose F (Compose G H) ≈> Compose (Compose F G) H). *)
(* Proof. *)
(*   id_nat. *)
(* Defined. *)

(* Definition compose_assoc_iso *)
(*   `{A: Category objA HomA} `{B: Category objB HomB} *)
(*   `{C: Category objC HomC} `{D: Category objD HomD} *)
(*   `{F: F₀ :: C ~> D} `{G: G₀ :: B ~> C} `{H: H₀ :: A ~> B} *)
(*   : [ compose_assoc (F:=F) (G:=G) (H:=H) ] *)
(*       Compose F (Compose G H) <≈> Compose (Compose F G) H *)
(*     [ compose_assoc_inverse  (F:=F) (G:=G) (H:=H) ]. *)
(* Proof. *)
(*   id_nat_iso. *)
(* Defined. *)

(* Definition SomeCategory : Type := { objC:Type & { C:objC -> objC -> Type & @Category objC C }}. *)
(* Definition objects (C:SomeCategory) : Type := projT1 C. *)
(* Definition hom (C:SomeCategory) *)
(*   : objects C -> objects C -> Type := projT1 (projT2 C). *)
(* Definition category (C:SomeCategory) *)
(*   : @Category (objects C) (hom C) := projT2 (projT2 C). *)

(* Ltac unfold_some_category := *)
(*   unfold hom in *; *)
(*   unfold category in *; *)
(*   unfold objects in *; *)
(*   simpl in *. *)

Program Instance functor_setoid
  {C D: Category}
  : Setoid (Functor C D) :=
{ equiv := fun F G =>
    exists (eta : NaturalTransformation F G) (theta: NaturalTransformation G F),
      natural_isomorphic eta theta
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros F.
    exists (id_natural_transformation F).
    exists (id_natural_transformation F).
    apply (id_natural_isomorphism F).
  - unfold Symmetric.
    intros F G.
    intros [eta [theta I]].
    exists theta; exists eta.
    apply (natural_isomorphic_symmetry eta theta I).
  - unfold Transitive.
    intros F G H [eta [theta I]] [eta' [theta' J]].
    exists (vertical_composition eta' eta).
    exists (vertical_composition theta theta').
    apply (natural_iso_preserved_under_vertical_composition I J).
Defined.

Program Instance Cat : Category :=
{
  Obj := Category;
  Hom := Functor;
  id := identity_functor;
  compose := fun _ _ _ => compose_functor
}.
(* Next Obligation. *)
(*   unfold Proper; unfold respectful. *)
(*   intros F G. *)
(* Next Obligation. *)
(*   destruct X as [objC [C C']]. *)
(*   unfold hom. *)
(*   simpl. *)
(*   exists Id₀. *)
(*   apply Id. *)
(* Defined. *)
(* Next Obligation. *)
(*   destruct X as [objC [C C']]. *)
(*   destruct Y as [objD [D D']]. *)
(*   destruct Z as [objE [E E']]. *)
(*   unfold_some_category. *)
(*   rename X0 into F₀. *)
(*   rename X3 into F. *)
(*   rename X1 into G₀. *)
(*   rename X2 into G. *)
(*   exists (Compose₀ F₀ G₀). *)
(*   apply (Compose F G). *)
(* Defined. *)
Next Obligation.
  rename X into C.
  rename Y into D.
  rename Z into E.
  unfold Proper; unfold respectful.
  intros F G [eta [theta I]].
  intros H J [eta' [theta' K]].
  exists (horizontal_composition eta' eta).
  exists (horizontal_composition theta' theta).
  simpl.
  apply (horizontal_composition_iso theta_iso eta_iso).
Defined.
Next Obligation.
  destruct X as [objC [HomC C]].
  destruct Y as [objD [HomD D]].
  unfold_some_category.
  rename f into F₀.
  rename X0 into F.
  exists (exists_natural_trans (compose_id (F:=F)),
          exists_natural_trans (compose_id_inverse (F:=F))).
  simpl.
  apply compose_id_iso.
Defined.
Next Obligation.
  destruct X as [objC [HomC C]].
  destruct Y as [objD [HomD D]].
  unfold_some_category.
  rename f into F₀.
  rename X0 into F.
  exists (exists_natural_trans (id_compose (F:=F)),
          exists_natural_trans (id_compose_inverse (F:=F))).
  simpl.
  apply id_compose_iso.
Defined. 
Next Obligation.
  destruct X as [objA [HomA A]].
  destruct Y as [objB [HomB B]].
  destruct Z as [objC [HomC C]].
  destruct U as [objD [HomD D]].
  unfold_some_category.
  rename f into F₀.
  rename X2 into F.
  rename g into G₀.
  rename X1 into G.
  rename h into H₀.
  rename X0 into H.
  exists (exists_natural_trans (compose_assoc (F:=F) (G:=G) (H:=H)),
          exists_natural_trans (compose_assoc_inverse (F:=F) (G:=G) (H:=H))).
  simpl.
  apply (compose_assoc_iso (F:=F) (G:=G) (H:=H)).
Defined.