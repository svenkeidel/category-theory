Require Export Category.
Require Export Functor.
Require Export NaturalIsomorphism.

(* Cat, the category of all categories *)

Definition SomeCategory : Type := { objC:Type & { C:objC -> objC -> Type & @Category objC C }}.

Definition objects (C:SomeCategory) : Type := projT1 C.
Definition hom (C:SomeCategory) : objects C -> objects C -> Type := projT1 (projT2 C).
Definition category (C:SomeCategory) : @Category (objects C) (hom C) :=
  projT2 (projT2 C).

Program Instance Cat : @Category SomeCategory
  (fun C D => { F : _ & @Functor (objects C) (hom C) (category C)
                                 (objects D) (hom D) (category D)
                                 F
                                 }).
Next Obligation.
  destruct X as [objC [C C']].
  unfold hom.
  simpl.
  exists Id₀.
  apply Id.
Defined.
Next Obligation.
  destruct X as [objC [C C']].
  destruct Y as [objD [D D']].
  destruct Z as [objE [E E']].
  unfold hom in *.
  unfold category in *.
  unfold objects in *.
  rename X0 into F₀.
  rename X3 into F.
  rename X1 into G₀.
  rename X2 into G.
  simpl in *.
  exists (Compose₀ F₀ G₀).
  apply (Compose F G).
Defined.
Next Obligation.
  destruct X as [objC [C C']].
  destruct Y as [objD [D D']].
  destruct Z as [objE [E E']].
  simpl in *.
  unfold hom in *.
  unfold category in *.
  unfold objects in *.
  simpl in *.
  unfold Proper.
  unfold respectful.
  intros [F₀ F] [G₀ G] [[[eta₁ eta] [eta₁' eta']] eta_iso].
  intros [H₀ H] [J₀ J] [[[theta₁ theta] [theta₁' theta']] theta_iso].
  simpl in *.
  exists (exists_natural_trans (horizontal_composition theta eta),
          exists_natural_trans (horizontal_composition theta' eta')).
  simpl.
  apply (horizontal_composition_iso theta_iso eta_iso).
Defined.
Next Obligation.
  destruct X as [objC [HomC C]].
  destruct Y as [objD [HomD D]].
  simpl in *.
  unfold hom in *.
  unfold category in *.
  unfold objects in *.
  simpl in *.
  rename f into F₀.
  rename X0 into F.
  exists (id_natural_transformation F,
          id_natural_transformation F).

  exists (fun X => id (F X)).
  exists (fun X => id (F X)).
