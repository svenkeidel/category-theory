Require Export Category.
Require Export Functor.

(* Cat, the category of all categories *)

Definition Id {obj} (X:obj) := X.
Definition Compose {objC objD objE} (F: objD -> objE) (G: objC -> objD) (X:objC) : objE :=
  F (G X).
  
Program Instance IdFunctor {objC: Type} (C : objC -> objC -> Type) `{Category objC C}: Id :: C ~> C :=
{ map := fun X Y f => f
}.
Next Obligation.
  unfold Proper.
  unfold respectful.
  intros x y eq. rewrite eq.
  reflexivity.
Defined.
Next Obligation.
  unfold Id.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

(* Set Typeclasses Debug. *)
(* Set Printing Implicit. *)
Generalizable Variables objC C objD D objE E F G.

Program Instance ComposeFunctor
  `{Category objC C} `{Category objD D} `{Category objE E}
  `{F :: D ~> E} `{G :: C ~> D}
  : (Compose F G) :: C ~> E :=
{ map := fun x y f => map (F:=F) (map (F:=G) f) }.
Next Obligation.
  unfold Proper.
  unfold respectful.
  intros f g eq.
  enough (forall (X Y:objD) (f g : D X Y), f == g -> map (F:=F) f == map (F:=F) g).
  apply H4.
  rewrite eq.
  reflexivity.
  intros.
  rewrite H4.
  reflexivity.
Defined.
Next Obligation.
  rewrite preserves_identity.
  rewrite preserves_identity.
  reflexivity.
Defined.
Next Obligation.
  rewrite preserves_composition.
  rewrite preserves_composition.
  reflexivity.
Defined.

Definition SomeCategory : Type := { objC:Type & { C:objC -> objC -> Type & @Category objC C }}.
Inductive SomeFunctor (C D:SomeCategory) : Type := MkSomeFunctor :
  match C, D with
  | existT _ objC (existT _ c C_), existT _ objD (existT _ d D_) => 
      { F: objC -> objD & @Functor objC objD F c d C_ D_ }
  end -> SomeFunctor C D.

Program Instance FunctorSetoid : Setoid SomeFunctor :=
  {
    equiv := fun F G => _
  }.


Program Instance Cat : @Category SomeCategory SomeFunctor :=
{
  
}.
Next Obligation.