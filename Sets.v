Set Warnings "-notation-overridden".

Require Export Category.

Set Universe Polymorphism.

Record SomeSet : Type :=
{
  carrier :> Type;
  carrier_setoid :> Setoid carrier
}.

Notation "Set[ X ]" := (@Build_SomeSet X _).

Record Function {X:Type} (S:Setoid X) {Y:Type} (S1:Setoid Y) :=
{
  function :> X -> Y;
  function_respects :>
    Proper (equiv ==> equiv ) function
}.
Arguments Function {X} S {Y} S1: assert.
Arguments function {X S Y S1} _ _: assert.
Arguments function_respects {X S Y S1} f x y _: assert.

Program Instance functions_setoid (X Y: SomeSet) : Setoid (Function X Y) :=
{
  equiv := fun f g => forall x, @equiv _ Y (f x) (g x)
}.
Next Obligation.
  split.
  - unfold Reflexive.
    intros f x. reflexivity.
  - unfold Symmetric.
    intros f g eq x.
    rewrite (eq x).
    reflexivity.
  - unfold Transitive.
    intros f g h eq1 eq2 x.
    rewrite (eq1 x).
    rewrite (eq2 x).
    reflexivity.
Defined.

Program Definition identity_function (X:SomeSet) : Function X X :=
{|
  function := fun x => x
|}.
Next Obligation.
  unfold Proper. unfold respectful.
  intros x y I. apply I.
Defined.

Program Definition compose_function
  {X Y Z: SomeSet} (f:Function Y Z) (g:Function X Y) : Function X Z :=
{|
  function := fun x => f (g x)
|}.
Next Obligation.
  unfold Proper; unfold respectful; simpl.
  intros.
  apply function_respects.
  apply function_respects.
  assumption.
Defined.

(* The category of sets and functions *)
Program Instance Sets : Category :=
{
  Obj := SomeSet;
  Hom := fun X Y => Function X Y;
  id := identity_function;
  compose := fun _ _ _ => compose_function
}.
Next Obligation.
  unfold Proper; unfold respectful.
  intros f f' eq1 g g' eq2 x.
  simpl in *.
  rewrite (eq1 (g x)).
  apply function_respects.
  rewrite (eq2 x).
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.