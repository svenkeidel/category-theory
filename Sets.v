Require Export Category.

Program Instance set_setoid (X Y:Type) `{Setoid Y} : Setoid (X -> Y) :=
{
  equiv := fun f g => forall x, f x == g x
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

Definition Functions (X Y: { obj : Type & Setoid obj }) : Type.
  destruct X as [X setoidX].
  destruct Y as [Y setoidY].
  apply ({ f : X -> Y & Proper (equiv ==> equiv) f}).
Defined.

(* The category of sets and functions *)
Check @equiv.
Program Instance Sets : Category (obj:={ obj : Type & Setoid obj })
                                 Functions.
Next Obligation.
  simpl.
  apply (set_setoid X Y).
Defined.
Next Obligation.
Next Obligation.
  unfold Proper.
  unfold respectful.
  intros f f' eq1 g g' eq2 x.
  simpl in *.
  rewrite (eq1 (g x)).
  rewrite (eq2 x).
  reflexivity.
Defined.

  (* c_oid := fun X Y => set_setoid (projT1 X) (projT1 Y); *)
  (* id := fun _ x => x; *)
  (* compose := fun _ _ _ f g x => f (g x) *)