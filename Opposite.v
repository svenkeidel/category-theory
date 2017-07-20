Require Export Category.

Generalizable Variables objC HomC C.

Program Instance op `{C: Category objC HomC} : Category (fun X Y => HomC Y X) :=
  @Build_Category objC (fun X Y => HomC Y X)
                       (fun X Y => c_oid (Category:=C) Y X)
                       (fun X => (id X : HomC X X))
                       (fun X Y Z f g => compose (Category:=C) g f)
                       _ _ _ _.
Next Obligation.
  unfold Proper. unfold respectful.
  intros f f' eq1 g g' eq2.
  rewrite eq1. rewrite eq2.
  reflexivity.
Defined.
Next Obligation.
  rewrite compose_associative.
  reflexivity.
Defined.

Arguments op {objC HomC} C : assert.
