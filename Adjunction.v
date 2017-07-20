Require Export Category.
Require Export Functor.
Require Export NaturalTransformation.
Require Export Isomorphism.

Generalizable Variables objC HomC C objD HomD D F₀ G₀ H₀ J₀ eta₁ theta₁.
Definition HomSetAdjunction
  `{C: Category objC HomC} `{D: Category objD HomD} 
  `{F: F₀ :: C ~> D} `{G: G₀ :: D ~> C}
  := NaturalTransformation (C:=C) (D:=set) (F:=
       (fun X Y => Isomorphism (HomC (F₀ X) Y) (HomD X (G₀ Y))).


