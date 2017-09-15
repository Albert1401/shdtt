module Setoid
%access public export

Reflx : { A : Type } -> (R : A -> A -> Type) -> Type
Reflx {A} R = (x : A) -> R x x

Sym : { A : Type } -> (R : A -> A -> Type) -> Type
Sym {A} R = (x : A) -> (y : A ) -> R x y -> R y x

Trans : {A : Type} -> (R : A -> A -> Type) -> Type
Trans {A} R = (x, y, z : A) -> R x y -> R y z -> R x z

data IsEquality : {A : Type} -> (R : A -> A -> Type) -> Type where
  EqualityProof : {A : Type} -> {R : A -> A -> Type} -> Reflx R -> Sym R -> Trans R -> IsEquality R

record Setoid where
    constructor MkSetoid
    Carrier: Type
    Equality: Carrier -> Carrier -> Type
    Proof: IsEquality Equality
