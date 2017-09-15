module Z
import Setoid

%access public export
%default total
data Z : Type where
  MkZ : Nat -> Nat -> Z

data EqZ : Z -> Z -> Type where
  ReflZ : (eq : a + d = b + c) -> EqZ (MkZ a b) (MkZ c d)


pr_reflEqZ : Reflx EqZ
pr_reflEqZ {x = (MkZ a b)} = ReflZ $ plusCommutative a b

pr_symEqZ : Sym EqZ
pr_symEqZ { x = MkZ a b } { y = MkZ c d } (ReflZ eq) = ReflZ $ sym eq2 where
  eq1 : d + a = b + c
  eq1 = rewrite (plusCommutative d a) in eq

  eq2 : d + a = c + b
  eq2 = rewrite (plusCommutative c b) in eq1


addZZ : Z -> Z -> Z
addZZ (MkZ a b) (MkZ c d) = MkZ (a + c) (b + d)

negZ : Z -> Z
negZ (MkZ a b) = MkZ b a

mulZNat : Z -> Nat -> Z
mulZNat (MkZ a b) n = MkZ (a * n) (b * n)

mulZZ : Z -> Z -> Z
mulZZ (MkZ a b) (MkZ c d) = MkZ (a * c + b * d) (a * d + b * c)

pr_transEqZ : Trans EqZ
pr_transEqZ {x = MkZ a b} {y = MkZ c d } {z = MkZ e f} (ReflZ eq1) (ReflZ eq2) = ReflZ s9 where
  s1 : a + d + f = b + c + f
  s2 : a + (d + f) = b + c + f
  s3 : a + (f + d) = b + c + f
  s4 : a + f + d = b + c + f
  s5 : a + f + d = b + (c + f)
  s6 : a + f + d = b + (d + e)
  s7 : a + f + d = b + (e + d)
  s8 : a + f + d = b + e + d
  s9 : a + f = b + e

  s1 = plusConstantRight (a + d) (b + c) f eq1
  s2 = rewrite plusAssociative a d f in s1
  s3 = rewrite plusCommutative f d in s2
  s4 = rewrite sym $ plusAssociative a f d in s3
  s5 = rewrite plusAssociative b c f in s4
  s6 = rewrite sym $ eq2 in s5
  s7 = rewrite plusCommutative e d in s6
  s8 = rewrite sym $ plusAssociative b e d in s7
  s9 = plusRightCancel (a + f) (b + e) d s8

setZ : Setoid
setZ = MkSetoid Z EqZ (EqualityProof pr_reflEqZ pr_symEqZ pr_transEqZ)
