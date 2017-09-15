module Q

import Setoid
import Z

%default total

data Q = MkQ Z Nat

data EqQ : Q -> Q -> Type where
  ReflQ : (eq : EqZ (a `mulZNat` (S d)) (c `mulZNat` (S b))) -> EqQ (MkQ a b) (MkQ c d)

pr_reflEqQ : Reflx EqQ
pr_reflEqQ (MkQ a b) = ReflQ $ pr_reflEqZ (a `mulZNat` (S b))

pr_symEqQ : Sym EqQ
pr_symEqQ (MkQ a b) (MkQ c d) (ReflQ eq) = ReflQ $ pr_symEqZ (a `mulZNat` (S d)) (c `mulZNat` (S b)) eq

pr_transEqQ : Trans EqQ
pr_transEqQ (MkQ (MkZ a b) c) (MkQ (MkZ d e) f) (MkQ (MkZ g h) i) (ReflQ (ReflZ eq1)) (ReflQ (ReflZ eq2)) = ReflQ $ ReflZ $ elemNatRight (a * S i + h * S c) (b * S i + g * S c) f st7 where
  -- a * S f + e * S c = b * S f + d * S c
  -- d * S i + h * S f = e * S i + g * S f
  -- mult a (S i) + mult h (S c) = mult b (S i) + mult g (S c)
  multAssoCom : (a, b, c : Nat) -> a * b * c = a * c * b
  multAssoCom a b c = rewrite sym $ multAssociative a c b in
                      rewrite multCommutative c b in
                      sym $ multAssociative a b c

  st1 : a * S f * S i + e * S i * S c = b * S f * S i + d * S c * S i
  st1 = rewrite multAssoCom e (S i) (S c) in
        rewrite sym $ multDistributesOverPlusLeft (a * S f) (e * S c) (S i) in
        rewrite sym $ multDistributesOverPlusLeft (b * S f) (d * S c) (S i) in cong { f = (* S i) } eq1

  st2 : d * S c * S i + h * S f * S c = e * S i * S c + g * S f * S c
  st2 = rewrite multAssoCom d (S c) (S i) in
        rewrite sym $ multDistributesOverPlusLeft (d * S i) (h * S f) (S c) in
        rewrite sym $ multDistributesOverPlusLeft (e * S i) (g * S f) (S c) in cong { f = (* S c) } eq2

  eqSum : {a', b', c', d' : Nat} -> (a' = b') -> (c' = d') -> (a' + c' = b' + d')
  eqSum eq1' eq2' = rewrite eq2' in
                    rewrite eq1' in Refl

  st3 : (a * S f * S i + e * S i * S c) + (d * S c * S i + h * S f * S c) = (b * S f * S i + d * S c * S i) + (e * S i * S c + g * S f * S c)
  st3 = eqSum st1 st2

  f1 : (a,b,c,d, a', b', c', d' : Nat) -> (a + b) + (c + d) = (a' + b') + (c' + d') -> a + d + (b + c) = a' + d' + (c' + b')
  f1 a b c d a' b' c' d' eq = rewrite plusAssociative (a + d) b c in st7' where
    st1' : (a + b) + (d + c) = (a' + b') + (d' + c')
    st2' : (a + b) + d + c = (a' + b') + d' + c'
    st3' : (a + (b + d)) + c = (a' + (b' + d')) + c'
    st4' : (a + (d + b)) + c = (a' + (d' + b')) + c'
    st5' : a + d + b + c = (a' + d') + b' + c'
    st6' : a + d + b + c = a' + d' + (b' + c')
    st7' : a + d + b + c = a' + d' + (c' + b')
    st1' = rewrite (plusCommutative d c) in
           rewrite (plusCommutative d' c') in eq
    st2' = rewrite sym $ plusAssociative (a + b) d c in
           rewrite sym $ plusAssociative (a' + b') d' c' in st1'
    st3' = rewrite plusAssociative a b d in (rewrite plusAssociative a' b' d' in st2')
    st4' = rewrite plusCommutative d b in rewrite plusCommutative d' b' in st3'
    st5' = rewrite sym $ plusAssociative a d b in
           rewrite sym $ plusAssociative a' d' b' in st4'
    st6' = rewrite plusAssociative (a' + d') b' c' in st5'
    st7' = rewrite plusCommutative c' b' in st6'

  st4 : a * S f * S i + h * S f * S c + (e * S i * S c + d * S c * S i) = b * S f * S i + g * S f * S c + (e * S i * S c + d * S c * S i)
  st4 = f1 (a * S f * S i) (e * S i * S c) (d * S c * S i) (h * S f * S c) (b * S f * S i) (d * S c * S i) (e * S i * S c) (g * S f * S c) st3

  st5 : a * S f * S i + h * S f * S c = b * S f * S i + g * S f * S c
  st5 = plusRightCancel (a * S f * S i + h * S f * S c) (b * S f * S i + g * S f * S c) (e * S i * S c + d * S c * S i) st4

  st6 : a * S i * S f + h * S c * S f = b * S i * S f + g * S c * S f
  st6 = rewrite multAssoCom a (S i) (S f) in
        rewrite multAssoCom h (S c) (S f) in
        rewrite multAssoCom b (S i) (S f) in
        rewrite multAssoCom g (S c) (S f) in st5

  st7 : (a * S i + h * S c) * S f = (b * S i + g * S c) * S f
  st7 = rewrite multDistributesOverPlusLeft (b * S i) (g * S c) (S f) in
        rewrite multDistributesOverPlusLeft (a * S i) (h * S c) (S f) in st6


  f2 : (a',b',c' : Nat) -> (S c') * a' = (S c') * b' -> c' * a' = c' * b'
  f2 (S a') Z c' eq' = void $ SIsNotZ st1' where
    st1' : (S c') * (S a') = Z
    st1' = rewrite sym $ multZeroRightZero (S c') in eq'
  f2 Z (S b') c' eq' = void $ SIsNotZ $ sym st1' where
    st1' : Z = (S c') * (S b')
    st1' = rewrite sym $ multZeroRightZero (S c') in eq'
  f2 Z Z c' eq' = Refl
  f2 (S a') (S b') c' eq' = st3' where
    st1' : (S c') * a' = (S c') * b'
    st1' = plusLeftCancel (S c') ((S c') * a') ((S c') * b') (
        rewrite sym $ multRightSuccPlus (S c') b' in
        rewrite sym $ multRightSuccPlus (S c') a' in eq')
    st2' : c' + c' * a' = c' + c' * b'
    st2' = plusConstantLeft (c' * a') (c' * b') c' (f2 a' b' c' st1')

    st3' : c' * (S a') = c' * (S b')
    st3' = rewrite multRightSuccPlus c' a' in
           rewrite multRightSuccPlus c' b' in st2'


  elemNatRight : (a, b, c : Nat) -> a * (S c) = b * (S c) -> a = b
  elemNatRight a b Z eq = rewrite sym $ multOneRightNeutral b in
                          rewrite sym $ multOneRightNeutral a in eq
  elemNatRight a b (S c) eq = elemNatRight a b c st2' where
    st1' : (S (S c)) * a = (S (S c)) * b
    st1' = rewrite multCommutative (S (S c)) a in
           rewrite multCommutative (S (S c)) b in eq
    st2' : a * (S c) = b * (S c)
    st2' = rewrite multCommutative a (S c) in
           rewrite multCommutative b (S c) in f2 a b (S c) st1'

setQ : Setoid
setQ = MkSetoid Q EqQ (EqualityProof pr_reflEqQ pr_symEqQ pr_transEqQ)
