import Game.NaturalNumber.MyNat.Definition
import Game.NaturalNumber.MyNat.Multiplication

namespace MyNat

opaque pow : MyNat → MyNat → MyNat

instance : Pow MyNat MyNat where
  pow := pow

macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : MyNat) ($y : MyNat))

axiom pow_zero (a : MyNat) : a ^ 0 = 1

axiom pow_succ (m n : MyNat) : m ^ (succ n) = m ^ n * m
