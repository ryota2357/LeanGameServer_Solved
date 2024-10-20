import Game.NaturalNumber.MyNat.Definition

namespace MyNat

opaque add : MyNat → MyNat → MyNat

instance : Add MyNat where
  add := add

axiom add_zero (a : MyNat) : a + 0 = a

axiom add_succ (a d : MyNat) : a + (succ d) = succ (a + d)
