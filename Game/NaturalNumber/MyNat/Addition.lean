import Game.NaturalNumber.MyNat.Definition

namespace MyNat

opaque add : MyNat → MyNat → MyNat

instance instAdd : Add MyNat where
  add := add

axiom add_zero (a : MyNat) : a + 0 = a

axiom add_succ (a d : MyNat) : a + (succ d) = succ (a + d)
