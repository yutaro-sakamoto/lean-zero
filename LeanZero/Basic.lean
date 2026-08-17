def hello := "world"

def eratosthenesAux (n : Nat) : Array Bool := Id.run do
  let mut isPrime := Array.replicate (n + 1) true
  isPrime := isPrime.set! 0 false
  isPrime := isPrime.set! 1 false

  for p in [1 : n + 1] do
    if not isPrime[p]! then
      continue
    if p ^ 2 > n then
      break

    let mut q := p * p
    while q ≤ n do
      isPrime := isPrime.set! q false
      q := q + p

  return isPrime

def eratosthenes (n : Nat) : Array Nat :=
  eratosthenesAux n
    |> .zipIdx
    |> .filterMap fun (isPrime, i) =>
      if isPrime then some i else none

#guard eratosthenes 10 = #[2, 3, 5, 7]

declare_syntax_cat compClause

syntax "for " term " in " term : compClause
syntax "if " term : compClause
syntax "[" term " | " compClause,* "]" : term

macro_rules
  | `([$t |]) => `([$t])
  | `([$t | for $x in $xs]) => `(List.map (fun $x => $t) $xs)
  | `([$t | if $x]) => `(if $x then [$t] else [])
  | `([$t | $c, $cs,*]) => `(List.flatten [[$t | $cs,*] | $c])

#guard [ x ^ 2 | for x in [1, 2, 3, 4, 5]] = [1, 4, 9, 16, 25]

#guard
  let lhs := [(x, y) | for x in [1, 2, 3], for y in [4, 5]]
  let rhs := [(1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)]
  lhs = rhs

#guard [x | for x in [1, 2, 3], if x < 2] =[1]

inductive MyNat where
  | zero
  | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ

#check MyNat.succ .zero

def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ .one

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => succ (add m n)
