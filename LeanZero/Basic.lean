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
