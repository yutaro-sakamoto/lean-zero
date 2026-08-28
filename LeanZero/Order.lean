example (n : Nat) : Nat.succ n ≠ Nat.zero := by
  intro h
  injection h

example (m n : Nat) (h : Nat.succ m = Nat.succ n) : m = n := by
  injection h
