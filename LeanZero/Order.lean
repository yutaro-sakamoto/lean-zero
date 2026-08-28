example (n : Nat) : Nat.succ n ≠ Nat.zero := by
  intro h
  injection h
