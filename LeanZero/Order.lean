example (n : Nat) : Nat.succ n ≠ Nat.zero := by
  intro h
  injection h

example (m n : Nat) (h : Nat.succ m = Nat.succ n) : m = n := by
  injection h

example (m n : Nat) (h : m + 1 = n + 1) : m = n := by
  injection h

variable {l m n : Nat}

theorem Nat_add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero => simp_all
  | succ m ih =>
    have lem : (l + m) + 1 = (n + m) + 1 := calc
      _ = l + (m + 1) := by ac_rfl
      _ = n + (m + 1) := by rw [h]
      _ = (n + m) + 1 := by ac_rfl
    have : l + m = n + m := by
      injection lem
    exact ih this

theorem Nat_left_cancel (h : l + m = l + n) : m = n := by
  rw [Nat.add_comm l m, Nat.add_comm l n] at h
  apply Nat.add_right_cancel h
