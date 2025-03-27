#check Quot

abbrev NatPair := Quot (α := Nat × Nat)
    (fun (a, b) (c, d) => a = d && b = c)

def smaller : NatPair → Nat :=
  Quot.lift (fun (a, b) => if a < b then a else b)
  (by
    intro (a, b) (c, d)
    simp
    intro h₁ h₂
    rw [← h₁, ← h₂]
    if h: a < b then
      simp [h]
      have h' : ¬ b <a := by
        simp [Nat.le_of_lt, h]
      simp [h']
    else
      simp [h]
      if h': b < a then
        simp [h']
      else
        simp [h']
        cases Nat.lt_trichotomy a b
        case inl hlt =>
          simp [hlt] at h
        case inr hge =>
          cases hge
          case inl heq =>
            simp [heq]
          case inr hgt =>
            simp [hgt] at h'
    )


def larger : NatPair → Nat :=
  Quot.lift (fun (a, b) => if a < b then b else a)
  (by
    intro (a, b) (c, d)
    simp
    intro h₁ h₂
    rw [← h₁, ← h₂]
    if h: a < b then
      simp [h]
      have h' : ¬ b <a := by
        simp [Nat.le_of_lt, h]
      simp [h']
    else
      simp [h]
      if h': b < a then
        simp [h']
      else
        simp [h']
        cases Nat.lt_trichotomy a b
        case inl hlt =>
          simp [hlt] at h
        case inr hge =>
          cases hge
          case inl heq =>
            simp [heq]
          case inr hgt =>
            simp [hgt] at h'
    )

abbrev NatPair.mk (a b : Nat) : NatPair :=
  Quot.mk (α := Nat × Nat) (fun (a, b) (c, d) => a = d && b = c) ((a, b) : Nat × Nat)

theorem smaller_le_larger (a b : Nat):
  smaller (NatPair.mk a b) ≤
    larger (NatPair.mk a b) :=
  by
    rw [NatPair.mk, smaller, larger]
    simp
    if h:a < b then
      simp [h]
      exact Nat.le_of_lt h
    else
      simp [h]
      exact Nat.le_of_not_gt h

#check Quot.ind
