import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.MetricSpaces
import MAT740TopologyInLeanHS25.Definitions.Filters
import MAT740TopologyInLeanHS25.Definitions.Compactness

universe u

section Compactness

structure ballCover (I : Type u) (X : Type u) [MetricSpace X] where
  Cover : I → Set X
  ball_Cover : ∀ i, ∃ (ε : ℝ)(x : X), 0 < ε ∧ Cover i = Metric.ball x ε
  Is_Cover : (⋃ i, Cover i) = Set.univ

def increasing (n : ℕ → ℕ) : Prop :=
  ∀ m k : ℕ, m < k → n m < n k

def sequentiallyCompact (X : Type u) [MetricSpace X] : Prop
  := ∀ (x : ℕ → X), ∃ (n : ℕ → ℕ) (l : X), increasing n ∧ (MyFilter.eventuality (x ∘ n)) lim l


end Compactness

def Convergent {X : Type u} [Topology X] (F : MyFilter.Filter X) : Prop
  := ∃ (l : X), F lim l

def CauchySequ {X : Type u} [MetricSpace X] (x : ℕ → X) : Prop
  := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → dist (x m) (x n) < ε

def Complete (X : Type u) [MetricSpace X] : Prop
  := ∀ (x : ℕ → X), CauchySequ x → Convergent (MyFilter.eventuality x)


def CauchyFilt {X : Type u} [MetricSpace X] (F : MyFilter.Filter X) : Prop
  := MyFilter.properFilter F ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : Set X, A ∈ F ∧ ∀ (x : X) (y : X), x ∈ A → y ∈ A → dist x y < ε

def CauchyComplete (X : Type u) [MetricSpace X] : Prop
  := ∀ (F : MyFilter.Filter X), CauchyFilt F → Convergent F

def totallyBounded (X : Type u) [MetricSpace X] : Prop
  := ∀ ε : ℝ, 0 < ε → ∃ (I : Type u) (s : I → X), Finite I ∧ (X = ⋃ i, Metric.ball (s i) ε)

def filterTotallyBounded (X : Type u) [MetricSpace X] : Prop
  := ∀ (F : MyFilter.Filter X), MyFilter.ultraFilter F → CauchyFilt F

lemma partition_in_ultraFilter {X I : Type u} (s : I → Set X) (U : MyFilter.Filter X) :
    Finite I → (X = ⋃ i, s i) → MyFilter.ultraFilter U → ∃ i : I, (s i) ∈ U := by
  sorry

lemma ultraFilter_extension {X : Type u} [MetricSpace X] (F : MyFilter.Filter X) :
    MyFilter.properFilter F → ∃ (U : MyFilter.Filter X), MyFilter.ultraFilter U ∧ F ⊆ U := by
  sorry

lemma eventuality_is_proper {X : Type u} (x : ℕ → X) :
  MyFilter.properFilter (MyFilter.eventuality x) := by
  intro h
  obtain ⟨N, hN⟩ := h
  rw [Set.subset_empty_iff] at hN
  have w : x N ∈ MyFilter.tail x N := by
    use N
  rw [hN] at w
  contradiction

structure Stage (X : Type u) [MetricSpace X] (n : ℕ) (δ : ℝ) where
  (s : Fin n → X)
  (sep : ∀ i j : Fin n, i ≠ j → dist (s i) (s j) > δ / 2)

lemma not_totally_bounded_implies_separated {X: Type u} [MetricSpace X] (h: ¬ totallyBounded X) :
      ∃ (ε : ℝ) (s : ℕ → X), ε > 0 ∧ ∀ i j : ℕ, i ≠ j → dist (s i) (s j) > ε := by
  simp only [totallyBounded] at h
  push_neg at h
  obtain ⟨δ, hδ, h⟩ := h
  have v : ∀ (n : ℕ) (s : Fin n → X), ∃ x, ∀ i , dist x (s i) > δ/2 := by sorry
  have hs : ∀ n : ℕ, Stage X n δ := by
    intro n
    induction n with
    | zero =>
      -- trivial, since Fin 0 is the empty set
      -- (I don't really know why this code works)
      use Fin.elim0
      intro i
      exact i.elim0
    | succ n hn =>
      obtain ⟨s, hs⟩ := hn
      let x := Classical.choose (v n s)
      have hx : ∀ i : Fin n, dist x (s i) > δ / 2 :=
        Classical.choose_spec (v n s)
      refine ⟨
        Fin.snoc s x,
        ?_
      ⟩
      intro i j hij
      dsimp [Fin.snoc]

      -- We reason on whether i or j is the new index n
      have hi : i.val < n ∨ i.val = n :=
        Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt)
      have hj : j.val < n ∨ j.val = n :=
        Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt)

      cases hi with
      | inl hi_lt =>
        cases hj with
        | inl hj_lt =>
            -- both indices < n → reduce to old separation
            have hne : (⟨i.val, hi_lt⟩ : Fin n) ≠ ⟨j.val, hj_lt⟩ := by
              intro h
              apply hij
              cases i
              cases j
              cases h
              rfl
            simp [hi_lt, hj_lt]
            exact hs ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩ hne
        | inr hj_eq =>
            -- i < n, j = n → use hx
            simp [hi_lt, hj_eq]
            exact dist_comm (s (i.castLT hi_lt)) x ▸ hx (i.castLT hi_lt)
      | inr hi_eq =>
        cases hj with
        | inl hj_lt =>
            -- i = n, j < n → symmetric case
            simp [hi_eq, hj_lt]
            exact dist_comm (s (j.castLT hj_lt)) x ▸ hx (j.castLT hj_lt)
        | inr hj_eq =>
            -- both equal n → impossible
            exfalso
            apply hij
            apply Fin.ext
            rw [hi_eq, hj_eq]
  -- Finally define S
  let S : ℕ → X := fun n =>
    (hs (n+1)).s ⟨n, Nat.lt_succ_self n⟩

  have S_in_s : ∀ i j, (hij : i < j) → S i = (hs (j+1)).s ⟨i, Nat.lt_succ_of_lt hij⟩ := by
    intro i j hij
    induction j with
    | zero => -- impossible, since i < 0
      exact (Nat.not_lt_zero i hij).elim
    | succ j ih =>
      by_cases hlt : i < j
      · sorry
      · sorry


  use (δ / 2), S

  constructor
  · linarith
  · intro i j hij
    by_cases h : i < j
    · let si : Fin (j+1) := ⟨i, Nat.lt_succ_of_lt h⟩
      let sj : Fin (j+1) := ⟨j, Nat.lt_succ_self j⟩
      have hne : si ≠ sj := by sorry
      calc
      dist (S i) (S j)
          = dist ((hs (j+1)).s ⟨i, Nat.lt_succ_of_lt h⟩)
                  ((hs (j+1)).s ⟨j, Nat.lt_succ_self j⟩) := by
            rw [S_in_s i j h]
      _ > δ / 2 := (hs (j+1)).sep si sj hne
    -- case j < i
    · have hjlt : j < i := Nat.lt_of_le_of_ne (le_of_not_gt h) hij.symm
      let si : Fin (i+1) := ⟨i, Nat.lt_succ_self i⟩
      let sj : Fin (i+1) := ⟨j, Nat.lt_succ_of_lt hjlt⟩
      have hne : sj ≠ si := by sorry
      rw [dist_comm]
      calc
      dist (S j) (S i)
          = dist ((hs (i+1)).s ⟨j, Nat.lt_succ_of_lt hjlt⟩)
                  ((hs (i+1)).s ⟨i, Nat.lt_succ_self i⟩) := by
            rw [S_in_s j i hjlt]
      _ > δ / 2 := (hs (i+1)).sep sj si hne

lemma totallyBounded_iff_filterTotallyBounded {X : Type u} [MetricSpace X] :
    totallyBounded X ↔ filterTotallyBounded X := by
  constructor
  · intro hX
    intro F hF
    constructor
    · exact hF.1
    · intro ε hε
      specialize hX (ε / 2) (by positivity)
      obtain ⟨I, t, hI, hC⟩ := hX
      let s := fun i : I => Metric.ball (t i) (ε / 2)
      obtain ⟨i , hi⟩ := partition_in_ultraFilter s F hI hC hF
      use s i
      constructor
      · exact hi
      · intro x y hx hy
        simp only [s, Metric.mem_ball] at hx hy
        calc dist x y ≤ dist x (t i) + dist (t i) y := by exact dist_triangle x (t i) y
              _ < ε / 2 + ε / 2 := by
                rw [dist_comm (t i) y]
                exact add_lt_add hx hy
              _ = ε := by ring
  · intro hX
    by_contra htB
    obtain ⟨ε, s, hε, hs⟩ := not_totally_bounded_implies_separated htB
    let F := MyFilter.eventuality s
    obtain ⟨U, hU, hFU⟩ := ultraFilter_extension F (by exact eventuality_is_proper s)
    specialize hX U hU
    obtain ⟨hUP, hUC⟩ := hX
    specialize hUC ε hε
    obtain ⟨A, hAU, hA⟩ := hUC
    have w : ∃ i j : ℕ, i ≠ j ∧ s i ∈ A ∧ s j ∈ A := by
      by_contra h
      push_neg at h
      have v : ∃ i : ℕ, s i ∈ A := by
        by_contra h
        push_neg at h
        have v : Aᶜ ∈ F := by
          use 0
          intro x hx
          obtain ⟨j, hj, hjx⟩ := hx
          specialize h j
          rw [← hjx]
          exact h
        specialize hFU Aᶜ v
        have u := U.inter_Sets hAU hFU
        rw [Set.inter_compl_self] at u
        contradiction
      obtain ⟨i, hi⟩ := v
      specialize h i
      have v : Aᶜ ∈ F := by
        use (i + 1)
        intro x hx
        obtain ⟨j, hj, hjx⟩ := hx
        specialize h j
          (by
            rw [@Nat.ne_iff_lt_or_gt]
            left
            calc i < i + 1 := by exact lt_add_one i
                _ ≤ j := by exact hj
          ) hi
        rw [← hjx]
        exact h
      specialize hFU Aᶜ v
      have u := U.inter_Sets hAU hFU
      rw [Set.inter_compl_self] at u
      contradiction
    obtain ⟨i, j, hij, hiA, hjA⟩ := w
    specialize hA (s i) (s j) hiA hjA
    specialize hs i j hij
    have c : ε < ε := by
      calc ε < dist (s i) (s j) := by exact hs
          _ < ε := by exact hA
    exact (lt_irrefl ε c)

section UsefulLemmas



end UsefulLemmas
