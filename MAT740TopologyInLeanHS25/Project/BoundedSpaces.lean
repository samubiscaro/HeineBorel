import Mathlib.Tactic

import MAT740TopologyInLeanHS25.Definitions.MetricSpaces
import MAT740TopologyInLeanHS25.Definitions.Filters
import MAT740TopologyInLeanHS25.Project.CompleteSpaces


universe u

section definitions

def totallyBounded (X : Type u) [MetricSpace X] : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ (I : Type u) (s : I → X),
      Finite I ∧ ((Set.univ : Set X) = ⋃ i, Metric.ball (s i) ε)

def filterTotallyBounded (X : Type u) [MetricSpace X] : Prop
  := ∀ (F : MyFilter.Filter X), MyFilter.ultraFilter F → CauchyFilt F

end definitions


section ultraExtension

-- I decided to prove this lemma, mainly because the one implemented in Compactness
--  is hard to apply in my context (it uses FIP)
lemma ultraFilter_extension {X : Type u} [MetricSpace X] (F : MyFilter.Filter X) :
    MyFilter.properFilter F → ∃ (U : MyFilter.Filter X), MyFilter.ultraFilter U ∧ F ⊆ U := by
  classical
  intro hF

  let S : Set (Set (Set X)) :=
    { A | ∃ G, MyFilter.properFilter G ∧ F ⊆ G ∧ A = G.Sets}

  have hne : F.Sets ∈ S := by
    use F
    constructor
    · exact hF
    · constructor
      · exact fun ⦃a⦄ a ↦ a
      · rfl

  -- Chain hypothesis
  have chain :
      ∀ c ⊆ S, IsChain (fun x1 x2 ↦ x1 ⊆ x2) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c csS cChain cNe
    -- This is the candidate maximal element
    use ⋃₀ c
    constructor
    · -- Very annoying, we must show that it is indeed an element of S: a proper filter extending F
      let G : MyFilter.Filter X := {
        Sets := ⋃₀ c
        univ_Sets := by
          rw [Set.mem_sUnion]
          obtain ⟨t, ht⟩ := cNe
          use t
          constructor
          · exact ht
          · obtain ⟨H, a, b, d⟩ := csS ht
            rw [d]
            exact H.univ_Sets
        upward_Sets {A B} := by
          intro hA hAB
          rw [Set.mem_sUnion] at *
          obtain ⟨t, htc, hAt⟩ := hA
          use t
          constructor
          · exact htc
          · obtain ⟨H, a, b, d⟩ := csS htc
            rw [d] at hAt
            rw [d]
            exact H.upward_Sets hAt hAB
        inter_Sets {A B} := by
          intro hA hB
          rw [Set.mem_sUnion] at *
          obtain ⟨t1, ht1c, hAt1⟩ := hA
          obtain ⟨t2, ht2c, hBt2⟩ := hB
          by_cases h : t1 = t2
          · use t1
            constructor
            · exact ht1c
            · obtain ⟨H, a, b, d⟩ := csS ht1c
              rw [d]
              rw [d] at hAt1 h
              rw [←h] at hBt2
              exact H.inter_Sets hAt1 hBt2
          · have h : t1 ⊆ t2 ∨ t2 ⊆ t1 := cChain ht1c ht2c h
            cases h with
            | inl h =>
              use t2
              constructor
              · exact ht2c
              · obtain ⟨H, a, b, d⟩ := csS ht2c
                rw [d]
                rw [d] at hBt2 h
                exact H.inter_Sets (h hAt1) hBt2
            | inr h =>
              use t1
              constructor
              · exact ht1c
              · obtain ⟨H, a, b, d⟩ := csS ht1c
                rw [d]
                rw [d] at hAt1 h
                exact H.inter_Sets hAt1 (h hBt2)
      }
      use G
      constructor
      · intro h
        have h : ∅ ∈ ⋃₀ c := by
          exact h
        rw [Set.mem_sUnion] at h
        obtain ⟨t, htc, het⟩ := h
        specialize csS htc
        obtain ⟨H, a, b, d⟩ := csS
        apply a
        rw [d] at het
        exact het
      · constructor
        · intro A hA
          dsimp [G]
          rw [Set.mem_sUnion]
          obtain ⟨t, ht⟩ := cNe
          use t
          constructor
          · exact ht
          · specialize csS ht
            obtain ⟨H, a, b, d⟩ := csS
            rw [d]
            exact b hA
        · rfl
    · -- We have to show that ⋃₀ c is maximal for c, but this is by definition
      intro s hsc A hA
      rw [Set.mem_sUnion]
      use s

  -- Now just apply Zorn, very bad notation here but we get all we need in one line
  obtain ⟨USets, hU_mem, ⟨⟨U, hUP, hFU, hU⟩, Umax⟩⟩ :=
    zorn_subset_nonempty S chain F.Sets hne

  use U

  constructor
  · rw [MyFilter.ultra_iff_max]
    constructor
    · exact hUP
    · -- Classical Zorn argument, show that the maximal of S is a maximal filter
      intro G ⟨hGP, hUG⟩
      rw [MyFilter.ext_iff]
      intro A
      constructor
      · exact fun a ↦ hUG a
      · intro hA
        have w : G.Sets ∈ S := by
          use G
          constructor
          · exact hGP
          constructor
          · exact fun ⦃a⦄ a_1 ↦ hUG (hFU a_1)
          · rfl
        rw [← hU] at hUG
        specialize Umax w hUG
        specialize Umax hA
        rw [hU] at Umax
        exact Umax
  · exact hFU

end ultraExtension


section separated_sequence

-- This is the most difficult part of this section
-- We need to show that if a space is not totally bounded then there is
--  some ε and a sequence x that is ε separated

-- We will need some recursion, I was not able to use it, in the end I opted
--  for adding a structure that makes me build the finite sequences

structure Stage (X : Type u) [MetricSpace X] (n : ℕ) (δ : ℝ) where
  (s : Fin n → X)
  (sep : ∀ i j : Fin n, i ≠ j → dist (s i) (s j) > δ / 2)

lemma not_totally_bounded_implies_separated {X : Type u} [MetricSpace X] (h : ¬ totallyBounded X) :
      ∃ (ε : ℝ) (s : ℕ → X), ε > 0 ∧ ∀ i j : ℕ, i ≠ j → dist (s i) (s j) > ε := by
  simp only [totallyBounded] at h
  push_neg at h
  obtain ⟨δ, hδ, h⟩ := h
  have v : ∀ (I : Type u) (s : I → X), Finite I →  ∃ x, ∀ i , dist x (s i) > δ/2 := by
    intro I s hI
    have w : ∃ x, x ∉ (⋃ i, Metric.ball (s i) δ) := by
      by_contra hx
      apply h I s hI
      push_neg at hx
      rw [← Set.eq_univ_iff_forall] at hx
      exact id (Eq.symm hx)
    obtain ⟨x, hx⟩ := w
    use x
    intro i
    have v : x ∉ Metric.ball (s i) δ := by
      intro hx'
      apply hx
      rw [@Set.mem_iUnion]
      exact ⟨i, hx'⟩
    by_contra w
    apply v
    rw [Metric.mem_ball]
    calc
      dist x (s i) ≤ δ / 2 := le_of_not_gt w
      _ < δ := div_two_lt_of_pos hδ

  -- We will now buil the truncated sequences, they will be "inscatulated"
  let hs : ∀ n : ℕ, Stage X n δ := by
    intro n
    induction n with
    | zero =>
      -- trivial, since Fin 0 is the empty set
      use Fin.elim0
      intro i
      exact i.elim0
    | succ n hn =>
      -- I don't really know why this code works,
      --  it is some mess with Fin n not being considered a Set
      -- But the idea is simple: suppose we have s : Fin n → X
      --  take an ε-distant point x from all s i, and define s n to be this x
      obtain ⟨s, hs⟩ := hn
      let x := Classical.choose (v (ULift (Fin n)) (fun i => s (ULift.down i)) (by infer_instance))
      have hx : ∀ i : Fin n, dist x (s i) > δ / 2 := by
        intro i
        let H := Classical.choose_spec
          (v (ULift (Fin n)) (fun i => s (ULift.down i)) (by infer_instance))
        exact H (ULift.up i)
      refine ⟨
        Fin.snoc s x,
        ?_
      ⟩
      -- We "appended" x to the old sequence, now we prove the separation
      intro i j hij
      dsimp [Fin.snoc]
      have hi : i.val < n ∨ i.val = n :=
        Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt)
      have hj : j.val < n ∨ j.val = n :=
        Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt)
      -- Separating the cases
      cases hi with
      | inl hi_lt =>
        cases hj with
        | inl hj_lt =>
            -- both indices < n
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
            -- i < n, j = n
            simp [hi_lt, hj_eq]
            exact dist_comm (s (i.castLT hi_lt)) x ▸ hx (i.castLT hi_lt)
      | inr hi_eq =>
        cases hj with
        | inl hj_lt =>
            -- i = n, j < n
            simp [hi_eq, hj_lt]
            exact dist_comm (s (j.castLT hj_lt)) x ▸ hx (j.castLT hj_lt)
        | inr hj_eq =>
            -- both equal n (not possible)
            exfalso
            apply hij
            apply Fin.ext
            rw [hi_eq, hj_eq]

  -- They are inscatolated
  have exte : ∀ i j, (hij : i < j) →
      (hs (i+1)).s ⟨i, Nat.lt_succ_self i⟩ = (hs (j+1)).s ⟨i, Nat.lt_succ_of_lt hij⟩ := by
    intro i j hij
    induction j with
    | zero => exact (Nat.not_lt_zero i hij).elim
    | succ j hj =>
      have hi : i < j ∨ i = j :=
        Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij)
      cases hi with
      | inl hi_lt =>
        specialize hj hi_lt
        rw [hj]
        dsimp [hs]
        simp [Fin.snoc, hi_lt]
        intro hji
        by_contra
        have hh : i < i := by
          calc
            i < j+1 := hij
            _ ≤ i := hji
        exact (lt_self_iff_false i).mp hh
      | inr hi_eq =>
        subst hi_eq
        dsimp [hs, Fin.snoc]
        simp only [lt_self_iff_false, ↓reduceDIte, gt_iff_lt, ULift.forall, lt_add_iff_pos_right,
          zero_lt_one, ↓reduceIte]

  -- Finally define S: this is a classical construction in set theory
  let S : ℕ → X := fun n =>
    (hs (n+1)).s ⟨n, Nat.lt_succ_self n⟩

  use (δ / 2), S

  constructor
  · linarith
  · intro i j hij
    by_cases h : i < j
    · calc
      dist (S i) (S j)
      = dist ((hs (j+1)).s ⟨i, Nat.lt_succ_of_lt h⟩)
              ((hs (j+1)).s ⟨j, Nat.lt_succ_self j⟩) := by
            dsimp [S]
            specialize exte i j h
            rw [exte]
      _ > δ / 2 := (hs (j+1)).sep
          ⟨i, Nat.lt_succ_of_lt h⟩ ⟨j, Nat.lt_succ_self j⟩ (Fin.ne_of_val_ne hij)
    · -- just the same
      have hji : j < i := Nat.lt_of_le_of_ne (le_of_not_gt h) hij.symm
      rw [dist_comm]
      calc
      dist (S j) (S i)
          = dist ((hs (i+1)).s ⟨j, Nat.lt_succ_of_lt hji⟩)
                  ((hs (i+1)).s ⟨i, Nat.lt_succ_self i⟩) := by
            dsimp [S]
            specialize exte j i hji
            rw [exte]
      _ > δ / 2 := (hs (i+1)).sep
          ⟨j, Nat.lt_succ_of_lt hji⟩ ⟨i, Nat.lt_succ_self i⟩ (Fin.ne_of_val_ne (id (Ne.symm hij)))

end separated_sequence


section totallyBounded_iff_filterTotallyBounded

-- Now that we've done the hard lemma we can prove the main theorem of the section

lemma totallyBounded_iff_filterTotallyBounded {X : Type u} [MetricSpace X] :
    totallyBounded X ↔ filterTotallyBounded X := by
  constructor
  · intro hX
    intro F hF
    -- We need to show that F is a Cauchy filter
    constructor
    · exact hF.1
    · intro ε hε
      specialize hX (ε / 2) (by positivity)
      -- Partition the space in finitely many ε-balls ...
      obtain ⟨I, t, hI, hC⟩ := hX
      --  ... one of them must be in F ...
      rw [MyFilter.ultra_iff_prime] at hF
      let C := Set.range (fun i : I => Metric.ball (t i) (ε / 2))
      have Cfin : C.Finite := Set.finite_range fun i ↦ Metric.ball (t i) (ε / 2)
      have CsUn : ⋃₀ C ∈ F := by
        simpa [C, hC, Set.sUnion_range] using (F.univ_Sets)
      obtain ⟨c, hc, hcF⟩ := MyFilter.prime_finite_sUnion hF Cfin CsUn
      -- ... this is our ε-small set
      use c
      constructor
      · exact hcF
      · intro x y hx hy
        obtain ⟨i, hi⟩ := hc
        rw [← hi, Metric.mem_ball] at hx hy
        calc dist x y ≤ dist x (t i) + dist (t i) y := by exact dist_triangle x (t i) y
              _ < ε / 2 + ε / 2 := by
                rw [dist_comm (t i) y]
                exact add_lt_add hx hy
              _ = ε := by ring
  · -- Mathematically it's not difficult, suppose X is not totally bounded ...
    intro hX
    by_contra htB
    -- ... take an ε separated sequence s ...
    obtain ⟨ε, s, hε, hs⟩ := not_totally_bounded_implies_separated htB
    -- ... take its eventuality filter F ...
    let F := MyFilter.eventuality s
    -- ... extend it to an ultrafilter U ...
    obtain ⟨U, hU, hFU⟩ := ultraFilter_extension F (by exact eventuality_is_proper s)
    specialize hX U hU
    obtain ⟨hUP, hUC⟩ := hX
    -- ... each A ∈ U containsinfinitely many elements of s, but they are ε-separated
    --  so U is an ultrafilter but not a Cauchy filter
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
        specialize hFU v
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
      specialize hFU v
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

end totallyBounded_iff_filterTotallyBounded
