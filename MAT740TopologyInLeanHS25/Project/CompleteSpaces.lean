import Mathlib.Tactic

import MAT740TopologyInLeanHS25.Definitions.MetricSpaces
import MAT740TopologyInLeanHS25.Definitions.Filters

universe u

section definitions

def Convergent {X : Type u} [Topology X] (F : MyFilter.Filter X) : Prop :=
    ∃ (l : X), F lim l

def CauchySequ {X : Type u} [MetricSpace X] (x : ℕ → X) : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → dist (x m) (x n) < ε

-- Cauchy filters are the generalisation of Cauchy seuences
def CauchyFilt {X : Type u} [MetricSpace X] (F : MyFilter.Filter X) : Prop :=
    MyFilter.properFilter F ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : Set X, A ∈ F ∧ ∀ (x : X) (y : X), x ∈ A → y ∈ A → dist x y < ε

def Complete (X : Type u) [MetricSpace X] : Prop :=
    ∀ (x : ℕ → X), CauchySequ x → Convergent (MyFilter.eventuality x)

def filterComplete (X : Type u) [MetricSpace X] : Prop :=
    ∀ (F : MyFilter.Filter X), CauchyFilt F → Convergent F

-- This is probably not the true definition of adherent filter, but it's useful for us
--  maybe I could rename it but I think adherent gives the right idea
def adherent {X : Type u} [Topology X] (F G : MyFilter.Filter X) : Prop :=
    ∀ (A B : Set X) (l : X), G lim l → A ∈ F → Nbhd B l → A ∩ B ≠ ∅

end definitions


section lemmas

-- We will use often this facts

lemma Open_Ball {X : Type u} [MetricSpace X] {x : X} {ε : ℝ} :
  @Open X metricTopology (Metric.ball x ε) := by
  rw [Open_basisTopology]
  intro y hy
  obtain ⟨δ, hδ1, hδ2⟩ := ball_in_ball y hy
  use Metric.ball y δ
  constructor
  · exact Basic_balls
  · constructor
    · exact Metric.mem_ball_self hδ1
    · exact hδ2

lemma eventuality_is_proper {X : Type u} (x : ℕ → X) :
  MyFilter.properFilter (MyFilter.eventuality x) := by
  intro h
  obtain ⟨N, hN⟩ := h
  rw [Set.subset_empty_iff] at hN
  have w : x N ∈ MyFilter.tail x N := by
    use N
  rw [hN] at w
  contradiction

lemma adherent_if_contained {X : Type u} [Topology X] (F G : MyFilter.Filter X) :
    F ⊆ G → MyFilter.properFilter G → adherent F G := by
  intro h hGP A B l hl hA hB
  specialize hl hB
  specialize h hA
  have w : A ∩ B ∈ G := by exact G.inter_Sets h hl
  intro he
  rw [he] at w
  contradiction

end lemmas

section CauchyFilters

-- We will now prove some properties of Cauchy filters

-- Like in the case of sequences we have the following:
lemma convergentFilt_is_Cauchy {X : Type u} [MetricSpace X] (F : MyFilter.Filter X) :
  MyFilter.properFilter F → Convergent F → CauchyFilt F := by
intro hP hC
constructor
· exact hP
· intro ε hε
  obtain ⟨l, hl⟩ := hC
  use Metric.ball l (ε / 2)
  constructor
  · apply hl
    constructor
    · rw [Open_basisTopology]
      intro x hx
      use Metric.ball l (ε / 2)
      simp only [Basic_balls, Metric.mem_ball, subset_refl, and_true, true_and]
      exact hx
    · rw [Metric.mem_ball, dist_self]
      exact half_pos hε
  · intro x y hx hy
    rw [Metric.mem_ball] at hx hy
    calc dist x y ≤ dist x l + dist l y := by apply dist_triangle x l y
          _ = dist x l + dist y l := by rw [dist_comm l y]
          _ < ε / 2 + ε / 2 := by
            apply add_lt_add hx hy
          _ = ε := by ring

-- If F is a Cauchy filter adherent to G, then F converges to the same limit as G
lemma CauchyFilter_converge_to_adeherent {X : Type u}
    [MetricSpace X] (F : MyFilter.Filter X) (G : MyFilter.Filter X) :
    CauchyFilt F → adherent F G → Convergent G → Convergent F := by
  intro hFC hFG hGC
  obtain ⟨l, hl⟩ := hGC
  use l
  intro C hC
  -- The idea here is to find a "small" element of F that is inside of the neighborhood C
  --  so that then C ∈ F
  have w1 : ∃ A : Set X, A ∈ F ∧ A ⊆ C := by
    obtain ⟨hC, hlC⟩ := hC
    rw [Open_basisTopology] at hC
    specialize hC l hlC
    obtain ⟨D, ⟨x, ε, DB⟩, hlD, hDsB⟩ := hC
    rw [DB] at hlD
    obtain ⟨hFP, hFC⟩ := hFC
    obtain ⟨δ, hδ1, hδ2⟩ := ball_in_ball l hlD
    specialize hFC (δ / 2) (by apply half_pos; exact hδ1)
    obtain ⟨A, hAinF, hAdist⟩ := hFC
    use A
    constructor
    · exact hAinF
    · intro y hy
      specialize hFG A (Metric.ball l (δ / 2)) l hl hAinF
        (by
          constructor
          · exact Open_Ball
          · exact Metric.mem_ball_self (by apply half_pos; exact hδ1)
        )
      rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def] at hFG
      obtain ⟨b, hb1, hb2⟩ := hFG
      apply hDsB
      rw [DB]
      apply hδ2
      rw [Metric.mem_ball]
      calc dist y l ≤ dist y b + dist b l := by apply dist_triangle y b l
            _ < δ / 2 + δ / 2 := by
              apply add_lt_add
              · specialize hAdist y b hy hb1
                exact hAdist
              · rw [Metric.mem_ball] at hb2
                exact hb2
            _ = δ := by ring
  obtain ⟨A, hAF, hAB⟩ := w1
  exact F.upward_Sets hAF hAB

-- Now, we prove that every Cauchy filter in a metric space admits a "Cauchy subsequence"
--  this is the most annoying part of this section, but mathematically it's not difficult

lemma CauchyFilter_has_CauchySequ {X : Type u} [MetricSpace X] (F : MyFilter.Filter X) :
    CauchyFilt F → ∃ (x : ℕ → X), CauchySequ x ∧ adherent F (MyFilter.eventuality x) := by
  intro hFC
  choose A hA using hFC.2
  let B (n : ℕ) := ⋂₀ {A (1/(i+1)) (by positivity) | i ≤ n}
  -- The idea is to choose a sequence x such that x n ∈ ∩ (i ≤ n), A i ...
  --  ... each of these set is non-empty because it is in F ...
  have hBn : ∀ (n : ℕ), B n ∈ F := by
    intro n
    induction n with
    | zero =>
      have h0 : B 0 = A (1 / 1) (by positivity) := by
        ext x
        simp only [B]
        rw [Set.mem_sInter]
        have w : A (1 / (↑(0 : ℕ) + 1)) (by positivity) = A (1 / 1) (by positivity) := by
          congr
          ring
        constructor
        · intro hx
          specialize hx (A (1 / 1) (by positivity))
            (by
              use 0
            )
          exact hx
        · intro hx
          intro S hS
          obtain ⟨k, hk1, hk2⟩ := hS
          rw [Nat.le_zero] at hk1
          rw [← hk2]
          subst hk1
          rw [w]
          exact hx
      rw [h0]
      exact (hA (1 / 1) (by positivity)).1
    | succ k ih =>
      have w : B (k + 1) = B k ∩ (A (1 / (k + 2)) (by positivity)) := by
        ext x
        simp only [B]
        rw [Set.mem_sInter, Set.mem_inter_iff]
        -- Very annoying, maybe there was a simpler way
        have ww : ∀ k : ℕ,
                    A (1 / (↑(k + 1) + 1)) (by positivity) =
                    A (1 / (↑k + 2)) (by positivity) := by
          intro k
          congr 2
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        constructor
        · intro hx
          constructor
          · intro S hS
            obtain ⟨m, hm1, hm2⟩ := hS
            specialize hx S
              (by
                use m
                constructor
                · linarith
                · exact hm2
              )
            exact hx
          · specialize hx (A (1 / (k + 2)) (by positivity))
              (by
                use k + 1
                constructor
                · trivial
                · exact ww k
              )
            exact hx
        · intro hx S hS
          obtain ⟨hxB, hxA⟩ := hx
          obtain ⟨m , hm1, hm2⟩ := hS
          by_cases h : m = k +1
          · rw [← hm2]
            subst h
            rw [ww k]
            exact hxA
          · have hmk : m ≤ k := by
              apply Nat.le_of_lt_succ
              rw [Nat.lt_iff_le_and_ne]
              constructor
              · exact hm1
              · exact h
            rw [← hm2]
            specialize hxB (A (1 / (m + 1)) (by positivity))
              (by
                use m
              )
            exact hxB
      rw [w]
      apply F.inter_Sets
      · exact ih
      · exact (hA (1 / (k + 2)) (by positivity)).1
  -- ... and these sets are shrinking because of how we defined them ...
  have w : ∀ N n : ℕ, n ≥ N → B n ⊆ A (1 / (N + 1)) (by positivity) := by
      intro N n hn
      intro y hy
      simp only [B] at hy
      rw [Set.mem_sInter] at hy
      specialize hy (A (1 / (N + 1)) (by positivity))
        (by
          use N
        )
      exact hy
  have hBne : ∀ n, ∃ x, x ∈ (B n) := by
    intro n
    rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
    intro h
    specialize hBn n
    rw [h] at hBn
    obtain ⟨FP, FC⟩ := hFC
    contradiction
  choose x hx using hBne
  -- We now have the candidate sequence, now we need to show that it is Cauchy
  use x
  constructor
  · -- ... so x is a Cauchy sequence, bacause it is definitely contained in B n for n big enough
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    have wN : (0 : ℝ) < N := by
      calc 0 < 1 / ε := by rw [one_div_pos]; exact hε
           _ < N := by exact hN
    use N
    intro m n hm hn
    have hAm : x m ∈ A (1 / (N + 1)) (by positivity) := by
      apply w N m hm
      exact hx m
    have hAn : x n ∈ A (1 / (N + 1)) (by positivity) := by
      apply w N n hn
      exact hx n
    specialize hA (1 / (N + 1)) (by positivity)
    obtain ⟨hA1, hA2⟩ := hA
    specialize hA2 (x m) (x n) hAm hAn
    calc dist (x m) (x n) < 1 / (N + 1) := by exact hA2
          _ ≤ 1 / N := by
            rw [one_div_le_one_div]
            · simp only [le_add_iff_nonneg_right, zero_le_one]
            · positivity
            · exact wN
          _ < ε := by
            exact (one_div_lt hε wN).mp hN
  · -- Now the adherence part
    intro C D l hl hC hD
    obtain ⟨hD, hlD⟩ := hD
    rw [Open_basisTopology] at hD
    specialize hD l hlD
    obtain ⟨E, ⟨c, ε, DE⟩, hlE, hEsD⟩ := hD
    rw [DE] at hlE
    obtain ⟨δ, hδ1, hδ2⟩ := ball_in_ball l hlE
    have ww : Metric.ball l (δ / 2) ∈ MyFilter.eventuality x := by
      apply hl
      constructor
      · apply Open_Ball
      · apply Metric.mem_ball_self (by refine div_pos hδ1 two_pos)
    obtain ⟨N, hN⟩ := ww
    obtain ⟨M, hM⟩ := exists_nat_gt (2 / δ)
    let N' := max N M
    have ww : A (1 / (N' + 1)) (by positivity) ⊆ D := by
      intro y hy
      apply hEsD
      rw [DE]
      apply hδ2
      rw [Metric.mem_ball]
      have hd1 : dist y (x N') < δ / 2 := by
        specialize hx N'
        apply w N' N' at hx
        · specialize hA (1 / (N' + 1)) (by positivity)
          obtain ⟨hA1, hA2⟩ := hA
          specialize hA2 y (x N') hy hx
          calc
            dist y (x N') < 1 / (N' + 1) := hA2
            _ < 1 / N' := by
              refine one_div_lt_one_div_of_lt ?_ ?_
              · calc
                  0 < 2 / δ := div_pos two_pos hδ1
                  _ < M := hM
                  _ ≤ N' := by simp only [Nat.cast_max, le_sup_right, N']
              · rw [@lt_add_iff_pos_right]
                exact Real.zero_lt_one
            _ ≤ 1 / M := by
              refine one_div_le_one_div_of_le ?_ ?_
              · calc
                  0 < 2 / δ := div_pos two_pos hδ1
                  _ < M := hM
              · simp only [Nat.cast_max, le_sup_right, N']
            _ < δ / 2 := by
              refine (one_div_lt ?_ ?_).mp ?_
              · exact half_pos hδ1
              · calc
                  0 < 2 / δ := div_pos two_pos hδ1
                  _ < M := hM
              · calc
                  1 / (δ / 2) = 2 / δ := by ring
                  _ < M := hM
        · exact Nat.le_refl N'
      have hd2 : dist (x N') l < δ / 2 := by
        have w : x N' ∈ MyFilter.tail x N := by
          use N'
          constructor
          · exact Nat.le_max_left N M
          · rfl
        apply hN at w
        exact w
      calc dist y l ≤ dist y (x N') + dist (x N') l := by exact dist_triangle y (x N') l
            _ < δ / 2 + δ / 2 := by
              exact add_lt_add hd1 hd2
            _ = δ := by ring
    have w : ∃ y, y ∈ C ∩ A (1 / (N' + 1)) (by positivity) := by
      rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
      intro h
      have hh := F.inter_Sets hC (hA (1 / (N' + 1)) (by positivity)).1
      rw [h] at hh
      apply hFC.1
      exact hh
    obtain ⟨y, hy⟩ := w
    rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def]
    use y
    constructor
    · exact hy.1
    · apply ww
      exact hy.2

end CauchyFilters

section complete_iff_filterComplete

-- Thanks to the previous lemma it will now be easy to prove

lemma complete_iff_filterComplete {X : Type u} [MetricSpace X] : Complete X ↔ filterComplete X := by
  constructor
  · -- Take a Cauchy filter F ...
    intro h F hFP
    -- ... extract a Cauchy subsequence x ...
    obtain ⟨x, hxC, hxF⟩ := CauchyFilter_has_CauchySequ F hFP
    -- ... x converges because X is complete ...
    specialize h x hxC
    -- ... but so also F converges
    exact CauchyFilter_converge_to_adeherent F (MyFilter.eventuality x)
      hFP hxF h
  · -- Take a Cauchy sequence x ...
    intro h x hx
    apply h
    -- ... its eventuality filter F is a Cauchy filter, so it converges
    constructor
    · exact eventuality_is_proper x
    · intro ε hε
      specialize hx ε hε
      obtain ⟨N, hN⟩ := hx
      use MyFilter.tail x N
      constructor
      · use N
      · intro y z hy hz
        obtain ⟨m, hm, hmy⟩ := hy
        obtain ⟨n, hn, hnz⟩ := hz
        specialize hN m n hm hn
        rw [←hmy, ←hnz]
        exact hN

end complete_iff_filterComplete
