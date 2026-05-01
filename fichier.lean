-- SardLemma/Subdivision.lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic

open Set

namespace Subdivision

lemma div_ceil_le {μ δ : ℝ} (hμ : μ > 0) (hδ : δ > 0) : μ / ⌈μ / δ⌉ ≤ δ := by
  have hk : (0 : ℝ) < (⌈μ / δ⌉ : ℤ) := Int.cast_pos.mpr (Int.ceil_pos.mpr (div_pos hμ hδ))
  have hle : μ / δ ≤ (⌈μ / δ⌉ : ℝ) := Int.le_ceil (μ / δ)
  rw [div_le_iff₀ hk]
  nlinarith [div_mul_cancel₀ μ (ne_of_gt hδ)]

lemma nat_eq_toNat {k : ℤ} (hk : (k : ℝ) > 0) : (k : ℝ) = (k.toNat : ℝ) := by
  have hk' : 0 < k := Int.cast_pos.mp hk
  have h : 0 ≤ k := le_of_lt hk'
  have h' : (k.toNat : ℤ) = k := by simpa [not_le.mpr hk']
  exact_mod_cast h'.symm

lemma toNat_mul_div_eq
  {k : ℤ}
  {μ : ℝ}
  (hk : (k : ℝ) > 0) :
  k.toNat * (μ / k) = μ :=
by
  have hk_ne_zero : (k : ℝ) ≠ 0 := by positivity
  have hk_eq_n : (k : ℝ) = (k.toNat : ℝ) := nat_eq_toNat hk
  rw [← hk_eq_n]
  field_simp [hk_ne_zero]

lemma subdivision_bounds
    {a b : ℝ} {k : ℤ} {i : ℕ}
    (hk : (k : ℝ) > 0) (hμ : b - a > 0) (hi : i ≤ k.toNat) :
    let δ := (b - a) / k
    let subdiv := a + i * δ
    let I := Set.Icc a b
    subdiv ∈ I := by
  intro δ subdiv I
  let n := k.toNat
  let μ : ℝ := b - a
  have subdiv_above_a : a ≤ subdiv := by
    have term_pos : 0 ≤ i * δ := by positivity
    linarith
  have subdiv_below_b : subdiv ≤ b := by
    have term_maj : i * δ ≤ n * δ := by
      gcongr
    have eq : n * (μ / k) = μ := toNat_mul_div_eq hk
    linarith
  unfold I
  refine Set.mem_Icc.mpr ?_
  constructor
  · exact subdiv_above_a
  · exact subdiv_below_b

lemma subdivision_intervals_subset
    {a b : ℝ} {k : ℤ} {i : ℕ}
    (hk : (k : ℝ) > 0) (hμ : b - a > 0) (hi : i < k.toNat) :
    let δ := (b - a) / k
    let subdiv := fun i : ℕ => a + i * δ
    let J := fun i : ℕ => Set.Icc (subdiv i) (subdiv (i + 1))
    let I := Set.Icc a b
    J i ⊆ I := by
  intro δ subdiv J I
  have hi_plus: i + 1 ≤ k.toNat := by
    nlinarith
  refine Set.Icc_subset I ?_ (subdivision_bounds hk hμ hi_plus)
  exact subdivision_bounds hk hμ (le_of_lt hi)

def growing (a : ℕ → ℝ) : Prop :=
  ∀ i, (a i) ≤ (a (i + 1))

lemma growing_transitive {a : ℕ → ℝ} (ha : growing a) (n : ℕ) : a 0 ≤ a n := by
  induction n
  · rfl
  · (expose_names; exact Std.IsPreorder.le_trans (a 0) (a n) (a (n + 1)) h (ha n))

lemma subdivision_union {a : ℕ → ℝ} (n : ℕ) (ha : growing a) :
    let I := fun (i : ℕ) => Icc (a i) (a (i + 1))
    Icc (a 0) (a (n + 1)) = ⋃ i ≤ n, I i := by
  intro I
  induction n
  · simp only [zero_add, nonpos_iff_eq_zero, iUnion_iUnion_eq_left]
    unfold I
    rfl
  · rw [biUnion_le_succ]
    (expose_names; rw [← h])
    unfold I
    have h0 : a 0 ≤ a (n + 1) := growing_transitive ha (n + 1)
    have hn : a (n + 1) ≤ a (n + 1 + 1) := ha (n + 1)
    exact Eq.symm (Icc_union_Icc_eq_Icc h0 hn)


lemma subdivision_covers
    {a b : ℝ} {k : ℤ}
    (hk : (k : ℝ) > 0) (hμ : b - a > 0) :
    let δ := (b - a) / k
    let subdiv := fun i : ℕ => a + i * δ
    let I := Set.Icc a b
    let J := fun i : ℕ => Set.Icc (subdiv i) (subdiv (i + 1))
    I = ⋃ i < k.toNat, J i := by
  intro δ sub I
  unfold I
  have hsub : growing sub := by
    intro i
    unfold sub
    simp only [Nat.cast_add, Nat.cast_one, add_le_add_iff_left]
    gcongr
    · simp
  have h := subdivision_union k.toNat hsub
  have h0 : a = sub 0 := by
    unfold sub
    simp
  have hn : b = sub (k.toNat) := by
    unfold sub
    unfold δ
    field_simp
    have h1 : k.toNat * (b - a) = k.toNat * b - k.toNat * a := by
      exact mul_sub_left_distrib (↑k.toNat) b a
    have h2 : k.toNat * b - k.toNat * a = - k.toNat * a + k.toNat * b := by
      field_simp
      simp
      constructor
      · simp only [sub_eq_neg_add]
    rw [h1, h2]
    rw [← nat_eq_toNat hk]
    rw [← @AddSemigroup.add_assoc]
    rw [@neg_mul]
    field_simp
    simp
  rw [h0, hn]
  simp only [Int.lt_toNat]
  have hlt_le (n : ℕ) : (n : ℕ) < k ↔ (n : ℕ) ≤ k - 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (Int.lt_add_one_iff (a := (n : ℤ)) (b := k - 1))
  simp only [hlt_le]
  have hk : (k : ℤ) > 0 := by exact_mod_cast hk
  have hk : 0 < k := GT.gt.lt hk
  have hk : 0 ≤ k - 1 := Int.sub_nonneg_of_le hk
  have hk_nat : k.toNat - 1 + 1 = k.toNat := by omega
  have h_union := subdivision_union (k - 1).toNat hsub
  simp only [Int.pred_toNat] at h_union
  rw [hk_nat] at h_union
  have hk_eq_nat : k = (k.toNat: ℤ) := by omega
  change Icc (sub 0) (sub k.toNat) = ⋃ i : ℕ, ⋃ (_ : (i : ℤ) ≤ k - 1), Icc (sub i) (sub (i + 1))
  rw [← hk_nat]
  convert h_union using 2
  · congr 1
  · have : k.toNat - 1 = (k - 1).toNat := by omega
    simp_rw [this]
    ext i
    simp only [mem_iUnion, mem_Icc, exists_and_left, exists_prop, Int.pred_toNat,
      and_congr_right_iff, and_congr_left_iff]
    omega


example {k : ℤ} (hk : 0 < (k : ℤ) ) : 0 ≤ k - 1 := by
  exact Int.sub_nonneg_of_le hk

end Subdivision
