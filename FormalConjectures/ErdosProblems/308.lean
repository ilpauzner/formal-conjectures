/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 308

*References:*
- [erdosproblems.com/308](https://www.erdosproblems.com/308)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980).
- [Cr99] Croot, III, Ernest S., _On some questions of Erdős and Graham about Egyptian
  fractions_. Mathematika (1999), 359-372.
-/

@[expose] public section

open Filter Real

namespace Erdos308

/-- `k` is representable as a sum of distinct unit fractions with denominators from
`{1, …, N}`. -/
def IsRepresentable (N k : ℕ) : Prop :=
  ∃ A ⊆ Finset.Icc 1 N, ∑ n ∈ A, (1 : ℚ) / n = k

/-- The set of positive integers representable as a sum of distinct unit fractions with
denominators from `{1, …, N}`. -/
def representable (N : ℕ) : Set ℕ := {k | 0 < k ∧ IsRepresentable N k}

/-- `f N` is the smallest positive integer which is not representable as a sum of distinct unit
fractions with denominators from `{1, …, N}`. -/
noncomputable def f (N : ℕ) : ℕ := sInf {k | 0 < k ∧ ¬ IsRepresentable N k}

/-- `m N = ⌊∑_{n ≤ N} 1/n⌋`. -/
def m (N : ℕ) : ℕ := ⌊harmonic N⌋₊

set_option linter.style.formal_proof_palomar false in
/--
Let $N\geq 1$. What is the smallest integer not representable as the sum of distinct unit
fractions with denominators from $\{1,\ldots,N\}$?

This was essentially solved by Croot [Cr99] (see `erdos_308.variants.croot`); in particular,
for all sufficiently large $N$, the smallest such integer is either $m_N$ or $m_N+1$, where
$m_N=\lfloor \sum_{n\leq N}\frac{1}{n}\rfloor$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos308.lean#L458"]
theorem erdos_308.parts.i : ∀ᶠ N : ℕ in atTop, f N = m N ∨ f N = m N + 1 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let $N\geq 1$. Is it true that the set of integers representable as the sum of distinct unit
fractions with denominators from $\{1,\ldots,N\}$ has the shape $\{1,\ldots,m\}$ for some $m$?

It follows from Croot's bounds [Cr99] that this holds for all sufficiently large $N$.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos308.lean#L458"]
theorem erdos_308.parts.ii :
    ∀ᶠ N : ℕ in atTop, ∃ m, representable N = Set.Icc 1 m := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
If $m_N=\lfloor \sum_{n\leq N}\frac{1}{n}\rfloor$, then the set of integers representable is, for
all $N$ sufficiently large, either $\{1,\ldots,m_N-1\}$ or $\{1,\ldots,m_N\}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos308.lean#L458"]
theorem erdos_308.variants.shape : ∀ᶠ N : ℕ in atTop,
    representable N = Set.Icc 1 (m N - 1) ∨ representable N = Set.Icc 1 (m N) := by
  sorry

/--
Croot [Cr99] bounded $\eta(N)$, the largest integer such that every integer in
$\{1,\ldots,\eta(N)\}$ is representable; this is $f(N)-1$, so his bounds read
$$\left\lfloor\sum_{n\leq N}\frac{1}{n}-\frac{9}{2}(1+o(1))\frac{(\log\log N)^2}{\log N}
\right\rfloor + 1 \leq f(N)$$
and
$$f(N)\leq \left\lfloor\sum_{n\leq N}\frac{1}{n}-\frac{1}{2}(1+o(1))
\frac{(\log\log N)^2}{\log N}\right\rfloor + 1.$$
-/
@[category research solved, AMS 11]
theorem erdos_308.variants.croot :
    ∃ o₁ o₂ : ℕ → ℝ, Tendsto o₁ atTop (nhds 0) ∧ Tendsto o₂ atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop,
        ⌊(harmonic N : ℝ) - 9 / 2 * (1 + o₁ N) * (log (log N)) ^ 2 / log N⌋₊ + 1 ≤ f N ∧
        f N ≤ ⌊(harmonic N : ℝ) - 1 / 2 * (1 + o₂ N) * (log (log N)) ^ 2 / log N⌋₊ + 1 := by
  sorry

end Erdos308
end

namespace Erdos308
section

open Chebyshev Finset Filter Real
open scoped ArithmeticFunction

/- ### Section 1: Binary-Tree Evaluation, Rational `log`/`harmonic` Bounds, and Threshold `W` -/
def treeSum (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, b => f b
  | d + 1, b => treeSum f d b + treeSum f d (b + (1 <<< d))
@[category API, AMS 11] lemma treeSum_Ico (f : ℕ → ℕ) (d : ℕ) :
    ∀ b, treeSum f d b = ∑ x ∈ Ico b (b + 2 ^ d), f x := by
  induction d with
  | zero => simp [treeSum]
  | succ d ih =>
    intro b
    rw [treeSum, Nat.shiftLeft_eq, one_mul, ih b, ih (b + 2 ^ d),
      sum_Ico_consecutive f (Nat.le_add_right b _) (Nat.le_add_right _ _),
      show b + 2 ^ d + 2 ^ d = b + 2 ^ (d + 1) by ring]
def treeAll (p : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, b => p b
  | d + 1, b => treeAll p d b && treeAll p d (b + (1 <<< d))
@[category API, AMS 11] lemma treeAll_iff (p : ℕ → Bool) (d : ℕ) :
    ∀ b, treeAll p d b = true ↔ ∀ x ∈ Ico b (b + 2 ^ d), p x = true := by
  induction d with
  | zero => simp [treeAll]
  | succ d ih =>
    intro b
    rw [treeAll, Nat.shiftLeft_eq, one_mul, Bool.and_eq_true, ih b, ih (b + 2 ^ d)]
    have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    refine ⟨fun ⟨hL, hR⟩ x hx => ?_, fun h => ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
    · rw [mem_Ico] at hx
      exact if h : x < b + 2 ^ d then hL x (mem_Ico.mpr ⟨hx.1, h⟩) else hR x (mem_Ico.mpr ⟨by omega, by omega⟩)
    · rw [mem_Ico] at hx
      exact h x (mem_Ico.mpr ⟨hx.1, by omega⟩)
    · rw [mem_Ico] at hx
      exact h x (mem_Ico.mpr ⟨by omega, by omega⟩)
@[category API, AMS 11] lemma inv_dvd {S : Finset ℕ} {L : ℕ} (hL : 0 < L) (hd : ∀ x ∈ S, 0 < x ∧ x ∣ L) :
    ∑ x ∈ S, (1 : ℚ) / x = ((∑ x ∈ S, L / x : ℕ) : ℚ) / L := by
  rw [Nat.cast_sum, sum_div]
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨hx0, hxd⟩ := hd x hx
  rw [Nat.cast_div hxd (by positivity), div_div_cancel_left' (by positivity), one_div]
@[category API, AMS 11] lemma harm_mono : StrictMono harmonic :=
  strictMono_nat_of_lt_succ fun n => by
    rw [harmonic_succ]
    linarith [show (0 : ℚ) < ((n + 1 : ℕ) : ℚ)⁻¹ by positivity]
@[category API, AMS 11] lemma harm_nn (n : ℕ) : (0 : ℚ) ≤ harmonic n := by
  rw [harmonic_eq_sum_Icc]
  positivity
def S9 : ℕ := 1000000000
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b
@[category API, AMS 11] lemma cdiv_ok {a b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  rw [div_le_iff₀ (by positivity)]
  unfold cdiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  rw [mul_comm] at h1
  exact_mod_cast (by omega : a ≤ (a + b - 1) / b * b)
@[category API, AMS 11] lemma le_cdiv_S9 {x : ℝ} {a b : ℕ} (hb : 0 < b) (hx : x ≤ (a : ℝ) / (b * S9)) :
    x ≤ (cdiv a b : ℝ) / S9 := by
  grw [hx, ← div_div, cdiv_ok hb]
@[category API, AMS 11] lemma log_succ {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k + 1 : ℕ) : ℝ) ≤ log ((k + 1 : ℕ) : ℝ) - log k ∧ log ((k + 1 : ℕ) : ℝ) - log k ≤ 1 / (k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [← log_div hk1.ne' hk0.ne']
  have hlo := one_sub_inv_le_log_of_pos (div_pos hk1 hk0)
  rw [inv_div] at hlo
  have heq1 : 1 - (k : ℝ) / (k + 1 : ℕ) = 1 / (k + 1 : ℕ) := by
    push_cast
    field_simp
    ring
  have heq2 : ((k + 1 : ℕ) : ℝ) / k - 1 = 1 / k := by
    push_cast
    field_simp
    ring
  exact ⟨by linarith, by linarith [log_le_sub_one_of_pos (div_pos hk1 hk0)]⟩
def isqrtLb (n : ℕ) : ℕ :=
  let s := ((fun s => (s + n / s) / 2)^[6]) (1 <<< (n.log2 / 2 + 1))
  if Nat.ble 1 s && Nat.ble (s * s) n then s else 1
def isqrtUb (n : ℕ) : ℕ :=
  let s := isqrtLb n + 1
  if Nat.ble n (s * s) then s else n
@[category API, AMS 11] lemma isqrt_bds (n : ℕ) :
    (1 ≤ n → 1 ≤ isqrtLb n ∧ (isqrtLb n : ℝ) ≤ sqrt n) ∧ sqrt n ≤ isqrtUb n := by
  refine ⟨fun hn => ?_, sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, ?_⟩⟩
  · have hs : 1 ≤ isqrtLb n ∧ isqrtLb n * isqrtLb n ≤ n := by
      unfold isqrtLb
      dsimp only []
      split_ifs with h
      · exact (Bool.and_eq_true _ _).mp h |>.imp Nat.ble_eq.mp Nat.ble_eq.mp
      · exact ⟨le_rfl, by omega⟩
    refine ⟨hs.1, le_sqrt_of_sq_le ?_⟩
    rw [sq]
    exact_mod_cast hs.2
  · rw [sq]
    unfold isqrtUb
    dsimp only []
    split_ifs with h
    · exact_mod_cast Nat.ble_eq.mp h
    · exact_mod_cast Nat.le_mul_self n
def log1pLb9 (num den : ℕ) : ℕ := (2 * num * S9) / (2 * den + num)
def log1pUb9 (num den : ℕ) : ℕ :=
  if Nat.beq num 0 then 0 else cdiv (num * (2 * den + num) * S9) (2 * den * (den + num))
@[category API, AMS 11] lemma log1p_bds {u : ℝ} {num den : ℕ} (hden : 0 < den) :
    (log1pLb9 num den : ℝ) / S9 ≤ log (1 + (num : ℝ) / den) ∧
      (0 ≤ u → u ≤ (num : ℝ) / den → log (1 + u) ≤ (log1pUb9 num den : ℝ) / S9) := by
  have hpade {w : ℝ} (hw : 0 ≤ w) : 2 * w / (w + 2) ≤ log (1 + w) ∧ log (1 + w) ≤ w * (w + 2) / (2 * (w + 1)) := by
    have hy0 : 0 ≤ w / (w + 2) := by positivity
    have hy1 : w / (w + 2) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    have heq : (1 + w / (w + 2)) / (1 - w / (w + 2)) = 1 + w := by
      field_simp
      ring
    have hlo := Real.sum_range_le_log_div (n := 1) hy0 hy1
    have hhi := Real.log_div_le_sum_range_add (n := 1) hy0 hy1
    rw [heq, sum_range_one] at hlo hhi
    norm_num at hlo hhi
    refine ⟨by linarith [show 2 * (w / (w + 2)) = 2 * w / (w + 2) by ring], ?_⟩
    have hsub : 1 - (w / (w + 2)) ^ 2 = 4 * (w + 1) / (w + 2) ^ 2 := by
      field_simp
      ring
    have hrat : w / (w + 2) + (w / (w + 2)) ^ 3 / (4 * (w + 1) / (w + 2) ^ 2) = w * (w + 2) / (4 * (w + 1)) := by
      field_simp
      ring
    rw [hsub, hrat] at hhi
    have h2 : 2 * (w * (w + 2) / (4 * (w + 1))) = w * (w + 2) / (2 * (w + 1)) := by
      have : w + 1 ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hdR : (0 : ℝ) < den := by positivity
  have hS9 : (0 : ℝ) < S9 := by
    unfold S9
    norm_num
  refine ⟨?_, fun hu hub => ?_⟩
  · unfold log1pLb9
    set D := 2 * den + num
    have hD : (0 : ℝ) < D := by
      dsimp [D]
      positivity
    have h1 : (((2 * num * S9) / D : ℕ) : ℝ) / S9 ≤ ((2 * num * S9 : ℕ) : ℝ) / (D * S9) := by
      rw [div_le_div_iff₀ hS9 (mul_pos hD hS9)]
      nlinarith [show (((2 * num * S9) / D : ℕ) : ℝ) * D ≤ (2 * num * S9 : ℕ) from mod_cast Nat.div_mul_le_self _ D]
    have h2 : ((2 * num * S9 : ℕ) : ℝ) / (D * S9) = 2 * ((num : ℝ) / den) / ((num : ℝ) / den + 2) := by
      dsimp [D]
      push_cast
      field_simp
      ring
    exact h1.trans (h2.le.trans (hpade (by positivity)).1)
  · unfold log1pUb9
    split_ifs with hz
    · obtain rfl : num = 0 := Nat.beq_eq.mp hz
      obtain rfl : u = 0 := le_antisymm (by simpa using hub) hu
      simp
    · set v := (num : ℝ) / den
      have hv : 0 ≤ v := hu.trans hub
      have hmono : u * (u + 2) / (2 * (u + 1)) ≤ v * (v + 2) / (2 * (v + 1)) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hub) (show 0 ≤ u + v + u * v + 2 by positivity)]
      refine (hpade hu).2.trans (hmono.trans (le_cdiv_S9 (by positivity) ?_))
      have := hS9.ne'
      dsimp [v]
      push_cast
      field_simp
      exact le_of_eq (by ring)
def log8Lb (c : ℕ) : ℕ :=
  [0, 117748917, 223085022, 318377136, 405374771, 485406783, 559506268, 628492292].getD (c - 8) 0
def log8Ub (c : ℕ) : ℕ :=
  [0, 117851308, 223260666, 318606987, 405645855, 485709959, 559834909, 628841478].getD (c - 8) 0
def logLb9 (x : ℕ) : ℕ :=
  if Nat.ble x 1 then 0 else
    let e := x.log2
    let c := (8 * x) / (1 <<< e)
    let b := c * (1 <<< e)
    e * 693147180 + log8Lb c + log1pLb9 (8 * x - b) b
def logUb9 (x : ℕ) : ℕ :=
  if Nat.ble x 1 then 0 else
    let e := x.log2
    let c := (8 * x) / (1 <<< e)
    let b := c * (1 <<< e)
    e * 693147181 + log8Ub c + log1pUb9 (8 * x - b) b
@[category API, AMS 11] lemma log_bds {x : ℕ} (hx1 : 1 ≤ x) :
    (logLb9 x : ℝ) / S9 ≤ log x ∧ log x ≤ (logUb9 x : ℝ) / S9 := by
  have hchk8 : ∀ c ∈ Icc 8 15, log8Lb c ≤ ∑ k ∈ Ico 16 (2 * c), log1pLb9 1 k ∧
      ∑ k ∈ Ico 16 (2 * c), log1pUb9 1 k ≤ log8Ub c := by decide
  unfold logLb9 logUb9
  split_ifs with hble
  · obtain rfl : x = 1 := by
      have := Nat.ble_eq.mp hble
      omega
    simp
  · dsimp only []
    have hx2 : 2 ≤ x := by
      have := not_le.mp (hble ∘ Nat.ble_eq.mpr)
      omega
    set e := x.log2
    have he : e = Nat.log 2 x := Nat.log2_eq_log_two
    rw [show (1 <<< e) = 2 ^ e by simp [Nat.shiftLeft_eq]]
    have hp_lo : 2 ^ e ≤ x := he ▸ Nat.pow_log_le_self 2 (by omega)
    have hp_pos : 0 < 2 ^ e := Nat.two_pow_pos e
    have hp_hi : x < 2 * 2 ^ e := by
      have := he ▸ Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
      rwa [pow_succ'] at this
    set c := (8 * x) / 2 ^ e
    set b := c * 2 ^ e
    have hc8 : 8 ≤ c := (Nat.le_div_iff_mul_le hp_pos).mpr (by omega)
    have hc15 : c ≤ 15 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp_pos).mpr (by omega))
    have hb_pos : 0 < b := Nat.mul_pos (by omega) hp_pos
    have hb_le : b ≤ 8 * x := Nat.div_mul_le_self (8 * x) (2 ^ e)
    have hlog_x : log x = e * log 2 + log ((c : ℝ) / 8) + log (1 + ((8 * x - b : ℕ) : ℝ) / b) := by
      have hx_eq : (x : ℝ) = (2 : ℝ) ^ e * ((c : ℝ) / 8) * (1 + ((8 * x - b : ℕ) : ℝ) / b) := by
        rw [Nat.cast_sub hb_le]
        dsimp only [b]
        push_cast
        field_simp
        ring
      conv_lhs => rw [hx_eq]
      rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity), log_pow]
    have hrc : log ((c : ℝ) / 8) = ∑ k ∈ Ico 16 (2 * c), log (1 + (1 : ℝ) / k) := by
      have hcongr : ∑ k ∈ Ico 16 (2 * c), log (1 + (1 : ℝ) / k) =
          ∑ k ∈ Ico 16 (2 * c), (log ((k + 1 : ℕ) : ℝ) - log (k : ℝ)) := by
        refine sum_congr rfl fun k hk => ?_
        have hk_ge := (mem_Ico.mp hk).1
        have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
        rw [← log_div (by positivity) hk0.ne']
        congr 1
        push_cast
        field_simp
      rw [hcongr, sum_Ico_sub (fun k : ℕ => log (k : ℝ)) (by omega), ← log_div (by positivity) (by norm_num)]
      congr 1
      push_cast
      ring
    obtain ⟨hlb8, hub8⟩ := hchk8 c (mem_Icc.mpr ⟨hc8, hc15⟩)
    have hlo8 : (log8Lb c : ℝ) / S9 ≤ log ((c : ℝ) / 8) := by
      grw [hlb8]
      rw [hrc, Nat.cast_sum, sum_div]
      refine sum_le_sum fun k hk => ?_
      have := (mem_Ico.mp hk).1
      simpa using (log1p_bds (u := 0) (num := 1) (by omega)).1
    have hhi8 : log ((c : ℝ) / 8) ≤ (log8Ub c : ℝ) / S9 := by
      grw [← hub8]
      rw [hrc, Nat.cast_sum, sum_div]
      refine sum_le_sum fun k hk => ?_
      have := (mem_Ico.mp hk).1
      exact (log1p_bds (by omega)).2 (by positivity) (by simp)
    have hl2_lo : (693147180 : ℝ) / S9 ≤ log 2 := by
      unfold S9
      linarith [log_two_gt_d9]
    have hl2_hi : log 2 ≤ (693147181 : ℝ) / S9 := by
      unfold S9
      linarith [log_two_lt_d9]
    rw [hlog_x]
    refine ⟨?_, ?_⟩
    · push_cast
      rw [add_div, add_div, mul_div_assoc]
      have := (log1p_bds (u := 0) (num := 8 * x - b) hb_pos).1
      gcongr
    · push_cast
      rw [add_div, add_div, mul_div_assoc]
      have := (log1p_bds (num := 8 * x - b) hb_pos).2 (by positivity) le_rfl
      gcongr
@[category API, AMS 11] lemma harm_tree {n d : ℕ} (hn : n ≤ 2 ^ d) :
    (treeSum (fun k => if k ≤ n then S9 / k else 0) d 1 : ℝ) / S9 ≤ harmonic n ∧
      (harmonic n : ℝ) ≤ (treeSum (fun k => if k ≤ n then cdiv S9 k else 0) d 1 : ℝ) / S9 := by
  have hS9 : (0 : ℝ) < S9 := by
    unfold S9
    norm_num
  have hIcc : Icc 1 n = (Ico 1 (1 + 2 ^ d)).filter (· ≤ n) := by
    ext
    simp only [mem_Icc, mem_filter, mem_Ico]
    omega
  rw [treeSum_Ico, treeSum_Ico, ← sum_filter, ← sum_filter, ← hIcc,
    harmonic_eq_sum_Icc, Rat.cast_sum, Nat.cast_sum, Nat.cast_sum, sum_div, sum_div]
  refine ⟨sum_le_sum fun k hk => ?_, sum_le_sum fun k hk => ?_⟩
  · rw [Rat.cast_inv, Rat.cast_natCast, div_le_iff₀ hS9, inv_mul_eq_div, le_div_iff₀ (Nat.cast_pos.mpr (mem_Icc.mp hk).1)]
    exact_mod_cast Nat.div_mul_le_self S9 k
  · rw [Rat.cast_inv, Rat.cast_natCast, le_div_iff₀ hS9, inv_mul_eq_div]
    exact cdiv_ok (mem_Icc.mp hk).1
def hCeil9 (n : ℕ) : ℕ :=
  if Nat.beq n 0 then 0
  else if Nat.beq n 1 then S9
  else if Nat.ble n 32 then 577135000 + logUb9 n + cdiv S9 (2 * n)
  else 592760000 + logUb9 n
@[category API, AMS 11] lemma hCeil9_ok (n : ℕ) : (harmonic n : ℝ) ≤ (hCeil9 n : ℝ) / S9 := by
  have hS9 : (S9 : ℝ) = 1000000000 := by
    unfold S9
    norm_num
  have hg_step {k : ℕ} (hk : 1 ≤ k) :
      (harmonic k : ℝ) - log k - 1 / (2 * (k : ℝ)) ≤
        (harmonic (k + 1) : ℝ) - log (k + 1 : ℕ) - 1 / (2 * (k + 1 : ℕ)) := by
    set K := (k : ℝ)
    have hkR : 0 < K := Nat.cast_pos.mpr hk
    have hhi := Real.log_div_le_sum_range_add (n := 1) (x := 1 / (2 * K + 1))
      (by positivity) ((div_lt_one (by positivity)).mpr (by linarith))
    rw [sum_range_one] at hhi
    norm_num at hhi
    have hlhs : (1 + (2 * K + 1)⁻¹) / (1 - (2 * K + 1)⁻¹) = (K + 1) / K := by
      field_simp
      ring
    have hrhs : (2 * K + 1)⁻¹ + ((2 * K + 1) ^ 3)⁻¹ / (1 - ((2 * K + 1) ^ 2)⁻¹) =
        (1 / (2 * K) + 1 / (2 * (K + 1))) / 2 := by
      have hden : 1 - ((2 * K + 1) ^ 2)⁻¹ = 4 * K * (K + 1) / (2 * K + 1) ^ 2 := by
        field_simp
        ring
      rw [hden]
      field_simp
      ring
    rw [hlhs, log_div (by positivity) hkR.ne', hrhs] at hhi
    rw [harmonic_succ]
    push_cast [K] at hhi ⊢
    have hinv1 : ((k : ℝ) + 1)⁻¹ = 2 * (1 / (2 * ((k : ℝ) + 1))) := by field_simp
    linarith
  have hg_mono : Monotone fun m => (harmonic (m + 1) : ℝ) - log (m + 1 : ℕ) - 1 / (2 * (m + 1 : ℕ)) :=
    monotone_nat_of_le_succ fun m => hg_step (by omega)
  have h32 := (harm_tree (n := 32) (d := 5) (by decide)).2
  rw [show treeSum (fun k => if k ≤ 32 then cdiv S9 k else 0) 5 1 = 4058495205 by decide, hS9, Nat.cast_ofNat] at h32
  have hl32 : 5 * (0.6931471803 : ℝ) < log 32 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, log_pow]
    linarith [log_two_gt_d9]
  unfold hCeil9
  split_ifs with hz h1 hble
  · rw [Nat.beq_eq.mp hz]
    simp
  · rw [Nat.beq_eq.mp h1, hS9]
    norm_num [harmonic_succ, harmonic_zero]
  · have hne0 : n ≠ 0 := fun h => hz (Nat.beq_eq.mpr h)
    have hne1 : n ≠ 1 := fun h => h1 (Nat.beq_eq.mpr h)
    have hn2 : 2 ≤ n := by omega
    have hn32 : n - 1 ≤ 31 := by
      have := Nat.ble_eq.mp hble
      omega
    have hm := hg_mono hn32
    dsimp only [] at hm
    rw [show n - 1 + 1 = n by omega, show (31 : ℕ) + 1 = 32 by rfl] at hm
    have hcd := cdiv_ok (a := S9) (b := 2 * n) (by omega)
    have hln := (log_bds (x := n) (by omega)).2
    rw [hS9] at hcd hln ⊢
    push_cast at hcd hln hm ⊢
    have hinv : 1 / (2 * (n : ℝ)) ≤ (cdiv S9 (2 * n) : ℝ) / 1000000000 := by
      rw [le_div_iff₀ (by norm_num), one_div_mul_eq_div]
      exact hcd
    linarith [show (1 : ℝ) / (2 * 32) = 1 / 64 by norm_num]
  · have hn32 : 32 ≤ n := by
      have := not_le.mp (hble ∘ Nat.ble_eq.mpr)
      omega
    have hanti := Real.strictAnti_eulerMascheroniSeq'.antitone hn32
    simp only [Real.eulerMascheroniSeq', show n ≠ 0 by omega, show (32 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.cast_ofNat] at hanti
    have hln := (log_bds (x := n) (by omega)).2
    push_cast
    rw [hS9] at hln ⊢
    linarith

noncomputable def W (k : ℕ) : ℕ :=
  if k ≤ 1 then k else if k = 2 then 10 else ⌊exp ((k : ℝ) + 4188 / 10000)⌋₊
@[category API, AMS 11] lemma W_mono {k₁ k₂ : ℕ} (hk1 : 3 ≤ k₁) (hle : k₁ ≤ k₂) : W k₁ ≤ W k₂ := by
  simp only [W, show ¬k₁ ≤ 1 by omega, show k₁ ≠ 2 by omega, show ¬k₂ ≤ 1 by omega, show k₂ ≠ 2 by omega, ↓reduceIte]
  gcongr
@[category API, AMS 11] lemma W_bds {k : ℕ} (n_lo n_hi : ℕ) (hk : 3 ≤ k) :
    (Nat.ble (n_lo * (10 ^ 9 * (10 ^ 10) ^ k)) (1520136295 * 27182818283 ^ k) = true → n_lo ≤ W k) ∧
    (Nat.ble (1520136299 * 27182818286 ^ k) ((n_hi + 1) * (10 ^ 9 * (10 ^ 10) ^ k)) = true → W k ≤ n_hi) := by
  have hb := Real.exp_bound (x := (4188 : ℝ) / 10000) (by norm_num) (n := 10) (by norm_num)
  rw [abs_le] at hb
  norm_num [sum_range_succ, Nat.factorial] at hb
  have heq : exp ((k : ℝ) + 4188 / 10000) = exp (4188 / 10000) * (exp 1) ^ k := by
    rw [exp_add, mul_comm, ← exp_nat_mul, mul_one]
  have hlo_e : ((1520136295 : ℝ) / 10 ^ 9) * ((27182818283 : ℝ) / 10 ^ 10) ^ k < exp ((k : ℝ) + 4188 / 10000) := by
    rw [heq]
    exact mul_lt_mul'' (by linarith)
      (pow_lt_pow_left₀ (by linarith [exp_one_gt_d9]) (by norm_num) (by omega)) (by norm_num) (by norm_num)
  have hhi_e : exp ((k : ℝ) + 4188 / 10000) < ((1520136299 : ℝ) / 10 ^ 9) * ((27182818286 : ℝ) / 10 ^ 10) ^ k := by
    rw [heq]
    exact mul_lt_mul'' (by linarith)
      (pow_lt_pow_left₀ (by linarith [exp_one_lt_d9]) (exp_pos 1).le (by omega)) (exp_pos _).le (by positivity)
  simp only [W, show ¬k ≤ 1 by omega, show k ≠ 2 by omega, ↓reduceIte]
  refine ⟨fun hble => ?_, fun hble => ?_⟩
  · have hleR : (n_lo : ℝ) * ((10 ^ 9 * (10 ^ 10) ^ k : ℕ) : ℝ) ≤ ((1520136295 * 27182818283 ^ k : ℕ) : ℝ) :=
      mod_cast Nat.ble_eq.mp hble
    refine Nat.le_floor (le_trans ?_ hlo_e.le)
    rw [div_pow, div_mul_div_comm, le_div_iff₀ (by positivity)]
    push_cast at hleR
    norm_num at hleR ⊢
    linarith
  · have hleR : ((1520136299 * 27182818286 ^ k : ℕ) : ℝ) ≤ ((n_hi + 1 : ℕ) : ℝ) * ((10 ^ 9 * (10 ^ 10) ^ k : ℕ) : ℝ) :=
      mod_cast Nat.ble_eq.mp hble
    refine Nat.lt_succ_iff.mp ((Nat.floor_lt (exp_pos _).le).mpr (hhi_e.trans_le ?_))
    rw [div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
    push_cast at hleR
    norm_num at hleR ⊢
    linarith
@[category API, AMS 11] lemma W_eq_bds {k : ℕ} (w : ℕ) (hk : 3 ≤ k := by decide)
    (hlo : Nat.ble (w * (10 ^ 9 * (10 ^ 10) ^ k)) (1520136295 * 27182818283 ^ k) = true := by decide)
    (hhi : Nat.ble (1520136299 * 27182818286 ^ k) ((w + 1) * (10 ^ 9 * (10 ^ 10) ^ k)) = true := by decide) :
    W k = w :=
  le_antisymm ((W_bds w w hk).2 hhi) ((W_bds w w hk).1 hlo)
@[category API, AMS 11] lemma harm_W_bds {k : ℕ} (hk : 5 ≤ k) :
    (k : ℝ) + 9921 / 10000 < harmonic (W k) ∧ (harmonic (W k) : ℝ) < (k : ℝ) + 1 := by
  have hWk : W k = ⌊exp ((k : ℝ) + 4188 / 10000)⌋₊ := by
    simp [W, show ¬k ≤ 1 by omega, show k ≠ 2 by omega]
  have h128 : 128 ≤ W k := by
    have := W_mono (by decide) hk
    rw [W_eq_bds 225] at this
    omega
  have hW_lo : exp ((k : ℝ) + 4188 / 10000) < (W k : ℝ) + 1 := hWk ▸ Nat.lt_floor_add_one _
  have hW_hi : (W k : ℝ) ≤ exp ((k : ℝ) + 4188 / 10000) := hWk ▸ Nat.floor_le (exp_pos _).le
  have hmono := Real.strictMono_eulerMascheroniSeq.monotone h128
  rw [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq, show ((128 : ℕ) : ℝ) + 1 = 129 by norm_num] at hmono
  have hanti := Real.strictAnti_eulerMascheroniSeq'.antitone h128
  simp only [Real.eulerMascheroniSeq', show W k ≠ 0 by omega, show (128 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.cast_ofNat] at hanti
  have hl128 : 7 * (0.6931471803 : ℝ) < log 128 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, log_pow]
    linarith [log_two_gt_d9]
  have hl129 : log 129 < 7 * 0.6931471808 + 1 / 128 := by
    rw [show (129 : ℝ) = 128 * (1 + 1 / 128) by norm_num, log_mul (by norm_num) (by norm_num),
      show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, log_pow]
    linarith [log_two_lt_d9, log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 128)]
  obtain ⟨hb_lo, hb_hi⟩ := harm_tree (n := 128) (d := 7) (by decide)
  rw [show treeSum (fun j => if j ≤ 128 then S9 / j else 0) 7 1 = 5433147035 by decide, S9, Nat.cast_ofNat] at hb_lo
  rw [show treeSum (fun j => if j ≤ 128 then cdiv S9 j else 0) 7 1 = 5433147146 by decide, S9, Nat.cast_ofNat] at hb_hi
  exact ⟨by linarith [(log_exp ((k : ℝ) + 4188 / 10000)).symm.trans_lt (log_lt_log (exp_pos _) hW_lo)],
    by linarith [(log_le_log (Nat.cast_pos.mpr (by omega)) hW_hi).trans_eq (log_exp _)]⟩

/- ### Section 2: Effective Chebyshev `ψ` and `θ` Bounds via Mathlib `Chebyshev` & `Stirling` -/
abbrev StepRow := ℕ × Bool × ℕ
def pEval : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (d, a) :: ps, y => Nat.add (Nat.mul a (Nat.div y d)) (pEval ps y)
def pPairs : List StepRow → List (ℕ × ℕ)
  | [] => []
  | (d, b, m) :: rs => if b then (d, d * m) :: pPairs rs else pPairs rs
def nPairs : List StepRow → List (ℕ × ℕ)
  | [] => []
  | (d, b, m) :: rs => if b then nPairs rs else (d, d * m) :: nPairs rs
def sumPosM : List StepRow → ℕ
  | [] => 0
  | r :: rs => (if r.2.1 then r.2.2 else 0) + sumPosM rs
def sumNegM : List StepRow → ℕ
  | [] => 0
  | r :: rs => (if r.2.1 then 0 else r.2.2) + sumNegM rs
def wNeg : List StepRow → ℕ
  | [] => 0
  | r :: rs => (if r.2.1 then 0 else r.1 * r.2.2) + wNeg rs
def sumAbsA : List StepRow → ℕ
  | [] => 0
  | r :: rs => r.1 * r.2.2 + sumAbsA rs
def negUlo : List StepRow → ℕ
  | [] => 0
  | r :: rs => (if r.2.1 then 0 else r.2.2 * logLb9 r.1) + negUlo rs
def posUhi : List StepRow → ℕ
  | [] => 0
  | r :: rs => (if r.2.1 then r.2.2 * logUb9 r.1 else 0) + posUhi rs
def absAUlo : List StepRow → ℕ
  | [] => 0
  | r :: rs => r.1 * r.2.2 * logLb9 r.1 + absAUlo rs
def chkStep (rows : List StepRow) (ap an K : ℕ) : Bool :=
  let p := pPairs rows
  let q := nPairs rows
  treeAll (fun y => Nat.blt K y || Nat.ble (pEval p y + ap) (pEval q y + an)) 12 1
@[category API, AMS 11] lemma psi_of_rows (rows : List StepRow) (ap an K cpsi : ℕ)
    (hvalid : rows.all (fun r => decide (1 ≤ r.1 ∧ r.1 ≤ 300)) = true)
    (hsum0 : sumPosM rows = sumNegM rows) (hK : K ≤ 4096) (hstep : chkStep rows ap an K = true)
    (han_le : an ≤ wNeg rows + ap) (hconst : 2 * S9 * sumAbsA rows ≤ absAUlo rows)
    (hcpsi : ∀ y : ℝ, 0 ≤ y → psi y ≤ ((cpsi : ℝ) / 100) * y) {x : ℝ} (hx : 300 ≤ x) :
    (((negUlo rows : ℝ) - posUhi rows) / S9 -
        ((wNeg rows + ap - an : ℕ) : ℝ) * ((cpsi : ℝ) / 100) / (K + 1 : ℕ)) * x -
      ((sumAbsA rows : ℝ) / 2) * log x ≤ ((an : ℝ) - ap) * psi x := by
  have hx0 : 0 ≤ x := by linarith
  have hrows : ∀ r ∈ rows, 1 ≤ r.1 ∧ r.1 ≤ 300 := by simpa using hvalid
  have hlfac {z : ℝ} (hz : 1 ≤ z) :
      (z - 1 / 2) * log z - z - 1 ≤ log (Nat.factorial ⌊z⌋₊ : ℝ) ∧
        log (Nat.factorial ⌊z⌋₊ : ℝ) ≤ (z + 1 / 2) * log z - z + 1 := by
    have hnat {m : ℕ} (hm : 1 ≤ m) : ((m : ℝ) + 1 / 2) * log m - m ≤ log (Nat.factorial m : ℝ) ∧
        log (Nat.factorial m : ℝ) ≤ ((m : ℝ) + 1 / 2) * log m - m + 1 := by
      have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      refine ⟨by linarith [Stirling.le_log_factorial_stirling (by omega : m ≠ 0),
          log_nonneg (by linarith [pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi)], ?_⟩
      have hant : log (Stirling.stirlingSeq m) ≤ log (Stirling.stirlingSeq 1) := by
        simpa [show m - 1 + 1 = m by omega] using Stirling.log_stirlingSeq'_antitone (Nat.zero_le (m - 1))
      rw [Stirling.log_stirlingSeq_formula m, Stirling.log_stirlingSeq_formula 1] at hant
      simp only [Nat.factorial_one, Nat.cast_one, log_one, mul_one, one_div,
        log_mul two_ne_zero hmR.ne', log_div hmR.ne' (exp_pos 1).ne', log_inv, log_exp] at hant
      linarith
    set m := ⌊z⌋₊
    have hm1 : 1 ≤ m := (Nat.one_le_floor_iff z).mpr hz
    have hmz : (m : ℝ) ≤ z := Nat.floor_le (by linarith)
    have hzm1 := Nat.lt_floor_add_one z
    obtain ⟨_, hhi_m⟩ := hnat hm1
    obtain ⟨hlo_m1, _⟩ := hnat (by omega : 1 ≤ m + 1)
    refine ⟨?_, ?_⟩
    · have hrel : log (Nat.factorial (m + 1) : ℝ) = log (Nat.factorial m : ℝ) + log ((m : ℝ) + 1) := by
        rw [Nat.factorial_succ, Nat.cast_mul, log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), Nat.cast_succ]
        ring
      rw [Nat.cast_add, Nat.cast_one] at hlo_m1
      linarith [le_trans (mul_le_mul_of_nonneg_right (by linarith : z - 1 / 2 ≤ (m : ℝ) + 1 / 2)
        (log_nonneg hz)) (mul_le_mul_of_nonneg_left (log_le_log (by linarith) hzm1.le) (by linarith))]
    · rcases eq_or_lt_of_le hmz with h_eq | h_lt
      · rwa [← h_eq]
      · have hdiff : 1 - (m : ℝ) / z ≤ log z - log m := by
          simpa [inv_div, log_div (by linarith : z ≠ 0) (by linarith : (m : ℝ) ≠ 0)] using
            one_sub_inv_le_log_of_pos (show (0 : ℝ) < z / m by positivity)
        linarith [mul_le_mul_of_nonneg_left hdiff (show (0 : ℝ) ≤ z + 1 / 2 by linarith),
          show (z + 1 / 2) * (1 - (m : ℝ) / z) = (z - m) + (z - m) / (2 * z) by field_simp,
          div_nonneg (sub_nonneg.mpr h_lt.le) (show (0 : ℝ) ≤ 2 * z by linarith),
          mul_nonneg (sub_nonneg.mpr h_lt.le) (log_nonneg (show (1 : ℝ) ≤ m from mod_cast hm1))]
  have hvM (m : ℕ) : ∑ n ∈ Ioc 0 m, Λ n * ((m / n : ℕ) : ℝ) = log (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, log_prod (fun j _ => by positivity)]
    simp_rw [← ArithmeticFunction.vonMangoldt_sum]
    rw [sum_comm' (t' := Ioc 0 m) (s' := fun n => (range m).filter (n ∣ · + 1))]
    · simp_rw [sum_const, nsmul_eq_mul, Nat.card_multiples, mul_comm]
    · intro j n
      simp only [mem_Ioc, Nat.mem_divisors, mem_filter, mem_range]
      exact ⟨fun ⟨hj, hnj, _⟩ => ⟨⟨hj, hnj⟩, Nat.pos_of_dvd_of_pos hnj (by omega), (Nat.le_of_dvd (by omega) hnj).trans hj⟩,
        fun ⟨⟨hj, hnj⟩, _⟩ => ⟨hj, hnj, by omega⟩⟩
  have hwNeg (y : ℕ) : (pEval (pPairs rows) y : ℝ) - pEval (nPairs rows) y ≤ wNeg rows := by
    suffices ∀ rs : List StepRow, (∀ r ∈ rs, 1 ≤ r.1) →
        (pEval (pPairs rs) y : ℝ) - pEval (nPairs rs) y - ((sumPosM rs : ℝ) - sumNegM rs) * y ≤ wNeg rs by
      simpa [hsum0] using this rows fun r hr => (hrows r hr).1
    intro rs hrs
    induction rs with
    | nil => simp [pPairs, nPairs, pEval, sumPosM, sumNegM, wNeg]
    | cons r rs ih =>
      rcases r with ⟨d, isPos, m⟩
      have hd1 : 0 < d := hrs _ List.mem_cons_self
      have hrs' := ih fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      have hdiv : (d : ℝ) * ((y / d : ℕ) : ℝ) = y - ((y % d : ℕ) : ℝ) := by
        have hR : ((d * (y / d) + y % d : ℕ) : ℝ) = y := mod_cast Nat.div_add_mod y d
        push_cast at hR
        linarith
      have hmod_le : (m : ℝ) * ((y % d : ℕ) : ℝ) ≤ d * m := by
        nlinarith [show ((y % d : ℕ) : ℝ) ≤ d from mod_cast (Nat.mod_lt y hd1).le, Nat.cast_nonneg (α := ℝ) m]
      cases isPos
      all_goals
        simp only [pPairs, nPairs, pEval, sumPosM, sumNegM, wNeg,
          Bool.false_eq_true, ↓reduceIte, Nat.add_eq, Nat.mul_eq]
        rw [show y.div d = y / d from rfl]
        push_cast
        rw [show (d : ℝ) * m * (y / d : ℕ) = m * (d * (y / d : ℕ)) by ring, hdiv]
        linarith [show 0 ≤ (m : ℝ) * ((y % d : ℕ) : ℝ) by positivity]
  have heval_cons (d a : ℕ) (ps : List (ℕ × ℕ)) :
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (pEval ((d, a) :: ps) (⌊x⌋₊ / n) : ℝ) =
        (a : ℝ) * log (Nat.factorial ⌊x / d⌋₊ : ℝ) + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (pEval ps (⌊x⌋₊ / n) : ℝ) := by
    have hlf : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (((⌊x⌋₊ / n).div d : ℕ) : ℝ) = log (Nat.factorial ⌊x / d⌋₊ : ℝ) := by
      rw [show (fun n => Λ n * (((⌊x⌋₊ / n).div d : ℕ) : ℝ)) = fun n => Λ n * ((⌊x⌋₊ / n / d : ℕ) : ℝ) from rfl,
        Nat.floor_div_natCast, ← hvM (⌊x⌋₊ / d)]
      simp_rw [Nat.div_div_eq_div_mul, mul_comm _ d, ← Nat.div_div_eq_div_mul]
      refine (sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self ⌊x⌋₊ d)) fun n hn1 hn2 => ?_).symm
      rw [mem_Ioc] at hn1 hn2
      rw [Nat.div_eq_zero_iff.mpr (Or.inr (by omega)), Nat.cast_zero, mul_zero]
    simp only [pEval, Nat.add_eq, Nat.mul_eq]
    rw [← hlf, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun _ _ => ?_
    push_cast
    ring
  have hstirl : ∀ rs : List StepRow, (∀ r ∈ rs, 1 ≤ r.1 ∧ r.1 ≤ 300) →
      2 * (S9 : ℝ) * (((sumPosM rs : ℝ) - sumNegM rs) * (x * log x - x)) +
        2 * ((negUlo rs : ℝ) - posUhi rs) * x -
        (S9 : ℝ) * sumAbsA rs * log x + ((absAUlo rs : ℝ) - 2 * S9 * sumAbsA rs) ≤
        2 * S9 * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (pEval (pPairs rs) (⌊x⌋₊ / n) : ℝ) -
          ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (pEval (nPairs rs) (⌊x⌋₊ / n) : ℝ)) := by
    intro rs hrs_all
    induction rs with
    | nil => simp [sumPosM, sumNegM, negUlo, posUhi, sumAbsA, absAUlo, pPairs, nPairs, pEval]
    | cons r rs ih =>
      rcases r with ⟨d, isPos, m⟩
      obtain ⟨hd1, hd300⟩ := hrs_all _ List.mem_cons_self
      dsimp only at hd1 hd300
      have hrs := ih fun q hq => hrs_all q (List.mem_cons_of_mem _ hq)
      have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd1
      obtain ⟨hlog_lo, hlog_hi⟩ := log_bds hd1
      have hS9 : (0 : ℝ) < S9 := by
        unfold S9
        norm_num
      have hloS := (div_le_iff₀ hS9).mp hlog_lo
      have hhiS := (le_div_iff₀ hS9).mp hlog_hi
      obtain ⟨hf_lo, hf_hi⟩ := hlfac (z := x / d)
        ((one_le_div hdR).mpr (by linarith [show (d : ℝ) ≤ 300 from mod_cast hd300]))
      rw [log_div (by linarith) hdR.ne'] at hf_lo hf_hi
      have ha_nn : (0 : ℝ) ≤ 2 * S9 * (d * m) := by positivity
      cases isPos
      · simp only [sumPosM, sumNegM, negUlo, posUhi, sumAbsA, absAUlo,
          pPairs, nPairs, Bool.false_eq_true, ↓reduceIte]
        rw [heval_cons]
        push_cast
        have hlin : 2 * (S9 : ℝ) * ((d : ℝ) * m) * ((x / d + 1 / 2) * (log x - log d) - x / d + 1) =
            2 * S9 * (m * (x * log x - x)) - 2 * (m * (log d * S9) * x) +
              S9 * (d * m) * log x - (d : ℝ) * m * (log d * S9) + 2 * S9 * (d * m) := by
          field_simp [hdR.ne']
          ring
        linarith [mul_le_mul_of_nonneg_left hf_hi ha_nn, hlin,
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hloS (Nat.cast_nonneg m)) hx0,
          mul_le_mul_of_nonneg_left hloS (show (0 : ℝ) ≤ (d : ℝ) * m by positivity)]
      · simp only [sumPosM, sumNegM, negUlo, posUhi, sumAbsA, absAUlo, pPairs, nPairs, ↓reduceIte]
        rw [heval_cons]
        push_cast
        have hlin : 2 * (S9 : ℝ) * ((d : ℝ) * m) * ((x / d - 1 / 2) * (log x - log d) - x / d - 1) =
            2 * S9 * (m * (x * log x - x)) - 2 * (m * (log d * S9) * x) -
              S9 * (d * m) * log x + (d : ℝ) * m * (log d * S9) - 2 * S9 * (d * m) := by
          field_simp [hdR.ne']
          ring
        linarith [mul_le_mul_of_nonneg_left hf_lo ha_nn, hlin,
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhiS (Nat.cast_nonneg m)) hx0,
          mul_le_mul_of_nonneg_left hloS (show (0 : ℝ) ≤ (d : ℝ) * m by positivity)]
  have hst := hstirl rows hrows
  have hdiff_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (pEval (pPairs rows) (⌊x⌋₊ / n) : ℝ) -
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (pEval (nPairs rows) (⌊x⌋₊ / n) : ℝ) =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ((pEval (pPairs rows) (⌊x⌋₊ / n) : ℝ) -
        pEval (nPairs rows) (⌊x⌋₊ / n)) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => (mul_sub _ _ _).symm
  rw [hdiff_eq] at hst
  have hsum_le := sum_le_sum (s := Ioc 0 ⌊x⌋₊) fun n hn => show Λ n *
      ((pEval (pPairs rows) (⌊x⌋₊ / n) : ℝ) - pEval (nPairs rows) (⌊x⌋₊ / n)) ≤
      ((an : ℝ) - ap) * Λ n + if n ≤ ⌊x⌋₊ / (K + 1) then ((wNeg rows + ap - an : ℕ) : ℝ) * Λ n else 0 by
    rw [mem_Ioc] at hn
    have hvn := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    split_ifs with hle
    · rw [Nat.cast_sub han_le, Nat.cast_add]
      linarith [mul_le_mul_of_nonneg_left (hwNeg (⌊x⌋₊ / n)) hvn]
    · have hy2 : ⌊x⌋₊ / n < 1 + K := by
        by_contra hge
        apply hle
        rw [Nat.le_div_iff_mul_le (by omega)]
        exact ((Nat.le_div_iff_mul_le hn.1).mp (by omega : K + 1 ≤ ⌊x⌋₊ / n)).trans' (by rw [mul_comm])
      have h2_12 : 1 + K ≤ 1 + 2 ^ 12 := by
        norm_num
        omega
      have ht := (treeAll_iff _ 12 1).mp hstep (⌊x⌋₊ / n) (mem_Ico.mpr ⟨Nat.div_pos hn.2 hn.1, hy2.trans_le h2_12⟩)
      simp only [Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at ht
      have hst0 : (pEval (pPairs rows) (⌊x⌋₊ / n) : ℝ) + ap ≤
          pEval (nPairs rows) (⌊x⌋₊ / n) + an := mod_cast ht.resolve_left (by omega)
      linarith [mul_le_mul_of_nonneg_left (by linarith :
        (pEval (pPairs rows) (⌊x⌋₊ / n) : ℝ) - pEval (nPairs rows) (⌊x⌋₊ / n) ≤ (an : ℝ) - ap) hvn]
  simp only [sum_add_distrib, ← mul_sum] at hsum_le
  have htail : (∑ n ∈ Ioc 0 ⌊x⌋₊, if n ≤ ⌊x⌋₊ / (K + 1) then ((wNeg rows + ap - an : ℕ) : ℝ) * Λ n else 0) =
      ((wNeg rows + ap - an : ℕ) : ℝ) * psi (x / (K + 1 : ℕ)) := by
    have hflt : (Ioc 0 ⌊x⌋₊).filter (· ≤ ⌊x⌋₊ / (K + 1)) = Ioc 0 (⌊x⌋₊ / (K + 1)) := by
      ext
      simp only [mem_filter, mem_Ioc]
      have := Nat.div_le_self ⌊x⌋₊ (K + 1)
      omega
    rw [← sum_filter, hflt, ← mul_sum, ← Nat.floor_div_natCast]
    rfl
  rw [show ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n = psi x from rfl, htail] at hsum_le
  rw [hsum0, sub_self, zero_mul, mul_zero, zero_add] at hst
  have hconst_nn : (2 : ℝ) * S9 * sumAbsA rows ≤ absAUlo rows := mod_cast hconst
  have hS9_pos : (0 : ℝ) < S9 := by
    unfold S9
    norm_num
  have hst' := le_of_mul_le_mul_right (calc
    (((negUlo rows : ℝ) - posUhi rows) / S9 * x - ((sumAbsA rows : ℝ) / 2) * log x) * (2 * S9)
      = 2 * ((negUlo rows : ℝ) - posUhi rows) * x - (S9 : ℝ) * sumAbsA rows * log x := by field_simp [hS9_pos.ne']
    _ ≤ (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ((pEval (pPairs rows) (⌊x⌋₊ / n) : ℝ) -
          pEval (nPairs rows) (⌊x⌋₊ / n))) * (2 * S9) := by linarith [hst, hconst_nn]) (by positivity)
  have htail_le := mul_le_mul_of_nonneg_left (hcpsi (x / (K + 1 : ℕ)) (by positivity)) (Nat.cast_nonneg (wNeg rows + ap - an))
  linarith [show ((wNeg rows + ap - an : ℕ) : ℝ) * (((cpsi : ℝ) / 100) * (x / (K + 1 : ℕ))) =
      (((wNeg rows + ap - an : ℕ) : ℝ) * ((cpsi : ℝ) / 100) / (K + 1 : ℕ)) * x by ring]
def tLoData : List StepRow := [
  (1, true, 999997), (2, false, 500000), (3, false, 333333), (5, false, 200000), (6, true, 166667), (7, false, 142857),
  (10, true, 100000), (11, false, 90909), (13, false, 76923), (14, true, 71429), (15, true, 62093), (16, false, 8625),
  (17, false, 46670), (19, false, 52632), (21, true, 47619), (22, true, 13533), (23, false, 12944), (26, true, 31989),
  (28, false, 17678), (29, false, 11611), (30, false, 38876), (31, false, 24681), (32, true, 4313), (33, true, 30303),
  (34, true, 22690), (38, true, 14362), (41, false, 4167), (42, false, 19740), (43, false, 12183), (44, true, 1559),
  (49, true, 2816), (53, false, 723), (55, true, 3716), (57, true, 7969), (58, true, 7034), (62, true, 6540), (66, false, 7019),
  (71, false, 5440), (72, false, 10680), (84, true, 3858), (86, true, 2056), (95, true, 3283), (98, false, 1544), (103, false, 3672),
  (105, false, 2044), (112, true, 1169), (115, true, 1301), (117, true, 2087), (124, true, 1410), (136, true, 1640),
  (178, true, 1781), (194, true, 2645), (209, true, 1551), (251, true, 485), (252, true, 1742), (279, true, 1671),
  (288, true, 1768), (300, true, 1875)]
def tHiNeg : List StepRow := [
  (1, false, 1000000), (2, true, 500000), (3, true, 333333), (5, true, 200000), (6, false, 166667), (7, true, 142857),
  (10, false, 100000), (11, true, 90909), (13, true, 59094), (14, false, 54873), (15, false, 66667), (17, true, 58824),
  (19, true, 36255), (21, false, 32802), (22, false, 45455), (23, true, 43478), (26, false, 29547), (28, false, 8278),
  (29, true, 28932), (30, true, 38699), (31, true, 12636), (33, false, 11870), (34, false, 31597), (35, false, 26448),
  (38, false, 9003), (39, false, 2948), (41, true, 21680), (42, true, 13528), (43, true, 3674), (44, true, 6006),
  (46, false, 9179), (55, false, 4410), (57, false, 8521), (58, false, 13786), (59, true, 6236), (66, true, 4307),
  (68, true, 2673), (70, true, 9913), (71, true, 5020), (72, true, 2229), (78, true, 3223), (82, false, 6419), (85, false, 3319),
  (87, false, 2541), (90, false, 2392), (91, false, 3255), (92, false, 1552), (93, false, 5219), (95, false, 4715), (99, true, 1243),
  (102, true, 1895), (105, true, 1667), (107, true, 1673), (112, true, 3681), (114, true, 3586), (116, true, 1971),
  (120, true, 264), (123, false, 1714), (131, true, 1924), (141, false, 2024), (143, false, 1666), (150, false, 1878),
  (165, true, 745), (167, true, 776), (183, true, 1438), (189, true, 3137), (206, true, 1873), (237, true, 747), (247, true, 1092),
  (254, true, 1006), (256, true, 1156), (272, true, 1290), (277, true, 1407), (285, true, 832), (289, true, 1121),
  (295, false, 971), (298, true, 1686)]
def lcmUp : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmUp n) (n + 1)
@[category API, AMS 11] lemma cert_hi : chkStep tHiNeg 999857 0 4096 = true := by decide
@[category API, AMS 11] lemma psi_le_142 (x : ℝ) (hx : 0 ≤ x) : psi x ≤ (142 / 100 : ℝ) * x := by
  have h539 : ∀ y : ℝ, 0 ≤ y → psi y ≤ ((539 : ℕ) / 100 : ℝ) * y := fun y hy => by
    have : log 4 < 1.3863 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
      push_cast
      linarith [log_two_lt_d9]
    nlinarith [psi_le_const_mul_self hy]
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    positivity
  rcases lt_or_ge x 300 with hlt | hge
  · set n := ⌊x⌋₊
    rw [psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
    have hlcm_eq : ∀ m : ℕ, lcmUp m = m.lcmUpto := fun m => by
      induction m with
      | zero => rfl
      | succ m ih =>
        unfold lcmUp Nat.lcmUpto
        have hI : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
          ext
          simp only [mem_Icc, mem_insert]
          omega
        rw [ih, hI, lcm_insert, Nat.lcm_comm]
        rfl
    have hchk : treeAll (fun m => Nat.blt 300 m || Nat.ble (lcmUp m * lcmUp m) (1 <<< (3 * m))) 9 0 = true := by decide
    have hn300 : n ≤ 300 := ((Nat.floor_lt hx).mpr hlt).le
    have hbit := (treeAll_iff _ 9 0).mp hchk n (mem_Ico.mpr ⟨Nat.zero_le n, by omega⟩)
    simp only [Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.shiftLeft_eq, one_mul] at hbit
    have hsq : (n.lcmUpto : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (3 * n) := by
      rw [sq, ← hlcm_eq]
      exact_mod_cast hbit.resolve_left (by omega)
    have hlog := log_le_log (pow_pos (Nat.cast_pos.mpr n.lcmUpto_pos) 2) hsq
    rw [log_pow, log_pow] at hlog
    push_cast at hlog
    nlinarith [log_two_lt_d9, Nat.floor_le hx, Nat.cast_nonneg (α := ℝ) n]
  · have hb := psi_of_rows tHiNeg 999857 0 4096 539 (by decide) (by decide) le_rfl cert_hi (by decide) (by decide) h539 hge
    rw [show negUlo tHiNeg = 1825589272932389 by decide, show posUhi tHiNeg = 2858030900883144 by decide,
      show wNeg tHiNeg = 16175620 by decide, show sumAbsA tHiNeg = 37500454 by decide] at hb
    unfold S9 at hb
    norm_num at hb
    have h2 := log_le_log (by norm_num : (0 : ℝ) < (300 : ℝ) ^ (3 : ℕ)) (by norm_num : (300 : ℝ) ^ (3 : ℕ) ≤ (2 : ℝ) ^ (25 : ℕ))
    rw [log_pow, log_pow] at h2
    norm_num at h2
    have hm : log x = log 300 + log (x / 300) := by
      conv_lhs => rw [show x = 300 * (x / 300) by ring]
      exact log_mul (by norm_num) (by positivity)
    linarith [log_two_lt_d9, log_le_sub_one_of_pos (show (0 : ℝ) < x / 300 by positivity), log_nonneg hx1]
@[category API, AMS 11] lemma theta_bds {x : ℝ} (hx : 300 ≤ x) :
    ((9569 : ℝ) / 10000) * x - ((156 : ℝ) / 10) * log x - ((426 : ℝ) / 100) * sqrt x ≤ theta x ∧
      theta x ≤ ((10386 : ℝ) / 10000) * x + ((188 : ℝ) / 10) * log x := by
  have hx1 : 1 ≤ x := by linarith
  have hb_lo := psi_of_rows tLoData 0 1000119 3072 142 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) psi_le_142 hx
  have hb_hi := psi_of_rows tHiNeg 999857 0 4096 142 (by decide) (by decide) le_rfl cert_hi (by decide) (by decide)
    psi_le_142 hx
  rw [show negUlo tLoData = 2664365459354840 by decide, show posUhi tLoData = 1700915161129655 by decide,
    show wNeg tLoData = 14916917 by decide, show sumAbsA tLoData = 31099926 by decide] at hb_lo
  rw [show negUlo tHiNeg = 1825589272932389 by decide, show posUhi tHiNeg = 2858030900883144 by decide,
    show wNeg tHiNeg = 16175620 by decide, show sumAbsA tHiNeg = 37500454 by decide] at hb_hi
  unfold S9 at hb_lo hb_hi
  norm_num at hb_lo hb_hi
  have hcp := psi_sub_theta_le_psi_add_psi_add_psi x
  have hsqrt : x ^ (2 : ℝ)⁻¹ = sqrt x := by rw [← one_div, ← sqrt_eq_rpow]
  have hp2 := psi_le_142 (sqrt x) (sqrt_nonneg x)
  have hp3 := (psi_le_142 _ (rpow_nonneg (by linarith) _)).trans
    (mul_le_mul_of_nonneg_left (hsqrt ▸ Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (3 : ℝ)⁻¹ ≤ 2⁻¹)) (by norm_num))
  have hp5 := (psi_le_142 _ (rpow_nonneg (by linarith) _)).trans
    (mul_le_mul_of_nonneg_left (hsqrt ▸ Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5 : ℝ)⁻¹ ≤ 2⁻¹)) (by norm_num))
  rw [hsqrt] at hcp
  exact ⟨by linarith [sqrt_nonneg x, log_nonneg hx1], by linarith [theta_le_psi x, log_nonneg hx1]⟩

/- ### Section 3: Regime 1 (`1 ≤ k ≤ 9`) via Compact Delta-Encoded Subsets -/
def treeLcm (u : ℕ) : ℕ → ℕ → ℕ
  | 0, b => if Nat.ble 1 b && Nat.ble b u then b else 1
  | d + 1, b => Nat.lcm (treeLcm u d b) (treeLcm u d (b + (1 <<< d)))
def bMask : ℕ → List ℕ → (ℕ × ℕ) × List ℕ
  | _, [] => ((0, 0), [])
  | 0, x :: xs => ((1 <<< x, x), xs)
  | d + 1, xs =>
    let ((m1, s1), ys) := bMask d xs
    let ((m2, s2), zs) := bMask d ys
    ((m1 ||| (m2 <<< s1), s1 + s2), zs)
def chkCert (w k d L : ℕ) (ds : List ℕ) : Bool :=
  let mask := (bMask 9 ds).1.1
  Nat.blt 0 L && Nat.beq (treeSum (fun n =>
    if Nat.ble 1 n && Nat.ble n w && Nat.beq (L % n) 0 && !mask.testBit n then L / n else 0) d 0) (k * L)
@[category API, AMS 11] lemma rep_W_le_9 {k : ℕ} (hk1 : 1 ≤ k) (hk9 : k ≤ 9) : IsRepresentable (W k) k := by
  have hcert {w k' d L : ℕ} {ds : List ℕ} (h : chkCert w k' d L ds = true) : IsRepresentable w k' := by
    unfold chkCert at h
    dsimp only at h
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    set mask := (bMask 9 ds).1.1
    let keep n := Nat.ble 1 n && Nat.ble n w && Nat.beq (L % n) 0 && !mask.testBit n
    let S := (Ico 0 (2 ^ d)).filter (keep · = true)
    refine ⟨S, fun n hn => ?_, ?_⟩
    · simp only [S, keep, mem_filter, mem_Icc, Bool.and_eq_true, Nat.ble_eq] at hn ⊢
      exact ⟨hn.2.1.1.1, hn.2.1.1.2⟩
    · have hdvd : ∀ n ∈ S, 0 < n ∧ n ∣ L := fun n hn => by
        simp only [S, keep, mem_filter, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hn
        exact ⟨hn.2.1.1.1, Nat.dvd_of_mod_eq_zero hn.2.1.2⟩
      have hsum : ∑ n ∈ S, L / n = k' * L := by
        rw [← h.2, treeSum_Ico, zero_add]
        simp [S, keep, sum_filter]
      rw [inv_dvd h.1 hdvd, hsum, Nat.cast_mul, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr h.1.ne')]
  interval_cases k
  · exact ⟨{1}, by simp [W], by simp⟩
  · simp only [W, show ¬(2 ≤ 1) by decide, ↓reduceIte]
    exact hcert (d := 4) (L := 6) (ds := []) (by decide)
  · rw [W_eq_bds 30]
    exact hcert (d := 5) (L := 360) (ds := [12, 18]) (by decide)
  · rw [W_eq_bds 82]
    exact hcert (d := 7) (L := 10810800) (ds := [16, 4, 5, 5, 9, 21, 10, 2, 6]) (by decide)
  · rw [W_eq_bds 225]
    exact hcert (d := 8) (L := 6746328388800) (ds := [36, 40, 4, 10, 15, 15, 10, 2, 6, 6, 3, 23, 1, 9, 4, 32, 5]) (by decide)
  · rw [W_eq_bds 613]
    exact hcert (d := 10) (L := treeLcm 53 6 0 * 1980)
      (ds := [32, 32, 80, 36, 25, 11, 24, 13, 12, 14, 50, 1, 30, 32, 78, 14, 20, 9, 5, 12, 16, 5, 4, 28, 12, 7, 3, 6, 1]) (by decide)
  · rw [W_eq_bds 1667]
    exact hcert (d := 11) (L := treeLcm 113 7 0 * 116396280)
      (ds := [32, 32, 16, 10, 30, 24, 36, 60, 16, 104, 126, 162, 28, 6, 38, 2, 27, 1, 117, 6, 31, 45, 19, 13, 6, 40, 2, 36, 3, 38, 24,
        26, 27, 17, 4, 8, 8, 16, 3, 34, 5, 6, 24, 3, 17, 24, 6, 7, 41, 5, 3, 10, 18, 18, 53, 17, 38, 7, 2, 5, 23, 11, 19, 8, 4, 3])
      (by decide)
  · rw [W_eq_bds 4531]
    exact hcert (d := 13) (L := treeLcm 269 9 0 * 2986012260)
      (ds := [48, 12, 4, 16, 10, 30, 8, 16, 36, 60, 120, 360, 379, 359, 103, 26, 95, 111, 48, 12, 91, 204, 21, 123, 4, 5, 20, 17, 15,
        35, 32, 2, 23, 8, 44, 26, 4, 7, 29, 7, 22, 27, 78, 54, 10, 83, 21, 3, 24, 29, 30, 8, 18, 10, 27, 15, 55, 4, 48, 9, 6, 22, 1,
        32, 16, 6, 4, 46, 22, 49, 27, 7, 10, 31, 5, 6, 21, 12, 3, 32, 11, 21, 50, 143, 15, 7, 13, 12, 36, 5, 8, 19, 12, 4, 42, 15, 115,
        32, 17, 30, 12, 48, 2, 7, 13, 28, 26, 11, 20, 25, 5, 2, 12, 14, 12, 4, 24, 4, 1, 27, 64, 11, 18, 12, 6, 4, 9]) (by decide)
  · rw [W_eq_bds 12317]
    exact hcert (d := 14) (L := treeLcm 599 10 0 * 115491417841800)
      (ds := [40, 8, 16, 16, 10, 30, 24, 36, 60, 120, 152, 208, 304, 1024, 161, 916, 763, 53, 128, 82, 42, 118, 107, 634, 69, 162, 12,
        96, 85, 123, 132, 113, 22, 269, 79, 99, 144, 128, 6, 123, 10, 75, 23, 6, 66, 80, 12, 178, 39, 117, 2, 43, 48, 58, 1, 29, 25,
        19, 29, 84, 49, 62, 23, 53, 35, 33, 26, 6, 14, 89, 30, 10, 62, 27, 37, 10, 36, 74, 40, 12, 121, 58, 22, 62, 7, 23, 46, 9, 52,
        11, 25, 19, 15, 1, 31, 15, 9, 35, 38, 75, 76, 26, 30, 5, 51, 4, 77, 86, 66, 4, 3, 92, 3, 14, 3, 37, 44, 109, 10, 16, 137, 9,
        38, 19, 8, 36, 45, 13, 7, 56, 5, 57, 33, 26, 39, 24, 18, 2, 5, 18, 9, 6, 34, 49, 31, 23, 20, 51, 9, 5, 26, 5, 10, 51, 1, 23,
        47, 14, 5, 25, 37, 4, 27, 4, 14, 24, 7, 4, 14, 11, 3, 22, 3, 20, 26, 5, 8, 7, 17, 9, 19, 56, 29, 17, 12, 41, 14, 1, 5, 5, 20,
        3, 39, 35, 10, 24, 36, 20, 1, 10, 7, 7, 5, 9, 22, 4, 24, 7, 13, 7, 43, 8, 2, 3, 11, 42, 42, 1, 6, 3, 14, 4, 16, 24, 2, 1, 11,
        54, 6, 15, 5, 25, 12, 3, 3, 7, 19, 30, 16, 1, 7, 9, 1, 55, 1, 3, 4, 10, 26, 1, 3, 17, 3, 1, 15, 46, 21, 31, 1]) (by decide)

/- ### Section 4: Modular Gadgets and `Rat.den` Sieve Cancellation -/

structure Gadget where
  (M D : ℕ) (S : Finset ℕ) (A B : ℕ) (eta : ℚ) (hD_pos : 0 < D) (hS_sub : S ⊆ Icc 1 M)
  (hS_dvd : ∀ d ∈ S, d ∣ D) (hD_smooth : ∀ p, p.Prime → p ∣ D → p ≤ M) (hA_le_B : A ≤ B)
  (hcov : ∀ t, A ≤ t → t ≤ B → ∃ U ⊆ S, ∑ d ∈ U, D / d = t)
  (heta : ((∑ d ∈ S, D / d : ℕ) : ℚ) - B = eta * D)
def dpMask (D : ℕ) : List ℕ → ℕ
  | [] => 1
  | d :: ds =>
    let bs := dpMask D ds
    bs ||| (bs <<< (D / d))
def chkRange (bs A L : ℕ) : Bool :=
  let m := (1 <<< L) - 1
  Nat.beq ((bs >>> A) &&& m) m
@[category API, AMS 11] lemma dpMask_ok {D A L : ℕ} {ds : List ℕ} (hnd : ds.Nodup)
    (h : chkRange (dpMask D ds) A L = true) {t : ℕ} (ht1 : A ≤ t) (ht2 : t < A + L) :
    ∃ U ⊆ ds.toFinset, ∑ d ∈ U, D / d = t := by
  have hdp : ∀ l : List ℕ, l.Nodup → ∀ i, (dpMask D l).testBit i = true → ∃ U ⊆ l.toFinset, ∑ d ∈ U, D / d = i := by
    intro l
    induction l with
    | nil =>
      intro _ i hi
      refine ⟨∅, empty_subset _, ?_⟩
      rcases eq_or_ne i 0 with rfl | h0
      · simp
      · exact absurd hi (by simp [dpMask, Nat.testBit_eq_false_of_lt (Nat.one_lt_pow h0 (by decide))])
    | cons d l ih =>
      intro hl i hi
      obtain ⟨hd, hl'⟩ := List.nodup_cons.mp hl
      simp only [dpMask, Nat.testBit_or, Bool.or_eq_true] at hi
      rcases hi with hk | hs
      · obtain ⟨U, hU, hs'⟩ := ih hl' i hk
        exact ⟨U, hU.trans (by simp), hs'⟩
      · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨U, hU, hs'⟩ := ih hl' (i - D / d) hs.2
        refine ⟨insert d U, ?_, ?_⟩
        · rw [List.toFinset_cons]
          exact insert_subset_insert d hU
        · rw [sum_insert fun hm => hd (List.mem_toFinset.mp (hU hm)), hs']
          omega
  have hbit := congrArg (·.testBit (t - A)) (Nat.beq_eq.mp h)
  have hmask : (((1 : ℕ) <<< L) - 1).testBit (t - A) = true := by
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    omega
  rw [Nat.testBit_and, Nat.testBit_shiftRight, hmask, Bool.and_true, show A + (t - A) = t by omega] at hbit
  exact hdp ds hnd t hbit
def divsLe (M D : ℕ) : List ℕ := (List.range M).map (· + 1) |>.filter fun d => Nat.beq (D % d) 0
def mkDivG (M D A B : ℕ) (hD : 0 < D) (hAB : A ≤ B)
    (hsmooth : ∀ p ∈ List.range (D + 1), p.Prime → D % p = 0 → p ≤ M)
    (hcov : chkRange (dpMask D (divsLe M D)) A (B - A + 1) = true)
    (heta : (divsLe M D).foldl (fun acc d => acc + D / d) 0 = B + A) : Gadget :=
  have hnd : (divsLe M D).Nodup :=
    List.Nodup.filter _ ((List.nodup_map_iff_inj_on List.nodup_range).mpr fun _ _ _ _ h => by omega)
  have hmem : ∀ {d}, d ∈ divsLe M D ↔ 1 ≤ d ∧ d ≤ M ∧ D % d = 0 := fun {d} => by
    simp only [divsLe, List.mem_filter, List.mem_map, List.mem_range, Nat.beq_eq]
    exact ⟨by rintro ⟨⟨_, _, rfl⟩, hm⟩
              exact ⟨by omega, by omega, hm⟩,
      fun ⟨h1, h2, hm⟩ => ⟨⟨d - 1, by omega, by omega⟩, hm⟩⟩
  { M := M, D := D, S := (divsLe M D).toFinset, A := A, B := B, eta := (A : ℚ) / D, hD_pos := hD, hA_le_B := hAB,
    hS_sub := fun d hd => by
      rw [List.mem_toFinset, hmem] at hd
      exact mem_Icc.mpr ⟨hd.1, hd.2.1⟩,
    hS_dvd := fun d hd => by
      rw [List.mem_toFinset, hmem] at hd
      exact Nat.dvd_of_mod_eq_zero hd.2.2,
    hD_smooth := fun p hp hd => hsmooth p
      (List.mem_range.mpr (by have := Nat.le_of_dvd hD hd
                              omega)) hp (Nat.mod_eq_zero_of_dvd hd),
    hcov := fun t ht1 ht2 => dpMask_ok hnd hcov ht1 (by omega),
    heta := by
      have hfold : ∀ (l : List ℕ) (acc : ℕ), l.foldl (fun s d => s + D / d) acc = acc + (l.map (D / ·)).sum := by
        intro l
        induction l with
        | nil => simp
        | cons x _ ih =>
          intro acc
          simp [ih (acc + D / x), Nat.add_assoc]
      rw [List.sum_toFinset _ hnd, ← zero_add (List.sum _), ← hfold, heta]
      push_cast
      rw [div_mul_cancel₀ _ (by positivity)]
      ring }
@[category API, AMS 11] lemma sub_two_pow : ∀ n t : ℕ, t < 2 ^ n → ∃ U ⊆ range n, ∑ i ∈ U, 2 ^ i = t
  | 0, t, ht => ⟨∅, empty_subset _, by
      rw [sum_empty]
      omega⟩
  | n + 1, t, ht => if hlt : t < 2 ^ n then
      let ⟨U, hU, hs⟩ := sub_two_pow n t hlt
      ⟨U, hU.trans (range_mono n.le_succ), hs⟩
    else
      let ⟨U, hU, hs⟩ := sub_two_pow n (t - 2 ^ n) (by
        rw [pow_succ'] at ht
        omega)
      ⟨insert n U, insert_subset (mem_range.mpr n.lt_succ_self) (hU.trans (range_mono n.le_succ)), by
        have hnm : n ∉ U := fun hm => by
          have := mem_range.mp (hU hm)
          omega
        rw [sum_insert hnm, hs]
        omega⟩
@[category API, AMS 11] lemma img_two_pow {c s k : ℕ} (hc : 0 < c) (hk : k ≤ s + 1) {U : Finset ℕ} (hU : U ⊆ range k) :
    ∑ x ∈ U.image (fun i => c * 2 ^ (s - i)), (c * 2 ^ s) / x = ∑ i ∈ U, 2 ^ i ∧
    ∑ x ∈ U.image (fun i => c * 2 ^ (s - i)), (1 : ℚ) / x = ((∑ i ∈ U, 2 ^ i : ℕ) : ℚ) / (c * 2 ^ s : ℕ) := by
  have h1 : ∑ x ∈ U.image (fun i => c * 2 ^ (s - i)), (c * 2 ^ s) / x = ∑ i ∈ U, 2 ^ i := by
    have hinj : ∀ a ∈ U, ∀ b ∈ U, c * 2 ^ (s - a) = c * 2 ^ (s - b) → a = b := fun a ha b hb hab => by
      have := mem_range.mp (hU ha)
      have := mem_range.mp (hU hb)
      have := Nat.pow_right_injective (by decide : 2 ≤ 2) (Nat.eq_of_mul_eq_mul_left hc hab)
      omega
    rw [sum_image hinj]
    refine sum_congr rfl fun i hi => ?_
    have := mem_range.mp (hU hi)
    have hpow : c * 2 ^ s = c * 2 ^ (s - i) * 2 ^ i := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hpow, Nat.mul_div_cancel_left _ (Nat.mul_pos hc (Nat.two_pow_pos _))]
  refine ⟨h1, ?_⟩
  have hdvd : ∀ x ∈ U.image (fun i => c * 2 ^ (s - i)), 0 < x ∧ x ∣ c * 2 ^ s := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have := mem_range.mp (hU hi)
    exact ⟨Nat.mul_pos hc (Nat.two_pow_pos _), Nat.mul_dvd_mul_left c (Nat.pow_dvd_pow 2 (by omega))⟩
  rw [inv_dvd (Nat.mul_pos hc (Nat.two_pow_pos s)) hdvd, h1]
def extendG (G : Gadget) {M q : ℕ} (hq0 : 0 < q) (hqM : q ≤ M) (hGM : G.M = M)
    {Tq : Finset ℕ} (hTq : ∀ m ∈ Tq, 1 ≤ m ∧ m ≤ M ∧ m ∣ G.D * q ∧ ¬ m ∣ G.D)
    (hreach : ∀ j < q, ∃ U ⊆ Tq, (∑ m ∈ U, (G.D * q) / m) % q = j)
    (hAB : q * G.A + ∑ m ∈ Tq, (G.D * q) / m ≤ q * G.B) : Gadget :=
  let hdisj : Disjoint G.S Tq := disjoint_left.mpr fun x hxG hxT => (hTq x hxT).2.2.2 (G.hS_dvd x hxG)
  let hDq : 0 < G.D * q := Nat.mul_pos G.hD_pos hq0
  have hmul_div {U : Finset ℕ} (h : ∀ d ∈ U, 0 < d ∧ d ∣ G.D) : ∑ d ∈ U, (G.D * q) / d = q * ∑ d ∈ U, G.D / d := by
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    obtain ⟨hd0, k, hk⟩ := h d hd
    rw [hk, show d * k * q = d * (q * k) by ring, Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0]
  { M := M, D := G.D * q, S := G.S ∪ Tq, A := q * G.A + ∑ m ∈ Tq, (G.D * q) / m, B := q * G.B,
    eta := G.eta + ∑ m ∈ Tq, (1 : ℚ) / m, hD_pos := hDq, hA_le_B := hAB,
    hS_sub := fun x hx => (mem_union.mp hx).elim (fun h => hGM ▸ G.hS_sub h) fun h => mem_Icc.mpr ⟨(hTq x h).1, (hTq x h).2.1⟩,
    hS_dvd := fun x hx => (mem_union.mp hx).elim (fun h => dvd_mul_of_dvd_left (G.hS_dvd x h) q) fun h => (hTq x h).2.2.1,
    hD_smooth := fun p hp hd => (hp.dvd_mul.mp hd).elim (fun h => hGM ▸ G.hD_smooth p hp h) fun h => (Nat.le_of_dvd hq0 h).trans hqM,
    hcov := fun u huA huB => by
      obtain ⟨U₂, hU₂, hmod⟩ := hreach (u % q) (Nat.mod_lt u hq0)
      set s := ∑ m ∈ U₂, (G.D * q) / m
      have hs_le : s ≤ ∑ m ∈ Tq, (G.D * q) / m := sum_le_sum_of_subset hU₂
      have hu_eq : q * ((u - s) / q) = u - s := Nat.mul_div_cancel' ⟨u / q - s / q, by
        have := Nat.div_add_mod u q
        have := Nat.div_add_mod s q
        have := Nat.div_le_div_right (c := q) (by omega : s ≤ u)
        rw [Nat.mul_sub, hmod] at *
        omega⟩
      obtain ⟨U₁, hU₁, hs₁⟩ := G.hcov ((u - s) / q) (Nat.le_of_mul_le_mul_left (by omega) hq0) (Nat.le_of_mul_le_mul_left (by omega) hq0)
      refine ⟨U₁ ∪ U₂, union_subset_union hU₁ hU₂, ?_⟩
      rw [sum_union (Disjoint.mono hU₁ hU₂ hdisj),
        hmul_div fun d hd => ⟨(mem_Icc.mp (G.hS_sub (hU₁ hd))).1, G.hS_dvd d (hU₁ hd)⟩, hs₁, hu_eq]
      omega,
    heta := by
      have hTQ : ((∑ m ∈ Tq, (G.D * q) / m : ℕ) : ℚ) = (∑ m ∈ Tq, (1 : ℚ) / m) * (G.D * q : ℕ) := by
        rw [inv_dvd hDq (fun m hm => ⟨(hTq m hm).1, (hTq m hm).2.2.1⟩), div_mul_cancel₀ _ (by positivity)]
      rw [sum_union hdisj, hmul_div fun d hd => ⟨(mem_Icc.mp (G.hS_sub hd)).1, G.hS_dvd d hd⟩,
        Nat.cast_add, Nat.cast_mul, hTQ, Nat.cast_mul, Nat.cast_mul]
      linear_combination (q : ℚ) * G.heta }
@[category API, AMS 11] lemma binGadget (R : ℕ) (hR : 3 ≤ R) :
    ∃ G : Gadget, G.M = 2 * R ^ 2 ∧
      G.D = 2 ^ (1 + Nat.log 2 R) * ∏ p ∈ (Icc 3 R).filter Nat.Prime, p ∧ G.D ≤ G.B - G.A ∧ G.eta ≤ 1 := by
  let t := Nat.log 2 R
  let M := 2 * R ^ 2
  have ht : 1 ≤ t := Nat.le_log_of_pow_le (by decide) (by omega : 2 ^ 1 ≤ R)
  have hMp : 2 ^ (1 + t) ≤ M := by
    dsimp [M, t]
    have := Nat.pow_log_le_self 2 (by omega : R ≠ 0)
    rw [pow_add, pow_one]
    nlinarith
  have hop_card {r} (hr : r < 2 ^ (t + 1)) : ((Icc 3 r).filter Nat.Prime).card ≤ 2 ^ t - 1 := by
    let g p := (p - 1) / 2
    have hinj : Set.InjOn g ((Icc 3 r).filter Nat.Prime) := fun a ha b hb hab => by
      simp only [Finset.mem_coe, mem_filter, mem_Icc] at ha hb
      have := ha.2.eq_two_or_odd.resolve_left (by omega)
      have := hb.2.eq_two_or_odd.resolve_left (by omega)
      dsimp [g] at hab
      omega
    have hsub : ((Icc 3 r).filter Nat.Prime).image g ⊆ Icc 1 (2 ^ t - 1) := fun _ hy => by
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
      simp only [mem_filter, mem_Icc] at hp
      have : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
      have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
      exact mem_Icc.mpr ⟨by dsimp [g]
                            omega, by dsimp [g]
                                      omega⟩
    simpa [card_image_of_injOn hinj] using card_le_card hsub
  have hbin_add {P A : ℕ} {eta : ℚ} (hA : (A : ℚ) = eta * (2 ^ (1 + t) * P : ℕ))
      (heta : eta ≤ ((2 ^ t - 1 : ℕ) : ℚ) * (1 / (2 : ℚ) ^ t)) : 2 ^ (1 + t) * P + A ≤ (2 ^ (2 + t) - 1) * P := by
    have h2t : (0 : ℚ) < (2 : ℚ) ^ t := by positivity
    have he2 : eta * (2 : ℚ) ^ t ≤ (2 : ℚ) ^ t - 1 := by
      have h1 := mul_le_mul_of_nonneg_right heta h2t.le
      rwa [mul_assoc, one_div_mul_cancel h2t.ne', mul_one, Nat.cast_sub Nat.one_le_two_pow,
        Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h1
    suffices hQ : ((2 ^ (1 + t) * P + A : ℕ) : ℚ) ≤ ((2 ^ (2 + t) - 1) * P : ℕ) from mod_cast hQ
    rw [Nat.cast_add, hA, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    have hpow2 : (2 : ℚ) ^ (1 + t) + eta * (2 : ℚ) ^ (1 + t) ≤ (2 : ℚ) ^ (2 + t) - 1 := by
      rw [show (2 : ℚ) ^ (1 + t) = 2 * (2 : ℚ) ^ t by ring, show (2 : ℚ) ^ (2 + t) = 4 * (2 : ℚ) ^ t by ring]
      linarith
    nlinarith [Nat.cast_nonneg (α := ℚ) P]
  have aux : ∀ r < 2 ^ (t + 1), r * 2 ^ (1 + t) ≤ M → ∃ G : Gadget, G.M = M ∧
      G.D = 2 ^ (1 + t) * ∏ p ∈ (Icc 3 r).filter Nat.Prime, p ∧
      G.B = (2 ^ (2 + t) - 1) * ∏ p ∈ (Icc 3 r).filter Nat.Prime, p ∧
      (G.A : ℚ) = G.eta * G.D ∧ G.eta ≤ ((Icc 3 r).filter Nat.Prime).card * (1 / (2 : ℚ) ^ t) := by
    intro r
    induction r with
    | zero =>
      refine fun _ _ => ⟨{
        M := M, D := 2 ^ (1 + t), S := (range (2 + t)).image (fun i => 2 ^ (1 + t - i)),
        A := 0, B := 2 ^ (2 + t) - 1, eta := 0, hD_pos := Nat.two_pow_pos _, hA_le_B := Nat.zero_le _,
        hS_sub := fun _ hx => by
          obtain ⟨i, _, rfl⟩ := mem_image.mp hx
          exact mem_Icc.mpr ⟨Nat.one_le_two_pow, (Nat.pow_le_pow_right (by decide) (by omega)).trans hMp⟩,
        hS_dvd := fun _ hx => by
          obtain ⟨i, _, rfl⟩ := mem_image.mp hx
          exact Nat.pow_dvd_pow 2 (by omega),
        hD_smooth := fun p hp hd => by
          obtain rfl : p = 2 := le_antisymm (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow hd)) hp.two_le
          exact ((by decide : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))).trans hMp,
        hcov := fun u _ huB => by
          have : 1 ≤ 2 ^ (2 + t) := Nat.one_le_two_pow
          obtain ⟨U₀, hU₀, hs⟩ := sub_two_pow (2 + t) u (by omega)
          exact ⟨U₀.image (fun i => 2 ^ (1 + t - i)), image_subset_image hU₀,
            by simpa [hs] using (img_two_pow (s := 1 + t) (k := 2 + t) zero_lt_one (by omega) hU₀).1⟩,
        heta := by
          have hs := Nat.geomSum_eq (by decide : 2 ≤ 2) (2 + t)
          have htot : ∑ x ∈ (range (2 + t)).image (fun i => 2 ^ (1 + t - i)), 2 ^ (1 + t) / x = 2 ^ (2 + t) - 1 := by
            simpa [hs] using (img_two_pow (s := 1 + t) (k := 2 + t) zero_lt_one (by omega) Subset.rfl).1
          rw [htot]
          ring }, rfl, by simp, by simp, by simp, by simp⟩
    | succ r ih =>
      intro hr hrM
      obtain ⟨G, hGM, hGD, hGB, hGA, hGe⟩ := ih (by omega) ((Nat.mul_le_mul_right _ r.le_succ).trans hrM)
      by_cases hcond : 3 ≤ r + 1 ∧ (r + 1).Prime
      · obtain ⟨hr3, hpr⟩ := hcond
        set q := r + 1
        set kq := Nat.log 2 q + 1
        have hkq : kq ≤ 1 + t := by
          have := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hr
          omega
        let f i := q * 2 ^ (1 + t - i)
        let Tq := (range kq).image f
        set Po := ∏ p ∈ (Icc 3 r).filter Nat.Prime, p
        have hqP : ¬ q ∣ Po := fun hd => by
          obtain ⟨p, hp, hqp⟩ := hpr.prime.exists_mem_finset_dvd hd
          simp only [mem_filter, mem_Icc] at hp
          have := Nat.le_of_dvd (by omega) hqp
          omega
        have hqD : ¬ q ∣ G.D := hGD ▸ fun hd => (hpr.dvd_mul.mp hd).elim
          (fun h => by
            have := Nat.le_of_dvd (by decide) (hpr.dvd_of_dvd_pow h)
            omega) hqP
        have hTq : ∀ m ∈ Tq, 1 ≤ m ∧ m ≤ M ∧ m ∣ G.D * q ∧ ¬ m ∣ G.D := fun m hm => by
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
          have := mem_range.mp hi
          refine ⟨Nat.mul_pos (by omega) (Nat.two_pow_pos _),
            (Nat.mul_le_mul_left q (Nat.pow_le_pow_right (by decide) (by omega))).trans hrM,
            ⟨Po * 2 ^ i, ?_⟩, fun h0 => hqD (dvd_trans ⟨2 ^ (1 + t - i), rfl⟩ h0)⟩
          have hp2 : 2 ^ (1 + t) = 2 ^ (1 + t - i) * 2 ^ i := by
            rw [← pow_add]
            congr 1
            omega
          rw [hGD, hp2]
          ring
        have hrch : ∀ j < q, ∃ U ⊆ Tq, (∑ m ∈ U, (G.D * q) / m) % q = j := fun j hj => by
          have : NeZero q := ⟨by omega⟩
          let uP := ZMod.unitOfCoprime Po (hpr.coprime_iff_not_dvd.mpr hqP).symm
          set v := (↑uP⁻¹ * (j : ZMod q)).val
          have hv : v < q := ZMod.val_lt _
          have hvm : (Po * v) % q = j := by
            rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← mul_assoc,
              show (Po : ZMod q) * ↑uP⁻¹ = 1 from Units.mul_inv uP, one_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hj]
          obtain ⟨U₀, hU₀, hs₀⟩ := sub_two_pow kq v (hv.trans (Nat.lt_pow_succ_log_self (by decide) q))
          refine ⟨U₀.image f, image_subset_image hU₀, ?_⟩
          have hmul : ∑ m ∈ U₀.image f, (q * 2 ^ (1 + t) * Po) / m = Po * ∑ m ∈ U₀.image f, (q * 2 ^ (1 + t)) / m := by
            rw [mul_sum]
            refine sum_congr rfl fun m hm => ?_
            obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
            have := mem_range.mp (hU₀ hi)
            obtain ⟨c', hc'⟩ : f i ∣ q * 2 ^ (1 + t) := Nat.mul_dvd_mul_left q (Nat.pow_dvd_pow 2 (by omega))
            have hf0 : 0 < f i := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
            rw [hc', show f i * c' * Po = f i * (Po * c') by ring, Nat.mul_div_cancel_left _ hf0, Nat.mul_div_cancel_left _ hf0]
          have hGDq : G.D * q = q * 2 ^ (1 + t) * Po := by
            rw [hGD]
            ring
          rw [hGDq, hmul, (img_two_pow (c := q) (s := 1 + t) (by omega) (by omega) hU₀).1, hs₀, hvm]
        have hI : (Icc 3 q).filter Nat.Prime = insert q ((Icc 3 r).filter Nat.Prime) := by
          have hIcc : Icc 3 q = insert q (Icc 3 r) := by
            ext
            simp only [mem_Icc, mem_insert]
            omega
          rw [hIcc, filter_insert, if_pos hpr]
        have hqn : q ∉ (Icc 3 r).filter Nat.Prime := by
          simp only [mem_filter, mem_Icc, not_and]
          omega
        have hDn : G.D * q = 2 ^ (1 + t) * ∏ p ∈ (Icc 3 q).filter Nat.Prime, p := by
          rw [hI, prod_insert hqn, hGD]
          ring
        have hBn : q * G.B = (2 ^ (2 + t) - 1) * ∏ p ∈ (Icc 3 q).filter Nat.Prime, p := by
          rw [hI, prod_insert hqn, hGB]
          ring
        have hsu : ∑ m ∈ Tq, (1 : ℚ) / m ≤ 1 / (2 : ℚ) ^ t := by
          have hs := Nat.geomSum_eq (by decide : 2 ≤ 2) kq
          simp only [Nat.reduceSub, Nat.div_one] at hs
          rw [(img_two_pow (by omega) (by omega) Subset.rfl).2, hs,
            Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_le_div_iff₀ (by positivity) (by positivity)]
          have h2q : 2 ^ kq - 1 ≤ 2 * q := by
            have := Nat.pow_log_le_self 2 (by omega : q ≠ 0)
            dsimp [kq]
            rw [pow_succ']
            omega
          have h2qQ : ((2 ^ kq - 1 : ℕ) : ℚ) ≤ 2 * q := mod_cast h2q
          rw [show (2 : ℚ) ^ (1 + t) = 2 * (2 : ℚ) ^ t by ring]
          nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) t]
        have hen : G.eta + ∑ m ∈ Tq, (1 : ℚ) / m ≤ (((Icc 3 q).filter Nat.Prime).card : ℚ) * (1 / (2 : ℚ) ^ t) := by
          rw [hI, card_insert_of_notMem hqn, Nat.cast_add, Nat.cast_one]
          linarith
        have hDq : 0 < G.D * q := Nat.mul_pos G.hD_pos (by omega)
        have hAn : ((q * G.A + ∑ m ∈ Tq, (G.D * q) / m : ℕ) : ℚ) = (G.eta + ∑ m ∈ Tq, (1 : ℚ) / m) * (G.D * q : ℕ) := by
          rw [Nat.cast_add, Nat.cast_mul, hGA, inv_dvd hDq (fun m hm => ⟨(hTq m hm).1, (hTq m hm).2.2.1⟩),
            add_mul, div_mul_cancel₀ _ (by positivity), Nat.cast_mul]
          ring
        have hcard_le : (((Icc 3 q).filter Nat.Prime).card : ℚ) ≤ (2 ^ t - 1 : ℕ) := mod_cast hop_card hr
        have hDAn := hbin_add (hDn ▸ hAn) (hen.trans (by gcongr))
        rw [← hDn, ← hBn] at hDAn
        exact ⟨extendG G (by omega) ((Nat.le_mul_of_pos_right q (Nat.two_pow_pos _)).trans hrM) hGM hTq hrch (by omega),
          rfl, hDn, hBn, by simpa [extendG, one_div] using hAn, by simpa [extendG, one_div] using hen⟩
      · have hI : (Icc 3 (r + 1)).filter Nat.Prime = (Icc 3 r).filter Nat.Prime := by
          ext x
          simp only [mem_filter, mem_Icc, and_congr_left_iff]
          intro hp
          exact ⟨fun ⟨h1, _⟩ => ⟨h1, by
              by_contra!
              exact hcond ⟨by omega, by rwa [show r + 1 = x by omega]⟩⟩,
            fun ⟨h1, _⟩ => ⟨h1, by omega⟩⟩
        exact ⟨G, hGM, hI ▸ hGD, hI ▸ hGB, hGA, hI ▸ hGe⟩
  have h2R : 2 ^ (1 + t) ≤ 2 * R := by
    dsimp [t]
    have := Nat.pow_log_le_self 2 (by omega : R ≠ 0)
    rw [pow_add, pow_one]
    omega
  have hRM : R * 2 ^ (1 + t) ≤ M := by
    dsimp [M]
    nlinarith
  obtain ⟨G, hGM, hGD, hGB, hGA, hGe⟩ := aux R (Nat.lt_pow_succ_log_self (by decide) R) hRM
  have hcardR : (((Icc 3 R).filter Nat.Prime).card : ℚ) ≤ (2 ^ t - 1 : ℕ) :=
    mod_cast hop_card (Nat.lt_pow_succ_log_self (by decide) R)
  have hel : G.eta ≤ ((2 ^ t - 1 : ℕ) : ℚ) * (1 / (2 : ℚ) ^ t) := hGe.trans (by gcongr)
  have hDA := hbin_add (A := G.A) (hGD ▸ hGA) hel
  rw [← hGD, ← hGB] at hDA
  refine ⟨G, hGM, hGD, by omega, hel.trans ?_⟩
  rw [mul_one_div, div_le_iff₀ (by positivity), Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  linarith
@[category API, AMS 11] lemma sub_fac_le (q₁ q₂ : ℚ) (p : ℕ) :
    (q₁ - q₂).den.factorization p ≤ max (q₁.den.factorization p) (q₂.den.factorization p) := by
  have hadd (a b : ℚ) : (a + b).den.factorization p ≤ max (a.den.factorization p) (b.den.factorization p) := by
    simpa [Nat.factorization_lcm a.den_ne_zero b.den_ne_zero] using
      (Nat.factorization_le_iff_dvd (a + b).den_ne_zero
        (Nat.lcm_ne_zero a.den_ne_zero b.den_ne_zero)).mpr (Rat.add_den_dvd_lcm a b) p
  simpa [sub_eq_add_neg] using hadd q₁ (-q₂)
@[category API, AMS 11] lemma den_fac_le {S : Finset ℕ} (hpos : ∀ x ∈ S, 0 < x)
    (p c : ℕ) (h : ∀ x ∈ S, x.factorization p ≤ c) :
    (∑ x ∈ S, (1 : ℚ) / x).den.factorization p ≤ c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, ← sub_neg_eq_add]
    refine (sub_fac_le _ _ p).trans (max_le ?_ ?_)
    · rw [one_div, Rat.inv_natCast_den_of_pos (hpos a (mem_insert_self a s))]
      exact h a (mem_insert_self a s)
    · simpa using ih (fun x hx => hpos x (mem_insert_of_mem hx)) fun x hx => h x (mem_insert_of_mem hx)
@[category API, AMS 11] lemma cancel_step {q a K A₀ B₀ : ℕ} {X B_set : Finset ℕ}
    (hq : q.Prime) (ha : 1 ≤ a) (hK_pos : 0 < K) (hqK : ¬ q ∣ K) (hX_pos : ∀ x ∈ X, 0 < x)
    (hB_sub : B_set ⊆ X) (hB_val : ∀ x ∈ B_set, x.factorization q ≤ a)
    (hcur_q : (∑ x ∈ X, (1 : ℚ) / x).den.factorization q ≤ a) (hcap : A₀ + q ≤ B₀ + 1)
    (hcov : ∀ t, A₀ ≤ t → t ≤ B₀ → ∃ U ⊆ B_set, ∑ x ∈ U, (1 : ℚ) / x = (t : ℚ) / (q ^ a * K : ℕ)) :
    ∃ X' ⊆ X, X \ B_set ⊆ X' ∧ (∑ x ∈ X', (1 : ℚ) / x).den.factorization q ≤ a - 1 ∧
      (∀ p, (∀ x ∈ B_set, ¬ p ∣ x) →
        (∑ x ∈ X', (1 : ℚ) / x).den.factorization p ≤ (∑ x ∈ X, (1 : ℚ) / x).den.factorization p) ∧
      (∑ x ∈ X, (1 : ℚ) / x) - (∑ x ∈ X', (1 : ℚ) / x) ≤
        (∑ x ∈ B_set, (1 : ℚ) / x) - ((B₀ + 1 - q : ℕ) : ℚ) / (q ^ a * K : ℕ) := by
  classical
  have hq_pos := hq.pos
  let R_rest : ℚ := ∑ x ∈ X \ B_set, (1 : ℚ) / x
  have hsplit_X : ∑ x ∈ X, (1 : ℚ) / x = R_rest + ∑ x ∈ B_set, (1 : ℚ) / x := (sum_sdiff hB_sub).symm
  have hB_pos : ∀ x ∈ B_set, 0 < x := fun x hx => hX_pos x (hB_sub hx)
  have hR_q : R_rest.den.factorization q ≤ a := by
    rw [show R_rest = (∑ x ∈ X, (1 : ℚ) / x) - ∑ x ∈ B_set, (1 : ℚ) / x by linarith]
    exact (sub_fac_le _ _ q).trans (max_le hcur_q (den_fac_le hB_pos q a hB_val))
  set e := R_rest.den.factorization q
  let m := R_rest.den / q ^ e
  have hm_mul : q ^ e * m = R_rest.den := Nat.mul_div_cancel' (Nat.ordProj_dvd R_rest.den q)
  have hm_pos : 0 < m := Nat.pos_of_ne_zero fun h0 => R_rest.den_pos.ne' (hm_mul ▸ by simp [h0])
  have hqm : ¬ q ∣ m := Nat.not_dvd_ordCompl hq R_rest.den_pos.ne'
  let u : ℤ := R_rest.num * (q ^ (a - e) : ℤ)
  have hR_div : R_rest = (u : ℚ) / (q ^ a * m : ℕ) := by
    conv_lhs => rw [← Rat.num_div_den R_rest]
    have hpow_add : q ^ e * m * q ^ (a - e) = q ^ (e + (a - e)) * m := by
      rw [pow_add]
      ring
    have hqam : q ^ a * m = R_rest.den * q ^ (a - e) := by
      rw [← hm_mul, hpow_add, Nat.add_sub_of_le hR_q]
    rw [hqam]
    push_cast [u]
    rw [mul_div_mul_right _ _ (by positivity)]
  let base := B₀ + 1 - q
  have : NeZero q := ⟨hq.ne_zero⟩
  let um := ZMod.unitOfCoprime m (hq.coprime_iff_not_dvd.mpr hqm).symm
  let z : ZMod q := ↑um⁻¹ * (-(u * K + m * base) : ℤ)
  let δ := z.val
  have hδ_lt : δ < q := ZMod.val_lt z
  let t := base + δ
  obtain ⟨w, hw⟩ : (q : ℤ) ∣ u * K + m * t := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_
    dsimp [t, δ]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_add]
    dsimp only [z]
    rw [← mul_assoc, show (m : ZMod q) * ↑um⁻¹ = 1 from Units.mul_inv um, one_mul]
    push_cast
    ring
  obtain ⟨U, hU_sub, hU_sum⟩ := hcov t (by omega) (by omega)
  let X' := (X \ B_set) ∪ U
  have hdisj_XU : Disjoint (X \ B_set) U := Disjoint.mono_right hU_sub sdiff_disjoint
  refine ⟨X', union_subset sdiff_subset (hU_sub.trans hB_sub), subset_union_left, ?_, ?_, ?_⟩
  · have hsum_X' : ∑ x ∈ X', (1 : ℚ) / x = (w : ℚ) / (q ^ (a - 1) * m * K : ℕ) := by
      have hqa_split : q ^ a = q * q ^ (a - 1) := by
        conv_lhs => rw [show a = 1 + (a - 1) by omega, pow_add, pow_one]
      rw [sum_union hdisj_XU, show ∑ x ∈ X \ B_set, (1 : ℚ) / x = R_rest from rfl, hR_div, hU_sum, hqa_split]
      have hwQ : (u : ℚ) * K + m * t = q * w := mod_cast hw
      push_cast
      field_simp
      linarith
    have hb0 : q ^ (a - 1) * m * K ≠ 0 := by positivity
    have hle_den : (∑ x ∈ X', (1 : ℚ) / x).den.factorization q ≤ (q ^ (a - 1) * m * K).factorization q :=
      (Nat.factorization_le_iff_dvd (∑ x ∈ X', (1 : ℚ) / x).den_pos.ne' hb0).mpr
        (hsum_X' ▸ Int.natCast_dvd_natCast.mp (by simpa [Rat.divInt_eq_div] using Rat.den_dvd w (q ^ (a - 1) * m * K))) q
    rw [Nat.factorization_mul (by positivity) hK_pos.ne', Nat.factorization_mul (by positivity) hm_pos.ne',
      Finsupp.add_apply, Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hqm, Nat.factorization_eq_zero_of_not_dvd hqK] at hle_den
    omega
  · intro p hpB
    have hdiff_X' : ∑ x ∈ X', (1 : ℚ) / x = (∑ x ∈ X, (1 : ℚ) / x) - ∑ x ∈ B_set \ U, (1 : ℚ) / x := by
      rw [sum_union hdisj_XU, hsplit_X, ← sum_sdiff hU_sub]
      ring
    rw [hdiff_X']
    exact (sub_fac_le _ _ p).trans (max_le le_rfl
      ((den_fac_le (fun x hx => hB_pos x (sdiff_subset hx)) p 0 fun x hx =>
        Nat.le_zero.mpr (Nat.factorization_eq_zero_of_not_dvd (hpB x (sdiff_subset hx)))).trans (Nat.zero_le _)))
  · rw [sum_union hdisj_XU, hsplit_X, show ∑ x ∈ X \ B_set, (1 : ℚ) / x = R_rest from rfl, hU_sum]
    have hbt : (base : ℚ) / (q ^ a * K) ≤ (t : ℚ) / (q ^ a * K) := by
      gcongr
      exact Nat.le_add_right base δ
    push_cast at hbt ⊢
    linarith
def tgtExp (p : ℕ) : ℕ := if p = 2 then 8 else if p = 3 then 2 else if p = 5 then 1 else 0
def lossTail (M_top n : ℕ) : ℚ := ∑ p ∈ (Ioc (n / M_top) n).filter Nat.Prime, harmonic (n / p) / p
def lossSq (M_bot n : ℕ) : ℚ :=
  ∑ p ∈ (Ioc M_bot n).filter (fun p => p.Prime ∧ p * p ≤ n), harmonic (n / (p * p)) / (p * p : ℕ)
def peelTerm (M_bot n : ℕ) (pickG : ℕ → Gadget) (p : ℕ) : ℚ :=
  let G := pickG p
  (G.eta + ((p - 1 : ℕ) : ℚ) / G.D) / (p * min M_bot (n / (p * G.M)) : ℕ)
def lossPeel (M_top M_bot n : ℕ) (pickG : ℕ → Gadget) : ℚ :=
  ∑ p ∈ (Ioc M_bot (n / M_top)).filter Nat.Prime, peelTerm M_bot n pickG p
def qaOdd (n q a : ℕ) : ℚ :=
  let kq := Nat.log 2 q + 1
  if q ^ a * 2 ^ (kq - 1) ≤ n then ((2 ^ kq - 1 : ℕ) : ℚ) / (q ^ a * 2 ^ Nat.log 2 (n / q ^ a) : ℕ)
  else harmonic (n / q ^ a) / (q ^ a : ℕ)
def lossQA (M_bot n : ℕ) : ℚ := (∑ a ∈ Icc 9 (Nat.log 2 n), (1 : ℚ) / (2 ^ a : ℕ)) +
  ∑ q ∈ (Icc 3 M_bot).filter Nat.Prime, ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), qaOdd n q a
def qaTerm (n q a : ℕ) : ℚ := if q = 2 then (1 : ℚ) / (2 ^ a : ℕ) else qaOdd n q a
@[category API, AMS 11] lemma inv_flt_dvd (n d : ℕ) (hd : 0 < d) :
    ∑ x ∈ (Icc 1 n).filter (d ∣ ·), (1 : ℚ) / x = harmonic (n / d) / d := by
  have himg : (Icc 1 n).filter (d ∣ ·) = (Icc 1 (n / d)).image (d * ·) := by
    ext x
    simp only [mem_filter, mem_Icc, mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨hx1, hxn⟩, m, rfl⟩
      refine ⟨m, ⟨?_, (Nat.mul_div_cancel_left m hd) ▸ Nat.div_le_div_right hxn⟩, rfl⟩
      rcases m with _ | m
      · simp at hx1
      · omega
    · rintro ⟨m, ⟨hm1, hmn⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hd hm1, (Nat.mul_le_mul_left d hmn).trans (Nat.mul_div_le n d)⟩, dvd_mul_right d m⟩
  rw [himg, sum_image fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hd h, harmonic_eq_sum_Icc, sum_div]
  refine sum_congr rfl fun _ _ => ?_
  push_cast
  rw [one_div, mul_inv_rev, div_eq_mul_inv]
@[category API, AMS 11] lemma descend_sieve {lo hi : ℕ} {X₀ : Finset ℕ} {Inv : ℕ → Finset ℕ → Prop}
    {cost : ℕ → ℚ} (hlo : lo ≤ hi) (h₀ : Inv hi X₀)
    (hstep : ∀ m, lo ≤ m → m < hi → ∀ X ⊆ X₀, Inv (m + 1) X →
      ∃ X' ⊆ X, Inv m X' ∧ (∑ x ∈ X, (1 : ℚ) / x) - (∑ x ∈ X', (1 : ℚ) / x) ≤ cost (m + 1)) :
    ∃ X ⊆ X₀, Inv lo X ∧ (∑ x ∈ X₀, (1 : ℚ) / x) - (∑ x ∈ X, (1 : ℚ) / x) ≤ ∑ k ∈ Ioc lo hi, cost k := by
  suffices ∀ d ≤ hi - lo, ∃ X ⊆ X₀, Inv (hi - d) X ∧
      (∑ x ∈ X₀, (1 : ℚ) / x) - (∑ x ∈ X, (1 : ℚ) / x) ≤ ∑ k ∈ Ioc (hi - d) hi, cost k by
    simpa [Nat.sub_sub_self hlo] using this (hi - lo) le_rfl
  intro d
  induction d with
  | zero => exact fun _ => ⟨X₀, Subset.rfl, h₀, by simp⟩
  | succ d ih =>
    intro hd
    obtain ⟨X, hX, hInv, hLoss⟩ := ih (Nat.le_of_succ_le hd)
    set m := hi - (d + 1)
    have hm_succ : hi - d = m + 1 := by omega
    obtain ⟨X', hX', hInv', hStep⟩ := hstep m (by omega) (by omega) X hX (hm_succ ▸ hInv)
    refine ⟨X', hX'.trans hX, hInv', ?_⟩
    rw [hm_succ] at hLoss
    have hI : Ioc m hi = insert (m + 1) (Ioc (m + 1) hi) := by
      ext
      simp only [mem_Ioc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]
    linarith
@[category API, AMS 11] lemma peelPrime {n M_bot q : ℕ} {X₀ : Finset ℕ} (hn : 11520 ≤ n)
    (hq_prime : q.Prime) (hqM : q ≤ M_bot) (hX₀_sub : X₀ ⊆ Icc 1 n)
    (hSurv₀ : ∀ x ∈ Icc 1 n, (∀ r, r.Prime → M_bot < r → ¬ r ∣ x) →
      (∀ r, r.Prime → q < r → ¬ r ^ (tgtExp r + 1) ∣ x) → x ∈ X₀)
    (hHigh₀ : ∀ r, r.Prime → q < r → (∑ x ∈ X₀, (1 : ℚ) / x).den.factorization r ≤ tgtExp r) :
    ∃ X' ⊆ X₀, (∀ x ∈ Icc 1 n, (∀ r, r.Prime → M_bot < r → ¬ r ∣ x) →
        (∀ r, r.Prime → q - 1 < r → ¬ r ^ (tgtExp r + 1) ∣ x) → x ∈ X') ∧
      (∀ r, r.Prime → q - 1 < r → (∑ x ∈ X', (1 : ℚ) / x).den.factorization r ≤ tgtExp r) ∧
      (∑ x ∈ X₀, (1 : ℚ) / x) - (∑ x ∈ X', (1 : ℚ) / x) ≤ ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), qaTerm n q a := by
  classical
  have hfac_le {p k x : ℕ} (hndvd : ¬ p ^ (k + 1) ∣ x) : x.factorization p ≤ k := by
    by_contra hlt
    exact hndvd ((Nat.pow_dvd_pow p (by omega : k + 1 ≤ _)).trans (Nat.ordProj_dvd x p))
  have hnd_lt {p x : ℕ} (hx : 0 < x) (hlt : x < p) : ¬ p ∣ x := fun hd => absurd (Nat.le_of_dvd hx hd) (by omega)
  have hq2_le := hq_prime.two_le
  have hX₀_pos : ∀ x ∈ X₀, 0 < x := fun x hx => (mem_Icc.mp (hX₀_sub hx)).1
  have hpnd {r a b j k : ℕ} (hr : r.Prime) (ha0 : 0 < a) (hb0 : 0 < b) (hra : a < r) (hrb : b < r) :
      ¬ r ∣ a ^ j * b ^ k := fun hd => (hr.dvd_mul.mp hd).elim
    (fun h => hnd_lt ha0 hra (hr.dvd_of_dvd_pow h)) fun h => hnd_lt hb0 hrb (hr.dvd_of_dvd_pow h)
  set Lq := Nat.log q n
  set eq := tgtExp q
  set hi := max eq Lq
  have hcur_Lq : (∑ x ∈ X₀, (1 : ℚ) / x).den.factorization q ≤ hi :=
    (den_fac_le hX₀_pos q Lq fun x hx => hfac_le fun hd => by
      have ⟨h1, _⟩ := mem_Icc.mp (hX₀_sub hx)
      have : n < q ^ (Lq + 1) := Nat.lt_pow_succ_log_self hq_prime.one_lt n
      have := Nat.le_of_dvd h1 hd
      omega).trans (le_max_right _ _)
  let Inv (m : ℕ) (X : Finset ℕ) : Prop :=
    (∀ x ∈ Icc 1 n, (∀ r, r.Prime → M_bot < r → ¬ r ∣ x) →
      (∀ r, r.Prime → q < r → ¬ r ^ (tgtExp r + 1) ∣ x) → ¬ q ^ (m + 1) ∣ x → x ∈ X) ∧
    (∑ x ∈ X, (1 : ℚ) / x).den.factorization q ≤ m ∧
    (∀ r, r.Prime → q < r → (∑ x ∈ X, (1 : ℚ) / x).den.factorization r ≤ tgtExp r)
  obtain ⟨Xf, hXf_sub, ⟨hSurv_f, hValQ_f, hHigh_f⟩, hLoss_f⟩ :=
    descend_sieve (Inv := Inv) (cost := qaTerm n q) (le_max_left eq Lq)
      ⟨fun x hx hsm hhi _ => hSurv₀ x hx hsm hhi, hcur_Lq, hHigh₀⟩
      fun m _ hm_lt X hX_sub ⟨hSurv, hValQ, hHigh⟩ => by
        set a := m + 1
        have hqa_pos : 0 < q ^ a := pow_pos hq_prime.pos a
        have hX_Icc : X ⊆ Icc 1 n := hX_sub.trans hX₀_sub
        have hX_pos : ∀ x ∈ X, 0 < x := fun x hx => (mem_Icc.mp (hX_Icc hx)).1
        let kq := if q = 2 then 1 else Nat.log 2 q + 1
        by_cases hC1 : q ^ a * 2 ^ (kq - 1) ≤ n
        · let s := if q = 2 then 0 else Nat.log 2 (n / q ^ a)
          have hkq_s : kq - 1 ≤ s := by
            dsimp [kq, s]
            split_ifs with h2
            · omega
            · exact Nat.le_log_of_pow_le (by decide) ((Nat.mul_div_cancel_left (2 ^ _) hqa_pos).symm ▸
                Nat.div_le_div_right (by simpa [kq, h2] using hC1))
          have hs_n : q ^ a * 2 ^ s ≤ n := by
            dsimp [s]
            split_ifs with h2
            · simpa [kq, h2] using hC1
            · have hC1' : q ^ a * 2 ^ Nat.log 2 q ≤ n := by simpa [kq, h2] using hC1
              exact (Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2
                (Nat.div_pos (le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hC1') hqa_pos).ne')).trans (Nat.mul_div_le n _)
          let f i := q ^ a * 2 ^ (s - i)
          let B_set := (range kq).image f
          have hq_not_2 (j) (hj : j ≤ s) : ¬ q ∣ 2 ^ j := fun hd => by
            by_cases h2 : q = 2
            · subst h2
              simp [s] at hj
              simp [hj] at hd
            · exact absurd (Nat.le_of_dvd (by decide) (hq_prime.dvd_of_dvd_pow hd)) (by omega)
          have hB_sub : B_set ⊆ X := fun x hx => by
            obtain ⟨i, hi', rfl⟩ := mem_image.mp hx
            have := mem_range.mp hi'
            refine hSurv (f i) (mem_Icc.mpr ⟨Nat.mul_pos hqa_pos (Nat.two_pow_pos _),
              (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))).trans hs_n⟩)
              (fun r hr hMr => hpnd hr hq_prime.pos (by decide) (by omega) (by omega))
              (fun r hr hqr hd => hpnd hr hq_prime.pos (by decide) hqr (by omega) ((dvd_pow_self r (by omega)).trans hd))
              fun hd => ?_
            have hcop := (hq_prime.coprime_iff_not_dvd.mpr (hq_not_2 (s - i) (by omega))).pow (a + 1) 1
            have := Nat.le_of_dvd hqa_pos (hcop.dvd_of_dvd_mul_right (by simpa using hd))
            have := Nat.pow_lt_pow_right hq_prime.one_lt (lt_add_one a)
            omega
          have hB_val_q : ∀ x ∈ B_set, x.factorization q ≤ a := fun x hx => by
            obtain ⟨i, _, rfl⟩ := mem_image.mp hx
            dsimp only [f]
            rw [Nat.factorization_mul hqa_pos.ne' (Nat.two_pow_pos _).ne', Finsupp.add_apply,
              hq_prime.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (hq_not_2 _ (by omega))]
          have hq_le_2kq : q ≤ 2 ^ kq := by
            dsimp [kq]
            split_ifs with h2
            · omega
            · exact (Nat.lt_pow_succ_log_self (by decide) q).le
          obtain ⟨X', hX'_sub, hkeep, hValQ', hOther', hStepLoss⟩ :=
            cancel_step (A₀ := 0) (B₀ := 2 ^ kq - 1) hq_prime m.succ_pos
              (Nat.two_pow_pos s) (hq_not_2 s le_rfl) hX_pos hB_sub hB_val_q hValQ
              (by have := Nat.one_le_two_pow (n := kq)
                  omega) fun t _ htB => by
                obtain ⟨U₀, hU₀, hsum₀⟩ := sub_two_pow kq t
                  (by have := Nat.one_le_two_pow (n := kq)
                      omega)
                exact ⟨U₀.image f, image_subset_image hU₀, by rw [(img_two_pow hqa_pos (by omega) hU₀).2, hsum₀]⟩
          refine ⟨X', hX'_sub, ⟨fun x hx hsm hhi hndvd => hkeep (mem_sdiff.mpr
            ⟨hSurv x hx hsm hhi fun h1 => hndvd ((Nat.pow_dvd_pow q a.le_succ).trans h1),
             fun hxB => by
               obtain ⟨i, _, rfl⟩ := mem_image.mp hxB
               exact hndvd (dvd_mul_right _ _)⟩),
            hValQ', fun r hr hqr => (hOther' r fun x hx => by
              obtain ⟨i, _, rfl⟩ := mem_image.mp hx
              exact hpnd hr hq_prime.pos (by decide) hqr (by omega)).trans (hHigh r hr hqr)⟩, ?_⟩
          have hg := Nat.geomSum_eq (by decide : 2 ≤ 2) kq
          simp only [Nat.reduceSub, Nat.div_one] at hg
          rw [(img_two_pow hqa_pos (by omega) Subset.rfl).2, hg] at hStepLoss
          have hterm : ((2 ^ kq - 1 : ℕ) : ℚ) / (q ^ a * 2 ^ s : ℕ) = qaTerm n q a := by
            by_cases h2 : q = 2
            · subst h2
              simp [qaTerm, kq, s]
            · dsimp only [qaTerm, qaOdd, kq, s]
              rw [if_neg h2, if_neg h2, if_neg h2, if_pos (by simpa [kq, h2] using hC1)]
          linarith [hterm, show (0 : ℚ) ≤ ((2 ^ kq - 1 + 1 - q : ℕ) : ℚ) / (q ^ a * 2 ^ s : ℕ) by positivity]
        · have hq2 : q ≠ 2 := fun h2 => hC1 <| by
            subst h2
            dsimp [kq, hi, eq, Lq, tgtExp] at hm_lt ⊢
            have : 8 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by omega : 2 ^ 8 ≤ n)
            simpa using (Nat.pow_le_pow_right (by decide) (by omega : a ≤ Nat.log 2 n)).trans (Nat.pow_log_le_self 2 (by omega))
          let Del := X.filter (q ^ a ∣ ·)
          let X' := X.filter (¬ q ^ a ∣ ·)
          have hpart : ∑ x ∈ X, (1 : ℚ) / x = (∑ x ∈ X', (1 : ℚ) / x) + ∑ x ∈ Del, (1 : ℚ) / x := by
            rw [add_comm, sum_filter_add_sum_filter_not]
          refine ⟨X', filter_subset _ X, ⟨fun x hx hsm hhi hndvd => mem_filter.mpr
            ⟨hSurv x hx hsm hhi fun h1 => hndvd ((Nat.pow_dvd_pow q a.le_succ).trans h1), hndvd⟩,
            den_fac_le (fun x hx => hX_pos x (filter_subset _ X hx)) q m
              fun x hx => hfac_le (mem_filter.mp hx).2, fun r hr hqr => ?_⟩, ?_⟩
          · rw [show ∑ x ∈ X', (1 : ℚ) / x = (∑ x ∈ X, (1 : ℚ) / x) - ∑ x ∈ Del, (1 : ℚ) / x by linarith]
            refine (sub_fac_le _ _ r).trans (max_le (hHigh r hr hqr)
              ((den_fac_le (fun x hx => hX_pos x (filter_subset _ X hx)) r 0 fun x hx => ?_).trans (Nat.zero_le _)))
            obtain ⟨hxX, m', rfl⟩ := mem_filter.mp hx
            obtain ⟨hx1, hxn⟩ := mem_Icc.mp (hX_Icc hxX)
            have hm_pos : 0 < m' := by
              rcases m' with _ | m'
              · simp at hx1
              · omega
            have hm_lt' : m' < 2 ^ Nat.log 2 q := not_le.mp fun hge =>
              hC1 (by simpa [kq, hq2] using (Nat.mul_le_mul_left (q ^ a) hge).trans hxn)
            have : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
            exact Nat.le_zero.mpr (Nat.factorization_eq_zero_of_not_dvd fun hd =>
              (hr.dvd_mul.mp hd).elim (fun h => hnd_lt hq_prime.pos hqr (hr.dvd_of_dvd_pow h)) (hnd_lt hm_pos (by omega)))
          · dsimp only [qaTerm, qaOdd]
            rw [if_neg hq2, if_neg (by simpa [kq, hq2] using hC1), ← inv_flt_dvd n (q ^ a) hqa_pos]
            linarith [sum_le_sum_of_subset_of_nonneg (s := Del) (t := (Icc 1 n).filter (q ^ a ∣ ·))
              (fun x hx => let ⟨hxX, hd⟩ := mem_filter.mp hx
                           mem_filter.mpr ⟨hX_Icc hxX, hd⟩)
              fun x _ _ => (by positivity : (0 : ℚ) ≤ 1 / x)]
  have hIeq : Ioc eq hi = Icc (eq + 1) Lq := by
    ext
    simp only [hi, mem_Ioc, mem_Icc]
    omega
  exact ⟨Xf, hXf_sub, fun x hx hsm hhi =>
      hSurv_f x hx hsm (fun r hr hqr => hhi r hr (by omega)) (hhi q hq_prime (by omega)),
    fun r hr hqr => (eq_or_lt_of_le (show q ≤ r by omega)).elim (fun e => e ▸ hValQ_f) (hHigh_f r hr),
    hIeq ▸ hLoss_f⟩
@[category API, AMS 11] lemma rep_sieve {n k M_top M_bot : ℕ}
    (pickG : ℕ → Gadget) (hn : 11520 ≤ n) (_hk : 1 ≤ k)
    (hM_top : 12 ≤ M_top) (hM_le : M_top ≤ M_bot) (hprod_le : M_top * M_bot ≤ n) (hharm_lt : harmonic n < (k : ℚ) + 1)
    (hG_props : ∀ p, p.Prime → M_bot < p → p ≤ n / M_top →
      0 < (pickG p).M ∧ (pickG p).M ≤ M_bot ∧ p * (pickG p).M ≤ n ∧ (pickG p).A + p ≤ (pickG p).B + 1)
    (hloss_le : lossTail M_top n + lossSq M_bot n + lossPeel M_top M_bot n pickG + lossQA M_bot n ≤ harmonic n - (k : ℚ)) :
    IsRepresentable n k := by
  classical
  have hnd_lt {p x : ℕ} (hx : 0 < x) (hlt : x < p) : ¬ p ∣ x := fun hd => absurd (Nat.le_of_dvd hx hd) (by omega)
  let X₀ := Icc 1 n
  set a_tail := n / M_top
  have hM_bot_le_tail : M_bot ≤ a_tail := (Nat.mul_div_cancel_left M_bot (by omega : 0 < M_top)).symm ▸ Nat.div_le_div_right hprod_le
  let E_tail := ((Ioc a_tail n).filter Nat.Prime).biUnion fun p => X₀.filter (p ∣ ·)
  let E_sq := ((Ioc M_bot n).filter fun p => p.Prime ∧ p * p ≤ n).biUnion fun p => X₀.filter (p * p ∣ ·)
  let X_A := X₀ \ (E_tail ∪ E_sq)
  have hE_sub : E_tail ∪ E_sq ⊆ X₀ := union_subset
    (biUnion_subset.mpr fun _ _ => filter_subset _ X₀) (biUnion_subset.mpr fun _ _ => filter_subset _ X₀)
  have hsum_bi {s : Finset ℕ} (t : ℕ → Finset ℕ) : ∑ x ∈ s.biUnion t, (1 : ℚ) / x ≤ ∑ a ∈ s, ∑ x ∈ t a, (1 : ℚ) / x := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [biUnion_insert, sum_insert ha]
      linarith [sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := fun x => (1 : ℚ) / x),
        sum_nonneg (s := t a ∩ s.biUnion t) fun x _ => (by positivity : (0 : ℚ) ≤ (1 : ℚ) / x)]
  have hLoss_A : (∑ x ∈ X₀, (1 : ℚ) / x) - (∑ x ∈ X_A, (1 : ℚ) / x) ≤ lossTail M_top n + lossSq M_bot n := by
    have hs : ∑ x ∈ X_A, (1 : ℚ) / x + ∑ x ∈ E_tail ∪ E_sq, (1 : ℚ) / x = ∑ x ∈ X₀, (1 : ℚ) / x := sum_sdiff hE_sub
    have h2 : ∑ x ∈ E_tail, (1 : ℚ) / x ≤ lossTail M_top n :=
      (hsum_bi _).trans (sum_le_sum fun p hp => (inv_flt_dvd n p (mem_filter.mp hp).2.pos).le)
    have h3 : ∑ x ∈ E_sq, (1 : ℚ) / x ≤ lossSq M_bot n :=
      (hsum_bi _).trans (sum_le_sum fun p hp => (inv_flt_dvd n (p * p)
        (Nat.mul_pos (mem_filter.mp hp).2.1.pos (mem_filter.mp hp).2.1.pos)).le)
    linarith [sum_union_inter (s₁ := E_tail) (s₂ := E_sq) (f := fun x => (1 : ℚ) / x),
      sum_nonneg (s := E_tail ∩ E_sq) fun x _ => (by positivity : (0 : ℚ) ≤ (1 : ℚ) / x)]
  have mem_XA {x} : x ∈ X_A ↔ x ∈ X₀ ∧ (∀ r, r.Prime → a_tail < r → ¬ r ∣ x) ∧ (∀ r, r.Prime → M_bot < r → ¬ r * r ∣ x) := by
    simp only [X_A, E_tail, E_sq, Finset.mem_sdiff, mem_union, mem_biUnion, mem_filter, mem_Ioc, not_or, not_exists, not_and]
    refine ⟨fun ⟨hx0, ht, hs⟩ => ?_, fun ⟨hx0, ht, hs⟩ =>
      ⟨hx0, fun r ⟨⟨ha, _⟩, hr⟩ _ => ht r hr ha, fun r ⟨⟨hm, _⟩, hr, _⟩ _ => hs r hr hm⟩⟩
    obtain ⟨hx1, hxn⟩ := mem_Icc.mp hx0
    have fle {d} (hd : d ∣ x) : d ≤ n := (Nat.le_of_dvd hx1 hd).trans hxn
    exact ⟨hx0, fun r hr ha hd => ht r ⟨⟨ha, fle hd⟩, hr⟩ hx0 hd,
      fun r hr hm hd => hs r ⟨⟨hm, (Nat.le_mul_of_pos_right r hr.pos).trans (fle hd)⟩, hr, fle hd⟩ hx0 hd⟩
  have hXA_sub : X_A ⊆ X₀ := sdiff_subset
  have hXA_pos : ∀ x ∈ X_A, 0 < x := fun x hx => (mem_Icc.mp (hXA_sub hx)).1
  have hXA_sq : ∀ x ∈ X_A, ∀ r, r.Prime → M_bot < r → x.factorization r ≤ 1 := fun x hx r hr hMr => by
    by_contra hlt
    exact (mem_XA.mp hx).2.2 r hr hMr (sq r ▸ (Nat.pow_dvd_pow r (by omega : 2 ≤ _)).trans (Nat.ordProj_dvd x r))
  let InvB (m : ℕ) (X : Finset ℕ) : Prop :=
    (∀ x ∈ X_A, (∀ r, r.Prime → m < r → ¬ r ∣ x) → x ∈ X) ∧
    (∀ r, r.Prime → m < r → (∑ x ∈ X, (1 : ℚ) / x).den.factorization r = 0)
  obtain ⟨X_B, hXB_sub, ⟨hXB_surv, hXB_zero⟩, hLoss_B⟩ :=
    descend_sieve (Inv := InvB) (cost := fun p => if p.Prime then peelTerm M_bot n pickG p else 0)
      hM_bot_le_tail ⟨fun x hx _ => hx, fun r hr hgt => Nat.eq_zero_of_le_zero
        (den_fac_le hXA_pos r 0 fun x hx =>
          Nat.le_zero.mpr (Nat.factorization_eq_zero_of_not_dvd ((mem_XA.mp hx).2.1 r hr hgt)))⟩
      fun m hm_ge hm_lt X hX_sub ⟨hSurv, hZero⟩ => by
        set p := m + 1
        by_cases hp_prime : p.Prime
        · obtain ⟨hGM_pos, _, hG_fit, hG_cap⟩ := hG_props p hp_prime (by omega) (by omega)
          set G := pickG p
          set kp := min M_bot (n / (p * G.M))
          have hp_pos := hp_prime.pos
          have hGD_pos := G.hD_pos
          have hkp_pos : 0 < kp := lt_min (by omega) (Nat.div_pos hG_fit (Nat.mul_pos hp_pos hGM_pos))
          let f d := p * kp * d
          let B_set := G.S.image f
          have hinj_f : Set.InjOn f G.S := fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp_pos hkp_pos) h
          have hnr_kpd {d r : ℕ} (hd : d ∈ G.S) (hr : r.Prime) (hMr : M_bot < r) : ¬ r ∣ kp * d :=
            fun h => (hr.dvd_mul.mp h).elim
              (hnd_lt hkp_pos (by have := min_le_left M_bot (n / (p * G.M))
                                  omega))
              (hnd_lt (mem_Icc.mp (G.hS_sub hd)).1 (by have := (mem_Icc.mp (G.hS_sub hd)).2
                                                       omega))
          have hfeq (d) : f d = p * (kp * d) := by
            dsimp [f]
            ring
          have hndvd_f {d r : ℕ} (hd : d ∈ G.S) (hr : r.Prime) (hpr : p < r) : ¬ r ∣ f d := fun hdvd => by
            rw [hfeq] at hdvd
            exact (hr.dvd_mul.mp hdvd).elim (hnd_lt hp_pos hpr) (hnr_kpd hd hr (by omega))
          have hB_sub_XA : B_set ⊆ X_A := fun x hx => by
            obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
            obtain ⟨hd1, hdM⟩ := mem_Icc.mp (G.hS_sub hd)
            refine mem_XA.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos (Nat.mul_pos hp_pos hkp_pos) hd1,
              (show p * kp * d ≤ p * G.M * kp by
                rw [mul_right_comm p kp d]
                gcongr).trans
                ((Nat.mul_le_mul_left _ (min_le_right _ _)).trans (Nat.mul_div_le n _))⟩,
              fun r hr ha => hndvd_f hd hr (by omega), fun r hr hMr hdvd => ?_⟩
            rw [hfeq] at hdvd
            have hnr := hnr_kpd hd hr hMr
            have heq := (hp_prime.dvd_iff_eq hr.ne_one).mp ((hr.dvd_mul.mp ((dvd_mul_right r r).trans hdvd)).resolve_right hnr)
            rw [← heq] at hnr hdvd
            exact hnr ((Nat.mul_dvd_mul_iff_left hp_pos).mp hdvd)
          have hB_sub_X : B_set ⊆ X := fun x hx => by
            obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
            exact hSurv (f d) (hB_sub_XA hx) fun r hr => hndvd_f hd hr
          have hp_not_KD : ¬ p ∣ kp * G.D := fun hd => (hp_prime.dvd_mul.mp hd).elim
            (hnd_lt hkp_pos (by have := min_le_left M_bot (n / (p * G.M))
                                omega))
            fun hpD => absurd (G.hD_smooth p hp_prime hpD) (by omega)
          have hX_pos : ∀ x ∈ X, 0 < x := fun x hx => hXA_pos x (hX_sub hx)
          have himg_sum {U : Finset ℕ} (hU : U ⊆ G.S) :
              ∑ x ∈ U.image f, (1 : ℚ) / x = ((∑ d ∈ U, G.D / d : ℕ) : ℚ) / G.D / (p * kp : ℕ) := by
            have hfdiv : ∑ d ∈ U, (1 : ℚ) / (f d : ℚ) = (∑ d ∈ U, (1 : ℚ) / d) / (p * kp : ℕ) := by
              rw [sum_div]
              refine sum_congr rfl fun d _ => ?_
              dsimp [f]
              push_cast
              ring
            rw [sum_image (hinj_f.mono (coe_subset.mpr hU)), hfdiv,
              inv_dvd hGD_pos fun d hd => ⟨(mem_Icc.mp (G.hS_sub (hU hd))).1, G.hS_dvd d (hU hd)⟩]
          obtain ⟨X', hX'_sub, hkeep, hValP', hOther', hStepLoss⟩ :=
            cancel_step hp_prime le_rfl (Nat.mul_pos hkp_pos hGD_pos) hp_not_KD hX_pos hB_sub_X
              (fun x hx => hXA_sq x (hB_sub_XA hx) p hp_prime (by omega))
              (den_fac_le hX_pos p 1 fun x hx => hXA_sq x (hX_sub hx) p hp_prime (by omega))
              hG_cap fun t htA htB => by
                obtain ⟨U₀, hU₀, hsum₀⟩ := G.hcov t htA htB
                refine ⟨U₀.image f, image_subset_image hU₀, ?_⟩
                rw [himg_sum hU₀, hsum₀, div_div, pow_one]
                push_cast
                ring
          have hB_sum_eq : ∑ x ∈ B_set, (1 : ℚ) / x = (G.eta + (G.B : ℚ) / G.D) / (p * kp : ℕ) := by
            rw [himg_sum Subset.rfl, show ((∑ d ∈ G.S, G.D / d : ℕ) : ℚ) = G.eta * G.D + G.B by linarith [G.heta],
              add_div, mul_div_cancel_right₀ _ (by positivity)]
          refine ⟨X', hX'_sub, ⟨fun x hx hndvd => hkeep (mem_sdiff.mpr
            ⟨hSurv x hx fun r hr hgt => hndvd r hr (by omega),
             fun hxB => by
               obtain ⟨d, _, rfl⟩ := mem_image.mp hxB
               exact hndvd p hp_prime (by omega) ⟨kp * d, by ring⟩⟩),
            fun r hr hgt => (eq_or_lt_of_le (show p ≤ r by omega)).elim
              (fun e => e ▸ Nat.eq_zero_of_le_zero hValP') fun hlt => Nat.eq_zero_of_le_zero
                ((hOther' r fun x hx => by
                    obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
                    exact hndvd_f hd hr hlt).trans (hZero r hr hlt).le)⟩, ?_⟩
          rw [if_pos hp_prime]
          unfold peelTerm
          dsimp only
          rw [hB_sum_eq, pow_one, Nat.cast_sub (by omega : p ≤ G.B + 1)] at hStepLoss
          rw [Nat.cast_sub (by omega : 1 ≤ p)]
          have halg : (G.eta + (G.B : ℚ) / G.D) / (p * kp : ℕ) - (((G.B + 1 : ℕ) : ℚ) - p) / (p * (kp * G.D) : ℕ) =
              (G.eta + ((p : ℚ) - (1 : ℕ)) / G.D) / (p * kp : ℕ) := by
            push_cast
            field_simp
            ring
          linarith
        · exact ⟨X, Subset.rfl, ⟨fun x hx hndvd => hSurv x hx fun r hr hgt => hndvd r hr (by omega),
            fun r hr hgt => (eq_or_lt_of_le (show p ≤ r by omega)).elim (fun e => absurd (e ▸ hr) hp_prime) (hZero r hr)⟩,
            by simp [hp_prime]⟩
  have hXB_smooth : ∀ x ∈ X₀, (∀ r, r.Prime → M_bot < r → ¬ r ∣ x) → x ∈ X_B := fun x hx0 hsm =>
    hXB_surv x (mem_XA.mpr ⟨hx0, fun r hr h => hsm r hr (by omega),
      fun r hr h hd => hsm r hr h ((dvd_mul_right r r).trans hd)⟩) hsm
  let InvC (m : ℕ) (X : Finset ℕ) : Prop :=
    (∀ x ∈ X₀, (∀ r, r.Prime → M_bot < r → ¬ r ∣ x) → (∀ r, r.Prime → m < r → ¬ r ^ (tgtExp r + 1) ∣ x) → x ∈ X) ∧
    (∀ r, r.Prime → m < r → (∑ x ∈ X, (1 : ℚ) / x).den.factorization r ≤ tgtExp r)
  obtain ⟨X_C, hXC_sub, ⟨hXC_surv, hXC_fac⟩, hLoss_C⟩ :=
    descend_sieve (Inv := InvC)
      (cost := fun q => if q.Prime then ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), qaTerm n q a else 0)
      (by omega : 1 ≤ M_bot)
      ⟨fun x hx0 hsm _ => hXB_smooth x hx0 hsm, fun r hr hgt => by
        rw [hXB_zero r hr hgt]
        exact Nat.zero_le _⟩
      fun m _ hm_lt X hX_sub ⟨hSurv, hHigh⟩ => by
        set q := m + 1
        by_cases hq_prime : q.Prime
        · obtain ⟨X', hX'_sub, hSurv', hHigh', hStepLoss⟩ :=
            peelPrime hn hq_prime (by omega) (hX_sub.trans (hXB_sub.trans hXA_sub)) hSurv hHigh
          exact ⟨X', hX'_sub, ⟨hSurv', hHigh'⟩, by simpa [hq_prime] using hStepLoss⟩
        · exact ⟨X, Subset.rfl, ⟨fun x hx0 hsm hhi => hSurv x hx0 hsm fun r hr hgt => hhi r hr (by omega),
            fun r hr hgt => (eq_or_lt_of_le (show q ≤ r by omega)).elim (fun e => absurd (e ▸ hr) hq_prime) (hHigh r hr)⟩,
            by simp [hq_prime]⟩
  have hXC_Icc : X_C ⊆ X₀ := hXC_sub.trans (hXB_sub.trans hXA_sub)
  have hLoss_C_eq : (∑ q ∈ Ioc 1 M_bot,
      if q.Prime then ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), qaTerm n q a else 0) = lossQA M_bot n := by
    have hflt : (Ioc 1 M_bot).filter Nat.Prime = insert 2 ((Icc 3 M_bot).filter Nat.Prime) := by
      ext z
      simp only [mem_filter, mem_Ioc, mem_insert, mem_Icc]
      refine ⟨fun ⟨⟨_, h2⟩, hz⟩ => (eq_or_lt_of_le hz.two_le).imp Eq.symm fun h => ⟨⟨by omega, h2⟩, hz⟩, ?_⟩
      rintro (rfl | ⟨⟨_, h2⟩, hz⟩)
      · exact ⟨⟨by omega, by omega⟩, Nat.prime_two⟩
      · exact ⟨⟨by omega, h2⟩, hz⟩
    rw [← sum_filter, hflt, sum_insert (by simp)]
    simp only [tgtExp, ↓reduceIte, qaTerm, lossQA]
    congr 1
    refine sum_congr rfl fun q hq => sum_congr rfl fun _ _ => if_neg ?_
    have := (mem_Icc.mp (mem_filter.mp hq).1).1
    omega
  have hfac_11520 (p) : (11520 : ℕ).factorization p = tgtExp p := by
    rw [show (11520 : ℕ) = 2 ^ 8 * (3 ^ 2 * 5) by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow, (by decide : Nat.Prime 5).factorization]
    simp only [Finsupp.add_apply, Finsupp.single_apply, tgtExp]
    split_ifs
    all_goals omega
  have hnot_pow_11520 {p} (hp : p.Prime) : ¬ p ^ (tgtExp p + 1) ∣ 11520 := fun hd => by
    have := (hp.pow_dvd_iff_le_factorization (by norm_num)).mp hd
    rw [hfac_11520] at this
    omega
  let ds11520 : List ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 32, 36, 40, 45, 48, 60, 64, 72, 80, 90, 96,
    120, 128, 144, 160, 180, 192, 240, 256, 288, 320, 360, 384, 480, 576, 640, 720, 768, 960, 1152, 1280, 1440, 1920, 2304,
    2880, 3840, 5760, 11520]
  let S_term := ds11520.toFinset
  have hSterm_mem : ∀ d ∈ S_term, 1 ≤ d ∧ d ≤ 11520 ∧ d ∣ 11520 := fun d hd => by
    have hp : ∀ x ∈ ds11520, 1 ≤ x ∧ x ≤ 11520 ∧ 11520 % x = 0 := by decide
    obtain ⟨h1, h2, h3⟩ := hp d (List.mem_toFinset.mp hd)
    exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3⟩
  have hS_sub_XC : S_term ⊆ X_C := fun d hd => by
    obtain ⟨hd1, _, hd_dvd⟩ := hSterm_mem d hd
    refine hXC_surv d (mem_Icc.mpr ⟨hd1, by omega⟩) (fun r hr hMr hdvd_d => ?_)
      fun r hr _ hdvd_d => hnot_pow_11520 hr (hdvd_d.trans hd_dvd)
    have hte0 : tgtExp r = 0 := by
      dsimp [tgtExp]
      split_ifs
      all_goals omega
    refine hnot_pow_11520 hr ?_
    rw [hte0, zero_add, pow_one]
    exact hdvd_d.trans hd_dvd
  have hSterm_sum : ∑ d ∈ S_term, (1 : ℚ) / d = (39858 : ℚ) / 11520 := by
    rw [inv_dvd (by norm_num) (fun d hd => ⟨(hSterm_mem d hd).1, (hSterm_mem d hd).2.2⟩),
      List.sum_toFinset _ (by decide : ds11520.Nodup), (by decide : (ds11520.map (11520 / ·)).sum = 39858)]
    norm_num
  let X_rest := X_C \ S_term
  let R_sum : ℚ := ∑ x ∈ X_rest, (1 : ℚ) / x
  have hXC_split : ∑ x ∈ X_C, (1 : ℚ) / x = R_sum + ∑ d ∈ S_term, (1 : ℚ) / d := (sum_sdiff hS_sub_XC).symm
  have hR_nn : 0 ≤ R_sum := sum_nonneg fun _ _ => by positivity
  obtain ⟨c, hc⟩ : R_sum.den ∣ 11520 :=
    (Nat.factorization_le_iff_dvd R_sum.den_pos.ne' (by norm_num)).mp fun p => by
      rw [show R_sum = (∑ x ∈ X_C, (1 : ℚ) / x) - (39858 : ℚ) / 11520 by linarith]
      have hd11520 : ((39858 : ℚ) / 11520).den.factorization p ≤ (11520 : ℕ).factorization p :=
        (Nat.factorization_le_iff_dvd ((39858 : ℚ) / 11520).den_pos.ne' (by norm_num)).mpr
          (Int.natCast_dvd_natCast.mp (by simpa [Rat.divInt_eq_div] using Rat.den_dvd 39858 11520)) p
      refine (sub_fac_le _ _ p).trans (max_le ?_ hd11520)
      exact if hp : p.Prime then (hXC_fac p hp hp.one_lt).trans (hfac_11520 p).ge
        else by simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  let R_int : ℕ := R_sum.num.toNat * c
  have hR_div : R_sum = (R_int : ℚ) / 11520 := by
    conv_lhs => rw [← Rat.num_div_den R_sum]
    rw [show (11520 : ℚ) = (R_sum.den : ℚ) * c from mod_cast hc]
    push_cast [R_int]
    rw [show (R_sum.num.toNat : ℚ) = R_sum.num from mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hR_nn)]
    exact (mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr fun h0 => by simp [h0] at hc)).symm
  have hX0_harm : ∑ x ∈ X₀, (1 : ℚ) / x = harmonic n := by
    rw [harmonic_eq_sum_Icc]
    simp [X₀, one_div]
  have hR_le_harm_sub : R_sum + (39858 : ℚ) / 11520 ≤ harmonic n := by
    rw [← hSterm_sum, ← hXC_split, ← hX0_harm]
    exact sum_le_sum_of_subset_of_nonneg hXC_Icc fun _ _ _ => by positivity
  have hR_int_lt : ((R_int : ℕ) : ℚ) < ((11520 * k : ℕ) : ℚ) := by
    push_cast
    linarith
  have hR_int_le : R_int ≤ 11520 * k := (Nat.cast_lt.mp hR_int_lt).le
  have hXC_ge_k : (k : ℚ) ≤ ∑ x ∈ X_C, (1 : ℚ) / x := by
    rw [← sum_filter] at hLoss_B
    rw [hLoss_C_eq] at hLoss_C
    dsimp only [lossPeel] at hloss_le
    linarith [hLoss_A, hLoss_B, hLoss_C, hX0_harm, hloss_le]
  have hneed_le : 11520 * k - R_int ≤ 39858 := by
    have hQ : ((11520 * k : ℕ) : ℚ) ≤ ((R_int + 39858 : ℕ) : ℚ) := by
      push_cast
      linarith
    have := Nat.cast_le (α := ℚ).mp hQ
    omega
  obtain ⟨U_term, hU_sub, hU_sum⟩ := dpMask_ok (D := 11520) (ds := ds11520) (by decide)
    (by decide : chkRange (dpMask 11520 ds11520) 0 39859 = true) (Nat.zero_le (11520 * k - R_int)) (by omega)
  refine ⟨X_rest ∪ U_term, union_subset (sdiff_subset.trans hXC_Icc) ((hU_sub.trans hS_sub_XC).trans hXC_Icc), ?_⟩
  rw [sum_union (Disjoint.mono_right hU_sub sdiff_disjoint), show ∑ x ∈ X_rest, (1 : ℚ) / x = R_sum from rfl, hR_div,
    inv_dvd (by norm_num) (fun d hd => ⟨(hSterm_mem d (hU_sub hd)).1, (hSterm_mem d (hU_sub hd)).2.2⟩),
    hU_sum, Nat.cast_sub hR_int_le]
  push_cast
  ring

/- ### Section 5: Abel Summation, Certificate (`10 ≤ k ≤ 149`), and Asymptotic (`k ≥ 150`) -/

structure GSpec where
  (M D L etaNum : ℕ)
def MatchSpec (G : Gadget) (s : GSpec) : Prop :=
  G.M = s.M ∧ G.D = s.D ∧ s.L ≤ G.B + 1 - G.A ∧ G.eta ≤ (s.etaNum : ℚ) / s.D
def tDiff9 (a b : ℕ) : ℕ :=
  (10386 * b - 9569 * a) * 100000 + cdiv (188 * logUb9 b + 156 * logUb9 a) 10 + 4260000000 * isqrtUb a
@[category API, AMS 11] lemma tDiff9_ok {a b : ℕ} (ha : 300 ≤ a) (hab : a ≤ b) :
    theta (b : ℝ) - theta (a : ℝ) ≤ (tDiff9 a b : ℝ) / S9 := by
  have hla := (log_bds (x := a) (by omega)).2
  have hlb := (log_bds (x := b) (by omega)).2
  have hcd := cdiv_ok (a := 188 * logUb9 b + 156 * logUb9 a) (by decide : 0 < 10)
  have hta := (theta_bds (show (300 : ℝ) ≤ a from mod_cast ha)).1
  have htb := (theta_bds (show (300 : ℝ) ≤ b from mod_cast ha.trans hab)).2
  have hsq := (isqrt_bds a).2
  unfold tDiff9 S9 at *
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 9569 * a ≤ 10386 * b)]
  push_cast at hcd ⊢
  norm_num at hla hlb ⊢
  linarith
@[category API, AMS 11] lemma slice_ub {n n_hi u v v_hi d nxt : ℕ}
    (hu300 : 300 ≤ u) (huv : u ≤ v) (hvv : v ≤ v_hi) (hd : 0 < d) (hnxt : 0 < nxt)
    (hlin : 9569 * d ≤ 10386 * nxt) (hn : n ≤ n_hi) (hu_eq : u = n / nxt) (hv_eq : v = n / d) :
    theta (v : ℝ) - theta (u : ℝ) ≤
      ((cdiv ((10386 * nxt - 9569 * d) * n_hi * 100000) (d * nxt) + 956900000 +
        cdiv (344 * logUb9 v_hi) 10 + 4260000000 * isqrtUb v_hi : ℕ) : ℝ) / S9 := by
  have hdR : (0 : ℝ) < d := by positivity
  have hnxtR : (0 : ℝ) < nxt := by positivity
  have hlv := (log_bds (x := v_hi) (by omega)).2
  have hv_le : (v : ℝ) ≤ (n : ℝ) / d := by
    rw [hv_eq, le_div_iff₀ hdR]
    exact_mod_cast Nat.div_mul_le_self n d
  have hu_ge : (n : ℝ) / nxt - 1 ≤ (u : ℝ) := by
    rw [hu_eq, sub_le_iff_le_add, div_le_iff₀ hnxtR]
    have hdm := Nat.div_add_mod n nxt
    have hlt := Nat.mod_lt n hnxt
    have hnle : n ≤ (n / nxt + 1) * nxt := by
      rw [add_mul, one_mul, mul_comm]
      omega
    exact_mod_cast hnle
  have hmain : ((10386 : ℝ) / 10000) * v - (9569 / 10000) * u ≤
      (((10386 * nxt - 9569 * d : ℕ) : ℝ) * n_hi * 100000 / ((d : ℝ) * nxt)) / S9 + 9569 / 10000 := by
    refine (by linarith : _ ≤ ((10386 : ℝ) / 10000) * ((n : ℝ) / d) - (9569 / 10000) * ((n : ℝ) / nxt - 1)).trans ?_
    rw [Nat.cast_sub hlin]
    unfold S9
    push_cast
    have heq1 : ((10386 : ℝ) / 10000) * ((n : ℝ) / d) - (9569 / 10000) * ((n : ℝ) / nxt - 1) =
        ((10386 * nxt - 9569 * d) * (n : ℝ)) / (10000 * d * nxt) + 9569 / 10000 := by
      field_simp
      ring
    have heq2 : ((10386 * nxt - 9569 * d) * (n_hi : ℝ)) / (10000 * d * nxt) =
        (((10386 * nxt - 9569 * d) * (n_hi : ℝ) * 100000) / ((d : ℝ) * nxt)) / 1000000000 := by
      field_simp
      ring
    have hnn : (0 : ℝ) ≤ 10386 * (nxt : ℝ) - 9569 * d := mod_cast Nat.zero_le (10386 * nxt - 9569 * d)
    have hdiv_le : ((10386 * nxt - 9569 * d) * (n : ℝ)) / (10000 * d * nxt) ≤
        ((10386 * nxt - 9569 * d) * (n_hi : ℝ)) / (10000 * d * nxt) := by gcongr
    linarith
  have hcd1 := cdiv_ok (a := (10386 * nxt - 9569 * d) * n_hi * 100000) (Nat.mul_pos hd hnxt)
  have hcd2 := cdiv_ok (a := 344 * logUb9 v_hi) (by decide : 0 < 10)
  unfold S9 at hlv hmain ⊢
  norm_num at hlv
  push_cast at hcd1 hcd2 ⊢
  linarith [(theta_bds (show (300 : ℝ) ≤ u from mod_cast hu300)).1,
    (theta_bds (show (300 : ℝ) ≤ v from mod_cast hu300.trans huv)).2,
    log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (huv.trans hvv)),
    log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr hvv),
    (sqrt_le_sqrt (Nat.cast_le.mpr (huv.trans hvv))).trans (isqrt_bds v_hi).2]
@[category API, AMS 11] lemma inv_p_real {a b : ℕ} (ha : 300 ≤ a) (hab : a ≤ b) :
    ((∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℚ) / p) : ℝ) ≤
      (((817 : ℝ) / 10000) * a + (344 / 10) * log a + (426 / 100) * sqrt a) /
        (((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) +
      (10386 / 10000) * log (log b / log a) + (188 / 10) / (a * log a) := by
  let T (n : ℕ) : ℝ := theta (n : ℝ)
  let H (n : ℕ) : ℝ := ((10386 : ℝ) / 10000) * n + (188 / 10) * log n
  let D (n : ℕ) : ℝ := T n - H n
  let f (n : ℕ) : ℝ := 1 / (n * log n)
  have hf_nn : ∀ n ≥ a, 0 ≤ f (n + 1) := fun n _ => by
    dsimp [f]
    have := log_pos (show (1 : ℝ) < (n + 1 : ℕ) from mod_cast (by omega : 1 < n + 1))
    positivity
  have hloga_pos : 0 < log a := log_pos (mod_cast (by omega : 1 < a))
  have hH_tel : ∑ n ∈ Ioc a b, (H n - H (n - 1)) * f n ≤
      (10386 / 10000) * (log (log b) - log (log a)) + ((188 : ℝ) / 10 / log a) * (1 / (a : ℝ) - 1 / b) := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ k hka ih =>
      rw [sum_Ioc_succ_top hka, Nat.add_sub_cancel]
      obtain ⟨hlog_lb, hlog_ub⟩ := log_succ (by omega : 1 ≤ k)
      have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
      have hlk : 0 < log k := log_pos (mod_cast (by omega : 1 < k))
      have hlk1 : 0 < log ((k + 1 : ℕ) : ℝ) := log_pos (mod_cast (by omega : 1 < k + 1))
      have hll : 1 / (((k + 1 : ℕ) : ℝ) * log ((k + 1 : ℕ) : ℝ)) ≤ log (log ((k + 1 : ℕ) : ℝ)) - log (log k) := by
        have h := one_sub_inv_le_log_of_pos (div_pos hlk1 hlk)
        rw [inv_div, log_div hlk1.ne' hlk.ne'] at h
        have h2 := div_le_div_of_nonneg_right hlog_lb hlk1.le
        rw [div_div] at h2
        linarith [show 1 - log k / log ((k + 1 : ℕ) : ℝ) =
          (log ((k + 1 : ℕ) : ℝ) - log k) / log ((k + 1 : ℕ) : ℝ) by field_simp]
      have herr : (1 / (k : ℝ)) * f (k + 1) ≤ (1 / log a) * (1 / (k : ℝ) - 1 / (k + 1 : ℕ)) := by
        dsimp [f]
        have hsub : 1 / (k : ℝ) - 1 / (k + 1 : ℕ) = 1 / (k * (k + 1 : ℕ)) := by
          push_cast
          field_simp
          ring
        rw [hsub, one_div_mul_one_div, one_div_mul_one_div, mul_comm (log a), mul_assoc]
        gcongr
        omega
      have hHd : H (k + 1) - H k ≤ 10386 / 10000 + (188 / 10) * (1 / (k : ℝ)) := by
        dsimp [H]
        push_cast at hlog_ub ⊢
        linarith
      have hprod := mul_le_mul_of_nonneg_right hHd (hf_nn k hka)
      have hpf : (10386 / 10000 + (188 / 10) * (1 / (k : ℝ))) * f (k + 1) =
          (10386 / 10000) * (1 / (((k + 1 : ℕ) : ℝ) * log ((k + 1 : ℕ) : ℝ))) +
            (188 / 10) * ((1 / (k : ℝ)) * f (k + 1)) := by
        dsimp [f]
        ring
      rw [hpf] at hprod
      linarith [mul_le_mul_of_nonneg_left hll (by norm_num : (0 : ℝ) ≤ 10386 / 10000),
        (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 188 / 10)).trans_eq (by ring :
          (188 / 10) * ((1 / log a) * (1 / (k : ℝ) - 1 / (k + 1 : ℕ))) =
            ((188 : ℝ) / 10 / log a) * (1 / (k : ℝ) - 1 / (k + 1 : ℕ)))]
  have hsum_eq : ((∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℚ) / p) : ℝ) =
      (∑ n ∈ Ioc a b, (D n - D (n - 1)) * f n) + ∑ n ∈ Ioc a b, (H n - H (n - 1)) * f n := by
    rw [← sum_add_distrib]
    push_cast
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := by
      have := (mem_Ioc.mp hn).1
      omega
    have hts : theta (n : ℝ) - theta ((n - 1 : ℕ) : ℝ) = if n.Prime then log n else 0 := by
      have hs (m : ℕ) : theta ((m + 1 : ℕ) : ℝ) - theta (m : ℝ) =
          if (m + 1).Prime then log ((m + 1 : ℕ) : ℝ) else 0 := by
        simp only [theta, Nat.floor_natCast, sum_filter, sum_Ioc_succ_top (Nat.zero_le m), add_sub_cancel_left]
      simpa [Nat.sub_add_cancel hn1] using hs (n - 1)
    have hDH : (D n - D (n - 1)) * f n + (H n - H (n - 1)) * f n =
        (theta (n : ℝ) - theta ((n - 1 : ℕ) : ℝ)) * f n := by
      dsimp [D, T]
      ring
    rw [hDH, hts]
    split_ifs with hp
    · dsimp [f]
      have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have : log (n : ℝ) ≠ 0 := (log_pos (mod_cast hp.one_lt)).ne'
      field_simp
    · simp
  have habel : ∑ n ∈ Ioc a b, (D n - D (n - 1)) * f n ≤ (-D a) * f (a + 1) := by
    have hD (n) (hna : a ≤ n) : D n ≤ 0 := by
      dsimp [D, T, H]
      linarith [(theta_bds (show (300 : ℝ) ≤ n from mod_cast ha.trans hna)).2]
    suffices ∀ m ≥ a, ∑ n ∈ Ioc a m, (D n - D (n - 1)) * f n - D m * f (m + 1) ≤ (-D a) * f (a + 1) by
      linarith [this b hab, mul_nonpos_of_nonpos_of_nonneg (hD b hab) (hf_nn b hab)]
    intro m ham
    induction m, ham using Nat.le_induction with
    | base => simp
    | succ k hka ih =>
      rw [sum_Ioc_succ_top hka, Nat.add_sub_cancel]
      have hanti : f (k + 2) ≤ f (k + 1) := by
        dsimp [f]
        have hk1 : (0 : ℝ) < (k + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
        have hl1 : 0 < log ((k + 1 : ℕ) : ℝ) := log_pos (mod_cast (by omega : 1 < k + 1))
        gcongr
        all_goals omega
      linarith [mul_nonpos_of_nonpos_of_nonneg (hD (k + 1) (by omega)) (sub_nonneg.mpr hanti)]
  have hDa : -D a ≤ (817 / 10000) * a + (344 / 10) * log a + (426 / 100) * sqrt a := by
    dsimp [D, T, H]
    linarith [(theta_bds (show (300 : ℝ) ≤ a from mod_cast ha)).1]
  have hbd : ∑ n ∈ Ioc a b, (D n - D (n - 1)) * f n ≤
      (((817 : ℝ) / 10000) * a + (344 / 10) * log a + (426 / 100) * sqrt a) /
        (((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) := by
    refine habel.trans ((mul_le_mul_of_nonneg_right hDa (hf_nn a le_rfl)).trans_eq ?_)
    dsimp [f]
    ring
  rw [← log_div (log_pos (mod_cast (by omega : 1 < b))).ne' hloga_pos.ne'] at hH_tel
  have herr_end : ((188 : ℝ) / 10 / log a) * (1 / (a : ℝ) - 1 / b) ≤ (188 / 10) / (a * log a) :=
    (mul_le_mul_of_nonneg_left (by linarith [show (0 : ℝ) ≤ 1 / b by positivity] : 1 / (a : ℝ) - 1 / b ≤ 1 / a)
      (by positivity)).trans_eq (by ring)
  rw [hsum_eq]
  linarith [hbd, hH_tel, herr_end]
@[category API, AMS 11] lemma logLb9_pos {x : ℕ} (hx : 300 ≤ x) : 0 < logLb9 x := by
  unfold logLb9
  rw [if_neg (by
    intro h
    have := Nat.ble_eq.mp h
    omega)]
  exact Nat.add_pos_left (Nat.add_pos_left
    (Nat.mul_pos (Nat.log2_eq_log_two ▸ Nat.le_log_of_pow_le (by decide) (by omega)) (by decide)) _) _
def invDelta9 (a_lo dlog9 : ℕ) : ℕ :=
  let loga := logLb9 a_lo
  let loga1 := logLb9 (a_lo + 1)
  cdiv (81700000 * S9) loga1 + cdiv 34400000000 (a_lo + 1) + cdiv (4260000000 * S9) (isqrtLb a_lo * loga1) +
    cdiv (10386 * log1pUb9 dlog9 loga) 10000 + cdiv (188 * S9 * S9) (10 * a_lo * loga)
@[category API, AMS 11] lemma invDelta9_ok {a b a_lo dlog9 : ℕ}
    (ha_lo : 300 ≤ a_lo) (ha_ge : a_lo ≤ a) (hab : a ≤ b) (hdlog : log (b : ℝ) - log (a : ℝ) ≤ (dlog9 : ℝ) / S9) :
    ((∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℚ) / p) : ℝ) ≤ (invDelta9 a_lo dlog9 : ℝ) / S9 := by
  have hreal := inv_p_real (ha_lo.trans ha_ge) hab
  obtain ⟨hsq_pos, hsq_lb⟩ := (isqrt_bds a_lo).1 (by omega)
  have hloga_n := logLb9_pos ha_lo
  have hloga1_n := logLb9_pos (by omega : 300 ≤ a_lo + 1)
  have hS9 : (0 : ℝ) < S9 := by
    unfold S9
    norm_num
  have hloga_ge := (log_bds (x := a_lo) (by omega)).1.trans
    (log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr ha_ge))
  have hloga1_ge := (log_bds (x := a_lo + 1) (by omega)).1.trans
    (log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (by omega : a_lo + 1 ≤ a + 1)))
  have hloga_lb : (0 : ℝ) < (logLb9 a_lo : ℝ) / S9 := div_pos (Nat.cast_pos.mpr hloga_n) hS9
  have hloga1_lb : (0 : ℝ) < (logLb9 (a_lo + 1) : ℝ) / S9 := div_pos (Nat.cast_pos.mpr hloga1_n) hS9
  have hloga_pos := hloga_lb.trans_le hloga_ge
  have hloga1_pos := hloga1_lb.trans_le hloga1_ge
  have ha1_pos : (0 : ℝ) < (a + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hnum : ((817 : ℝ) / 10000) * a + (344 / 10) * log a + (426 / 100) * sqrt a ≤
      (817 / 10000) * ((a + 1 : ℕ) : ℝ) + ((426 / 100) / isqrtLb a_lo) * ((a + 1 : ℕ) : ℝ) +
        ((344 / 10) / (a_lo + 1 : ℕ)) * (((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) := by
    have hsq1 : sqrt (a : ℝ) ≤ ((a + 1 : ℕ) : ℝ) / isqrtLb a_lo :=
      ((le_div_iff₀ (sqrt_pos.mpr ha_pos)).mpr (by
        rw [mul_self_sqrt ha_pos.le]
        exact_mod_cast (by omega : a ≤ a + 1))).trans
        (div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr hsq_pos)
          (hsq_lb.trans (sqrt_le_sqrt (Nat.cast_le.mpr ha_ge))))
    have hl1 : log (a : ℝ) ≤ (((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) / (a_lo + 1 : ℕ) := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega : 0 < a_lo + 1))]
      exact (mul_le_mul (log_le_log ha_pos (Nat.cast_le.mpr (by omega))) (Nat.cast_le.mpr (by omega))
        (by positivity) hloga1_pos.le).trans_eq (mul_comm _ _)
    linarith [show (a : ℝ) ≤ (a + 1 : ℕ) from Nat.cast_le.mpr (by omega),
      mul_le_mul_of_nonneg_left hsq1 (by norm_num : (0 : ℝ) ≤ 426 / 100),
      mul_le_mul_of_nonneg_left hl1 (by norm_num : (0 : ℝ) ≤ 344 / 10),
      show (426 / 100) * (((a + 1 : ℕ) : ℝ) / isqrtLb a_lo) = ((426 / 100) / isqrtLb a_lo) * ((a + 1 : ℕ) : ℝ) by ring,
      show (344 / 10) * ((((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) / (a_lo + 1 : ℕ)) =
        ((344 / 10) / (a_lo + 1 : ℕ)) * (((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) by ring]
  have hd : (((817 : ℝ) / 10000) * a + (344 / 10) * log a + (426 / 100) * sqrt a) /
      (((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) ≤
      (817 / 10000) / log ((a + 1 : ℕ) : ℝ) + (344 / 10) / (a_lo + 1 : ℕ) +
        ((426 / 100) / isqrtLb a_lo) / log ((a + 1 : ℕ) : ℝ) := by
    refine (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq ?_
    have := ha1_pos.ne'
    have := hloga1_pos.ne'
    field_simp
    ring
  have hc1 : (817 / 10000) / log ((a + 1 : ℕ) : ℝ) ≤ (cdiv (81700000 * S9) (logLb9 (a_lo + 1)) : ℝ) / S9 := by
    refine le_cdiv_S9 hloga1_n ((div_le_div_of_nonneg_left (by norm_num) hloga1_lb hloga1_ge).trans ?_)
    have : (logLb9 (a_lo + 1) : ℝ) ≠ 0 := by positivity
    unfold S9
    push_cast
    field_simp
    norm_num
  have hc2 : (344 / 10) / ((a_lo + 1 : ℕ) : ℝ) ≤ (cdiv 34400000000 (a_lo + 1) : ℝ) / S9 := by
    refine le_cdiv_S9 (by omega) ?_
    have : (a_lo : ℝ) + 1 ≠ 0 := by positivity
    unfold S9
    push_cast
    field_simp
    norm_num
  have hc3 : ((426 / 100) / (isqrtLb a_lo : ℝ)) / log ((a + 1 : ℕ) : ℝ) ≤
      (cdiv (4260000000 * S9) (isqrtLb a_lo * logLb9 (a_lo + 1)) : ℝ) / S9 := by
    refine le_cdiv_S9 (Nat.mul_pos hsq_pos hloga1_n) ((div_le_div_of_nonneg_left (by positivity) hloga1_lb hloga1_ge).trans ?_)
    have : (isqrtLb a_lo : ℝ) ≠ 0 := by positivity
    have : (logLb9 (a_lo + 1) : ℝ) ≠ 0 := by positivity
    unfold S9
    push_cast
    field_simp
    norm_num
  have hmn : (10386 / 10000) * log (log (b : ℝ) / log (a : ℝ)) ≤
      (cdiv (10386 * log1pUb9 dlog9 (logLb9 a_lo)) 10000 : ℝ) / S9 := by
    apply le_cdiv_S9 (by decide)
    have hldiv : log (b : ℝ) / log a = 1 + (log b - log a) / log a := by
      have := hloga_pos.ne'
      field_simp
      ring
    rw [hldiv]
    have hu_ub : (log (b : ℝ) - log a) / log a ≤ dlog9 / logLb9 a_lo := by
      refine (div_le_div₀ (by positivity) hdlog hloga_lb hloga_ge).trans ?_
      have := hS9.ne'
      field_simp
      exact le_rfl
    refine (mul_le_mul_of_nonneg_left ((log1p_bds hloga_n).2
      (div_nonneg (sub_nonneg.mpr (log_le_log ha_pos (Nat.cast_le.mpr hab))) hloga_pos.le) hu_ub) (by norm_num)).trans ?_
    push_cast
    ring_nf
    exact le_rfl
  have her : (188 / 10) / ((a : ℝ) * log a) ≤ (cdiv (188 * S9 * S9) (10 * a_lo * logLb9 a_lo) : ℝ) / S9 := by
    apply le_cdiv_S9 (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hloga_n)
    refine (div_le_div_of_nonneg_left (by norm_num) (mul_pos (Nat.cast_pos.mpr (by omega)) hloga_lb)
      (mul_le_mul (Nat.cast_le.mpr ha_ge) hloga_ge hloga_lb.le (Nat.cast_nonneg a))).trans ?_
    have : (a_lo : ℝ) ≠ 0 := by positivity
    have : (logLb9 a_lo : ℝ) ≠ 0 := by positivity
    unfold S9
    push_cast
    field_simp
    norm_num
  unfold invDelta9
  push_cast
  rw [add_div, add_div, add_div, add_div]
  linarith
def invUb9 (a b : ℕ) : ℕ := if Nat.ble b a then 0 else invDelta9 a (logUb9 b - logLb9 a)
@[category API, AMS 11] lemma invUb9_ok {a b : ℕ} (ha : 300 ≤ a) :
    ((∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℚ) / p) : ℝ) ≤ (invUb9 a b : ℝ) / S9 := by
  unfold invUb9
  split_ifs with hble
  · rw [Ioc_eq_empty (by
      have := Nat.ble_eq.mp hble
      omega)]
    simp
  · have hab : a ≤ b := (not_le.mp fun h => hble (Nat.ble_eq.mpr h)).le
    have hla := (log_bds (x := a) (by omega)).1
    have hlb := (log_bds (x := b) (by omega)).2
    have hle_log := log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr hab)
    have hS9 : (0 : ℝ) < S9 := by
      unfold S9
      norm_num
    refine invDelta9_ok ha le_rfl hab ?_
    rw [Nat.cast_sub (mod_cast (div_le_div_iff_of_pos_right hS9).mp
      (by linarith : (logLb9 a : ℝ) / S9 ≤ logUb9 b / S9)), sub_div]
    linarith
@[category API, AMS 11] lemma quot_log_sub_le {n a_lo den_hi den_lo : ℕ}
    (hd_hi : 0 < den_hi) (ha_pos : 1 ≤ a_lo) (ha_le : a_lo ≤ n / den_lo) :
    log ((n / den_hi : ℕ) : ℝ) - log ((n / den_lo : ℕ) : ℝ) ≤
      (((logUb9 den_lo - logLb9 den_hi) + cdiv S9 a_lo : ℕ) : ℝ) / S9 := by
  have hS9 : (0 : ℝ) < S9 := by
    unfold S9
    norm_num
  by_cases hb0 : n / den_hi = 0
  · rw [hb0, Nat.cast_zero, log_zero, zero_sub]
    linarith [log_nonneg (show (1 : ℝ) ≤ (n / den_lo : ℕ) from mod_cast ha_pos.trans ha_le),
      div_nonneg (Nat.cast_nonneg ((logUb9 den_lo - logLb9 den_hi) + cdiv S9 a_lo)) hS9.le]
  · set a := n / den_lo
    set b := n / den_hi
    have hd_lo : 0 < den_lo := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      simp [a] at ha_le
      omega
    have haR : (0 : ℝ) < a := Nat.cast_pos.mpr (ha_pos.trans ha_le)
    have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb0)
    have hdhiR : (0 : ℝ) < den_hi := Nat.cast_pos.mpr hd_hi
    have hdloR : (0 : ℝ) < den_lo := Nat.cast_pos.mpr hd_lo
    have had : n ≤ (a + 1) * den_lo := by
      have := Nat.div_add_mod n den_lo
      have := Nat.mod_lt n hd_lo
      dsimp [a]
      rw [add_mul, one_mul, mul_comm]
      omega
    have hrat : (b : ℝ) / a ≤ ((den_lo : ℝ) / den_hi) * (1 + 1 / (a_lo : ℝ)) := by
      have h1 : (b : ℝ) * den_hi ≤ ((a + 1 : ℕ) : ℝ) * den_lo := mod_cast (Nat.div_mul_le_self n den_hi).trans had
      have h2 : (b : ℝ) / a ≤ ((den_lo : ℝ) / den_hi) * (1 + 1 / (a : ℝ)) := by
        have heq : ((den_lo : ℝ) / den_hi) * (1 + 1 / (a : ℝ)) * a = (((a + 1 : ℕ) : ℝ) * den_lo) / den_hi := by
          have := haR.ne'
          have := hdhiR.ne'
          push_cast
          field_simp
        rw [div_le_iff₀ haR, heq, le_div_iff₀ hdhiR]
        exact h1
      exact h2.trans (by gcongr)
    have hlog := log_le_log (div_pos hbR haR) hrat
    rw [log_div hbR.ne' haR.ne', log_mul (div_pos hdloR hdhiR).ne' (by positivity), log_div hdloR.ne' hdhiR.ne'] at hlog
    have hl1p : log (1 + 1 / (a_lo : ℝ)) ≤ (cdiv S9 a_lo : ℝ) / S9 := by
      refine (log_le_sub_one_of_pos (by positivity)).trans (le_cdiv_S9 ha_pos ?_)
      have : (a_lo : ℝ) ≠ 0 := by positivity
      have := hS9.ne'
      field_simp
      linarith
    have hsub : (logUb9 den_lo : ℝ) - logLb9 den_hi ≤ ((logUb9 den_lo - logLb9 den_hi : ℕ) : ℝ) :=
      if h : logLb9 den_hi ≤ logUb9 den_lo then by rw [Nat.cast_sub h]
      else by
        rw [Nat.sub_eq_zero_of_le (by omega)]
        push_cast
        linarith [show (logUb9 den_lo : ℝ) < logLb9 den_hi from mod_cast not_le.mp h]
    have hd1 := div_le_div_of_nonneg_right hsub hS9.le
    rw [sub_div] at hd1
    push_cast
    rw [add_div]
    linarith [(log_bds hd_lo).2, (log_bds hd_hi).1]
@[category API, AMS 11] lemma tail_above {M_top n lo : ℕ} (hM : 0 < M_top) (hlo : n / M_top ≤ lo) :
    ∑ p ∈ (Ioc lo n).filter Nat.Prime, (harmonic (n / p) : ℚ) / p =
      ∑ m ∈ Icc 1 (M_top - 1), ((1 : ℚ) / m) * ∑ p ∈ (Ioc lo (n / m)).filter Nat.Prime, (1 : ℚ) / p := by
  have hterm : ∀ p ∈ (Ioc lo n).filter Nat.Prime, (harmonic (n / p) : ℚ) / p =
      ∑ m ∈ Icc 1 (M_top - 1), if p ≤ n / m then ((1 : ℚ) / m) * ((1 : ℚ) / p) else 0 := fun p hp => by
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    obtain ⟨hp_gt, _⟩ := mem_Ioc.mp hpI
    have hq_lt : n / p < M_top := by
      by_contra hge
      have := (Nat.le_div_iff_mul_le hM).mpr
        (mul_comm p M_top ▸ (Nat.mul_le_mul_right p (not_lt.mp hge)).trans (Nat.div_mul_le_self n p))
      omega
    have hflt : (Icc 1 (M_top - 1)).filter (fun m => p ≤ n / m) = Icc 1 (n / p) := by
      ext m
      simp only [mem_filter, mem_Icc]
      exact ⟨fun ⟨⟨h1, _⟩, hd⟩ => ⟨h1, (Nat.le_div_iff_mul_le hpP.pos).mpr
          (mul_comm m p ▸ (Nat.le_div_iff_mul_le (by omega)).mp hd)⟩,
        fun ⟨h1, hm⟩ => ⟨⟨h1, by omega⟩, (Nat.le_div_iff_mul_le (by omega)).mpr
          (mul_comm p m ▸ (Nat.le_div_iff_mul_le hpP.pos).mp hm)⟩⟩
    rw [harmonic_eq_sum_Icc, sum_div, ← sum_filter, hflt]
    exact sum_congr rfl fun _ _ => by simp [div_eq_mul_inv]
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_filter, mul_sum]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc]
  have := Nat.div_le_self n m
  exact ⟨fun ⟨⟨⟨h1, _⟩, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨⟨h1, by omega⟩, h2⟩, h3⟩⟩
@[category API, AMS 11] lemma pred_mul_le {A B : ℕ} (hA : 1 ≤ A) :
    ∑ x ∈ Ioc A B, (1 : ℝ) / (((x - 1 : ℕ) : ℝ) * x) ≤ 1 / A := by
  by_cases hAB : A ≤ B
  · suffices ∑ x ∈ Ioc A B, (1 : ℝ) / (((x - 1 : ℕ) : ℝ) * x) = 1 / (A : ℝ) - 1 / B by
      linarith [show (0 : ℝ) ≤ 1 / B by positivity]
    induction B, hAB using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [sum_Ioc_succ_top hk, ih, Nat.add_sub_cancel]
      have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast
      field_simp
      ring
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity
@[category API, AMS 11] lemma sq_above_le {L n : ℕ} (hL : 1 ≤ L) :
    ((∑ p ∈ (Ioc L n).filter (fun p => p.Prime ∧ p * p ≤ n),
      harmonic (n / (p * p)) / ((p * p : ℕ) : ℚ)) : ℝ) ≤
      if n / ((L + 1) * (L + 1)) = 0 then 0 else (harmonic (n / ((L + 1) * (L + 1))) : ℝ) / L := by
  have hsq_inv : ∑ x ∈ Ioc L n, (1 : ℝ) / ((x : ℝ) * x) ≤ 1 / L := by
    refine (sum_le_sum fun x hx => ?_).trans (pred_mul_le hL)
    have hx2 : 2 ≤ x := by
      have := (mem_Ioc.mp hx).1
      omega
    have hpos : (0 : ℝ) < ((x - 1 : ℕ) : ℝ) * x := by
      have : 0 < x - 1 := by omega
      positivity
    exact one_div_le_one_div_of_le hpos (by
      have : ((x - 1 : ℕ) : ℝ) ≤ x := mod_cast Nat.sub_le x 1
      nlinarith)
  split_ifs with hz
  · have hemp : (Ioc L n).filter (fun p => p.Prime ∧ p * p ≤ n) = ∅ :=
      filter_eq_empty_iff.mpr fun p hp ⟨_, hpp⟩ => by
        have hpL : L + 1 ≤ p := (mem_Ioc.mp hp).1
        have : 1 ≤ n / ((L + 1) * (L + 1)) :=
          (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith [Nat.mul_le_mul hpL hpL])
        omega
    rw [hemp]
    simp
  · push_cast
    set H := (harmonic (n / ((L + 1) * (L + 1))) : ℝ)
    have hH : 0 ≤ H := Rat.cast_nonneg.mpr (harm_nn _)
    refine (sum_le_sum (g := fun p : ℕ => H * (1 / ((p : ℝ) * p))) fun p hp => ?_).trans ?_
    · have hpL : L + 1 ≤ p := (mem_Ioc.mp (mem_filter.mp hp).1).1
      exact (div_le_div_of_nonneg_right
        (Rat.cast_le.mpr (harm_mono.monotone (Nat.div_le_div_left (Nat.mul_le_mul hpL hpL) (by positivity))))
        (by positivity)).trans_eq (div_eq_mul_one_div H ((p : ℝ) * p))
    · rw [← mul_sum]
      have hsub := (sum_le_sum_of_subset_of_nonneg
        (filter_subset (fun p => p.Prime ∧ p * p ≤ n) (Ioc L n)) fun _ _ _ => by positivity).trans hsq_inv
      linarith [mul_le_mul_of_nonneg_left hsub hH, show H * (1 / (L : ℝ)) = H / L by ring]
def cStep (p q : ℕ) : Bool := Nat.ble p q || !Nat.beq (p % q) 0
def candPrime (p : ℕ) : Bool :=
  cStep p 3 && cStep p 5 && cStep p 7 && cStep p 11 && cStep p 13 &&
  cStep p 17 && cStep p 19 && cStep p 23 && cStep p 29 && cStep p 31 &&
  cStep p 37 && cStep p 41 && cStep p 43 && cStep p 47 && cStep p 53 &&
  cStep p 59 && cStep p 61 && cStep p 67 && cStep p 71 && cStep p 73 &&
  cStep p 79 && cStep p 83 && cStep p 89 && cStep p 97 && cStep p 101 &&
  cStep p 103 && cStep p 107 && cStep p 109 && cStep p 113 && cStep p 127 &&
  cStep p 131 && cStep p 137
def oddSum (lo hi : ℕ) (f : ℕ → ℕ) : ℕ :=
  if Nat.ble hi lo then 0 else
    let b := lo / 2
    let d := (hi / 2 - b).log2 + 1
    treeSum (fun j =>
      let p := 2 * j + 1
      if Nat.blt lo p && Nat.ble p hi && candPrime p then f p else 0) d b
@[category API, AMS 11] lemma oddSum_ok {lo hi : ℕ} {P : ℕ → Prop} [DecidablePred P]
    {g : ℕ → ℝ} {f : ℕ → ℕ} (hlo : 2 ≤ lo) (hP : ∀ p, P p → p.Prime)
    (hg : ∀ p ∈ (Ioc lo hi).filter P, g p ≤ (f p : ℝ) / S9) :
    ∑ p ∈ (Ioc lo hi).filter P, g p ≤ (oddSum lo hi f : ℝ) / S9 := by
  have hcand {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) : cStep p q = true := by
    simp only [cStep, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.ble_eq, Nat.beq_eq]
    by_cases hdv : p % q = 0
    · have h1 := hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hdv)
      exact Or.inl (by omega)
    · exact Or.inr hdv
  have hS9_nn : (0 : ℝ) ≤ S9 := by
    unfold S9
    norm_num
  unfold oddSum
  split_ifs with hble
  · rw [Ioc_eq_empty (by
      have := Nat.ble_eq.mp hble
      omega)]
    simp
  · dsimp only []
    set b := lo / 2
    set d := (hi / 2 - b).log2 + 1
    refine (sum_le_sum hg).trans ?_
    rw [← sum_div, ← Nat.cast_sum]
    refine div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) hS9_nn
    rw [treeSum_Ico]
    have hhi_lt : hi / 2 - b < 2 ^ d := by
      dsimp [d]
      rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self (by decide) _
    let tf p := if Nat.blt lo p && Nat.ble p hi && candPrime p then f p else 0
    have hinj : ∀ x ∈ Ico b (b + 2 ^ d), ∀ y ∈ Ico b (b + 2 ^ d), 2 * x + 1 = 2 * y + 1 → x = y :=
      fun _ _ _ _ h => by omega
    rw [(sum_image (f := tf) (g := (2 * · + 1)) hinj).symm]
    refine (sum_congr rfl fun p hp => ?_).trans_le (sum_le_sum_of_subset fun p hp => ?_)
    · obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
      obtain ⟨hgt, hle⟩ := mem_Ioc.mp hpI
      dsimp [tf]
      rw [if_pos (by simp [Nat.blt_eq, Nat.ble_eq, hgt, hle, candPrime, hcand (hP p hpP)])]
    · obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
      obtain ⟨hgt, hle⟩ := mem_Ioc.mp hpI
      have := (hP p hpP).eq_two_or_odd.resolve_left (by omega)
      have := Nat.div_le_div_right (c := 2) hgt.le
      have := Nat.div_le_div_right (c := 2) hle
      exact mem_image.mpr ⟨p / 2, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
@[category API, AMS 11] lemma qaOdd_four {n n_lo M q a : ℕ}
    (hq3 : 3 ≤ q) (hqM : q ≤ M) (hn_lo_pos : 0 < n_lo) (hn_lo : n_lo ≤ n) (hc : q ^ a * 2 ^ Nat.log 2 q ≤ n) :
    (qaOdd n q a : ℝ) ≤ (4 * (M : ℝ)) / n_lo := by
  unfold qaOdd
  dsimp only []
  rw [Nat.add_sub_cancel, if_pos hc]
  set s := Nat.log 2 (n / q ^ a)
  have hqa_pos : 0 < q ^ a := pow_pos (by omega) a
  have hs_gt : n / q ^ a + 1 ≤ 2 * 2 ^ s := by
    have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n / q ^ a)
    rw [pow_succ'] at hlt
    dsimp [s]
    omega
  have hden_ge : n_lo ≤ 2 * (q ^ a * 2 ^ s) := by
    have := Nat.div_add_mod n (q ^ a)
    have := Nat.mod_lt n hqa_pos
    exact (show n_lo ≤ q ^ a * (n / q ^ a + 1) by
      rw [mul_add, mul_one]
      omega).trans ((Nat.mul_le_mul_left _ hs_gt).trans_eq (by ring))
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
    div_le_div_iff₀ (Nat.cast_pos.mpr (Nat.mul_pos hqa_pos (Nat.two_pow_pos s))) (Nat.cast_pos.mpr hn_lo_pos)]
  have h2M : 2 ^ (Nat.log 2 q + 1) - 1 ≤ 2 * M := by
    have := Nat.pow_log_le_self 2 (by omega : q ≠ 0)
    rw [pow_succ']
    omega
  nlinarith [show ((2 ^ (Nat.log 2 q + 1) - 1 : ℕ) : ℝ) ≤ 2 * M from mod_cast h2M,
    show (n_lo : ℝ) ≤ 2 * ((q ^ a * 2 ^ s : ℕ) : ℝ) from mod_cast hden_ge]
@[category API, AMS 11] lemma qaOdd_pow {n q a : ℕ} {K : ℝ}
    (hq3 : 3 ≤ q) (hK2 : 2 ≤ K) (hharm : ∀ m < q, (harmonic m : ℝ) ≤ K) :
    (qaOdd n q a : ℝ) ≤ K * (1 / (q : ℝ) ^ a) := by
  unfold qaOdd
  dsimp only []
  rw [Nat.add_sub_cancel]
  have hpow_le_q : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  split_ifs with hc
  · have hqa_pos : 0 < q ^ a := pow_pos (by omega) a
    have hs_ge : Nat.log 2 q ≤ Nat.log 2 (n / q ^ a) :=
      Nat.le_log_of_pow_le (by decide) ((Nat.le_div_iff_mul_le hqa_pos).mpr (Nat.mul_comm _ _ ▸ hc))
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
    refine (div_le_div₀ (Nat.cast_nonneg _)
      (Nat.cast_le.mpr (show 2 ^ (Nat.log 2 q + 1) - 1 ≤ 2 * 2 ^ Nat.log 2 q by
        rw [pow_succ']
        omega))
      (Nat.cast_pos.mpr (Nat.mul_pos hqa_pos (Nat.two_pow_pos _)))
      (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hs_ge)))).trans ?_
    have : (2 : ℝ) ^ Nat.log 2 q ≠ 0 := by positivity
    have : (q : ℝ) ^ a ≠ 0 := pow_ne_zero a (Nat.cast_ne_zero.mpr (by omega))
    have hcancel : ((2 * 2 ^ Nat.log 2 q : ℕ) : ℝ) / ((q ^ a * 2 ^ Nat.log 2 q : ℕ) : ℝ) = 2 * (1 / (q : ℝ) ^ a) := by
      push_cast
      field_simp
    rw [hcancel]
    gcongr
  · rw [Rat.cast_div, Rat.cast_natCast, Nat.cast_pow, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hharm _ (Nat.div_lt_of_lt_mul
      (by linarith [(not_le.mp hc).trans_le (Nat.mul_le_mul_left _ hpow_le_q)]))) (by positivity)
def qaTermUb9 (n_lo n_hi qa kq : ℕ) : ℕ :=
  let v1 := cdiv (((1 <<< kq) - 1) * S9) (qa * (1 <<< (n_lo / qa).log2))
  let v2 := cdiv (hCeil9 (n_hi / qa)) qa
  if Nat.ble (qa * (1 <<< (kq - 1))) n_lo then v1
  else if Nat.blt n_hi (qa * (1 <<< (kq - 1))) then v2 else max v1 v2
def qaSmallUb9 (n_lo n_hi M_lim : ℕ) : ℕ :=
  let hi := n_hi.log2 + 1
  oddSum 2 M_lim fun q =>
    let a0 := if Nat.beq q 3 then 3 else if Nat.beq q 5 then 2 else 1
    let fq := q.log2
    treeSum (fun i =>
      let a := a0 + i
      if Nat.ble (a * fq) hi then
        let qa := q ^ a
        if Nat.ble qa n_hi then qaTermUb9 n_lo n_hi qa (fq + 1) else 0
      else 0) ((hi / fq).log2 + 1) 0
@[category API, AMS 11] lemma harm_div_le {n n_hi d : ℕ} (hd : 0 < d) (hn : n ≤ n_hi) :
    (harmonic (n / d) : ℝ) / d ≤ (cdiv (hCeil9 (n_hi / d)) d : ℝ) / S9 :=
  le_cdiv_S9 hd ((div_le_div_of_nonneg_right
    ((Rat.cast_le.mpr (harm_mono.monotone (Nat.div_le_div_right hn))).trans (hCeil9_ok _))
    (Nat.cast_nonneg _)).trans (by rw [div_div, mul_comm (S9 : ℝ)]))
@[category API, AMS 11] lemma qaSmall_ok {n n_lo n_hi M_lim : ℕ} (hn_lo : n_lo ≤ n) (hn_hi : n ≤ n_hi) :
    ((∑ q ∈ (Icc 3 M_lim).filter Nat.Prime,
      ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), qaOdd n q a) : ℝ) ≤ (qaSmallUb9 n_lo n_hi M_lim : ℝ) / S9 := by
  have hS9 : (0 : ℝ) < S9 := by
    unfold S9
    norm_num
  have hterm {q a : ℕ} (hq3 : 3 ≤ q) : (qaOdd n q a : ℝ) ≤ (qaTermUb9 n_lo n_hi (q ^ a) (q.log2 + 1) : ℝ) / S9 := by
    have hkq_eq : q.log2 + 1 = Nat.log 2 q + 1 := by rw [Nat.log2_eq_log_two]
    have hqa_pos : 0 < q ^ a := pow_pos (by omega) a
    set v1 := cdiv (((1 <<< (q.log2 + 1)) - 1) * S9) (q ^ a * (1 <<< (n_lo / q ^ a).log2))
    set v2 := cdiv (hCeil9 (n_hi / q ^ a)) (q ^ a)
    have hv1 (hc : q ^ a * 2 ^ (Nat.log 2 q + 1 - 1) ≤ n) : (qaOdd n q a : ℝ) ≤ (v1 : ℝ) / S9 := by
      unfold qaOdd
      dsimp only []
      rw [if_pos hc]
      have hden_pos : 0 < q ^ a * (1 <<< (n_lo / q ^ a).log2) := by
        rw [Nat.shiftLeft_eq, one_mul]
        exact Nat.mul_pos hqa_pos (Nat.two_pow_pos _)
      have hden_le : q ^ a * (1 <<< (n_lo / q ^ a).log2) ≤ q ^ a * 2 ^ Nat.log 2 (n / q ^ a) := by
        rw [Nat.shiftLeft_eq, one_mul, Nat.log2_eq_log_two]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.log_mono_right (Nat.div_le_div_right hn_lo)))
      apply le_cdiv_S9 hden_pos
      rw [show (1 <<< (q.log2 + 1)) - 1 = 2 ^ (Nat.log 2 q + 1) - 1 by rw [hkq_eq, Nat.shiftLeft_eq, one_mul],
        Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
      refine (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr hden_pos) (Nat.cast_le.mpr hden_le)).trans ?_
      have := hS9.ne'
      push_cast
      field_simp
      exact le_rfl
    have hv2 (hc : ¬ (q ^ a * 2 ^ (Nat.log 2 q + 1 - 1) ≤ n)) : (qaOdd n q a : ℝ) ≤ (v2 : ℝ) / S9 := by
      unfold qaOdd
      dsimp only []
      rw [if_neg hc, Rat.cast_div, Rat.cast_natCast]
      exact harm_div_le hqa_pos hn_hi
    unfold qaTermUb9
    dsimp only []
    split_ifs with hble hblt
    · refine hv1 (le_trans ?_ hn_lo)
      have := Nat.ble_eq.mp hble
      rwa [hkq_eq, Nat.shiftLeft_eq, one_mul] at this
    · refine hv2 fun hc => not_lt.mpr (hc.trans hn_hi) ?_
      have := Nat.blt_eq.mp hblt
      rwa [hkq_eq, Nat.shiftLeft_eq, one_mul] at this
    · exact if hc : q ^ a * 2 ^ (Nat.log 2 q + 1 - 1) ≤ n then
        (hv1 hc).trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_max_left _ _)) hS9.le)
      else (hv2 hc).trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_max_right _ _)) hS9.le)
  have hIeq : (Icc 3 M_lim).filter Nat.Prime = (Ioc 2 M_lim).filter Nat.Prime := by
    ext
    simp only [mem_filter, mem_Icc, mem_Ioc]
    exact and_congr_left' ⟨by omega, by omega⟩
  rw [hIeq]
  unfold qaSmallUb9
  set hi := n_hi.log2 + 1
  refine oddSum_ok (by decide) (fun _ h => h) fun q hq => ?_
  obtain ⟨hqI, _⟩ := mem_filter.mp hq
  obtain ⟨hq2, _⟩ := mem_Ioc.mp hqI
  set a0 := if Nat.beq q 3 then 3 else if Nat.beq q 5 then 2 else 1
  have ha0 : a0 = tgtExp q + 1 := by
    dsimp [a0]
    unfold tgtExp
    by_cases h3 : q = 3
    · subst h3
      decide
    · by_cases h5 : q = 5
      · subst h5
        decide
      · have hb3 : Nat.beq q 3 = false := Bool.eq_false_iff.mpr (h3 ∘ Nat.beq_eq.mp)
        have hb5 : Nat.beq q 5 = false := Bool.eq_false_iff.mpr (h5 ∘ Nat.beq_eq.mp)
        simp [hb3, hb5, show q ≠ 2 by omega, h3, h5]
  let leaf i :=
    let a := a0 + i
    if Nat.ble (a * q.log2) hi then
      let qa := q ^ a
      if Nat.ble qa n_hi then qaTermUb9 n_lo n_hi qa (q.log2 + 1) else 0
    else 0
  change ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), (qaOdd n q a : ℝ) ≤
    (treeSum leaf ((hi / q.log2).log2 + 1) 0 : ℝ) / S9
  rw [treeSum_Ico, zero_add]
  have hafq_lt {a : ℕ} (ha : a ∈ Icc (tgtExp q + 1) (Nat.log q n)) : q ^ a ≤ n_hi ∧ a * q.log2 < hi := by
    obtain ⟨_, ha_hi⟩ := mem_Icc.mp ha
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at ha_hi
      omega
    have hqa_le : q ^ a ≤ n_hi := ((Nat.pow_le_pow_right (by omega) ha_hi).trans (Nat.pow_log_le_self q hn0)).trans hn_hi
    refine ⟨hqa_le, ?_⟩
    by_contra hge
    have hpow1 : 2 ^ hi ≤ q ^ a := (Nat.pow_le_pow_right (by decide) (not_lt.mp hge)).trans
      (by
        rw [mul_comm, pow_mul, Nat.log2_eq_log_two]
        exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) a)
    have hpow2 : n_hi < 2 ^ hi := by
      dsimp [hi]
      rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self (by decide) n_hi
    omega
  refine (sum_le_sum (g := fun a => (leaf (a - a0) : ℝ) / S9) fun a ha => ?_).trans ?_
  · obtain ⟨hqa_le, hafq⟩ := hafq_lt ha
    have ha_lo := (mem_Icc.mp ha).1
    dsimp only [leaf]
    rw [show a0 + (a - a0) = a by omega, if_pos (Nat.ble_eq.mpr hafq.le), if_pos (Nat.ble_eq.mpr hqa_le)]
    exact hterm (by omega)
  · have hinj : ∀ x ∈ Icc (tgtExp q + 1) (Nat.log q n),
        ∀ y ∈ Icc (tgtExp q + 1) (Nat.log q n), x - a0 = y - a0 → x = y := fun x hx y hy h => by
      have := (mem_Icc.mp hx).1
      have := (mem_Icc.mp hy).1
      omega
    rw [(sum_image (f := fun i => (leaf i : ℝ) / S9) hinj).symm, ← sum_div, ← Nat.cast_sum]
    refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (sum_le_sum_of_subset fun i hi_mem => ?_)) hS9.le
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hi_mem
    have hfq_pos : 0 < q.log2 := Nat.log2_eq_log_two ▸ Nat.le_log_of_pow_le (by decide) (by omega : 2 ^ 1 ≤ q)
    have hai : a - a0 ≤ hi / q.log2 := (Nat.sub_le a a0).trans ((Nat.le_div_iff_mul_le hfq_pos).mpr (hafq_lt ha).2.le)
    have hlt_pow : hi / q.log2 < 2 ^ ((hi / q.log2).log2 + 1) := by
      have h : (hi / q.log2).log2 = Nat.log 2 (hi / q.log2) := Nat.log2_eq_log_two
      rw [h]
      exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) (hi / q.log2)
    exact mem_Ico.mpr ⟨Nat.zero_le _, hai.trans_lt hlt_pow⟩
def AutoInv (G : Gadget) (M D A B : ℕ) : Prop :=
  G.M = M ∧ G.D = D ∧ G.A = A ∧ G.B = B ∧ (A : ℚ) = G.eta * D
def qPart (D q : ℕ) : ℕ → ℕ
  | 0 => q
  | k + 1 => if Nat.blt q 2 then q else if Nat.beq (D % q) 0 then q * qPart (D / q) q k else q
def cycShift (q bs r : ℕ) : ℕ := ((bs <<< r) ||| (bs >>> (q - r))) &&& ((1 <<< q) - 1)
def gLoop (D q : ℕ) : List ℕ → ℕ → List ℕ → ℕ × List ℕ
  | [], bs, acc => (bs, acc)
  | m :: ms, bs, acc =>
    let bs' := bs ||| cycShift q bs (((D * q) / m) % q)
    if Nat.beq bs' bs then gLoop D q ms bs acc else gLoop D q ms bs' (m :: acc)
def pickTq (M D q : ℕ) : Option (List ℕ) :=
  let qs := max 1 (qPart D q 12)
  let top := M / qs
  let cands := ((List.range (min top 24)).map fun i => (top - i) * qs).filter fun m =>
    Nat.ble 1 m && Nat.ble m M && Nat.beq ((D * q) % m) 0 && !Nat.beq (D % m) 0
  let (bs, acc) := gLoop D q cands 1 []
  if Nat.beq bs ((1 <<< q) - 1) then some acc else none
@[category API, AMS 11] lemma pickTq_ok {M D q : ℕ} {tq : List ℕ} (hq : 2 ≤ q) (hp : pickTq M D q = some tq) :
    tq.Nodup ∧ (∀ m ∈ tq, 1 ≤ m ∧ m ≤ M ∧ m ∣ D * q ∧ ¬ m ∣ D) ∧
      (∀ j < q, ∃ U ⊆ tq.toFinset, (∑ m ∈ U, (D * q) / m) % q = j) := by
  have hcyc {bs : ℕ} {T : Finset ℕ} {m : ℕ} (hm : m ∉ T) (hhi : ∀ k ≥ q, bs.testBit k = false)
      (hlo : ∀ j < q, bs.testBit j = true → ∃ U ⊆ T, (∑ x ∈ U, (D * q) / x) % q = j) :
      let bs' := bs ||| cycShift q bs (((D * q) / m) % q)
      (∀ k ≥ q, bs'.testBit k = false) ∧
        (∀ j < q, bs'.testBit j = true → ∃ U ⊆ insert m T, (∑ x ∈ U, (D * q) / x) % q = j) := by
    dsimp only []
    refine ⟨fun k hk => ?_, fun j hj hbit => ?_⟩
    · rw [Nat.testBit_or, hhi k hk, Bool.false_or, cycShift, Nat.testBit_and,
        show (1 <<< q) = 2 ^ q by simp [Nat.shiftLeft_eq], Nat.testBit_two_pow_sub_one, decide_eq_false (by omega), Bool.and_false]
    · rw [Nat.testBit_or, Bool.or_eq_true] at hbit
      rcases hbit with hb | hc
      · obtain ⟨U, hU, hs⟩ := hlo j hj hb
        exact ⟨U, hU.trans (subset_insert m T), hs⟩
      · set r := ((D * q) / m) % q
        have hr_lt : r < q := Nat.mod_lt _ (by omega)
        rw [cycShift, Nat.testBit_and, Bool.and_eq_true, Nat.testBit_or, Bool.or_eq_true] at hc
        rcases hc.1 with hshL | hshR
        · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hshL
          obtain ⟨U, hU, hs⟩ := hlo (j - r) (by omega) hshL.2
          refine ⟨insert m U, insert_subset_insert m hU, ?_⟩
          rw [sum_insert fun hx => hm (hU hx), Nat.add_mod, show ((D * q) / m) % q = r from rfl,
            hs, show r + (j - r) = j by omega, Nat.mod_eq_of_lt hj]
        · rw [Nat.testBit_shiftRight] at hshR
          obtain ⟨U, hU, hs⟩ := hlo (q - r + j)
            (by
              by_contra hge
              exact Bool.false_ne_true ((hhi _ (not_lt.mp hge)).symm.trans hshR)) hshR
          refine ⟨insert m U, insert_subset_insert m hU, ?_⟩
          rw [sum_insert fun hx => hm (hU hx), Nat.add_mod, show ((D * q) / m) % q = r from rfl,
            hs, show r + (q - r + j) = j + q * 1 by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  unfold pickTq at hp
  dsimp only [] at hp
  set qs := max 1 (qPart D q 12)
  set top := M / qs
  let P m := 1 ≤ m ∧ m ≤ M ∧ m ∣ D * q ∧ ¬ m ∣ D
  set cands := ((List.range (min top 24)).map fun i => (top - i) * qs).filter fun m =>
    Nat.ble 1 m && Nat.ble m M && Nat.beq ((D * q) % m) 0 && !Nat.beq (D % m) 0
  have hc_nd : cands.Nodup := List.Nodup.filter _ ((List.nodup_map_iff_inj_on List.nodup_range).mpr fun a ha b hb heq => by
    rw [List.mem_range] at ha hb
    have := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < qs) heq
    omega)
  have hc_P : ∀ m ∈ cands, P m := fun m hm => by
    simp only [cands, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq, Nat.beq_eq] at hm
    exact ⟨hm.2.1.1.1, hm.2.1.1.2, Nat.dvd_of_mod_eq_zero hm.2.1.2,
      fun hd => Bool.eq_false_iff.mp hm.2.2 (Nat.beq_eq.mpr (Nat.mod_eq_zero_of_dvd hd))⟩
  have hloop : ∀ (ms : List ℕ) (bs : ℕ) (acc : List ℕ), ms.Nodup → acc.Nodup →
      (∀ x ∈ ms, x ∉ acc) → (∀ x ∈ ms, P x) → (∀ x ∈ acc, P x) → (∀ k ≥ q, bs.testBit k = false) →
      (∀ j < q, bs.testBit j = true → ∃ U ⊆ acc.toFinset, (∑ x ∈ U, (D * q) / x) % q = j) →
      let (bs_f, acc_f) := gLoop D q ms bs acc
      acc_f.Nodup ∧ (∀ x ∈ acc_f, P x) ∧
        (∀ j < q, bs_f.testBit j = true → ∃ U ⊆ acc_f.toFinset, (∑ x ∈ U, (D * q) / x) % q = j) := by
    intro ms
    induction ms with
    | nil =>
      intro bs acc _ hnd _ _ hPa _ hlo
      exact ⟨hnd, hPa, hlo⟩
    | cons m ms ih =>
      intro bs acc hnd_m hnd_a hdisj hPm hPa hhi hlo
      obtain ⟨hm_ms, hnd_ms⟩ := List.nodup_cons.mp hnd_m
      have hm_acc : m ∉ acc := hdisj m List.mem_cons_self
      unfold gLoop
      dsimp only []
      split_ifs with heq
      · exact ih bs acc hnd_ms hnd_a (fun x hx => hdisj x (List.mem_cons_of_mem _ hx))
          (fun x hx => hPm x (List.mem_cons_of_mem _ hx)) hPa hhi hlo
      · obtain ⟨hhi', hlo'⟩ := hcyc (by simpa using hm_acc) hhi hlo
        exact ih _ (m :: acc) hnd_ms (List.nodup_cons.mpr ⟨hm_acc, hnd_a⟩)
          (fun x hx hmem => (List.mem_cons.mp hmem).elim (fun e => hm_ms (e ▸ hx)) (hdisj x (List.mem_cons_of_mem _ hx)))
          (fun x hx => hPm x (List.mem_cons_of_mem _ hx))
          (fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hPm m List.mem_cons_self) (hPa x))
          hhi' (by simpa [List.toFinset_cons] using hlo')
  have hinit := hloop cands 1 [] hc_nd List.nodup_nil (by simp) hc_P (by simp)
    (fun k hk => Nat.testBit_eq_false_of_lt (Nat.one_lt_pow (by omega) (by decide)))
    (fun j _ hbit => ⟨∅, empty_subset _, if hj0 : j = 0 then by
        subst hj0
        simp
      else absurd hbit (by simp [Nat.testBit_eq_false_of_lt (Nat.one_lt_pow hj0 (by decide))])⟩)
  rcases hg : gLoop D q cands 1 [] with ⟨bs, acc⟩
  rw [hg] at hp hinit
  dsimp only [] at hp hinit
  split_ifs at hp with hfull
  injection hp with hp_eq
  subst hp_eq
  refine ⟨hinit.1, hinit.2.1, fun j hj => hinit.2.2 j hj ?_⟩
  rw [Nat.beq_eq.mp hfull, show (1 <<< q) = 2 ^ q by simp [Nat.shiftLeft_eq], Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact hj
def autoStep (M R : ℕ) (st : ℕ × ℕ × ℕ) (q : ℕ) : ℕ × ℕ × ℕ :=
  let (D, A, B) := st
  if Nat.ble 2 q && Nat.ble q R && Nat.ble q M then
    match pickTq M D q with
    | none => st
    | some tq =>
      let s := (tq.map ((D * q) / ·)).sum
      if Nat.ble (q * A + s) (q * B) then (D * q, q * A + s, q * B) else st
  else st
def mkAutoSpec (M R : ℕ) : GSpec :=
  let st0 := if Nat.ble 60 M then (2520, 212, 8800) else if Nat.ble 36 M then (2520, 558, 8188) else (2520, 1340, 6985)
  let qs := [2, 2, 2, 2, 3, 3, 5, 5, 7] ++ (((List.range R).map (2 * · + 3)).filter fun p => Nat.ble p R && candPrime p).drop 3
  let (D, A, B) := qs.foldl (autoStep M R) st0
  { M := M, D := D, L := B + 1 - A, etaNum := A }
@[category API, AMS 11] lemma autoG (M R : ℕ) (hM : 21 ≤ M := by decide) : ∃ G, MatchSpec G (mkAutoSpec M R) := by
  have hastep {st : ℕ × ℕ × ℕ} {q : ℕ} (h : ∃ G, AutoInv G M st.1 st.2.1 st.2.2) :
      ∃ G', AutoInv G' M (autoStep M R st q).1 (autoStep M R st q).2.1 (autoStep M R st q).2.2 := by
    rcases st with ⟨D, A, B⟩
    obtain ⟨G, hGM, hGD, hGA, hGB, heta⟩ := h
    dsimp only [] at hGM hGD hGA hGB heta
    unfold autoStep
    dsimp only []
    split_ifs with hq_ok
    swap
    · exact ⟨G, hGM, hGD, hGA, hGB, heta⟩
    simp only [Bool.and_eq_true, Nat.ble_eq] at hq_ok
    rcases hq_ok with ⟨⟨hq2, _⟩, hqM⟩
    cases hp : pickTq M D q with
    | none => exact ⟨G, hGM, hGD, hGA, hGB, heta⟩
    | some tq =>
      dsimp only []
      set s := (tq.map ((D * q) / ·)).sum
      split_ifs with hAB_ok
      swap
      · exact ⟨G, hGM, hGD, hGA, hGB, heta⟩
      obtain ⟨hnd, hP, hreach⟩ := pickTq_ok hq2 hp
      set Tq := tq.toFinset
      have hs_eq : ∑ m ∈ Tq, (G.D * q) / m = s := hGD ▸ List.sum_toFinset ((D * q) / ·) hnd
      have hTq : ∀ m ∈ Tq, 1 ≤ m ∧ m ≤ M ∧ m ∣ G.D * q ∧ ¬ m ∣ G.D := fun m hm => hGD ▸ hP m (List.mem_toFinset.mp hm)
      have hDq_pos : 0 < D * q := Nat.mul_pos (hGD ▸ G.hD_pos) (by omega)
      have hTsumQ : ((s : ℕ) : ℚ) = (∑ m ∈ Tq, (1 : ℚ) / m) * ((D * q : ℕ) : ℚ) := by
        rw [← hs_eq, hGD, inv_dvd hDq_pos
          (fun m hm => ⟨(hP m (List.mem_toFinset.mp hm)).1, (hP m (List.mem_toFinset.mp hm)).2.2.1⟩),
          div_mul_cancel₀ _ (by positivity)]
      refine ⟨extendG G (by omega) hqM hGM hTq (by simpa [hGD] using hreach)
          (by
            rw [hs_eq, hGA, hGB]
            exact Nat.ble_eq.mp hAB_ok),
        rfl, by simp [extendG, hGD], by simp [extendG, hs_eq, hGA], by simp [extendG, hGB], ?_⟩
      dsimp only [extendG]
      rw [Nat.cast_add, Nat.cast_mul, hTsumQ, heta, Nat.cast_mul]
      ring
  have hsm {M₀} (h7 : 7 ≤ M₀) : ∀ p ∈ List.range (2520 + 1), p.Prime → 2520 % p = 0 → p ≤ M₀ := fun p _ hp hm => by
    rcases hp.dvd_mul.mp (Nat.dvd_of_mod_eq_zero hm : p ∣ 2 ^ 3 * (3 ^ 2 * (5 * 7))) with h2 | hrest
    · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow h2)).trans (by omega)
    rcases hp.dvd_mul.mp hrest with h3 | h57
    · exact (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow h3)).trans (by omega)
    exact (hp.dvd_mul.mp h57).elim (fun h5 => (Nat.le_of_dvd (by decide) h5).trans (by omega))
      fun h7' => (Nat.le_of_dvd (by decide) h7').trans (by omega)
  have hmk (M₀ A B : ℕ) (h7 : 7 ≤ M₀) (hAB : A ≤ B) (hle : M₀ ≤ M)
      (hc : chkRange (dpMask 2520 (divsLe M₀ 2520)) A (B - A + 1) = true)
      (he : (divsLe M₀ 2520).foldl (fun acc d => acc + 2520 / d) 0 = B + A) : ∃ G, AutoInv G M 2520 A B := by
    let G := mkDivG M₀ 2520 A B (by decide) hAB (hsm h7) hc he
    refine ⟨⟨M, G.D, G.S, G.A, G.B, G.eta, G.hD_pos, fun d hd => ?_,
      G.hS_dvd, fun p hp hd => (G.hD_smooth p hp hd).trans hle, G.hA_le_B, G.hcov, G.heta⟩,
      rfl, rfl, rfl, rfl, by
        dsimp [G, mkDivG]
        exact (div_mul_cancel₀ _ (by norm_num)).symm⟩
    obtain ⟨h1, h2⟩ := mem_Icc.mp (G.hS_sub hd)
    exact mem_Icc.mpr ⟨h1, h2.trans hle⟩
  let st0 := if Nat.ble 60 M then (2520, 212, 8800) else if Nat.ble 36 M then (2520, 558, 8188) else (2520, 1340, 6985)
  have hst0 : ∃ G, AutoInv G M st0.1 st0.2.1 st0.2.2 := by
    dsimp [st0]
    split_ifs with h60 h36
    · exact hmk 60 212 8800 (by decide) (by decide) (Nat.ble_eq.mp h60) (by decide) (by decide)
    · exact hmk 36 558 8188 (by decide) (by decide) (Nat.ble_eq.mp h36) (by decide) (by decide)
    · exact hmk 21 1340 6985 (by decide) (by decide) hM (by decide) (by decide)
  have hfold : ∀ (qs : List ℕ) (st : ℕ × ℕ × ℕ), (∃ G, AutoInv G M st.1 st.2.1 st.2.2) →
      ∃ G, AutoInv G M (qs.foldl (autoStep M R) st).1 (qs.foldl (autoStep M R) st).2.1 (qs.foldl (autoStep M R) st).2.2 := fun qs => by
    induction qs with
    | nil => exact fun _ h => h
    | cons _ _ ih => exact fun _ h => ih _ (hastep h)
  unfold mkAutoSpec
  dsimp only []
  let qs := [2, 2, 2, 2, 3, 3, 5, 5, 7] ++ (((List.range R).map (2 * · + 3)).filter fun p => Nat.ble p R && candPrime p).drop 3
  have hres := hfold qs st0 hst0
  rcases hf : qs.foldl (autoStep M R) st0 with ⟨D, A, B⟩
  rw [hf] at hres
  obtain ⟨G, hGM, hGD, hGA, hGB, heta⟩ := hres
  dsimp only [] at hGM hGD hGA hGB heta
  refine ⟨G, hGM, hGD, ?_, ?_⟩
  · dsimp
    rw [hGA, hGB]
  · dsimp
    exact le_of_eq ((eq_div_iff (Nat.cast_ne_zero.mpr (hGD ▸ G.hD_pos).ne')).mpr heta.symm)
def ValidPeel (n M_top M_bot : ℕ) (pickG : ℕ → Gadget) : Prop :=
  12 ≤ M_top ∧ M_top ≤ M_bot ∧ M_top * M_bot ≤ n ∧
  (∀ p, p.Prime → M_bot < p → p ≤ n / M_top →
    0 < (pickG p).M ∧ (pickG p).M ≤ M_bot ∧ p * (pickG p).M ≤ n ∧ (pickG p).A + p ≤ (pickG p).B + 1) ∧
  lossTail M_top n + lossSq M_bot n + lossPeel M_top M_bot n pickG + lossQA M_bot n ≤ 9921 / 10000
@[category API, AMS 11] lemma rep_W_peel {k M_top M_bot : ℕ}
    {pickG : ℕ → Gadget} (hk : 5 ≤ k) (hn : 11520 ≤ W k) (hv : ValidPeel (W k) M_top M_bot pickG) :
    IsRepresentable (W k) k := by
  obtain ⟨hlb, hub⟩ := harm_W_bds hk
  exact rep_sieve pickG hn (by omega) hv.1 hv.2.1 hv.2.2.1 (mod_cast hub) hv.2.2.2.1
    (hv.2.2.2.2.trans (Rat.cast_lt (K := ℝ).mp (by
      push_cast
      linarith)).le)
def pickG2 (n : ℕ) (G0 G1 : Gadget) (p : ℕ) : Gadget :=
  if p ≤ n / G1.M then G1 else G0
def peelOne9 (n_lo M_bot : ℕ) (s : GSpec) (p : ℕ) : ℕ :=
  cdiv ((s.etaNum + p - 1) * S9) (s.D * p * min M_bot (max 1 (n_lo / (p * s.M))))
def peelEx9 (n_lo n_hi M_bot : ℕ) (s0 s1 : GSpec) (p : ℕ) : ℕ :=
  max (if Nat.ble p (n_hi / s1.M) then peelOne9 n_lo M_bot s1 p else 0)
    (if Nat.blt (n_lo / s1.M) p && Nat.ble p (n_hi / s0.M) then peelOne9 n_lo M_bot s0 p else 0)
def pStep9 (n_lo n_hi M_bot B_peel : ℕ) (s : GSpec) (d nxt : ℕ) : ℕ :=
  let kp_lb := min M_bot (d / s.M)
  let u_lo := max B_peel (n_lo / nxt)
  let v_hi := max B_peel (n_hi / d)
  let pair := if Nat.ble B_peel (n_lo / nxt) && Nat.ble (9569 * d) (10386 * nxt) then
    (invDelta9 u_lo ((logUb9 nxt - logLb9 d) + cdiv S9 u_lo),
     cdiv ((10386 * nxt - 9569 * d) * n_hi * 100000) (d * nxt) + 956900000 +
       cdiv (344 * logUb9 v_hi) 10 + 4260000000 * isqrtUb v_hi)
  else (invUb9 u_lo v_hi, tDiff9 u_lo v_hi)
  cdiv (s.etaNum * pair.1) (s.D * kp_lb) + cdiv (pair.2 * S9) (logLb9 u_lo * s.D * kp_lb)
@[category API, AMS 11] lemma pStep9_ok {n n_lo n_hi M_bot B_peel d nxt : ℕ}
    {pickG : ℕ → Gadget} {G : Gadget} {s : GSpec}
    (hms : MatchSpec G s) (hsM2 : 2 ≤ s.M) (hsD0 : 0 < s.D) (hMb : 1 ≤ M_bot)
    (hB300 : 300 ≤ B_peel) (hn_lo : n_lo ≤ n) (hn_hi : n ≤ n_hi) (hdM : s.M ≤ d) (hd_nxt : d ≤ nxt)
    (hpick : ∀ p ∈ (Ioc (max B_peel (n / nxt)) (max B_peel (n / d))).filter Nat.Prime, pickG p = G) :
    ((∑ p ∈ (Ioc (max B_peel (n / nxt)) (max B_peel (n / d))).filter Nat.Prime,
      peelTerm M_bot n pickG p) : ℝ) ≤ (pStep9 n_lo n_hi M_bot B_peel s d nxt : ℝ) / S9 := by
  have hsM0 : 0 < s.M := by omega
  set u := max B_peel (n / nxt)
  set v := max B_peel (n / d)
  by_cases hv_le : n / d ≤ B_peel
  · rw [show u = v by simp [u, v, max_eq_left hv_le, max_eq_left ((Nat.div_le_div_left hd_nxt (by omega)).trans hv_le)], Ioc_self]
    simp only [filter_empty, sum_empty]
    positivity
  · have hv_eq : v = n / d := max_eq_right (not_le.mp hv_le).le
    have huv : u ≤ v := max_le_max le_rfl (Nat.div_le_div_left hd_nxt (by omega))
    set u_lo := max B_peel (n_lo / nxt)
    set v_hi := max B_peel (n_hi / d)
    have hulo_300 : 300 ≤ u_lo := hB300.trans (le_max_left _ _)
    have hulo_u : u_lo ≤ u := max_le_max le_rfl (Nat.div_le_div_right hn_lo)
    have hv_vhi : v ≤ v_hi := max_le_max le_rfl (Nat.div_le_div_right hn_hi)
    set kp_lb := min M_bot (d / s.M)
    have hkp_lb_pos : 0 < kp_lb := lt_min (by omega) ((Nat.le_div_iff_mul_le hsM0).mpr (by simpa))
    set P := (Ioc u v).filter Nat.Prime
    have hterm_le : ∀ p ∈ P, (peelTerm M_bot n pickG p : ℝ) ≤
        ((s.etaNum : ℝ) / ((s.D * kp_lb : ℕ) : ℝ)) * ((1 : ℝ) / p) + 1 / ((s.D * kp_lb : ℕ) : ℝ) := fun p hp => by
      obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
      obtain ⟨_, hp_le_v⟩ := mem_Ioc.mp hpI
      have hkp_ge : kp_lb ≤ min M_bot (n / (p * G.M)) := by
        rw [hms.1]
        exact min_le_min le_rfl ((Nat.le_div_iff_mul_le (Nat.mul_pos hpP.pos hsM0)).mpr
          ((by ring : (d / s.M) * (p * s.M) = p * ((d / s.M) * s.M)).trans_le
            ((Nat.mul_le_mul_left p (Nat.div_mul_le_self d s.M)).trans ((Nat.le_div_iff_mul_le (by omega)).mp (hv_eq ▸ hp_le_v)))))
      unfold peelTerm
      dsimp only []
      rw [hpick p hp, hms.2.1]
      set kp := min M_bot (n / (p * G.M))
      have hetaR : (G.eta : ℝ) ≤ (s.etaNum : ℝ) / s.D := by simpa using Rat.cast_le (K := ℝ).mpr hms.2.2.2
      have hkp_pos : (0 : ℝ) < kp := Nat.cast_pos.mpr (lt_of_lt_of_le hkp_lb_pos hkp_ge)
      have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hpP.pos
      have hsD_pos : (0 : ℝ) < s.D := Nat.cast_pos.mpr hsD0
      have hkplb_pos : (0 : ℝ) < kp_lb := Nat.cast_pos.mpr hkp_lb_pos
      push_cast
      rw [add_div]
      have hpartA : (G.eta : ℝ) / (p * kp) ≤ ((s.etaNum : ℝ) / (s.D * kp_lb)) * (1 / p) := by
        grw [hetaR]
        rw [div_div, show (s.D : ℝ) * (p * kp) = (s.D * kp) * p by ring, ← div_div, div_eq_mul_one_div]
        gcongr
      have hpartB : (((p - 1 : ℕ) : ℝ) / s.D) / (p * kp) ≤ 1 / (s.D * kp_lb) := by
        grw [Nat.sub_le p 1]
        have hpc : ((p : ℝ) / s.D) / (p * kp) = 1 / (s.D * kp) := by
          have := hp_pos.ne'
          field_simp
        rw [hpc]
        gcongr
      linarith
    unfold pStep9
    dsimp only []
    set cond := Nat.ble B_peel (n_lo / nxt) && Nat.ble (9569 * d) (10386 * nxt)
    set pair := if cond then
      (invDelta9 u_lo ((logUb9 nxt - logLb9 d) + cdiv S9 u_lo),
       cdiv ((10386 * nxt - 9569 * d) * n_hi * 100000) (d * nxt) + 956900000 +
         cdiv (344 * logUb9 v_hi) 10 + 4260000000 * isqrtUb v_hi)
    else (invUb9 u_lo v_hi, tDiff9 u_lo v_hi)
    have hpair : (∑ p ∈ P, (1 : ℝ) / p) ≤ (pair.1 : ℝ) / S9 ∧
        theta (v : ℝ) - theta (u : ℝ) ≤ (pair.2 : ℝ) / S9 := by
      dsimp only [pair]
      split_ifs with hc
      · simp only [cond, Bool.and_eq_true, Nat.ble_eq] at hc
        rcases hc with ⟨hB_nlo, hlin⟩
        have hu_eq : u = n / nxt := max_eq_right (hB_nlo.trans (Nat.div_le_div_right hn_lo))
        have hdlog := quot_log_sub_le (n := n) (a_lo := u_lo) (den_hi := d) (den_lo := nxt) (by omega) (by omega) (hu_eq ▸ hulo_u)
        rw [← hv_eq, ← hu_eq] at hdlog
        have hsinv := invDelta9_ok hulo_300 hulo_u huv hdlog
        push_cast at hsinv
        exact ⟨hsinv, slice_ub (by omega) huv hv_vhi (by omega) (by omega) hlin hn_hi hu_eq hv_eq⟩
      · dsimp only []
        have hsinv0 := invUb9_ok (a := u_lo) (b := v_hi) hulo_300
        push_cast at hsinv0
        have hsub_le : ∑ p ∈ P, (1 : ℝ) / p ≤ ∑ p ∈ (Ioc u_lo v_hi).filter Nat.Prime, (1 : ℝ) / p := by
          dsimp only [P]
          gcongr
        refine ⟨hsub_le.trans hsinv0, ?_⟩
        linarith [tDiff9_ok hulo_300 (hulo_u.trans (huv.trans hv_vhi)),
          theta_mono (Nat.cast_le.mpr hulo_u), theta_mono (Nat.cast_le.mpr hv_vhi)]
    have hlogu_n := logLb9_pos hulo_300
    have hS9 : (0 : ℝ) < S9 := by
      unfold S9
      norm_num
    have hlogu_ge := (log_bds (x := u_lo) (by omega)).1.trans (log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr hulo_u))
    have hcard_mul : (P.card : ℝ) * log u ≤ theta (v : ℝ) - theta (u : ℝ) := by
      simp only [theta, Nat.floor_natCast, sum_filter, ← sum_Ioc_consecutive _ (Nat.zero_le u) huv, add_sub_cancel_left]
      rw [← sum_filter, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun p hp => log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (mem_Ioc.mp (mem_filter.mp hp).1).1.le)
    have hcard_ub : (P.card : ℝ) ≤ (pair.2 : ℝ) / logLb9 u_lo := by
      have h1 := (mul_le_mul_of_nonneg_left hlogu_ge (Nat.cast_nonneg _)).trans (hcard_mul.trans hpair.2)
      rw [← mul_div_assoc] at h1
      exact (le_div_iff₀ (Nat.cast_pos.mpr hlogu_n)).mpr ((div_le_div_iff_of_pos_right hS9).mp h1)
    push_cast
    refine (sum_le_sum hterm_le).trans ?_
    rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one_div]
    have hp1 : ((s.etaNum : ℝ) / ((s.D * kp_lb : ℕ) : ℝ)) * (∑ p ∈ P, (1 : ℝ) / p) ≤
        (cdiv (s.etaNum * pair.1) (s.D * kp_lb) : ℝ) / S9 := by
      apply le_cdiv_S9 (Nat.mul_pos hsD0 hkp_lb_pos)
      have hm := mul_le_mul_of_nonneg_left hpair.1 (div_nonneg (Nat.cast_nonneg s.etaNum) (Nat.cast_nonneg (s.D * kp_lb)))
      push_cast at hm ⊢
      linarith [show ((s.etaNum : ℝ) / (s.D * kp_lb)) * (pair.1 / S9) = (s.etaNum * pair.1) / ((s.D * kp_lb) * S9) by ring]
    have hp2 : (P.card : ℝ) / ((s.D * kp_lb : ℕ) : ℝ) ≤
        (cdiv (pair.2 * S9) (logLb9 u_lo * s.D * kp_lb) : ℝ) / S9 := by
      apply le_cdiv_S9 (Nat.mul_pos (Nat.mul_pos hlogu_n hsD0) hkp_lb_pos)
      have hm := div_le_div_of_nonneg_right hcard_ub (Nat.cast_nonneg (s.D * kp_lb))
      push_cast at hm ⊢
      have heq : ((pair.2 : ℝ) / logLb9 u_lo) / (s.D * kp_lb) = (pair.2 * S9) / ((logLb9 u_lo * s.D * kp_lb) * S9) := by
        have := hS9.ne'
        field_simp
      linarith
    rw [add_div]
    linarith
def peelDenom (M M_next i : ℕ) : ℕ := min M_next (if Nat.blt i 15 then (i + 1) * M else M <<< (i - 11))
def pSum9 (n_lo n_hi M_bot B_peel M_next : ℕ) (s : GSpec) : ℕ :=
  treeSum (fun i =>
    let d := peelDenom s.M M_next i
    if Nat.ble M_next d || Nat.ble (n_hi / d) B_peel then 0
    else pStep9 n_lo n_hi M_bot B_peel s d (peelDenom s.M M_next (i + 1))) 8 0
@[category API, AMS 11] lemma pSum9_ok {n n_lo n_hi M_bot B_peel M_next : ℕ}
    {pickG : ℕ → Gadget} {G : Gadget} {s : GSpec}
    (hms : MatchSpec G s) (hsM2 : 2 ≤ s.M) (hsD0 : 0 < s.D) (hMb : 1 ≤ M_bot)
    (hB300 : 300 ≤ B_peel) (hn_lo : n_lo ≤ n) (hn_hi : n ≤ n_hi) (hM_next : s.M ≤ M_next) (hM_next_ub : M_next ≤ 2 ^ 245)
    (hpick_all : ∀ p ∈ (Ioc (max B_peel (n / M_next)) (max B_peel (n / s.M))).filter Nat.Prime, pickG p = G) :
    ((∑ p ∈ (Ioc (max B_peel (n / M_next)) (max B_peel (n / s.M))).filter Nat.Prime,
      peelTerm M_bot n pickG p) : ℝ) ≤ (pSum9 n_lo n_hi M_bot B_peel M_next s : ℝ) / S9 := by
  let d := peelDenom s.M M_next
  have hd0 : d 0 = s.M := by simp [d, peelDenom, hM_next]
  have hd_hi (i) : d i ≤ M_next := min_le_left _ _
  have hd256 : d 256 = M_next := by
    show min M_next (if Nat.blt 256 15 then 257 * s.M else s.M <<< 245) = M_next
    rw [if_neg (by decide), Nat.shiftLeft_eq]
    exact min_eq_left (hM_next_ub.trans (Nat.le_mul_of_pos_left _ (by omega)))
  have hd_lo (i) : s.M ≤ d i := le_min hM_next
    (if h : (Nat.blt i 15 : Bool) then by
       rw [if_pos h]
       exact Nat.le_mul_of_pos_left s.M (by omega)
     else by
       rw [if_neg h, Nat.shiftLeft_eq]
       exact Nat.le_mul_of_pos_right s.M (pow_pos (by decide) _))
  have hd_mono (i) : d i ≤ d (i + 1) := min_le_min le_rfl
    (if h14 : i < 14 then by
       rw [if_pos (Nat.blt_eq.mpr (by omega)), if_pos (Nat.blt_eq.mpr (by omega))]
       exact Nat.mul_le_mul_right s.M (by omega)
     else if heq14 : i = 14 then by
       subst heq14
       norm_num [Nat.blt_eq, Nat.shiftLeft_eq]
       omega
     else by
       have hn1 : ¬ (Nat.blt i 15 = true) := by
         rw [Nat.blt_eq]
         omega
       have hn2 : ¬ (Nat.blt (i + 1) 15 = true) := by
         rw [Nat.blt_eq]
         omega
       rw [if_neg hn1, if_neg hn2, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
       exact Nat.mul_le_mul_left s.M (Nat.pow_le_pow_right (by decide) (by omega)))
  let u i := max B_peel (n / d i)
  have hu_anti {i j} (hij : i ≤ j) : u j ≤ u i := max_le_max le_rfl
    (Nat.div_le_div_left (Nat.le_induction le_rfl (fun k _ ih => ih.trans (hd_mono k)) j hij)
      (lt_of_lt_of_le (by omega : 0 < s.M) (hd_lo i)))
  let term i := if Nat.ble M_next (d i) || Nat.ble (n_hi / d i) B_peel then 0
    else pStep9 n_lo n_hi M_bot B_peel s (d i) (d (i + 1))
  have hstep (i) : ((∑ p ∈ (Ioc (u (i + 1)) (u i)).filter Nat.Prime, peelTerm M_bot n pickG p) : ℝ) ≤ (term i : ℝ) / S9 := by
    dsimp only [term]
    by_cases hstop : (Nat.ble M_next (d i) || Nat.ble (n_hi / d i) B_peel) = true
    · have hemp : Ioc (u (i + 1)) (u i) = ∅ := by
        rcases Bool.or_eq_true_iff.mp hstop with hge | hdiv_le
        · have heq1 : d i = M_next := le_antisymm (hd_hi i) (Nat.ble_eq.mp hge)
          simp [u, heq1, le_antisymm (hd_hi (i + 1)) (heq1 ▸ hd_mono i)]
        · rw [show u i = B_peel from max_eq_left ((Nat.div_le_div_right hn_hi).trans (Nat.ble_eq.mp hdiv_le))]
          exact Ioc_eq_empty (not_lt.mpr (le_max_left _ _))
      rw [if_pos hstop, hemp]
      simp
    · rw [if_neg hstop]
      simpa [u] using pStep9_ok hms hsM2 hsD0 hMb hB300 hn_lo hn_hi (hd_lo i) (hd_mono i) fun p hp => by
        obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
        obtain ⟨h1, h2⟩ := mem_Ioc.mp hpI
        exact hpick_all p (mem_filter.mpr ⟨mem_Ioc.mpr
          ⟨lt_of_le_of_lt (max_le_max le_rfl (Nat.div_le_div_left (hd_hi (i + 1)) (lt_of_lt_of_le (by omega) (hd_lo (i + 1))))) h1,
            h2.trans (max_le_max le_rfl (Nat.div_le_div_left (hd_lo i) (by omega)))⟩, hpP⟩)
  have htel (k) : ((∑ p ∈ (Ioc (u k) (u 0)).filter Nat.Prime, peelTerm M_bot n pickG p) : ℝ) ≤
      ((∑ i ∈ Ico 0 k, term i : ℕ) : ℝ) / S9 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_filter, ← sum_Ioc_consecutive _ (hu_anti k.le_succ) (hu_anti k.zero_le),
        ← sum_filter, ← sum_filter, sum_Ico_succ_top k.zero_le, Nat.cast_add, add_div]
      linarith [hstep k]
  unfold pSum9
  rw [treeSum_Ico, zero_add, show (2 : ℕ) ^ 8 = 256 by norm_num]
  have h256 := htel 256
  dsimp [u] at h256
  rwa [hd256, hd0] at h256
def tailUb9 (n_lo n_hi B_ex M_top : ℕ) : ℕ :=
  let a_lo := n_lo / M_top
  oddSum a_lo (min n_hi B_ex) (fun p => cdiv (hCeil9 (n_hi / p)) p) +
    treeSum (fun m => if Nat.ble 1 m && Nat.blt m M_top then
      cdiv (if Nat.ble B_ex a_lo then invDelta9 a_lo ((logUb9 M_top - logLb9 m) + cdiv S9 a_lo)
            else invUb9 B_ex (n_hi / m)) m
      else 0) (M_top.log2 + 1) 0
def sqUb9 (n_hi B_ex M_bot : ℕ) : ℕ :=
  let B_peel := max M_bot B_ex
  let sq_q := n_hi / ((B_peel + 1) * (B_peel + 1))
  oddSum M_bot (min (isqrtUb n_hi) B_ex) (fun p => cdiv (hCeil9 (n_hi / (p * p))) (p * p)) +
    (if Nat.beq sq_q 0 then 0 else cdiv (hCeil9 sq_q) B_peel)
def peelUb9 (n_lo n_hi B_ex : ℕ) (s0 s1 : GSpec) : ℕ :=
  let M_top := s0.M
  let M_bot := s1.M
  let B_peel := max M_bot B_ex
  oddSum M_bot (min (n_hi / M_top) B_ex) (peelEx9 n_lo n_hi M_bot s0 s1) +
    pSum9 n_lo n_hi M_bot B_peel M_bot s0 + pSum9 n_lo n_hi M_bot B_peel (n_hi + 1) s1
def qaCompute (n_lo n_hi M_bot : ℕ) : ℕ := cdiv S9 256 + qaSmallUb9 n_lo n_hi M_bot
def rowUb9 (n_lo n_hi B_ex : ℕ) (s0 s1 : GSpec) : ℕ :=
  tailUb9 n_lo n_hi B_ex s0.M + sqUb9 n_hi B_ex s1.M + peelUb9 n_lo n_hi B_ex s0 s1 + qaCompute n_lo n_hi s1.M
def chkRow (k_lo k_hi n_lo n_hi B_ex : ℕ) (s0 s1 : GSpec) : Bool :=
  let M_top := s0.M
  let M_bot := s1.M
  let B_peel := max M_bot B_ex
  Nat.ble 5 k_lo && Nat.ble k_lo k_hi &&
  Nat.ble (n_lo * (10 ^ 9 * (10 ^ 10) ^ k_lo)) (1520136295 * 27182818283 ^ k_lo) &&
  Nat.ble (1520136299 * 27182818286 ^ k_hi) ((n_hi + 1) * (10 ^ 9 * (10 ^ 10) ^ k_hi)) &&
  Nat.ble 11520 n_lo && Nat.ble n_lo n_hi && Nat.blt n_hi (1 <<< 220) &&
  Nat.ble 12 s0.M && Nat.ble s0.M s1.M &&
  Nat.ble 300 B_ex && Nat.ble 2 (n_lo / M_top) && Nat.ble B_peel n_lo &&
  Nat.ble (M_top * M_bot) n_lo && Nat.ble 1 s0.D && Nat.ble 1 s1.D &&
  Nat.ble (n_hi / s0.M) s0.L && Nat.ble (n_hi / s1.M) s1.L &&
  Nat.ble (rowUb9 n_lo n_hi B_ex s0 s1) 992100000
@[category API, AMS 11] lemma chkRow_ok {k : ℕ} (k_lo k_hi n_lo n_hi B_ex : ℕ)
    {s0 s1 : GSpec} (h0 : ∃ G, MatchSpec G s0) (h1 : ∃ G, MatchSpec G s1)
    (hk_lo : k_lo ≤ k) (hk_hi : k ≤ k_hi)
    (hchk : chkRow k_lo k_hi n_lo n_hi B_ex s0 s1 = true := by decide) :
    IsRepresentable (W k) k := by
  rcases h0, h1 with ⟨⟨G0, h0⟩, ⟨G1, h1⟩⟩
  unfold chkRow at hchk
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, and_assoc] at hchk
  rcases hchk with ⟨hk5, _, hw_lb, hw_ub, hn11520, _, hnhi220, h12, hm01,
    hB300, halo2, hBpeel_nlo, hprod_nlo, hd0, hd1, hl0, hl1, htot⟩
  have hk3 : 3 ≤ k_lo := (by decide : 3 ≤ 5).trans hk5
  have hn_lo : n_lo ≤ W k := ((W_bds n_lo n_hi hk3).1 (Nat.ble_eq.mpr hw_lb)).trans (W_mono hk3 hk_lo)
  have hn_hi : W k ≤ n_hi := (W_mono (hk3.trans hk_lo) hk_hi).trans
    ((W_bds n_lo n_hi (hk3.trans (hk_lo.trans hk_hi))).2 (Nat.ble_eq.mpr hw_ub))
  have hnhi220_pow : n_hi < 2 ^ 220 := by rwa [Nat.shiftLeft_eq, one_mul] at hnhi220
  have hnh1_245 : n_hi + 1 ≤ 2 ^ 245 := (Nat.succ_le_of_lt hnhi220_pow).trans (Nat.pow_le_pow_right (by decide) (by decide))
  clear hw_lb hw_ub hnhi220 hnhi220_pow
  set n := W k
  refine rep_W_peel (M_top := s0.M) (M_bot := s1.M)
    (pickG := pickG2 n G0 G1) (by omega) (hn11520.trans hn_lo) ⟨h12, hm01, hprod_nlo.trans hn_lo, ?_, ?_⟩
  · have hgv {G s p} (hms : MatchSpec G s) (hM0 : 0 < s.M) (hMle : s.M ≤ s1.M) (hL : n / s.M ≤ s.L) (hp : p ≤ n / s.M) :
        0 < G.M ∧ G.M ≤ s1.M ∧ p * G.M ≤ n ∧ G.A + p ≤ G.B + 1 := by
      have := G.hA_le_B
      have := hms.2.2.1
      rw [hms.1]
      exact ⟨hM0, hMle, (Nat.le_div_iff_mul_le hM0).mp hp, by omega⟩
    intro p _ _ hp_le
    unfold pickG2
    rw [h1.1]
    split_ifs with c1
    · exact hgv h1 (by omega) le_rfl ((Nat.div_le_div_right hn_hi).trans hl1) c1
    · exact hgv h0 (by omega) hm01 ((Nat.div_le_div_right hn_hi).trans hl0) hp_le
  · have hS9_eq : (S9 : ℝ) = 1000000000 := by
      unfold S9
      norm_num
    have hS9 : (0 : ℝ) < S9 := by linarith
    suffices hR : (lossTail s0.M n : ℝ) + (lossSq s1.M n : ℝ) +
        (lossPeel s0.M s1.M n (pickG2 n G0 G1) : ℝ) + (lossQA s1.M n : ℝ) ≤ (992100000 : ℝ) / S9 from
      Rat.cast_le (K := ℝ).mp (by
        push_cast
        rw [hS9_eq] at hR
        linarith)
    have h1' : (lossTail s0.M n : ℝ) ≤ (tailUb9 n_lo n_hi B_ex s0.M : ℝ) / S9 := by
      have hMtop_pow : s0.M < 2 ^ (s0.M.log2 + 1) := Nat.log2_eq_log_two ▸ Nat.lt_pow_succ_log_self (by decide) _
      set a_lo := n_lo / s0.M
      set lo := max (n / s0.M) B_ex
      let tf m := if Nat.ble 1 m && Nat.blt m s0.M then
        cdiv (if Nat.ble B_ex a_lo then invDelta9 a_lo ((logUb9 s0.M - logLb9 m) + cdiv S9 a_lo)
              else invUb9 B_ex (n_hi / m)) m
        else 0
      set tail_ex := oddSum a_lo (min n_hi B_ex) (fun p => cdiv (hCeil9 (n_hi / p)) p)
      change (lossTail s0.M n : ℝ) ≤ ((tail_ex + treeSum tf (s0.M.log2 + 1) 0 : ℕ) : ℝ) / S9
      unfold lossTail
      rw [Nat.cast_add, add_div]
      push_cast
      have hB_le_n : B_ex ≤ n := ((le_max_right _ _).trans hBpeel_nlo).trans hn_lo
      have halo_ge : a_lo ≤ n / s0.M := Nat.div_le_div_right hn_lo
      rw [sum_filter, ← sum_Ioc_consecutive _ (le_max_left (n / s0.M) B_ex) (max_le (Nat.div_le_self n s0.M) hB_le_n),
        ← sum_filter, ← sum_filter]
      have htex : (∑ p ∈ (Ioc (n / s0.M) lo).filter Nat.Prime, (harmonic (n / p) : ℝ) / p) ≤ (tail_ex : ℝ) / S9 := by
        by_cases hBn : B_ex ≤ n / s0.M
        · rw [show lo = n / s0.M from max_eq_left hBn, Ioc_self]
          simp only [filter_empty, sum_empty]
          positivity
        · have hlo_le : lo ≤ min n_hi B_ex := (max_eq_right (by omega)).le.trans (le_min (hB_le_n.trans hn_hi) le_rfl)
          have hsub_le : (∑ p ∈ (Ioc (n / s0.M) lo).filter Nat.Prime, (harmonic (n / p) : ℝ) / p) ≤
              ∑ p ∈ (Ioc a_lo (min n_hi B_ex)).filter Nat.Prime, (harmonic (n / p) : ℝ) / p :=
            sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ioc_subset_Ioc halo_ge hlo_le))
              fun _ _ _ => div_nonneg (Rat.cast_nonneg.mpr (harm_nn _)) (Nat.cast_nonneg _)
          exact hsub_le.trans (oddSum_ok halo2 (fun _ h => h) fun p hp =>
            harm_div_le (mem_filter.mp hp).2.pos hn_hi)
      have htan : (∑ p ∈ (Ioc lo n).filter Nat.Prime, (harmonic (n / p) : ℝ) / p) ≤ (treeSum tf (s0.M.log2 + 1) 0 : ℝ) / S9 := by
        have habove := congrArg (Rat.cast (K := ℝ))
          (tail_above (M_top := s0.M) (n := n) (lo := lo) (by omega) (le_max_left _ _))
        push_cast at habove
        rw [habove, treeSum_Ico, zero_add]
        refine (sum_le_sum (g := fun m => (tf m : ℝ) / S9) fun m hm => ?_).trans ?_
        · obtain ⟨hm1, hm2⟩ := mem_Icc.mp hm
          dsimp only [tf]
          rw [if_pos (by
            simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
            omega)]
          apply le_cdiv_S9 (by omega)
          have hm_ne : (m : ℝ) ≠ 0 := by positivity
          split_ifs with hBa
          · have hBa' := Nat.ble_eq.mp hBa
            rw [show lo = n / s0.M from max_eq_left (hBa'.trans halo_ge)]
            have hsinv := invDelta9_ok (hB300.trans hBa') halo_ge
              (Nat.div_le_div_left (by omega : m ≤ s0.M) (by omega)) (quot_log_sub_le (den_hi := m) (by omega) (by omega) halo_ge)
            push_cast at hsinv
            refine (mul_le_mul_of_nonneg_left hsinv (by positivity)).trans ?_
            have := hS9.ne'
            field_simp
            exact le_rfl
          · have han_m := invUb9_ok (a := B_ex) (b := n_hi / m) hB300
            push_cast at han_m
            have hsub_le : ∑ p ∈ (Ioc lo (n / m)).filter Nat.Prime, (1 : ℝ) / p ≤
                ∑ p ∈ (Ioc B_ex (n_hi / m)).filter Nat.Prime, (1 : ℝ) / p := by
              have : B_ex ≤ lo := le_max_right _ _
              have : n / m ≤ n_hi / m := Nat.div_le_div_right hn_hi
              gcongr
            refine (mul_le_mul_of_nonneg_left (hsub_le.trans han_m) (by positivity)).trans ?_
            have := hS9.ne'
            field_simp
            exact le_rfl
        · rw [← sum_div, ← Nat.cast_sum]
          refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (sum_le_sum_of_subset fun m hm => ?_)) hS9.le
          have := (mem_Icc.mp hm).2
          exact mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩
      linarith
    have h2' : (lossSq s1.M n : ℝ) ≤ (sqUb9 n_hi B_ex s1.M : ℝ) / S9 := by
      set B_peel := max s1.M B_ex
      set sq_q := n_hi / ((B_peel + 1) * (B_peel + 1))
      unfold sqUb9 lossSq
      dsimp only []
      rw [Nat.cast_add, add_div, Rat.cast_sum, sum_filter,
        ← sum_Ioc_consecutive _ (le_max_left s1.M B_ex) (hBpeel_nlo.trans hn_lo), ← sum_filter, ← sum_filter]
      have hsq_u (m) : m ≤ isqrtUb m * isqrtUb m := by
        have := (isqrt_bds m).2
        have hsq := mul_le_mul this this (sqrt_nonneg _) (Nat.cast_nonneg _)
        rw [mul_self_sqrt (Nat.cast_nonneg _)] at hsq
        exact_mod_cast hsq
      have hsq_ex : (∑ p ∈ (Ioc s1.M B_peel).filter (fun p => p.Prime ∧ p * p ≤ n),
          ((harmonic (n / (p * p)) / ((p * p : ℕ) : ℚ) : ℚ) : ℝ)) ≤
          (oddSum s1.M (min (isqrtUb n_hi) B_ex) (fun p => cdiv (hCeil9 (n_hi / (p * p))) (p * p)) : ℝ) / S9 := by
        refine (sum_le_sum_of_subset_of_nonneg
            (fun p hp => by
              obtain ⟨hpI, hpP, hpp⟩ := mem_filter.mp hp
              obtain ⟨h1, h2⟩ := mem_Ioc.mp hpI
              exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨h1,
                le_min (Nat.mul_self_le_mul_self_iff.mp (hpp.trans (hn_hi.trans (hsq_u n_hi))))
                  (by
                    dsimp [B_peel] at h2
                    omega)⟩, hpP⟩)
            fun p _ _ => by
              rw [Rat.cast_div, Rat.cast_natCast]
              exact div_nonneg (Rat.cast_nonneg.mpr (harm_nn _)) (Nat.cast_nonneg _)).trans <|
          oddSum_ok (by omega) (fun _ h => h) fun p hp => by
            rw [Rat.cast_div, Rat.cast_natCast]
            exact harm_div_le (Nat.mul_pos (mem_filter.mp hp).2.pos (mem_filter.mp hp).2.pos) hn_hi
      have hsq_an : (∑ p ∈ (Ioc B_peel n).filter (fun p => p.Prime ∧ p * p ≤ n),
          ((harmonic (n / (p * p)) / ((p * p : ℕ) : ℚ) : ℚ) : ℝ)) ≤
          ((if Nat.beq sq_q 0 then 0 else cdiv (hCeil9 sq_q) B_peel : ℕ) : ℝ) / S9 := by
        have hab := sq_above_le (L := B_peel) (n := n) (by omega)
        simp only [Rat.cast_div]
        refine hab.trans ?_
        by_cases hz1 : n / ((B_peel + 1) * (B_peel + 1)) = 0
        · rw [if_pos hz1]
          exact div_nonneg (Nat.cast_nonneg _) hS9.le
        · have hz2 : Nat.beq sq_q 0 = false := Bool.eq_false_iff.mpr fun h0 =>
            hz1 (Nat.eq_zero_of_le_zero ((Nat.beq_eq.mp h0) ▸ Nat.div_le_div_right hn_hi))
          rw [if_neg hz1, hz2, if_neg Bool.false_ne_true]
          exact le_cdiv_S9 (by omega) ((div_le_div_of_nonneg_right
            ((Rat.cast_le.mpr (harm_mono.monotone (Nat.div_le_div_right hn_hi))).trans (hCeil9_ok _))
            (Nat.cast_nonneg _)).trans (by rw [div_div, mul_comm (S9 : ℝ)]))
      linarith
    have h3' : (lossPeel s0.M s1.M n (pickG2 n G0 G1) : ℝ) ≤ (peelUb9 n_lo n_hi B_ex s0 s1 : ℝ) / S9 := by
      have hex_sound {p : ℕ} (hp1 : 1 ≤ p) (hp_le : p ≤ n / s0.M) :
          (peelTerm s1.M n (pickG2 n G0 G1) p : ℝ) ≤ (peelEx9 n_lo n_hi s1.M s0 s1 p : ℝ) / S9 := by
        have hone {G s} (hms : MatchSpec G s) (hM : 0 < s.M) (hD : 0 < s.D) (hp' : p ≤ n / s.M) (hpk : pickG2 n G0 G1 p = G) :
            (peelTerm s1.M n (pickG2 n G0 G1) p : ℝ) ≤ (peelOne9 n_lo s1.M s p : ℝ) / S9 := by
          unfold peelTerm peelOne9
          dsimp only []
          rw [hpk, hms.1, hms.2.1]
          set kp_lb := min s1.M (max 1 (n_lo / (p * s.M)))
          set kp := min s1.M (n / (p * s.M))
          have hkp_pos : 0 < kp_lb := lt_min (by omega) (by positivity)
          have hkp_le : kp_lb ≤ kp := min_le_min le_rfl (max_le
            ((Nat.le_div_iff_mul_le (Nat.mul_pos hp1 hM)).mpr (by simpa using (Nat.le_div_iff_mul_le hM).mp hp'))
            (Nat.div_le_div_right hn_lo))
          apply le_cdiv_S9 (Nat.mul_pos (Nat.mul_pos hD hp1) hkp_pos)
          have hetaR : (G.eta : ℝ) ≤ (s.etaNum : ℝ) / s.D := by simpa using Rat.cast_le (K := ℝ).mpr hms.2.2.2
          have hnum : (G.eta : ℝ) + ((p - 1 : ℕ) : ℝ) / s.D ≤ ((s.etaNum + p - 1 : ℕ) : ℝ) / s.D := by
            rw [show s.etaNum + p - 1 = s.etaNum + (p - 1) by omega, Nat.cast_add, add_div]
            linarith
          push_cast
          refine (div_le_div₀ (by positivity) hnum (by positivity)
            (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkp_le) (Nat.cast_nonneg p))).trans ?_
          have : (s.D : ℝ) ≠ 0 := by positivity
          have := hS9.ne'
          field_simp
          exact le_rfl
        by_cases c1 : p ≤ n / G1.M
        · have hc1' : p ≤ n / s1.M := h1.1 ▸ c1
          refine (hone h1 (by omega) hd1 hc1' (if_pos c1)).trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) hS9.le)
          unfold peelEx9
          rw [if_pos (Nat.ble_eq.mpr (hc1'.trans (Nat.div_le_div_right hn_hi)))]
          exact le_max_left _ _
        · refine (hone h0 (by omega) hd0 hp_le (if_neg c1)).trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) hS9.le)
          unfold peelEx9
          rw [if_pos (Bool.and_eq_true_iff.mpr
            ⟨Nat.blt_eq.mpr (lt_of_le_of_lt (Nat.div_le_div_right hn_lo) (not_le.mp (h1.1 ▸ c1))),
              Nat.ble_eq.mpr (hp_le.trans (Nat.div_le_div_right hn_hi))⟩)]
          exact le_max_right _ _
      set B_peel := max s1.M B_ex
      set pick := pickG2 n G0 G1
      have hBpeel_nhi : B_peel ≤ n_hi := hBpeel_nlo.trans (hn_lo.trans hn_hi)
      have hMb_245 : s1.M ≤ 2 ^ 245 := ((le_max_left s1.M B_ex).trans (hBpeel_nhi.trans n_hi.le_succ)).trans hnh1_245
      set S_an := pSum9 n_lo n_hi s1.M B_peel s1.M s0 + pSum9 n_lo n_hi s1.M B_peel (n_hi + 1) s1
      have hb0 := pSum9_ok (n_lo := n_lo) (M_bot := s1.M) (B_peel := B_peel) (M_next := s1.M)
        (pickG := pick) h0 (by omega) hd0 (by omega) (hB300.trans (le_max_right _ _)) hn_lo hn_hi hm01 hMb_245 fun p hp => by
          have := (mem_Ioc.mp (mem_filter.mp hp).1).1
          have := le_max_right B_peel (n / s1.M)
          dsimp [pick, pickG2]
          rw [if_neg (by
            rw [h1.1]
            omega)]
      have hb1 : (∑ p ∈ (Ioc B_peel (max B_peel (n / s1.M))).filter Nat.Prime, (peelTerm s1.M n pick p : ℝ)) ≤
          (pSum9 n_lo n_hi s1.M B_peel (n_hi + 1) s1 : ℝ) / S9 := by
        rw [show Ioc B_peel (max B_peel (n / s1.M)) = Ioc (max B_peel (n / (n_hi + 1))) (max B_peel (n / s1.M)) by
          rw [(Nat.div_eq_zero_iff.mpr (Or.inr (by omega)) : n / (n_hi + 1) = 0), max_eq_left (Nat.zero_le _)]]
        exact pSum9_ok h1 (by omega) hd1 (by omega) (hB300.trans (le_max_right _ _))
          hn_lo hn_hi ((le_max_left s1.M B_ex).trans (hBpeel_nhi.trans n_hi.le_succ)) hnh1_245 fun p hp => by
            obtain ⟨h1', h2'⟩ := mem_Ioc.mp (mem_filter.mp hp).1
            have := lt_of_le_of_lt (le_max_left _ _) h1'
            dsimp [pick, pickG2]
            rw [if_pos (by
              rw [h1.1]
              by_contra hgt
              rw [max_eq_left (by omega)] at h2'
              omega)]
      have hpeel_an : (∑ p ∈ (Ioc B_peel (max B_peel (n / s0.M))).filter Nat.Prime, (peelTerm s1.M n pick p : ℝ)) ≤
          (S_an : ℝ) / S9 := by
        rw [sum_filter, ← sum_Ioc_consecutive _ (le_max_left B_peel (n / s1.M))
          (max_le_max le_rfl (Nat.div_le_div_left hm01 (by omega))), ← sum_filter, ← sum_filter]
        dsimp [S_an]
        rw [Nat.cast_add, add_div]
        linarith
      unfold lossPeel
      rw [Rat.cast_sum]
      by_cases htop_le : n / s0.M ≤ s1.M
      · rw [Ioc_eq_empty (by omega), filter_empty, sum_empty]
        exact div_nonneg (Nat.cast_nonneg _) hS9.le
      · rw [sum_filter, ← sum_Ioc_consecutive _ (le_min (by omega) (le_max_left s1.M B_ex)) (min_le_left (n / s0.M) B_peel),
          ← sum_filter, ← sum_filter]
        have hpart_ex : (∑ p ∈ (Ioc s1.M (min (n / s0.M) B_peel)).filter Nat.Prime, (peelTerm s1.M n pick p : ℝ)) ≤
            (oddSum s1.M (min (n_hi / s0.M) B_ex) (peelEx9 n_lo n_hi s1.M s0 s1) : ℝ) / S9 := by
          by_cases hBM : B_ex ≤ s1.M
          · rw [show B_peel = s1.M from max_eq_left hBM, min_eq_right (by omega), Ioc_self, filter_empty, sum_empty]
            exact div_nonneg (Nat.cast_nonneg _) hS9.le
          · rw [show B_peel = B_ex from max_eq_right (by omega)]
            have hm_le : min (n / s0.M) B_ex ≤ min (n_hi / s0.M) B_ex := min_le_min (Nat.div_le_div_right hn_hi) le_rfl
            have h1_le : ∑ p ∈ (Ioc s1.M (min (n / s0.M) B_ex)).filter Nat.Prime, (peelTerm s1.M n pick p : ℝ) ≤
                ∑ p ∈ (Ioc s1.M (min (n_hi / s0.M) B_ex)).filter Nat.Prime, (peelEx9 n_lo n_hi s1.M s0 s1 p : ℝ) / S9 := by
              refine (sum_le_sum fun p hp => ?_).trans
                (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ioc_subset_Ioc_right hm_le))
                  fun _ _ _ => div_nonneg (Nat.cast_nonneg _) hS9.le)
              obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
              exact hex_sound hpP.pos ((mem_Ioc.mp hpI).2.trans (min_le_left _ _))
            exact h1_le.trans (oddSum_ok (by omega) (fun _ h => h) fun _ _ => le_rfl)
        have hpart_an : (∑ p ∈ (Ioc (min (n / s0.M) B_peel) (n / s0.M)).filter Nat.Prime, (peelTerm s1.M n pick p : ℝ)) ≤
            (S_an : ℝ) / S9 := by
          by_cases hnB : n / s0.M ≤ B_peel
          · rw [min_eq_left hnB, Ioc_self, filter_empty, sum_empty]
            exact div_nonneg (Nat.cast_nonneg _) hS9.le
          · rw [min_eq_right (not_le.mp hnB).le]
            rwa [max_eq_right (not_le.mp hnB).le] at hpeel_an
        unfold peelUb9
        dsimp only [S_an, B_peel] at hpart_an ⊢
        rw [Nat.cast_add, add_div] at hpart_an ⊢
        rw [Nat.cast_add, add_div]
        linarith
    have h4' : (lossQA s1.M n : ℝ) ≤ (qaCompute n_lo n_hi s1.M : ℝ) / S9 := by
      unfold qaCompute lossQA
      rw [Rat.cast_add, Nat.cast_add, add_div]
      have h2 : ((∑ a ∈ Icc 9 (Nat.log 2 n), (1 : ℚ) / ((2 ^ a : ℕ) : ℚ)) : ℝ) ≤ (cdiv S9 256 : ℝ) / S9 := by
        apply le_cdiv_S9 (by decide)
        push_cast
        rw [← Ico_add_one_right_eq_Icc]
        simp_rw [← one_div_pow]
        have hg := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : ℝ)) (m := 9) (n := Nat.log 2 n + 1) (by norm_num) (by norm_num)
        rw [hS9_eq]
        norm_num at hg ⊢
        exact hg
      have hsm := qaSmall_ok hn_lo hn_hi (M_lim := s1.M)
      simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one] at hsm ⊢
      linarith
    have htotR : ((rowUb9 n_lo n_hi B_ex s0 s1 : ℕ) : ℝ) ≤ 992100000 := Nat.cast_le.mpr htot
    unfold rowUb9 at htotR
    push_cast at htotR
    have htot_div := div_le_div_of_nonneg_right htotR hS9.le
    rw [add_div, add_div, add_div] at htot_div
    linarith
@[category API, AMS 11] lemma rW0 : chkRow 10 10 33483 33483 6500 (mkAutoSpec 21 5) (mkAutoSpec 36 7) = true := by decide
@[category API, AMS 11] lemma rW1 : chkRow 11 11 91016 91016 6500 (mkAutoSpec 21 5) (mkAutoSpec 60 7) = true := by decide
@[category API, AMS 11] lemma rW2 : chkRow 12 12 247409 247409 15000 (mkAutoSpec 23 7) (mkAutoSpec 36 11) = true := by decide
set_option maxHeartbeats 400000 in
@[category API, AMS 11] lemma rW3 : chkRow 13 13 672528 672528 28000 (mkAutoSpec 32 11) (mkAutoSpec 44 11) = true := by decide
@[category API, AMS 11] lemma rW4 : chkRow 14 14 1828122 1828122 6000 (mkAutoSpec 44 11) (mkAutoSpec 60 11) = true := by decide
@[category API, AMS 11] lemma rW5 : chkRow 15 15 4969351 4969351 8000 (mkAutoSpec 44 11) (mkAutoSpec 60 11) = true := by decide
@[category API, AMS 11] lemma rW6 : chkRow 16 16 13508099 13508099 3000 (mkAutoSpec 54 11) (mkAutoSpec 130 13) = true := by decide
@[category API, AMS 11] lemma rW7 : chkRow 17 17 36718820 36718820 300 (mkAutoSpec 54 11) (mkAutoSpec 130 13) = true := by decide
@[category API, AMS 11] lemma rW8 : chkRow 18 18 99812102 99812102 300 (mkAutoSpec 64 11) (mkAutoSpec 130 13) = true := by decide
@[category API, AMS 11] lemma rW9 : chkRow 19 21 271317423 2004779672 300 (mkAutoSpec 84 13) (mkAutoSpec 800 31) = true := by decide
@[category API, AMS 11] lemma rWA : chkRow 22 25 (544 * 10 ^ 7) (11 * 10 ^ 10) 300 (mkAutoSpec 120 17) (mkAutoSpec 800 43) = true := by decide
@[category API, AMS 11] lemma rWB : chkRow 26 34 (297 * 10 ^ 9) (89 * 10 ^ 13) 300 (mkAutoSpec 190 23) (mkAutoSpec 800 47) = true := by decide
@[category API, AMS 11] lemma rWC : chkRow 35 55 (241 * 10 ^ 13) (117 * 10 ^ 22) 300 (mkAutoSpec 450 53) (mkAutoSpec 800 89) = true := by decide
@[category API, AMS 11] lemma rWD : chkRow 56 99 (317 * 10 ^ 22) (151 * 10 ^ 42) 300 (mkAutoSpec 980 131) (mkAutoSpec 1600 163) = true := by decide
@[category API, AMS 11] lemma rWE : chkRow 100 149 (408 * 10 ^ 41) (78 * 10 ^ 63) 300 (mkAutoSpec 1600 163) (mkAutoSpec 2000 211) = true := by decide
@[category API, AMS 11] lemma rep_W_10_149 {k : ℕ} (hk10 : 10 ≤ k) (hk149 : k ≤ 149) : IsRepresentable (W k) k :=
  if h10 : k ≤ 10 then chkRow_ok 10 10 33483 33483 6500 (autoG 21 5) (autoG 36 7) hk10 h10 rW0
  else if h11 : k ≤ 11 then chkRow_ok 11 11 91016 91016 6500 (autoG 21 5) (autoG 60 7) (by omega) h11 rW1
  else if h12 : k ≤ 12 then chkRow_ok 12 12 247409 247409 15000 (autoG 23 7) (autoG 36 11) (by omega) h12 rW2
  else if h13 : k ≤ 13 then chkRow_ok 13 13 672528 672528 28000 (autoG 32 11) (autoG 44 11) (by omega) h13 rW3
  else if h14 : k ≤ 14 then chkRow_ok 14 14 1828122 1828122 6000 (autoG 44 11) (autoG 60 11) (by omega) h14 rW4
  else if h15 : k ≤ 15 then chkRow_ok 15 15 4969351 4969351 8000 (autoG 44 11) (autoG 60 11) (by omega) h15 rW5
  else if h16 : k ≤ 16 then chkRow_ok 16 16 13508099 13508099 3000 (autoG 54 11) (autoG 130 13) (by omega) h16 rW6
  else if h17 : k ≤ 17 then chkRow_ok 17 17 36718820 36718820 300 (autoG 54 11) (autoG 130 13) (by omega) h17 rW7
  else if h18 : k ≤ 18 then chkRow_ok 18 18 99812102 99812102 300 (autoG 64 11) (autoG 130 13) (by omega) h18 rW8
  else if h21 : k ≤ 21 then chkRow_ok 19 21 271317423 2004779672 300 (autoG 84 13) (autoG 800 31) (by omega) h21 rW9
  else if h25 : k ≤ 25 then chkRow_ok 22 25 (544 * 10 ^ 7) (11 * 10 ^ 10) 300 (autoG 120 17) (autoG 800 43) (by omega) h25 rWA
  else if h34 : k ≤ 34 then chkRow_ok 26 34 (297 * 10 ^ 9) (89 * 10 ^ 13) 300 (autoG 190 23) (autoG 800 47) (by omega) h34 rWB
  else if h55 : k ≤ 55 then chkRow_ok 35 55 (241 * 10 ^ 13) (117 * 10 ^ 22) 300 (autoG 450 53) (autoG 800 89) (by omega) h55 rWC
  else if h99 : k ≤ 99 then chkRow_ok 56 99 (317 * 10 ^ 22) (151 * 10 ^ 42) 300 (autoG 980 131) (autoG 1600 163) (by omega) h99 rWD
  else chkRow_ok 100 149 (408 * 10 ^ 41) (78 * 10 ^ 63) 300 (autoG 1600 163) (autoG 2000 211) (by omega) hk149 rWE
@[category API, AMS 11] lemma inv_p_le {a b : ℕ} (ha : 250000 ≤ a) (hab : a ≤ b) :
    ((∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℚ) / p) : ℝ) ≤
      ((229 : ℝ) / 1000 + ((10386 : ℝ) / 10000) * (log b - log a)) / log a := by
  have hreal := inv_p_real (by omega : 300 ≤ a) hab
  have haR : (250000 : ℝ) ≤ a := mod_cast ha
  have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have ha1_pos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq : sqrt (a : ℝ) ≤ a / 500 := sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hlog_lin : log (a : ℝ) ≤ a / 250 := by
    have hl1 : log (a : ℝ) = 2 * log (sqrt a) := by
      rw [← sq_sqrt ha_pos.le, log_pow, sq_sqrt ha_pos.le]
      norm_num
    linarith [log_le_sub_one_of_pos (sqrt_pos.mpr ha_pos)]
  have hloga_pos : 0 < log (a : ℝ) := log_pos (mod_cast (by omega : 1 < a))
  have hterm1 : (((817 : ℝ) / 10000) * a + (344 / 10) * log a + (426 / 100) * sqrt a) /
      (((a + 1 : ℕ) : ℝ) * log ((a + 1 : ℕ) : ℝ)) ≤ (228 / 1000) / log a := by
    refine (div_le_div₀ (by positivity)
      (by linarith [Nat.cast_le (α := ℝ).mpr a.le_succ] :
        ((817 : ℝ) / 10000) * a + (344 / 10) * log a + (426 / 100) * sqrt a ≤ (228 / 1000) * ((a + 1 : ℕ) : ℝ))
      (mul_pos ha1_pos hloga_pos) (by
        gcongr
        omega)).trans_eq ?_
    have := ha1_pos.ne'
    field_simp
  have hterm2 : log (log (b : ℝ) / log a) ≤ (log b - log a) / log a := by
    refine (log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le hloga_pos (log_le_log ha_pos (Nat.cast_le.mpr hab))) hloga_pos)).trans_eq ?_
    have := hloga_pos.ne'
    field_simp
  have hterm3 : ((188 : ℝ) / 10) / (a * log a) ≤ (1 / 1000) / log a := by
    refine (div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hloga_pos)
      (mul_le_mul_of_nonneg_right haR hloga_pos.le)).trans ?_
    rw [← div_div]
    exact div_le_div_of_nonneg_right (by norm_num) hloga_pos.le
  rw [add_div]
  linarith [mul_le_mul_of_nonneg_left hterm2 (by norm_num : (0 : ℝ) ≤ 10386 / 10000),
    show ((10386 : ℝ) / 10000) * ((log b - log a) / log a) = ((10386 / 10000) * (log b - log a)) / log a by ring,
    show ((228 : ℝ) / 1000) / log a + (1 / 1000) / log a = (229 / 1000) / log a by ring]
@[category API, AMS 11] lemma inv_log_le {M : ℕ} (hM : 2 ≤ M) :
    ∑ m ∈ Icc 1 (M - 1), (1 / (m : ℝ)) * log ((M : ℝ) / m) ≤ log M + (1 / 2 : ℝ) * (log M) ^ 2 := by
  have hI : Icc 1 (M - 1) = insert 1 (Ioc 1 (M - 1)) := by
    ext
    simp only [mem_Icc, mem_insert, mem_Ioc]
    omega
  rw [hI, sum_insert (by simp), show (1 / ((1 : ℕ) : ℝ)) * log ((M : ℝ) / ((1 : ℕ) : ℝ)) = log M by simp]
  let u (j : ℕ) : ℝ := log ((M : ℝ) / j)
  suffices htel : ∀ K, 1 ≤ K → K ≤ M - 1 → ∑ m ∈ Ioc 1 K, (1 / (m : ℝ)) * u m ≤ (1 / 2 : ℝ) * ((u 1) ^ 2 - (u K) ^ 2) by
    have h := htel (M - 1) (by omega) le_rfl
    simp only [u, Nat.cast_one, div_one] at h
    linarith [sq_nonneg (u (M - 1))]
  intro K h1K
  induction K, h1K using Nat.le_induction with
  | base =>
    intro _
    simp
  | succ k' hk1 ih =>
    intro hk1M
    rw [sum_Ioc_succ_top hk1]
    have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    have hk_pos : (0 : ℝ) < k' := Nat.cast_pos.mpr hk1
    have hk1_pos : (0 : ℝ) < ((k' + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hu_nn : 0 ≤ u (k' + 1) := log_nonneg ((one_le_div hk1_pos).mpr (Nat.cast_le.mpr (by omega)))
    have hlb : 1 / ((k' + 1 : ℕ) : ℝ) ≤ u k' - u (k' + 1) := by
      dsimp [u]
      rw [log_div hM_pos.ne' hk_pos.ne', log_div hM_pos.ne' hk1_pos.ne']
      linarith [(log_succ hk1).1]
    nlinarith [ih (by omega), show (0 : ℝ) ≤ 1 / ((k' + 1 : ℕ) : ℝ) by positivity]
@[category API, AMS 11] lemma qa_reg4_le {M n : ℕ} (hM_lb : 352800 ≤ M) (h4M6_lt_n : 4 * M ^ 6 < n) :
    (lossQA M n : ℝ) ≤ 24 / 1000 := by
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h4M6_lt_n
  have hharm_le (m : ℕ) : (harmonic m : ℝ) ≤ m := by
    rcases m.eq_zero_or_pos with rfl | hm
    · simp
    · linarith [harmonic_le_one_add_log m, log_le_sub_one_of_pos (Nat.cast_pos.mpr hm : (0 : ℝ) < m)]
  unfold lossQA
  push_cast
  have hqa2 : ∑ a ∈ Icc 9 (Nat.log 2 n), (1 : ℝ) / (2 : ℝ) ^ a ≤ 4 / 1000 := by
    rw [← Ico_add_one_right_eq_Icc]
    simp_rw [← one_div_pow]
    exact (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans (by norm_num)
  let P_odd := (Icc 3 M).filter Nat.Prime
  have hq_each : ∀ q ∈ P_odd, ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), (qaOdd n q a : ℝ) ≤
      (20 * (M : ℝ)) / n + (1 / 27) * (1 / (((q - 1 : ℕ) : ℝ) * q)) := fun q hq => by
    obtain ⟨hq3, hqM⟩ := mem_Icc.mp (mem_filter.mp hq).1
    have hterm_nn (a) : 0 ≤ (qaOdd n q a : ℝ) := by
      unfold qaOdd
      dsimp only []
      split_ifs
      · exact Rat.cast_nonneg.mpr (by positivity)
      · exact Rat.cast_nonneg.mpr (div_nonneg (harm_nn _) (Nat.cast_nonneg _))
    have hsplit_a : ∑ a ∈ Icc (tgtExp q + 1) (Nat.log q n), (qaOdd n q a : ℝ) ≤
        (∑ a ∈ Icc 1 5, (qaOdd n q a : ℝ)) + ∑ a ∈ Icc 6 (Nat.log q n), (qaOdd n q a : ℝ) := by
      have hdisj : Disjoint (Icc 1 5) (Icc 6 (Nat.log q n)) := disjoint_left.mpr fun a h1 h2 => by
        have := (mem_Icc.mp h1).2
        have := (mem_Icc.mp h2).1
        omega
      rw [← sum_union hdisj]
      refine sum_le_sum_of_subset_of_nonneg (fun a ha => ?_) fun a _ _ => hterm_nn a
      obtain ⟨_, ha2⟩ := mem_Icc.mp ha
      rw [mem_union, mem_Icc, mem_Icc]
      exact if ha5 : a ≤ 5 then Or.inl ⟨by omega, ha5⟩ else Or.inr ⟨by omega, ha2⟩
    have ha15 : ∑ a ∈ Icc 1 5, (qaOdd n q a : ℝ) ≤ (20 * (M : ℝ)) / n := by
      refine (sum_le_sum (g := fun _ => (4 * (M : ℝ)) / n) fun a ha =>
        qaOdd_four hq3 hqM hn_pos le_rfl <|
          (Nat.mul_le_mul ((Nat.pow_le_pow_left hqM a).trans (Nat.pow_le_pow_right (by omega) (mem_Icc.mp ha).2))
            ((Nat.pow_log_le_self 2 (by omega)).trans hqM)).trans
            ((show M ^ 5 * M ≤ 4 * M ^ 6 by
              rw [← pow_succ]
              exact Nat.le_mul_of_pos_left _ (by decide)).trans h4M6_lt_n.le)).trans ?_
      rw [sum_const, show (Icc 1 5).card = 5 by decide, nsmul_eq_mul]
      push_cast
      ring_nf
      exact le_rfl
    have ha6 : ∑ a ∈ Icc 6 (Nat.log q n), (qaOdd n q a : ℝ) ≤ (1 / 27) * (1 / (((q - 1 : ℕ) : ℝ) * q)) := by
      have hgeom : ∑ a ∈ Icc 6 (Nat.log q n), (1 : ℝ) / (q : ℝ) ^ (a - 4) ≤ 1 / (((q - 1 : ℕ) : ℝ) * q) := by
        have hq1 : (1 : ℝ) < q := mod_cast (by omega : 1 < q)
        have himg : Icc 6 (Nat.log q n) = (Ico 2 (Nat.log q n + 1 - 4)).image (· + 4) := by
          ext a
          simp only [mem_Icc, mem_Ico, mem_image]
          exact ⟨fun h => ⟨a - 4, by omega, by omega⟩, by
            rintro ⟨i, hi, rfl⟩
            omega⟩
        rw [himg, sum_image fun _ _ _ _ h => by simpa using h]
        simp_rw [Nat.add_sub_cancel, ← one_div_pow]
        refine (geom_sum_Ico_le_of_lt_one (by positivity) ((div_lt_one (by positivity)).mpr hq1)).trans_eq ?_
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        field_simp
      refine (sum_le_sum (g := fun a => (1 / 27 : ℝ) * (1 / (q : ℝ) ^ (a - 4))) fun a ha => ?_).trans
        (by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left hgeom (by norm_num))
      have ha6_le := (mem_Icc.mp ha).1
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have h1 := qaOdd_pow (n := n) (q := q) (a := a) (K := q) hq3
        (mod_cast (by omega : 2 ≤ q)) fun m hm => (hharm_le m).trans (Nat.cast_le.mpr hm.le)
      have hpow_eq : (q : ℝ) * (1 / (q : ℝ) ^ a) = (1 / (q : ℝ) ^ (3 : ℕ)) * (1 / (q : ℝ) ^ (a - 4)) := by
        conv_lhs => rw [show a = 1 + 3 + (a - 4) by omega, pow_add, pow_add, pow_one]
        field_simp
      rw [hpow_eq] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num)
        (by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (mod_cast hq3 : (3 : ℝ) ≤ q) 3
          linarith)) (by positivity))
    linarith
  have hsum := sum_le_sum hq_each
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum] at hsum
  have hpart1 : (P_odd.card : ℝ) * ((20 * (M : ℝ)) / n) ≤ 1 / 1000 := by
    have hcard_le : (P_odd.card : ℝ) ≤ M := Nat.cast_le.mpr
      ((card_filter_le _ _).trans (by
        rw [Nat.card_Icc]
        omega))
    refine (mul_le_mul_of_nonneg_right hcard_le (by positivity)).trans ?_
    rw [mul_div_assoc', div_le_iff₀ (Nat.cast_pos.mpr hn_pos)]
    linarith [show 20000 * ((M : ℝ) * M) ≤ n from mod_cast
      (((Nat.mul_le_mul_right _ ((by norm_num : 20000 ≤ 4 * 352800 ^ 4).trans
          (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hM_lb 4)))).trans_eq
        (by ring : (4 * M ^ 4) * (M * M) = 4 * M ^ 6)).trans h4M6_lt_n.le)]
  have htel : ∑ q ∈ P_odd, (1 : ℝ) / (((q - 1 : ℕ) : ℝ) * q) ≤ 1 / (2 : ℕ) := by
    refine (sum_le_sum_of_subset_of_nonneg (s := P_odd) (t := Ioc 2 M)
      (fun q hq => by
        obtain ⟨h1, h2⟩ := mem_Icc.mp (mem_filter.mp hq).1
        exact mem_Ioc.mpr ⟨by omega, h2⟩)
      fun _ _ _ => by positivity).trans (pred_mul_le (A := 2) (B := M) (by decide))
  push_cast at htel
  linarith [mul_le_mul_of_nonneg_left htel (by norm_num : (0 : ℝ) ≤ 1 / 27)]

set_option maxHeartbeats 400000 in
@[category API, AMS 11] lemma regime4_valid {k : ℕ} (hk : 150 ≤ k) (G : Gadget)
    (hGM : G.M = 2 * ((4 * k) / 3 + 220) ^ 2)
    (hGD : G.D = 2 ^ (1 + Nat.log 2 ((4 * k) / 3 + 220)) * ∏ p ∈ (Icc 3 ((4 * k) / 3 + 220)).filter Nat.Prime, p)
    (hGcov : G.D ≤ G.B - G.A) (hGeta : G.eta ≤ 1) (hHW : (harmonic (W k) : ℝ) < (k : ℝ) + 1) :
    ValidPeel (W k) G.M G.M (fun _ => G) := by
  generalize hR_def : (4 * k) / 3 + 220 = R at hGM hGD
  have h1000_exp_lt_GD : 1000 * exp ((k : ℝ) + 1) < G.D := by
    have hGD_ge : exp (theta (R : ℝ)) ≤ G.D := by
      rw [theta_eq_log_primorial, Nat.floor_natCast, exp_log (Nat.cast_pos.mpr (primorial_pos R))]
      have hpr : primorial R = 2 * ∏ p ∈ (Icc 3 R).filter Nat.Prime, p := by
        unfold primorial
        have hflt : filter Nat.Prime (range (R + 1)) = insert 2 ((Icc 3 R).filter Nat.Prime) := by
          ext p
          simp only [mem_filter, mem_range, mem_insert, mem_Icc]
          refine ⟨fun ⟨hpR, hp⟩ => (eq_or_lt_of_le hp.two_le).imp Eq.symm fun h => ⟨⟨by omega, by omega⟩, hp⟩, ?_⟩
          rintro (rfl | ⟨⟨_, hpR⟩, hp⟩)
          · exact ⟨by omega, Nat.prime_two⟩
          · exact ⟨by omega, hp⟩
        rw [hflt, prod_insert (by simp)]
      have := Nat.le_log_of_pow_le (by decide) (by omega : 2 ^ 1 ≤ R)
      exact_mod_cast (hGD ▸ hpr ▸ Nat.mul_le_mul_right _
        (show 2 ^ 1 ≤ 2 ^ (1 + Nat.log 2 R) from Nat.pow_le_pow_right (by decide) (by omega)))
    have hR_pos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
    have hth := (theta_bds (show (300 : ℝ) ≤ R from mod_cast (by omega : 300 ≤ R))).1
    have hsqR : sqrt (R : ℝ) ≤ R / 40 + 10 := sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg ((R : ℝ) - 400)]⟩
    have hl256 : log 256 < 555 / 100 := by
      rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, log_pow]
      push_cast
      linarith [log_two_lt_d9]
    have hlogR : log (R : ℝ) ≤ 455 / 100 + R / 256 := by
      rw [show (R : ℝ) = 256 * (R / 256) by ring, log_mul (by norm_num) (by positivity)]
      linarith [log_le_sub_one_of_pos (div_pos hR_pos (by norm_num : (0 : ℝ) < 256))]
    have hp : (2 : ℝ) ^ (10 : ℕ) < exp 10 := by
      simpa [← exp_nat_mul] using pow_lt_pow_left₀ (by linarith [exp_one_gt_d9] : (2 : ℝ) < exp 1) (by norm_num) (by decide : 10 ≠ 0)
    have hp1000 : (1000 : ℝ) < exp 10 := by
      norm_num at hp
      linarith
    refine (mul_lt_mul_of_pos_right hp1000 (exp_pos _)).trans_le (le_trans ?_ hGD_ge)
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith [show (4 : ℝ) * k + 658 ≤ 3 * R from mod_cast (by omega), show (150 : ℝ) ≤ k from mod_cast hk])
  have hR420 : 420 ≤ R := by omega
  have hk_le_R : k ≤ R := by omega
  have hR_lin : 150 * R ≤ 420 * k := by omega
  have hn_eq : W k = ⌊exp ((k : ℝ) + 4188 / 10000)⌋₊ := by
    simp [W, show ¬ k ≤ 1 by omega, show k ≠ 2 by omega]
  have hexp_k_lt : exp (k : ℝ) < W k := by
    have hprod : exp (k : ℝ) + 1 < exp ((k : ℝ) + 4188 / 10000) := by
      rw [exp_add]
      nlinarith [add_one_le_exp (4188 / 10000 : ℝ), add_one_le_exp (k : ℝ), exp_pos (k : ℝ), show (150 : ℝ) ≤ k from mod_cast hk]
    have hfl := Nat.lt_floor_add_one (exp ((k : ℝ) + 4188 / 10000))
    rw [← hn_eq] at hfl
    linarith
  have hn_lt_exp : (W k : ℝ) < exp ((k : ℝ) + 1) := by
    have hfl := Nat.floor_le (exp_pos ((k : ℝ) + 4188 / 10000)).le
    rw [← hn_eq] at hfl
    exact hfl.trans_lt (by
      gcongr
      norm_num)
  unfold ValidPeel
  dsimp only []
  generalize hn_def : W k = n at hexp_k_lt hn_lt_exp hHW ⊢
  clear hn_def hn_eq hGD hR_def
  set M := G.M
  have hM_lb : 352800 ≤ M := by
    rw [show M = 2 * R ^ 2 from hGM]
    nlinarith
  have hM_k_lb : 840 * k ≤ M := by
    rw [show M = 2 * R ^ 2 from hGM]
    nlinarith
  have hM_ub : M ≤ 16 * k ^ 2 := Nat.le_of_mul_le_mul_left (calc
    150 ^ 2 * M = 2 * (150 * R) ^ 2 := by
      rw [show M = 2 * R ^ 2 from hGM]
      ring
    _ ≤ 2 * (420 * k) ^ 2 := by gcongr
    _ ≤ 150 ^ 2 * (16 * k ^ 2) := by nlinarith) (by norm_num : 0 < 150 ^ 2)
  clear hGM hR420 hk_le_R hR_lin R
  have h4M6_lt_n : 4 * M ^ 6 < n := by
    have hkR : (150 : ℝ) ≤ k := mod_cast hk
    have h1 : 32 * (k : ℝ) ^ 2 < exp ((k : ℝ) / 6) := by
      have hexp := Real.pow_div_factorial_le_exp ((k : ℝ) / 6) (by positivity) 7
      have h7 : 150 ^ 5 * (k : ℝ) ^ 2 ≤ k ^ 7 := by
        rw [show (k : ℝ) ^ 7 = k ^ 5 * k ^ 2 by ring]
        gcongr
      norm_num [Nat.factorial] at hexp h7
      linarith [show (0 : ℝ) < k ^ 2 by positivity]
    have h2 : (32 * (k : ℝ) ^ 2) ^ 6 < exp k := by
      refine (pow_lt_pow_left₀ h1 (by positivity) (by decide : 6 ≠ 0)).trans_eq ?_
      rw [← exp_nat_mul]
      congr 1
      ring
    have hle6 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hM_ub 6)
    refine hle6.trans_lt (Nat.cast_lt (α := ℝ).mp (lt_trans ?_ hexp_k_lt))
    push_cast
    linarith [show (1 : ℝ) ≤ k ^ 12 from one_le_pow₀ (by linarith : (1 : ℝ) ≤ k)]
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h4M6_lt_n
  have hM3_le_n : M * (M * M) ≤ n :=
    ((by ring : M * (M * M) = 1 * M ^ 3).le.trans
      ((Nat.mul_le_mul (by decide) (Nat.le_mul_of_pos_right _ (pow_pos (by omega) 3))).trans_eq
        (by ring : 4 * (M ^ 3 * M ^ 3) = 4 * M ^ 6))).trans h4M6_lt_n.le
  have h1000n_lt_GD : 1000 * (n : ℝ) < G.D := by linarith
  have hn_lt_GD : n < G.D := mod_cast (by linarith [Nat.cast_pos (α := ℝ).mpr hn_pos] : (n : ℝ) < G.D)
  refine ⟨by omega, le_rfl, (Nat.le_mul_of_pos_left _ (by omega)).trans hM3_le_n, fun p _ _ hp_le => ?_, ?_⟩
  · have := G.hA_le_B
    have := lt_of_le_of_lt (hp_le.trans (Nat.div_le_self n M)) hn_lt_GD
    exact ⟨by omega, le_rfl, (Nat.le_div_iff_mul_le (by omega)).mp hp_le, by omega⟩
  · suffices hR : (lossTail M n : ℝ) + (lossSq M n : ℝ) + (lossPeel M M n (fun _ => G) : ℝ) + (lossQA M n : ℝ) ≤ 9921 / 10000 from
      Rat.cast_le (K := ℝ).mp (by
        push_cast
        linarith)
    set x : ℝ := (k : ℝ) / 150
    have hkx : (k : ℝ) = 150 * x := by
      dsimp [x]
      ring
    have hx1 : 1 ≤ x := by
      dsimp [x]
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast hk
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hsqx1 : 1 ≤ sqrt x := sqrt_one ▸ sqrt_le_sqrt hx1
    have hlogM_pos_lb : (12 : ℝ) ≤ log M := by
      have hl18 : (12 : ℝ) ≤ log 262144 := by
        rw [show (262144 : ℝ) = (2 : ℝ) ^ (18 : ℕ) by norm_num, log_pow]
        push_cast
        linarith [log_two_gt_d9]
      exact hl18.trans (log_le_log (by norm_num) (mod_cast (by omega : 262144 ≤ M)))
    have hlogM_sqx : log (M : ℝ) ≤ (1317 / 100) * sqrt x := by
      have hMR : (M : ℝ) ≤ 16 * (k : ℝ) ^ (2 : ℕ) := mod_cast hM_ub
      rw [hkx] at hMR
      have hlog_le1 := log_le_log (Nat.cast_pos.mpr (by omega : 0 < M)) (by nlinarith : (M : ℝ) ≤ 524288 * x ^ (2 : ℕ))
      rw [log_mul (by norm_num) (pow_ne_zero 2 hx_pos.ne')] at hlog_le1
      have hl19 : log 524288 < 1317 / 100 := by
        rw [show (524288 : ℝ) = (2 : ℝ) ^ (19 : ℕ) by norm_num, log_pow]
        push_cast
        linarith [log_two_lt_d9]
      have hlx2 : log (x ^ (2 : ℕ)) ≤ 4 * (sqrt x - 1) := by
        have hx4 : x ^ (2 : ℕ) = (sqrt x) ^ (4 : ℕ) :=
          calc x ^ (2 : ℕ) = ((sqrt x) ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [sq_sqrt hx_pos.le]
            _ = (sqrt x) ^ (4 : ℕ) := by ring
        rw [hx4, log_pow]
        push_cast
        linarith [log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hsqx1)]
      linarith
    have hlogM_ub : log (M : ℝ) ≤ (1317 / 100) * x :=
      hlogM_sqx.trans (mul_le_mul_of_nonneg_left (sqrt_le_iff.mpr ⟨hx_pos.le, by nlinarith⟩) (by norm_num))
    have hlogM_sq_ub : (log (M : ℝ)) ^ 2 ≤ (1735 / 10) * x := by
      have hsq1 := pow_le_pow_left₀ (by linarith) hlogM_sqx 2
      rw [mul_pow, sq_sqrt hx_pos.le] at hsq1
      linarith
    clear hM_ub hsqx1 hlogM_sqx
    set a_tail := n / M
    set B := n / (M * M)
    have hB_ge : 250000 ≤ B := (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mpr <|
      ((Nat.mul_le_mul_right _ ((by norm_num : 250000 ≤ 4 * 352800 ^ 4).trans
          (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hM_lb 4)))).trans_eq
        (by ring : (4 * M ^ 4) * (M * M) = 4 * M ^ 6)).trans h4M6_lt_n.le
    have hatail_ge_B : B ≤ a_tail := Nat.div_le_div_left (Nat.le_mul_of_pos_left M (by omega)) (by omega)
    have hatail_ge : 250000 ≤ a_tail := hB_ge.trans hatail_ge_B
    have hatail_mul_gt : (n : ℝ) < (M : ℝ) * ((a_tail + 1 : ℕ) : ℝ) :=
      mod_cast Nat.mul_comm (a_tail + 1) M ▸ (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mp a_tail.lt_succ_self
    have hB_mul_gt : (n : ℝ) < ((M * M : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ) :=
      mod_cast Nat.mul_comm (B + 1) (M * M) ▸
        (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega : 0 < M) (by omega))).mp B.lt_succ_self
    have hlog_succ_sub (u) (hu : 250000 ≤ u) : log ((u + 1 : ℕ) : ℝ) - log u ≤ 1 / 250000 :=
      (log_succ (by omega)).2.trans (one_div_le_one_div_of_le (by norm_num) (mod_cast hu))
    have hloga_lb : (1368 / 10) * x ≤ log (a_tail : ℝ) := by
      have hlog_gt := log_lt_log (exp_pos _) (hexp_k_lt.trans hatail_mul_gt)
      rw [log_exp, log_mul (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega)), hkx] at hlog_gt
      linarith [hlog_succ_sub a_tail hatail_ge]
    have hlogB_lb : (12365 / 100) * x ≤ log (B : ℝ) := by
      have hlog_gt := log_lt_log (exp_pos _) (hexp_k_lt.trans hB_mul_gt)
      rw [log_exp, Nat.cast_mul,
        log_mul (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))) (Nat.cast_ne_zero.mpr (by omega)),
        log_mul (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega)), hkx] at hlog_gt
      linarith [hlog_succ_sub B hB_ge]
    have htail_le : (lossTail M n : ℝ) ≤ 790 / 1000 := by
      unfold lossTail
      have habove := congrArg (Rat.cast (K := ℝ)) (tail_above (M_top := M) (n := n) (lo := a_tail) (by omega) le_rfl)
      push_cast at habove ⊢
      rw [habove]
      have hloga_pos : 0 < log (a_tail : ℝ) := lt_of_lt_of_le (by positivity) hloga_lb
      have hterm : ∀ m ∈ Icc 1 (M - 1),
          (1 / (m : ℝ)) * ∑ p ∈ (Ioc a_tail (n / m)).filter Nat.Prime, (1 : ℝ) / p ≤
            ((1 / (m : ℝ)) * (229 / 1000 + (10386 / 10000) / 250000) +
              (10386 / 10000) * ((1 / (m : ℝ)) * log ((M : ℝ) / m))) / log a_tail := fun m hm => by
        obtain ⟨_, hmM⟩ := mem_Icc.mp hm
        have hab_m : a_tail ≤ n / m := Nat.div_le_div_left (by omega : m ≤ M) (by omega)
        have hsinv_m := inv_p_le hatail_ge hab_m
        push_cast at hsinv_m
        have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
        have hbm_le : ((n / m : ℕ) : ℝ) ≤ ((M : ℝ) / m) * ((a_tail + 1 : ℕ) : ℝ) :=
          ((le_div_iff₀ hm_pos).mpr (mod_cast Nat.div_mul_le_self n m)).trans
            ((div_le_div_of_nonneg_right hatail_mul_gt.le hm_pos.le).trans_eq (by ring))
        have hl1 := log_le_log (Nat.cast_pos.mpr (by omega)) hbm_le
        rw [log_mul (div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hm_pos.ne') (Nat.cast_ne_zero.mpr (by omega))] at hl1
        have hlog_bm : log ((n / m : ℕ) : ℝ) - log (a_tail : ℝ) ≤ 1 / 250000 + log ((M : ℝ) / m) := by
          linarith [hlog_succ_sub a_tail hatail_ge]
        refine (mul_le_mul_of_nonneg_left hsinv_m (by positivity)).trans ?_
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ 1 / m by positivity]) hloga_pos.le
      refine (sum_le_sum hterm).trans ?_
      rw [← sum_div, sum_add_distrib, ← sum_mul, ← mul_sum]
      have hh := (Rat.cast_le.mpr (harm_mono.monotone (by omega : M - 1 ≤ M))).trans (harmonic_le_one_add_log M)
      rw [harmonic_eq_sum_Icc] at hh
      push_cast at hh
      rw [div_le_iff₀ hloga_pos]
      linarith [(by simpa [one_div] using hh : ∑ m ∈ Icc 1 (M - 1), (1 : ℝ) / m ≤ 1 + log M), inv_log_le (by omega : 2 ≤ M)]
    have hsq_le : (lossSq M n : ℝ) ≤ 3 / 1000 := by
      unfold lossSq
      have hab := sq_above_le (L := M) (n := n) (by omega)
      push_cast at hab ⊢
      refine hab.trans ?_
      split_ifs
      · norm_num
      · rw [div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0 < M))]
        linarith [Rat.cast_le (K := ℝ).mpr (harm_mono.monotone (Nat.div_le_self n ((M + 1) * (M + 1)))),
          show 840 * (k : ℝ) ≤ M from mod_cast hM_k_lb, show (150 : ℝ) ≤ k from mod_cast hk]
    have hpeel_le : (lossPeel M M n (fun _ => G) : ℝ) ≤ 115 / 1000 := by
      unfold lossPeel
      have hM_le_B : M ≤ B := (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mpr hM3_le_n
      push_cast
      rw [sum_filter, ← sum_Ioc_consecutive _ hM_le_B hatail_ge_B, ← sum_filter, ← sum_filter]
      have hpeel_term {p c : ℕ} (hp_pos : 0 < p) (hp_le : p ≤ a_tail) (hc : 0 < c) (hckp : c ≤ min M (n / (p * M))) :
          (peelTerm M n (fun _ => G) p : ℝ) ≤ ((1001 / 1000) / (c : ℝ)) * (1 / (p : ℝ)) := by
        have hp_le_n : ((p - 1 : ℕ) : ℝ) ≤ n := mod_cast (Nat.sub_le p 1).trans (hp_le.trans (Nat.div_le_self n M))
        have hnum : (G.eta : ℝ) + ((p - 1 : ℕ) : ℝ) / G.D ≤ 1001 / 1000 := by
          linarith [show (G.eta : ℝ) ≤ 1 from mod_cast hGeta,
            (div_le_iff₀ (Nat.cast_pos.mpr G.hD_pos)).mpr (by linarith : ((p - 1 : ℕ) : ℝ) ≤ 1 / 1000 * G.D)]
        unfold peelTerm
        dsimp only []
        change (((G.eta + ((p - 1 : ℕ) : ℚ) / G.D) / ((p * min M (n / (p * M)) : ℕ) : ℚ) : ℚ) : ℝ) ≤
          ((1001 / 1000) / (c : ℝ)) * (1 / (p : ℝ))
        set kp := min M (n / (p * M))
        push_cast
        have hpR : (0 : ℝ) < p := mod_cast hp_pos
        have hcR : (0 : ℝ) < c := mod_cast hc
        exact (div_le_div₀ (by norm_num) hnum (mul_pos hpR hcR)
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hckp) hpR.le)).trans (le_of_eq (by ring))
      have hp3a : ∑ p ∈ (Ioc M B).filter Nat.Prime, (peelTerm M n (fun _ => G) p : ℝ) ≤ 1 / 1000 := by
        refine le_trans (sum_le_sum fun p hp => show
          (peelTerm M n (fun _ => G) p : ℝ) ≤ ((1001 / 1000) / (M : ℝ)) * (1 / (p : ℝ)) from ?_) ?_
        · obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
          obtain ⟨_, hpB⟩ := mem_Ioc.mp hpI
          exact hpeel_term hpP.pos (hpB.trans hatail_ge_B) (by omega) (le_min le_rfl
            ((Nat.le_div_iff_mul_le (Nat.mul_pos hpP.pos (by omega))).mpr
              (by linarith [(Nat.le_div_iff_mul_le (Nat.mul_pos (by omega : 0 < M) (by omega))).mp hpB,
                show M * (p * M) = p * (M * M) by ring])))
        · rw [← mul_sum]
          have hsinv1 := inv_p_le (by omega : 250000 ≤ M) hM_le_B
          push_cast at hsinv1
          have hlogB_le : log (B : ℝ) - log M ≤ k + 1 := by
            linarith [(log_le_iff_le_exp (Nat.cast_pos.mpr hn_pos)).mpr hn_lt_exp.le,
              log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (Nat.div_le_self n (M * M)))]
          have hsinv_k : (∑ p ∈ (Ioc M B).filter Nat.Prime, (1 : ℝ) / p) ≤ (2 / 10) * k :=
            hsinv1.trans ((div_le_iff₀ (by linarith : 0 < log (M : ℝ))).mpr
              (by linarith [show (150 : ℝ) ≤ k from mod_cast hk,
                mul_le_mul_of_nonneg_left hlogM_pos_lb (Nat.cast_nonneg (α := ℝ) k)]))
          refine (mul_le_mul_of_nonneg_left hsinv_k (by positivity)).trans ?_
          rw [div_mul_eq_mul_div, div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0 < M))]
          linarith [show 840 * (k : ℝ) ≤ M from mod_cast hM_k_lb]
      have hp3b : ∑ p ∈ (Ioc B a_tail).filter Nat.Prime, (peelTerm M n (fun _ => G) p : ℝ) ≤ 114 / 1000 := by
        refine le_trans (sum_le_sum fun p hp => show
          (peelTerm M n (fun _ => G) p : ℝ) ≤ (1001 / 1000 : ℝ) * (1 / (p : ℝ)) from ?_) ?_
        · obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
          obtain ⟨_, hp_le⟩ := mem_Ioc.mp hpI
          simpa using hpeel_term (c := 1) hpP.pos hp_le zero_lt_one (le_min (by omega)
            ((Nat.le_div_iff_mul_le (Nat.mul_pos hpP.pos (by omega))).mpr
              (by simpa using (Nat.le_div_iff_mul_le (by omega)).mp hp_le)))
        · rw [← mul_sum]
          have hsinv2 := inv_p_le hB_ge hatail_ge_B
          push_cast at hsinv2
          have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
          have hatail_le_MB : (a_tail : ℝ) ≤ M * ((B + 1 : ℕ) : ℝ) := by
            have h2 := div_le_div_of_nonneg_right hB_mul_gt.le hM_pos.le
            rw [Nat.cast_mul] at h2
            refine ((le_div_iff₀ hM_pos).mpr (mod_cast Nat.div_mul_le_self n M)).trans (h2.trans_eq ?_)
            have := hM_pos.ne'
            field_simp
          have hl1 := log_le_log (Nat.cast_pos.mpr (by omega)) hatail_le_MB
          rw [log_mul (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))] at hl1
          have hlogB_pos : 0 < log (B : ℝ) := lt_of_lt_of_le (by positivity) hlogB_lb
          linarith [hlog_succ_sub B hB_ge, mul_le_mul_of_nonneg_left
            (hsinv2.trans ((div_le_iff₀ hlogB_pos).mpr (by linarith [hlog_succ_sub B hB_ge])) :
              (∑ p ∈ (Ioc B a_tail).filter Nat.Prime, (1 : ℝ) / p) ≤ 113 / 1000) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)]
      linarith
    linarith [qa_reg4_le hM_lb h4M6_lt_n]
open Classical in
@[category API, AMS 11] lemma all_N_main (N : ℕ) :
    representable N = Set.Icc 1 (if IsRepresentable N (m N) then m N else (m N) - 1) := by
  have hH (k : ℕ) (hk : 1 ≤ k) : (harmonic (W k) : ℝ) < (k : ℝ) + 1 := by
    by_cases hk5 : 5 ≤ k
    · exact (harm_W_bds hk5).2
    · interval_cases k
      · simp [W]
      · simp only [W, show ¬(2 ≤ 1) by decide, ↓reduceIte]
        refine (hCeil9_ok 10).trans_lt ?_
        rw [show hCeil9 10 = 2929837209 by decide, S9]
        norm_num
      · rw [W_eq_bds 30]
        refine (hCeil9_ok 30).trans_lt ?_
        rw [show hCeil9 30 = 3995231869 by decide, S9]
        norm_num
      · rw [W_eq_bds 82]
        refine (hCeil9_ok 82).trans_lt ?_
        rw [show hCeil9 82 = 4999598874 by decide, S9]
        norm_num
  have hRep (k : ℕ) (hk : 1 ≤ k) : IsRepresentable (W k) k :=
    if h9 : k ≤ 9 then rep_W_le_9 hk h9
    else if h149 : k ≤ 149 then rep_W_10_149 (by omega) h149
    else by
      have hk150 : 150 ≤ k := by omega
      obtain ⟨G, hGM, hGD, hGcov, hGeta⟩ := binGadget ((4 * k) / 3 + 220) (by omega)
      have hW10 : 33483 ≤ W 10 := (W_bds 33483 33483 (by decide)).1 (by decide)
      exact rep_W_peel (by omega)
        ((by decide : 11520 ≤ 33483).trans (hW10.trans (W_mono (by decide) (by omega))))
        (regime4_valid hk150 G hGM hGD hGcov hGeta (harm_W_bds (by omega)).2)
  have hle_m {k : ℕ} (hk : k ∈ representable N) : k ≤ m N := by
    rcases hk with ⟨_, A, hA, hsum⟩
    refine Nat.le_floor (hsum ▸ ?_)
    rw [harmonic_eq_sum_Icc]
    simp only [one_div]
    exact sum_le_sum_of_subset_of_nonneg hA fun _ _ _ => by positivity
  have hlow (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m N - 1) : IsRepresentable N k := by
    have hm_le : (m N : ℝ) ≤ (harmonic N : ℝ) := mod_cast Nat.floor_le (harm_nn N)
    have hltR : (harmonic (W k) : ℝ) < (harmonic N : ℝ) := by
      linarith [hH k hk1, show (k : ℝ) + 1 ≤ m N from mod_cast (by omega : k + 1 ≤ m N)]
    obtain ⟨A, hA, hs⟩ := hRep k hk1
    exact ⟨A, hA.trans (Icc_subset_Icc_right (harm_mono.lt_iff_lt.mp (mod_cast hltR)).le), hs⟩
  split_ifs with hmRep
  · refine Set.ext fun k => ⟨fun hk => ⟨hk.1, hle_m hk⟩, fun ⟨hk1, hkm⟩ => ⟨hk1, ?_⟩⟩
    rcases eq_or_lt_of_le hkm with rfl | hlt
    · exact hmRep
    · exact hlow k hk1 (by omega)
  · refine Set.ext fun k => ⟨fun hk => ⟨hk.1, ?_⟩, fun ⟨h1, hm⟩ => ⟨h1, hlow k h1 hm⟩⟩
    have := hle_m hk
    have : k ≠ m N := fun h => hmRep (h ▸ hk.2)
    omega

end
end Erdos308

@[expose] public section
namespace Erdos308

/--
Is it true that, for every $N\geq 1$, the set of integers representable as the sum of distinct
unit fractions with denominators from $\{1,\ldots,N\}$ has the shape $\{1,\ldots,m\}$ for some
$m$?
-/
@[category research solved, question, AMS 11]
theorem erdos_308.variants.all_N :
    ∀ N ≥ 1, ∃ m, representable N = Set.Icc 1 m := by
  exact fun N _ => ⟨_, all_N_main N⟩

end Erdos308
