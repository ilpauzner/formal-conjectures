/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 878

*References:*
- [erdosproblems.com/878](https://www.erdosproblems.com/878)
- [Er84e] Erdős, P., _On two unconventional number theoretic functions and on some
  related problems_. (1984), 113--121.
- [Ki26] Kitamura, K., _Erdős Problem #878 in Lean_,
  [GitHub repository](https://github.com/KitaKen1/erdos-878-lean/tree/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76) (2026).
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology Real

namespace Erdos878

/-- The function $f(n)=\sum_{p\mid n}p^{\lfloor\log_p n\rfloor}$. -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

open scoped Classical in
/-- The function $F(n)$ from Erdős Problem 878, with nontrivial terms $a_i \ge 2$. -/
noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).powerset.filter fun A ↦
    A ⊆ Finset.Icc 2 n ∧
      (A : Set ℕ).Pairwise (fun a b ↦ Nat.Coprime a b) ∧
      ∀ a ∈ A, ∀ p, p.Prime → p ∣ a → p ∣ n).sup fun A ↦ ∑ a ∈ A, a

/-- The maximum of an arithmetic function on $\{0,\ldots,x\}$. -/
noncomputable def maxUpTo (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sup g

/-- The function $H(x)=\sum_{1\le n<x}f(n)/n$. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / n

section

set_option linter.style.openClassical false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
open Classical

@[gcongr] theorem maxUpTo_mono {g : ℕ → ℕ} {x y : ℕ} (hxy : x ≤ y) :
    maxUpTo g x ≤ maxUpTo g y :=
  Finset.sup_mono (Finset.range_mono (by omega))

theorem le_maxUpTo {g : ℕ → ℕ} {n x : ℕ} (hnx : n ≤ x) : g n ≤ maxUpTo g x :=
  Finset.le_sup (f := g) (Finset.mem_range_succ_iff.mpr hnx)

/- ### Core Number-Theoretic Machinery for Question 3b -/

/-- For a prime $p$ and positive integer $n$, $\operatorname{q\_p} p\, n = p^{\lfloor \log_p n \rfloor}$ is the largest
power of $p$ not exceeding $n$. -/
abbrev q_p (p n : ℕ) : ℕ := p ^ Nat.log p n

@[gcongr] lemma q_p_mono (p : ℕ) {m n : ℕ} (hmn : m ≤ n) : q_p p m ≤ q_p p n := by
  rcases p with _ | p; · simp [q_p]
  exact Nat.pow_le_pow_right p.succ_pos (Nat.log_mono_right hmn)

def IsAdmissibleTerm (n : ℕ) (P : Finset ℕ) (a : ℕ) : Prop :=
  2 ≤ a ∧ a ≤ n ∧ a ∈ Nat.factoredNumbers P

lemma q_p_admissible {p n : ℕ} (hp : p ∈ n.primeFactors) : IsAdmissibleTerm n {p} (q_p p n) :=
  have hp' := Nat.prime_of_mem_primeFactors hp
  ⟨hp'.two_le.trans <| Nat.le_self_pow (Nat.log_pos hp'.one_lt (Nat.le_of_mem_primeFactors hp)).ne' p,
    Nat.pow_log_le_self p (by grind),
    by simpa using Nat.pow_mul_mem_factoredNumbers hp' _ (n := 1) (s := ∅) (by simp)⟩

/-- Any family of integers in $[2, n]$ with pairwise disjoint prime-factor supports inside
`n.primeFactors` is admissible for $F(n)$, so its sum is at most $F(n)$. -/
lemma sum_le_F_of_disjoint {α : Type*} [DecidableEq α] (n : ℕ)
    (S : Finset α) (g : α → ℕ) (supp : α → Finset ℕ)
    (h_adm : ∀ i ∈ S, IsAdmissibleTerm n (supp i) (g i))
    (h_supp : ∀ i ∈ S, supp i ⊆ n.primeFactors)
    (h_disj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (supp i) (supp j)) :
    ∑ i ∈ S, g i ≤ F n := by
  have hcop (i : α) (hi : i ∈ S) (j : α) (hj : j ∈ S) (hij : i ≠ j) : Nat.Coprime (g i) (g j) :=
    Nat.coprime_of_dvd fun k hk hki hkj ↦ by
      grind [IsAdmissibleTerm, Nat.mem_factoredNumbers', Finset.disjoint_left]
  rw [← Finset.sum_image (f := fun a ↦ a) (by grind [Set.InjOn, Nat.coprime_self, IsAdmissibleTerm])]
  apply Finset.le_sup (f := fun B ↦ ∑ a ∈ B, a)
  rw [Finset.mem_filter, Finset.mem_powerset]
  grind (ematch := 8) [Set.Pairwise, IsAdmissibleTerm, Nat.mem_factoredNumbers', Nat.dvd_of_mem_primeFactors]

/-- **Lemma 2:** For every integer $n \ge 1$, $f(n) < f(2n)$. Consequently any maximizer of $f$
on $[1, y]$ must lie in $(y/2, y]$. -/
lemma lemma2_f_two_mul_gt (n : ℕ) (hn : 1 ≤ n) : f n < f (2 * n) := by
  have hsub : n.primeFactors ⊆ (2 * n).primeFactors :=
    Nat.primeFactors_mono (dvd_mul_left n 2) (by omega)
  have h2_mem : 2 ∈ (2 * n).primeFactors :=
    Nat.Prime.mem_primeFactors Nat.prime_two (dvd_mul_right 2 n) (by omega)
  have hmono : ∀ p ∈ n.primeFactors, q_p p n ≤ q_p p (2 * n) := fun p _ ↦ q_p_mono p (by omega)
  by_cases h2 : 2 ∈ n.primeFactors
  · refine (Finset.sum_lt_sum hmono ⟨2, h2, ?_⟩).trans_le (Finset.sum_le_sum_of_subset hsub)
    dsimp [q_p]; rw [mul_comm 2 n, Nat.log_mul_base (by decide) (by omega)]
    exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  · exact (Finset.sum_le_sum hmono).trans_lt
      (Finset.sum_lt_sum_of_subset hsub h2_mem h2 (by positivity) fun _ _ _ ↦ Nat.zero_le _)

lemma exists_step_crossing (z : ℕ → ℕ) (J n : ℕ) (h0 : z 0 ≤ n) (hJ : n < z J) :
    ∃ j < J, z j ≤ n ∧ n < z (j + 1) := by
  induction J with
  | zero => omega
  | succ m ih => exact if hm : n < z m then let ⟨j, _, _, _⟩ := ih hm; ⟨j, by omega⟩ else ⟨m, by omega⟩

/-- **Lemma 1:** For any two close primes $p < r$ with $98 r < 100 p$ and any $n \ge p^{p^2 + 2}$,
there exists a $\{p, r\}$-smooth integer $z \in [2, n]$ satisfying $98 n < 100 z$. -/
lemma lemma1_exists_smooth_gt (p r : ℕ) (hp : p.Prime) (hr : r.Prime)
    (hpr : p < r) (hclose : 98 * r < 100 * p) {n : ℕ} (hn : p ^ (p ^ 2 + 2) ≤ n) :
    ∃ z : ℕ, IsAdmissibleTerm n {p, r} z ∧ 98 * n < 100 * z := by
  let J := p ^ 2 + 1
  let ℓ := Nat.log p n
  have hp_pos : 0 < p := hp.pos
  have hJ_lt_ℓ : J < ℓ := Nat.le_log_of_pow_le hp.one_lt hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by positivity) hn
  let z (j : ℕ) := p ^ (ℓ - j) * r ^ j
  have hz0 : z 0 ≤ n := by simpa [z, ℓ] using Nat.pow_log_le_self p hn_pos.ne'
  have hzJ : n < z J := calc
    n < p ^ (ℓ + 1) := Nat.lt_pow_succ_log_self hp.one_lt n
    _ = p ^ (ℓ - J) * (p ^ J * p) := by rw [← pow_succ, ← pow_add, show ℓ - J + (J + 1) = ℓ + 1 by omega]
    _ ≤ p ^ (ℓ - J) * (p + 1) ^ J := Nat.mul_le_mul_left _ <|
      (by dsimp [J]; ring_nf; omega : p ^ J * p ≤ p ^ J + J * p ^ (J - 1) * 1).trans
        (pow_add_mul_le_add_pow (by positivity) (by positivity) J)
    _ ≤ z J := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpr J)
  obtain ⟨j, hj_lt, hzj_le, hzj1_gt⟩ := exists_step_crossing z J n hz0 hzJ
  have hzj_rel : z j * r = z (j + 1) * p := by
    dsimp [z]; rw [show ℓ - j = ℓ - (j + 1) + 1 by omega, pow_succ, pow_succ r j]; ring
  have : 2 ≤ n := hp.two_le.trans ((Nat.le_self_pow (by positivity) p).trans hn)
  have := hr.pos
  refine ⟨z j, ⟨by nlinarith, hzj_le, ?_⟩, by nlinarith⟩
  simpa using Nat.pow_mul_mem_factoredNumbers hp (ℓ - j)
    (Nat.pow_mul_mem_factoredNumbers hr j (n := 1) (s := ∅) (by simp))

/- ### The 6 Fixed Primes `Q6` and Three-Pair Lower Bound for `F(m)` -/
abbrev q1 : ℕ := 168000061
abbrev q2 : ℕ := 168000101
abbrev q3 : ℕ := 168000121
abbrev q4 : ℕ := 168000139
abbrev q5 : ℕ := 168000143
abbrev q6 : ℕ := 168000167
abbrev Q6 : Finset ℕ := {q1, q2, q3, q4, q5, q6}
def C6 : ℕ := ∏ p ∈ Q6, p
lemma Q6_card : Q6.card = 6 := by decide
lemma Q6_prime : ∀ p ∈ Q6, p.Prime := by
  intro p hp; fin_cases hp <;> norm_num [q1, q2, q3, q4, q5, q6]
lemma C6_pos : 0 < C6 := Finset.prod_pos fun p hp ↦ (Q6_prime p hp).pos

lemma exists_F_ge_of_smooth :
    ∃ N_smooth : ℕ, ∀ {m : ℕ}, N_smooth ≤ m → ∀ R' ⊆ m.primeFactors,
      Disjoint R' Q6 → Q6 ⊆ m.primeFactors →
      294 * m + 100 * ∑ p ∈ R', q_p p m < 100 * F m := by
  refine ⟨q1 ^ (q1 ^ 2 + 2) + q3 ^ (q3 ^ 2 + 2) + q5 ^ (q5 ^ 2 + 2),
    fun {m} hm R' hR'_sub hR'_disj hQ6_sub ↦ ?_⟩
  rcases lemma1_exists_smooth_gt q1 q2 (Q6_prime q1 (by decide)) (Q6_prime q2 (by decide))
    (by decide) (by decide) (n := m) (by omega) with ⟨b₁, hb₁, hb₁'⟩
  rcases lemma1_exists_smooth_gt q3 q4 (Q6_prime q3 (by decide)) (Q6_prime q4 (by decide))
    (by decide) (by decide) (n := m) (by omega) with ⟨b₂, hb₂, hb₂'⟩
  rcases lemma1_exists_smooth_gt q5 q6 (Q6_prime q5 (by decide)) (Q6_prime q6 (by decide))
    (by decide) (by decide) (n := m) (by omega) with ⟨b₃, hb₃, hb₃'⟩
  clear hm
  let S : Finset ℕ := insert q1 (insert q3 (insert q5 R'))
  let g (ℓ : ℕ) := if ℓ = q1 then b₁ else if ℓ = q3 then b₂ else if ℓ = q5 then b₃ else q_p ℓ m
  let supp (ℓ : ℕ) : Finset ℕ :=
    if ℓ = q1 then {q1, q2} else if ℓ = q3 then {q3, q4} else if ℓ = q5 then {q5, q6} else {ℓ}
  have h_not_in_R' (q : ℕ) (hq : q ∈ Q6) : q ∉ R' := fun hqR ↦ Finset.disjoint_left.mp hR'_disj hqR hq
  have h_sum_eq : ∑ ℓ ∈ S, g ℓ = b₁ + b₂ + b₃ + ∑ p ∈ R', q_p p m := by
    dsimp [S]
    rw [Finset.sum_insert (by grind), Finset.sum_insert (by grind), Finset.sum_insert (by grind),
      Finset.sum_congr rfl (g := fun p ↦ q_p p m) (by grind)]
    grind
  have h_le : ∑ ℓ ∈ S, g ℓ ≤ F m := by
    apply sum_le_F_of_disjoint m S g supp
    · intro ℓ hℓ; dsimp [g, supp]; split_ifs <;>
        [exact hb₁; exact hb₂; exact hb₃; exact q_p_admissible (hR'_sub (by grind))]
    · intro ℓ hℓ; dsimp [supp]; split_ifs <;> grind
    · intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hne; rw [Finset.disjoint_left]; dsimp [supp]; split_ifs <;> grind
  omega

/- ### Single-Step Jump, Superlinearity, and Main Theorem -/
def IsGoodForPrime (p Y : ℕ) : Prop :=
  14 * q_p p ((21 * Y) / 20) < Y

lemma sum_sdiff_erase_two_le (g : ℕ → ℕ) (S Q : Finset ℕ) {a b : ℕ}
    (ha : a ∈ S \ Q) (hb : b ∈ S \ Q) (hab : a ≠ b) :
    ∑ p ∈ S, g p ≤ g a + g b + ∑ p ∈ ((S \ Q).erase a).erase b, g p + ∑ q ∈ Q, g q := by
  have := (Finset.sum_sdiff (s₁ := S \ Q) Finset.sdiff_subset (f := g)).symm.trans_le
    (Nat.add_le_add_right (Finset.sum_le_sum_of_subset (t := Q) (by grind)) _)
  rw [← Finset.add_sum_erase _ g ha, ← Finset.add_sum_erase _ g (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)] at this
  omega

lemma mul_mul_prod_erase_le {n a b : ℕ} (hn : 0 < n) (Q : Finset ℕ)
    (ha : a ∈ n.primeFactors \ Q) (hb : b ∈ n.primeFactors \ Q) (hab : a ≠ b) :
    a * b * ∏ p ∈ ((n.primeFactors \ Q).erase a).erase b, p ≤ n := by
  have := Nat.le_of_dvd hn ((Finset.prod_dvd_prod_of_subset (n.primeFactors \ Q) _ (fun p ↦ p)
    Finset.sdiff_subset).trans n.prod_primeFactors_dvd)
  rwa [← Finset.mul_prod_erase _ (fun p ↦ p) ha,
    ← Finset.mul_prod_erase _ (fun p ↦ p) (Finset.mem_erase.mpr ⟨hab.symm, hb⟩), ← mul_assoc] at this

lemma single_step_jump {N_smooth Y y M : ℕ}
    (h_smooth : ∀ {m : ℕ}, N_smooth ≤ m → ∀ R' ⊆ m.primeFactors,
      Disjoint R' Q6 → Q6 ⊆ m.primeFactors → 294 * m + 100 * ∑ p ∈ R', q_p p m < 100 * F m)
    (h_no_jump : ∀ x ≥ Y, maxUpTo F x ≤ maxUpTo f x) (hY_ge : 20 ≤ Y ∧ 2 * N_smooth ≤ Y)
    (hgood : ∀ p ∈ Q6, IsGoodForPrime p Y) (hy_lo : Y ≤ y) (hy_hi : y ≤ (21 * Y) / 20)
    (hM_pos : 1 ≤ M) (hM_f : 105 * (M + 8) * Y ≤ 100 * maxUpTo f y) :
    ∃ y' : ℕ, y ≤ y' ∧ y' ≤ y + (2 * C6 * Y) / M ^ 2 ∧ 25 * maxUpTo f y + Y ≤ 25 * maxUpTo f y' := by
  obtain ⟨n, hn_le, hn_eq⟩ : ∃ n ≤ y, maxUpTo f y = f n := by
    simpa [maxUpTo, Finset.mem_range_succ_iff] using Finset.exists_mem_eq_sup (Finset.range (y + 1)) ⟨0, by simp⟩ f
  have hn_pos : 0 < n := by rcases eq_or_ne n 0 with rfl | _; · simp [f] at hn_eq; nlinarith
                            omega
  have hy_lt_2n : y < 2 * n := by
    by_contra! hle; have := le_maxUpTo (g := f) hle; have := lemma2_f_two_mul_gt n hn_pos; omega
  have hcard : M + 8 ≤ n.primeFactors.card := by
    have : f n ≤ n * n.primeFactors.card := by
      simpa [f, Nat.mul_comm] using Finset.sum_le_sum fun p _ ↦ Nat.pow_log_le_self p hn_pos.ne'
    have := Nat.mul_le_mul_left (5 * n.primeFactors.card) (show 20 * n ≤ 21 * Y by omega)
    nlinarith
  have h_sdiff : 1 < ((n.primeFactors \ Q6) \ Finset.range M).card := by
    have := Finset.le_card_sdiff Q6 n.primeFactors
    have := Finset.le_card_sdiff (Finset.range M) (n.primeFactors \ Q6)
    rw [Q6_card, Finset.card_range] at *; omega
  obtain ⟨r_a, hra, r_b, hrb, hab⟩ := Finset.one_lt_card.mp h_sdiff
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hra hrb
  let R' := ((n.primeFactors \ Q6).erase r_a).erase r_b
  let D := (∏ p ∈ R', p) * C6
  have hR'_sub : R' ⊆ n.primeFactors \ Q6 := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hR'_prime : ∀ p ∈ R', p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors (Finset.sdiff_subset (hR'_sub hp))
  have hD_pos : 0 < D := mul_pos (Finset.prod_pos fun p hp ↦ (hR'_prime p hp).pos) C6_pos
  have hD_le : D ≤ (2 * C6 * Y) / M ^ 2 := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have := mul_mul_prod_erase_le (by omega) Q6 hra.1 hrb.1 hab
    have : M ^ 2 * ∏ p ∈ R', p ≤ r_a * r_b * ∏ p ∈ R', p := Nat.mul_le_mul_right _ (by nlinarith [sq M])
    have : n ≤ 2 * Y := by omega
    have := C6_pos; dsimp [D]; nlinarith
  let m := D * (n / D + 1)
  have hn_lt_m : n < m := Nat.lt_mul_div_succ n hD_pos
  have hm_le : m ≤ y + D := by have := Nat.mul_div_le n D; dsimp [m]; linarith
  have hR'_sub_m : R' ⊆ m.primeFactors :=
    Nat.primeFactors_prod hR'_prime ▸
      Nat.primeFactors_mono (dvd_trans (dvd_mul_right _ C6) (dvd_mul_right D _)) (by omega)
  have hQ6_sub_m : Q6 ⊆ m.primeFactors :=
    Nat.primeFactors_prod Q6_prime ▸
      Nat.primeFactors_mono (dvd_trans (dvd_mul_left C6 _) (dvd_mul_right D _)) (by omega)
  have hF_ge := h_smooth (m := m) (by omega) R' hR'_sub_m (by rw [Finset.disjoint_left]; grind) hQ6_sub_m
  have hR'_sum_mono : ∑ p ∈ R', q_p p n ≤ ∑ p ∈ R', q_p p m := by gcongr
  have hf_decomp : f n ≤ q_p r_a n + q_p r_b n + ∑ p ∈ R', q_p p n + ∑ q ∈ Q6, q_p q n :=
    sum_sdiff_erase_two_le (fun p ↦ q_p p n) n.primeFactors Q6 hra.1 hrb.1 hab
  have hqa_le : q_p r_a n ≤ n := Nat.pow_log_le_self r_a (by omega)
  have hqb_le : q_p r_b n ≤ n := Nat.pow_log_le_self r_b (by omega)
  have hQ6_lt : 7 * ∑ q ∈ Q6, q_p q n < 6 * n := by
    rw [Finset.mul_sum]
    simpa [Q6_card] using Finset.sum_lt_sum_of_nonempty (s := Q6) ⟨q1, by decide⟩ fun q hq ↦
      show 7 * q_p q n < n by
        have := q_p_mono q (hn_le.trans hy_hi); have := hgood q hq; dsimp [IsGoodForPrime] at this; omega
  have : F m ≤ maxUpTo f (y + D) := (le_maxUpTo hm_le).trans (h_no_jump (y + D) (by omega))
  exact ⟨y + D, by omega, by omega, by omega⟩

/-- **Lemma 3:** For any multiplier $R$, $\operatorname{maxUpTo} f\, y > R y$ for all sufficiently large $y$. -/
lemma lemma3_superlinear_maxUpTo_f (R : ℕ) :
    ∃ N₂ : ℕ, ∀ y ≥ N₂, R * y < maxUpTo f y := by
  have h_tend := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦
    Set.indicator_nonneg (fun _ _ ↦ by positivity) n).mp not_summable_one_div_on_primes
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (R : ℝ) + 1 ≤ ∑ p ∈ N.primesBelow, ((p : ℝ)⁻¹) := by
    simpa [Nat.primesBelow_eq_filter_range, Finset.sum_filter, Set.indicator] using
      (h_tend.eventually (eventually_ge_atTop (2 * (R : ℝ) + 1))).exists
  have hprime : ∀ p ∈ N.primesBelow, p.Prime := fun p hp ↦ Nat.prime_of_mem_primesBelow hp
  let P := ∏ p ∈ N.primesBelow, p
  have hP_pos : 0 < P := Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  refine ⟨2 * P, fun y hy ↦ ?_⟩
  let m := P * (y / P)
  have hy_lt : y < 2 * m := by
    have := Nat.mod_lt y hP_pos; have := Nat.mod_add_div y P; dsimp [m] at *; omega
  have hterm : ∀ p ∈ N.primesBelow, (m : ℝ) * ((p : ℝ)⁻¹) ≤ (q_p p m : ℝ) := fun p hp ↦ by
    rw [mul_inv_le_iff₀ (by exact_mod_cast (hprime p hp).pos)]
    exact_mod_cast (by simpa [pow_succ] using (Nat.lt_pow_succ_log_self (hprime p hp).one_lt m).le)
  have hsub : N.primesBelow ⊆ m.primeFactors :=
    Nat.primeFactors_prod hprime ▸ Nat.primeFactors_mono (dvd_mul_right P _) (by omega)
  have h_mass : (m : ℝ) * ∑ p ∈ N.primesBelow, ((p : ℝ)⁻¹) ≤ (maxUpTo f y : ℝ) := calc
    (m : ℝ) * ∑ p ∈ N.primesBelow, ((p : ℝ)⁻¹) = ∑ p ∈ N.primesBelow, (m : ℝ) * ((p : ℝ)⁻¹) := Finset.mul_sum ..
    _ ≤ ∑ p ∈ N.primesBelow, (q_p p m : ℝ) := Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ m.primeFactors, (q_p p m : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ = (f m : ℝ) := by simp [f]
    _ ≤ (maxUpTo f y : ℝ) := by exact_mod_cast le_maxUpTo (Nat.mul_div_le y P)
  have : (y : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hy_lt
  exact_mod_cast (by nlinarith : (R * y : ℝ) < (maxUpTo f y : ℝ))

/-- **Lemma 4:** For any $X_0$, there exists $Y \ge \max(X_0, 20)$ among $Y_0 \cdot 15^m$ ($0 \le m < 7$)
that is simultaneously good ($14 q_p(\lfloor 21Y/20 \rfloor) < Y$) for all 6 primes in `Q6`. -/
lemma lemma4_exists_good_Y (X₀ : ℕ) :
    ∃ Y : ℕ, max X₀ 20 ≤ Y ∧ ∀ p ∈ Q6, IsGoodForPrime p Y := by
  let Y₀ := max X₀ 20
  let bad (p : ℕ) := (Finset.range 7).filter fun m ↦ ¬ IsGoodForPrime p (Y₀ * 15 ^ m)
  have hbad (p : ℕ) (hp : p ∈ Q6) : (bad p).card ≤ 1 := Finset.card_le_one.mpr fun m₁ hm₁ m₂ hm₂ ↦ by
    simp only [bad, Finset.mem_filter, Finset.mem_range, IsGoodForPrime, not_lt] at hm₁ hm₂
    wlog hab : m₁ < m₂ generalizing m₁ m₂
    · exact (lt_or_eq_of_le (not_lt.mp hab)).elim (fun h ↦ (this m₂ m₁ hm₂ hm₁ h).symm) Eq.symm
    have hp' := Q6_prime p hp
    have : 168000000 ≤ p := (by decide : ∀ q ∈ Q6, 168000000 ≤ q) p hp
    have : 20 ≤ Y₀ := le_max_right _ _
    set Ya := Y₀ * 15 ^ m₁; set Yb := Y₀ * 15 ^ m₂
    set Qa := q_p p ((21 * Ya) / 20); set Qb := q_p p ((21 * Yb) / 20)
    have hpow : 1 ≤ 15 ^ m₁ ∧ 15 ^ (m₁ + 1) ≤ 15 ^ m₂ ∧ 15 ^ m₂ ≤ 15 ^ 6 :=
      ⟨Nat.one_le_pow _ _ (by decide), Nat.pow_le_pow_right (by decide) hab,
       Nat.pow_le_pow_right (by decide) (by omega)⟩
    have hY : 20 ≤ Ya ∧ 15 * Ya ≤ Yb ∧ Yb ≤ 11390625 * Ya :=
      ⟨by dsimp [Ya]; nlinarith,
       by dsimp [Ya, Yb]; linarith [show Y₀ * (15 ^ m₁ * 15) ≤ Y₀ * 15 ^ m₂ from Nat.mul_le_mul_left Y₀ hpow.2.1],
       by dsimp [Ya, Yb]; nlinarith⟩
    have hQa : Qa ≤ (21 * Ya) / 20 := Nat.pow_log_le_self p (by omega)
    have hQb : Qb ≤ (21 * Yb) / 20 := Nat.pow_log_le_self p (by omega)
    have hlt : Nat.log p ((21 * Ya) / 20) < Nat.log p ((21 * Yb) / 20) :=
      (Nat.pow_lt_pow_iff_right hp'.one_lt).mp (by omega : Qa < Qb)
    have : Qa * p ≤ Qb := by dsimp [Qa, Qb, q_p]; rw [← pow_succ]; exact Nat.pow_le_pow_right hp'.pos hlt
    have : 20 * Qb ≤ 21 * Yb ∧ Ya ≤ 14 * Qa := by omega
    nlinarith
  have hcard : (Q6.biUnion bad).card < (Finset.range 7).card :=
    Finset.card_biUnion_le.trans_lt ((Finset.sum_le_sum hbad).trans_lt (by simp))
  obtain ⟨m, hm1, hm2⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨Y₀ * 15 ^ m, Nat.le_mul_of_pos_right _ (by positivity), fun p hp ↦ by grind⟩

/-- **Main Theorem (`erdos_878_q3_disproved`):** For every threshold $X_0 \in \mathbb{N}$, there exists
$x \ge X_0$ such that $\operatorname{maxUpTo} f\, x < \operatorname{maxUpTo} F\, x$. -/
theorem erdos_878_q3_disproved : ∀ X₀ : ℕ, ∃ x ≥ X₀, maxUpTo f x < maxUpTo F x := by
  intro X₀
  by_contra! h_no_jump
  let A := 2000 * C6 + 1
  obtain ⟨N_smooth, h_smooth⟩ := exists_F_ge_of_smooth
  obtain ⟨N₂, hN₂⟩ := lemma3_superlinear_maxUpTo_f (2 * (A + 10))
  obtain ⟨Y, hY_max, hgood⟩ := lemma4_exists_good_Y (max X₀ (max N₂ (2 * N_smooth)))
  have ⟨hY_X₀, hY_N₂, hY_smooth⟩ : X₀ ≤ Y ∧ N₂ ≤ Y ∧ (20 ≤ Y ∧ 2 * N_smooth ≤ Y) := by
    simp only [max_le_iff] at hY_max; omega
  have := C6_pos
  have iter {y M : ℕ} (hy : Y ≤ y) (hM : 1 ≤ M) (hMf : 105 * (M + 8) * Y ≤ 100 * maxUpTo f y)
      (j : ℕ) (hj : y + j * ((2 * C6 * Y) / M ^ 2) ≤ (21 * Y) / 20) :
      ∃ y' ≥ y, y' ≤ y + j * ((2 * C6 * Y) / M ^ 2) ∧ 25 * maxUpTo f y + j * Y ≤ 25 * maxUpTo f y' := by
    induction j with
    | zero => exact ⟨y, le_rfl, by simp, by simp⟩
    | succ r ih =>
      have : r * ((2 * C6 * Y) / M ^ 2) ≤ (r + 1) * ((2 * C6 * Y) / M ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      obtain ⟨y_r, hy_r_lo, hy_r_hi, hy_r_Mf⟩ := ih (by omega)
      obtain ⟨y', hy'_lo, hy'_hi, hy'_Mf⟩ := single_step_jump (y := y_r) h_smooth
        (fun x hx ↦ h_no_jump x (hY_X₀.trans hx)) hY_smooth hgood (by omega) (by omega) hM (by omega)
      exact ⟨y', by omega, by nlinarith, by nlinarith⟩
  let rem (k : ℕ) : ℝ := (54 * C6 * Y : ℝ) / (A + k : ℝ)
  have le_cap {z k : ℕ} (hz : 20 * ((z : ℝ) + rem k) ≤ 21 * (Y : ℝ)) : z ≤ (21 * Y) / 20 := by
    rw [Nat.le_div_iff_mul_le (by decide)]
    have : 0 ≤ rem k := by dsimp [rem]; positivity
    exact_mod_cast (by linarith : (z : ℝ) * 20 ≤ 21 * (Y : ℝ))
  have h_seq (k : ℕ) : ∃ y_k ≥ Y, 20 * ((y_k : ℝ) + rem k) ≤ 21 * (Y : ℝ) ∧
      105 * (A + 1 + k + 8) * Y ≤ 100 * maxUpTo f y_k := by
    induction k with
    | zero =>
      refine ⟨Y, le_rfl, ?_, by have := hN₂ Y hY_N₂; linarith⟩
      have : 20 * rem 0 ≤ Y := by
        dsimp [rem, A]; rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; push_cast; nlinarith
      linarith
    | succ k ih =>
      obtain ⟨y_k, hy_k_lo, hy_k_sum, hy_k_Mf⟩ := ih
      let M := A + 1 + k
      let step := (2 * C6 * Y) / M ^ 2
      have h_step_nat : 27 * step * ((A + k) * (A + (k + 1))) ≤ 54 * C6 * Y := by
        have := Nat.div_mul_le_self (2 * C6 * Y) (M ^ 2); dsimp [M, step] at *; nlinarith
      have h_step_real : ((27 * step : ℕ) : ℝ) ≤ rem k - rem (k + 1) := by
        dsimp [rem]; rw [div_sub_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
        exact (by exact_mod_cast h_step_nat : _ ≤ (54 * C6 * Y : ℝ)).trans_eq (by push_cast; ring)
      obtain ⟨y', hy'_lo, hy'_hi, hy'_Mf⟩ := iter hy_k_lo (by omega) hy_k_Mf 27
        (le_cap (k := k + 1) (by push_cast at h_step_real ⊢; linarith))
      have : (y' : ℝ) ≤ y_k + (27 * step : ℕ) := by exact_mod_cast hy'_hi
      exact ⟨y', hy_k_lo.trans hy'_lo, by linarith, by linarith⟩
  let K := maxUpTo f ((21 * Y) / 20) + 1
  obtain ⟨y_K, _, hy_K_sum, hy_K_Mf⟩ := h_seq K
  have : maxUpTo f y_K < K := (maxUpTo_mono (le_cap hy_K_sum)).trans_lt (by dsimp [K]; omega)
  nlinarith

end

/-- Is it true that, for almost all $n$, $f(n)=o(n\log\log n)$ and
$F(n)\gg n\log\log n$?

The answer is yes; a Lean proof is given in [Ki26]. -/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/FixedLoss.lean#L120"]
theorem erdos_878.parts.i :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      (fun n : A ↦ (f n : ℝ)) =o[atTop]
        (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) ∧
      (fun n : A ↦ (n : ℝ) * Real.log (Real.log (n : ℝ))) =O[atTop]
        (fun n : A ↦ (F n : ℝ)) := by
  sorry

/-- Is it true that $\max_{n\le x}f(n)\sim x\log x/\log\log x$?

The answer is yes; a Lean proof is given in [Ki26]. -/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/TrackBEndpointParameters.lean#L630"]
theorem erdos_878.parts.ii :
    Tendsto (fun x : ℕ ↦
        (maxUpTo f x : ℝ) / ((x : ℝ) * Real.log x / Real.log (Real.log x)))
        atTop (𝓝 1) := by
  sorry

/-- Is it true that, for all $x$, $\max_{n\le x}f(n)=\max_{n\le x}F(n)$?
Barreto noted that this is false at $x=210$. -/
@[category research solved, question, AMS 11]
theorem erdos_878.parts.iii_all :
    ¬ ∀ x : ℕ, maxUpTo f x = maxUpTo F x := by
  sorry

/-- Is it true that, for all large $x$, $\max_{n\le x}f(n)=\max_{n\le x}F(n)$? -/
@[category research solved, question, AMS 11]
theorem erdos_878.parts.iii_eventually :
    ¬ ∀ᶠ x : ℕ in atTop, maxUpTo f x = maxUpTo F x := by
  simpa [not_eventually, frequently_atTop] using fun B ↦
    (erdos_878_q3_disproved B).imp fun x ⟨hx, hlt⟩ ↦ ⟨hx, hlt.ne⟩

def erdos_878.parts.iv.answer : ℕ → ℝ := by sorry

/-- Find an asymptotic formula for the number of $n<x$ such that $f(n)=F(n)$. -/
@[category research open, question value, AMS 11]
theorem erdos_878.parts.iv :
    (fun x : ℕ ↦
      (((Finset.Ico 1 x).filter fun n ↦ f n = F n).card : ℝ))
      ~[atTop] erdos_878.parts.iv.answer := by
  sorry

def erdos_878.parts.v.answer : ℕ → ℝ := by sorry

/-- Find an asymptotic formula for $H(x)=\sum_{n<x}f(n)/n$. -/
@[category research open, question value, AMS 11]
theorem erdos_878.parts.v :
    H ~[atTop] erdos_878.parts.v.answer := by
  sorry

/-- Is it true that $H(x)\ll x\log\log\log\log x$? -/
@[category research open, question, AMS 11]
theorem erdos_878.parts.vi :
    H =O[atTop] fun x : ℕ ↦
        (x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ)))) := by
  sorry

/-- Erdős [Er84e] proved that $\max_{n\le x}f(n)\sim x\log x/\log\log x$
for a sequence of $x\to\infty$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.second_question_subsequence :
    ∃ X : ℕ → ℕ, Tendsto X atTop atTop ∧
      Tendsto (fun k : ℕ ↦
        (maxUpTo f (X k) : ℝ) /
          ((X k : ℝ) * Real.log (X k) / Real.log (Real.log (X k))))
        atTop (𝓝 1) := by
  sorry

/-- For almost all $n$, $F(n)\sim \frac12 n\log\log n$.
A Lean proof is given in [Ki26]. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/SharpFirstAsymptotic.lean#L168"]
theorem erdos_878.variants.proposed_first_question_sharp :
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n : A ↦
        (F n : ℝ) / ((n : ℝ) * Real.log (Real.log (n : ℝ))))
        atTop (𝓝 (1 / 2 : ℝ)) := by
  sorry

/-- Erdős [Er84e] showed that $\limsup_{x\to\infty}H(x)/x=\infty$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_div_self_limsup_infinite :
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C ≤ H x / (x : ℝ) := by
  sorry

/-- Erdős [Er84e] showed that $\liminf_{x\to\infty}H(x)/x<\infty$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_div_self_liminf_finite :
    ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, H x / (x : ℝ) ≤ C := by
  sorry

/-- Erdős [Er84e] proved that $H(x)\ll x\log\log\log x$. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_upper_triple_log :
    H =O[atTop] fun x : ℕ ↦
      (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) := by
  sorry

/-- Erdős [Er84e] proved that $x\log\log\log\log x\ll H(x)$;
this entry records the infinitely-often consequence. -/
@[category research solved, AMS 11]
theorem erdos_878.variants.H_lower_quadruple_log_infinitely_often :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℕ in atTop,
      c * ((x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ))))) ≤ H x := by
  sorry

/-- The function $h(x)=\max_{n\le x}\omega(n)$ from [Er84e]. -/
noncomputable def h (x : ℕ) : ℕ :=
  maxUpTo (fun n ↦ n.primeFactors.card) x

/-- The function $m(x)=\max_{n\le x}f(n)$ from [Er84e]. -/
noncomputable def m (x : ℕ) : ℕ := maxUpTo f x

/-- Formula (17) of [Er84e]: does $(x h(x)-m(x))/x\to\infty$?

The answer is yes; a Lean proof is given in [Ki26]. -/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-878-lean/blob/d4a8eecf0606b3eee7342c2040a31c8c30eb5d76/lean/Erdos878/Formula17.lean#L192"]
theorem erdos_878.variants.original_formula_17 :
    Tendsto (fun x : ℕ ↦
        ((x * h x - m x : ℕ) : ℝ) / (x : ℝ)) atTop atTop := by
  sorry

end Erdos878
