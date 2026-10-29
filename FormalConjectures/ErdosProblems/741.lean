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
# Erdős Problem 741

*References:*
 - [erdosproblems.com/741](https://www.erdosproblems.com/741)
 - [Er94b] Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
    Math. Pannon. (1994), 261-269.
-/

@[expose] public section

open scoped Pointwise
open Set

namespace Erdos741


/-- Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive upper density.
Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$
both have positive upper density?

This was proved by the DeepMind prover agent.
-/
@[category research solved, question, AMS 5, formal_proof using formal_conjectures at
"https://github.com/google-deepmind/formal-conjectures/blob/9d492049e42167b0d2fd58a9e91da3bf160172b5/FormalConjectures/ErdosProblems/741.lean#L228"]
theorem erdos_741.parts.i : ∀ A : Set ℕ, 0 < upperDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < upperDensity (A₁ + A₁)
    ∧ 0 < upperDensity (A₂ + A₂) := by
  sorry

@[category API, AMS 5]
lemma lowerDensity_pos_of_forall_ge {S : Set ℕ} {c : ℝ} (hc : 0 < c) {n₀ : ℕ}
    (h : ∀ n ≥ n₀, c * (n : ℝ) ≤ ((S ∩ Iio n).ncard : ℝ)) :
    0 < lowerDensity S := by
  rw [Set.lowerDensity, Filter.liminf_eq]
  have hb : BddAbove {a : ℝ | ∀ᶠ n : ℕ in Filter.atTop, a ≤ S.partialDensity univ n} :=
    ⟨1, fun _ ha => ha.exists.choose_spec.trans (Set.partialDensity_le_one S univ _)⟩
  refine hc.trans_le (le_csSup hb (Filter.eventually_atTop.mpr ⟨max n₀ 1, fun n hn => ?_⟩))
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  simpa [Set.partialDensity, le_div_iff₀ hn_pos] using h n (le_of_max_le_left hn)

@[category API, AMS 5]
lemma exists_eventually_ge_of_lowerDensity_pos {S : Set ℕ} (h : 0 < lowerDensity S) :
    ∃ K N₀ : ℕ, ∀ n ≥ N₀, n ≤ K * (S ∩ Iio n).ncard := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / lowerDensity S)
  have hK_pos : (0 : ℝ) < K := (div_pos one_pos h).trans hK
  have hlt : 1 / (K : ℝ) < Filter.atTop.liminf (fun n => S.partialDensity univ n) := by
    change 1 / (K : ℝ) < lowerDensity S
    exact (div_lt_iff₀ hK_pos).mpr (by rw [mul_comm]; exact (div_lt_iff₀ h).mp hK)
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => S.partialDensity univ n) :=
    ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun _ => by positivity)⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_lt_liminf hlt hbdd)
  refine ⟨K, max N₀ 1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hd : 1 / (K : ℝ) ≤ ((S ∩ Iio n).ncard : ℝ) / n := by
    simpa [Set.partialDensity] using (hN₀ n (le_of_max_le_left hn)).le
  rw [div_le_div_iff₀ hK_pos hn_pos, one_mul, mul_comm] at hd
  exact_mod_cast hd

def digit (B x t : ℕ) : ℕ := (x / B ^ t) % B

@[category API, AMS 5]
lemma digit_add_mul_pow {B d z w t : ℕ} (hB : 0 < B) (hz : B ^ d ∣ z) (ht : t < d) :
    digit B (z + w) t = digit B w t := by
  obtain ⟨q, rfl⟩ := (Nat.pow_dvd_pow B ht).trans hz
  simp [digit, pow_succ, mul_assoc, Nat.mul_add_div (pow_pos hB t)]

@[category API, AMS 5]
lemma digit_add_pow {B t t' w : ℕ} (hB : 0 < B) (hw : digit B w t + 1 < B) :
    digit B (w + B ^ t) t' = digit B w t' + if t' = t then 1 else 0 := by
  rcases lt_trichotomy t' t with hlt | rfl | hgt
  · rw [if_neg hlt.ne, add_zero, add_comm, digit_add_mul_pow hB (Nat.pow_dvd_pow B hlt) (by omega)]
  · rw [if_pos rfl]
    dsimp [digit] at hw ⊢
    rw [Nat.add_div_right _ (pow_pos hB _), Nat.add_mod,
      Nat.mod_eq_of_lt (by omega : 1 < B), Nat.mod_eq_of_lt hw]
  · rw [if_neg hgt.ne', add_zero]
    dsimp [digit] at hw ⊢
    have hstep : (w + B ^ t) / B ^ (t + 1) = w / B ^ (t + 1) := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        Nat.add_div_right _ (pow_pos hB t)]
      conv_lhs => rw [← Nat.div_add_mod (w / B ^ t) B, add_assoc]
      rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hw, add_zero]
    rw [← Nat.add_sub_of_le (hgt : t + 1 ≤ t'), pow_add, ← Nat.div_div_eq_div_mul, hstep,
      Nat.div_div_eq_div_mul]

@[category API, AMS 5]
lemma mul_add_div_mod (a : ℕ) {m b : ℕ} (hb : b < m) :
    (a * m + b) / m = a ∧ (a * m + b) % m = b :=
  ⟨by rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add],
   by rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]⟩

def boundedDigits (B K : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | d + 1 => (boundedDigits B K d ×ˢ Finset.range K).image fun p => p.1 * B + p.2

@[category API, AMS 5]
lemma boundedDigits_spec {B K : ℕ} (hKB : K ≤ B) :
    ∀ {d x}, x ∈ boundedDigits B K d → x < B ^ d ∧ ∀ s < d, digit B x s < K
  | 0, x, hx => by simp [boundedDigits] at hx; subst hx; simp
  | d + 1, _, hx => by
    obtain ⟨⟨q, r⟩, hqr, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_product, Finset.mem_range] at hqr
    obtain ⟨hq_lt, hq_dig⟩ := boundedDigits_spec hKB hqr.1
    have hrB : r < B := hqr.2.trans_le hKB
    refine ⟨by rw [pow_succ]; nlinarith, fun s hs => ?_⟩
    rcases s with _ | s
    · dsimp [digit]; rw [Nat.div_one, (mul_add_div_mod q hrB).2]; exact hqr.2
    · dsimp [digit]; rw [pow_succ', ← Nat.div_div_eq_div_mul, (mul_add_div_mod q hrB).1]
      exact hq_dig s (by omega)

@[category API, AMS 5]
lemma boundedDigits_card {B K : ℕ} (hKB : K ≤ B) :
    ∀ d, (boundedDigits B K d).card = K ^ d
  | 0 => by simp [boundedDigits]
  | d + 1 => by
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * B + p.2)
        (boundedDigits B K d ×ˢ Finset.range K : Finset (ℕ × ℕ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
      dsimp only at heq
      have h1 : p₁.1 = p₂.1 := by
        rw [← (mul_add_div_mod p₁.1 (hp₁.2.trans_le hKB)).1, heq,
          (mul_add_div_mod p₂.1 (hp₂.2.trans_le hKB)).1]
      exact Prod.ext h1 (by rw [h1] at heq; omega)
    rw [boundedDigits, Finset.card_image_of_injOn hinj, Finset.card_product,
      boundedDigits_card hKB d, Finset.card_range, pow_succ]

@[category API, AMS 5]
lemma add_mod_eq_zero_iff {m x a : ℕ} (hm : 0 < m) :
    (x + a) % m = 0 ↔ x % m = (m - a % m) % m := by
  have hx := Nat.mod_lt x hm
  have ha := Nat.mod_lt a hm
  have hrem := Nat.mod_lt (x % m + a % m) hm
  have hdm := Nat.div_add_mod (x % m + a % m) m
  have hq : (x % m + a % m) / m < 2 := Nat.div_lt_of_lt_mul (by omega)
  rw [Nat.add_mod]
  rcases eq_or_ne (a % m) 0 with h0 | hne
  · simp [h0, Nat.mod_eq_of_lt hx]
  · rw [Nat.mod_eq_of_lt (by omega : m - a % m < m)]
    rcases h : (x % m + a % m) / m with _ | _ | k
    · rw [h, mul_zero, zero_add] at hdm; omega
    · rw [h, Nat.zero_add, mul_one] at hdm; omega
    · omega

@[category API, AMS 5]
lemma pow_le_pred_pow_add {B : ℕ} (hB : 1 ≤ B) :
    ∀ n : ℕ, B ^ n ≤ (B - 1) ^ n + n * B ^ (n - 1)
  | 0 => by simp
  | 1 => by simp; omega
  | n + 2 => by
    have ih := pow_le_pred_pow_add hB (n + 1)
    simp only [Nat.add_sub_cancel] at ih ⊢
    have hle : (B - 1) * B ^ n ≤ B ^ (n + 1) := by
      rw [pow_succ']; exact Nat.mul_le_mul_right _ (Nat.sub_le B 1)
    calc
      B ^ (n + 2) = (B - 1) * B ^ (n + 1) + B ^ (n + 1) := by
        rw [← add_one_mul, Nat.sub_add_cancel hB, pow_succ']
      _ ≤ (B - 1) * ((B - 1) ^ (n + 1) + (n + 1) * B ^ n) + B ^ (n + 1) := by gcongr
      _ = (B - 1) ^ (n + 2) + (n + 1) * ((B - 1) * B ^ n) + B ^ (n + 1) := by rw [pow_succ']; ring
      _ ≤ (B - 1) ^ (n + 2) + (n + 1) * B ^ (n + 1) + B ^ (n + 1) := by gcongr
      _ = (B - 1) ^ (n + 2) + (n + 2) * B ^ (n + 1) := by ring

-- Parameters, configurations, scales, and linear forms

def qParam (k : ℕ) : ℕ := k + 2
def mParam (k : ℕ) : ℕ := 2 * qParam k
abbrev d0Param (k : ℕ) : ℕ := mParam k * (2 * mParam k)
abbrev dParam (k : ℕ) : ℕ := d0Param k + 1
def BParam (k : ℕ) : ℕ := 8 * (mParam k) ^ 3
def QParam (k : ℕ) : ℕ := (BParam k) ^ (dParam k)

abbrev Cfg (k : ℕ) :=
  (Fin (qParam k) ↪ Fin (mParam k)) × (Fin (qParam k) → Fin (mParam k) ↪ Fin (2 * mParam k))

@[irreducible] noncomputable def RParam (k : ℕ) : ℕ := Fintype.card (Cfg k)
@[irreducible] noncomputable def getCfg (k : ℕ) (r : Fin (RParam k)) : Cfg k :=
  (Fintype.equivFin (Cfg k)).symm (r.cast (by unfold RParam; rfl))

@[category API, AMS 5]
lemma RParam_pos (k : ℕ) : 0 < RParam k := by
  unfold RParam
  exact Fintype.card_pos_iff.mpr ⟨(Fin.castLEEmb (by dsimp [mParam]; omega),
    fun _ => Fin.castLEEmb (by omega))⟩

@[category API, AMS 5]
lemma exists_getCfg_eq (k : ℕ) (cfg : Cfg k) : ∃ r : Fin (RParam k), getCfg k r = cfg := by
  unfold RParam getCfg
  exact ⟨Fintype.equivFin (Cfg k) cfg, Equiv.symm_apply_apply _ _⟩

def stepScale (k base : ℕ) : ℕ → ℕ
  | 0 => base
  | r + 1 => 4 * mParam k * stepScale k base r

noncomputable def M_end : ℕ → ℕ
  | 0 => 16
  | k + 1 =>
    stepScale k
      (10 * mParam k * (2 * mParam k * (2 * (2 * mParam k * (4 * M_end k * QParam k)))))
      (RParam k)

noncomputable def L0 (k : ℕ) : ℕ := 4 * M_end k * QParam k
noncomputable def DHalf (k : ℕ) : ℕ := 2 * mParam k * L0 k
noncomputable def D0 (k : ℕ) : ℕ := 2 * DHalf k
noncomputable def PParam (k : ℕ) : ℕ := 2 * mParam k * D0 k
noncomputable def N0 (k : ℕ) : ℕ := 10 * mParam k * PParam k
noncomputable def NScale (k r : ℕ) : ℕ := stepScale k (N0 k) r

@[category API, AMS 5]
lemma M_end_succ (k : ℕ) : M_end (k + 1) = NScale k (RParam k) := rfl

@[category API, AMS 5]
lemma NScale_succ (k r : ℕ) : NScale k (r + 1) = 4 * mParam k * NScale k r := rfl

@[category API, AMS 5]
lemma mParam_ge_four (k : ℕ) : 4 ≤ mParam k := by simp [mParam, qParam]; omega

@[category API, AMS 5]
lemma mParam_lt_BParam (k : ℕ) : mParam k < BParam k := by
  have hm := mParam_ge_four k
  have : mParam k * 1 < mParam k * (8 * (mParam k) ^ 2) :=
    (mul_lt_mul_iff_right₀ (by omega)).mpr (by nlinarith)
  dsimp [BParam]; nlinarith

@[category API, AMS 5]
lemma BParam_pos (k : ℕ) : 0 < BParam k :=
  lt_trans (by have := mParam_ge_four k; omega) (mParam_lt_BParam k)

@[category API, AMS 5]
lemma N0_eq_mul_L0 (k : ℕ) : N0 k = 80 * (mParam k) ^ 3 * L0 k := by
  dsimp [N0, PParam, D0, DHalf]; ring

@[category API, AMS 5]
lemma le_stepScale (k base : ℕ) : ∀ r, base ≤ stepScale k base r
  | 0 => le_rfl
  | r + 1 => (le_stepScale k base r).trans
      (Nat.le_mul_of_pos_left _ (by have := mParam_ge_four k; omega))

@[category API, AMS 5]
lemma M_end_ge_16 : ∀ k : ℕ, 16 ≤ M_end k
  | 0 => le_rfl
  | k + 1 => by
    have hm3 : 1 ≤ (mParam k) ^ 3 := Nat.one_le_pow _ _ (by have := mParam_ge_four k; omega)
    have hL : 16 ≤ L0 k := by
      have := M_end_ge_16 k; have : 0 < QParam k := pow_pos (BParam_pos k) _; dsimp [L0]; nlinarith
    have hN : 16 ≤ N0 k := by rw [N0_eq_mul_L0]; nlinarith
    rw [M_end_succ]; exact hN.trans (le_stepScale k (N0 k) (RParam k))

@[category API, AMS 5]
lemma scale_chain (k : ℕ) :
    4 * M_end k ≤ L0 k ∧ QParam k < L0 k ∧ 2 * L0 k < DHalf k ∧ D0 k = 2 * DHalf k ∧
    (mParam k + 1) * D0 k < PParam k ∧ D0 k < PParam k ∧ 40 * PParam k ≤ N0 k := by
  have hM := M_end_ge_16 k
  have hm := mParam_ge_four k
  have hQ : 0 < QParam k := pow_pos (BParam_pos k) _
  have hL : 1 ≤ L0 k := by dsimp [L0]; nlinarith
  have hDH : 1 ≤ DHalf k := by dsimp [DHalf]; nlinarith
  have hD : 1 ≤ D0 k := by dsimp [D0]; omega
  exact ⟨by dsimp [L0]; nlinarith, by dsimp [L0]; nlinarith, by dsimp [DHalf]; nlinarith, rfl,
    by dsimp [PParam]; nlinarith, by dsimp [PParam]; nlinarith, by dsimp [N0]; nlinarith⟩

@[category API, AMS 5]
lemma NScale_strictMono (k : ℕ) : StrictMono (NScale k) :=
  strictMono_nat_of_lt_succ fun r => by
    have hm := mParam_ge_four k
    have hN0 : 1 ≤ N0 k := by have := M_end_ge_16 k; have := scale_chain k; omega
    have hpos : 1 ≤ NScale k r := hN0.trans (le_stepScale k (N0 k) r)
    rw [NScale_succ]; nlinarith

@[category API, AMS 5]
lemma M_end_strictMono : StrictMono M_end :=
  strictMono_nat_of_lt_succ fun k => by
    have sc := scale_chain k
    have hlt : M_end k < NScale k 0 := by change M_end k < N0 k; omega
    rw [M_end_succ]
    exact hlt.trans_le ((NScale_strictMono k).monotone (Nat.zero_le (RParam k)))

@[category API, AMS 5]
lemma PParam_dvd_NScale (k : ℕ) : ∀ r, PParam k ∣ NScale k r
  | 0 => ⟨10 * mParam k, by dsimp [NScale, stepScale, N0]; ring⟩
  | r + 1 => dvd_mul_of_dvd_right (PParam_dvd_NScale k r) _

@[category API, AMS 5]
lemma QParam_dvd_D0 (k : ℕ) : QParam k ∣ D0 k :=
  ⟨16 * mParam k * M_end k, by dsimp [D0, DHalf, L0]; ring⟩

abbrev coordIdx (k : ℕ) (j : Fin (mParam k)) (u : Fin (2 * mParam k)) : ℕ :=
  (finProdFinEquiv (j, u)).val + 1

noncomputable def coeffPair (k : ℕ) (cfg : Cfg k) (p : Fin (mParam k) × Fin (2 * mParam k)) : ℕ :=
  open scoped Classical in
  if h : ∃ iv : Fin (qParam k) × Fin (mParam k), cfg.1 iv.1 = p.1 ∧ cfg.2 iv.1 iv.2 = p.2 then
    h.choose.2.val
  else 0

@[category API, AMS 5]
lemma coeffPair_apply (k : ℕ) (cfg : Cfg k) (i : Fin (qParam k)) (v : Fin (mParam k)) :
    coeffPair k cfg (cfg.1 i, cfg.2 i v) = v.val := by
  classical
  have hex : ∃ iv : Fin (qParam k) × Fin (mParam k),
      cfg.1 iv.1 = cfg.1 i ∧ cfg.2 iv.1 iv.2 = cfg.2 i v := ⟨(i, v), rfl, rfl⟩
  rw [coeffPair, dif_pos hex]
  obtain ⟨hi, hv⟩ := hex.choose_spec
  rw [cfg.1.injective hi] at hv
  exact congrArg Fin.val ((cfg.2 i).injective hv)

noncomputable def hiForm (k : ℕ) (cfg : Cfg k) (q : ℕ) : ℕ :=
  ∑ p : Fin (mParam k) × Fin (2 * mParam k),
    coeffPair k cfg p * digit (BParam k) q (finProdFinEquiv p).val

noncomputable def linForm (k : ℕ) (cfg : Cfg k) (x : ℕ) : ℕ :=
  x % BParam k + hiForm k cfg (x / BParam k)

@[category API, AMS 5]
lemma div_BParam_digit_add_mul_QParam {k z w s : ℕ} (hz : QParam k ∣ z) (hs : s < d0Param k) :
    digit (BParam k) ((z + w) / BParam k) s = digit (BParam k) (w / BParam k) s := by
  obtain ⟨c, rfl⟩ := hz
  have hdiv : (QParam k * c + w) / BParam k = (BParam k) ^ (d0Param k) * c + w / BParam k := by
    rw [show QParam k * c = ((BParam k) ^ (d0Param k) * c) * BParam k by
      dsimp [QParam]; rw [pow_succ]; ring]
    rw [add_comm, Nat.add_mul_div_right _ _ (BParam_pos k), add_comm]
  rw [hdiv, digit_add_mul_pow (BParam_pos k) ⟨c, rfl⟩ hs]

@[category API, AMS 5]
lemma BParam_dvd_QParam (k : ℕ) : BParam k ∣ QParam k :=
  ⟨(BParam k) ^ (d0Param k), by dsimp [QParam]; rw [pow_succ, mul_comm]⟩

@[category API, AMS 5]
lemma linForm_add_mul_QParam {k : ℕ} (cfg : Cfg k) {z w : ℕ} (hz : QParam k ∣ z) :
    linForm k cfg (z + w) = linForm k cfg w := by
  obtain ⟨c, hzc⟩ := dvd_trans (BParam_dvd_QParam k) hz
  have hmod : (z + w) % BParam k = w % BParam k := by
    rw [hzc, mul_comm, add_comm, Nat.add_mul_mod_self_right]
  have hhi : hiForm k cfg ((z + w) / BParam k) = hiForm k cfg (w / BParam k) :=
    Finset.sum_congr rfl fun p _ => by
      rw [div_BParam_digit_add_mul_QParam hz (finProdFinEquiv p).isLt]
  rw [linForm, linForm, hmod, hhi]

-- Gadget sets and partition configuration extraction

noncomputable def Ik (k : ℕ) : Set ℕ := Ico (M_end k) (L0 k)
noncomputable def Jk (k : ℕ) : Set ℕ :=
  {x | ∃ q, 1 ≤ q ∧ q < 80 * (mParam k) ^ 3 ∧ x = q * L0 k}
noncomputable def hub (k : ℕ) (j : Fin (mParam k)) (u : Fin (2 * mParam k)) : ℕ :=
  (j.val + 1) * D0 k + (BParam k) ^ (coordIdx k j u)
noncomputable def Hk (k : ℕ) : Set ℕ := {x | ∃ j u, x = hub k j u}
noncomputable def hubSet (k : ℕ) (cfg : Cfg k) : Set ℕ :=
  {x | ∃ i v, x = hub k (cfg.1 i) (cfg.2 i v)}
noncomputable def Wk (k : ℕ) (r : Fin (RParam k)) : Set ℕ :=
  {w | NScale k r.val ≤ w ∧ w < NScale k (r.val + 1) ∧ w % PParam k < DHalf k ∧
    (∀ s < d0Param k, digit (BParam k) (w / BParam k) s < BParam k - 1) ∧
    linForm k (getCfg k r) w % mParam k = 0}
noncomputable def GadgetK (k : ℕ) : Set ℕ :=
  Ik k ∪ Jk k ∪ Hk k ∪ ⋃ r : Fin (RParam k), Wk k r
noncomputable def CounterexampleA : Set ℕ := Iio 16 ∪ ⋃ k : ℕ, GadgetK k

@[category API, AMS 5]
lemma linForm_hub_add {k : ℕ} (cfg : Cfg k) (j : Fin (mParam k)) (u : Fin (2 * mParam k))
    {w : ℕ} (hw : ∀ s < d0Param k, digit (BParam k) (w / BParam k) s < BParam k - 1) :
    linForm k cfg (hub k j u + w) = linForm k cfg w + coeffPair k cfg (j, u) := by
  set s₀ := (finProdFinEquiv (j, u)).val
  have hB := BParam_pos k
  have hrew : hub k j u + w = (j.val + 1) * D0 k + (w + (BParam k) ^ s₀ * BParam k) := by
    dsimp [hub, coordIdx, s₀]; rw [pow_succ]; ring
  rw [hrew, linForm_add_mul_QParam cfg (dvd_mul_of_dvd_right (QParam_dvd_D0 k) _)]
  have hdig : digit (BParam k) (w / BParam k) s₀ + 1 < BParam k := by
    have := hw s₀ (finProdFinEquiv (j, u)).isLt
    have := mParam_ge_four k; have := mParam_lt_BParam k; omega
  have hsum : hiForm k cfg (w / BParam k + (BParam k) ^ s₀) =
      ∑ p : Fin (mParam k) × Fin (2 * mParam k),
        (coeffPair k cfg p * digit (BParam k) (w / BParam k) (finProdFinEquiv p).val +
          if p = (j, u) then coeffPair k cfg p else 0) :=
    Finset.sum_congr rfl fun p _ => by
      rw [digit_add_pow hB hdig, mul_add]
      by_cases h : p = (j, u)
      · subst h; rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg (mt (Fin.val_inj.trans finProdFinEquiv.injective.eq_iff).mp h),
          if_neg h, mul_zero]
  dsimp only [linForm]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hB, hsum, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j, u), if_pos (Finset.mem_univ _), ← add_assoc]
  rfl

@[category API, AMS 5]
lemma hub_bounds (k : ℕ) (j : Fin (mParam k)) (u : Fin (2 * mParam k)) :
    (BParam k) ^ (coordIdx k j u) < QParam k ∧ D0 k ≤ hub k j u ∧ hub k j u < PParam k := by
  have sc := scale_chain k
  have hB : 1 < BParam k :=
    lt_of_lt_of_le (by have := mParam_ge_four k; omega) (mParam_lt_BParam k).le
  have hpow : (BParam k) ^ (coordIdx k j u) < QParam k :=
    Nat.pow_lt_pow_right hB (Nat.succ_lt_succ (finProdFinEquiv (j, u)).isLt)
  refine ⟨hpow, ?_, ?_⟩ <;> dsimp [hub]
  · have : 1 * D0 k ≤ (j.val + 1) * D0 k := Nat.mul_le_mul_right _ (by omega)
    omega
  · have : (j.val + 1) * D0 k ≤ mParam k * D0 k := Nat.mul_le_mul_right _ j.isLt
    nlinarith

@[category API, AMS 5]
lemma GadgetK_subset_Ico (k : ℕ) : GadgetK k ⊆ Ico (M_end k) (M_end (k + 1)) := by
  intro x hx
  have sc := scale_chain k
  have hN0_le : N0 k ≤ M_end (k + 1) := by
    rw [M_end_succ]; exact le_stepScale k (N0 k) (RParam k)
  rcases hx with ((⟨hx1, hx2⟩ | ⟨q, hq1, hq_lt, rfl⟩) | ⟨j, u, rfl⟩) | hxW
  · exact ⟨hx1, lt_of_lt_of_le (by omega) hN0_le⟩
  · have : 1 * L0 k ≤ q * L0 k := Nat.mul_le_mul_right _ hq1
    have hqN : q * L0 k < N0 k := by
      rw [N0_eq_mul_L0]; exact (mul_lt_mul_iff_left₀ (by have := M_end_ge_16 k; omega)).mpr hq_lt
    exact ⟨by omega, hqN.trans_le hN0_le⟩
  · obtain ⟨_, hb1, hb2⟩ := hub_bounds k j u
    exact ⟨by omega, lt_of_lt_of_le (by omega) hN0_le⟩
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hxW
    have : N0 k ≤ NScale k r.val := le_stepScale k (N0 k) r.val
    have := hr.1; rw [M_end_succ]
    exact ⟨by omega, hr.2.1.trans_le ((NScale_strictMono k).monotone r.isLt)⟩

@[category API, AMS 5]
lemma exists_cfg_of_partition {A₁ A₂ : Set ℕ} (hcov : CounterexampleA = A₁ ∪ A₂) (k : ℕ) :
    (∃ r : Fin (RParam k), hubSet k (getCfg k r) ⊆ A₁) ∨
    (∃ r : Fin (RParam k), hubSet k (getCfg k r) ⊆ A₂) := by
  classical
  have half : ∀ {M n} (_ : M = 2 * n) (P Q : Fin M → Prop) [DecidablePred P] [DecidablePred Q],
      (∀ x, P x ∨ Q x) → n ≤ (Finset.univ.filter P).card ∨ n ≤ (Finset.univ.filter Q).card :=
    fun hM P Q _ _ hPQ => by
      have hsub : (Finset.univ : Finset (Fin _)) ⊆
          Finset.univ.filter P ∪ Finset.univ.filter Q := fun x _ =>
        (hPQ x).elim (fun h => Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
          (fun h => Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      simp only [Finset.card_univ, Fintype.card_fin] at hc; omega
  have extract : ∀ {S : Set ℕ} (J0 : Finset (Fin (mParam k))), qParam k ≤ J0.card →
      ∀ U0 : Fin (mParam k) → Finset (Fin (2 * mParam k)),
      (∀ j ∈ J0, mParam k ≤ (U0 j).card) → (∀ j ∈ J0, ∀ u ∈ U0 j, hub k j u ∈ S) →
      ∃ r : Fin (RParam k), hubSet k (getCfg k r) ⊆ S := by
    intro S J0 hJ0 U0 hU0_c hU0_m
    obtain ⟨J, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq hJ0
    let eJ : Fin (qParam k) ↪ Fin (mParam k) := (J.orderEmbOfFin hJ_card).toEmbedding
    have heJ : ∀ i, eJ i ∈ J0 := fun i => hJ_sub (J.orderEmbOfFin_mem hJ_card i)
    let hU := fun i => Finset.exists_subset_card_eq (hU0_c (eJ i) (heJ i))
    let eU : Fin (qParam k) → Fin (mParam k) ↪ Fin (2 * mParam k) := fun i =>
      ((hU i).choose.orderEmbOfFin (hU i).choose_spec.2).toEmbedding
    obtain ⟨r, hr⟩ := exists_getCfg_eq k (eJ, eU)
    refine ⟨r, hr.symm ▸ fun _ ⟨i, v, h⟩ => h ▸ hU0_m (eJ i) (heJ i) (eU i v)
      ((hU i).choose_spec.1 ((hU i).choose.orderEmbOfFin_mem (hU i).choose_spec.2 v))⟩
  let U₁ : Fin (mParam k) → Finset (Fin (2 * mParam k)) := fun j =>
    Finset.univ.filter fun u => hub k j u ∈ A₁
  let U₂ : Fin (mParam k) → Finset (Fin (2 * mParam k)) := fun j =>
    Finset.univ.filter fun u => hub k j u ∈ A₂
  have hblock : ∀ j, mParam k ≤ (U₁ j).card ∨ mParam k ≤ (U₂ j).card := fun j =>
    half rfl _ _ fun u => by
      have hA : hub k j u ∈ CounterexampleA :=
        Or.inr (Set.mem_iUnion.mpr ⟨k, Or.inl (Or.inr ⟨j, u, rfl⟩)⟩)
      rwa [hcov] at hA
  rcases half (rfl : mParam k = 2 * qParam k) _ _ hblock with h1 | h2
  · exact Or.inl (extract _ h1 U₁ (fun _ hj => (Finset.mem_filter.mp hj).2)
      (fun _ _ _ hu => (Finset.mem_filter.mp hu).2))
  · exact Or.inr (extract _ h2 U₂ (fun _ hj => (Finset.mem_filter.mp hj).2)
      (fun _ _ _ hu => (Finset.mem_filter.mp hu).2))

-- Positive lower density of `CounterexampleA + CounterexampleA`

@[category API, AMS 5]
lemma card_le_ncard_inter_Iio {S : Set ℕ} {n : ℕ} {F : Finset ℕ}
    (hF : ∀ z ∈ F, z ∈ S ∧ z < n) : F.card ≤ (S ∩ Iio n).ncard := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun z hz => hF z hz) ((Set.finite_Iio n).inter_of_right S)

noncomputable def mkW (k : ℕ) (cfg : Cfg k) (p : ℕ × ℕ) : ℕ :=
  p.1 * BParam k + (p.2 * mParam k + (mParam k - hiForm k cfg p.1 % mParam k) % mParam k)

@[category API, AMS 5]
lemma mkW_props {k : ℕ} (cfg : Cfg k) {p : ℕ × ℕ} (hu : p.2 < 8 * (mParam k) ^ 2) :
    mkW k cfg p / BParam k = p.1 ∧
    linForm k cfg (mkW k cfg p) % mParam k = 0 ∧
    (p.1 < (BParam k) ^ (d0Param k) → mkW k cfg p < QParam k) := by
  have hm : 0 < mParam k := by have := mParam_ge_four k; omega
  set r0 := (mParam k - hiForm k cfg p.1 % mParam k) % mParam k
  have hr0 : r0 < mParam k := Nat.mod_lt _ hm
  set lo := p.2 * mParam k + r0
  have hlo : lo < BParam k := by
    have hmul := Nat.mul_le_mul_right (mParam k) hu
    rw [Nat.succ_mul] at hmul
    have hBeq : 8 * (mParam k) ^ 2 * mParam k = BParam k := by dsimp [BParam]; ring
    dsimp [lo]; omega
  have hdiv : mkW k cfg p / BParam k = p.1 := (mul_add_div_mod p.1 hlo).1
  have hmod : mkW k cfg p % BParam k = lo := (mul_add_div_mod p.1 hlo).2
  refine ⟨hdiv, ?_, fun hq => ?_⟩
  · rw [linForm, hdiv, hmod, add_mod_eq_zero_iff hm]
    dsimp [lo]; rw [(mul_add_div_mod p.2 hr0).2]
  · have hmul := Nat.mul_le_mul_right (BParam k) hq
    rw [Nat.succ_mul] at hmul
    have hQeq : (BParam k) ^ (d0Param k) * BParam k = QParam k := by dsimp [QParam]; rw [pow_succ]
    change p.1 * BParam k + lo < QParam k; omega

noncomputable def baseWFinset (k : ℕ) (cfg : Cfg k) : Finset ℕ :=
  (boundedDigits (BParam k) (BParam k - 1) (d0Param k) ×ˢ
    Finset.range (8 * (mParam k) ^ 2)).image (mkW k cfg)

@[category API, AMS 5]
lemma mem_baseWFinset {k : ℕ} {cfg : Cfg k} {x : ℕ} (hx : x ∈ baseWFinset k cfg) :
    x < QParam k ∧
    (∀ s < d0Param k, digit (BParam k) (x / BParam k) s < BParam k - 1) ∧
    linForm k cfg x % mParam k = 0 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_product, Finset.mem_range] at hp
  obtain ⟨hq_lt, hq_dig⟩ := boundedDigits_spec (Nat.sub_le _ _) hp.1
  obtain ⟨hdiv, hlin, hltQ⟩ := mkW_props cfg hp.2
  exact ⟨hltQ hq_lt, fun s hs => hdiv ▸ hq_dig s hs, hlin⟩

@[category API, AMS 5]
lemma baseWFinset_card_bound (k : ℕ) (cfg : Cfg k) :
    3 * QParam k ≤ 4 * mParam k * (baseWFinset k cfg).card := by
  have hm4 := mParam_ge_four k
  have hB1 : 1 ≤ BParam k := BParam_pos k
  have hinj : Set.InjOn (mkW k cfg)
      (boundedDigits (BParam k) (BParam k - 1) (d0Param k) ×ˢ
        Finset.range (8 * (mParam k) ^ 2) : Finset (ℕ × ℕ)) := by
    intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
    have h1 : p₁.1 = p₂.1 := by rw [← (mkW_props cfg hp₁.2).1, heq, (mkW_props cfg hp₂.2).1]
    have h2 : p₁.2 * mParam k = p₂.2 * mParam k := by dsimp [mkW] at heq; rw [h1] at heq; omega
    exact Prod.ext h1 (Nat.eq_of_mul_eq_mul_right (by omega) h2)
  have hcard : (baseWFinset k cfg).card =
      (BParam k - 1) ^ (d0Param k) * (8 * (mParam k) ^ 2) := by
    rw [baseWFinset, Finset.card_image_of_injOn hinj, Finset.card_product,
      boundedDigits_card (Nat.sub_le _ _), Finset.card_range]
  have hd_pos : 1 ≤ d0Param k := by nlinarith
  have hbern := pow_le_pred_pow_add hB1 (d0Param k)
  have hterm : 4 * (d0Param k * (BParam k) ^ (d0Param k - 1)) ≤ (BParam k) ^ (d0Param k) := by
    calc
      4 * (d0Param k * (BParam k) ^ (d0Param k - 1))
        = (8 * (mParam k) ^ 2) * (BParam k) ^ (d0Param k - 1) := by dsimp [d0Param]; ring
      _ ≤ BParam k * (BParam k) ^ (d0Param k - 1) :=
          Nat.mul_le_mul_right _ (by dsimp [BParam]; nlinarith)
      _ = (BParam k) ^ (d0Param k) := by conv_rhs => rw [← Nat.sub_add_cancel hd_pos, pow_succ']
  calc
    3 * QParam k = (3 * (BParam k) ^ (d0Param k)) * BParam k := by
        dsimp [QParam]; rw [pow_succ]; ring
    _ ≤ (4 * (BParam k - 1) ^ (d0Param k)) * BParam k :=
        Nat.mul_le_mul_right _ (by linarith)
    _ = 4 * mParam k * (baseWFinset k cfg).card := by rw [hcard]; dsimp [BParam]; ring

@[category API, AMS 5]
lemma sumset_scale_bound (k : ℕ) (r : Fin (RParam k)) {n : ℕ}
    (hn_lo : 4 * NScale k r.val ≤ n) (hn_hi : n ≤ NScale k (r.val + 1)) :
    3 * n ≤ 64 * ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard := by
  set cfg := getCfg k r
  have sc := scale_chain k
  have hM := M_end_ge_16 k
  have hP_pos : 0 < PParam k := by omega
  set p_start := NScale k r.val / PParam k
  have hp_mul : p_start * PParam k = NScale k r.val :=
    Nat.div_mul_cancel (PParam_dvd_NScale k r.val)
  have hp_ge : 40 ≤ p_start := (Nat.le_div_iff_mul_le hP_pos).mpr
    (sc.2.2.2.2.2.2.trans (le_stepScale k (N0 k) r.val))
  set Q_n := n / PParam k
  have hQn_ge : 4 * p_start ≤ Q_n := (Nat.le_div_iff_mul_le hP_pos).mpr (by nlinarith)
  set numP := Q_n - p_start - 1
  set numB := 8 * mParam k * M_end k
  have hDHalf : DHalf k = numB * QParam k := by dsimp [DHalf, L0, numB]; ring
  set Dom := (Finset.univ : Finset (Fin (qParam k) × Fin (mParam k))) ×ˢ
    (Finset.range numP ×ˢ (Finset.range numB ×ˢ baseWFinset k cfg))
  let wFn (t b x : ℕ) : ℕ := (p_start + t) * PParam k + (b * QParam k + x)
  let sumFn : (Fin (qParam k) × Fin (mParam k)) × (ℕ × (ℕ × ℕ)) → ℕ :=
    fun z => hub k (cfg.1 z.1.1) (cfg.2 z.1.1 z.1.2) + wFn z.2.1 z.2.2.1 z.2.2.2
  set F := Dom.image sumFn
  have hy_lt : ∀ b < numB, ∀ x < QParam k, b * QParam k + x < DHalf k := fun b hb x hx => by
    rw [hDHalf]; have := Nat.mul_le_mul_right (QParam k) hb; nlinarith
  have hw_inv : ∀ t b {x}, x ∈ baseWFinset k cfg →
      (∀ s < d0Param k, digit (BParam k) (wFn t b x / BParam k) s < BParam k - 1) ∧
      linForm k cfg (wFn t b x) % mParam k = 0 := fun t b {x} hx => by
    obtain ⟨_, hx_dig, hx_lin⟩ := mem_baseWFinset hx
    have hdvdQ : QParam k ∣ (p_start + t) * PParam k + b * QParam k :=
      dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (QParam_dvd_D0 k) _) _)
        ⟨b, mul_comm _ _⟩
    have hassoc : wFn t b x = ((p_start + t) * PParam k + b * QParam k) + x :=
      (add_assoc _ _ _).symm
    exact ⟨fun s hs => by rw [hassoc, div_BParam_digit_add_mul_QParam hdvdQ hs]; exact hx_dig s hs,
      by rw [hassoc, linForm_add_mul_QParam cfg hdvdQ]; exact hx_lin⟩
  have hF_mem : ∀ z ∈ F, z ∈ CounterexampleA + CounterexampleA ∧ z < n := by
    intro z hz
    obtain ⟨⟨⟨i, v⟩, ⟨t, ⟨b, x⟩⟩⟩, hdom, rfl⟩ := Finset.mem_image.mp hz
    simp only [Dom, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and] at hdom
    rcases hdom with ⟨ht, hb, hx_mem⟩
    have hp1_ge : NScale k r.val ≤ (p_start + t) * PParam k :=
      hp_mul ▸ Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    have hp2_le : (p_start + t) * PParam k + 2 * PParam k ≤ n := by
      simpa [Nat.add_mul, add_assoc] using
        (Nat.mul_le_mul_right (PParam k) (by omega : p_start + (t + 2) ≤ Q_n)).trans
          (Nat.div_mul_le_self n (PParam k))
    have hy_half := hy_lt b hb x (mem_baseWFinset hx_mem).1
    have hw : wFn t b x ∈ Wk k r := by
      refine ⟨by dsimp [wFn]; omega, by dsimp [wFn]; omega, ?_,
        (hw_inv t b hx_mem).1, (hw_inv t b hx_mem).2⟩
      dsimp [wFn]; rw [(mul_add_div_mod _ (by omega : b * QParam k + x < PParam k)).2]; exact hy_half
    have hhub_lt := (hub_bounds k (cfg.1 i) (cfg.2 i v)).2.2
    dsimp only [sumFn, wFn]
    exact ⟨Set.add_mem_add (Or.inr (Set.mem_iUnion.mpr ⟨k, Or.inl (Or.inr ⟨_, _, rfl⟩)⟩))
      (Or.inr (Set.mem_iUnion.mpr ⟨k, Or.inr (Set.mem_iUnion.mpr ⟨r, hw⟩)⟩)), by omega⟩
  have hinj : Set.InjOn sumFn Dom := by
    rintro ⟨⟨i₁, v₁⟩, ⟨t₁, ⟨b₁, x₁⟩⟩⟩ h₁ ⟨⟨i₂, v₂⟩, ⟨t₂, ⟨b₂, x₂⟩⟩⟩ h₂ heq
    rw [Finset.mem_coe] at h₁ h₂
    simp only [Dom, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and] at h₁ h₂
    dsimp only [sumFn] at heq
    have hdecomp : ∀ (i : Fin (qParam k)) (v : Fin (mParam k)) (t y : ℕ), y < DHalf k →
        (hub k (cfg.1 i) (cfg.2 i v) + ((p_start + t) * PParam k + y)) / PParam k = p_start + t ∧
        ((hub k (cfg.1 i) (cfg.2 i v) + ((p_start + t) * PParam k + y)) % PParam k) / D0 k =
          (cfg.1 i).val + 1 := by
      intro i v t y hy
      set rem := (BParam k) ^ (coordIdx k (cfg.1 i) (cfg.2 i v)) + y
      have hrem : rem < D0 k := by have := (hub_bounds k (cfg.1 i) (cfg.2 i v)).1; omega
      have hinner : ((cfg.1 i).val + 1) * D0 k + rem < PParam k := by
        have := Nat.mul_le_mul_right (D0 k) (by omega : (cfg.1 i).val + 2 ≤ mParam k + 1)
        nlinarith
      have hrew : hub k (cfg.1 i) (cfg.2 i v) + ((p_start + t) * PParam k + y) =
          (p_start + t) * PParam k + (((cfg.1 i).val + 1) * D0 k + rem) := by
        dsimp [hub, rem]; ring
      rw [hrew, (mul_add_div_mod _ hinner).1, (mul_add_div_mod _ hinner).2,
        (mul_add_div_mod _ hrem).1]
      exact ⟨rfl, rfl⟩
    obtain ⟨hd₁, hm₁⟩ := hdecomp i₁ v₁ t₁ _ (hy_lt b₁ h₁.2.1 x₁ (mem_baseWFinset h₁.2.2).1)
    obtain ⟨hd₂, hm₂⟩ := hdecomp i₂ v₂ t₂ _ (hy_lt b₂ h₂.2.1 x₂ (mem_baseWFinset h₂.2.2).1)
    have ht_eq : t₁ = t₂ := by
      have : p_start + t₁ = p_start + t₂ := by rw [← hd₁, heq, hd₂]
      omega
    have hi_eq : i₁ = i₂ := cfg.1.injective (Fin.ext (by
      have : (cfg.1 i₁).val + 1 = (cfg.1 i₂).val + 1 := by rw [← hm₁, heq, hm₂]
      omega))
    subst ht_eq; subst hi_eq
    have hlin : ∀ (v : Fin (mParam k)) (b : ℕ) {x : ℕ}, x ∈ baseWFinset k cfg →
        linForm k cfg (hub k (cfg.1 i₁) (cfg.2 i₁ v) + wFn t₁ b x) % mParam k = v.val :=
      fun v b {x} hx => by
        rw [linForm_hub_add cfg _ _ (hw_inv t₁ b hx).1, coeffPair_apply,
          Nat.add_mod, (hw_inv t₁ b hx).2, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt v.isLt]
    have hv_eq : v₁ = v₂ := Fin.ext (by rw [← hlin v₁ b₁ h₁.2.2, heq, hlin v₂ b₂ h₂.2.2])
    subst hv_eq
    have hy_eq : b₁ * QParam k + x₁ = b₂ * QParam k + x₂ := by dsimp [wFn] at heq; omega
    have hb_eq : b₁ = b₂ := by
      rw [← (mul_add_div_mod b₁ (mem_baseWFinset h₁.2.2).1).1, hy_eq,
        (mul_add_div_mod b₂ (mem_baseWFinset h₂.2.2).1).1]
    subst hb_eq
    have hx_eq : x₁ = x₂ := by omega
    rw [hx_eq]
  have hF_card : F.card =
      (qParam k * mParam k) * (numP * (numB * (baseWFinset k cfg).card)) := by
    rw [Finset.card_image_of_injOn hinj]; simp [Dom]
  have hn_lt : n < (Q_n + 1) * PParam k := by
    have := Nat.mod_lt n hP_pos; have := Nat.div_add_mod n (PParam k); dsimp [Q_n]; nlinarith
  calc
    3 * n ≤ 3 * ((Q_n + 1) * PParam k) := Nat.mul_le_mul_left 3 hn_lt.le
    _ ≤ 3 * ((2 * numP) * PParam k) :=
        Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right _ (by omega : Q_n + 1 ≤ 2 * numP))
    _ = 64 * (mParam k) ^ 2 * numP * M_end k * (3 * QParam k) := by
        dsimp [PParam, D0, DHalf, L0]; ring
    _ ≤ 64 * (mParam k) ^ 2 * numP * M_end k * (4 * mParam k * (baseWFinset k cfg).card) :=
        Nat.mul_le_mul_left _ (baseWFinset_card_bound k cfg)
    _ = 64 * F.card := by rw [hF_card]; dsimp [mParam, numB]; ring
    _ ≤ 64 * ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard :=
        Nat.mul_le_mul_left 64 (card_le_ncard_inter_Iio hF_mem)

@[category API, AMS 5]
lemma sumset_bridge_J_I_bound (k : ℕ) {n : ℕ}
    (hn_lo : 2 * L0 k ≤ n) (hn_hi : n ≤ N0 k) :
    3 * n ≤ 64 * ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard := by
  have sc := scale_chain k
  have hL_pos : 0 < L0 k := by have := M_end_ge_16 k; omega
  set Q_L := n / L0 k
  have hQL_ge : 2 ≤ Q_L := (Nat.le_div_iff_mul_le hL_pos).mpr hn_lo
  have hN0 := N0_eq_mul_L0 k
  have hQL_le : Q_L ≤ 80 * (mParam k) ^ 3 := Nat.div_le_of_le_mul (by linarith)
  set Dom := Finset.Ico 1 Q_L ×ˢ Finset.Ico (M_end k) (L0 k)
  let sumFn : ℕ × ℕ → ℕ := fun p => p.1 * L0 k + p.2
  set F := Dom.image sumFn
  have hF_mem : ∀ z ∈ F, z ∈ CounterexampleA + CounterexampleA ∧ z < n := by
    intro z hz
    obtain ⟨⟨q, x⟩, hdom, rfl⟩ := Finset.mem_image.mp hz
    simp only [Dom, Finset.mem_product, Finset.mem_Ico] at hdom
    have hJ : q * L0 k ∈ CounterexampleA :=
      Or.inr (Set.mem_iUnion.mpr ⟨k, Or.inl (Or.inl (Or.inr ⟨q, hdom.1.1, by omega, rfl⟩))⟩)
    have hI : x ∈ CounterexampleA :=
      Or.inr (Set.mem_iUnion.mpr ⟨k, Or.inl (Or.inl (Or.inl hdom.2))⟩)
    have h1 : q * L0 k + L0 k ≤ Q_L * L0 k := by
      simpa [add_one_mul] using Nat.mul_le_mul_right (L0 k) hdom.1.2
    have h2 : Q_L * L0 k ≤ n := Nat.div_mul_le_self n (L0 k)
    dsimp only [sumFn]; exact ⟨Set.add_mem_add hJ hI, by omega⟩
  have hinj : Set.InjOn sumFn Dom := by
    intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico] at hp₁ hp₂
    dsimp only [sumFn] at heq
    have h1 : p₁.1 = p₂.1 := by
      rw [← (mul_add_div_mod p₁.1 hp₁.2.2).1, heq, (mul_add_div_mod p₂.1 hp₂.2.2).1]
    exact Prod.ext h1 (by rw [h1] at heq; omega)
  have hF_card : F.card = (Q_L - 1) * (L0 k - M_end k) := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Nat.card_Ico, Nat.card_Ico]
  have hn_lt : n < (Q_L + 1) * L0 k := by
    have := Nat.mod_lt n hL_pos; have := Nat.div_add_mod n (L0 k); dsimp [Q_L]; nlinarith
  calc
    3 * n ≤ (Q_L + 1) * (3 * L0 k) := by nlinarith
    _ ≤ (3 * (Q_L - 1)) * (4 * (L0 k - M_end k)) := Nat.mul_le_mul (by omega) (by omega)
    _ = 12 * F.card := by rw [hF_card]; ring
    _ ≤ 64 * ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard :=
        (Nat.mul_le_mul_right _ (by decide : 12 ≤ 64)).trans
          (Nat.mul_le_mul_left 64 (card_le_ncard_inter_Iio hF_mem))

@[category API, AMS 5]
lemma exists_step_interval {f : ℕ → ℕ} {n : ℕ} :
    ∀ K, f 0 ≤ n → n < f K → ∃ i < K, f i ≤ n ∧ n < f (i + 1)
  | 0, h0, hK => absurd (h0.trans_lt hK) (lt_irrefl _)
  | K + 1, h0, hK =>
    if h : f K ≤ n then ⟨K, Nat.lt_succ_self K, h, hK⟩
    else let ⟨i, hi, h1, h2⟩ := exists_step_interval K h0 (lt_of_not_ge h)
      ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩

@[category API, AMS 5]
lemma lowerDensity_CounterexampleA_add_pos :
    0 < lowerDensity (CounterexampleA + CounterexampleA) := by
  have hmono : ∀ {a b}, a ≤ b →
      ((CounterexampleA + CounterexampleA) ∩ Iio a).ncard ≤
        ((CounterexampleA + CounterexampleA) ∩ Iio b).ncard := fun hab =>
    Set.ncard_le_ncard (fun _ ⟨hS, hlt⟩ => ⟨hS, hlt.trans_le hab⟩)
      ((Set.finite_Iio _).inter_of_right _)
  have hzero : 0 ∈ CounterexampleA := Or.inl (by decide : 0 < 16)
  refine lowerDensity_pos_of_forall_ge (c := 3 / 256) (by positivity) (n₀ := 16) fun n hn => ?_
  suffices hnat : 3 * n ≤ 256 * ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard by
    have : (3 * n : ℝ) ≤ (256 * ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard : ℝ) := by
      exact_mod_cast hnat
    linarith
  obtain ⟨k, _, hk_lo, hk_hi⟩ := exists_step_interval (n + 1) hn
    ((Nat.lt_succ_self n).trans_le (M_end_strictMono.id_le (n + 1)))
  have sc := scale_chain k
  rcases lt_or_ge n (4 * M_end k) with h1 | h1
  · rcases k with _ | k'
    · change n < 4 * 16 at h1
      have h1_le : ({0} : Finset ℕ).card ≤ ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard :=
        card_le_ncard_inter_Iio fun z hz => by
          rw [Finset.mem_singleton] at hz; subst hz
          exact ⟨by simpa using Set.add_mem_add hzero hzero, by omega⟩
      simp only [Finset.card_singleton] at h1_le; omega
    · let r_last : Fin (RParam k') := ⟨RParam k' - 1, Nat.sub_lt (RParam_pos k') Nat.one_pos⟩
      have hM_eq : M_end (k' + 1) = NScale k' (r_last.val + 1) := by
        rw [M_end_succ]; simp [r_last, Nat.sub_add_cancel (RParam_pos k')]
      have h4 : 4 * NScale k' r_last.val ≤ M_end (k' + 1) := by
        rw [hM_eq, NScale_succ]; nlinarith [mParam_ge_four k']
      have := sumset_scale_bound k' r_last h4 hM_eq.le
      have := hmono hk_lo; omega
  · rcases le_or_gt n (2 * L0 k) with h2 | h2
    · set F := Finset.Ico (M_end k) (min n (L0 k))
      have hF : F.card ≤ ((CounterexampleA + CounterexampleA) ∩ Iio n).ncard :=
        card_le_ncard_inter_Iio fun z hz => by
          rw [Finset.mem_Ico] at hz
          have hzI : z ∈ CounterexampleA := Or.inr (Set.mem_iUnion.mpr
            ⟨k, Or.inl (Or.inl (Or.inl ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩))⟩)
          exact ⟨by simpa using Set.add_mem_add hzero hzI, hz.2.trans_le (min_le_left _ _)⟩
      have hcard : F.card = min n (L0 k) - M_end k := Nat.card_Ico _ _
      rcases le_total n (L0 k) with hle | hge <;> [rw [min_eq_left hle] at hcard;
        rw [min_eq_right hge] at hcard] <;> omega
    · rcases le_or_gt n (N0 k) with h3 | h3
      · have := sumset_bridge_J_I_bound k h2.le h3; omega
      · rw [M_end_succ] at hk_hi
        obtain ⟨r_val, hr_lt, hr_lo, hr_hi⟩ := exists_step_interval (f := NScale k) (RParam k)
          h3.le hk_hi
        rcases lt_or_ge n (4 * NScale k r_val) with h4 | h4
        · have h64_left : 3 * NScale k r_val ≤
              64 * ((CounterexampleA + CounterexampleA) ∩ Iio (NScale k r_val)).ncard := by
            rcases r_val with _ | r_prev
            · exact sumset_bridge_J_I_bound k (by omega) le_rfl
            · exact sumset_scale_bound k ⟨r_prev, by omega⟩
                (by rw [NScale_succ]; nlinarith [mParam_ge_four k]) le_rfl
          have := hmono hr_lo; omega
        · have := sumset_scale_bound k ⟨r_val, hr_lt⟩ h4 hr_hi.le; omega

-- Upper bound on `(A_target + A_target) ∩ Iio N` and disproof of `erdos_741.variants.lower`

@[category API, AMS 5]
lemma mem_target_lt_NScale_cases {A_t A_o : Set ℕ}
    (hsub : A_t ⊆ CounterexampleA) (hdisj : Disjoint A_t A_o)
    (k : ℕ) (r : Fin (RParam k)) (hhub : hubSet k (getCfg k r) ⊆ A_o)
    {x : ℕ} (hx_mem : x ∈ A_t) (hx_lt : x < NScale k (r.val + 1)) :
    (x < NScale k r.val ∧
      (x % PParam k < DHalf k ∨ x ∈ Jk k ∨ x ∈ Hk k \ hubSet k (getCfg k r))) ∨
    x ∈ Wk k r := by
  have sc := scale_chain k
  have hM := M_end_ge_16 k
  have hN0_le : N0 k ≤ NScale k r.val := le_stepScale k (N0 k) r.val
  have h_small : x < L0 k → x < NScale k r.val ∧
      (x % PParam k < DHalf k ∨ x ∈ Jk k ∨ x ∈ Hk k \ hubSet k (getCfg k r)) := fun hlt =>
    ⟨by omega, Or.inl (by rw [Nat.mod_eq_of_lt (by omega : x < PParam k)]; omega)⟩
  rcases hsub hx_mem with hx16 | hxU
  · exact Or.inl (h_small (by rw [Set.mem_Iio] at hx16; omega))
  · obtain ⟨k', hxk'⟩ := Set.mem_iUnion.mp hxU
    rcases lt_trichotomy k k' with hk_gt | rfl | hk_lt
    · have hb := (GadgetK_subset_Ico k' hxk').1
      have h1 : NScale k (r.val + 1) ≤ M_end (k + 1) := by
        rw [M_end_succ]; exact (NScale_strictMono k).monotone r.isLt
      have h2 : M_end (k + 1) ≤ M_end k' := M_end_strictMono.monotone hk_gt
      omega
    · rcases hxk' with ((hxI | ⟨q, hq1, hq_lt, rfl⟩) | ⟨j, u, rfl⟩) | hxW
      · exact Or.inl (h_small hxI.2)
      · have hxN0 : q * L0 k < N0 k := by
          rw [N0_eq_mul_L0]; exact (mul_lt_mul_iff_left₀ (by omega : 0 < L0 k)).mpr hq_lt
        exact Or.inl ⟨hxN0.trans_le hN0_le, Or.inr (Or.inl ⟨q, hq1, hq_lt, rfl⟩)⟩
      · have hP := (hub_bounds k j u).2.2
        exact Or.inl ⟨by omega,
          Or.inr (Or.inr ⟨⟨j, u, rfl⟩, fun h => Set.disjoint_left.mp hdisj hx_mem (hhub h)⟩)⟩
      · obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hxW
        rcases lt_trichotomy u.val r.val with hu_lt | hu_eq | hu_gt
        · exact Or.inl ⟨hu.2.1.trans_le ((NScale_strictMono k).monotone hu_lt), Or.inl hu.2.2.1⟩
        · exact Fin.ext hu_eq ▸ Or.inr hu
        · exact absurd (hu.1.trans_lt hx_lt)
            (not_lt_of_ge ((NScale_strictMono k).monotone hu_gt))
    · have hb := (GadgetK_subset_Ico k' hxk').2.trans_le (M_end_strictMono.monotone hk_lt)
      exact Or.inl (h_small (by omega))

@[category API, AMS 5]
lemma target_sumset_ncard_bound {A_t A_o : Set ℕ}
    (hsub : A_t ⊆ CounterexampleA) (hdisj : Disjoint A_t A_o)
    (k : ℕ) (r : Fin (RParam k)) (hhub : hubSet k (getCfg k r) ⊆ A_o) :
    mParam k * ((A_t + A_t) ∩ Iio (NScale k (r.val + 1))).ncard ≤
      2 * NScale k (r.val + 1) := by
  set cfg := getCfg k r
  set N := NScale k (r.val + 1)
  have hm4 := mParam_ge_four k
  have hBN : BParam k ∣ N := dvd_trans (BParam_dvd_QParam k)
    (dvd_trans (dvd_mul_of_dvd_right (QParam_dvd_D0 k) _) (PParam_dvd_NScale k (r.val + 1)))
  have hmid_lin : ∀ {x y}, (x ∈ Jk k ∨ x ∈ Hk k \ hubSet k cfg) → y ∈ Wk k r →
      linForm k cfg (x + y) % mParam k = 0 := by
    rintro x y (⟨q, _, _, rfl⟩ | ⟨⟨j, u, rfl⟩, hnot_hub⟩) hy
    · rw [linForm_add_mul_QParam cfg ⟨q * (4 * M_end k), by dsimp [L0]; ring⟩]
      exact hy.2.2.2.2
    · classical
      have hnot : ¬ ∃ iv : Fin (qParam k) × Fin (mParam k),
          cfg.1 iv.1 = j ∧ cfg.2 iv.1 iv.2 = u := fun ⟨⟨i, v⟩, hi, hv⟩ =>
        hnot_hub ⟨i, v, by rw [hi, hv]⟩
      rw [linForm_hub_add cfg j u hy.2.2.2.1, coeffPair, dif_neg hnot, add_zero]
      exact hy.2.2.2.2
  have hmod_sum : ∀ {x y}, x % PParam k < DHalf k → y % PParam k < DHalf k →
      (x + y) % PParam k < D0 k := fun hx hy => by
    rw [Nat.add_mod]; exact (Nat.mod_le _ _).trans_lt (by dsimp [D0]; omega)
  let E₁ := Finset.range (2 * NScale k r.val)
  let E₂ := (Finset.range (N / PParam k) ×ˢ Finset.range (D0 k)).image
    fun p => p.1 * PParam k + p.2
  let E₃ := (Finset.range (N / BParam k) ×ˢ Finset.range (8 * (mParam k) ^ 2)).image (mkW k cfg)
  have hcov_sum : (A_t + A_t) ∩ Iio N ⊆ ((E₁ ∪ E₂ ∪ E₃ : Finset ℕ) : Set ℕ) := by
    rintro z ⟨hz_sum, hz_lt⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz_sum
    rw [Set.mem_Iio] at hz_lt
    have hcx := mem_target_lt_NScale_cases hsub hdisj k r hhub hx (by omega)
    have hcy := mem_target_lt_NScale_cases hsub hdisj k r hhub hy (by omega)
    have m1 : x + y < 2 * NScale k r.val → x + y ∈ E₁ ∪ E₂ ∪ E₃ := fun h =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr h))
    have m2 : (x + y) % PParam k < D0 k → x + y ∈ E₁ ∪ E₂ ∪ E₃ := fun h => by
      refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨((x + y) / PParam k, (x + y) % PParam k), ?_, ?_⟩))
      · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        have hmul : PParam k * (N / PParam k) = N :=
          Nat.mul_div_cancel' (PParam_dvd_NScale k (r.val + 1))
        exact ⟨Nat.div_lt_of_lt_mul (by linarith), h⟩
      · linarith [Nat.div_add_mod (x + y) (PParam k)]
    have m3 : linForm k cfg (x + y) % mParam k = 0 → x + y ∈ E₁ ∪ E₂ ∪ E₃ := fun h => by
      set q := (x + y) / BParam k
      set lo := (x + y) % BParam k
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(q, lo / mParam k), ?_, ?_⟩)
      · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        have hmulB : BParam k * (N / BParam k) = N := Nat.mul_div_cancel' hBN
        have hloB : lo < mParam k * (8 * (mParam k) ^ 2) := by
          have := Nat.mod_lt (x + y) (BParam_pos k)
          have hBeq : BParam k = mParam k * (8 * (mParam k) ^ 2) := by dsimp [BParam]; ring
          omega
        exact ⟨Nat.div_lt_of_lt_mul (by linarith), Nat.div_lt_of_lt_mul hloB⟩
      · have hmod0 : lo % mParam k = (mParam k - hiForm k cfg q % mParam k) % mParam k :=
          (add_mod_eq_zero_iff (by omega)).mp h
        dsimp [mkW]
        rw [← hmod0, mul_comm (lo / mParam k), Nat.div_add_mod lo (mParam k),
          mul_comm q, Nat.div_add_mod (x + y) (BParam k)]
    rcases hcx with ⟨_, hxc⟩ | hxW <;> rcases hcy with ⟨_, hyc⟩ | hyW
    · exact m1 (by omega)
    · exact hxc.elim (fun hxm => m2 (hmod_sum hxm hyW.2.2.1)) (fun hxmid => m3 (hmid_lin hxmid hyW))
    · exact hyc.elim (fun hym => m2 (hmod_sum hxW.2.2.1 hym))
        (fun hymid => m3 (add_comm x y ▸ hmid_lin hymid hxW))
    · exact m2 (hmod_sum hxW.2.2.1 hyW.2.2.1)
  have hncard : ((A_t + A_t) ∩ Iio N).ncard ≤ E₁.card + E₂.card + E₃.card :=
    ((Set.ncard_le_ncard hcov_sum (E₁ ∪ E₂ ∪ E₃).finite_toSet).trans_eq
      (Set.ncard_coe_finset _)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hE1 : 2 * mParam k * E₁.card = N := by dsimp [N]; rw [Finset.card_range, NScale_succ]; ring
  have hE2 : 2 * mParam k * E₂.card ≤ N := by
    have hle : E₂.card ≤ (N / PParam k) * D0 k := Finset.card_image_le.trans_eq (by simp)
    refine (Nat.mul_le_mul_left _ hle).trans ?_
    rw [show 2 * mParam k * ((N / PParam k) * D0 k) = (N / PParam k) * PParam k by
      dsimp [PParam]; ring]
    exact Nat.div_mul_le_self _ _
  have hE3 : mParam k * E₃.card ≤ N := by
    have hle : E₃.card ≤ (N / BParam k) * (8 * (mParam k) ^ 2) :=
      Finset.card_image_le.trans_eq (by simp)
    refine (Nat.mul_le_mul_left _ hle).trans ?_
    rw [show mParam k * ((N / BParam k) * (8 * (mParam k) ^ 2)) = (N / BParam k) * BParam k by
      dsimp [BParam]; ring]
    exact Nat.div_mul_le_self _ _
  have h2m : 2 * (mParam k * ((A_t + A_t) ∩ Iio N).ncard) ≤ 4 * N := calc
    2 * (mParam k * ((A_t + A_t) ∩ Iio N).ncard)
      ≤ 2 * mParam k * (E₁.card + E₂.card + E₃.card) := by
        rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hncard
    _ = 2 * mParam k * E₁.card + 2 * mParam k * E₂.card + 2 * (mParam k * E₃.card) := by ring
    _ ≤ 4 * N := by omega
  omega

/--
Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive lower density.
Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$
both have positive lower density?
-/
@[category research solved, question, AMS 5]
theorem erdos_741.variants.lower :
    ¬ ∀ A : Set ℕ, 0 < lowerDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ 0 < lowerDensity (A₁ + A₁)
    ∧ 0 < lowerDensity (A₂ + A₂) := by
  intro hall
  obtain ⟨A₁, A₂, hcov, hdisj, hlow₁, hlow₂⟩ :=
    hall CounterexampleA lowerDensity_CounterexampleA_add_pos
  obtain ⟨K₁, N₁, hN₁⟩ := exists_eventually_ge_of_lowerDensity_pos hlow₁
  obtain ⟨K₂, N₂, hN₂⟩ := exists_eventually_ge_of_lowerDensity_pos hlow₂
  let k := max (max N₁ N₂) (max K₁ K₂)
  have sc := scale_chain k
  have hM := M_end_ge_16 k
  have hcontra : ∀ {A_t A_o : Set ℕ} {K_t N_t : ℕ},
      A_t ⊆ CounterexampleA → Disjoint A_t A_o → K_t ≤ max K₁ K₂ → N_t ≤ max N₁ N₂ →
      (∀ n ≥ N_t, n ≤ K_t * ((A_t + A_t) ∩ Iio n).ncard) →
      ∀ r : Fin (RParam k), hubSet k (getCfg k r) ⊆ A_o → False := by
    intro A_t A_o K_t N_t hsub_t hdisj_t hKt_le hNt_le hNt_spec r hhub
    set N := NScale k (r.val + 1)
    set c := ((A_t + A_t) ∩ Iio N).ncard
    have hN0_le : N0 k ≤ N := le_stepScale k (N0 k) (r.val + 1)
    have h1 : N_t ≤ k := hNt_le.trans (le_max_left _ _)
    have h2 : K_t ≤ k := hKt_le.trans (le_max_right _ _)
    have h3 : k ≤ M_end k := M_end_strictMono.id_le k
    have hlow : N ≤ K_t * c := hNt_spec N (by omega)
    have hup : mParam k * c ≤ 2 * N := target_sumset_ncard_bound hsub_t hdisj_t k r hhub
    have hmc : 2 * (K_t * c) + c ≤ mParam k * c := by
      simpa [add_one_mul, mul_assoc] using
        Nat.mul_le_mul_right c (show 2 * K_t + 1 ≤ mParam k by dsimp [mParam, qParam]; omega)
    rcases eq_or_ne c 0 with hc0 | hc_pos
    · rw [hc0, mul_zero] at hlow; omega
    · omega
  rcases exists_cfg_of_partition hcov k with ⟨r, hr₁⟩ | ⟨r, hr₂⟩
  · exact hcontra (hcov ▸ Set.subset_union_right) hdisj.symm
      (le_max_right _ _) (le_max_right _ _) hN₂ r hr₁
  · exact hcontra (hcov ▸ Set.subset_union_left) hdisj
      (le_max_left _ _) (le_max_left _ _) hN₁ r hr₂

/--
Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive density in the literal sense that its
natural density exists and is positive.
Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$
both have positive density in this sense?

This was disproved by the DeepMind prover agent.
-/
@[category research solved, question, AMS 5,
formal_proof using formal_conjectures at "https://github.com/mo271/formal-conjectures/blob/486bc8afae062b6711cd16d3466d651ee2880a52/FormalConjectures/ErdosProblems/741.lean#L1449"]
theorem erdos_741.variants.exact_density :
    ¬ ∀ A : Set ℕ, HasPosDensity (A + A) → ∃ A₁ A₂,
    A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ HasPosDensity (A₁ + A₁)
    ∧ HasPosDensity (A₂ + A₂) := by
  sorry

/--
Is there a basis $A$ of order $2$ such that if $A=A_1\sqcup A_2$ then $A_1+A_1$ and $A_2+A_2$
cannot both have bounded gaps?

This was proved by DeepMind prover agent.
 -/
@[category research solved, question, AMS 5,
formal_proof using formal_conjectures at "https://github.com/mo271/formal-conjectures/blob/486bc8afae062b6711cd16d3466d651ee2880a52/FormalConjectures/ErdosProblems/741.lean#L1629"]
theorem erdos_741.parts.ii : ∃ A : Set ℕ, IsAddBasisOfOrder (A ∪ {0}) 2 ∧ ∀ A₁ A₂,
    A = A₁ ∪ A₂ → Disjoint A₁ A₂ → ¬ (IsSyndetic (A₁ + A₁) ∧ IsSyndetic (A₂ + A₂)) := by
  sorry


end Erdos741
