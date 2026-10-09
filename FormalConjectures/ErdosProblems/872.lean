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
# Erdős Problem 872

This file states Erdős Problem 872 for the primitive-set saturation game on $\{2, \dots, n\}$.
The game value `L n` is defined by a finite minimax recursion: Prolonger moves first and maximizes
the final size of the claimed primitive set, while Shortener minimizes it.

The problem statement does not fix the turn order. This file fixes Prolonger to move first,
following the convention used in the forum discussion of the problem. The choice is not cosmetic:
computational data suggests the Shortener-first value tracks $\pi(n)$ while the Prolonger-first
value grows linearly, and the questions below concern the Prolonger-first quantity.

*References:*
- [erdosproblems.com/872](https://www.erdosproblems.com/872)
- [erdosproblems.com/forum/thread/872](https://www.erdosproblems.com/forum/thread/872)
-/

@[expose] public section

open Filter Finset Nat List

namespace Erdos872

noncomputable section

/-- A primitive subset of $\{2, \dots, n\}$ is a set in which no element divides another.
The quantified divisibility condition is one-sided because the variables range over all ordered
pairs of distinct elements. -/
def IsPrimitive (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 n ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a ∣ b

/- The two-player primitive-set saturation game on `{2, ..., n}`.

A position records the already claimed set and the unclaimed pool. A legal move chooses `x` from
the pool such that adding `x` keeps the claimed set primitive. The next position inserts `x` into
the claimed set and erases `x` from the pool. Elements that have become illegal are left in the
pool, but `legalMoves` filters them out at the next turn. Thus the game ends exactly when no
unclaimed element can be legally added, and the pool cardinality strictly decreases after every
played move.
-/

/-- A game position consists of the already claimed set and the still unclaimed pool. -/
structure GamePos (n : ℕ) where
  claimed : Finset ℕ
  pool : Finset ℕ

/-- The legal moves from a position: unclaimed elements whose insertion preserves primitiveness. -/
def legalMoves {n : ℕ} (p : GamePos n) : Finset ℕ :=
  open scoped Classical in
  p.pool.filter fun x => IsPrimitive n (insert x p.claimed)

/-- Membership in `legalMoves`: a legal move is a pool element whose insertion preserves
primitiveness. -/
@[category API, AMS 5]
lemma mem_legalMoves {n : ℕ} {p : GamePos n} {x : ℕ} :
    x ∈ legalMoves p ↔ x ∈ p.pool ∧ IsPrimitive n (insert x p.claimed) := by
  classical
  simp [legalMoves]

/-- Apply a move by claiming `x` and removing it from the unclaimed pool.

This function is intentionally total: if `x` is not legal, it still returns the formal position
obtained by inserting and erasing `x`. The minimax recursion below only calls it for
`x ∈ legalMoves p`. -/
def applyMove {n : ℕ} (p : GamePos n) (x : ℕ) : GamePos n where
  claimed := insert x p.claimed
  pool := p.pool.erase x

/-- The empty starting position on $\{2, \dots, n\}$. -/
def startPos (n : ℕ) : GamePos n where
  claimed := ∅
  pool := Finset.Icc 2 n

/-- Auxiliary finite minimax recursion with an explicit fuel bound.

At a Prolonger turn (`turn = true`) the recursion takes the maximum over legal moves; at a
Shortener turn (`turn = false`) it takes the minimum. If there are no legal moves, or the fuel is
exhausted, it returns the current final size `p.claimed.card`. Starting with fuel `p.pool.card` is
sufficient because every played move erases the chosen pool element. -/
def gameValueAux {n : ℕ} : ℕ → Bool → GamePos n → ℕ
  | 0, _turn, p => p.claimed.card
  | fuel + 1, turn, p =>
      let moves := legalMoves p
      let f := fun x => gameValueAux fuel (!turn) (applyMove p x)
      let vals := moves.image f
      if h : moves.Nonempty then
        let hvals : vals.Nonempty := h.image f
        if turn then vals.max' hvals else vals.min' hvals
      else
        p.claimed.card

/-- Each move claims exactly one pool element, so the minimax value never exceeds the number of
already claimed elements plus the number of still unclaimed elements. -/
@[category API, AMS 5]
lemma gameValueAux_le {n : ℕ} (fuel : ℕ) (turn : Bool) (p : GamePos n) :
    gameValueAux fuel turn p ≤ p.claimed.card + p.pool.card := by
  induction fuel generalizing turn p with
  | zero =>
    simp only [gameValueAux]
    exact Nat.le_add_right _ _
  | succ fuel ih =>
    have key : ∀ x ∈ legalMoves p,
        gameValueAux fuel (!turn) (applyMove p x) ≤ p.claimed.card + p.pool.card := by
      intro x hx
      have hxpool : x ∈ p.pool := (mem_legalMoves.mp hx).1
      have h1 : (insert x p.claimed).card ≤ p.claimed.card + 1 := Finset.card_insert_le _ _
      have h2 : (p.pool.erase x).card = p.pool.card - 1 := Finset.card_erase_of_mem hxpool
      have h3 : 0 < p.pool.card := Finset.card_pos.mpr ⟨x, hxpool⟩
      have h4 : gameValueAux fuel (!turn) (applyMove p x) ≤
          (insert x p.claimed).card + (p.pool.erase x).card := ih (!turn) (applyMove p x)
      omega
    have key' : ∀ v ∈ (legalMoves p).image
        (fun x => gameValueAux fuel (!turn) (applyMove p x)),
        v ≤ p.claimed.card + p.pool.card := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact key x hx
    simp only [gameValueAux]
    split_ifs with h ht
    · exact Finset.max'_le _ _ _ key'
    · exact key' _ (Finset.min'_mem _ _)
    · exact Nat.le_add_right _ _

/-- The minimax value of the primitive-set saturation game from `p`, with Prolonger to move.

This is a genuine game-value definition rather than an uninterpreted placeholder. It unfolds the
finite game tree up to `p.pool.card` moves; at each node Prolonger maximizes and Shortener
minimizes the eventual terminal cardinality. -/
def gameLength {n : ℕ} : GamePos n → ℕ := fun p =>
  gameValueAux p.pool.card true p

/-- The Erdős primitive-set game length on $\{2, \dots, n\}$. -/
def L (n : ℕ) : ℕ := gameLength (startPos n)

/-- A set of natural numbers is *primitive* (an antichain under divisibility)
    if `a ∣ b` implies `a = b` for all `a, b` in the set. -/
def IsAntichainDvd (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/-- The game board {2, ..., n}. -/
def gameRange (n : ℕ) : Finset ℕ := Finset.Icc 2 n

/-- The top half H = {⌊n/2⌋ + 1, ..., n}. -/
def topHalf (n : ℕ) : Finset ℕ := Finset.Icc (n / 2 + 1) n

/-- The bottom half B = {2, ..., ⌊n/2⌋}. -/
def botHalf (n : ℕ) : Finset ℕ := Finset.Icc 2 (n / 2)

/-- Covered top elements: M(S) = {h ∈ H : ∃ s ∈ S, s ∣ h}. -/
def coveredTop (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (topHalf n).filter (fun h => ∃ s ∈ S, s ∣ h)

/-- Odd covered top elements: elements of M(S) that are odd. -/
def oddCoveredTop (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (coveredTop n S).filter (fun h => ¬ 2 ∣ h)

/-- Odd centers: C = {s ∈ ℕ : n/4 < s ≤ n/3, s odd}. -/
def oddCenters (n : ℕ) : Finset ℕ :=
  (Finset.Ioc (n / 4) (n / 3)).filter (fun s => ¬ 2 ∣ s)

/-- Bottom-killed centers: {s ∈ C : ∃ t ∈ A, t ∣ s}. -/
def botKilled (A : Finset ℕ) (C : Finset ℕ) : Finset ℕ :=
  C.filter (fun s => ∃ t ∈ A, t ∣ s)

/-- Top-killed centers: {s ∈ C : 2s ∈ A ∨ 3s ∈ A}. -/
def topKilled (A : Finset ℕ) (C : Finset ℕ) : Finset ℕ :=
  C.filter (fun s => 2 * s ∈ A ∨ 3 * s ∈ A)

/-! ## Play Structure -/

/-- A play of the primitive-set game on {2, ..., n}.
    `moves` is the ordered list of chosen elements. -/
structure Play (n : ℕ) where
  moves : List ℕ
  nodup : moves.Nodup
  in_range : ∀ x ∈ moves, x ∈ gameRange n
  prim_prefix : ∀ k, k ≤ moves.length → IsAntichainDvd (moves.take k).toFinset

namespace Play
variable {n : ℕ}

/-- The terminal (final) set of a play. -/
def terminal (π : Play n) : Finset ℕ := π.moves.toFinset

/-- The prefix set after the first `t` moves. -/
def prefixAt (π : Play n) (t : ℕ) : Finset ℕ := (π.moves.take t).toFinset

/-- A play is maximal if no legal move remains:
    for every `y ∈ {2,...,n} \ A`, some `a ∈ A` satisfies `a ∣ y` or `y ∣ a`. -/
def IsMaximal (π : Play n) : Prop :=
  ∀ y ∈ gameRange n, y ∉ π.terminal →
    ∃ a ∈ π.terminal, a ∣ y ∨ y ∣ a

/-- A play is *C-respecting* if at every Shortener turn (even 1-based index,
    equivalently odd 0-based index), whenever a legal C-move exists,
    the Shortener plays in C. -/
def IsCRespecting (π : Play n) (C : Finset ℕ) : Prop :=
  ∀ i (hi : i < π.moves.length),
    i % 2 = 1 →
    (∃ s ∈ C, s ∈ gameRange n ∧ s ∉ π.prefixAt i ∧
      IsAntichainDvd (insert s (π.prefixAt i))) →
    π.moves.get ⟨i, hi⟩ ∈ C

/-- The terminal set is primitive. -/
lemma terminal_prim (π : Play n) : IsAntichainDvd π.terminal := by
  have h := π.prim_prefix π.moves.length (le_refl _)
  simp [terminal, List.take_length] at h ⊢
  exact h

/-- The terminal set is contained in the game range. -/
lemma terminal_sub (π : Play n) : π.terminal ⊆ gameRange n := by
  intro x hx
  simp [terminal, List.mem_toFinset] at hx
  exact π.in_range x hx

end Play

-- ====================================================================
-- File: RequestProject/Combinatorics.lean
-- ====================================================================
/-!
# Combinatorial Lemmas for the Primitive Set Game

These lemmas establish the key combinatorial facts about maximal primitive sets,
the even matching, parity slack, odd centers, and kill types.
They do not depend on the Play structure or C-respecting property.
-/


open Finset Nat

/-! ## Terminal Structure -/

/-
The top half and bottom half partition the game range.
-/
lemma gameRange_eq_union (n : ℕ) (hn : 2 ≤ n) :
    gameRange n = botHalf n ∪ topHalf n := by
  unfold gameRange botHalf topHalf;
  grind

/-
The top half and bottom half are disjoint.
-/
lemma bot_top_disjoint (n : ℕ) :
    Disjoint (botHalf n) (topHalf n) := by
  exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hx₁ |>.1, Finset.mem_Icc.mp hx₁ |>.2 ⟩ ), Finset.mem_Icc.mp ( Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp hx₂ |>.1, Finset.mem_Icc.mp hx₂ |>.2 ⟩ ) ] ;

/-
Cardinality of the top half.
-/
lemma topHalf_card (n : ℕ) (_hn : 2 ≤ n) :
    (topHalf n).card = n - n / 2 := by
  unfold topHalf; aesop;

/-
For a maximal primitive A ⊆ {2,...,n}, A ∩ H = H \ M(A ∩ B).
    Stated as the terminal identity: |A| + |M(S)| = |S| + |H|.
-/
lemma terminal_card {n : ℕ} {A : Finset ℕ}
    (hn : 2 ≤ n) (hA : A ⊆ gameRange n) (hprim : IsAntichainDvd A)
    (hmax : ∀ y ∈ gameRange n, y ∉ A → ∃ a ∈ A, a ∣ y ∨ y ∣ a) :
    A.card + (coveredTop n (A ∩ botHalf n)).card =
      (A ∩ botHalf n).card + (topHalf n).card := by
  -- Let's split A into its bottom and top parts.
  set S := A ∩ (Finset.Icc 2 (n / 2))
  set H := Finset.Icc (n / 2 + 1) n
  have hA_split : A = S ∪ (A ∩ H) := by
    ext x;
    simp +zetaDelta at *;
    exact ⟨ fun hx => if h : x ≤ n / 2 then Or.inl ⟨ hx, Finset.mem_Icc.mp ( hA hx ) |>.1, h ⟩ else Or.inr ⟨ hx, not_le.mp h, Finset.mem_Icc.mp ( hA hx ) |>.2 ⟩, fun hx => hx.elim ( fun hx => hx.1 ) fun hx => hx.1 ⟩;
  -- We need to show that $A \cap H = H \setminus M$.
  have hA_H : A ∩ H = H \ (coveredTop n S) := by
    ext x;
    simp +zetaDelta at *;
    constructor <;> intro hx;
    · unfold coveredTop; simp +decide [ hx ] ;
      exact fun _ y hy hy' hy'' => fun h => by have := hprim y hy x hx.1 h; linarith [ Nat.div_mul_le_self n 2 ] ;
    · contrapose! hmax;
      refine' ⟨ x, _, _, _ ⟩ <;> norm_num [ gameRange ] at *;
      · omega;
      · exact fun hx' => by linarith [ hmax hx' hx.1.1 ] ;
      · intro a ha; refine' ⟨ _, _ ⟩ <;> intro h <;> have := hprim a ha x;
        · obtain ⟨ k, hk ⟩ := h;
          rcases k with ( _ | _ | k ) <;> simp +decide [ hk ] at *;
          · grind;
          · exact hx.2 ( Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, a, Finset.mem_inter.mpr ⟨ ha, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( hA ha ) ], by nlinarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos ] ⟩ ⟩, by norm_num ⟩ );
        · obtain ⟨ k, hk ⟩ := h;
          rcases k with ( _ | _ | k ) <;> simp +decide [ hk ] at *;
          · linarith [ Finset.mem_Icc.mp ( hA ha ) ];
          · linarith [ hmax ha hx.1.1, Finset.mem_Icc.mp ( hA ha ) ];
          · have := hA ha; norm_num at this; nlinarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos ] ;
  rw [ hA_split, hA_H, Finset.card_union_of_disjoint ];
  · rw [ show ( S ∪ H \ coveredTop n S ) ∩ botHalf n = S from ?_ ];
    · rw [ add_assoc, Finset.card_sdiff_add_card ];
      exact congrArg _ ( congrArg _ ( Finset.union_eq_left.mpr <| Finset.filter_subset _ _ ) );
    · ext x; simp [S, H, botHalf];
      grind;
  · exact Finset.disjoint_left.mpr fun x hxS hxH => by linarith [ Finset.mem_Icc.mp ( Finset.mem_inter.mp hxS |>.2 ), Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hxH |>.1 ) ] ;

/-! ## Even Matching and Parity Slack -/

/-
Parity slack: |M(S)| ≥ |S| + |M(S) ∩ odd|.
    The even matching provides an injection f : S → M(S) with
    f(S) consisting only of even elements.
-/
lemma parity_slack {n : ℕ} {S : Finset ℕ}
    (_hn : 2 ≤ n)
    (hS : S ⊆ botHalf n) (hprim : IsAntichainDvd S) :
    S.card + (oddCoveredTop n S).card ≤ (coveredTop n S).card := by
  -- Define the function $f: S \to \text{coveredTop } n S$ by $f(s) = 2^k s$ where $k$ is the smallest integer such that $2^k s > n/2$.
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, (∀ s ∈ S, f s ∈ coveredTop n S ∧ 2 ∣ f s ∧ s ∣ f s) ∧ (∀ s1 s2, s1 ∈ S → s2 ∈ S → s1 ≠ s2 → f s1 ≠ f s2) := by
    -- For each $s \in S$, define $f(s)$ as the smallest power of 2 times $s$ that is greater than $n/2$.
    have hf_exists : ∀ s ∈ S, ∃ k : ℕ, 2^k * s ∈ coveredTop n S ∧ 2 ∣ 2^k * s ∧ s ∣ 2^k * s := by
      intro s hs
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 2^k * s > n / 2 ∧ 2^k * s ≤ n := by
        have h_exists_k : ∃ k : ℕ, 2^k * s > n / 2 := by
          use Nat.log 2 (n / 2) + 1;
          exact lt_of_lt_of_le ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ( Nat.le_mul_of_pos_right _ ( Finset.mem_Icc.mp ( hS hs ) |>.1.trans_lt' ( by decide ) ) );
        obtain ⟨ k, hk ⟩ := Nat.findX h_exists_k;
        rcases k <;> simp_all +decide [ pow_succ', mul_assoc ];
        · exact absurd hk ( by have := hS hs; exact not_lt_of_ge ( Finset.mem_Icc.mp this |>.2 ) );
        · exact ⟨ ‹_› + 1, by simpa only [ pow_succ', mul_assoc ] using hk.1, by simpa only [ pow_succ', mul_assoc ] using by linarith [ hk.2 _ le_rfl, Nat.div_mul_le_self n 2 ] ⟩;
      refine' ⟨ k, _, _, _ ⟩ <;> norm_num [ hk ];
      · exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos ], by linarith ⟩, s, hs, by norm_num ⟩;
      · rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc, Nat.dvd_iff_mod_eq_zero ];
        have := hS hs; simp_all +decide [ botHalf ] ; omega;
    choose! k hk using hf_exists;
    refine' ⟨ _, fun s hs => hk s hs, _ ⟩;
    intro s1 s2 hs1 hs2 hne h_eq
    have h_div : s1 ∣ s2 ∨ s2 ∣ s1 := by
      by_cases h_cases : k s1 ≤ k s2;
      · cases le_iff_exists_add.mp h_cases ; simp_all +decide [ pow_add, mul_assoc ];
      · have h_div : 2 ^ (k s1 - k s2) * s1 = s2 := by
          refine' mul_left_cancel₀ ( pow_ne_zero ( k s2 ) two_ne_zero ) _;
          rw [ ← mul_assoc, ← pow_add, add_tsub_cancel_of_le ( le_of_not_ge h_cases ), h_eq ];
        exact Or.inl ( h_div ▸ dvd_mul_left _ _ );
    exact hne ( hprim s1 hs1 s2 hs2 ( h_div.resolve_right fun h => hne <| hprim s2 hs2 s1 hs1 h ▸ rfl ) );
  -- Since $f$ is injective, the image of $S$ under $f$ is a subset of $coveredTop n S$ with cardinality $|S|$.
  have h_image : (Finset.image f S).card = S.card := by
    exact Finset.card_image_of_injOn fun x hx y hy hxy => Classical.not_not.1 fun h => hf.2 x y hx hy h hxy;
  rw [ ← h_image, ← Finset.card_union_of_disjoint ];
  · exact Finset.card_le_card ( Finset.union_subset ( Finset.image_subset_iff.mpr fun x hx => hf.1 x hx |>.1 ) ( Finset.filter_subset _ _ ) );
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hx₁; exact Finset.mem_filter.mp hx₂ |>.2 ( hf.1 s hs |>.2.1 ) ;

/-! ## Odd Centers -/

/-
Centers lie in the bottom half.
-/
lemma oddCenters_sub_botHalf {n : ℕ} (hn : 4 ≤ n) :
    oddCenters n ⊆ botHalf n := by
  unfold oddCenters botHalf at *;
  grind

/-
Centers lie in the game range.
-/
lemma oddCenters_sub_gameRange {n : ℕ} (hn : 4 ≤ n) :
    oddCenters n ⊆ gameRange n := by
  exact Finset.Subset.trans ( oddCenters_sub_botHalf hn ) ( Finset.Icc_subset_Icc ( by decide ) ( Nat.div_le_self _ _ ) )

/-
For s ∈ C, 2s ∈ H.
-/
lemma center_double_in_top {n : ℕ} {s : ℕ} (hs : s ∈ oddCenters n) :
    2 * s ∈ topHalf n := by
  unfold oddCenters at hs; unfold topHalf; simp_all +arith +decide;
  lia

/-
For s ∈ C, 3s ∈ H and 3s ≤ n.
-/
lemma center_triple_in_top {n : ℕ} {s : ℕ} (hs : s ∈ oddCenters n) :
    3 * s ∈ topHalf n := by
  unfold oddCenters at hs; unfold topHalf; simp_all +arith +decide;
  omega

/-
For s ∈ C, 3s is odd.
-/
lemma center_triple_odd {n : ℕ} {s : ℕ} (hs : s ∈ oddCenters n) :
    ¬ 2 ∣ (3 * s) := by
  unfold oddCenters at hs; norm_num at hs; omega;

/-
For s ∈ C, the only multiples of s in {2,...,n} are s, 2s, 3s.
-/
lemma center_multiples {n : ℕ} {s : ℕ} (hs : s ∈ oddCenters n)
    {k : ℕ} (hk : k * s ∈ gameRange n) (hk1 : 1 ≤ k) :
    k = 1 ∨ k = 2 ∨ k = 3 := by
  unfold oddCenters at hs;
  unfold gameRange at hk;
  rcases k with ( _ | _ | _ | _ | k ) <;> simp_all +arith +decide;
  grind

/-
Leaf disjointness: for distinct s, s' ∈ C, the values 2s, 3s, 2s', 3s'
    are all distinct.
-/
lemma leaf_disjoint {n : ℕ} {s s' : ℕ}
    (hs : s ∈ oddCenters n) (hs' : s' ∈ oddCenters n) (hne : s ≠ s') :
    ({2 * s, 3 * s} : Finset ℕ) ∩ {2 * s', 3 * s'} = ∅ := by
  -- Since $s \neq s'$ and both are in the oddCenters, they are odd and lie in the interval $(n/4, n/3]$.
  have hs_odd : ¬2 ∣ s := by
    exact Finset.mem_filter.mp hs |>.2
  have hs'_odd : ¬2 ∣ s' := by
    exact Finset.mem_filter.mp hs' |>.2
  have hs_bounds : n / 4 < s ∧ s ≤ n / 3 := by
    unfold oddCenters at hs; aesop;
  have hs'_bounds : n / 4 < s' ∧ s' ≤ n / 3 := by
    unfold oddCenters at hs'; aesop;
  grind

/-! ## Kill Types -/

/-
Every center is killed in a maximal primitive set.
-/
lemma every_center_killed {n : ℕ} {A : Finset ℕ}
    (hn : 4 ≤ n)
    (hA : A ⊆ gameRange n) (_hprim : IsAntichainDvd A)
    (hmax : ∀ y ∈ gameRange n, y ∉ A → ∃ a ∈ A, a ∣ y ∨ y ∣ a) :
    ∀ s ∈ oddCenters n,
      s ∈ botKilled A (oddCenters n) ∨ s ∈ topKilled A (oddCenters n) := by
  intros s hs
  by_cases hsA : s ∈ A;
  · exact Or.inl <| Finset.mem_filter.mpr ⟨ hs, s, hsA, dvd_rfl ⟩;
  · specialize hmax s ( oddCenters_sub_gameRange hn hs ) hsA;
    obtain ⟨ a, haA, ha | ha ⟩ := hmax <;> simp_all +decide [ botKilled, topKilled ];
    · exact Or.inl ⟨ a, haA, ha ⟩;
    · obtain ⟨ k, hk ⟩ := ha;
      have := center_multiples hs ( show k * s ∈ gameRange n from ?_ ) ?_ <;> simp_all +decide [ mul_comm ];
      · rcases this with ( rfl | rfl | rfl ) <;> simp_all +decide;
      · exact hA haA;
      · exact Nat.pos_of_ne_zero ( by rintro rfl; have := hA haA; simp_all +decide [ gameRange ] )

/-
Kills are exclusive: no center is both bottom-killed and top-killed.
-/
lemma kills_exclusive {n : ℕ} {A : Finset ℕ}
    (hprim : IsAntichainDvd A) :
    Disjoint (botKilled A (oddCenters n)) (topKilled A (oddCenters n)) := by
  -- Suppose s ∈ botKilled ∩ topKilled. Then ∃ t ∈ A with t ∣ s, and 2s ∈ A or 3s ∈ A.
  unfold botKilled topKilled
  by_contra h_not_disjoint
  obtain ⟨s, hs⟩ : ∃ s, s ∈ (oddCenters n) ∧ (∃ t ∈ A, t ∣ s) ∧ (2 * s ∈ A ∨ 3 * s ∈ A) := by
    rw [ Finset.not_disjoint_iff ] at h_not_disjoint ; aesop;
  obtain ⟨t, htA, hts⟩ : ∃ t ∈ A, t ∣ s := hs.right.left
  obtain h2s | h3s : 2 * s ∈ A ∨ 3 * s ∈ A := hs.right.right;
  · have := hprim _ htA _ h2s;
    rcases s with ( _ | _ | s ) <;> simp_all +arith +decide;
    · unfold oddCenters at hs; aesop;
    · exact absurd ( this ( hts.trans ( by exact ⟨ 2, by ring ⟩ ) ) ) ( by linarith [ Nat.le_of_dvd ( Nat.succ_pos _ ) hts ] );
  · have := hprim _ htA _ h3s;
    rcases hts with ⟨ k, rfl ⟩;
    rcases t with ( _ | _ | t ) <;> rcases k with ( _ | _ | k ) <;> norm_num at *;
    · unfold oddCenters at hs; aesop;
    · unfold oddCenters at hs; aesop;
    · unfold oddCenters at hs; aesop;
    · linarith;
    · exact absurd ( this ⟨ 3 * ( k + 1 + 1 ), by ring ⟩ ) ( by nlinarith )

/-
The partition C = Y ⊔ Z gives |C| = |Y| + |Z|.
-/
lemma center_card_split {n : ℕ} {A : Finset ℕ}
    (hn : 4 ≤ n)
    (hA : A ⊆ gameRange n) (hprim : IsAntichainDvd A)
    (hmax : ∀ y ∈ gameRange n, y ∉ A → ∃ a ∈ A, a ∣ y ∨ y ∣ a) :
    (oddCenters n).card =
      (botKilled A (oddCenters n)).card + (topKilled A (oddCenters n)).card := by
  rw [ ← Finset.card_union_of_disjoint ];
  · congr with x;
    simp +zetaDelta at *;
    exact ⟨ fun hx => every_center_killed hn hA hprim hmax x hx, fun hx => by cases hx <;> [ exact Finset.mem_filter.mp ‹_› |>.1; exact Finset.mem_filter.mp ‹_› |>.1 ] ⟩;
  · exact kills_exclusive hprim

/-! ## Bottom-Kills Produce Odd Covered Top Elements -/

/-
Each bottom-killed center s gives an odd element 3s ∈ M(S).
    The injection s ↦ 3s shows |Z| ≤ |M(S) ∩ odd|.
-/
lemma odd_covers_ge_botKilled {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ gameRange n) :
    (botKilled A (oddCenters n)).card ≤ (oddCoveredTop n (A ∩ botHalf n)).card := by
  refine' Finset.card_le_card_of_injOn _ _ _;
  use fun s => 3 * s;
  · intro s hs
    simp [botKilled, oddCoveredTop] at hs ⊢;
    unfold coveredTop oddCenters at *; simp_all +decide [ Nat.mul_mod ] ;
    unfold topHalf botHalf; simp_all +decide ;
    exact ⟨ ⟨ by omega, by omega ⟩, by obtain ⟨ t, ht₁, ht₂ ⟩ := hs.2; exact ⟨ t, ⟨ ht₁, by have := hA ht₁; exact Finset.mem_Icc.mp this |>.1, by have := hA ht₁; exact Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by linarith [ Finset.mem_Icc.mp this |>.2, Nat.le_of_dvd ( Nat.pos_of_ne_zero <| by aesop ) ht₂, Nat.div_mul_le_self n 3 ] ⟩, ht₂.mul_left _ ⟩ ⟩;
  · aesop_cat

/-! ## Lower Bound on |C| -/

/-
Lower bound on the number of odd centers: |C| ≥ n/48 for n ≥ 48.
-/
lemma centers_card_lower {n : ℕ} (hn : 48 ≤ n) :
    n / 48 ≤ (oddCenters n).card := by
  unfold oddCenters;
  rw [ show { s ∈ Ioc ( n / 4 ) ( n / 3 ) | ¬2 ∣ s } = Finset.image ( fun k => 2 * k + 1 ) ( Finset.Icc ( ( n / 4 + 1 ) / 2 ) ( ( n / 3 - 1 ) / 2 ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => by linarith ];
  · norm_num; omega;
  · ext;
    simp +zetaDelta at *;
    exact ⟨ fun h => ⟨ ‹_› / 2, ⟨ by omega, by omega ⟩, by omega ⟩, fun ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ => ⟨ ⟨ by omega, by omega ⟩, by omega ⟩ ⟩

/-! ## Main Combinatorial Bound -/

/-
The main combinatorial bound (without the top-kill bound):
    |A| + |Z| ≤ |H| for any maximal primitive A.
-/
lemma main_bound {n : ℕ} {A : Finset ℕ}
    (hn : 2 ≤ n)
    (hA : A ⊆ gameRange n) (hprim : IsAntichainDvd A)
    (hmax : ∀ y ∈ gameRange n, y ∉ A → ∃ a ∈ A, a ∣ y ∨ y ∣ a) :
    A.card + (botKilled A (oddCenters n)).card ≤ (topHalf n).card := by
  have := terminal_card hn hA hprim hmax;
  have := parity_slack hn ( Finset.inter_subset_right ) ( fun a ha b hb hab => hprim a ( Finset.subset_iff.mp ( Finset.inter_subset_left ) ha ) b ( Finset.subset_iff.mp ( Finset.inter_subset_left ) hb ) hab ) ; simp_all +decide ;
  linarith [ odd_covers_ge_botKilled hA ]

-- ====================================================================
-- File: RequestProject/MainTheorem.lean
-- ====================================================================
/-!
# Main Theorem — Strategy-Free Formulation

We prove the top-kill bound (Lemma 5.7) and combine it with the
combinatorial lemmas to establish the main theorem: any maximal
C-respecting play has terminal set of size at most ⌈n/2⌉ - |C|/2.

We also prove non-vacuousness: maximal C-respecting plays exist for all n ≥ 2.
-/


open Finset Nat List

set_option maxHeartbeats 1600000

/-! ## Helper Lemmas for Top-Kill Bound -/

/-
An unkilled center is a legal move: if no element of the current prefix divides s,
    and neither 2s nor 3s is in the prefix, then inserting s preserves primitiveness.
-/
lemma unkilled_center_legal {n : ℕ} {s : ℕ} {P : Finset ℕ}
    (_hn : 4 ≤ n)
    (hs : s ∈ oddCenters n)
    (hP_prim : IsAntichainDvd P)
    (hP_sub : P ⊆ gameRange n)
    (h_not_bot : ∀ t ∈ P, ¬(t ∣ s))
    (h_not_s : s ∉ P)
    (h_not_2s : 2 * s ∉ P)
    (h_not_3s : 3 * s ∉ P) :
    IsAntichainDvd (insert s P) := by
  -- For any a, b ∈ insert s P, we need to show a ∣ b → a = b.
  intro a ha b hb hab
  by_cases ha_s : a = s
  by_cases hb_s : b = s;
  · rw [ha_s, hb_s];
  · obtain ⟨ k, hk ⟩ := hab;
    rcases k with ( _ | _ | _ | _ | k ) <;> simp_all +decide [ Nat.mul_succ ];
    · exact absurd ( hP_sub hb ) ( by norm_num [ gameRange ] );
    · exact h_not_2s ( by simpa only [ two_mul ] using hb );
    · exact h_not_3s ( by convert hb using 1; ring );
    · have := hP_sub ( hb.resolve_left ( by aesop ) ) ; simp_all +decide [ gameRange ] ;
      exact absurd this.2 ( by nlinarith only [ _hn, show s > n / 4 from Finset.mem_Ioc.mp ( Finset.mem_filter.mp hs |>.1 ) |>.1, Nat.div_add_mod n 4, Nat.mod_lt n zero_lt_four ] );
  · by_cases hb_s : b = s <;> simp_all +decide;
    exact hP_prim a ha b hb hab

/-- Odd centers are in the game range. -/
lemma oddCenters_mem_gameRange {n : ℕ} (hn : 4 ≤ n) {s : ℕ} (hs : s ∈ oddCenters n) :
    s ∈ gameRange n :=
  oddCenters_sub_gameRange hn hs

/-
Odd centers are in the bottom half, not the top half.
-/
lemma oddCenters_not_in_topHalf {n : ℕ} (hn : 4 ≤ n) {s : ℕ} (hs : s ∈ oddCenters n) :
    s ∉ topHalf n := by
  exact fun h => Finset.disjoint_left.mp ( bot_top_disjoint n ) ( oddCenters_sub_botHalf hn hs ) h

/-
Top-killed center values (2s, 3s) are in the top half, hence not in C.
-/
lemma topkill_values_not_in_C {n : ℕ} {s : ℕ} (hn : 4 ≤ n) (hs : s ∈ oddCenters n) :
    2 * s ∉ oddCenters n ∧ 3 * s ∉ oddCenters n := by
  constructor <;> intro h <;> have := Finset.mem_filter.mp h <;> have := Finset.mem_filter.mp hs <;> simp_all +decide [ Finset.mem_Ioc ];
  omega

/-
A top-killed center is not bottom-killed (from kills_exclusive).
-/
lemma topkilled_not_botkilled {n : ℕ} {A : Finset ℕ} {s : ℕ}
    (hprim : IsAntichainDvd A) (hs : s ∈ topKilled A (oddCenters n)) :
    s ∉ botKilled A (oddCenters n) := by
  apply Finset.disjoint_right.mp (kills_exclusive hprim) hs

/-
If s ∈ topKilled A C and A is primitive, then s ∉ A.
-/
lemma topkilled_not_in_A {n : ℕ} {A : Finset ℕ} {s : ℕ}
    (hprim : IsAntichainDvd A) (hA : A ⊆ gameRange n)
    (hs : s ∈ topKilled A (oddCenters n)) :
    s ∉ A := by
  unfold topKilled at hs;
  have := hprim s; simp_all +decide [ IsAntichainDvd ] ;
  rcases hs.2 with ( h | h ) <;> specialize this <;> have := hA h <;> simp_all +decide [ gameRange ];
  · exact fun H => by have := hprim _ H _ h ( by norm_num ) ; linarith [ Finset.mem_Icc.mp ( hA H ) ] ;
  · exact fun H => by have := hprim _ H _ h ( by norm_num ) ; linarith [ Finset.mem_Icc.mp ( hA H ) ] ;

/-
For s ∈ topKilled, s doesn't divide any element of A other than 2s and 3s.
-/
lemma topkilled_no_other_multiples {n : ℕ} {A : Finset ℕ} {s : ℕ}
    (hA : A ⊆ gameRange n)
    (hs_center : s ∈ oddCenters n) {a : ℕ} (ha : a ∈ A)
    (hdvd : s ∣ a) :
    a = s ∨ a = 2 * s ∨ a = 3 * s := by
  -- Since $a$ is in $A$ and $A$ is a subset of the gameRange $n$, $a$ must be at least 2. Therefore, $k$ must be at least 1.
  obtain ⟨k, hk⟩ : ∃ k, a = k * s := by
    exact exists_eq_mul_left_of_dvd hdvd
  have hk_ge_1 : 1 ≤ k := by
    exact Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Finset.mem_Icc.mp ( hA ha ) ] );
  have := center_multiples hs_center ( show k * s ∈ gameRange n from by simpa [ hk ] using hA ha ) hk_ge_1; aesop;

/-! ## Top-Kill Bound (Lemma 5.7) -/

/-
Top-kill bound: for any maximal C-respecting play, |Y| ≤ |Z| + 1.

This is the key new lemma using the C-respecting hypothesis.
The proof uses an injection argument:

For each s ∈ Y (top-killed), let j_s be the first index where 2s or 3s
appears in the play. Then:
- j_s is a Prolonger turn (even 0-based), because at any Shortener turn
  where s is unkilled, the C-respecting property forces a C-move, but
  C ⊆ botHalf while {2s,3s} ⊆ topHalf.
- For j_s ≥ 2, the preceding index j_s - 1 is a Shortener turn where
  an unkilled center exists, so moves[j_s-1] ∈ C ∩ A ⊆ Z.
- The map s ↦ moves[j_s-1] is injective (by nodup + leaf_disjoint).
- At most one s has j_s = 0.
- Therefore |Y| ≤ |Z| + 1.
-/
lemma top_kill_bound {n : ℕ} (π : Play n)
    (hn : 4 ≤ n)
    (_hmax : π.IsMaximal)
    (hcr : π.IsCRespecting (oddCenters n)) :
    (topKilled π.terminal (oddCenters n)).card ≤
      (botKilled π.terminal (oddCenters n)).card + 1 := by
  set A := π.terminal
  set C := oddCenters n
  set Y := topKilled A C
  set Z := botKilled A C
  have hY : Y = {s ∈ C | 2 * s ∈ A ∨ 3 * s ∈ A} := by
    rfl;
  -- For each s ∈ Y, let j_s be the first index where 2s or 3s appears in the play.
  have h_j_s : ∀ s ∈ Y, ∃ j_s : Fin π.moves.length, (π.moves.get j_s = 2 * s ∨ π.moves.get j_s = 3 * s) ∧ ∀ k < j_s, ¬(π.moves.get k = 2 * s ∨ π.moves.get k = 3 * s) := by
    intro s hs
    obtain ⟨j_s, hj_s⟩ : ∃ j_s : Fin π.moves.length, (π.moves.get j_s = 2 * s ∨ π.moves.get j_s = 3 * s) := by
      have h_exists_j_s : 2 * s ∈ A ∨ 3 * s ∈ A := by
        aesop;
      simp +zetaDelta at *;
      rcases h_exists_j_s with ( h | h ) <;> [ exact List.mem_iff_get.mp ( by simpa [ Play.terminal ] using h ) |> fun ⟨ j, hj ⟩ => ⟨ j, Or.inl hj ⟩ ; exact List.mem_iff_get.mp ( by simpa [ Play.terminal ] using h ) |> fun ⟨ j, hj ⟩ => ⟨ j, Or.inr hj ⟩ ];
    by_cases h : ∃ k : Fin π.moves.length, k.val < j_s + 1 ∧ (π.moves.get k = 2 * s ∨ π.moves.get k = 3 * s);
    · obtain ⟨ k, hk₁, hk₂ ⟩ := h;
      have h_min : ∃ m ∈ Finset.univ.filter (fun m : Fin π.moves.length => (π.moves.get m = 2 * s ∨ π.moves.get m = 3 * s)), ∀ k ∈ Finset.univ.filter (fun m : Fin π.moves.length => (π.moves.get m = 2 * s ∨ π.moves.get m = 3 * s)), m.val ≤ k.val := by
        exact Finset.exists_min_image _ _ ⟨ k, by aesop ⟩;
      grind;
    · grind;
  choose! j hj₁ hj₂ using h_j_s;
  -- For each s ∈ Y, j_s is even.
  have h_j_even : ∀ s hs, (j s hs).val % 2 = 0 := by
    intro s hs
    by_contra h_contra
    have h_unkilled : ∀ t ∈ π.prefixAt (j s hs).val, ¬(t ∣ s) := by
      intro t ht hts
      have h_contra : s ∈ botKilled A C := by
        exact Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hs |>.1, t, by
          exact ⟨ by exact List.mem_toFinset.mpr ( List.mem_of_mem_take ( List.mem_toFinset.mp ht ) ), hts ⟩ ⟩
      exact absurd h_contra (by
      apply topkilled_not_botkilled;
      · exact π.terminal_prim;
      · exact hs)
    have h_not_in_prefix : s ∉ π.prefixAt (j s hs).val := by
      exact fun h => h_unkilled s h ( dvd_refl s )
    have h_not_2s : 2 * s ∉ π.prefixAt (j s hs).val := by
      intro h; specialize hj₂ s hs; simp_all +decide [ Play.prefixAt ] ;
      obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp h;
      have hklt : k.1 < (j s hs).val := lt_of_lt_of_le k.2 (by simp)
      have hlt : (⟨k.1, lt_trans hklt (j s hs).2⟩ : Fin π.moves.length) < j s hs := Fin.mk_lt_mk.mpr hklt
      exact (hj₂ ⟨k.1, lt_trans hklt (j s hs).2⟩ hlt).1 (by simpa using hk)
    have h_not_3s : 3 * s ∉ π.prefixAt (j s hs).val := by
      intro h; specialize hj₂ s hs; simp_all +decide [ Play.prefixAt ] ;
      obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp h;
      have hklt : k.1 < (j s hs).val := lt_of_lt_of_le k.2 (by simp)
      have hlt : (⟨k.1, lt_trans hklt (j s hs).2⟩ : Fin π.moves.length) < j s hs := Fin.mk_lt_mk.mpr hklt
      exact (hj₂ ⟨k.1, lt_trans hklt (j s hs).2⟩ hlt).2 (by simpa using hk)
    have h_legal : IsAntichainDvd (insert s (π.prefixAt (j s hs).val)) := by
      apply unkilled_center_legal hn (by
      exact Finset.mem_filter.mp hs |>.1) (by
      exact π.prim_prefix _ ( by simp )) (by
      exact fun x hx => by obtain ⟨ k, hk₁, hk₂ ⟩ := List.mem_iff_get.mp ( List.mem_toFinset.mp hx ) ; exact π.in_range _ ( by aesop ) ;) h_unkilled h_not_in_prefix h_not_2s h_not_3s
    have h_c_move : s ∈ C := by
      grind
    have h_c_respecting : π.moves.get (j s hs) ∈ C := by
      apply hcr;
      · exact Nat.mod_two_ne_zero.mp h_contra;
      · exact ⟨ s, h_c_move, oddCenters_mem_gameRange hn h_c_move, h_not_in_prefix, h_legal ⟩
    have h_contradiction : π.moves.get (j s hs) ∈ C ∧ (π.moves.get (j s hs) = 2 * s ∨ π.moves.get (j s hs) = 3 * s) := by
      exact ⟨ h_c_respecting, hj₁ s hs ⟩
    have h_final : False := by
      exact absurd h_contradiction.1 ( by rcases h_contradiction.2 with h | h <;> [ exact fun h' => by have := topkill_values_not_in_C hn h_c_move; aesop; ; exact fun h' => by have := topkill_values_not_in_C hn h_c_move; aesop ] )
    exact h_final;
  -- For each s ∈ Y, if j_s ≥ 2, then moves[j_s-1] ∈ Z.
  have h_j_minus_one_in_Z : ∀ s hs, (j s hs).val ≥ 2 → π.moves.get ⟨(j s hs).val - 1, by
    exact lt_of_le_of_lt ( Nat.pred_le _ ) ( Fin.is_lt _ )⟩ ∈ Z := by
    intros s hs hj_ge_two
    have h_unkilled : s ∉ π.prefixAt ((j s hs).val - 1) ∧ ¬(∃ t ∈ π.prefixAt ((j s hs).val - 1), t ∣ s) ∧ ¬(2 * s ∈ π.prefixAt ((j s hs).val - 1)) ∧ ¬(3 * s ∈ π.prefixAt ((j s hs).val - 1)) := by
      refine' ⟨ _, _, _, _ ⟩
      all_goals generalize_proofs at *;
      · intro h;
        have h_contradiction : s ∈ π.terminal := by
          exact Finset.mem_of_subset ( show π.prefixAt ( ( j s hs : ℕ ) - 1 ) ⊆ π.terminal from by
                                        exact fun x hx => by rw [ Play.prefixAt ] at hx; rw [ Play.terminal ] ; exact List.mem_toFinset.mpr ( List.mem_of_mem_take ( List.mem_toFinset.mp hx ) ) ; ) h;
        exact absurd ( topkilled_not_in_A ( show IsAntichainDvd π.terminal from π.terminal_prim ) ( show π.terminal ⊆ gameRange n from π.terminal_sub ) hs ) ( by aesop );
      · rintro ⟨ t, ht₁, ht₂ ⟩;
        have := topkilled_not_botkilled ( show IsAntichainDvd A from π.terminal_prim ) hs; simp_all +decide [ botKilled ] ;
        exact this ( Finset.mem_filter.mp hs |>.1 ) t ( by
          exact Finset.mem_of_subset ( show π.prefixAt ( j s hs - 1 ) ⊆ A from by
                                        exact fun x hx => by exact List.mem_toFinset.mpr ( List.mem_of_mem_take ( List.mem_toFinset.mp hx ) ) ; ) ht₁ ) ht₂;
      · simp +decide [ Play.prefixAt ];
        rw [ List.mem_iff_get ];
        simp +zetaDelta at *;
        intro x hx; specialize hj₂ s hs ⟨ x, by
          exact lt_of_lt_of_le x.2 ( by simp ) ⟩ ( by
          grind ) ; aesop;
      · simp_all +decide [ Play.prefixAt ];
        rw [ List.mem_iff_get ];
        simp +zetaDelta at *;
        intro x hx; specialize hj₂ s ( by
          exact Finset.mem_filter.mp hs |>.1 ) ( by
          grind ) ⟨ x, by
          exact lt_of_lt_of_le x.2 ( by simp ) ⟩ ( by
          grind ) ; aesop;
    have h_legal : IsAntichainDvd (insert s (π.prefixAt ((j s hs).val - 1))) := by
      apply unkilled_center_legal hn (by
      exact Finset.mem_filter.mp hs |>.1) (by
      exact π.prim_prefix _ ( Nat.le_trans ( Nat.pred_le _ ) ( Nat.le_of_lt ( Fin.is_lt _ ) ) )) (by
      exact fun x hx => π.in_range x <| List.mem_toFinset.mp hx |> fun h => List.mem_of_mem_take h) (by
      exact fun t ht => fun h => h_unkilled.2.1 ⟨ t, ht, h ⟩) (by
      exact h_unkilled.1) (by
      exact h_unkilled.2.2.1) (by
      exact h_unkilled.2.2.2);
    have := hcr ( ( j s hs ).val - 1 ) ( by
      grind ) ( by
      grind ) ⟨ s, by
      exact ⟨ Finset.mem_filter.mp hs |>.1, oddCenters_mem_gameRange hn ( Finset.mem_filter.mp hs |>.1 ), h_unkilled.1, h_legal ⟩ ⟩
    generalize_proofs at *;
    refine' Finset.mem_filter.mpr ⟨ this, _ ⟩;
    exact ⟨ _, Finset.mem_coe.mpr ( List.mem_toFinset.mpr ( List.getElem_mem _ ) ), dvd_rfl ⟩
  generalize_proofs at *;
  -- The map s ↦ moves[j_s-1] is injective from {s ∈ Y : j_s ≥ 2} to Z.
  have h_inj : ∀ s hs s' hs' (hs_ge_two : (j s hs).val ≥ 2) (hs'_ge_two : (j s' hs').val ≥ 2), π.moves.get ⟨(j s hs).val - 1, by
    grind⟩ = π.moves.get ⟨(j s' hs').val - 1, by
    grind⟩ → s = s' := by
    intros s hs s' hs' hs_ge_two hs'_ge_two h_eq
    have h_j_eq : (j s hs).val = (j s' hs').val := by
      have := π.nodup; simp_all +decide [ List.nodup_iff_injective_get ] ;
      have := @this ⟨ ( j s hs : ℕ ) - 1, by
        exact Nat.lt_of_le_of_lt (Nat.pred_le _) (Fin.is_lt _) ⟩ ⟨ ( j s' hs' : ℕ ) - 1, by
        exact Nat.lt_of_le_of_lt (Nat.pred_le _) (Fin.is_lt _) ⟩ ; simp_all +decide [ Fin.ext_iff ] ;
      generalize_proofs at *;
      omega
    generalize_proofs at *;
    have := hj₁ s hs; have := hj₁ s' hs'; simp_all +decide ;
    have := Finset.mem_filter.mp ( show s ∈ oddCenters n from by
                                    exact Finset.mem_filter.mp ( hY ▸ hs ) |>.1 ) ; have := Finset.mem_filter.mp ( show s' ∈ oddCenters n from by
                                                                                                            grind +extAll ) ; norm_num at * ; omega;
  generalize_proofs at *;
  have h_card_Y_le_card_Z_plus_one : (Finset.filter (fun s => (j s.1 s.2).val ≥ 2) (Finset.attach Y)).card ≤ Z.card := by
    have h_card_Y_le_card_Z_plus_one : (Finset.image (fun s : {s : ℕ // s ∈ Y} => π.moves.get ⟨(j s.1 s.2).val - 1, by
      exact Nat.lt_of_le_of_lt ( Nat.pred_le _ ) ( Fin.is_lt _ )⟩) (Finset.filter (fun s => (j s.1 s.2).val ≥ 2) (Finset.attach Y))).card ≤ Z.card := by
      exact Finset.card_le_card <| Finset.image_subset_iff.mpr fun s hs => h_j_minus_one_in_Z _ _ <| Finset.mem_filter.mp hs |>.2
    generalize_proofs at *;
    rwa [ Finset.card_image_of_injOn ] at h_card_Y_le_card_Z_plus_one;
    intros s hs s' hs' h_eq;
    apply Subtype.ext;
    have hs_ge := (Finset.mem_filter.mp hs).2;
    have hs'_ge := (Finset.mem_filter.mp hs').2;
    exact h_inj s.1 s.2 s'.1 s'.2 hs_ge hs'_ge h_eq;
  have h_card_Y_lt_two : (Finset.filter (fun s => (j s.1 s.2).val < 2) (Finset.attach Y)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    apply Subtype.ext
    have ha_lt : (j a.1 a.2).val < 2 := (Finset.mem_filter.mp ha).2
    have hb_lt : (j b.1 b.2).val < 2 := (Finset.mem_filter.mp hb).2
    have ha_ev : (j a.1 a.2).val % 2 = 0 := h_j_even a.1 a.2
    have hb_ev : (j b.1 b.2).val % 2 = 0 := h_j_even b.1 b.2
    have hj_eq : j a.1 a.2 = j b.1 b.2 := Fin.ext (by omega)
    have h1 := hj₁ a.1 a.2
    have h2 := hj₁ b.1 b.2
    rw [hj_eq] at h1
    have ha_odd : ¬ 2 ∣ a.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp a.2).1).2
    have hb_odd : ¬ 2 ∣ b.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp b.2).1).2
    omega
  have h_card_Y_split : (Finset.attach Y).card ≤ (Finset.filter (fun s => (j s.1 s.2).val ≥ 2) (Finset.attach Y)).card + (Finset.filter (fun s => (j s.1 s.2).val < 2) (Finset.attach Y)).card := by
    rw [ Finset.card_filter, Finset.card_filter ];
    simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones _ ▸ Finset.sum_le_sum fun x hx => by split_ifs <;> linarith;
  have h_attach : (Finset.attach Y).card = Y.card := Finset.card_attach
  omega

/-! ## Main Theorem -/

/-- **Main Theorem (strategy-free form).**
    For any maximal C-respecting play π with terminal set A,
    |A| + |C|/2 ≤ ⌈n/2⌉, i.e., |A| ≤ ⌈n/2⌉ - |C|/2.

    Since |C| ≈ n/24, this gives |A| ≤ (23/48 + o(1))n. -/
theorem main_theorem {n : ℕ} (hn : 4 ≤ n) (π : Play n)
    (hmax : π.IsMaximal)
    (hcr : π.IsCRespecting (oddCenters n)) :
    π.terminal.card + (oddCenters n).card / 2 ≤ n - n / 2 := by
  have h1 := main_bound (by omega : 2 ≤ n) π.terminal_sub π.terminal_prim hmax
  have h2 := topHalf_card n (by omega : 2 ≤ n)
  have h3 := top_kill_bound π hn hmax hcr
  have h4 := center_card_split hn π.terminal_sub π.terminal_prim hmax
  omega

/-! ## Asymptotic Corollary -/

/-
Stronger lower bound on |C|: |C| ≥ n/24 for n ≥ 48.
-/
lemma centers_card_lower' {n : ℕ} (hn : 48 ≤ n) :
    n / 24 ≤ (oddCenters n).card := by
  unfold oddCenters;
  rw [ show Finset.filter ( fun s => ¬2∣s ) ( Finset.Ioc ( n / 4 ) ( n / 3 ) ) = Finset.image ( fun k => 2 * k + 1 ) ( Finset.Ico ( ( n / 4 + 1 ) / 2 ) ( ( n / 3 + 1 ) / 2 ) ) from ?_ ];
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ; omega;
  · ext;
    constructor <;> intro h <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
    · exact ⟨ ‹_› / 2, ⟨ by omega, by omega ⟩, by omega ⟩;
    · omega

theorem main_theorem_asymptotic {n : ℕ} (hn : 48 ≤ n) (π : Play n)
    (hmax : π.IsMaximal)
    (hcr : π.IsCRespecting (oddCenters n)) :
    π.terminal.card + n / 48 ≤ n - n / 2 := by
  have h := main_theorem (by omega) π hmax hcr
  have hc := centers_card_lower' hn
  have : n / 48 ≤ (oddCenters n).card / 2 := by omega
  omega

/-! ## Non-Vacuousness -/

/-
Appending a legal move to a play gives a valid play.
-/
lemma play_append {n : ℕ} (π : Play n) (y : ℕ)
    (hy_range : y ∈ gameRange n)
    (hy_notin : y ∉ π.terminal)
    (hy_prim : ∀ a ∈ π.terminal, ¬(a ∣ y) ∧ ¬(y ∣ a)) :
    ∃ π' : Play n, π'.moves = π.moves ++ [y] ∧
      π'.terminal = insert y π.terminal ∧
      π'.moves.length = π.moves.length + 1 := by
  refine' ⟨ ⟨ π.moves ++ [ y ], _, _, _ ⟩, rfl, _, _ ⟩ <;> simp_all +decide [ Play.terminal ];
  · exact List.Nodup.append π.nodup ( List.nodup_singleton _ ) ( by aesop );
  · rintro x ( hx | rfl ) <;> [ exact π.in_range x hx; exact hy_range ];
  · intro k hk; by_cases hk' : k ≤ π.moves.length <;> simp_all +decide [ List.take_append ] ;
    · exact π.prim_prefix k hk';
    · cases hk.eq_or_lt <;> first | linarith | simp_all +decide [ List.take_of_length_le ] ;
      intro a ha b hb hab; by_cases ha' : a = y <;> by_cases hb' : b = y <;> simp_all +decide ;
      exact π.prim_prefix _ ( by linarith [ List.idxOf_lt_length_iff.mpr ha, List.idxOf_lt_length_iff.mpr hb ] ) _ ( by aesop ) _ ( by aesop ) hab


lemma isPrimitive_iff {n : ℕ} {A : Finset ℕ} :
    IsPrimitive n A ↔ A ⊆ gameRange n ∧ IsAntichainDvd A := by
  constructor
  · rintro ⟨hsub, hndvd⟩
    refine ⟨hsub, fun a ha b hb hab => ?_⟩
    by_contra hne
    exact hndvd a ha b hb hne hab
  · rintro ⟨hsub, hanti⟩
    refine ⟨hsub, fun a ha b hb hne hab => hne (hanti a ha b hb hab)⟩

lemma isMaximal_of_legalMoves_empty {n : ℕ} {p : GamePos n} {π : Play n}
    (hclaim : π.terminal = p.claimed)
    (hpool : p.pool = gameRange n \ p.claimed)
    (hemp : legalMoves p = ∅) :
    π.IsMaximal := by
  intro y hy hy_not_in
  have hypool : y ∈ p.pool := by
    rw [hpool, Finset.mem_sdiff, ← hclaim]
    exact ⟨hy, hy_not_in⟩
  have hnotleg : y ∉ legalMoves p := by simp [hemp]
  rw [mem_legalMoves, not_and] at hnotleg
  have hnotprim : ¬ IsPrimitive n (insert y p.claimed) := hnotleg hypool
  rw [isPrimitive_iff, ← hclaim, not_and] at hnotprim
  have hsub : insert y π.terminal ⊆ gameRange n := Finset.insert_subset hy π.terminal_sub
  have hnotanti : ¬ IsAntichainDvd (insert y π.terminal) := hnotprim hsub
  unfold IsAntichainDvd at hnotanti
  push Not at hnotanti
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hnotanti
  rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
  · exact absurd rfl hne
  · exact ⟨b, hb', Or.inr hab⟩
  · exact ⟨a, ha', Or.inl hab⟩
  · exact absurd (π.terminal_prim a ha' b hb' hab) hne

lemma play_step {n : ℕ} {p : GamePos n} {π : Play n} {x : ℕ}
    (hclaim : π.terminal = p.claimed)
    (hpool : p.pool = gameRange n \ p.claimed)
    (hx : x ∈ legalMoves p) :
    ∃ π' : Play n,
      π'.moves = π.moves ++ [x] ∧
      π'.terminal = (applyMove p x).claimed ∧
      (applyMove p x).pool = gameRange n \ (applyMove p x).claimed ∧
      (applyMove p x).pool.card + 1 = p.pool.card ∧
      π'.moves.length = π.moves.length + 1 := by
  have hxpool : x ∈ p.pool := (mem_legalMoves.mp hx).1
  have hxprim : IsPrimitive n (insert x p.claimed) := (mem_legalMoves.mp hx).2
  have hx_sdiff : x ∈ gameRange n \ p.claimed := hpool ▸ hxpool
  have hx_range : x ∈ gameRange n := (Finset.mem_sdiff.mp hx_sdiff).1
  have hx_notin : x ∉ π.terminal := by
    rw [hclaim]
    exact (Finset.mem_sdiff.mp hx_sdiff).2
  have hx_ndvd : ∀ a ∈ π.terminal, ¬(a ∣ x) ∧ ¬(x ∣ a) := by
    intro a ha
    have ha_cl : a ∈ p.claimed := hclaim ▸ ha
    have hne : a ≠ x := fun h => hx_notin (h ▸ ha)
    exact ⟨hxprim.2 a (Finset.mem_insert_of_mem ha_cl) x (Finset.mem_insert_self x p.claimed) hne,
      hxprim.2 x (Finset.mem_insert_self x p.claimed) a (Finset.mem_insert_of_mem ha_cl) hne.symm⟩
  obtain ⟨π', hmoves, hterm, hlen⟩ := play_append π x hx_range hx_notin hx_ndvd
  refine ⟨π', hmoves, ?_, ?_, ?_, hlen⟩
  · simp [applyMove, hterm, hclaim]
  · ext y
    simp only [applyMove, hpool, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto
  · exact Finset.card_erase_add_one hxpool

lemma crespecting_step_even {n : ℕ} {π π' : Play n} {x : ℕ}
    (hcr : π.IsCRespecting (oddCenters n))
    (heven : π.moves.length % 2 = 0)
    (hmoves : π'.moves = π.moves ++ [x]) :
    π'.IsCRespecting (oddCenters n) := by
  intro i hi hodd hex
  have hlen : π'.moves.length = π.moves.length + 1 := by simp [hmoves]
  have hilt : i < π.moves.length := by omega
  have hget : π'.moves.get ⟨i, hi⟩ = π.moves.get ⟨i, hilt⟩ := by
    simp [hmoves, List.getElem_append_left hilt]
  have hpref : π'.prefixAt i = π.prefixAt i := by
    simp [Play.prefixAt, hmoves, List.take_append_of_le_length (le_of_lt hilt)]
  rw [hget]
  rw [hpref] at hex
  exact hcr i hilt hodd hex

lemma crespecting_step_odd_mem {n : ℕ} {π π' : Play n} {s : ℕ}
    (hcr : π.IsCRespecting (oddCenters n))
    (hsC : s ∈ oddCenters n)
    (hmoves : π'.moves = π.moves ++ [s]) :
    π'.IsCRespecting (oddCenters n) := by
  intro i hi hodd hex
  have hlen : π'.moves.length = π.moves.length + 1 := by simp [hmoves]
  by_cases hilt : i < π.moves.length
  · have hget : π'.moves.get ⟨i, hi⟩ = π.moves.get ⟨i, hilt⟩ := by
      simp [hmoves, List.getElem_append_left hilt]
    have hpref : π'.prefixAt i = π.prefixAt i := by
      simp [Play.prefixAt, hmoves, List.take_append_of_le_length (le_of_lt hilt)]
    rw [hget]
    rw [hpref] at hex
    exact hcr i hilt hodd hex
  · have hieq : i = π.moves.length := by omega
    have hget : π'.moves.get ⟨i, hi⟩ = s := by
      simp [hmoves, hieq]
    rwa [hget]

lemma crespecting_step_odd_none {n : ℕ} {p : GamePos n} {π π' : Play n} {x : ℕ}
    (hcr : π.IsCRespecting (oddCenters n))
    (hclaim : π.terminal = p.claimed)
    (hpool : p.pool = gameRange n \ p.claimed)
    (hnoC : ∀ s ∈ oddCenters n, s ∉ legalMoves p)
    (hmoves : π'.moves = π.moves ++ [x]) :
    π'.IsCRespecting (oddCenters n) := by
  intro i hi hodd hex
  have hlen : π'.moves.length = π.moves.length + 1 := by simp [hmoves]
  by_cases hilt : i < π.moves.length
  · have hget : π'.moves.get ⟨i, hi⟩ = π.moves.get ⟨i, hilt⟩ := by
      simp [hmoves, List.getElem_append_left hilt]
    have hpref : π'.prefixAt i = π.prefixAt i := by
      simp [Play.prefixAt, hmoves, List.take_append_of_le_length (le_of_lt hilt)]
    rw [hget]
    rw [hpref] at hex
    exact hcr i hilt hodd hex
  · have hieq : i = π.moves.length := by omega
    have hpref : π'.prefixAt i = p.claimed := by
      simp [Play.prefixAt, hmoves, hieq, ← hclaim, Play.terminal]
    rw [hpref] at hex
    obtain ⟨s, hsC, hs_range, hs_notin, hs_anti⟩ := hex
    have hsub : insert s p.claimed ⊆ gameRange n := by
      rw [← hclaim]
      exact Finset.insert_subset hs_range π.terminal_sub
    have hs_leg : s ∈ legalMoves p := by
      rw [mem_legalMoves, hpool, Finset.mem_sdiff, isPrimitive_iff]
      exact ⟨⟨hs_range, hs_notin⟩, hsub, hs_anti⟩
    exact absurd hs_leg (hnoC s hsC)

lemma exists_crespecting_ge_gameValueAux {n : ℕ} (fuel : ℕ) (turn : Bool) (p : GamePos n) (π : Play n)
    (hclaim : π.terminal = p.claimed)
    (hpool : p.pool = gameRange n \ p.claimed)
    (hfuel : p.pool.card ≤ fuel)
    (hcr : π.IsCRespecting (oddCenters n))
    (hturn : π.moves.length % 2 = if turn then 0 else 1) :
    ∃ π_star : Play n, π_star.IsMaximal ∧ π_star.IsCRespecting (oddCenters n) ∧
      gameValueAux fuel turn p ≤ π_star.terminal.card := by
  classical
  induction fuel generalizing turn p π with
  | zero =>
    have hpool_empty : p.pool = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hfuel)
    have hemp : legalMoves p = ∅ := by
      rw [← Finset.subset_empty]
      exact le_trans (Finset.filter_subset _ _) (by simp [hpool_empty])
    refine ⟨π, isMaximal_of_legalMoves_empty hclaim hpool hemp, hcr, ?_⟩
    simp [gameValueAux, hclaim]
  | succ fuel ih =>
    simp only [gameValueAux]
    split_ifs with h ht
    · subst ht
      let f := fun x => gameValueAux fuel (!true) (applyMove p x)
      have hmem : ((legalMoves p).image f).max' (h.image f) ∈ (legalMoves p).image f :=
        Finset.max'_mem _ _
      obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hmem
      obtain ⟨π', hmoves, hclaim', hpool', hcard', hlen'⟩ := play_step hclaim hpool hx
      have hcr' : π'.IsCRespecting (oddCenters n) :=
        crespecting_step_even hcr (by simpa using hturn) hmoves
      have hturn' : π'.moves.length % 2 = if false then 0 else 1 := by
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [↓reduceIte] at hturn
        omega
      obtain ⟨π_star, hmax_star, hcr_star, hle_star⟩ :=
        ih false (applyMove p x) π' hclaim' hpool' (by omega) hcr' hturn'
      refine ⟨π_star, hmax_star, hcr_star, ?_⟩
      rw [← hfx]
      exact hle_star
    · have htf : turn = false := by cases turn <;> simp_all
      subst htf
      let f := fun x => gameValueAux fuel (!false) (applyMove p x)
      by_cases hC : ∃ s ∈ oddCenters n, s ∈ legalMoves p
      · obtain ⟨s, hsC, hsleg⟩ := hC
        obtain ⟨π', hmoves, hclaim', hpool', hcard', hlen'⟩ := play_step hclaim hpool hsleg
        have hcr' : π'.IsCRespecting (oddCenters n) :=
          crespecting_step_odd_mem hcr hsC hmoves
        have hturn' : π'.moves.length % 2 = if true then 0 else 1 := by
          simp only [↓reduceIte]
          simp only [Bool.false_eq_true, ↓reduceIte] at hturn
          omega
        obtain ⟨π_star, hmax_star, hcr_star, hle_star⟩ :=
          ih true (applyMove p s) π' hclaim' hpool' (by omega) hcr' hturn'
        have hmin : ((legalMoves p).image f).min' (h.image f) ≤ f s :=
          Finset.min'_le _ _ (Finset.mem_image_of_mem f hsleg)
        exact ⟨π_star, hmax_star, hcr_star, le_trans hmin hle_star⟩
      · push Not at hC
        obtain ⟨x, hx⟩ := h
        obtain ⟨π', hmoves, hclaim', hpool', hcard', hlen'⟩ := play_step hclaim hpool hx
        have hcr' : π'.IsCRespecting (oddCenters n) :=
          crespecting_step_odd_none hcr hclaim hpool hC hmoves
        have hturn' : π'.moves.length % 2 = if true then 0 else 1 := by
          simp only [↓reduceIte]
          simp only [Bool.false_eq_true, ↓reduceIte] at hturn
          omega
        obtain ⟨π_star, hmax_star, hcr_star, hle_star⟩ :=
          ih true (applyMove p x) π' hclaim' hpool' (by omega) hcr' hturn'
        have hmin : ((legalMoves p).image f).min' (Finset.Nonempty.image ⟨x, hx⟩ f) ≤ f x :=
          Finset.min'_le _ _ (Finset.mem_image_of_mem f hx)
        exact ⟨π_star, hmax_star, hcr_star, le_trans hmin hle_star⟩
    · have hemp : legalMoves p = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      refine ⟨π, isMaximal_of_legalMoves_empty hclaim hpool hemp, hcr, ?_⟩
      simp [hclaim]

def emptyPlay (n : ℕ) : Play n where
  moves := []
  nodup := List.nodup_nil
  in_range := by simp
  prim_prefix := by intro k _; simp [IsAntichainDvd]

lemma L_upper_bound {n : ℕ} (hn : 48 ≤ n) :
    L n + n / 48 ≤ n - n / 2 := by
  have hclaim : (emptyPlay n).terminal = (startPos n).claimed := by
    simp [emptyPlay, Play.terminal, startPos]
  have hpool : (startPos n).pool = gameRange n \ (startPos n).claimed := by
    simp [startPos, gameRange]
  have hcr : (emptyPlay n).IsCRespecting (oddCenters n) := by
    intro i hi
    simp [emptyPlay] at hi
  obtain ⟨π_star, hmax, hcr_star, hle⟩ :=
    exists_crespecting_ge_gameValueAux (startPos n).pool.card true (startPos n) (emptyPlay n)
      hclaim hpool le_rfl hcr (by simp [emptyPlay])
  have hmain := main_theorem_asymptotic hn π_star hmax hcr_star
  unfold L gameLength
  omega

theorem not_erdos_872_parts_ii :
    ¬ (∀ ε > (0 : ℝ), ∀ᶠ n in Filter.atTop, (L n : ℝ) ≥ (1 - ε) * n / 2) := by
  intro hall
  have hev := hall (1 / 48 : ℝ) (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let n := 48 * (N + 1)
  have hn_ge_N : N ≤ n := by omega
  have hn_ge_48 : 48 ≤ n := by omega
  have hL_nat : L n ≤ 23 * (N + 1) := by
    have hbound := L_upper_bound hn_ge_48
    omega
  have hL_real : (L n : ℝ) ≤ 23 * ((N : ℝ) + 1) := by exact_mod_cast hL_nat
  have hlow := hN n hn_ge_N
  have hn_real : (n : ℝ) = 48 * ((N : ℝ) + 1) := by exact_mod_cast rfl
  rw [hn_real] at hlow
  linarith




/- ## Erdős Problem 872

The problem asks for asymptotic lower bounds on `L(n)`. Two specific targets are stated. -/

/-- Erdős Problem 872, part (i) (weak form): there exists a constant $\epsilon > 0$ such that the
game length is at least $\epsilon \cdot n$ for all sufficiently large $n$. -/
@[category research open, AMS 5 11 91]
theorem erdos_872.parts.i : answer(sorry) ↔
    ∃ ε > (0 : ℝ), ∀ᶠ n in atTop, (L n : ℝ) ≥ ε * n := by
  sorry

/-- Erdős Problem 872, part (ii) (strong form): for every $\epsilon > 0$, the game length is at
least $(1-\epsilon) \cdot n / 2$ for all sufficiently large $n$.

Status note: the forum thread (April-May 2026) records Shortener strategies giving
$L(n) \leq (23/48 + o(1)) \cdot n$ (described in the thread as accepted as correct, with a Lean
formalization in progress) and a claimed $L(n) \leq 0.19 \cdot n$, either of which would answer this
question negatively under the Prolonger-first convention. Neither is published, so the statement
is recorded here as the original Erdős question. -/
@[category research solved, AMS 5 11 91]
theorem erdos_872.parts.ii : answer(False) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, (L n : ℝ) ≥ (1 - ε) * n / 2 := by
  simp only [false_iff]
  exact not_erdos_872_parts_ii

/-- A trivial upper bound: a play can claim at most the $n - 1$ elements of $\{2, \dots, n\}$, so
$L(n) \leq n - 1$. -/
@[category textbook, AMS 5 11 91]
theorem erdos_872.trivial_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    L n ≤ n - 1 := by
  calc L n ≤ (startPos n).claimed.card + (startPos n).pool.card :=
        gameValueAux_le (startPos n).pool.card true (startPos n)
    _ = n - 1 := by
        simp only [startPos, Finset.card_empty, Nat.card_Icc]
        omega

/-- Forum-related variant: how small can a maximal primitive subset of $\{2, \dots, n\}$ be?
The set of primes in $\{2, \dots, n\}$ is a maximal primitive subset of size $\pi(n)$, and the forum
thread asks whether this is the smallest possible for all $n \geq 2$. Equivalently: must every
completed play of the saturation game, by both players and regardless of strategy, claim at least
$\pi(n)$ elements? (Terminal positions of the game are exactly the maximal primitive subsets.) -/
@[category research open, AMS 5 11 91]
theorem erdos_872.variants.prime_question : answer(sorry) ↔
    ∀ n ≥ 2, ∀ A : Finset ℕ, Maximal (IsPrimitive n) A →
      ((Finset.Icc 2 n).filter Nat.Prime).card ≤ A.card := by
  sorry

end

end Erdos872
