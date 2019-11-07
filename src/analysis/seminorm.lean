import analysis.normed_space.basic
import analysis.convex

/-- A seminorm on a vector space over a normed field is a nonnegative
function that is subadditive and homogenous. -/
structure seminorm (𝕜 : Type*) [normed_field 𝕜]
(E : Type*) [add_comm_group E] [module 𝕜 E] :=
(to_fun : E → ℝ)
(triangle : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)
(smul : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)

variables (𝕜 : Type*) [normed_field 𝕜]
variables {E : Type*} [add_comm_group E] [module 𝕜 E]

-- is this sensible notation? how strongly should this bind? should it
-- be a `localized infixr` or something else instead?
local notation a ` •'' `:74 S:75 := (λ x, a • x) '' S

-- Definitions of balanced / absorbing / absorbent sets.

-- (These make sense on any vector space over a normed field, and
-- perhaps belong instead in another file?)

/-- A set S is balanced if a • S ⊆ S for all ∥a∥ < 1. -/
def balanced (S : set E) :=
∀ a : 𝕜, ∥a∥ ≤ 1 → a •'' S ⊆ S

lemma subset_of_norm_le_of_balanced {S : set E} (hS : balanced 𝕜 S)
  {t s : 𝕜} (hle : ∥t∥ ≤ ∥s∥) : t •'' S ⊆ s •'' S :=
or.elim (classical.em (s = 0))
(λ heq tx htx,
have htz : t = 0,
  from (norm_le_zero_iff _).1 $ by rwa [heq, norm_zero] at hle,
by { rw htz at htx; rwa heq })
(λ hne tx ⟨x, hxs, htx⟩, ⟨s⁻¹ • t • x,
have hst : ∥s⁻¹ * t∥ ≤ 1, from begin
  rw [normed_field.norm_mul, normed_field.norm_inv, ←div_eq_inv_mul],
  exact div_le_of_le_mul ((norm_pos_iff _).2 hne) (by rwa mul_one),
end,
by { rw smul_smul; exact hS _ hst ⟨_, hxs, rfl⟩ },
show s • s⁻¹ • t • x = tx,
  by { rwa [←htx, smul_smul, mul_inv_cancel, one_smul] }⟩)
 
/-- A set A absorbs another set B if A can be 'inflated' so that it
contains B. -/
def absorbs (A : set E) (B : set E) :=
∃ r, ∀ t : 𝕜, r < ∥t∥ → B ⊆ t •'' A

lemma absorbs_singleton_iff (A : set E) (x : E):
absorbs 𝕜 A {x} ↔ ∃ r, ∀ t : 𝕜, r < ∥t∥ → x ∈ t •'' A :=
⟨λ ⟨r, hr⟩, begin

end, _⟩


/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) :=
∀ x : E, ∃ r, ∀ t : 𝕜, r < ∥t∥ → x ∈ t •'' A

/-- For a balanced set A to absorb another set B, it suffices for some
inflation of A to contain B. -/
lemma absorbs_of_balanced
{A : set E} (hA : balanced 𝕜 A) (B : set E)
(h : ∃ t : 𝕜, B ⊆ t •'' A) : absorbs 𝕜 A B :=
let ⟨t, ht⟩ := h in
⟨∥t∥, λ s hs, set.subset.trans ht
(subset_of_norm_le_of_balanced _ hA (le_of_lt hs))⟩

namespace seminorm

variables {𝕜 E} (p : seminorm 𝕜 E)

instance : has_coe_to_fun (seminorm 𝕜 E) := ⟨_, λ p, p.to_fun⟩

lemma smul' (a : 𝕜) (x : E) : p (a • x) = ∥a∥ * p x :=
p.smul _ _

@[simp] lemma zero {x : E} (h : x = 0) : p x = 0 :=
have l : _, from p.smul 0 0,
by { rw h; rwa [zero_smul, norm_zero, zero_mul] at l }

@[simp] lemma neg (x : E) : p x = p (-x) :=
eq.symm (calc p (-x)
    = p ((-1 : 𝕜) • x) : by rw neg_one_smul 𝕜 x
... = ∥(-1 : 𝕜)∥ * p x : p.smul _ _
... = p x : by rw [norm_neg, normed_field.norm_one, one_mul])

/-- Seminorms are symmetric. -/
lemma symm (x y : E) : p (x - y) = p (y - x) :=
by rw [←neg_sub, ←neg]

lemma reverse_triangle' (x y : E) : p x - p y ≤ p (x - y) :=
sub_le_iff_le_add.2 (calc _
    = p (y +(x - y)) : by rw [add_comm, sub_add_cancel]
... ≤ _ : by { rw [add_comm _ (p y)]; exact p.triangle _ _ })

lemma reverse_triangle (x y : E) : abs (p x - p y) ≤ p (x - y) :=
abs_le_of_le_of_neg_le (reverse_triangle' _ _ _)
(by { rw [neg_sub, symm]; exact reverse_triangle' _ _ _})

/-- Seminorms are non-negative. -/
lemma nonneg (x : E) : 0 ≤ p x :=
have l : _, from reverse_triangle p x 0,
by { rw [sub_zero] at l; exact le_trans (abs_nonneg _) l }

/-- The r-ball centred at x: the set of elements such that
p (y - x) < r. -/
def ball (x : E) (r : ℝ) : set E := { y | p (y - x) < r }

-- some of these results are nearly identical to their corresponding
-- statements for metric spaces. Can this be better with code reuse?

lemma mem_ball (x : E) (y : E) (r : ℝ): y ∈ ball p x r ↔ p (y - x) < r :=
iff.rfl

lemma mem_ball' (x : E) (y : E) (r : ℝ): y ∈ ball p x r ↔ p (x - y) < r :=
symm p y x ▸ iff.rfl

lemma mem_ball_zero (x : E) (r : ℝ) : x ∈ ball p 0 r ↔ p x < r :=
by rw [mem_ball, sub_zero]

/-- Balls at the origin are balanced. -/
lemma balanced_ball (r : ℝ) : balanced 𝕜 (ball p 0 r) :=
λ a ha y ⟨x, hx, hax⟩, by { rw [mem_ball_zero, ←hax, smul'];
  exact lt_of_le_of_lt (mul_le_of_le_one_left (nonneg _ _) ha)
  (by rwa ←mem_ball_zero) }

/-- Balls at the origin are absorbent. -/
lemma absorbent_ball (r : ℝ) : absorbent 𝕜 (ball p 0 r) :=
sorry

-- These statements depend on convex.lean, where the definition of
-- `convex` depends on ℝ.

variables {V : Type*} [add_comm_group V] [vector_space ℝ V]
variable  (d : seminorm ℝ V)

/-- The seminorm ball at the origin is convex. -/
lemma convex_ball (r : ℝ) : convex (ball d 0 r) :=
(convex_iff _).2 $ λ x y θ hx hy hleθ hθle,
have 0 ≤ 1 - θ, by rwa ←sub_nonneg at hθle,
by { rw mem_ball_zero;
calc _ ≤ d (θ • x) + d ((1 - θ) • y) : d.triangle _ _
...    = θ * d x + (1 - θ) * d y : by rwa [
  smul', real.norm_eq_abs, abs_of_nonneg hleθ,
  smul', real.norm_eq_abs, abs_of_nonneg]
...    < θ * r + (1 - θ) * r : or.elim (lt_or_eq_of_le hleθ)
  (λ hlt, add_lt_add_of_lt_of_le
    ((mul_lt_mul_left hlt).2 (by rwa mem_ball_zero at hx))
    (mul_le_mul_of_nonneg_left (le_of_lt (by rwa mem_ball_zero at hy)) this))
  (λ heq, by { rw ←heq; rw mem_ball_zero at hy;
    simpa only [zero_mul, zero_add, sub_zero, one_mul] })
...    = r : by rw [sub_mul, one_mul, add_sub, add_sub_cancel'] }

end seminorm

section minkowski_functional

open seminorm

/-- The Minkowski functional of a set. -/
noncomputable def minkowski_functional (A : set E) (x : E) :=
real.Inf $ (λ t : 𝕜, ∥t∥) '' { t | x ∈ t •'' A }

local notation `μ_` := minkowski_functional

/-- A seminorm is the Minkowski functional of its unit ball at the
origin. -/
example (p : seminorm 𝕜 E) (x : E) : μ_ 𝕜 (ball p 0 1) x = p x := _

end minkowski_functional
