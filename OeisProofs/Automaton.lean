import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! Finite Laurent polynomials encode the triangular odd-neighbour rule over F₂. -/
namespace Triangular
open AddMonoidAlgebra
noncomputable section
abbrev Point := ℤ × ℤ
abbrev Pattern := AddMonoidAlgebra (ZMod 2) Point

private instance : CharP Pattern 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by
  change single (0 : Point) ((2:ℕ) : ZMod 2) = (0 : Pattern)
  rw [show ((2:ℕ) : ZMod 2) = 0 by decide]
  simp)

def mon (i j : ℤ) : Pattern := single (i,j) 1
def weight (p : Pattern) : ℕ := p.coeff.support.card

private def affine (d i j : ℤ) (hd : 0 < d) : Point ↪ Point where
  toFun z := (i+d*z.1, j+d*z.2)
  inj' := by
    rintro ⟨a,b⟩ ⟨c,e⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    constructor <;> nlinarith [h.1,h.2]

private theorem mono_square (i j : ℤ) (p : Pattern) :
    mon i j * p^2 = mapDomain (affine 2 i j (by decide)) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_pow_char, mul_add, ha, hb, mapDomain_add]
  | single z r =>
    obtain ⟨a,b⟩ := z
    have hr : r * r = r := by revert r; decide
    simp [mon, pow_two, single_mul_single, affine, hr, Prod.mk_add_mk, two_mul]

private theorem mono_translate (i j : ℤ) (p : Pattern) :
    mon i j * p = mapDomain (affine 1 i j (by decide)) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [mul_add, ha, hb, mapDomain_add]
  | single z r => rcases z with ⟨a,b⟩; simp [mon, affine, single_mul_single]

private theorem weight_map (e : Point ↪ Point) (p : Pattern) :
    weight (mapDomain e p) = weight p := by
  simp [weight, mapDomain]

private theorem wt_shift (i j : ℤ) (p : Pattern) : weight (mon i j * p) = weight p := by
  rw [mono_translate, weight_map]

private theorem m00 : mon 0 0 = 1 := rfl

private theorem wt_sq (p : Pattern) : weight (p^2) = weight p := by
  have h := mono_square 0 0 p
  rw [m00, one_mul] at h
  rw [h, weight_map]

private def pack (a b c d : Pattern) : Pattern :=
  mon 0 0*a^2 + mon 1 0*b^2 + mon 0 1*c^2 + mon 1 1*d^2

private theorem support_copy (i j : ℤ) (p : Pattern) :
    (mon i j * p^2).coeff.support = p.coeff.support.map (affine 2 i j (by decide)) := by
  rw [mono_square]
  simp [mapDomain]

private theorem separated {i j k l : ℤ} (h : i%2 ≠ k%2 ∨ j%2 ≠ l%2) (a b : Pattern) :
    Disjoint (mon i j*a^2).coeff.support (mon k l*b^2).coeff.support := by
  rw [support_copy, support_copy, Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨⟨r,s⟩, _, rfl⟩ := Finset.mem_map.mp hz1
  obtain ⟨⟨u,v⟩, _, he⟩ := Finset.mem_map.mp hz2
  change (k+2*u,l+2*v) = (i+2*r,j+2*s) at he
  obtain ⟨hx,hy⟩ := Prod.mk.inj he
  omega

private theorem weight_pack (a b c d : Pattern) :
    weight (pack a b c d) = weight a + weight b + weight c + weight d := by
  classical
  have ab := separated (i:=0) (j:=0) (k:=1) (l:=0) (by decide) a b
  have ac := separated (i:=0) (j:=0) (k:=0) (l:=1) (by decide) a c
  have ad := separated (i:=0) (j:=0) (k:=1) (l:=1) (by decide) a d
  have bc := separated (i:=1) (j:=0) (k:=0) (l:=1) (by decide) b c
  have bd := separated (i:=1) (j:=0) (k:=1) (l:=1) (by decide) b d
  have cd := separated (i:=0) (j:=1) (k:=1) (l:=1) (by decide) c d
  simp only [weight, pack, coeff_add]
  have abc := Finset.disjoint_union_left.mpr ⟨ac,bc⟩
  have abd := Finset.disjoint_union_left.mpr ⟨ad,bd⟩
  have abcd := Finset.disjoint_union_left.mpr ⟨abd,cd⟩
  have h2 := Finsupp.support_add_eq ab
  have h3 := Finsupp.support_add_eq (h2.symm ▸ abc)
  have h4 := Finsupp.support_add_eq (h3.symm ▸ (h2.symm ▸ abcd))
  rw [h4,h3,h2, Finset.card_union_of_disjoint abcd, Finset.card_union_of_disjoint abc,
    Finset.card_union_of_disjoint ab]
  simp only [support_copy, Finset.card_map]

def F : Pattern := mon 0 0 + mon 1 0 + mon 0 1
def G : Pattern := mon 0 0 + mon (-1) 0 + mon 0 (-1)
def H : Pattern := F*G
private def edge (i j : ℤ) : Pattern := mon 0 0 + mon i j

private lemma mon_mul (i j k l : ℤ) : mon i j * mon k l = mon (i+k) (j+l) := by
  simp [mon, single_mul_single]
private lemma mon_sq (i j : ℤ) : (mon i j)^2 = mon (i+i) (j+j) := by rw [pow_two, mon_mul]
private lemma one_mon : (1:Pattern) = mon 0 0 := rfl

/-- Multiplying by a square applies the same stencil inside each parity class. -/
private lemma pack_mul (a b c d p : Pattern) :
    pack a b c d * p^2 = pack (a*p) (b*p) (c*p) (d*p) := by
  unfold pack
  ring

private lemma four_zero : (4:Pattern) = 0 := by
  calc (4:Pattern) = 2+2 := by norm_num
       _ = 0 := CharTwo.add_self_eq_zero _

/-- Normalize a concrete finite stencil. All cancellations take place in characteristic two. -/
local macro "stencil" : tactic => `(tactic|
  (simp only [H,F,G,edge,pack,add_pow_char,mul_pow,mon_sq,mul_add,add_mul,
     zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,add_zero,zero_add,one_mon,mon_mul]
   all_goals norm_num1 <;> abel_nf <;>
     simp [succ_nsmul, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero, four_zero] <;> try ac_rfl))

private lemma wt_zero : weight 0 = 0 := by simp [weight]

private lemma count_F (p : Pattern) :
    weight (F * p^2) = 3 * weight p := by
  have h : F = pack 1 1 1 0 := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [one_mul,zero_mul,wt_zero]
  omega

private lemma count_G (p : Pattern) :
    weight (G * p^2) = 3 * weight p := by
  have h : G = pack 1 (mon (-1) 0) (mon 0 (-1)) 0 := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [one_mul,zero_mul,wt_shift,wt_zero]
  omega

private lemma count_H (p : Pattern) :
    weight (H * p^2) = weight p + weight (edge 1 0 * p) + weight (edge 0 1 * p) + weight (edge 1 (-1) * p) := by
  have h : H = pack 1 (mon (-1) 0 * edge 1 0) (mon 0 (-1) * edge 0 1) (mon (-1) 0 * edge 1 (-1)) := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [one_mul,mul_assoc,wt_shift]

private lemma count_e0 (p : Pattern) :
    weight ((edge 1 0) * p^2) = 2 * weight p := by
  have h : (edge 1 0) = pack 1 1 0 0 := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [one_mul,zero_mul,wt_zero]
  omega

private lemma count_h0 (p : Pattern) :
    weight ((edge 1 0 * H) * p^2) = 2 * weight p + 2 * weight (edge 1 0 * p) := by
  have h : (edge 1 0 * H) = pack (mon 1 0) (mon (-1) 0) (mon 0 (-1) * edge 1 0) (mon (-1) 0 * edge 1 0) := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [mul_assoc,wt_shift]
  omega

private lemma count_e1 (p : Pattern) :
    weight ((edge 0 1) * p^2) = 2 * weight p := by
  have h : (edge 0 1) = pack 1 0 1 0 := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [one_mul,zero_mul,wt_zero]
  omega

private lemma count_h1 (p : Pattern) :
    weight ((edge 0 1 * H) * p^2) = 2 * weight p + 2 * weight (edge 0 1 * p) := by
  have h : (edge 0 1 * H) = pack (mon 0 1) (mon (-1) 0 * edge 0 1) (mon 0 (-1)) (mon 0 (-1) * edge 0 1) := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [mul_assoc,wt_shift]
  omega

private lemma count_e2 (p : Pattern) :
    weight ((edge 1 (-1)) * p^2) = 2 * weight p := by
  have h : (edge 1 (-1)) = pack 1 0 0 (mon 0 (-1)) := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [one_mul,zero_mul,wt_shift,wt_zero]
  omega

private lemma count_h2 (p : Pattern) :
    weight ((edge 1 (-1) * H) * p^2) = 2 * weight p + 2 * weight (edge 1 (-1) * p) := by
  have h : (edge 1 (-1) * H) = pack (mon 1 (-1)) (mon (-1) 0 * edge 1 (-1)) (edge 1 (-1)) (mon (-1) 0) := by stencil
  rw [h,pack_mul,weight_pack]
  simp only [mul_assoc,wt_shift]
  omega


/-- The single lit triangle at time zero, followed by the alternating three-neighbour steps. -/
def generation : ℕ → Pattern
  | 0 => 1
  | n+1 => (if n%2=0 then F else G) * generation n

def population (n : ℕ) : ℕ := weight (generation n)

theorem forward_rule (p : Pattern) (i j : ℤ) :
    (F*p).coeff (i,j) = p.coeff (i,j) + p.coeff (i-1,j) + p.coeff (i,j-1) := by
  simp [F,mon, add_mul, Prod.mk_add_mk, sub_eq_add_neg, add_comm]

theorem backward_rule (p : Pattern) (i j : ℤ) :
    (G*p).coeff (i,j) = p.coeff (i,j) + p.coeff (i+1,j) + p.coeff (i,j+1) := by
  simp [G,mon, add_mul, Prod.mk_add_mk, add_comm]

private lemma even_gen (s : ℕ) : generation (2*s) = H^s := by
  induction s with
  | zero => simp [generation]
  | succ s ih =>
    rw [Nat.mul_succ, generation, generation, ih]
    simp [H,pow_succ]
    ring

private lemma odd_gen (s : ℕ) : generation (2*s+1) = F * H^s := by
  rw [generation, even_gen]
  simp

private def b (s : ℕ) := weight (H^s)
private def c (s : ℕ) := weight (edge 1 0*H^s) + weight (edge 0 1*H^s) + weight (edge 1 (-1)*H^s)

private lemma twice (s : ℕ) : H^(2*s) = (H^s)^2 := by rw [Nat.mul_comm, pow_mul]
private lemma twice_one (s : ℕ) : H^(2*s+1) = H*(H^s)^2 := by rw [pow_succ, twice, mul_comm]
private lemma b_even (s : ℕ) : b (2*s) = b s := by simp only [b,twice,wt_sq]
private lemma b_odd (s : ℕ) : b (2*s+1) = b s + c s := by
  simp only [b,c,twice_one,count_H]; omega
private lemma c_even (s : ℕ) : c (2*s) = 6*b s := by
  simp only [c,b,twice,count_e0,count_e1,count_e2]; omega
private lemma c_odd (s : ℕ) : c (2*s+1) = 6*b s + 2*c s := by
  simp only [c,b,twice_one,← mul_assoc,count_h0,count_h1,count_h2]; omega

private lemma even_pop (s : ℕ) : population (2*s) = b s := by simp [population,even_gen,b]

theorem odd_population (t : ℕ) : population (2*t+1) = 3*population t := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · obtain ⟨s,rfl⟩ : ∃ s, t=2*s := ⟨t/2,by omega⟩
    simp only [population, odd_gen, even_gen, twice, count_F]
  · obtain ⟨s,rfl⟩ : ∃ s, t=2*s+1 := ⟨t/2,by omega⟩
    simp only [population, odd_gen,twice_one]
    rw [show F*(H*(H^s)^2) = G*(F*H^s)^2 by unfold H; ring, count_G]

theorem four_population (t : ℕ) : population (4*t) = population (2*t) := by
  rw [show 4*t=2*(2*t) by omega, even_pop, even_pop, b_even]

theorem eight_two_population (t : ℕ) :
    population (8*t+2) = 3*population (4*t) + 4*population (2*t) := by
  rw [show 8*t+2=2*(2*(2*t)+1) by omega, even_pop, four_population, even_pop,
    b_odd, b_even,c_even]
  omega

theorem eight_six_population (t : ℕ) :
    population (8*t+6) = 3*population (4*t+2) + 4*population (2*t) := by
  rw [show 8*t+6=2*(2*(2*t+1)+1) by omega, show 4*t+2=2*(2*t+1) by omega,
    even_pop, even_pop, even_pop, b_odd, b_odd, c_odd]
  omega

end
end Triangular
