import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A strip is a permutation with displacement at most one. Its target list is
the second-row partner of each first-row cell, in left-to-right order. -/
namespace Domicule
open List
def Near (x y : ℕ) := x ≤ y+1 ∧ y ≤ x+1
def StripOK (s n : ℕ) (ys : List ℕ) :=
  ys.Perm (range' s n) ∧ Forall₂ Near (range' s n) ys

inductive Block | vertical | crossed deriving DecidableEq, Repr
abbrev Word := List Block

def width : Word → ℕ
  | [] => 0
  | .vertical::xs => 1 + width xs
  | .crossed::xs => 2 + width xs

def straights : Word → ℕ
  | [] => 0
  | .vertical::xs => 1 + straights xs
  | .crossed::xs => straights xs

def partners (s : ℕ) : Word → List ℕ
  | [] => []
  | .vertical::xs => s :: partners (s+1) xs
  | .crossed::xs => (s+1)::s::partners (s+2) xs

private lemma lower_of_near {s n x : ℕ} {ys : List ℕ}
    (h : Forall₂ Near (range' s n) ys) (hx : x ∈ ys) : s ≤ x+1 := by
  induction n generalizing s ys with
  | zero => simp_all
  | succ n ih =>
    rw [range'_succ] at h
    cases h with
    | cons h hs =>
      rcases List.mem_cons.mp hx with rfl | ht
      · exact h.1
      · have := ih hs ht; omega

theorem strip_decode {s n : ℕ} {ys : List ℕ} (h : StripOK s n ys) :
    ∃ w, width w=n ∧ partners s w=ys := by
  induction n using Nat.strong_induction_on generalizing s ys with
  | ind n ih =>
    obtain ⟨hp,hn⟩ := h
    cases n with
    | zero =>
      have : ys=[] := List.length_eq_zero_iff.mp (by simpa using hp.length_eq)
      exact ⟨[],rfl,this.symm⟩
    | succ k =>
      rw [range'_succ] at hp hn
      cases hn with
      | cons head tail =>
        rename_i y rest
        have memy := hp.mem_iff.mp (List.mem_cons_self (a:=y) (l:=rest))
        have low : s ≤ y := by
          rcases List.mem_cons.mp memy with rfl | hm
          · omega
          · have := (List.mem_range'_1.mp hm).1; omega
        by_cases hy : y=s
        · subst y
          obtain ⟨w,hw,hr⟩ := ih k (by omega) (s:=s+1) ⟨List.Perm.cons_inv hp,tail⟩
          exact ⟨.vertical::w,by simp [width,hw,Nat.add_comm],by simp [partners,hr]⟩
        · have ey : y=s+1 := by obtain ⟨_, hh⟩ := head; omega
          subst y
          cases k with
          | zero => simp_all
          | succ j =>
            rw [range'_succ] at tail hp
            cases tail with
            | cons nextNear tail2 =>
              rename_i z zs
              have hs := hp.mem_iff.mpr (List.mem_cons_self (a:=s))
              have hz : z=s := by
                simp only [List.mem_cons] at hs
                rcases hs with hh | hh | hh
                · omega
                · exact hh.symm
                · have := lower_of_near tail2 hh; omega
              subst z
              have hp' := (List.Perm.swap _ _ _).trans hp
              have hp'' := List.Perm.cons_inv (List.Perm.cons_inv hp')
              obtain ⟨w,hw,hr⟩ := ih j (by omega) (s:=s+2) ⟨hp'',tail2⟩
              exact ⟨.crossed::w,by simp [width,hw]; omega,by simp [partners,hr]⟩

theorem strip_encode (s : ℕ) (w : Word) : StripOK s (width w) (partners s w) := by
  induction w generalizing s with
  | nil => simp [StripOK,width,partners]
  | cons x xs ih =>
    cases x with
    | vertical =>
      obtain ⟨hp,hn⟩ := ih (s+1)
      simp only [width,partners, Nat.add_comm 1 (width xs)]
      exact ⟨hp.cons _,.cons (by constructor <;> omega) hn⟩
    | crossed =>
      obtain ⟨hp,hn⟩ := ih (s+2)
      change StripOK s (2+width xs) ((s+1)::s::partners (s+2) xs)
      rw [show 2+width xs=width xs+1+1 by omega]
      unfold StripOK
      rw [range'_succ,range'_succ]
      exact ⟨(List.Perm.swap _ _ _).trans ((hp.cons _).cons _),
        .cons (by constructor <;> omega) (.cons (by constructor <;> omega) hn)⟩

theorem partners_injective (s : ℕ) : Function.Injective (partners s) := by
  intro x
  induction x generalizing s with
  | nil => rintro (_|⟨_|_,_⟩) h <;> simp_all [partners]
  | cons a xs ih =>
    rintro (_|⟨b,bs⟩) h
    · cases a <;> simp [partners] at h
    · cases a <;> cases b <;> simp_all [partners] <;> exact ih _ h


/-- Count equal-column edges between the two lists of cell columns. -/
def fixed : List ℕ → List ℕ → ℕ
  | a::as', b::bs => (if a=b then 1 else 0) + fixed as' bs
  | _, _ => 0

theorem fixed_partners (s : ℕ) (w : Word) :
    fixed (range' s (width w)) (partners s w) = straights w := by
  induction w generalizing s with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | vertical =>
      simp [width,partners,straights,Nat.add_comm 1 (width xs),range'_succ,fixed,ih]
    | crossed =>
      simp [width,partners,straights,show 2+width xs = width xs+1+1 by omega,range'_succ,fixed,ih]

/-- Oriented matching with no horizontal pieces. Seam i lists edges from row 2i
to row 2i-1, recording the source and destination columns. In band i, remaining
source columns are visited in increasing order; targets is their partner list. -/
@[ext] structure Frame (n : ℕ) where
  seam : ℕ → List (ℕ × ℕ)
  targets : Fin n → List ℕ

def cols (n : ℕ) := range' 0 (2*n)
def sources (n : ℕ) (edges : List (ℕ × ℕ)) :=
  (cols n).filter fun j => j ∉ edges.map Prod.fst

structure Frame.Valid {n : ℕ} (f : Frame n) (k : ℕ) : Prop where
  top : f.seam 0 = []
  outside : ∀ i, n ≤ i → f.seam i = []
  seamLegal : ∀ i e, e ∈ f.seam i → Near e.1 e.2
  sourceCover : ∀ i : Fin n, (sources n (f.seam i) ++ (f.seam i).map Prod.fst).Perm (cols n)
  targetCover : ∀ i : Fin n, (f.targets i ++ (f.seam (i.val+1)).map Prod.snd).Perm (cols n)
  localEdges : ∀ i : Fin n, Forall₂ Near (sources n (f.seam i)) (f.targets i)
  budget : (∑ i : Fin n, (fixed (sources n (f.seam i)) (f.targets i) +
    ((f.seam i).filter fun e => e.1=e.2).length)) = k

abbrev Axis (n k : ℕ) := {f : Frame n // f.Valid k}

@[simp] private theorem sources_nil (n : ℕ) : sources n [] = cols n := by simp [sources]

/-- Full occupancy forces the boundary between every pair of bands to be empty. -/
theorem seams_empty {n k} {f : Frame n} (h : f.Valid k) (i : ℕ) : f.seam i=[] := by
  induction i with
  | zero => exact h.top
  | succ i ih =>
    by_cases hi : i<n
    · let j : Fin n := ⟨i,hi⟩
      have h₁ := (h.localEdges j).length_eq
      have h₂ := (h.targetCover j).length_eq
      simp only [j, ih, sources_nil] at h₁
      simp only [j, length_append, length_map] at h₂
      apply List.length_eq_zero_iff.mp
      omega
    · exact h.outside _ (by omega)

abbrev Families (n k : ℕ) := {f : Fin n → Word //
    (∀ i, width (f i)=2*n) ∧ (∑ i, straights (f i))=k}

private def assemble {n k} (w : Families n k) : Axis n k := by
  refine ⟨⟨fun _ => [],fun i => partners 0 (w.val i)⟩, ?_⟩
  constructor
  · rfl
  · intros; rfl
  · simp
  · simp
  · intro i
    simpa [cols,w.property.1 i] using (strip_encode 0 (w.val i)).1
  · intro i
    simpa [cols,w.property.1 i] using (strip_encode 0 (w.val i)).2
  · have step (i : Fin n) : fixed (cols n) (partners 0 (w.val i)) = straights (w.val i) := by
      simpa only [w.property.1 i,cols] using fixed_partners 0 (w.val i)
    simpa [step] using w.property.2

private theorem assemble_bijective (n k) :
    Function.Bijective (@assemble n k) := by
  constructor
  · intro a b h
    apply Subtype.ext
    funext i
    exact partners_injective 0 (congrArg (fun z : Axis n k => z.val.targets i) h)
  · intro ⟨f,h⟩
    have he := seams_empty h
    have hs (i : Fin n) : StripOK 0 (2*n) (f.targets i) := by
      exact ⟨by simpa [he,cols] using h.targetCover i,
        by simpa [he,cols] using h.localEdges i⟩
    choose w hw hp using fun i => strip_decode (hs i)
    have hfix (i : Fin n) : fixed (cols n) (f.targets i) = straights (w i) := by
      rw [cols,← hw i,← hp i,fixed_partners]
    refine ⟨⟨w,hw,by simpa [he,hfix] using h.budget⟩, ?_⟩
    apply Subtype.ext
    exact Frame.ext (funext fun i => (he i).symm) (funext hp)

noncomputable def frameEquiv (n k : ℕ) : Families n k ≃ Axis n k :=
  Equiv.ofBijective _ (assemble_bijective n k)


private lemma balance (w : Word) : width w + straights w = 2*w.length := by
  induction w with
  | nil => rfl
  | cons a l ih => cases a <;> simp only [width,straights,length_cons] <;> omega

private lemma straights_count (w : Word) : straights w = w.count .vertical := by
  induction w with
  | nil => rfl
  | cons a l ih => cases a <;> simp [straights,ih,Nat.add_comm]

private def plain (n : ℕ) : Word := replicate n .crossed
private lemma plain_spec (n : ℕ) : width (plain n)=2*n ∧ straights (plain n)=0 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    change width (.crossed::plain n)=_ ∧ straights (.crossed::plain n)=0
    simp only [width,straights,ih.1,ih.2,and_true]; omega

private lemma sole_word (w : Word) (h : straights w=0) : w=plain w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | vertical => simp [straights] at h
    | crossed => exact congrArg (Block.crossed :: ·) (ih h)

private lemma plain_unique {w : Word} {n} (hw : width w=2*n) (hs : straights w=0) :
    w=plain n := by
  have hb := balance w
  have hl : w.length=n := by omega
  simpa only [hl] using sole_word w hs

private def emptyFamily (n : ℕ) : Families n 0 :=
  ⟨fun _ => plain n, fun _ => (plain_spec n).1, by simp [(plain_spec n).2]⟩

theorem all_diagonal (n : ℕ) : Nat.card (Axis n 0)=1 := by
  rw [← Nat.card_congr (frameEquiv n 0)]
  let _ : Unique (Families n 0) := {
    default := emptyFamily n
    uniq := by
      intro x
      apply Subtype.ext; funext i
      apply plain_unique (x.property.1 i)
      have h := Finset.single_le_sum (f:=fun j => straights (x.val j))
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega }
  exact Nat.card_unique

abbrev TwoWord (n : ℕ) := {w : Word // width w=2*n ∧ straights w=2}
abbrev Marks (n : ℕ) := {s : Finset (Fin (n+1)) // s.card=2}
private def marked {n} (s : Marks n) : Word :=
  ofFn fun i => if i∈s.val then .vertical else .crossed

private lemma marked_count {n} (s : Marks n) : straights (marked s)=2 := by
  rw [straights_count,marked,count_ofFn]
  simpa using s.property

private def makeWord {n} (s : Marks n) : TwoWord n :=
  ⟨marked s, by
    have h := balance (marked s)
    have hc := marked_count s
    have hl : (marked s).length=n+1 := by simp [marked]
    omega, marked_count s⟩

private theorem makeWord_bijective (n) : Function.Bijective (@makeWord n) := by
  constructor
  · intro a b h
    have hw : marked a=marked b := congrArg Subtype.val h
    have hf := List.ofFn_injective hw
    apply Subtype.ext; ext i
    have hv := congrFun hf i
    by_cases ha : i∈a.val <;> by_cases hb : i∈b.val <;> simp_all
  · intro ⟨w,hw,hs⟩
    have hl : w.length=n+1 := by have := balance w; omega
    let f (i : Fin (n+1)) := w[i.val]'(by omega)
    have hf : ofFn f=w := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using hl.symm
      · intro i h₁ h₂; simp only [List.getElem_ofFn,f]
    let s := Finset.univ.filter (fun i => f i=Block.vertical)
    have hc : s.card=2 := by
      rw [straights_count,← hf,count_ofFn] at hs
      exact hs
    refine ⟨⟨s,hc⟩,Subtype.ext ?_⟩
    change marked ⟨s,hc⟩ = w
    rw [← hf]
    apply congrArg List.ofFn
    funext i
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    cases f i <;> simp

private def place {n} (p : Fin n × TwoWord n) : Families n 2 :=
  ⟨fun i => if i=p.1 then p.2.val else plain n, by
    intro i
    by_cases h : i=p.1 <;> simp [h,p.2.property.1,(plain_spec n).1], by
    simp only [apply_ite straights, p.2.property.2, (plain_spec n).2]
    simp⟩

private lemma place_bijective (n) : Function.Bijective (@place n) := by
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩ h
    have eqAt (k : Fin n) := congrFun (congrArg Subtype.val h) k
    by_cases hij : i=j
    · subst j
      have he : a.val=b.val := by simpa [place] using eqAt i
      simp [Subtype.ext he]
    · have he : a.val=plain n := by simpa [place,hij] using eqAt i
      have := a.property.2
      rw [he,(plain_spec n).2] at this
      omega
  · intro x
    have total := x.property.2
    obtain ⟨i,hi⟩ : ∃ i, straights (x.val i) ≠ 0 := by
      by_contra! h
      simp [h] at total
    have le2 (j : Fin n) : straights (x.val j) ≤ 2 := by
      exact (Finset.single_le_sum (f:=fun l => straights (x.val l))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_eq total
    have two : straights (x.val i)=2 := by
      have := le2 i; have := balance (x.val i); have := x.property.1 i; omega
    have rest (j : Fin n) (hj : j≠i) : straights (x.val j)=0 := by
      have hsplit := Finset.sum_erase_add (s:=Finset.univ) (fun y => straights (x.val y)) (Finset.mem_univ i)
      have hj' : j∈Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩
      have hle := Finset.single_le_sum (f:=fun y => straights (x.val y))
        (fun _ _ => Nat.zero_le _) hj'
      omega
    refine ⟨(i,⟨x.val i,x.property.1 i,two⟩),Subtype.ext ?_⟩
    funext j
    by_cases h : j=i
    · subst j; simp [place]
    · simpa [place,h] using (plain_unique (x.property.1 j) (rest j h)).symm

abbrev Slot (n : ℕ) := Fin n × Fin (2*n)

/-- One horizontal tile and one vertical tile. Remove the horizontal endpoints
from their row-parity class; every remaining tile must connect the two classes. -/
structure Mixed (n : ℕ) where
  oddRow : Bool
  leftCell : Slot n
  rightCell : Slot n
  sameRow : leftCell.1 = rightCell.1
  consecutive : leftCell.2.val+1=rightCell.2.val
  cross : {z : Slot n // z≠leftCell ∧ z≠rightCell} ≃ Slot n
  legal : ∀ z, Near (2*z.val.1.val + oddRow.toNat)
    (2*(cross z).1.val + (!oddRow).toNat) ∧ Near z.val.2.val (cross z).2.val
  oneVertical : (Finset.univ.filter fun z => (cross z).2=z.val.2).card=1

private instance (n) : IsEmpty (Mixed n) := ⟨fun m => by
  let embed (z : Slot n) := (m.cross.symm z).val
  have hi : Function.Injective embed := Subtype.val_injective.comp m.cross.symm.injective
  obtain ⟨z,hz⟩ := (Finite.injective_iff_surjective.mp hi) m.leftCell
  exact (m.cross.symm z).property.1 hz⟩

/-- The Boolean chooses the direction of two parallel ordinary pieces; the other
summand retains all placements in which the two pieces have different directions. -/
abbrev TwoOrdinary (n : ℕ) := (Bool × Axis n 2) ⊕ Mixed n

theorem two_ordinary (n : ℕ) : Nat.card (TwoOrdinary n)=n^2*(n+1) := by
  let wordEquiv := Equiv.ofBijective _ (makeWord_bijective n)
  let e := ((Equiv.prodCongr (Equiv.refl (Fin n)) wordEquiv).trans
    (Equiv.ofBijective _ (place_bijective n))).trans (frameEquiv n 2)
  let e' : TwoOrdinary n ≃ Bool × (Fin n × Marks n) :=
    (Equiv.sumEmpty _ _).trans (Equiv.prodCongr (Equiv.refl Bool) e.symm)
  rw [Nat.card_congr e',Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Fintype.card_finset_len]
  have h := Nat.add_one_mul_choose_eq n 1
  simp at h
  calc 2 * (n * (n+1).choose 2) = n * ((n+1).choose 2 * 2) := by ring
       _ = _ := by rw [← h]; ring

end Domicule
