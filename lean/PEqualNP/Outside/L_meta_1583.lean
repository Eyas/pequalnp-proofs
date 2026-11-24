import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Iterate
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1583

def nextFin (m : ℕ) (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

lemma nextFin_inj (m : ℕ) (hm : 0 < m) : Function.Injective (nextFin m hm) := by
  intro i j hij
  have hval : (i.val + 1) % m = (j.val + 1) % m := congrArg Fin.val hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi' : i.val + 1 < m <;> by_cases hj' : j.val + 1 < m
  · rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hval
    omega
  · have hjm : j.val + 1 = m := by omega
    rw [Nat.mod_eq_of_lt hi', hjm, Nat.mod_self] at hval
    omega
  · have him : i.val + 1 = m := by omega
    rw [him, Nat.mod_self, Nat.mod_eq_of_lt hj'] at hval
    omega
  · omega

lemma nextFin_iterate (m : ℕ) (hm : 0 < m) (k : ℕ) (i : Fin m) :
    ((nextFin m hm)^[k] i).val = (i.val + k) % m := by
  induction k with
  | zero =>
    simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((((nextFin m hm)^[k] i).val + 1) % m) = (i.val + (k + 1)) % m
    rw [ih]
    rw [Nat.mod_add_mod, Nat.add_assoc]

lemma exists_cycle {N m : ℕ} (T0 : Finset (Fin N)) (hm : 0 < m) (hcard : T0.card = m) :
    ∃ sigma : Fin N → Fin N,
      (∀ x ∈ T0, sigma x ∈ T0) ∧
      Set.InjOn sigma ↑T0 ∧
      (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) := by
  classical
  let e : Fin m ≃ {x : Fin N // x ∈ T0} := (T0.equivFinOfCardEq hcard).symm
  let sigma : Fin N → Fin N := fun z =>
    if hz : z ∈ T0 then (e (nextFin m hm (e.symm ⟨z, hz⟩))).val else z
  have hstep : ∀ i : Fin m, sigma (e i).val = (e (nextFin m hm i)).val := by
    intro i
    simp [sigma]
  have hiter : ∀ (k : ℕ) (i : Fin m), sigma^[k] (e i).val = (e ((nextFin m hm)^[k] i)).val := by
    intro k i
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hstep]
  refine ⟨sigma, ?_, ?_, ?_⟩
  · intro x hx
    simp [sigma, hx]
  · intro x hx y hy hxy
    have hx' : x ∈ T0 := hx
    have hy' : y ∈ T0 := hy
    simp only [sigma, hx', hy', ↓reduceDIte] at hxy
    have hsub : e (nextFin m hm (e.symm ⟨x, hx'⟩)) = e (nextFin m hm (e.symm ⟨y, hy'⟩)) :=
      Subtype.ext hxy
    have h1 := nextFin_inj m hm (e.injective hsub)
    have h2 : (⟨x, hx'⟩ : {z : Fin N // z ∈ T0}) = ⟨y, hy'⟩ := e.symm.injective h1
    exact congrArg Subtype.val h2
  · intro x hx y hy
    let i := e.symm ⟨x, hx⟩
    let j := e.symm ⟨y, hy⟩
    refine ⟨j.val + m - i.val, ?_⟩
    have hx_eq : x = (e i).val := by simp [i]
    have hy_eq : y = (e j).val := by simp [j]
    rw [hx_eq, hiter, hy_eq]
    apply congrArg (fun a => (e a).val)
    apply Fin.ext
    rw [nextFin_iterate]
    have hi := i.isLt
    have hj := j.isLt
    have hsum : i.val + (j.val + m - i.val) = j.val + m := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

lemma card_le_two_of_order_two {N : ℕ} {T0 : Finset (Fin N)} {sigma : Fin N → Fin N} {u : Fin N}
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    (hu : u ∈ T0) (h2 : sigma (sigma u) = u) : T0.card ≤ 2 := by
  have horb : ∀ k : ℕ, sigma^[k] u = u ∨ sigma^[k] u = sigma u := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · exact Or.inr (congrArg sigma h)
      · rw [h, h2]
        exact Or.inl rfl
  have hsub : T0 ⊆ {u, sigma u} := by
    intro y hy
    rcases htrans u hu y hy with ⟨k, hk⟩
    rcases horb k with h | h
    · rw [← hk, h]
      simp
    · rw [← hk, h]
      simp
  calc T0.card ≤ ({u, sigma u} : Finset (Fin N)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

lemma sigma_ne_self {N m : ℕ} {T0 : Finset (Fin N)} {sigma : Fin N → Fin N} {u : Fin N}
    (hm3 : 3 ≤ m) (hcard : T0.card = m)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    (hu : u ∈ T0) : sigma u ≠ u := by
  intro h
  have h2 : sigma (sigma u) = u := by rw [h, h]
  have hle := card_le_two_of_order_two htrans hu h2
  omega

lemma sigma_sigma_ne {N m : ℕ} {T0 : Finset (Fin N)} {sigma : Fin N → Fin N} {u : Fin N}
    (hm3 : 3 ≤ m) (hcard : T0.card = m)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    (hu : u ∈ T0) : sigma (sigma u) ≠ u := by
  intro h2
  have hle := card_le_two_of_order_two htrans hu h2
  omega

lemma main_proof : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  intro q m N L i0 T0 hq hm3 hmq hN hcard hinter hline hT0_sub hT0_card
  refine ⟨exists_cycle T0 (by omega) hT0_card, ?_⟩
  intro sigma x0 B ⟨hsigma_mem, hsigma_inj, hsigma_trans⟩ hx0 hB_T0 hB_out
  have huniq : ∀ s : Fin N, s ≠ i0 → ∃ u : Fin N, u ∈ L s ∧ u ∈ L i0 ∧ ∀ v : Fin N, v ∈ L s → v ∈ L i0 → v = u := by
    intro s hs
    rcases Finset.card_eq_one.mp (hinter s i0 hs) with ⟨u, hu⟩
    refine ⟨u, ?_, ?_, ?_⟩
    · have : u ∈ L s ∩ L i0 := by rw [hu]; simp
      exact (Finset.mem_inter.mp this).1
    · have : u ∈ L s ∩ L i0 := by rw [hu]; simp
      exact (Finset.mem_inter.mp this).2
    · intro v hvs hvi0
      have : v ∈ L s ∩ L i0 := Finset.mem_inter.mpr ⟨hvs, hvi0⟩
      rw [hu] at this
      exact Finset.mem_singleton.mp this
  have hB_mem_T0 : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ w ∈ B s p, w ∈ T0 := by
    intro s hs p hp w hw
    rcases huniq s hs with ⟨u, hus, hui0, _⟩
    by_cases huT : u ∈ T0
    · rw [hB_T0 s hs p hp u huT hus] at hw
      split_ifs at hw
      · exact False.elim (Finset.notMem_empty w hw)
      · rw [Finset.mem_singleton.mp hw]
        exact hsigma_mem u huT
    · have hudiff : u ∈ L i0 \ T0 := Finset.mem_sdiff.mpr ⟨hui0, huT⟩
      rw [hB_out s hs u hudiff hus p hp] at hw
      rw [Finset.mem_singleton.mp hw]
      exact hx0
  constructor
  · intro s hs p hp
    rcases huniq s hs with ⟨u, hus, hui0, hu_uniq⟩
    have hdisj : B s p ∩ L s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rcases Finset.mem_inter.mp hw with ⟨hwB, hws⟩
      by_cases huT : u ∈ T0
      · rw [hB_T0 s hs p hp u huT hus] at hwB
        split_ifs at hwB
        · exact Finset.notMem_empty w hwB
        · have hw_eq : w = sigma u := Finset.mem_singleton.mp hwB
          have hwi0 : w ∈ L i0 := hT0_sub (hw_eq ▸ hsigma_mem u huT)
          have hwu : w = u := hu_uniq w hws hwi0
          exact sigma_ne_self hm3 hT0_card hsigma_trans huT (hw_eq ▸ hwu)
      · have hudiff : u ∈ L i0 \ T0 := Finset.mem_sdiff.mpr ⟨hui0, huT⟩
        rw [hB_out s hs u hudiff hus p hp] at hwB
        have hw_eq : w = x0 := Finset.mem_singleton.mp hwB
        have hwi0 : w ∈ L i0 := hT0_sub (hw_eq ▸ hx0)
        have hwu : w = u := hu_uniq w hws hwi0
        exact huT (hwu ▸ hw_eq ▸ hx0)
    refine ⟨hdisj, ?_, ?_⟩
    · left
      by_cases huT : u ∈ T0
      · by_cases hpu : p = u
        · refine ⟨u, huT, ?_⟩
          simp [hpu]
        · refine ⟨sigma u, hsigma_mem u huT, ?_⟩
          rw [hB_T0 s hs p hp u huT hus]
          simp [hpu]
      · have hudiff : u ∈ L i0 \ T0 := Finset.mem_sdiff.mpr ⟨hui0, huT⟩
        refine ⟨x0, hx0, ?_⟩
        rw [hB_out s hs u hudiff hus p hp]
        simp
    · intro v hvs
      have hv_notB : v ∉ B s p := by
        intro hvB
        have : v ∈ B s p ∩ L s := Finset.mem_inter.mpr ⟨hvB, hvs⟩
        rw [hdisj] at this
        exact Finset.notMem_empty v this
      simp [hv_notB]
  · intro s s' hs hs' hss' ⟨⟨p, hp_diff, w, hw_inter⟩, ⟨p', hp'_diff, w', hw'_inter⟩⟩
    have hp : p ∈ L s := (Finset.mem_sdiff.mp hp_diff).1
    have hp' : p' ∈ L s' := (Finset.mem_sdiff.mp hp'_diff).1
    rcases Finset.mem_inter.mp hw_inter with ⟨hwB, hws'⟩
    rcases Finset.mem_inter.mp hw'_inter with ⟨hw'B, hw's⟩
    rcases huniq s hs with ⟨u, hus, hui0, hu_uniq⟩
    rcases huniq s' hs' with ⟨u', hu's', hu'i0, hu'_uniq⟩
    have hwT : w ∈ T0 := hB_mem_T0 s hs p hp w hwB
    have hw'T : w' ∈ T0 := hB_mem_T0 s' hs' p' hp' w' hw'B
    have hwu' : w = u' := hu'_uniq w hws' (hT0_sub hwT)
    have hw'u : w' = u := hu_uniq w' hw's (hT0_sub hw'T)
    have huT : u ∈ T0 := hw'u ▸ hw'T
    have hu'T : u' ∈ T0 := hwu' ▸ hwT
    rw [hB_T0 s hs p hp u huT hus] at hwB
    split_ifs at hwB
    · exact Finset.notMem_empty w hwB
    · have hu'_eq : u' = sigma u := hwu' ▸ Finset.mem_singleton.mp hwB
      rw [hB_T0 s' hs' p' hp' u' hu'T hu's'] at hw'B
      split_ifs at hw'B
      · exact Finset.notMem_empty w' hw'B
      · have hu_eq : u = sigma u' := hw'u ▸ Finset.mem_singleton.mp hw'B
        have h2 : sigma (sigma u) = u := by rw [← hu'_eq, ← hu_eq]
        exact sigma_sigma_ne hm3 hT0_card hsigma_trans huT h2

end PEqualNP.Outside.L_meta_1583

theorem PEqualNP.Outside.L_meta_1583 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  exact PEqualNP.Outside.L_meta_1583.main_proof
