import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_651_1 :
    (¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      C.gates.head? = some ⟨GateOp.not, [0]⟩ ∧
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
         (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
         (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) →
    (¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      C.gates.head? = some ⟨GateOp.and, [0, 1]⟩ ∧
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
         (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
         (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) →
    (¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      C.gates.head? = some ⟨GateOp.or, [0, 1]⟩ ∧
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
         (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
         (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) →
    (¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 19 ∧
      (C.gates.head? = some ⟨GateOp.and, [0, 2]⟩ ∨
       C.gates.head? = some ⟨GateOp.or, [0, 2]⟩) ∧
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
         (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
         (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) →
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 19 := by
  classical
  intro hnot hand hor hnonedge hhas
  let pet : (Fin 10 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
    (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hceval : ∀ (D : Circuit) (x : List Bool), D.eval x = (D.wires x).getD D.output false :=
    fun _ _ => rfl
  have hcwires : ∀ (D : Circuit) (x : List Bool), D.wires x = D.gates.foldl step x :=
    fun _ _ => rfl
  have hcsize : ∀ (D : Circuit), D.size = D.gates.length := fun _ => rfl
  have heval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have heval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have heval_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have hfold_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih (step w g) i (by simp only [step, List.length_append, List.length_singleton]; omega)]
      simp only [step, List.getD_append _ _ _ _ hi]
  have hex : ∃ s, HasCircuitSize 10 pet s := ⟨19, hhas⟩
  obtain ⟨C, hC, hCsize, hCeval⟩ := Nat.find_spec hex
  have hC19 : C.size ≤ 19 := hCsize.trans (Nat.find_min' hex hhas)
  have hCmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = pet x) → C.size ≤ D.size :=
    fun D hD hDeval => hCsize.trans (Nat.find_min' hex ⟨D, hD, le_rfl, hDeval⟩)
  -- Non-empty gates: 0-gate circuits cannot compute pet.
  have hCne : C.gates ≠ [] := by
    intro hemp
    by_cases hout : C.output < 10
    · let i : Fin 10 := ⟨C.output, hout⟩
      have h1 := hCeval (fun j => decide (j = i))
      have hlhs : C.eval (List.ofFn (fun j : Fin 10 => decide (j = i))) = true := by
        rw [hceval, hcwires, hemp, List.foldl_nil,
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hout), List.getElem_ofFn]
        simp [i]
      have hrhs_all : ∀ k : Fin 10, pet (fun j : Fin 10 => decide (j = k)) = false := by decide
      have hrhs : pet (fun j : Fin 10 => decide (j = i)) = false := hrhs_all i
      rw [hlhs, hrhs] at h1
      exact Bool.noConfusion h1
    · have h1 := hCeval (fun _ => true)
      have hlhs : C.eval (List.ofFn (fun _ : Fin 10 => true)) = false := by
        rw [hceval, hcwires, hemp, List.foldl_nil]
        exact List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
      have hrhs : pet (fun _ : Fin 10 => true) = true := by decide
      rw [hlhs, hrhs] at h1
      exact Bool.noConfusion h1
  -- Eliminate gate 0 when it always equals wire v0 (either an input < 10 or an out-of-range wire).
  have helim_wire : ∀ (g0 : Gate) (rest : List Gate), C.gates = g0 :: rest →
      ∀ (v0 : ℕ), (v0 < 10 ∨ 10 + rest.length ≤ v0) →
      (∀ x : Fin 10 → Bool,
        g0.op.eval (g0.inputs.map fun r => (List.ofFn x).getD r false) =
          (List.ofFn x).getD v0 false) → False := by
    intro g0 rest hgates v0 hv0 hagree
    let sh : ℕ → ℕ := fun w => if w < 10 then w else if w = 10 then v0 else w - 1
    let D : Circuit := ⟨rest.map (fun g => ⟨g.op, g.inputs.map sh⟩), sh C.output⟩
    have hDfan : FanInTwo D := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hmem : g' ∈ C.gates := by rw [hgates]; exact List.mem_cons_of_mem _ hg'
      exact ⟨(hC g' hmem).1, by simp only [List.length_map]; exact (hC g' hmem).2⟩
    have hDsize : D.size < C.size := by
      simp only [hcsize, D, hgates, List.length_map, List.length_cons]; omega
    have hsim : ∀ (gs : List Gate) (w1 w2 : List Bool),
        w1.length = w2.length + 1 → 10 ≤ w2.length → w2.length + gs.length ≤ 10 + rest.length →
        (∀ r < 10, w1.getD r false = w2.getD r false) →
        w1.getD 10 false = w2.getD v0 false →
        (∀ r, 10 < r → w1.getD r false = w2.getD (r - 1) false) →
        let w1' := gs.foldl step w1
        let w2' := (gs.map fun g => ⟨g.op, g.inputs.map sh⟩).foldl step w2
        (∀ r < 10, w1'.getD r false = w2'.getD r false) ∧
        w1'.getD 10 false = w2'.getD v0 false ∧
        (∀ r, 10 < r → w1'.getD r false = w2'.getD (r - 1) false) := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ _ hlt h10 hgt; exact ⟨hlt, h10, hgt⟩
      | cons g gs ih =>
        intro w1 w2 hlen h10le hbound hlt h10 hgt
        have hread : ∀ r, w2.getD (sh r) false = w1.getD r false := by
          intro r
          simp only [sh]
          split_ifs with h1 h2
          · exact (hlt r h1).symm
          · subst h2; exact h10.symm
          · exact (hgt r (by omega)).symm
        have hval : g.op.eval ((g.inputs.map sh).map fun i => w2.getD i false) =
            g.op.eval (g.inputs.map fun i => w1.getD i false) := by
          rw [List.map_map]; congr 1; exact List.map_congr_left fun r _ => hread r
        have hstep1 : step w1 g = w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := rfl
        have hstep2 : step w2 ⟨g.op, g.inputs.map sh⟩ =
            w2 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := by simp only [step, hval]
        simp only [List.map_cons, List.foldl_cons]
        apply ih (step w1 g) (step w2 ⟨g.op, g.inputs.map sh⟩)
        · simp only [hstep1, hstep2, List.length_append, List.length_singleton]; omega
        · simp only [hstep2, List.length_append, List.length_singleton]; omega
        · have hb' : w2.length + (gs.length + 1) ≤ 10 + rest.length := by
            simpa only [List.length_cons] using hbound
          rw [hstep2, List.length_append, List.length_singleton]; omega
        · intro r hr
          rw [hstep1, hstep2, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hlt r hr
        · rw [hstep1, hstep2, List.getD_append _ _ _ _ (by omega)]
          rcases hv0 with hvlt | hvge
          · rw [List.getD_append _ _ _ _ (by omega)]; exact h10
          · have hb' : w2.length + (gs.length + 1) ≤ 10 + rest.length := by
              simpa only [List.length_cons] using hbound
            have hvge1 : w2.length ≤ v0 := by omega
            have hvge2 : (w2 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).length ≤ v0 := by
              rw [List.length_append, List.length_singleton]; omega
            rw [List.getD_eq_default _ _ hvge2, h10, List.getD_eq_default _ _ hvge1]
        · intro r hr
          rw [hstep1, hstep2]
          by_cases hrl : r < w1.length
          · rw [List.getD_append _ _ _ _ hrl, List.getD_append _ _ _ _ (by omega)]
            exact hgt r hr
          · by_cases hreq : r = w1.length
            · rw [hreq, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
              have hreq2 : w1.length - 1 = w2.length := by omega
              rw [hreq2, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
            · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
                List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]
    have hDeval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = pet x := by
      intro x
      rw [← hCeval x]
      simp only [hceval, hcwires, D, hgates, List.foldl_cons]
      have hstart := hsim rest (step (List.ofFn x) g0) (List.ofFn x)
        (by simp [step]) (by rw [List.length_ofFn]) (by rw [List.length_ofFn])
        (by
          intro r hr
          simp only [step]
          exact List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hr))
        (by
          simp only [step]
          rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn,
            Nat.sub_self, List.getD_cons_zero]
          exact hagree x)
        (by
          intro r hr
          rw [List.getD_eq_default _ _ (by simp [step]; omega),
              List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)])
      simp only [sh]
      split_ifs with h1 h2
      · exact (hstart.1 C.output h1).symm
      · rw [h2]; exact hstart.2.1.symm
      · exact (hstart.2.2 C.output (by omega)).symm
    have hle := hCmin D hDfan hDeval
    omega
  -- Eliminate gate 0 when it is constant true.
  have helim_true : ∀ (g0 : Gate) (rest : List Gate), C.gates = g0 :: rest →
      (∀ x : Fin 10 → Bool,
        g0.op.eval (g0.inputs.map fun r => (List.ofFn x).getD r false) = true) → False := by
    intro g0 rest hgates htrue
    have houtne : C.output ≠ 10 := by
      intro hout10
      have h0 := hCeval (fun _ => false)
      have hlhs : C.eval (List.ofFn (fun _ : Fin 10 => false)) = true := by
        simp only [hceval, hcwires, hgates, hout10, List.foldl_cons]
        rw [hfold_getD_lt rest (step (List.ofFn (fun _ : Fin 10 => false)) g0) 10
          (by simp [step])]
        simp only [step]
        rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn,
          Nat.sub_self, List.getD_cons_zero]
        exact htrue (fun _ => false)
      have hrhs : pet (fun _ : Fin 10 => false) = false := by decide
      rw [hlhs, hrhs] at h0
      exact Bool.noConfusion h0
    let sh : ℕ → ℕ := fun w => if w < 10 then w else w - 1
    let rwG : Gate → Gate := fun g =>
      GateOp.casesOn g.op
        ⟨.and, (g.inputs.filter (· != 10)).map sh⟩
        (if 10 ∈ g.inputs then ⟨.and, []⟩ else ⟨.or, g.inputs.map sh⟩)
        (List.casesOn g.inputs ⟨.not, []⟩ (fun r _ => if r = 10 then ⟨.or, []⟩ else ⟨.not, [sh r]⟩))
        (fun m => ⟨.mod m, g.inputs.map sh⟩)
        ⟨.maj, g.inputs.map sh⟩
    let D : Circuit := ⟨rest.map rwG, sh C.output⟩
    have hDfan : FanInTwo D := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hmem : g' ∈ C.gates := by rw [hgates]; exact List.mem_cons_of_mem _ hg'
      obtain ⟨hop, hlen⟩ := hC g' hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · simp only [rwG, hop, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, true_and,
          List.length_map]
        exact (List.length_filter_le _ _).trans hlen
      · simp only [rwG, hop]
        split_ifs
        · simp
        · simp [hlen]
      · simp only [rwG, hop]
        cases g'.inputs with
        | nil => simp
        | cons r _ => dsimp only; split_ifs <;> simp
    have hDsize : D.size < C.size := by
      simp only [hcsize, D, hgates, List.length_map, List.length_cons]; omega
    have hsim : ∀ (gs : List Gate),
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
        ∀ (w1 w2 : List Bool),
        w1.length = w2.length + 1 → 10 ≤ w2.length →
        (∀ r, r ≠ 10 → w1.getD r false = w2.getD (sh r) false) →
        w1.getD 10 false = true →
        let w1' := gs.foldl step w1
        let w2' := (gs.map rwG).foldl step w2
        (∀ r, r ≠ 10 → w1'.getD r false = w2'.getD (sh r) false) ∧ w1'.getD 10 false = true := by
      intro gs
      induction gs with
      | nil => intro _ w1 w2 _ _ hne h10; exact ⟨hne, h10⟩
      | cons g gs ih =>
        intro hgs w1 w2 hlen h10le hne h10
        have hg_op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
          hgs g (List.mem_cons_self ..)
        have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
          fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
        have hval : (rwG g).op.eval ((rwG g).inputs.map fun i => w2.getD i false) =
            g.op.eval (g.inputs.map fun i => w1.getD i false) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg_op
          rcases hg_op with hop | hop | hop
          · simp only [rwG, hop, heval_and, List.map_map]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true, id_eq]
            constructor
            · intro hall b hb
              obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
              by_cases hr10 : r = 10
              · rw [hr10, h10]
              · rw [hne r hr10]
                exact hall _ (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [hr10]⟩, rfl⟩)
            · intro hall b hb
              obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
              obtain ⟨hrm, hr10⟩ := List.mem_filter.mp hr
              have hr10' : r ≠ 10 := by simpa using hr10
              change w2.getD (sh r) false = true
              rw [← hne r hr10']
              exact hall _ (List.mem_map.mpr ⟨r, hrm, rfl⟩)
          · simp only [rwG, hop]
            split_ifs with h10in
            · simp only [heval_and, heval_or, List.map_nil, List.all_nil]
              symm
              rw [List.any_eq_true]
              exact ⟨true, List.mem_map.mpr ⟨10, h10in, h10⟩, rfl⟩
            · simp only [heval_or, List.map_map]
              congr 1
              exact List.map_congr_left fun r hr =>
                (hne r fun heq => h10in (heq ▸ hr)).symm
          · simp only [rwG, hop]
            cases hin : g.inputs with
            | nil => simp [heval_not]
            | cons r rs =>
              dsimp only
              split_ifs with hr10
              · subst hr10
                simp only [heval_or, heval_not, List.map_nil, List.any_nil, List.map_cons,
                  List.headD_cons, h10, Bool.not_true]
              · simp only [heval_not, List.map_cons, List.headD_cons, hne r hr10]
        have hstep1 : step w1 g = w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := rfl
        have hstep2 : step w2 (rwG g) =
            w2 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := by simp only [step, hval]
        simp only [List.map_cons, List.foldl_cons]
        apply ih hgs' (step w1 g) (step w2 (rwG g))
        · simp only [hstep1, hstep2, List.length_append, List.length_singleton]; omega
        · simp only [hstep2, List.length_append, List.length_singleton]; omega
        · intro r hrne
          rw [hstep1, hstep2]
          by_cases hrlt : r < 10
          · simp only [sh, hrlt, ↓reduceIte]
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            simpa only [sh, hrlt, ↓reduceIte] using hne r hrne
          · have hrgt : 10 < r := by omega
            simp only [sh, hrlt, ↓reduceIte]
            by_cases hrl : r < w1.length
            · rw [List.getD_append _ _ _ _ hrl, List.getD_append _ _ _ _ (by omega)]
              simpa only [sh, hrlt, ↓reduceIte] using hne r hrne
            · by_cases hreq : r = w1.length
              · rw [hreq, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                have hreq2 : w1.length - 1 = w2.length := by omega
                rw [hreq2, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
              · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
                  List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]
        · rw [hstep1, List.getD_append _ _ _ _ (by omega)]; exact h10
    have hDeval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = pet x := by
      intro x
      rw [← hCeval x]
      simp only [hceval, hcwires, D, hgates, List.foldl_cons]
      have hrest_ops : ∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
        fun g hg => (hC g (by rw [hgates]; exact List.mem_cons_of_mem _ hg)).1
      have hstart := hsim rest hrest_ops (step (List.ofFn x) g0) (List.ofFn x)
        (by simp [step]) (by rw [List.length_ofFn])
        (by
          intro r hrne
          simp only [sh]
          by_cases hrlt : r < 10
          · simp only [hrlt, ↓reduceIte, step]
            exact List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hrlt)
          · simp only [hrlt, ↓reduceIte]
            rw [List.getD_eq_default _ _ (by simp [step]; omega),
                List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)])
        (by
          simp only [step]
          rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn,
            Nat.sub_self, List.getD_cons_zero]
          exact htrue x)
      exact (hstart.1 C.output houtne).symm
    have hle := hCmin D hDfan hDeval
    omega
  -- Input relabeling for any Petersen automorphism π : Fin 10 → Fin 10.
  let remap : (Fin 10 → Fin 10) → ℕ → ℕ := fun π w =>
    if h : w < 10 then (π ⟨w, h⟩).val else w
  have hrelabel : ∀ (π : Fin 10 → Fin 10), (∀ x : Fin 10 → Bool, pet (x ∘ π) = pet x) →
      ∀ (D : Circuit), FanInTwo D → (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = pet x) →
      let D' : Circuit := ⟨D.gates.map fun g => ⟨g.op, g.inputs.map (remap π)⟩, remap π D.output⟩
      FanInTwo D' ∧ D'.size = D.size ∧ ∀ x : Fin 10 → Bool, D'.eval (List.ofFn x) = pet x := by
    intro π hπ D hD hDeval
    let D' : Circuit := ⟨D.gates.map fun g => ⟨g.op, g.inputs.map (remap π)⟩, remap π D.output⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hD g' hg').1, by simp only [List.length_map]; exact (hD g' hg').2⟩
    · simp only [hcsize, List.length_map]
    · intro x
      have hsim : ∀ (gs : List Gate) (w1 w2 : List Bool),
          w1.length = w2.length → 10 ≤ w1.length →
          (∀ k : Fin 10, w2.getD (π k).val false = w1.getD k.val false) →
          (∀ j, 10 ≤ j → w2.getD j false = w1.getD j false) →
          let w1' := gs.foldl step w1
          let w2' := (gs.map fun g => ⟨g.op, g.inputs.map (remap π)⟩).foldl step w2
          (∀ k : Fin 10, w2'.getD (π k).val false = w1'.getD k.val false) ∧
          (∀ j, 10 ≤ j → w2'.getD j false = w1'.getD j false) := by
        intro gs
        induction gs with
        | nil => intro w1 w2 _ _ hk hj; exact ⟨hk, hj⟩
        | cons g gs ih =>
          intro w1 w2 hlen h10 hk hj
          have hread : ∀ r, w2.getD (remap π r) false = w1.getD r false := by
            intro r
            simp only [remap]
            split_ifs with hr
            · exact hk ⟨r, hr⟩
            · exact hj r (by omega)
          have hval : g.op.eval ((g.inputs.map (remap π)).map fun i => w2.getD i false) =
              g.op.eval (g.inputs.map fun i => w1.getD i false) := by
            rw [List.map_map]; congr 1; exact List.map_congr_left fun r _ => hread r
          have hstep1 : step w1 g = w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := rfl
          have hstep2 : step w2 ⟨g.op, g.inputs.map (remap π)⟩ =
              w2 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)] := by simp only [step, hval]
          simp only [List.map_cons, List.foldl_cons]
          apply ih (step w1 g) (step w2 ⟨g.op, g.inputs.map (remap π)⟩)
          · simp only [hstep1, hstep2, List.length_append, List.length_singleton, hlen]
          · simp only [hstep1, List.length_append, List.length_singleton]; omega
          · intro k
            rw [hstep1, hstep2,
              List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            exact hk k
          · intro j hj10
            rw [hstep1, hstep2]
            by_cases hjl : j < w1.length
            · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hjl]
              exact hj j hj10
            · by_cases hjeq : j = w1.length
              · rw [hjeq, List.getD_append_right _ _ _ _ (by omega),
                  List.getD_append_right _ _ _ _ le_rfl, hlen, Nat.sub_self, List.getD_cons_zero]
              · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
                  List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]
      have hstart := hsim D.gates (List.ofFn (x ∘ π)) (List.ofFn x) (by simp) (by simp)
        (by
          intro k
          rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp),
            List.getElem_ofFn, List.getElem_ofFn]
          rfl)
        (by
          intro j hj
          rw [List.getD_eq_default _ _ (by simp [hj]), List.getD_eq_default _ _ (by simp [hj])])
      have heq : D'.eval (List.ofFn x) = D.eval (List.ofFn (x ∘ π)) := by
        simp only [hceval, hcwires, D', remap]
        split_ifs with hlt
        · exact hstart.1 ⟨D.output, hlt⟩
        · exact hstart.2 D.output (by omega)
      rw [heq, hDeval (x ∘ π), hπ x]
  -- Adjacency predicate for the Petersen graph, to verify automorphisms by decide.
  let adj : Fin 10 → Fin 10 → Bool := fun u v =>
    (u == 0 && v == 1) || (u == 1 && v == 0) ||
    (u == 1 && v == 2) || (u == 2 && v == 1) ||
    (u == 2 && v == 3) || (u == 3 && v == 2) ||
    (u == 3 && v == 4) || (u == 4 && v == 3) ||
    (u == 4 && v == 0) || (u == 0 && v == 4) ||
    (u == 0 && v == 5) || (u == 5 && v == 0) ||
    (u == 1 && v == 6) || (u == 6 && v == 1) ||
    (u == 2 && v == 7) || (u == 7 && v == 2) ||
    (u == 3 && v == 8) || (u == 8 && v == 3) ||
    (u == 4 && v == 9) || (u == 9 && v == 4) ||
    (u == 5 && v == 7) || (u == 7 && v == 5) ||
    (u == 7 && v == 9) || (u == 9 && v == 7) ||
    (u == 9 && v == 6) || (u == 6 && v == 9) ||
    (u == 6 && v == 8) || (u == 8 && v == 6) ||
    (u == 8 && v == 5) || (u == 5 && v == 8)
  have hpet_adj : ∀ x : Fin 10 → Bool,
      pet x = true ↔ ∃ u v : Fin 10, adj u v = true ∧ x u = true ∧ x v = true := by
    intro x
    constructor
    · intro hx
      simp only [pet, Bool.or_eq_true, Bool.and_eq_true] at hx
      rcases hx with ((((((((((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
        ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
        ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨0, 1, by decide, h1, h2⟩
      · exact ⟨1, 2, by decide, h1, h2⟩
      · exact ⟨2, 3, by decide, h1, h2⟩
      · exact ⟨3, 4, by decide, h1, h2⟩
      · exact ⟨4, 0, by decide, h1, h2⟩
      · exact ⟨0, 5, by decide, h1, h2⟩
      · exact ⟨1, 6, by decide, h1, h2⟩
      · exact ⟨2, 7, by decide, h1, h2⟩
      · exact ⟨3, 8, by decide, h1, h2⟩
      · exact ⟨4, 9, by decide, h1, h2⟩
      · exact ⟨5, 7, by decide, h1, h2⟩
      · exact ⟨7, 9, by decide, h1, h2⟩
      · exact ⟨9, 6, by decide, h1, h2⟩
      · exact ⟨6, 8, by decide, h1, h2⟩
      · exact ⟨8, 5, by decide, h1, h2⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      simp only [adj, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at huv
      rcases huv with (((((((((((((((((((((((((((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) <;>
        simp only [pet, hu, hv, Bool.and_true, Bool.true_or, Bool.or_true]
  have hinv_aut : ∀ (π πi : Fin 10 → Fin 10),
      (∀ u, π (πi u) = u) → (∀ u v, adj (π u) (π v) = adj u v) →
      ∀ x : Fin 10 → Bool, pet (x ∘ π) = pet x := by
    intro π πi hsurj hadj x
    apply Bool.eq_iff_iff.mpr
    rw [hpet_adj, hpet_adj]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨π u, π v, by rw [hadj, huv], hu, hv⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨πi u, πi v, ?_, ?_, ?_⟩
      · rw [← hadj, hsurj, hsurj]; exact huv
      · simpa only [Function.comp, hsurj] using hu
      · simpa only [Function.comp, hsurj] using hv
  -- Three generators of Aut(Petersen): 5-cycle rotation, swap(0,5), and stabilizer 6-cycle at 0.
  let g1 : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]
  let g1i : Fin 10 → Fin 10 := ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8]
  let sw : Fin 10 → Fin 10 := ![5, 7, 2, 3, 8, 0, 9, 1, 4, 6]
  let swi : Fin 10 → Fin 10 := ![5, 7, 2, 3, 8, 0, 9, 1, 4, 6]
  let r0 : Fin 10 → Fin 10 := ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6]
  let r0i : Fin 10 → Fin 10 := ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7]
  have hg1 : ∀ x : Fin 10 → Bool, pet (x ∘ g1) = pet x := hinv_aut g1 g1i (by decide) (by decide)
  have hsw : ∀ x : Fin 10 → Bool, pet (x ∘ sw) = pet x := hinv_aut sw swi (by decide) (by decide)
  have hr0 : ∀ x : Fin 10 → Bool, pet (x ∘ r0) = pet x := hinv_aut r0 r0i (by decide) (by decide)
  have hcomp_aut : ∀ (a b : Fin 10 → Fin 10),
      (∀ x, pet (x ∘ a) = pet x) → (∀ x, pet (x ∘ b) = pet x) →
      ∀ x, pet (x ∘ (a ∘ b)) = pet x := by
    intro a b ha hb x
    change pet ((x ∘ a) ∘ b) = pet x
    rw [hb (x ∘ a), ha x]
  have hg1_inj : Function.Injective g1 := by decide
  have hsw_inj : Function.Injective sw := by decide
  have hr0_inj : Function.Injective r0 := by decide
  have hsend0 : ∀ i : Fin 10, ∃ π : Fin 10 → Fin 10,
      Function.Injective π ∧ (∀ x, pet (x ∘ π) = pet x) ∧ π i = 0 := by
    intro i
    fin_cases i
    · exact ⟨id, Function.injective_id, fun _ => rfl, rfl⟩
    · exact ⟨g1 ∘ g1 ∘ g1 ∘ g1, hg1_inj.comp (hg1_inj.comp (hg1_inj.comp hg1_inj)),
        hcomp_aut _ _ hg1 (hcomp_aut _ _ hg1 (hcomp_aut _ _ hg1 hg1)), by decide⟩
    · exact ⟨g1 ∘ g1 ∘ g1, hg1_inj.comp (hg1_inj.comp hg1_inj),
        hcomp_aut _ _ hg1 (hcomp_aut _ _ hg1 hg1), by decide⟩
    · exact ⟨g1 ∘ g1, hg1_inj.comp hg1_inj, hcomp_aut _ _ hg1 hg1, by decide⟩
    · exact ⟨g1, hg1_inj, hg1, by decide⟩
    · exact ⟨sw, hsw_inj, hsw, by decide⟩
    · exact ⟨sw ∘ g1 ∘ g1 ∘ g1 ∘ g1, hsw_inj.comp (hg1_inj.comp (hg1_inj.comp (hg1_inj.comp hg1_inj))),
        hcomp_aut _ _ hsw (hcomp_aut _ _ hg1 (hcomp_aut _ _ hg1 (hcomp_aut _ _ hg1 hg1))), by decide⟩
    · exact ⟨sw ∘ g1 ∘ g1 ∘ g1, hsw_inj.comp (hg1_inj.comp (hg1_inj.comp hg1_inj)),
        hcomp_aut _ _ hsw (hcomp_aut _ _ hg1 (hcomp_aut _ _ hg1 hg1)), by decide⟩
    · exact ⟨sw ∘ g1 ∘ g1, hsw_inj.comp (hg1_inj.comp hg1_inj),
        hcomp_aut _ _ hsw (hcomp_aut _ _ hg1 hg1), by decide⟩
    · exact ⟨sw ∘ g1, hsw_inj.comp hg1_inj, hcomp_aut _ _ hsw hg1, by decide⟩
  have hfix0 : ∀ j : Fin 10, j ≠ 0 → ∃ π : Fin 10 → Fin 10,
      (∀ x, pet (x ∘ π) = pet x) ∧ π 0 = 0 ∧ (π j = 1 ∨ π j = 2) := by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact ⟨id, fun _ => rfl, rfl, Or.inl rfl⟩
    · exact ⟨id, fun _ => rfl, rfl, Or.inr rfl⟩
    · exact ⟨r0, hr0, by decide, Or.inr (by decide)⟩
    · exact ⟨r0, hr0, by decide, Or.inl (by decide)⟩
    · exact ⟨r0 ∘ r0, hcomp_aut _ _ hr0 hr0, by decide, Or.inl (by decide)⟩
    · exact ⟨r0 ∘ r0 ∘ r0, hcomp_aut _ _ hr0 (hcomp_aut _ _ hr0 hr0), by decide, Or.inr (by decide)⟩
    · exact ⟨r0 ∘ r0 ∘ r0 ∘ r0 ∘ r0,
        hcomp_aut _ _ hr0 (hcomp_aut _ _ hr0 (hcomp_aut _ _ hr0 (hcomp_aut _ _ hr0 hr0))),
        by decide, Or.inr (by decide)⟩
    · exact ⟨r0 ∘ r0, hcomp_aut _ _ hr0 hr0, by decide, Or.inr (by decide)⟩
    · exact ⟨r0 ∘ r0 ∘ r0 ∘ r0,
        hcomp_aut _ _ hr0 (hcomp_aut _ _ hr0 (hcomp_aut _ _ hr0 hr0)),
        by decide, Or.inr (by decide)⟩
  have hgetD_def : ∀ (x : Fin 10 → Bool) (k : ℕ), 10 ≤ k → (List.ofFn x).getD k false = false :=
    fun x k hk => List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; exact hk)
  -- Analyze the first gate g0 of the minimal circuit C.
  cases hgates : C.gates with
  | nil => exact hCne hgates
  | cons g0 rest =>
    have hg0 : g0 ∈ C.gates := by rw [hgates]; exact List.mem_cons_self ..
    obtain ⟨hop, hlen⟩ := hC g0 hg0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · -- First gate is AND.
      cases hin : g0.inputs with
      | nil =>
        exact helim_true g0 rest hgates (fun _ => by simp [hop, hin, heval_and])
      | cons a xs =>
        cases xs with
        | nil =>
          by_cases ha : a < 10
          · exact helim_wire g0 rest hgates a (Or.inl ha) (fun _ => by simp [hop, hin, heval_and])
          · exact helim_wire g0 rest hgates (10 + rest.length) (Or.inr le_rfl)
              (fun x => by
                simp only [hop, hin, heval_and, List.map_cons, List.map_nil, List.all_cons,
                  List.all_nil, Bool.and_true, id_eq]
                rw [hgetD_def x a (by omega), hgetD_def x (10 + rest.length) (by omega)])
        | cons b ys =>
          cases ys with
          | cons _ _ => simp [hin] at hlen
          | nil =>
            by_cases ha : a < 10
            · by_cases hb : b < 10
              · by_cases hab : a = b
                · subst hab
                  exact helim_wire g0 rest hgates a (Or.inl ha)
                    (fun _ => by simp [hop, hin, heval_and])
                · let ia : Fin 10 := ⟨a, ha⟩
                  let ib : Fin 10 := ⟨b, hb⟩
                  have hiab : ia ≠ ib := fun h => hab (congrArg Fin.val h)
                  obtain ⟨π1, hπ1inj, hπ1aut, hπ1a⟩ := hsend0 ia
                  have hne0 : π1 ib ≠ 0 := by rw [← hπ1a]; exact fun h => hiab (hπ1inj h.symm)
                  obtain ⟨π2, hπ2aut, hπ20, hπ2b⟩ := hfix0 (π1 ib) hne0
                  let π : Fin 10 → Fin 10 := π2 ∘ π1
                  have hπaut : ∀ x, pet (x ∘ π) = pet x := hcomp_aut π2 π1 hπ2aut hπ1aut
                  obtain ⟨hDfan, hDsize, hDeval⟩ := hrelabel π hπaut C hC hCeval
                  let D : Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (remap π)⟩, remap π C.output⟩
                  have hD19 : D.size ≤ 19 := by rw [hDsize]; exact hC19
                  have hDhead : D.gates.head? = some ⟨GateOp.and, [0, (π ib).val]⟩ := by
                    simp only [D, hgates, List.map_cons, List.head?_cons, hop, hin,
                      List.map_cons, List.map_nil, remap, ha, hb, ↓reduceDIte]
                    have h0val : (π ia).val = 0 := by simp [π, hπ1a, hπ20]
                    rw [h0val]
                  rcases hπ2b with hb1 | hb2
                  · have hbval : (π ib).val = 1 := by simp [π, hb1]
                    rw [hbval] at hDhead
                    exact hand ⟨D, hDfan, hD19, hDhead, hDeval⟩
                  · have hbval : (π ib).val = 2 := by simp [π, hb2]
                    rw [hbval] at hDhead
                    exact hnonedge ⟨D, hDfan, hD19, Or.inl hDhead, hDeval⟩
              · exact helim_wire g0 rest hgates (10 + rest.length) (Or.inr le_rfl)
                  (fun x => by
                    simp only [hop, hin, heval_and, List.map_cons, List.map_nil, List.all_cons,
                      List.all_nil, Bool.and_true, id_eq]
                    rw [hgetD_def x b (by omega), Bool.and_false, hgetD_def x (10 + rest.length) (by omega)])
            · exact helim_wire g0 rest hgates (10 + rest.length) (Or.inr le_rfl)
                (fun x => by
                  simp only [hop, hin, heval_and, List.map_cons, List.map_nil, List.all_cons,
                    List.all_nil, Bool.and_true, id_eq]
                  rw [hgetD_def x a (by omega), Bool.false_and, hgetD_def x (10 + rest.length) (by omega)])
    · -- First gate is OR.
      cases hin : g0.inputs with
      | nil =>
        exact helim_wire g0 rest hgates (10 + rest.length) (Or.inr le_rfl)
          (fun x => by
            simp only [hop, hin, heval_or, List.map_nil, List.any_nil]
            exact (hgetD_def x (10 + rest.length) (by omega)).symm)
      | cons a xs =>
        cases xs with
        | nil =>
          by_cases ha : a < 10
          · exact helim_wire g0 rest hgates a (Or.inl ha) (fun _ => by simp [hop, hin, heval_or])
          · exact helim_wire g0 rest hgates (10 + rest.length) (Or.inr le_rfl)
              (fun x => by
                simp only [hop, hin, heval_or, List.map_cons, List.map_nil, List.any_cons,
                  List.any_nil, Bool.or_false, id_eq]
                rw [hgetD_def x a (by omega), hgetD_def x (10 + rest.length) (by omega)])
        | cons b ys =>
          cases ys with
          | cons _ _ => simp [hin] at hlen
          | nil =>
            by_cases ha : a < 10
            · by_cases hb : b < 10
              · by_cases hab : a = b
                · subst hab
                  exact helim_wire g0 rest hgates a (Or.inl ha)
                    (fun _ => by simp [hop, hin, heval_or])
                · let ia : Fin 10 := ⟨a, ha⟩
                  let ib : Fin 10 := ⟨b, hb⟩
                  have hiab : ia ≠ ib := fun h => hab (congrArg Fin.val h)
                  obtain ⟨π1, hπ1inj, hπ1aut, hπ1a⟩ := hsend0 ia
                  have hne0 : π1 ib ≠ 0 := by rw [← hπ1a]; exact fun h => hiab (hπ1inj h.symm)
                  obtain ⟨π2, hπ2aut, hπ20, hπ2b⟩ := hfix0 (π1 ib) hne0
                  let π : Fin 10 → Fin 10 := π2 ∘ π1
                  have hπaut : ∀ x, pet (x ∘ π) = pet x := hcomp_aut π2 π1 hπ2aut hπ1aut
                  obtain ⟨hDfan, hDsize, hDeval⟩ := hrelabel π hπaut C hC hCeval
                  let D : Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (remap π)⟩, remap π C.output⟩
                  have hD19 : D.size ≤ 19 := by rw [hDsize]; exact hC19
                  have hDhead : D.gates.head? = some ⟨GateOp.or, [0, (π ib).val]⟩ := by
                    simp only [D, hgates, List.map_cons, List.head?_cons, hop, hin,
                      List.map_cons, List.map_nil, remap, ha, hb, ↓reduceDIte]
                    have h0val : (π ia).val = 0 := by simp [π, hπ1a, hπ20]
                    rw [h0val]
                  rcases hπ2b with hb1 | hb2
                  · have hbval : (π ib).val = 1 := by simp [π, hb1]
                    rw [hbval] at hDhead
                    exact hor ⟨D, hDfan, hD19, hDhead, hDeval⟩
                  · have hbval : (π ib).val = 2 := by simp [π, hb2]
                    rw [hbval] at hDhead
                    exact hnonedge ⟨D, hDfan, hD19, Or.inr hDhead, hDeval⟩
              · exact helim_wire g0 rest hgates a (Or.inl ha)
                  (fun x => by
                    simp only [hop, hin, heval_or, List.map_cons, List.map_nil, List.any_cons,
                      List.any_nil, Bool.or_false, id_eq]
                    rw [hgetD_def x b (by omega), Bool.or_false])
            · by_cases hb : b < 10
              · exact helim_wire g0 rest hgates b (Or.inl hb)
                  (fun x => by
                    simp only [hop, hin, heval_or, List.map_cons, List.map_nil, List.any_cons,
                      List.any_nil, Bool.or_false, id_eq]
                    rw [hgetD_def x a (by omega), Bool.false_or])
              · exact helim_wire g0 rest hgates (10 + rest.length) (Or.inr le_rfl)
                  (fun x => by
                    simp only [hop, hin, heval_or, List.map_cons, List.map_nil, List.any_cons,
                      List.any_nil, Bool.or_false, id_eq]
                    rw [hgetD_def x a (by omega), hgetD_def x b (by omega), Bool.or_false,
                        hgetD_def x (10 + rest.length) (by omega)])
    · -- First gate is NOT.
      cases hin : g0.inputs with
      | nil =>
        exact helim_true g0 rest hgates (fun _ => by simp [hop, hin, heval_not])
      | cons a xs =>
        by_cases ha : a < 10
        · -- Normalize first gate to ⟨.not, [a]⟩, then map a ↦ 0.
          let C1 : Circuit := ⟨⟨GateOp.not, [a]⟩ :: rest, C.output⟩
          have hC1fan : FanInTwo C1 := by
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hmem
            · simp
            · exact hC g (by rw [hgates]; exact List.mem_cons_of_mem _ hmem)
          have hC1size : C1.size = C.size := by simp [hcsize, C1, hgates]
          have hC1eval : ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = pet x := by
            intro x
            rw [← hCeval x]
            simp only [hceval, hcwires, C1, hgates, List.foldl_cons, step, hop, hin,
              heval_not, List.map_cons, List.headD_cons]
          obtain ⟨π, _, hπaut, hπa⟩ := hsend0 ⟨a, ha⟩
          obtain ⟨hDfan, hDsize, hDeval⟩ := hrelabel π hπaut C1 hC1fan hC1eval
          let D : Circuit := ⟨C1.gates.map fun g => ⟨g.op, g.inputs.map (remap π)⟩, remap π C1.output⟩
          have hD19 : D.size ≤ 19 := by rw [hDsize, hC1size]; exact hC19
          have hDhead : D.gates.head? = some ⟨GateOp.not, [0]⟩ := by
            simp only [D, C1, List.map_cons, List.head?_cons, List.map_nil, remap, ha, ↓reduceDIte]
            have h0val : (π ⟨a, ha⟩).val = 0 := by simp [hπa]
            rw [h0val]
          exact hnot ⟨D, hDfan, hD19, hDhead, hDeval⟩
        · exact helim_true g0 rest hgates
            (fun x => by
              simp only [hop, hin, heval_not, List.map_cons, List.headD_cons]
              rw [hgetD_def x a (by omega)]; rfl)
