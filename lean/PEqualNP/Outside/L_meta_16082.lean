import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_16082 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 1 && x 6)) 13 := by
  let circuit : Circuit := ⟨[
    ⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 5]⟩,
    ⟨.or, [2, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [3, 9]⟩,
    ⟨.and, [8, 7]⟩, ⟨.and, [6, 11]⟩,
    ⟨.and, [12, 4]⟩, ⟨.and, [10, 0]⟩,
    ⟨.or, [13, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · dsimp only [circuit]
    decide +kernel
