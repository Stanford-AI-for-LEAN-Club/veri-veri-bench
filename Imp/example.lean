import Imp.parser

namespace Imp

-- (x+2) * (y-3) + 1
-- AST:
--                  (+)
--                 /   \
--               (*)    1
--              /   \
--            (+)   (-)
--           /  \   /  \
--          x    2 y    3
def _simple_arith_example: Aexp :=
  Aexp.add (Aexp.mul (Aexp.add (Aexp.var "x") (Aexp.const 2)) (Aexp.sub (Aexp.var "y") (Aexp.const 3))) (Aexp.const 1)

-- x := 0; i := 1; while (i <= n) do {x := (x + i); i := (i + 1)}; n := 0; i := 0
-- AST:
--                       (;)
--                      /   \
--                x := 0    (;)
--                         /   \
--                   i := 1    (;)
--                            /   \
--                    while(i<=n)  (;)
--                        |       /   \
--                       (;)  n := 0  i := 0
--                      /   \
--               x := x+i  i := i+1
def my_program : String :=
  "x := 0; i := 1; while (i <= n) do {x := (x + i); i := (i + 1)}; n := 0; i := 0"

#eval parseComAllStr ["x", "i", "n"] my_program

def my_compiled_program : Com := Imp.Com.comp
  (Imp.Com.assign "x" (Imp.Aexp.const 0)) (Imp.Com.comp (Imp.Com.assign "i" (Imp.Aexp.const 1))
  (Imp.Com.comp (Imp.Com.while (Imp.Bexp.le (Imp.Aexp.var "i") (Imp.Aexp.var "n"))
  (Imp.Com.comp (Imp.Com.assign "x" (Imp.Aexp.add (Imp.Aexp.var "x") (Imp.Aexp.var "i")))
  (Imp.Com.assign "i" (Imp.Aexp.add (Imp.Aexp.var "i") (Imp.Aexp.const 1)))))
  (Imp.Com.comp (Imp.Com.assign "n" (Imp.Aexp.const 0)) (Imp.Com.assign "i" (Imp.Aexp.const 0)))))

def zero_state : State := fun _ => 0

def initial_state (n : ℤ) : State := zero_state.assign "n" n

def final_state (x : ℤ) : State := zero_state.assign "x" x

def loopBody : Com :=
  Com.comp
    (Com.assign "x" (Aexp.add (Aexp.var "x") (Aexp.var "i")))
    (Com.assign "i" (Aexp.add (Aexp.var "i") (Aexp.const 1)))

def loopStep (σ : State) : State :=
  let σ1 := σ.assign "x" (Aexp.eval σ (Aexp.add (Aexp.var "x") (Aexp.var "i")))
  σ1.assign "i" (Aexp.eval σ1 (Aexp.add (Aexp.var "i") (Aexp.const 1)))

def loopIter : Nat → State → State
  | 0, σ => σ
  | n + 1, σ => loopIter n (loopStep σ)

def loopState (n i : Nat) (x : ℤ) : State :=
  ((initial_state (n : ℤ)).assign "x" x).assign "i" (i : ℤ)

def loopStart (n : Nat) : State :=
  loopState n 1 0

lemma loopState_x (n i : Nat) (x : ℤ) : loopState n i x "x" = x := by
  simp [loopState, State.assign]

lemma loopState_i (n i : Nat) (x : ℤ) : loopState n i x "i" = (i : ℤ) := by
  simp [loopState, State.assign]

lemma loopState_n (n i : Nat) (x : ℤ) : loopState n i x "n" = (n : ℤ) := by
  simp [loopState, initial_state, State.assign]

lemma loopStep_x (σ : State) : loopStep σ "x" = σ "x" + σ "i" := by
  simp [loopStep, State.assign, Aexp.eval]

lemma loopStep_i (σ : State) : loopStep σ "i" = σ "i" + 1 := by
  simp [loopStep, State.assign, Aexp.eval]

lemma loopStep_n (σ : State) : loopStep σ "n" = σ "n" := by
  simp [loopStep, State.assign, Aexp.eval]

lemma loopStep_other (σ : State) {Y : Loc} (hYx : Y ≠ "x") (hYi : Y ≠ "i") :
    loopStep σ Y = σ Y := by
  simp [loopStep, State.assign, hYx, hYi]

lemma loopIter_other (k : Nat) (σ : State) {Y : Loc} (hYx : Y ≠ "x") (hYi : Y ≠ "i") :
    loopIter k σ Y = σ Y := by
  induction k generalizing σ with
  | zero =>
      simp [loopIter]
  | succ k ih =>
      simp [loopIter, loopStep_other (σ:=σ) hYx hYi, ih]

lemma loopStep_loopState (n i : Nat) (x : ℤ) :
    loopStep (loopState n i x) = loopState n (i + 1) (x + (i : ℤ)) := by
  funext Y
  by_cases hI : Y = "i"
  · simp [loopStep, loopState, State.assign, hI, Aexp.eval]
  · by_cases hX : Y = "x"
    · simp [loopStep, loopState, State.assign, hX, Aexp.eval]
    · simp [loopStep, loopState, State.assign, hI, hX]

lemma loopIter_i (k : Nat) (σ : State) :
    loopIter k σ "i" = σ "i" + (k : ℤ) := by
  induction k generalizing σ with
  | zero =>
      simp [loopIter]
  | succ k ih =>
      simp only [loopIter, ih, loopStep_i, Int.add_assoc, Nat.cast_add, Nat.cast_one, add_right_inj]
      exact Int.add_comm 1 ↑k

lemma loopIter_n (k : Nat) (σ : State) :
    loopIter k σ "n" = σ "n" := by
  induction k generalizing σ with
  | zero =>
      simp [loopIter]
  | succ k ih =>
      simp [loopIter, loopStep_n, ih]

lemma terminate_loopBody (σ : State) :
    Com.terminate σ loopBody (loopStep σ) := by
  dsimp [loopBody, loopStep]
  set σ1 := σ.assign "x" (Aexp.eval σ (Aexp.add (Aexp.var "x") (Aexp.var "i"))) with hσ1
  simp [terminate_comp, σ1]

lemma terminate_while_from (n i k : Nat)
    (x : ℤ)
    (hk : k = n + 1 - i) :
    Com.terminate (loopState n i x)
      (Com.while (Bexp.le (Aexp.var "i") (Aexp.var "n")) loopBody)
      (loopIter k (loopState n i x)) := by
  induction k generalizing n i x with
  | zero =>
      have hni : n + 1 ≤ i := by
        omega
      have hi_gt_n : (n : ℤ) < (i : ℤ) := by
        exact_mod_cast hni
      have hnot : ¬ ((loopState n i x "i") ≤ (loopState n i x "n")) := by
        have hi_gt_n' :
            (loopState n i x "i") > (loopState n i x "n") := by
          simpa [loopState_i, loopState_n] using hi_gt_n
        exact not_le_of_gt hi_gt_n'
      have hb :
          Bexp.eval (loopState n i x) (Bexp.le (Aexp.var "i") (Aexp.var "n")) = Bool.false := by
        have hdec : decide ((loopState n i x "i") ≤ (loopState n i x "n")) = false :=
          (decide_eq_false_iff_not).2 hnot
        simpa [Bexp.eval, Aexp.eval, loopState_i, loopState_n] using hdec
      simpa using
        (Com.terminate.while_false (b:=Bexp.le (Aexp.var "i") (Aexp.var "n"))
          (σ:=loopState n i x) (c:=loopBody) hb)
  | succ k ih =>
      have hi_le_n : i ≤ n := by
        omega
      have htrue :
          Bexp.eval (loopState n i x) (Bexp.le (Aexp.var "i") (Aexp.var "n")) = Bool.true := by
        have hle : (loopState n i x "i") ≤ (loopState n i x "n") := by
          simp only [loopState_i, loopState_n, Nat.cast_le]; exact hi_le_n
        simpa [Bexp.eval, Aexp.eval, loopState_i, loopState_n, hle]
      have hk' : k = n + 1 - (i + 1) := by
        omega
      have hbody : Com.terminate (loopState n i x) loopBody (loopStep (loopState n i x)) :=
        terminate_loopBody (loopState n i x)
      have hstate :
          loopStep (loopState n i x) = loopState n (i + 1) (x + (i : ℤ)) := by
        funext Y
        simp [loopStep, loopState, State.assign, Aexp.eval]
        by_cases hI : Y = "i"
        · simp [hI]
        · by_cases hX : Y = "x"
          · simp [hX]
          · simp [hI, hX]
      have hrec :
          Com.terminate (loopStep (loopState n i x))
            (Com.while (Bexp.le (Aexp.var "i") (Aexp.var "n")) loopBody)
            (loopIter k (loopStep (loopState n i x))) := by
        simpa [hstate] using (ih (n:=n) (i:=i+1) (x:=x + (i : ℤ)) hk')
      simpa [loopIter] using
        (Com.terminate.while_true (b:=Bexp.le (Aexp.var "i") (Aexp.var "n"))
          (ρ:=loopState n i x) (σ:=loopStep (loopState n i x))
          (τ:=loopIter k (loopStep (loopState n i x)))
          (c:=loopBody) htrue hbody hrec)

lemma loopIter_x_state (n i k : Nat) (x : ℤ) :
    loopIter k (loopState n i x) "x" =
      x + ∑ j ∈ Finset.range k, ((i + j : Nat) : ℤ) := by
  induction k generalizing n i x with
  | zero =>
      simp [loopIter, loopState_x]
  | succ k ih =>
      have hi :
          loopIter k (loopState n i x) "i" = (i : ℤ) + (k : ℤ) := by
        simpa [loopState_i] using (loopIter_i k (loopState n i x))
      have hsum :
          ∑ j ∈ Finset.range k, ((i + 1 + j : Nat) : ℤ) =
            (∑ j ∈ Finset.range k, ((i + j : Nat) : ℤ)) + (k : ℤ) := by
        classical
        calc
          ∑ j ∈ Finset.range k, ((i + 1 + j : Nat) : ℤ)
              = ∑ j ∈ Finset.range k, (((i + j : Nat) : ℤ) + 1) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  simp [Nat.add_left_comm, Nat.add_comm, Int.add_assoc]
          _ = (∑ j ∈ Finset.range k, ((i + j : Nat) : ℤ)) + ∑ j ∈ Finset.range k, (1 : ℤ) := by
                  simp [Finset.sum_add_distrib]
          _ = (∑ j ∈ Finset.range k, ((i + j : Nat) : ℤ)) + (k : ℤ) := by
                  simp [Finset.sum_const]
      -- unfold one iteration and rewrite with the shifted state
      simp [loopIter, loopStep_loopState, ih,
        Finset.sum_range_succ, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      -- finish the arithmetic rearrangement
      have hsum' :
          ∑ x ∈ Finset.range k, ((i : ℤ) + ((x : ℤ) + 1)) =
            (∑ x ∈ Finset.range k, ((i : ℤ) + (x : ℤ))) + (k : ℤ) := by
        classical
        calc
          ∑ x ∈ Finset.range k, ((i : ℤ) + ((x : ℤ) + 1))
              = ∑ x ∈ Finset.range k, (((i : ℤ) + (x : ℤ)) + 1) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  simp [Int.add_assoc]
          _ = (∑ x ∈ Finset.range k, ((i : ℤ) + (x : ℤ))) + ∑ x ∈ Finset.range k, (1 : ℤ) := by
                  simp [Finset.sum_add_distrib]
          _ = (∑ x ∈ Finset.range k, ((i : ℤ) + (x : ℤ))) + (k : ℤ) := by
                  simp [Finset.sum_const]
      -- now reorder additions
      simp [hsum', Int.add_left_comm, Int.add_comm]

lemma loopIter_x_start (n : Nat) :
    ∀ k, loopIter k (loopStart n) "x" =
      (∑ i ∈ Finset.range (k + 1), (i : ℤ)) := by
  intro k
  -- use the generalized lemma with i=1 and x=0
  have h :=
    (loopIter_x_state n 1 k 0)
  -- simplify the right-hand side to the desired sum
  have hsum :
      ∑ x ∈ Finset.range k, ((x : ℤ) + 1) =
        (∑ x ∈ Finset.range k, (x : ℤ)) + (k : ℤ) := by
    classical
    calc
      ∑ x ∈ Finset.range k, ((x : ℤ) + 1)
          = (∑ x ∈ Finset.range k, (x : ℤ)) + ∑ x ∈ Finset.range k, (1 : ℤ) := by
              simp [Finset.sum_add_distrib]
      _ = (∑ x ∈ Finset.range k, (x : ℤ)) + (k : ℤ) := by
              simp [Finset.sum_const]
  calc
    loopIter k (loopStart n) "x"
        = ∑ x ∈ Finset.range k, ((x : ℤ) + 1) := by
            simpa [loopStart, loopState_x, Int.add_assoc, Int.add_left_comm, Int.add_comm] using h
    _ = (∑ x ∈ Finset.range k, (x : ℤ)) + (k : ℤ) := by
            simp [hsum]
    _ = (∑ i ∈ Finset.range (k + 1), (i : ℤ)) := by
            symm
            simp [Finset.sum_range_succ]

theorem my_program_halts (n : ℕ) : Com.halt (some (initial_state n)) my_compiled_program := by
  -- Build a concrete terminating run.
  -- Let σ0 be the initial state, then execute the comp chain.
  dsimp [Com.halt, my_compiled_program]
  -- Provide a final state witnessing termination.
  let σ0 : State := initial_state n
  let σ1 : State := σ0.assign "x" 0
  let σ2 : State := σ1.assign "i" 1
  let σ3 : State := loopIter n (loopStart n)
  let σ4 : State := σ3.assign "n" 0
  let σ5 : State := σ4.assign "i" 0
  refine ⟨σ5, ?_⟩
  -- Now build the terminate derivation.
  refine Com.terminate.comp (σ:=σ1) ?h1 ?hrest
  · -- x := 0
    simp [σ0, σ1, Aexp.eval]
  · refine Com.terminate.comp (σ:=σ2) ?h2 ?hrest2
    · -- i := 1
      simp [σ1, σ2, Aexp.eval]
    · refine Com.terminate.comp (σ:=σ3) ?h3 ?hrest3
      · -- while loop terminates in n iterations
        -- Align σ2 with loopStart n 1
        have hσ2 : σ2 = loopStart n := by
          rfl
        simpa [hσ2, σ3] using (terminate_while_from n 1 n 0 (by omega))
      · refine Com.terminate.comp (σ:=σ4) ?h4 ?h5
        · -- n := 0
          simp [σ3, σ4, Aexp.eval]
        · -- i := 0
          simp [σ4, σ5, Aexp.eval]

theorem my_program_output (n : ℕ) :
    my_compiled_program.output (initial_state (n : ℤ)) =
      (final_state (∑ i ∈ Finset.range (n + 1), (i : ℤ))) := by
  -- Use termination uniqueness to identify the output state.
  -- Build the same terminating run as in my_program_halts.
  let σ0 : State := initial_state n
  let σ1 : State := σ0.assign "x" 0
  let σ2 : State := σ1.assign "i" 1
  let σ3 : State := loopIter n (loopStart n)
  let σ4 : State := σ3.assign "n" 0
  let σ5 : State := σ4.assign "i" 0
  have hterm :
      Com.terminate σ0 my_compiled_program σ5 := by
    -- same derivation as above
    refine Com.terminate.comp (σ:=σ1) ?h1 ?hrest
    · simp [σ1, σ0, Aexp.eval]
    · refine Com.terminate.comp (σ:=σ2) ?h2 ?hrest2
      · simp [σ1, σ2, σ0, Aexp.eval]
      · refine Com.terminate.comp (σ:=σ3) ?h3 ?hrest3
        · have hσ2 : σ2 = loopStart n := by rfl
          simpa [hσ2, σ3] using (terminate_while_from n 1 n 0 (by omega))
        · refine Com.terminate.comp (σ:=σ4) ?h4 ?h5
          · simp [σ3, σ4, Aexp.eval]
          · simp [σ4, σ5, Aexp.eval]
  -- Identify the output with the final state.
  have hout : Com.output (some σ0) my_compiled_program = some σ5 := by
    simpa using (terminate_output hterm)
  -- Compute σ5 "x" and show it matches the desired final state.
  have hx : σ5 "x" = (∑ i ∈ Finset.range (n + 1), (i : ℤ)) := by
    -- σ5 has the same x as σ3; assignments to n and i don't affect x.
    simp [σ5, σ4, σ3, loopIter_x_start n, State.assign]
  have hσ5 : σ5 = final_state (∑ i ∈ Finset.range (n + 1), (i : ℤ)) := by
    funext Y
    by_cases hYx : Y = "x"
    · simp [final_state, σ5, σ4, σ3, State.assign, hYx, hx]
    · by_cases hYi : Y = "i"
      · simp [final_state, σ5, σ4, State.assign, hYi, zero_state]
      · by_cases hYn : Y = "n"
        · simp [final_state, σ5, σ4, State.assign, hYn, zero_state]
        · have : σ3 Y = 0 := by
            -- Y is neither x nor i, so loopIter doesn't change it; then it comes
            -- from initial_state.
            have hYx' : Y ≠ "x" := hYx
            have hYi' : Y ≠ "i" := hYi
            simpa [σ3, loopStart, loopState, initial_state, zero_state, State.assign, hYx, hYi, hYn]
            using (loopIter_other n (loopStart n) (Y:=Y) hYx' hYi')
          simp [final_state, σ5, σ4, σ3, zero_state, State.assign, hYx, hYi, hYn, this]
  -- Conclude.
  change Com.output (some σ0) my_compiled_program =
    some (final_state (∑ i ∈ Finset.range (n + 1), ↑i))
  simp [hout, hσ5]

end Imp
