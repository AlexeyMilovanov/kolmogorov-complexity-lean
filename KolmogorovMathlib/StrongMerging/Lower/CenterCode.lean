import KolmogorovMathlib.StrongMerging.Coding
import KolmogorovMathlib.StrongMerging.Lower.CubeCollision

/-!
# The sharp lower bound: the generic game interface and the center occurrence code

Blueprint node L22 (`centerOccurrenceCode`) of the formalization of `sublinear-merging.tex`
(paper: proof of Lemma `lem:ham-reservoir`, lines ~1478-1490; blueprint: "L22--L23", lines
~4784-4806), together with the shared interface of the moving-sphere reservoir (node L23) and of
the sharp parameters (nodes L24, L25):

* `IsCubePartitionProgram M p`: `p` is an exact partition program of the `M`-cube for the
  canonical total interpreter `universalDecompressor` (it need not halt off the cube);
* `heavyTheta` and `ReservoirInequalities`: the heavy-cell constant
  `θ = 2^δ (V(M, h - 1) 2^(-ℓ) + β^h)` and the four game inequalities of the paper, in the exact
  integer forms of the generic game where they are integer statements;
* `centerOccurrenceCode` (L22): for a computable, prefix-monotone stream of emitted centers,
  indexed by a list of numeric parameters bounded by a fixed polynomial `(n + 2)^B`, the `j`th
  emitted center has `C(z) ≤ log₂ (j + 1) + c ⌈log₂ (n + 2)⌉`, with `c` depending only on the
  machine, on `B` and on the number of parameters.  The decoder waits only for the `j`th
  occurrence; it never recognizes the final center, and off-range ordinals diverge.
  The program is the occurrence packet `occurrencePacket ps j` (a count field, the parameters as
  self-delimiting numeric fields, the ordinal in binary), parsed by `parseOccurrence`
  (`readFields`); the decoder is `occurrenceDecoder` (`Nat.rfindOpt` over the stages).
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### The generic game interface -/

/-- **Exact partition programs of the `M`-cube** (paper: "partition program", lines 1365-1369).
On every `M`-word `y` the canonical total interpreter runs `p` to the canonical code of a finite
set `Q ∋ y` of `M`-words, and it prints the same code on every member of `Q`.  The program need
not halt on words of other lengths; every globally total partition program is of this form. -/
def IsCubePartitionProgram (M : ℕ) (p : BitString) : Prop :=
  ∀ y : BitString, y.length = M → ∃ Q : Finset BitString,
    produces universalDecompressor p y (canonicalFiniteSetCode Q) ∧ y ∈ Q ∧
      ∀ y' ∈ Q, y'.length = M ∧ produces universalDecompressor p y' (canonicalFiniteSetCode Q)

/-- The heavy-cell constant `θ = 2^δ (V(M, h - 1) 2^(-ℓ) + β^h)` of the moving-sphere game, with
`β = 2 √(ρ (1 - ρ))`, `ρ = R / M` (`collisionBeta`).  It bounds the heavy-pair probability of
every exact partition (node L09, `partitionHeavyBound`). -/
noncomputable def heavyTheta (M R ℓ δ h : ℕ) : ℝ :=
  2 ^ δ * ((hammingVol M (h - 1) : ℝ) / 2 ^ ℓ + collisionBeta M R ^ h)

/-- **The four game inequalities** of Lemma `lem:ham-reservoir` (`eq:ham-game-density`,
`eq:ham-game-heavy`, `eq:ham-game-charge`, `eq:ham-game-arrivals`), for the sphere size
`N = (M choose R)`: the density inequality `2^K + (K+τ+1) 2^(K+τ) ≤ 2^M / 256`, the heavy
inequality `2^(S+1) θ ≤ 1/256`, the charge inequality `(K+τ+1) 2^(τ-δ) ≤ 1` and the arrival
inequality `2^(S+1) ≤ 2^K / N`.  The density, charge and arrival inequalities are stated in
cross-multiplied integer form (the forms of the generic game's `GameHyp`); the heavy one is real. -/
structure ReservoirInequalities (M R K S τ ℓ δ h : ℕ) : Prop where
  /-- Density: `256 (2^K + (K+τ+1) 2^(K+τ)) ≤ 2^M`. -/
  density : 256 * (2 ^ K + (K + τ + 1) * 2 ^ (K + τ)) ≤ 2 ^ M
  /-- Heavy cells: `2^(S+1) θ ≤ 1/256`. -/
  heavy : (2 : ℝ) ^ (S + 1) * heavyTheta M R ℓ δ h ≤ 1 / 256
  /-- Charge: `(K+τ+1) 2^(K+τ) ≤ 2^(K+δ)`. -/
  charge : (K + τ + 1) * 2 ^ (K + τ) ≤ 2 ^ (K + δ)
  /-- Arrivals: `N 2^(S+1) ≤ 2^K`. -/
  arrivals : M.choose R * 2 ^ (S + 1) ≤ 2 ^ K

/-! ### L22: the packet of the occurrence code -/

/-- One step of the packet parser: read the numeric field at the front of the remaining packet
(`numFieldDecode`) and append it to the fields read so far. -/
def readFieldStep (st : List ℕ × BitString) : List ℕ × BitString :=
  (st.1 ++ [(numFieldDecode st.2).1], (numFieldDecode st.2).2)

/-- The packet parser: read `k` numeric fields off the front of `w`, returning the fields (in
order) and the rest of the packet. -/
def readFields (k : ℕ) (w : BitString) : List ℕ × BitString :=
  readFieldStep^[k] ([], w)

/-- Reading the fields of a packet appends them to the accumulator and leaves the body. -/
theorem readFieldStep_iterate_numPacket (acc ks : List ℕ) (body : BitString) :
    readFieldStep^[ks.length] (acc, numPacket ks body) = (acc ++ ks, body) := by
  induction ks generalizing acc with
  | nil => simp [numPacket]
  | cons k ks ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : readFieldStep (acc, numPacket (k :: ks) body) =
        (acc ++ [k], numPacket ks body) := by
      simp [readFieldStep, numPacket]
    rw [hstep, ih]
    simp

/-- **Parsing inverts packing**: reading `|ks|` fields of `numPacket ks body` recovers `ks` and
the body. -/
theorem readFields_numPacket (ks : List ℕ) (body : BitString) :
    readFields ks.length (numPacket ks body) = (ks, body) := by
  simpa [readFields] using readFieldStep_iterate_numPacket [] ks body

/-- The parser step is computable. -/
theorem readFieldStep_computable : Computable readFieldStep :=
  (Computable.list_concat.comp Computable.fst
    (Computable.fst.comp (numFieldDecode_computable.comp Computable.snd))).pair
    (Computable.snd.comp (numFieldDecode_computable.comp Computable.snd))

/-- `readFields` as a primitive recursion on the number of fields. -/
theorem readFields_eq_rec (k : ℕ) (w : BitString) :
    readFields k w = Nat.rec (motive := fun _ => List ℕ × BitString) ([], w)
      (fun _ IH => readFieldStep IH) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [readFields, Function.iterate_succ_apply', ← readFields, ih]

/-- The packet parser is computable in the number of fields and the packet. -/
theorem readFields_computable : Computable₂ readFields := by
  have h := Computable.nat_rec (f := fun p : ℕ × BitString => p.1)
    (g := fun p => (([] : List ℕ), p.2)) (h := fun _ q => readFieldStep q.2)
    Computable.fst ((Computable.const []).pair Computable.snd)
    (readFieldStep_computable.comp (Computable.snd.comp Computable.snd)).to₂
  exact h.of_eq fun p => (readFields_eq_rec p.1 p.2).symm

/-- **The occurrence packet** of node L22: the number of parameters, the parameters, each as a
self-delimiting numeric field (`numPacket`), then the ordinal `j` in binary as the body. -/
def occurrencePacket (ps : List ℕ) (j : ℕ) : BitString :=
  numPacket (ps.length :: ps) (Nat.bits j)

/-- The total parser of occurrence packets: the parameter list and the ordinal. -/
def parseOccurrence (w : BitString) : List ℕ × ℕ :=
  ((readFields (numFieldDecode w).1 (numFieldDecode w).2).1,
    decodeBits (readFields (numFieldDecode w).1 (numFieldDecode w).2).2)

/-- Parsing an occurrence packet recovers the parameters and the ordinal. -/
theorem parseOccurrence_occurrencePacket (ps : List ℕ) (j : ℕ) :
    parseOccurrence (occurrencePacket ps j) = (ps, j) := by
  have h : occurrencePacket ps j = numField ps.length (numPacket ps (Nat.bits j)) := rfl
  simp only [parseOccurrence, h, numFieldDecode_numField, readFields_numPacket,
    decodeBits_natBits]

/-- The occurrence parser is computable. -/
theorem parseOccurrence_computable : Computable parseOccurrence := by
  have hr : Computable fun w : BitString =>
      readFields (numFieldDecode w).1 (numFieldDecode w).2 :=
    readFields_computable.comp (Computable.fst.comp numFieldDecode_computable)
      (Computable.snd.comp numFieldDecode_computable)
  exact (Computable.fst.comp hr).pair (decodeBits_computable.comp (Computable.snd.comp hr))

/-! ### L22: the occurrence decoder -/

/-- **The ordinary partial occurrence decoder** of node L22, for a stream `emit` of emitted
centers: parse the parameters `ps` and the ordinal `j` from the program, search the least stage
`s` at which the stream `emit ps s` has a `j`th entry (`Nat.rfindOpt`) and output that entry.
The condition is ignored.  Off-range ordinals diverge; the final center is never recognized. -/
def occurrenceDecoder (emit : List ℕ → ℕ → List BitString) : Map := fun pr =>
  Nat.rfindOpt fun s => (emit (parseOccurrence pr.1).1 s)[(parseOccurrence pr.1).2]?

/-- The occurrence decoder is partial recursive when the stream is computable. -/
theorem occurrenceDecoder_partrec (emit : List ℕ → ℕ → List BitString)
    (hemit : Computable₂ emit) : isDecompressor (occurrenceDecoder emit) := by
  have hp : Computable fun x : (BitString × BitString) × ℕ => parseOccurrence x.1.1 :=
    parseOccurrence_computable.comp (Computable.fst.comp Computable.fst)
  exact Partrec.rfindOpt (Computable.list_getElem?.comp
    (hemit.comp (Computable.fst.comp hp) Computable.snd) (Computable.snd.comp hp))

/-- A stream growing by appending at each stage grows by appending between any two stages. -/
theorem emit_prefix_of_le {emit : List ℕ → ℕ → List BitString}
    (hmono : ∀ ps s, emit ps s <+: emit ps (s + 1)) (ps : List ℕ) {s t : ℕ} (hst : s ≤ t) :
    emit ps s <+: emit ps t := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih => exact ih.trans (hmono ps t)

/-- An entry of a list is also the entry of every extension of the list. -/
theorem getElem?_eq_some_of_isPrefix {l₁ l₂ : List BitString} (h : l₁ <+: l₂) {j : ℕ}
    {z : BitString} (hz : l₁[j]? = some z) : l₂[j]? = some z := by
  obtain ⟨u, rfl⟩ := h
  have hj : j < l₁.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hz
    exact absurd hz (by simp)
  rw [List.getElem?_append_left hj, hz]

/-- **Soundness of the occurrence decoder**: if the `j`th entry of the stream at some stage is
`z`, the decoder prints `z` from the occurrence packet of `ps` and `j`, under every condition. -/
theorem mem_occurrenceDecoder {emit : List ℕ → ℕ → List BitString}
    (hmono : ∀ ps s, emit ps s <+: emit ps (s + 1)) (ps : List ℕ) (s j : ℕ) (z : BitString)
    (h : (emit ps s)[j]? = some z) (y : BitString) :
    produces (occurrenceDecoder emit) (occurrencePacket ps j) y z := by
  change z ∈ Nat.rfindOpt fun t =>
    (emit (parseOccurrence (occurrencePacket ps j)).1 t)[(parseOccurrence
      (occurrencePacket ps j)).2]?
  rw [parseOccurrence_occurrencePacket, Nat.rfindOpt_mono]
  · exact ⟨s, h⟩
  · intro a m t hmt ha
    exact getElem?_eq_some_of_isPrefix (emit_prefix_of_le hmono ps hmt) ha

/-! ### L22: the length of the occurrence code -/

/-- A natural at most `2^t` has at most `t + 1` binary digits. -/
theorem length_natBits_le_of_le_two_pow {q t : ℕ} (hq : q ≤ 2 ^ t) :
    (Nat.bits q).length ≤ t + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact lt_of_le_of_lt hq (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- The length of one numeric field in front of the rest of a packet. -/
theorem length_numField_eq_add (q : ℕ) (rest : BitString) :
    (numField q rest).length =
      rest.length + ((Nat.bits q).length + 2 * (Nat.bits (Nat.bits q).length).length + 1) := by
  rw [numField, length_totalProgramPairCode]
  omega

/-- A numeric field holding a value at most `2^t` costs at most `3 t + 4` bits. -/
theorem numFieldCost_le_of_le_two_pow {q t : ℕ} (hq : q ≤ 2 ^ t) :
    (Nat.bits q).length + 2 * (Nat.bits (Nat.bits q).length).length + 1 ≤ 3 * t + 4 := by
  have h1 := length_natBits_le_of_le_two_pow hq
  have h2 : (Nat.bits (Nat.bits q).length).length ≤ (Nat.bits q).length := by
    rw [Nat.size_eq_bits_len (Nat.bits q).length]
    exact Nat.size_le.2 Nat.lt_two_pow_self
  omega

/-- A packet of fields, each at most `2^t`, costs at most `3 t + 4` bits per field beyond its
body. -/
theorem length_numPacket_le_of_forall_le_two_pow (t : ℕ) (ks : List ℕ) (body : BitString)
    (hks : ∀ q ∈ ks, q ≤ 2 ^ t) :
    (numPacket ks body).length ≤ body.length + ks.length * (3 * t + 4) := by
  induction ks with
  | nil => simp [numPacket]
  | cons k ks ih =>
    have hk := numFieldCost_le_of_le_two_pow (hks k (by simp))
    have ih' := ih (fun q hq => hks q (by simp [hq]))
    have hlen : (numPacket (k :: ks) body).length = (numPacket ks body).length +
        ((Nat.bits k).length + 2 * (Nat.bits (Nat.bits k).length).length + 1) :=
      length_numField_eq_add k _
    rw [hlen, List.length_cons, add_mul, one_mul]
    generalize ks.length * (3 * t + 4) = X at ih' ⊢
    omega

/-- `(n + 2)^B ≤ 2^(B m)` with `m = ⌈log₂ (n + 2)⌉`. -/
theorem add_two_pow_le_two_pow_headerLog (n B : ℕ) : (n + 2) ^ B ≤ 2 ^ (B * headerLog n) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two (n + 2)) B

/-- **Occurrence-packet length, integer form**: with at most `k` parameters, each at most
`(n + 2)^B`, the packet has at most `|bits j| + (k + 1)(3B + 3k + 4) m` bits,
`m = ⌈log₂ (n + 2)⌉`. -/
theorem length_occurrencePacket_le_nat (B k n : ℕ) (ps : List ℕ) (j : ℕ) (hk : ps.length ≤ k)
    (hps : ∀ q ∈ ps, q ≤ (n + 2) ^ B) :
    (occurrencePacket ps j).length ≤
      (Nat.bits j).length + (k + 1) * (3 * B + 3 * k + 4) * headerLog n := by
  have hm := one_le_headerLog n
  have hfields : ∀ q ∈ ps.length :: ps, q ≤ 2 ^ (B * headerLog n + k) := by
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · calc ps.length ≤ k := hk
        _ ≤ 2 ^ k := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ (B * headerLog n + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · calc q ≤ (n + 2) ^ B := hps q hq
        _ ≤ 2 ^ (B * headerLog n) := add_two_pow_le_two_pow_headerLog n B
        _ ≤ 2 ^ (B * headerLog n + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := length_numPacket_le_of_forall_le_two_pow _ _ (Nat.bits j) hfields
  have h1 : (ps.length :: ps).length * (3 * (B * headerLog n + k) + 4) ≤
      (k + 1) * (3 * B + 3 * k + 4) * headerLog n := by
    rw [List.length_cons, Nat.mul_assoc]
    apply Nat.mul_le_mul (by omega)
    have h3 : 3 * k + 4 ≤ (3 * k + 4) * headerLog n := Nat.le_mul_of_pos_right _ hm
    have h4 : (3 * B + 3 * k + 4) * headerLog n =
        3 * (B * headerLog n) + (3 * k + 4) * headerLog n := by ring
    rw [h4]
    omega
  exact h.trans (Nat.add_le_add_left h1 _)

/-- The binary digits of `j` number at most `log₂ (j + 1) + 1`. -/
theorem length_natBits_le_logb_succ (j : ℕ) :
    ((Nat.bits j).length : ℝ) ≤ Real.logb 2 ((j : ℝ) + 1) + 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have h := bits_length_le_logb_add_one hj
    have h2 : Real.logb 2 (j : ℝ) ≤ Real.logb 2 ((j : ℝ) + 1) :=
      Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hj) (by linarith)
    linarith

/-- **Occurrence-packet length** (node L22): there is a constant `c`, depending only on `B` and
`k`, such that the occurrence packet of at most `k` parameters, each at most `(n + 2)^B`, and of
the ordinal `j` has at most `log₂ (j + 1) + c ⌈log₂ (n + 2)⌉` bits. -/
theorem length_occurrencePacket_le (B k : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (ps : List ℕ) (j : ℕ), ps.length ≤ k → (∀ q ∈ ps, q ≤ (n + 2) ^ B) →
      ((occurrencePacket ps j).length : ℝ) ≤ Real.logb 2 ((j : ℝ) + 1) + c * headerLog n := by
  refine ⟨(k + 1) * (3 * B + 3 * k + 4) + 1, fun n ps j hk hps => ?_⟩
  have h := length_occurrencePacket_le_nat B k n ps j hk hps
  have hb := length_natBits_le_logb_succ j
  have hm : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
  have hcast : ((occurrencePacket ps j).length : ℝ) ≤
      ((Nat.bits j).length : ℝ) + ((k + 1) * (3 * B + 3 * k + 4) : ℕ) * (headerLog n : ℝ) := by
    exact_mod_cast h
  push_cast at hcast ⊢
  nlinarith

/-! ### L22: the center occurrence code -/

/-- **Center occurrence code** (blueprint node L22).  Let `emit ps s` be a computable stream of
emitted centers, indexed by a list `ps` of numeric parameters and a stage `s`, growing by
appending.  Fix a header exponent `B` and a number `k` of parameters.  Then there is a constant
`c` such that for every `n` and every list `ps` of at most `k` parameters, each at most
`(n + 2)^B`, the `j`th entry `z` of the stream (at any stage) satisfies
`C(z) ≤ log₂ (j + 1) + c ⌈log₂ (n + 2)⌉`.

The ordinary partial decoder `occurrenceDecoder` reads the parameter packet and the ordinal `j`
(`occurrencePacket`), searches the least stage at which the stream has a `j`th entry and prints
it; by prefix-monotonicity this entry is `z` (`mem_occurrenceDecoder`).  It never decides whether
a center is the final one, and off-range ordinals diverge. -/
theorem centerOccurrenceCode (V : Map) (hV : isOptimalConditional V)
    (emit : List ℕ → ℕ → List BitString) (hemit : Computable₂ emit)
    (hmono : ∀ ps s, emit ps s <+: emit ps (s + 1)) (B k : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (ps : List ℕ), ps.length ≤ k → (∀ q ∈ ps, q ≤ (n + 2) ^ B) →
      ∀ s j : ℕ, ∀ z : BitString, (emit ps s)[j]? = some z →
        plainC V z ≤ Real.logb 2 (j + 1) + c * headerLog n := by
  obtain ⟨c₀, hc₀⟩ := condC_le_of_decoder V hV (occurrenceDecoder emit)
    (occurrenceDecoder_partrec emit hemit)
  obtain ⟨cl, hcl⟩ := length_occurrencePacket_le B k
  refine ⟨cl + c₀, fun n ps hk hps s j z hz => ?_⟩
  have h1 := hc₀ (occurrencePacket ps j) [] z (mem_occurrenceDecoder hmono ps s j z hz [])
  have h2 := hcl n ps j hk hps
  have hm : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
  have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg c₀
  rw [plainC_eq_condC_nil]
  push_cast
  nlinarith

end Kolmogorov.StrongMerging.Lower
