import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13047

-- The LRAT verifier, circuit model and normalization lemmas below are adapted
-- from the project library. The six gate circuit and its lower bound certificate
-- are for the truth table in the posted statement.

namespace Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end Helpers

namespace LRAT

noncomputable section

def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

inductive Trie where
  | nil : Trie
  | node (v : Option Nat) (l r : Trie) : Trie

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  Trie.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := Trie.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t

def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

theorem All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (r.get _) (l.get _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

theorem All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

theorem All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

theorem All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

theorem All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)

def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

def stop : Cont := fun _ _ _ _ _ _ => false

def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

def fuelW : Nat := 1024

def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e

def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

theorem stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

theorem tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    ·
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    ·
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h

          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

theorem runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

theorem runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

theorem runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

theorem clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

theorem verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

theorem loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

theorem loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

theorem check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

theorem checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end

end LRAT

namespace LRAT.LinkN

open PEqualNP.Outside.L_meta_13047.LRAT

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else if t = 3 then !a else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 4
  not_eq : ∀ j < s, M.op j = 3 → M.s1 j = M.s2 j
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

instance (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j)
  notNot : ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 2

def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2),
    P (ix n s 0 j 3)]

def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)],
   [Q (ix n s 0 j 3), P (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 3), Q (ix n s 3 j r), Q (ix n s 4 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).map fun k =>
    [Q (ix n s 0 j 3), Q (ix n s 1 j k), P (ix n s 2 j k)]

def fNotNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).map fun i =>
    [Q (ix n s 0 j 3), Q (ix n s 0 i 3), Q (ix n s 1 j (n + i))]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l =>
      [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)] ++
        if l = k then [P (ix n s 0 j 3)] else []

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s ++ fNot n s ++ fNotNot n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 2) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 4) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) ∧ ((!(t == 3) || x || a) = true) ∧
    ((!(t == 3) || !x || !a) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7 G8 G9
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  by_cases hlk : l = k
  · rw [if_pos hlk]
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [List.cons_append, List.nil_append, cs_cons, cs_nil, litVal_Q,
      litVal_P, v_s1, v_s2, v_op, v_pad, or_false, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      decide_eq_true_eq, beq_iff_eq]
    by_cases hp : M.pad n j
    · exact Or.inr (Or.inr (Or.inl hp))
    · have := hn.ord j hj hp
      omega
  · rw [if_neg hlk]
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [List.append_nil, cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2,
      v_pad, or_false, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
    by_cases hp : M.pad n j
    · exact Or.inr (Or.inr hp)
    · have := hn.ord j hj hp
      omega

theorem s_fNot : ∀ c ∈ fNot n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fNot, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, rfl⟩ := hc
  have := hv.not_eq j hj
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq]
  omega

theorem s_fNotNot : ∀ c ∈ fNotNot n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fNotNot, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, i, hi, rfl⟩ := hc
  have := hn.notNot j hj i hi
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_op, v_s1, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  tauto

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in

theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h
  · exact s_fNot hv hn c h
  · exact s_fNotNot hv hn c h

end sound

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_13047.Helpers

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | .not, a :: _ => (3, nm n j a, nm n j a)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 4 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_not (n : ℕ) (g : Gate) (j : ℕ) (h : (code n g j).1 = 3) :
    (code n g j).2.1 = (code n g j).2.2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [code]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : FanInTwo C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  not_eq j _ h := code_not n _ j h
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  not_eq j hj h3 := by
    simp only [mv] at h3 ⊢
    by_cases h0 : j = 0
    · rw [if_pos h0] at h3; omega
    · by_cases h1 : j ≤ d
      · simp only [if_neg h0, if_pos h1] at h3 ⊢
        rw [hv.not_eq (j - 1) (by omega) h3]
      · simp only [if_neg h0, if_neg h1] at h3 ⊢
        rw [hv.not_eq j hj h3]
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  not_eq i hi h3 := by
    have := hv.not_eq i hi h3
    simp only [sw]; split_ifs with h
    · subst h; exact this.symm
    · exact this
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      by_cases h3 : M.op i = 3
      · rw [this, hv.not_eq i hi h3]
      · rw [this]; unfold gfun
        simp only [if_neg h3]
        split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgt true fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgt false fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_triv hv hj (by omega)

theorem notnot_triv {i : ℕ} (hi : i < j) (h3 : M.op j = 3) (hi3 : M.op i = 3)
    (he : M.s1 j = n + i) : ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hle := hv.s1_le i (by omega)
  refine copy_tgt hv hj (k := if M.s1 i < n + i then M.s1 i else n + j) (by split_ifs <;> omega)
    fun r hr => ?_
  have e1 : M.sv n j (n + i) r = M.w i r := by
    unfold Model.sv
    simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
      show n + i - n = i by omega]
  rw [hv.w_eq j hj r hr, h3, he, e1, hv.w_eq i (by omega) r hr, hi3]
  simp only [gfun, show ¬ (3 : ℕ) = 0 by omega, show ¬ (3 : ℕ) = 1 by omega, if_true, if_false,
    Bool.not_not]
  unfold Model.sv
  by_cases h6 : M.s1 i < n + i
  · simp only [if_pos h6]
    by_cases h7 : M.s1 i < n
    · simp [h7]
    · simp only [if_neg h7, if_pos (show M.s1 i < n + j by omega)]
  · simp only [if_neg h6, if_neg (show ¬ M.s1 i < n by omega), if_neg (show ¬ n + j < n by omega),
      if_neg (show ¬ n + j < n + j by omega)]

theorem same_src (h3 : M.op j ≠ 3) (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  simp only [if_neg h3]
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have notNot : ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i := by
    intro j hj i hi h3 hi3 he
    exact htriv j hj (fun hp => by have := hp.1; omega) (notnot_triv hv hj hi h3 hi3 he)
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j) := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj (fun h3 => hc (Or.inr ⟨h3, he⟩)) he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨M, hv, {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    notNot := notNot
    used := ?_
    out := ?_ }⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : FanInTwo C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf⟩ := exists_nf ⟨_, hv⟩
  exact ⟨val n s M, enc_sat hrows hM hnf⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc n s (rowFun n f) rows)) :
    ∀ C : Circuit, FanInTwo C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link n s f rows hrows C hC (by omega) hev)

theorem sat_of_check (a : ℕ → Bool) (F : List (List ℕ))
    (h : F.all (fun c => c.any fun l => litVal a l) = true) : FormulaSat F := by
  refine ⟨a, fun c hc => ?_⟩
  have := List.all_eq_true.1 h c hc
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.1 this
  exact ⟨l, hl, hv⟩

end LRAT.LinkN

namespace LRAT.LinkN

open PEqualNP.Outside.L_meta_13047.LRAT

def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

theorem lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

theorem lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

theorem lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (4 * (n + s + 1)) + M.s2 j * 4 + M.op j

def lexB (n s : ℕ) : ℕ := 4 * (n + s + 1) * (n + s + 1)

theorem lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 4 + z1 < K) (hz : z1 < 4)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 4 + z1 < x2 * K + y2 * 4 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (4 * (n + s + 1)) ≤ (n + s) * (4 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (4 * (n + s + 1)) + 4 * (n + s + 1) = 4 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

theorem lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

theorem meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

theorem meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (4 * (n + s + 1)) ≤ M.s1 j * (4 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, if_pos rfl, ↓reduceIte]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, show i ≠ j by omega]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

def xsw (n : ℕ) (M : Model) (j : ℕ) : Model where
  op i := if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i
  s1 i := if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
    else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i
  s2 i := if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
    else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i
  so := tsw n j M.so
  w i r := if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [if_neg h6, if_pos (show k < n + i by omega), if_pos (show k < n + i' by omega),
      xsw, if_neg (show k - n ≠ j by omega), if_neg (show k - n ≠ j + 1 by omega)]

theorem sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
        if_neg (show k - n ≠ j + 1 by omega)]
    · simp only [if_neg h6, if_neg h7]

theorem sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [if_pos rfl, ↓reduceIte]
    unfold Model.sv
    simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      if_neg (show j + 1 ≠ j by omega), if_pos rfl, ↓reduceIte]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [if_neg h1, if_pos rfl, ↓reduceIte]
      unfold Model.sv
      simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
        if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, if_pos rfl, ↓reduceIte]
    · simp only [if_neg h1, if_neg h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
            if_neg (show k - n ≠ j + 1 by omega)]
        · simp only [if_neg h6, if_neg h7]

theorem tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

theorem tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

theorem valid_xsw : Valid n s g R (xsw n M j) where
  op_lt i hi := by
    simp only [xsw]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  not_eq i hi h := by
    simp only [xsw] at h ⊢
    split_ifs at h ⊢ with a b c
    · exact hv.not_eq _ hj h
    · exact hv.not_eq _ (by omega) h
    · rw [hv.not_eq i hi h]
    · exact hv.not_eq i hi h
  s1_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  so_le := tsw_le (by omega) hv.so_le
  w_eq i hi r hr := by
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  out_eq r hr := by
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
theorem ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, if_pos rfl, ↓reduceIte]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, if_neg a, if_pos rfl, ↓reduceIte]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_pos c, tsw_eq_iff c]
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_neg c]
  by_cases h : M.pad n i
  · simp [h, hp.2 h]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

theorem meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

theorem nf_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have notNot : ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i := by
    intro j hj i hi h3 hi3 he
    exact htriv j hj (fun hp => by have := hp.1; omega) (notnot_triv hv hj hi h3 hi3 he)
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j) := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj (fun h3 => hc (Or.inr ⟨h3, he⟩)) he)
    · exact hmin _ (valid_sw hv j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    notNot := notNot
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

theorem lex_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min2 hv hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)

  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 4 → y * 4 + z < 4 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      ·
        have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt hv hj (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (meas2_mv hv hv' hj (Or.inl hnp1))
      · have q0 := hnf.ord j (by omega) hnp
        have q1 := hnf.ord (j + 1) hj hnp1
        have n0 := hv.not_eq j (by omega)
        have n1 := hv.not_eq (j + 1) hj
        have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

theorem exists_nf2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas2 n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  exact ⟨M, hv, nf_of_min2 hv hmin, lex_of_min2 hv hmin⟩

section formula
variable (n s : ℕ)

def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

theorem enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : FanInTwo C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc2 n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc2 n s (rowFun n f) rows)) :
    ∀ C : Circuit, FanInTwo C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link2 n s f rows hrows C hC (by omega) hev)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem size_of_unsat2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc2 n s (rowFun n f) rows)) :
    ∀ t : ℕ, HasCircuitSize n f t → s + 1 ≤ t := by
  rintro t ⟨C, hC, hs, hev⟩
  exact (lower_of_unsat2 n s f rows hrows hU C hC hev).trans hs

end LRAT.LinkN

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity LRAT LRAT.LinkN

def rows : List Nat := [42, 44, 14, 22, 54, 33, 50, 58]

def f (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372970 * 2 ^ 32 + 4004178602) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def table (r : Nat) : Bool := (17215830820324567722 : Nat).testBit r

def formula : List (List Nat) := enc2 6 5 table rows

def keyWords : List Nat := [
  0x142c8540021442684908a1041e83906a0c4160010520941081d0320540880d01201000800ff9fe3fa7f0fd9fa3f27e0fb8003ec7d4fa1f33e47c4f81ef3dc000001ed3d87acf51e93d079cf31e53c8000f19e23c2780ef9de3ba000001dc00076ced1d93b075c000003ac754ea1d33a4744e800000073ce71cd39872ce51c9000000e41c738c714e21c3384704001c037e6f8de9bc3766e8dc8003706dcdb1b53686ccd91b10006c0d79ae35a6b0d59aa352000d41a734c694d200000068cd10000006840000034067ccf19d33866c0019a332660cb99632a000ca193324644c818f000638c698c316628c480031061cc318530860c00182302600bf97e2fa000be0002f65e8bc9782ee5d80000000000000175000000ba1732e45c4001702de00000000000000000002dc5b4b616b2d45a4b4167000598b29642c600000162000584b015f2bc574ae0002b6568000002b2000001582ae558aa9542a6548a895029e000a714d0005300014b294524a414728c514a2143000508a08002804fc9f13d2784ec9d1392704dc9b135268000000002664c89893025e4b89692c2564a89492824e0009312524848c911210000000012000047c0000023c4748e11b2344648c00000045c0000022c4548a1132244448810f21c4348610b0004288490820e41882904206408809001fe0007f0fd1f83ec7d0f91f03dc7b0f51e83cc000f21e23c0778ee1da3b0758ea1d23a0738001cc394720e31c4384700df1bc3746e0db0003686c8d81ae3586a8d41a6348688d019e000670cd19832c650c919031c630c5000000620c3184304600bf17c2f45e0001762e85c8b816e2d85a8b41662c8588b015e2b8568ac1562a8548a814e000530a514828c510a114027c4f09d0002704d89a1322604b89612a250498001242444808f11c2344608b1142244408710c214420831042044007f0fc0003e87c0f61e83c8780ee1d8000000ea1d0398720e21c0378000dc1b43606b0d41a434067000198328640c6188308600be0002f05d0b816c2d0590b015c000560aa150298520a21402780009c1342604b09412424047000118228440861082084007e0001f03d0780ec1d0390000e01b8360000d41a0000660c81883005e0b80002d0580ac150290500001382604a090118220000841001f03c0740e0000360680c81802e0580001502804c0901102003c0700d01802c0500901001c0300500800c01001,
  0x18040000000000000200c007fe00000000000000003fe7faff1fdbfa7f2fe1fbbf67eafd0000007e6000000007e4fc4003f0000001f7bee7da000003ec000001f5800000001f53e97d0000003e7000000003e67ca001f2000000f8df13e1000001f0000000f7c00000000f79ee8007b8000003db7b4f6400000000f61eb8007acf55ea000000f4de90007a2f41e7bce79af30003cb000001e53c9790f1de33c5788001e1bc2782f01dfbbe77aef0003bb774ee5dc3b776ced5da000766ec9d8bb075eeb9d6bac000eadd53a9750e9dd33a5748001d1ba2742e81cfb9e73ae71cdb9a732e61cbb9672ae51c9800724e45c838f71ce35c638b000e29c4b8870ee19c2b84706001c1381700dfdbf37d6f8dec0037a6f2de1bbb766eadd1b98006e4dc5b836f6dcdb5b636b6d4da5b43676ccd95b23636c4001b0b606bed79aeb5c6b6d69acb586aed59aab546a6d49a88006a0d3da734d698d2c0034a000d25a434768cd15a2343684d05a033f67ccf59e33b674ce59c33766ccd59a333664cc59832f65ccb59632b654ca59432764cc9592323644c859031f63c0018eb1c636c698cb1862ec598ab14626c4988b1061ec3986b0c616c2984b0860ec1982b04606001813016000017fafe5fabf17dafa5f20017c2f75ecbd57a2f35e4bc5782ef5dcbb5762eb5d4ba5742e75ccb95722e35c4b85702df5bcb756e2db5b4b656c2d75acb556a2d35a4b45682cf59cb35662cb59400164ac8000b1d632c5000001622c3584b0560000000afc002be00000000000000000000000000000000057aaf0002bb000ae800000572ae15b800000ad8002b5568acd592b15600000000055e0000000055c00156aac55600155000552001542a7000a9952aa4000a8d512a1540a7d4f000000a754e29b534a654c00052ea594aa94526a4800000522a400028f000a380028d518a2d45289510a1d43285508a0d412815000013fa7e0009f40027c0000013da7a000000002794f09dc002760009d400000000000000004e89cd392710009c137a6e4da9b135a6a0009a5342674cc995322634c4984002604be0012f25d4b896d2d2594b095d2b2554a894c002524a294127a4e49a93125a4a4929212380048c9152200048690920a4047e8f91e8000008f11da3a4728e11ba3646a8d119a324620011822f45c8b51622b4548a51422700089912a2444688910a2000087c0000043c8750e21b4348650c217,
  0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000052ba5400294d28000000000000000000000000000293800000000000000000000000000000000000000000000000000000000000000000526a4b49291800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000291521a40000000000000000000000000000000a3e000000000000028f0000000028e800000000000000000000000000000000000a3946c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000146800000000000000000000028c800a3145e8b515a280000000000144e8900000000288d1000000287d0ea1b4328580000142a84d0800141e83505a0940e81000001406800009ff3fa7ecfc9f73e8004f99f13de7b4f59e93ce794f10013c277cee9db3b275cea9d2002744e79cd396724e39c4000004e19c137e6f4dd9b936e6d4d90000000000000000000000000000004d89af35a6acd49a734a68cd099e002674cd0013300000000132c004ca99200000000000000000009900000000098e002634c598930e61000001304004c00012fe5f4bd0000025e0009772e80000000000000000000000000009732e25bcb696b2d259cb29632c257cae95b2b255caa9532a253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c9292324247c8e91a00000000000000000000000024648b9152264448790d216424839052064047f8fd1f63e47b8f51e63c4778ed1d63a4738e51c63846f8dd1b63646b8d51a40000000000000000000002344678cd196324638c51863045f8bd1762e45b8b51662c4578ad1562a4538a51462844f89d134000000000000000000113225c4a89312223c4688b11221c428831021fc3e87b0f21dc3a8730e21bc3686b0d219c328630c217c2e85b0b215c2a8530a213c2684b09211c228430820fc1e83a0000041c83706a0c8000010620bc1682a0020a4138250460800000103e0740d81800205c0a812002040000000000000000101c000000000000000000000203000000000000000000000000080a00000000000000004040000000000000000000403,
  0x1000000000000000000000000000000000000000000000000000000000162ac4d88b0e00000000000000000000000000000000161ac2d8400000000000000000005830000000000000000000000000000000000000000000000000000000000000000000000000000000000000582b03600000000000000000000000000000afe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000afd5f4000000000000000000000000000af80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000af60000000000000000000000000000000015eabcd78aef5daba800000002ba573ae55c6b8000000002b78000015b80056d0000000056c00000000000ad600000000ad4002b4800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015a00056700159800000000000000000000000000000000000000000000000000000000000000000000000000002b2d64ac758ab0d60000000000000000000000000157eaf0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000abb572add5aab20000000000000000000000002ac557aac0000000000000000000000000000000000000000000000000000000000000000000000000000000000000001556aa553aa40000000000000000000000002a8d50000002a78000000000000000000000000000000000000000000000000000000000000000000000000000000000153aa6d4c0000000000000000000000000002a58000015280000000000000000000000000000000000000000000000000000000000000000000000000000000000a935200000000000000000000000005470000000054600000000000000000000000000000000000000000000000000000000000000000000000000000000002a28000000000000000000000000a8950c00542a835029fd3e0000000053da794ee9d0000014e69c537a6c0029ad34a674ca98800a614be9752da5800000000000000000000000000000000000000000,
  0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000167ecf59db3966ecd5990000000000000000000000000002cc597b2c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002cad94b2764ac8d9000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c7d8eb1b632c58000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]

def proofWords : List Nat := [
  0x12c8aff2db400672243b11c2b74ae52bb65c158b73a705680846b6272125e3c11ac3ab2dac005719c0eb6fa2dc4835d93b60012372dbc833d93b6000aff2db4831d93b60003ab2dac01d4d5c54d4d4c5054d2c5012e07c52087ab12aae168b67eb0b653107af1c8b634d3c581758b5bbb8b594d7c8618c0865509664d9c869350804dac86d3488434dbcb476b5cb4f6c9cb49137cb4300364ed996db02c7323765fb0a4087d13407b972086b09b020f21c3dba4509663508034884332a4830a562c2341c8b6330dcb456c04b536ad4b4d00364168b67ab85a1eec2c1eaeb414e71014244df2d0dab52d35b272d2400d53ac2d95962c02a13089f93289f56807c7d52ae1687a7c405094d6401d4d5cb614d4cb5f4d2cb5d0b07a9320255db02515f824d72086b4dac86d09b024d9c8690f21c8c08653dba44d7c8615096635080348843bb8b594d3c581758b5b30dcb456b5cb4f137cb436c9cb494dbcb47003641c8b63658c227e4ca27d754ab85a1eecb0262eb414ddc821ac26c083c870f6e9142598d4200d2210d7e09376c0944c809542c1ea534b2d753532d7cc372d144df2d0dab52d3775f2cfdb272d2400d90724d5cb61658c20a14ca27d5001eff54ab85a1e9cb02627101415c821ac26c083c870f6e9142598d4200d2210d7e09376c0944c809542c1ea534b2d74c372d15ab52d344df2d0db272d2775f2cfc00d90724d4cb5f1edcfe099f54abbee6585a1e9cb02614c225ef101405c821ac26c083c870f6e9142598d4200d2210d7e09376c0944c809542c1ea5b2f2d2c4df2d0cc372d15b272d2775f2cfc00d90724d2cb5d65b6c09457e27ccca27d5061ebf54ab82c1ed4b0261cc82604c225f7a6147534d00745a1f8fac161d3571615353160d34b15fdc821ad36b21b426c0936721a43c872302194f6e9135f218542598d4200d2210eee2d64c372d15b272d244df2d0db2f2d2f75f2cfd36f2d1db652d5c00d91d62d6c7afd509731c824db89962c098332097f308979db097732897572086b09b020f21c3dba450966350803488436c9cb49dd7cb3f30dcb4500364bb8b59203eb7d2d04006d94b572036b7d2d04006d1cb55202eb7d2d04006c04b532026b7d2d04006d54b51201eb7d2d04006b5cb4f200eb7d2d04006ad4b4d1ff6b7d2d04006cbcb4b1fe6b7d2d04006c9cb4920f775f2cfc004dbcb4720ef75f2cfc0030dcb4520e775f2cfc00137cb43204775f2cfc00adf4b411fc6b6d1fa478a62b731fcd343b842be2b771fd54259a863701496ab7b1fdcd4203a27c15c1cd6b7f1fe4d2210c3a920bdb251eb762921144dd20deb5b1faeb631fb6b5f1feeb6b1fbeb571ffeb672006b83201400dd7cb3f,
  0x102fc9a02150402053001f5f031a676e199f1a1875563c9a819ac5c23348e23066390f07820e640e3584c1400035024021b63a9a22e84f22506536a0647f28387d2037700286088ea0c1742e7cf26a064725061fd20375da035500286090223a9fa2e7461d98807d558f2a81346a06472388b92688af3808a74108a15f089dd20373038d613050000d42d024088ea5b0b9b3c894194da818dfca0e2e6010dac00a18ea0c122688b993c9a819ac94187f820e5f680d6400a1824020ea6a8b973c894194da818dfca0e1e6010d9c00a18ea0c1225d0b953c89419dda8191e5d70e7f480dcc00a18223a98c5b0b933c9a818dc94187e6010d97680d5400a18243a9227e8b914d08e22dc9a22b4e0229504227d7c226d3022644c14000350b43a94a2e3c4054394b8762ac42902e36b040184054162000d20e9c018814242bc518282e340a1a818d0c815312012f1781191e81132f8111f687194a3566b2d2a886b7002de1104e18896760fc198b8b0286a06345e04b4bea43da1c65acb49460b83e2e1cdac10121acc48f883204047a8c92c2e0538114676d2de4061000c04150588aee5800348440e84e70062760142412e2e266c453ba3c3403a36662ac454a5e0010fd0e9c005090af10e5bc83e2e1c0a1a816717812d2fa907f446f96b2d21ea320c8101123e2002de1104e18a4c5a0662e142e19b800fa5e8e03f79003d1003a2188140a0dac100e5100a6f06e50c89d71e89d30a02e19bf09003d1bca6c450b7f3c0b7d3a0b7b0fa3e1781031a80ff2fbc00184003010541622bb96000d21103a139c0188142412e43952c2e040a0c89d71e89d30a02e19b801208f78e03f50184003010000d21104e18980a29cc2910e143a5142dfda88780a6f06e51e89d30a02e19bf01208f59034001840030102fbc01a80ff1781030fa3e000d21104e050904b10e13c0b7d1b0e7c044c280ba0002866fc04823c432237e40d98061000c040bef006a03fc5e040c3e8f80034844138144b92c3a0b7b03fe8a02a4c1accbe27447a274c280b83eb984823cc5e23a4322386fc0f750e59b0661c6cda115d141154f0114ce8113c061000c04150588aee5800348440e84e701d80512e9db4b791acc2823452cf01800284823bc5e23943223746a235c7a234c0c0400034844138142bb96006d22312b51e119d217118dca8aa10b612372dbc005716029a063392114865225118b75bc172086536c3118b92b6c6110,
  0x14d3c9a14d2c99fbb899dd685e4dbcb47dd7cb3fd93b60013692f2d965f82b132274db02690f1e03d825b2c23430a5632a483187cd1a07c33f87b31c87a912aae7206a30dcb456d54b516b5cb4f6cbcb4b6c9cb49137cb43dd7cb3f0001a09136b2789c163542f245e9bc086f76fc04f939b88609a2c9047688755baa0779fc001421b3f29a0bc700b7786e1d9516cef0001642edd202ec69c17bdb8178e18908b2e11da5f24a30cde4f50cace79ea00a981de7f342d615e2f0f0e2f04005086c06a523a14e8139f4e752f17a8af8895c48893cf08917d04c9a3f8d0b58001423a255e2f0c5a3bc08977634029fc9b8860bbf2c8bbd768bbb5b8bb9590bb76e05e3c48317af8301cf02fd9a02f993d4333915c31b931430302a60779fc001421b01a94b0e2f0400a7059365844763c02700134068e85aba182efc00a705ed6583475ac06100134948e81ab8b22ef400a705936584e763c02300134068e7dab9da2eec00a705df6584876f40517d0307933430f6e05e393d4333001341b30e5b8bb90029c164d96511d8f007c004d01a39d6ae590bb76e15e00a564511da13a18110b20d16e121d8f168ef00029c172e4770c9ce89ea3122ecdf42ec6be0c064c52ebdb8184f3c0d265052eb6682eac0a981de7f342d60005086c068840822c482122ed5b82c8025591447684e5b848763c5a3bc000a705cb578893860b491dc32302a60779fc001420688439d4e7dab8e79c48bb36e16e008564511d8f168ef00029c169d5e13218908b2e11da5f24cf0c1c0a981de7f0005081a480e75ab9f42ec5b8860063591447684e2c8345b84875a45f9578895bc0003a17a8a70595c38303c482ff7d02fb02a60779fcd0b580014206a1239d4e7daba4c52ebdb876802f591445b848765c5b5bc0006e05bfa705955788918608e2c8e09154315931c2fd39f7a8c3834faf834dc4834b7d034702a60779fcd0b580014206820480e759414bad17a5dbf013ef00024e6e1b817ce9c16555efe218268b2411da21d56ea824a10cd64c70be40a981de7f0005086c06a129a0bab191f480ddcfa3c8fb5828942e958e661fa2e740e3594a6d00035024088ea3ee7983eb53a2ea4b8f1708c3000d43a94a6d20a5d08c95b08c52d0ba352835197e461f639987e8b9d038d6000d4090223a8fb9e613a250ba5027c8754d2ce190c8e22f4e022af480ddcfb58296c2e6c4c1418e661fa2e740e3593001f50402049a02171a18754a0d465f9187c0035024088ea3ee7984e8942d0ba34d0e003c57c,
  0x12d35b2f2d2db272d25b012d4db552d4400310ba3b11c2b0582fdcbd105897138896f4f096d00885b892f07081b7485c4794d81a55c81a1be84af4784ab5001ef6401eb4601e588873bb524e77072986875d67875bd93b62bfcb6d000ba3b11c160763993650eb4562fd4ba91b89cf6888cd6a88cb5b08c52d21e0116600142139c04d751c090ce880224e8bf33c89418c5a81a766030db66390f1400a193e8e9b63d0ea618bf1ea3120c8ebe0c073c0bf6475172e4c516542e001b817870e2ee5f44c1dbd01440a98342d61962fadde7f000069422106c39d56e2fbc5f1ab8bb775a405b0001a4d21239d5642fb5b886004b7680475780292c80255b80215914474fc5d9763c5a30001aa688439d5962fac029fc9b82c83486044763c5a35b848c48bb3af8301bc0be5768bbb7d0bb19314bafcf03499414bad779fc590bb702a600001a508840821239d6ae480be96e0b200f564016d5e016618015dda014d6e0145d1f16f5d6b17c5dbf178400a68201b2126e0be70c9ce89ea2475172f122ecebe0c042e001f42ec64c52ebc0a98342d6000069422121239d52039f6f0ab8be52f5c5e23a400348521998087a8a1104e4e0be307b4ae9bc1841da41c27bc8a27b51827857227954027ad90279dc2278caff2db4002e92154875225818ce4865211890602f84bdd1e02594187af6c9cb49000c43db862ed41ee923a0bb6520b3c920ae4a80a8c540a353e291e41edd001efda01f1d0c1f3e23b1f5ec61f9db652d5db012d4db552d45ad72d3dab52d35b2f2d2c00068c43d8bdd154d36127fc880a9da01f1dad72d3c007d8c40f0bdb252000294c1b744823de76ee90ed9b1382f5c622f540c04150588bef006a03fc5e040c32054d28d58342f4cae1055b0c18da0f44f0d00e8d9952fc000348144b0660e9c0258444b8902f641278000a7186cb1208f37403f103010000d26028a730668784e110524e0bd72514c1b760002a7610144804bd0e52e05acb480c040bef006a03fc5e040c32054d28d58342f4cae1055b0c18da0f44f0d00e8d9952fc000348144b0660e9c0258444b890188bd59b114240d3823fd50588003490e143a6f20e9c0af0342f4c01b488c969486c965484c961891cc48dcb6fd93b6000d2161365485521d4894ce818a62f4401b38896f4f096dbe896b478967485c963891cc058475488c469486c465484c46148dcb6fd93b6000d2050584d96102f3dcc0584750dbcc8f072b7707294d9c513c405194da4bcb000d2050581d8562f3401d4d9e8a8c07a4d7e00eb0be4d5d804d4c9a3,
  0x13089f9db09f73289f52e8c03720a133db866807c7d52ae0b07ab4d5c507bb84ff2289ed4f096d0709ef38896f4d2c5314d3c5334d4c5351687bb4d9c541ad0543673224401e34da4bcb30dcb456b5cb4f137cb436c9cb496ad4b4dd93b6000600d862208c052fc53a2ea62c11656c2e6e76d1c8c5c2aff200625200f9d80029c02e243430045ea186a3e87eaa8f0d00e8d9818043448f883204047a8ca50b994cae1529792c8f8a40b8662ffcdac1012dc19209252408a42a08446407ec520784fc072c9806ce24bc118cc93607b57207a540069d90068dc2067ef41e8d1077ab61e1d4e1dde80d29841da52a1ce43ad2fedf215a59c1515f816465c15e5ec14ad5c145c0c040061027e157eb414edaa2e5da22e869d716277a15cfa61497101444022000e1a06640bc4bc0af4380a446e283d36127fc048718c0b4d22e88420974ac2fdc262ff5061ebde41edd001efd0c1f3e23b1f5ec61f9caff2db53692f2db652d5db012d4db552d45ab52d35b2f2d2db272d2400310ba3b11c300cbd34209072b88fb000d20a2f243850e90e83430049077026c1380a4e042d3a042b1a81671e81653c041b0c81531fb3e4503f52b83ed06013512012f17812d2fa909c246fb7f446f96c3064a356743806b2d203010541620002234862259680a2f2198bffbc118cc93607b57207a43606cd40069d90068dc2067d4e1ddd841da52a1ce43ad2fee5c15e5f215a59c1515ec14ad5c145f7a15d67e158eb414ffa614a71014553652805680b5c960b04620a552e0a0140985061ebde41edd001efd0c1f3e23b1f5caff2db53692f2db012d4db552d45ab52d35b2f2d2db272d2400310ba3b11c098bfd006c1625c4e225bd3c25b624bc1c206dd21711e5360695720686fa12bd1e12ad4007bd9007ad18079522311a521b11952131186221ceed4939dc1ca61a1d759e1d6e3c1caccca70462fe52372dbf64ed8aff2db43ab2dac002e8ec470763988c2a9580eb4bfb006c1625c4e225bd3c25b624bc1213134d18085540081d360816fa1315223130d90074d720745c2073d1e124d21b1245217123f141e0e6e1e05761dc7301dcdaefca725792372dbf64ed8aff2db4003b11c230aa5603ad118bf92f441625c4e225bd3c25b402216e24bc118085540081d360816fa131590074d720745c2073d1e124d217123e6e1e05761dc7301dcdaefca72578e4a70562fd460284d367a2a5c0b6df20b0d9c0a5dec09f55c09975a6590c1f3e23b1f5cf6e197e09376c0944c80955061ebcca099de41edcc20a15001efcb00a85a01f1f64ed8aff2db43ab2daf75f2cfcc372d15ad72d3dab5,
  0x1213c208028b4803e06825b00106791a040223b432c63d8586e16e0175da01d4b20155d6917b5dcd182ddbd176c0024a528ea9a93a02fca9c0f1b857804d86003374f45d776545b3bc0006e0f6a705b72c803d76803b5b80390013e150a84d29a939d1d2b1b886004b57803574fc5cf765c5ab5b803976803b2c803d0013e2a29a939d1d6e0f6ea1f40beebe0c670e0c3f120c2f3c0c264c7166e45517064cf16b6ae0026821be9c16dd961685d1f00ddd8f007c0aa6342d60001e13e15142592202e2592ca86479852850fc048986e8003484e111c00e906791a0402c6098b01455365280414098458659c809943c2f6cb027f4c827ed7e27ccc227e76c27dcca27d4f6e19061ebd34b14053531417ac142482145d3571534c372d15b272d253692f2c00571f64d35345310c21db0e61d168c11fc00488cae988846321967202652c09fd3209fb5f89f33089f9db09f73289f54187afd50bc94d5c54d1687d3bb856b4d3c51deb05094d4c5054d2c5019f85672e0557de857737852b2085177c9c42e875b973e439a4e1d872b840469a3047fc502c6101e55db3209b020f21c10af8a18dc3dba41e2984d0ee509663508030dcb456c9cb494da4bcb6c04b5300122346002158c1d209c0c043cd23b24c8c80029a244607a30aae0b07c5310c037d855922894b070959137cb436b5cb4f4da4bcbd93b6001223270ba3066f0708217462e4ad87854429a5605772305435687d32187bb272ae0b07c56401bb5c81b9310c037d8559a03785822a9c84958684adc502c50093f22894b0709590d89692bfcb6d4da4bcb6c04b536ad4b4d137cb436b5cb4fd93b60012232ba5ec11b6ca7056f90465bb1416ad411ec3ab2dac000eb65c7b121b3056f00709512289435009374d892d6409255c891f70891b2bfcb6dd93b600224c7121332801b05897138896f4f096d488c969478967486c965485c963484c96148dcb6fd93b60003ad489436fb9b87680752c80555780418600335b802d59002b773460b76f45db74745b776545a500054a692024a3aa717e3c9a819ec9418fde9d0336ce027400a18383a9784c2e2ab85a1f442c1ea623bac1067818c1a144218ade9d03366201f6a04d17c027ece193c4c14004870c41efcd00a444df2d0db012d4db272d25ab52d34000f038d138485a422d06e302d344c0185f2de3a8f26a06375b0363528361038d613050000d448b44e1216908b455a6033025345f00cf4c009d7a74675e6863f003f80e18cd138485a422d094301cbdb2e05572b1962c02a13209fb5f89f3098a01,
  0x12b0144b862241683493610e8c411be5460bb16059412274e00028e82dec3e8f86a03fe4c30f4069680c040000512e188905a0d273144138446021e30feb86f0fa2902ea280a198b850486b31ea3201a5a00014188905a2de73144138446021e930c3d3c9a819ec941945e9d03374c02b400a18305e0ea4c0c3b3c9a819ec9419446e1935e9d03374c02b6ce02758c3108812d438127ea04d2060c85c2afc8e2ac49a2a8ce02a5d042a3d7c2a244c1400e358045981e2135c02e34662e141227452cf027212561a12b7140b01c25640c040aee5b64ed800488cac0506224168349361138440e8be30e69c15ae811a2a2e8c191687d3de8577970c351809e59b82196781e98684adc502c486c47ba3047f0eacb6b6c04b534da4bcb0012235c8c37a70461e1456f903ab2dac00f42b60eb65c30d453f4d94a01188295161960f0bdb2c09fd3209fb5f89f33089f9db09f73289f5720a133db864007bfd52ae1687cb0b07ab4d4c56d4d3c54b4d2c549eb05394d5c537bb852f9f8567c405195685792e05572185457cb26572ba5607872e8769231de0eb49359b821d5382056781ed6bb0c4a81a530dcb456ad4b4d137cb436d54b516c9cb494da4bcbd93b60012234d9c81f4c9c30677a15dd60ba25cf90cca704632060278d9e079e8006dcaddbc11809a1a12b7140b14024fc8a252c1c25643625a5217118e1011a5b012d4d3692f2c3ab2dacaff2db764ed8002992232b97de2ba75a9b0f02a053829fce829f53a8296c0d4daa0de7681897481925a20dad740d9dfa0d954a6d2ce0274fa3ca60330246e302ea04d094301c5c2afc8e2ac49a2a8ce02a5d042a3d7c2a258e6604c1400e358f40182478178ac02292804870ac658f6160aee58981455365730262c17ec28c89d36c09a4b08d0c2958ca921e21f94c61f35021f54d01ef4681f0cfe1ecc721ea44aab9c81a8c430847e500da2b7514c71082b95800285a1f4eee15ad34f1474182cc4342c7c482c54322bfc6a8905e2c35505880c0429d7163e7e159cb8155eb4150f7a15dcde14ac82145c023075f8f39f2710ba1d6d9c80a5cf90e6938761caccca70463207a3086027875c08f576cc98407968006d61011a68c11fe721257140b03625a521312961a12b4c372d15b652d5db552d45b012d4dab52d35ad72d3db2f2d2db272d244df2d0f75f2cfd3692f2c3ab2daf64ed8002992232ba518099b85b80212c803176802f763c599765c5abab800a703c6585c757804186003f7474ac59220779fc02a9807ba48b02eb8482cd1b3dc,
  0x11695642edc2e00000bc01a48134a6bf239d7781d174aab8c612ef74a6e3122ecdda2eedf42ec5b816f61800fd6400dc0a981de7f33c0d265052eb400508200692021252fc8e75de1d1f317e0a6188cf6888cd6a88cb5d08c97e88c75b08c52d134238c5b268c59380c57410c555f0c4f4c2e2529b4038d61305063998000d4108880e0bc489b65e0ea3174f225063f6a0623b380a7c6808700286108383a88e316cf26a065725063ff980b5b380a500286220383a89a3164f22506636a0623db80c3c6808300286108bc3a8e0315fa8cf3447d17c1d15b85b8c45c4832fc3831baf83199a03112c805593d45dd91545b976f45db0b8006e0c536585c757804186003f5900377474c51d0b58779fc02a6048036f1b039b21038f08037d0788494ea0a5d036768837b6a8379f28655e08665980c633d20641558f26a06357e88a35b08a1f980b1fe8091038d663998529b4000d4220382f1223a9043155b85b80452c803176802f74fc5cf765c5ab000a84fa9a93a02fc9b8314fa87d031faf8319c3830fc4830bcf030991dc5d191545c1933c5adab8009a086f6585b3765c02b938aca705b702a60779fcd0b5800142150a84f9d1d3145b886002759001f57803576345a1765c5b5bc0006e0c4da705b72c803d76803b5b8039747cc4b4f8c47d0b58779fc02a601b039b21038f06835f08037d8e83c50788494ea0a7e83856a837968835b5d035798ec699f28655e08665d20641da0621558f26a06235b089d7c040edf980afc6807f038d663998529b4000d4108880e0bc6d8ea5f0c4fea33c0c86680c470e0d3ebe0d37120d2df40d1e47717464551706507184c008b0542a0e8d7475b83135b87680472c80775b807374fc5cf773c611ab800a70c496585c757804186003f59003702a60779fc001428b0542a092481d1f312f4439f7a81d15b8c4832fc3831baf830d7d03079a03052c80555b802d93d45dd91545b993345a776f45db76545a5779fcd0b5859003786003f5780416585c70014215092481d1fa70c49ea33cd11f45f07456e16e3117120cbf0e0c6ebe0c66680c44b201564f5177645516e5dbd176c2e001b8310d96171d5e01061800fdd1d2b1648800a981de7f342d600050a2c150782a0924f8c470c84e7dea24771735f44c1d3d011742d6000508a8bc29c39d4e853a24e815b8c456e16e01ccb200c5da00bddcf1845d9716ac008b29a4fa4e80bf26e0c432e05082c153823864c04061e30fcbe30e45e2c4c482c6c342c94182cdcae5d697230dd367203625a764ed800299223,
  0x12680854100814c007dc68c6d130506d8c6b000d4108880e0bc488b431d486f939b839d7a8c38303c482ff5780292c8025af8325cf03217d031f86004b7680475b8045931c59b763c59991dc5d174fc5cfab800658c71a717e4f8c6fd0b58779fc02a608b03c31b039b06835f08037d21038f0788494ea0af286557e83bb6a837968835b5d03575b089df980af98e4697e08665d20641da062121d534558f2238c5b380c57529b4038d613050639984c007d4100812680856a0623000d4108880e0bc990b4988ea31cdb85b803986002759001f5780352c803176802f747c5c776345a1765c5b5000541e29a4819631c4c45de1b8768075c4832fc3831baf83199a03112c8055773460b93d45dd91545b976f45db0b8006e0c536585c757804186003f592207474c5102a60779fc001422a0541e0928e93e31bcc45de1b8768075c4832fc3831baf83199a03112c8055773460b93d45dd91545b976f45db0b8006e0c536585c757804186003f592207474c51779fc02a608b03c31b039b06835f08037d48036f21038f0788494ea0a5b03536a837968836b5d03677e8365e0866df28659da062598e469fd20649980cc093e8f225063f7c0c0ebdbbb8b3809da8134268c59410c55529b41b862b2380873800835f007f038d613050639986d8c6b000d4108880e0bc488b4c68c6d311c6c0e6c1a0d7e3a0f14200df5200dbc840e3c1e21253a8296c0ee5aa0de5a20dad740d9dfa0d978219b7ca196768189663b1a774819276eee2ce02766033024fa3caa04d094301c9a31650431554a6d06e18ac8e021ce0020d7c01fe6231a45c319578318c0e3584c1418e6600035042220382f1226d8c6b4d08e035ce0028d7c027de9f1a16ce193cea319c9a02150402053001f44c1400035042220382f1b6630b4988c694d08e316ce0315d7c313c0e3584c1413001f50402049a02140035042220382f1b62d2623a8c672fa5b82f9e682eac92032ca802e53e026478022652036c5402af6e19cfe6197ffa18ef1a18ade9f1a16ce193cea233d3a829de7f1a22335aa232d742325fa231d6c23154a230c1e211d8e6600035042220382f1226305c3197a8af8331c483177d031393dc5e3915c5bfab8c612c803d76803b747cc5fcf03499414bad5b8bef9a0bc7578bc3c38bc1d0b58779fc02a608480d92480cb2a00b94f80991e00891500ab658a030788472d1342380b72680854c007d3800a34100a15f009f7a74683db8673f9865ffe863bc6862bb3864f3a8c5d13050000d4108880e0bc489b65e0c6300ce026e1d95,
  0x16617c01fce0020c8e021d4a6d000350b4c68ea4e83885922250c8d3c8941905a819ae58b0df7820e7400a189208038020ea618c8b233c6e18ad3a82a620225a22335aa232d742325fa231d6c23154a230d8e66000350781085c32248cf1b862b4ea0a9880896888cd6a88cb5d08c97e88c75b08c55288c32d0c753d3f402296092aa0c31e08b3e0e8b8d4203f9942e66c2c07438862ac454a5e2902e2b88d119ad20486b3692fe71a904b3c0639980184000880000d41e020188900512e258be321c2e19b560486d70fa3e6901536b012b930101003a218814258329c0c3f0c8aa92f8aa300880000d418968240144b9cc5104e1109a0e8c834d0e0034d7c023c8e029de9d1a0ffa18ef9a19353001f50402049a021400fe122089782d2621b8c8131f41ee906cf7084f08200a2d200f81a096e2031dc3c31ecc61f35021f54d01ef4681f0cfe1ecc721ea44aaba7e159eb4150cc43085f27119c808761caccca7134f152c468a8b8155cba30645a1f4eee15af7a15de5c30d460279e6e086d76eb8ae5d697230dd367211e119f140b21a12b67212561011a5b552d45b012d4dab52d35ad72d3db2f2d2db272d244df2d0d3692f2c3ab2dac0029922331fcc6f8b0c470013e150922a1421e0c7d31e4f4018247803081178ac008950229280487000419e46810088ed0c0f0c7b31d45c319400108880e0bc488d4630c7900f74a3185da2eedd1f317db8184f3c0d256e2fbe5052eb6682f1d5e2f0f0e2f061203663a03e492032ca802e53e02647802245402ade9d1a0d96280df031a8f6e19cfe6197ffa18ef1a18aece193cea233d3a829de7f00a9818c3195a22335aa232d742325fa231d6c23154a230c1e211cb431d5b631acf4fd008a5822cf830c7824aaa50b99b0b01d0e218ab1152978a40b8662e14122745a4bf9c6a412cf018030fd8e660322c1c0421443a3104aee58182cdc342c94482c6c5e2c4c0c0400696a30266c02c0924a082a6f86479852850fc048986e8586583625a5c81a9021f54c61f367e159df271176eb8ca920c2958b08d0721ea76c09a4fe1eccc89d0681f0d7ec28d01ef44aab8c43084761cad34f152cb8155eee15aeb4150d9c808cca70468a8ba30645a1f4f7a15de5c30d66e086f140b21a12b460279cae5d697230dd367211e119e1011a672125775f2cfcc372d15ab52d353692f2c3ab2dadb012d4c4df2d0dad72d3db2f2d2db272d25b552d4764ed800299223880ac31dd342380b73800a35f009ff9865fb3864f3a8c73,
  0x1909e9f32eeae0b07c31687b93107d7682044024a4082d32206590e06495e067b3e8f21b8187a740cdb3809d528381137cb436b5cb4f6ad4b4d6c04b5300286d23ca0f1564c0cb96e1da008d6e00b5d8d1685d9516cef0001b832b40a981de7f21832c4005093e0b878fcb4a938cb7225d9617ace892f0ddbd0164005089257b4600196171db81665d1d00f5d8d0094001e0544d02e2c8cb30c3ce89ea24cf16b6be172ae001961687122d33c239f490a68269d8f009c0a98342d6000508784f82e860cb16e1da011d6e0115d3f1766f0001b832b4001e0844d29a4fa4e0bbf2d2a0232bdb85b802176802f763c599765c5ab00078a693e93bf2d2a026e0cadea1f4327f3c0d27120cbcb201570e0c6ebe0c66680c4596171d5e01061800fe50518364f51775dbd176e45516e5d1d16dc00150928ea9a3a364ea70cabab82c1f0c5a1ee5a0811009288819643819265a90e2658b0de44df2d0dad72d3dab52d34000f354e69a86a8ca91ee49cab9009282c1f0c381925a081258b0de4883244fb9828c41ebc7209756c0d4d740d5da20d6f681895ab52d344df2d0dad72d3db272d24003f143c10b9a3ea5a83ec53a329c3bb98e469f3ec60a6dbd261836d6a83697887e19804639272ae48ba20b07b36d94b57137cb436cbcb4b000fc50f354fe9f013ea5a83eb4fb5e613e3f8ca50db53a82a60118e5aa22d5fa22c5ecb02558e6614a6d0003513e3d0ea6a0fad3ed798268ca34d10403449a0295300275e9d19d79a18fd7c01fce0020c8e021c00fe038630b4c68943285b85b9307697c0788150024ed2bf2a6af0809f4327eae1687d10b07b388ec2c7790269137cb436c04b536cbcb4b00354db0c9d028341b85ea186a3e800b78846004487a00511bc326c0a06010b1789d91a89d59306b30d09dd1209db0c89d71e89d3002de1090e143950ed7010e9bc814600123267a89a086faf83257d031fc3830fc4830bcf03096585b3938c5391dc5d1933c5ad765c5ab779fcd0b580014280bf22a13e6e0c976e1da008d6e00b5d8d1685d9516cef00029c0f164324c0a981de7f00050878d2a02fc93e24a528eaae325400a705db6585a176fc04f763c01f001341e092ab964324e0a6a83897e838568835b5d03575b0353f28659da0625000fc53ea4424e8886a0c91829740d9da20e65aa0e5dfa0e4d6c0e4660318de62b19acfa3c8943234bc31d58e6614a6d09a31640e35800350b4c68ea1093a22038488c8f0d9cfb582a60318cdfa228d6c2287fa0247444d1a20dedaa0de53002774819079a18fc4c1418e,
  0x17887e14087d13187c93407b9272aedb0c9d7206a30dcb456d94b576c04b536d54b516ad4b4d137cb43dd7cb3f4da4bcb000228499212b5433860a6a83bf68835b98ec699da06215d08ab558f2038d663998c680835288a55b08a77e88a96a069b7c040f1090cdd000d44e8e06d8ea337e0a688ba16a83592f066397e461f5d08ab558f21b862d038d663998c68083db80c35288a55b08a77e88a96a069b7c040f1000d44e8e06d82433760a5d08ab5b08a7e11345f0cd968837b1700a92380a76a83597e8355d20641e6863f97e461f558f2529b41b862d2680854100814c007dc68cd72c803d5b8039747c5bd038d613050639980116659007176807500142069b8773ef06d8240e13a9154fa080cdb6e15e294618291dde7f16401c5da01d400509dcf4eb78d28b45f0cd9ea30e2936be1726826a026e15e2954fb9272e164d13003ad040285f011a86ce193cea3c85c022c9418748e021ce0020d7c01fdde7f342d600e3584c14004599f40c4f3c0c57120c5d6e00e4b200f4005081a938745bc1b6090384ea4553e9d1dc68cd7022cb44d26218b48e2734e027257cb789a272d0403130060ea3c9a81a749419056c0d8da20e2d740e1daa0d65fa0d554a0d4658b0df66010dbe6390f165a90e3e5f90d7c0e3584c14000350240e01a2123a480206d9863356ae0b07c5310c037d85592289ed4f096d0709ef0eb7eebe896b38896f137cb436b5cb4f4da4bcbd93b600036270ba334c0a0d0197120193002de6028a730448021e8ebda33466c4209153689133c090f3a090b1103254162008800709ef0eb7eebe896b38896fd93b6000d40d93612b2bc43950ed0e8ccf0c87ee301804de381b3dc61b3400351361818ec148382b03e3337a8c38327af830191d45d3931459d9a086f74fc043763c01fd0b580014206884bc1b839e4e7d3a0564332db85b802d86002776802359004376545a5763459374f45c90029a06884483f2d2a9c3326f05c823f22b8a4db0c462e4073d45001a76401a370819fbd3ce440b24a872d2bfcb6d000240815c671f884224158cc7bc01c077dc206ddaec8a227693627a51827857227954027ac8a27b5213118521b119522311a4aff2db4000e1ec67210891225338ae5180cc54d0e0028d7c027c00fe0b4a834485a42e68cc3658f60a2d7ec28c372d140008058d68c15fb8c193084ac3075003307ee1809f1be896b891ccd93b600058349365298cbfa70561cb460279ddc068c3ab2dac00572104874e4640cbd4d0e0034d0403457c033c00fe2a02d216,
  0x12d3cc372d15b272d25b012d4db552d45ab52d344df2d0f75f2cff64ed800068369007e198cf31add2e07267c04762276920026ce614b5ecb18f4de1ec522e883adfbafa25ad3692f2db2f2d2f64ed8000d8661685c0f06e0d0fe33c5963082853282672c09fd098a010f09ff3209fb5f89f3db09f7720a133db864007bf7907b730dcb456ad4b4d6cbcb4b000604d1534d4d553614d95359310cef3c8941905a8189658b0df65f90d7d3a33ac5404cc4e028be058c48055c5e05543204ac6a04a47a049f161bf5a41bb5c61b2e70910edb0dc9d0e31b6f4978ac008950229296808ac96084cac65a6e1e2576c98f6096d5815dcca0b14aa159cc20acc26850b00a24c8dd97ec28721e9c6e339de21f855a1f4d021f449e1f2cc61f24d01ee49cabb6c3275c81a80c04018245c02216c12dc024aa80e3580421442c1eac6230171014655cae92af30981a9c3adfbafa25acc372d153692f2db272d25b652d5db012d4db552d45ab52d344df2d0f75f2cff64ed800068369007e198b4d50ced829aa391fa331a20d6d740d5d6c0d4e5d519ff681894fa3c89419d5e9f32ec9a02953002779a33a44c1418e6614a6d08e316c0e35800350422d0ea0f038632644e8ceb03aea0330df011a7c9a22c663b0eecfb1329cfa3c89418fd0402844c1418e6614a6d08e316c0e35800350422d0ea0f0389913ae68ce9096c721e9e2065b1014643c9515cae8bc19cd2af332c031c981a9e424d1460b89a02153001f43e1b3f1a18add0e30221934e0028d0402857c027ece338c4c140061000220012dc1c81ab6c32757ec28c8dd8b00a24c20accc61f24ca0b15021f442685062078daec888c150c861eec3adfbafa25acd01ee424aa9b272d24c372d153692f2dab52d3764ed9b012d4db552d4775f2cfc00350b406836d505a9007e1b8ce79b0ae10a5141075380fc670b1c06081bc6381b3c0043f4520a92443850e9bc9c00e83e33966c1f843b2b842945041d4e03f19c2c7018206f18e06cf2902e1986a7053cc772ba1d85192087a741825b881965e06830f24a7a7ccbb0e064f2380a72680a54c009d1305001840541620088004b707206adb0c9d5fb0a323762c02893082b33187c93282c54087d12582135db262a85672787cb5a022b9b87895605775687d309a141881e36bb222305432187bb0eb7eebe896b3407b93a3663c3403683d1423fc4da4bcb6c9cb4930dcb456ad4b4dd93b66c04b536d54b51dd7cb3f000d42d01a0db5416a401bace338d9609b2a3d82cd3282c53082b30f24a2c0289323765fb0a,
  0x131fd2372dbf64ed800b50a648443ad48541c342ccbf0981205ae04d9c529000d2e9ad4790fc3425b82c80615b805d0029a93a02fc874575acd07bc14007bd9007ad7206859e1d9ddcae8761464821eacba1564b81f14aff2db53692f2dad72d3db272d24000b224c70add2ba4ec4706034142e0f86ef1986b72582134b81c95db26889da04b700eb7eebe896b9f01134a014fd93b6003a27b1f21e836340c63f558c09b3809d980436fa81344e8c8f380083988cff4100b15f00afd30cfd2a0ea4f811d1e01076f06e3a886c19306af6284119403e954b9c0e8c013c090100885b04b700eb7eebe896b13050238c5b268c59038d6d93b600036350380f8b43a84248888260fc1910e1bc83434060a61835f68837b6a8379da0621d206415d08ab7e88a95b08a7558f2e11346a06234c007d1305063998529b4238c5b038d6000d40e0b43a8428581a21d744988cff18865f90d5f1a323cfb5829860e3dfa0e156c0e0da20dedaa0de7ca1957481905563c9a8195c0e3598e6614a6d000350382d0ea1092222084d30cfd330c8e02dc9a02150402053001f6ce193fe6197f1a18ac00fe042220382d06efa022b9b87894906ff5605777f441715687d58480d988eeb07a74683630cf73a88cf4ea0a6888cd6a88cb5d08c97e88c75b08c55288c30eb7eebe896b639984da4bcb6c04b53d93b6000363503c0f82c0d100170cf9084c2a1bbd76c9928056caa159c6c03249e1f372c19c50c31ecbc31e5020b4c3adfbafa25ac24780721ea4f4018fe1ecc30810681f0c22928ea233d3a829a22335aa232d6c2315742325fa231d4a230d8e6613692f2db552d45ad72d3db2f2d2db272d2764ed8000d8d40f03e0b0344005c630cf7078c521b3daec89d0e308c150c22928861eecd01ee43adfbafa25ad3692f2dab52d3764ed8000d87e0f83c168cf51b649007e54c3a99e1d9c8402ecba15674c1984b81f048831e5a031ecf4018fe33c44e028be058c48055c5e05543204ac6a04a47a049f161bf5a41bb5c61b2e70910edb0dc9d0e3178ac008950229296808ac96084cea233cac65a6e1e2576c993a828f6096d5815dcca0b14aa159cc20acc26850b00a24c8dd97ec29a22335aa232d742325fa231d6c23154a230c721e9d5a1f4d021f449e1f2cc61f24d01ee4b433b49cabb6c3275c81a8c433bfac14e48615148c779ae0785367144e30143c6230142c1ead357141d34f140eee13ff1014655cae92af30981a9c0c04018245c02216c12dc03adfbafa25ac24aa98e6600421453692f2dad7,
  0x1759f8353c58f4da4bcb001e8a75d8815f53692f2c00a6d6447b85794da4bcb0025c568d4915dd3692f2c005637a4685694da4bcb001f227b74159d3692f2c002aa7e2805594da4bcb001f62e874155d3692f2c00580b834fc5454da4bcb0019c218d3d150d3692f2c00232b41f052d4da4bcb003a6398c014ad3692f2c007b0de34dc5194da4bcb003101d870145d3692f2c005708234cc01b48dcb6f00121548752254864a6484522133a0634c59630dcb45000c193074c21305458fba20d6ae22b0d2fbc0aff2db4002bb4ae58931cf78ae92b751c3b2ccab84df2d0c00d504a2719aa703ab2dac000eb4e43316a850d01ee462b489cab9460b8c41edc3eb68fe0a2a2046dc604bdab52d344df2d0db2f2d2c00e8848098281292e349d344100915f007f4c009d7b2c635988623e686493e8f22506412688b5962c37913050238c5b038d6000d448838108eae10b46a8d2518fece0275563caa04d1a818949a22bd0422857c22765f90d4c4c1408e316c0e3580035038108eae10b45b0d23829aa232dfa231d6c23158e66000350fa93ed7984e85c34848cf1b864f4ea0ae680ab6888cd6a88cb5d08c97e88c75b08c55288c363998000d40e054173b0829aa22d5fa22c56c22be164d104290d7c290586346d3002b7e63465a22e65742e54e0315c8e316d4a6d00e3584c1418e6600459800508382f122108302a1202c8b43a8d1d3c894194da818dfca0e366010dbc00a19220c0a8480ea618d1b0dbd3a28fe6033026a04d09419449a02d50402c57c02bc4c1400459800509220c1202c8b490b84f98d190283405c44805b400b784480252601cc87a8a7f44d173344be058c5e05543204ac6a04a7161c1f201c9da4e39c61b5c00b784480062259687623a048d1510c50ed9b27091c0d38236f16059e8a028aee587eaa908ff0f0d00e8d9834ff848f89529792c8f80c04150588003481a11168800240521e0a2f2601cc0f8d130c6ce89ea24551706be172ae0019617af122d33c239f490a68269dbd015dd1f00fc0a98342d6000508542482e860d11ea3120cbf0e0c6f3c0bf6be0c35f40c1e4f5179645517064c516764cd16be6821beae0019617edd69016ddbf013dd1f00ddd8f007c0a98342d60005085424a524802e76541a590d0f01c64e6e1dcd18561823a5070d24e7dea2be0c36680c170e0c0f120bfdf40bee4cd16be4c7166eae0019631c40a981de7f342d61da00bcb200c400508548ebf24802ede1d951e0d0d006ce2257d3c257521b11ed1e11f6fa1205223,
  0x1334d2233066b414ef101447a614956034fc380a4442097536127fdf62f6d22e88ac34bdc8379cb00a84c20a14ca099cc809576c09457e0934f6e19a0fa900f59e4357d06d3800348580512e188644909c310de9578e45a9d2128c561cae102f3ca632fc60284d9c0a5d5c0995367378506d3900f58003485805062311c8379cbc94da4bcb00024d509c06858278de51a93692f2f75f2cfc00d51c8378e8add7cb3f001367720de11eb75f2cfc008c1c8377c99bdd7cb3f00230098ddd266775f2cfc004d7c26376c997dd7cb3f001357098dd9265775f2cfc00bb826375c993dd7cb3f00135f0f0dd5264775f2cfc00eb03c374c98fdd7cb3f0013573d8dd1263775f2cfc00bb8f6373c971d93b6000360583ad373496fd93b6000e20d8dcb25b764ed8004f036372496bd93b6002fa0d8dc7257f64ed8000eb4e20737c257764ed8004f01cd4095bd93b6002fa070dc1255f64ed8004781c36fc955d93b600121b070dbd254f64ed800485c1c36ec94fd93b60008a0eb53c36e494dd93b6002fa228db7252f64ed800488c8a36d4949d93b60011e228db3251f64ed800486c8a36c4945d93b6001217228daf250f64ed800484c8a36b4941d93b60003adbe94036ac93dd93b60011e500da924ef64ed800486d40369c939d93b6001217500da524cf64ed80047936368c931d93b600121b4d8da124bf64ed800485d36367c92bd93b60003ad6411e3674929d93b600121b640d9b249f64ed800485d903664923d93b60003ad486d72365c921d93b60012175c8d95247764ed8000eb5217708d93246764ed8000eb5213460d911f9db652d5c00b18c4363c7e56d94b57001e27582cb207e36d94b57001d616aec1f85b652d5c007885aa907df6d1cb55003b2310d871f75b472d54000b246ba87db6d1cb550002cacb341f65b472d5400ac85a91b901f5db012d4c0088ecc435fc7d56c04b53001025682cfd87d36c04b530015a16a361f45b012d4c004085a5507cf6d54b510010c310d771f35b552d44003189e0b1821f2db552d44002785a7387c96d54b51000c61690a1f1dad72d3c00680c4fa87c56b5cb4f0002c2e1121f0dad72d3c000b0682d87c16b5cb4f000b8168688307bf6ad4b4d00100313d61ef5ab52d34002182c341701eedab52d34002185a5e87b96ad4b4d000d01690e1eddb2f2d2c00790c4357c7b56cbcb4b0002c379481ecdb2f2d2c000b0fe6507b16cbcb4b000de3f85aa107af6c9cb49001063134e1eadb272d24000b0824587a96c9cb490002c1c8a21e9db272d24002087216a2616453692f2c00,
  0x15182e0f86cf790d5f683ea779fcd0b58078ee0285e7000c42b3a20e06c0d0288e01606852381fa8af8331c483177d031393dc5e3915c5bfab8c612c803d76803bcf0349747cc5f9414bad5b8bef658beb9a0bc7578bc3c38bc1848e014f811d2a0eaa886b76f06d94b84892404b9b524e86875d3316a11bf24401df3b0bfb228e03180a137e02f79702db5802af6702977b027d5702657cb74d68d2f9f8df588ecd7fb18d8f3db865f824ddb025132025541b4e328267790d5f308285403d62c02a1683ea779fcd0b58078ee0285e7000c42b0381b0340581a19820160e05ea2be0cc7120c5df40c4e4f7178e45716feae3184b200f5da00ef3c0d25d1f317e5052eb56e2fbd962fae682f1d5e2f0f0e2f061238053e0704a807c6221ced9e1d6ccc5a84637fdde7f342d601e3b80a179c001b0340581a19820398ba561e80eb48a380cbe96e0be79a0bab779fc078ee0285e70006c0682021120848e011224fc1aded41d167c0476800705202ed4a837f652088e3a090e6e1e075c1e741e3b80a179c001b0340581a19820398ba561e82284637fc4b91906d9868765530ea6101f100034058662e88a118a837f5342680c52380d73800a34100a15f009fdb86697a7c67bb386453e8f2250df91708cf4e8df74c0c3b688ba16a8b975d0b9f13050038d69902f16302d32f02bd2202a70e02911b8a0f48ba20121c790d5f403d6683ea430d7788ecd7fb18d8f000243103c37ed345f008f2380b73800b3268085410081fe862ff98651c6861d000243d030fe2a02d09437e4b9b3eb4ba9170d21529b400024350ea088fb53ee7984e8df7157cbc0af536127fcac34bdc80b0caa2810c35dcf6e197e09376c0944c8095506d38ca099de4357cc20a1500f58b00a85a0fa800160c49f8df517b42e32c5d6b018e0237c400508929493e2a0788e8df3175ef0859d3f0124e812ef74a3255b8325c0aa615ed18001e14224a524f8a88ea0237c5345f008f3800e32380a72680854100814c007dfe862f7b84687e6863fc6861d003f8092920e0b43d09437bc4edbd82378189ef3b2cc228deb7089e35009eb6409e75c89e5da8795772ba0db704d89e94609e1485c463478467be846b00012571a118f2881486521148846037b446f1e01a93389ed0023c1812a228debd48a812c51cb31841da5c2278d4027ad90279d7227953627a5182784ce2f841c27bc3ad5a846579213134d21b11ece211cefa11ad1e119d217118e1a7a9d2128f14dfa8c1224561cae102f3ca632fd9c34f55c34cd367149c36,
  0x16a0e23341e18009dda008dd6917b5d8d164c0006a9a94bf293a9c3884e1b0b800590bb75b8bef658beb9a0bc7578bc36e0e19c38bc1848e1d02a60779fc001420686c210e1f858e81ea34a6e30e0ccebe0cc73c0cb5f40cad5e016618015dda014e4f7178ddbf1786ae0029c386d6e2fbd962fad642fb6682eac0a981de7f342d60005081a1b084848e1d6e15e0134b2012618009dda008dd3d1725d8d164c00a681a2124ede29c386c043939b874f45d32ca1691dc3233a04bc5af8331cf032d86005776805393dc5e376fc5e1658beb779fc5b8bef9a0bc7578bc3c38bc100142068841b2526e0e190b8661a943e384c1409845838340610106d383cea83a3004f02404e823f4da241400348349306831028298e1737ec42097506d38003103cea8e0f10b9c570d339006af3b0c03c40515050261228e11484cca460b1f0d8cd3580d3f7d85552402ab4d94a0141b4e1690e403d6000d20d24c1a0c41f8a60f826384cd31388b2d4f0b2bbe8db7478db3486cdb1485cdaf488cc7f484cca460b1f000d20d07e2983e8908a38477c180739818d31773d44f350be8dc1478dbf486cdbd485cdbb488cc7f000a64844241d81c383cde14d94cbfd68d2f5f829930829d2c02a13db86db025132025541b4e328267790d5f000d21a0c4298ac160e0db301c077c8a06a57206853606f5c206dd4007bd9007ad180795ae861dc1ca6221ced9e1d6ccc5a836334c461dcc60284d600abd9c0a5dec09f55c0995f2dd35a34be7e37d5d2128c260b05fee78521b3c2a1bc4a40b81aff8661a952c38250c35dcf6e197e09376c0944c8095506d38ca099de4357cc20a145a43900f58b00a85a0fa806101d0e303a3004f02404e823f4da241400310ac348381b034110980a208058e0b139f141dfd241bfeb6088dfd1345ca40b83204ae123804663815c604c53e0704a807c454076d1cb301c077d7206853606f5c206dd4007bd9007ad180795ae861dc1ca6221ced9e1d6ccc5a836334c4657860284e5c0b6d600abd9c0a5dec09f55c09975a34bdd2128c260a5452381c78041cbef0223b35fcf6e197e09376c0944c8095506d38ca099de4357cc20a145a43900f58b00a85a0fa8061000c0407a053c6a05445e0555a40565d0e303a3004f02404e823f4da241400310ac348381b034110280592c3827a8af8331c483177d031393dc5e3915c5bfab8c612c803d76803bcf0349747cc5f9414bad5b8bef658beb9a0bc7578bc3c38bc1848e012a0ea4f811d6f06d9a886b72402ab4b828160e051501337186cb,
  0x1151421e0a87910c3d8e4721bce75ea24e6e30e0c0f120bfd5e00a6be0c973c0c85f40c7e18012dda011d6e01164c7166dd8f16664771745d3f173eae0019631c53e390cb232cc0a981de7f342d6000151422a02e1e0e450107f232ddd1d314564880b232cc0a98000151422a02e1e13e390cc75173b000054350882f042488383904d0786006376805f0029afca4e75ace3f5b8e6302d4b80dea112eb69e40faa2047d3e314e183446ae0029c32ad6438ed5ed1a2c0bac6cf719638d5e2a90c64280a981de7f342d601e212c0005846150340f8a8948f6168e3d343c7834353e31469c16dd6e0085d1f00ddd9700add8f007d5ed1800151422a25224a3a590e3b0283205a46a059c7a059400b7980731441104ec58e3932ec8e029c9a0295300275e9d19d79a18fc5cec178ac0229284c140d04390255000250d41505a0f0e37016e4e6e1d6b17ee1834455ed1a120b346cf71de7f0c6429025516e00e5da00ecb200f69c16ddd1f171c0050854169963d8e3538bca638342638c43cea9a0fa802200000a0d41f8547181c250c438cc8cf4e8df72d0df96a835968838b5d03871b86614c00ad97e461f96a4653f986514883e910b9c0e38c220411bf06b99006a78e06cb9d86db5182e0f86cd2402ab1882954b82805026113050018400088041b4e790d5f403d6683ea000283507e718943102638c46db5182e2404b90f86cd8687651884a36284116101f59c95e0c06513916ad300b7158e29908cc31708cfb38e2b4e8ba50e0e2d688e276a83591b862d2680854100814c007d97e461fc6861d108e25180a137e02f75802af6702977b027d5702654d9cde17cb74d68d2f9f8df5130500184000880b18d8f3db860f3aa5f824ddb025132025541b4e328267790d5f308285403d62c02a1683ea000283507e151c60709431016160e2f5a85638a446fc85cec110077c4c1400035054070943988c2e83ad0903838b437f4e8ba5962c6431b862dc6861d6a835997e461f000d41509409398b382238acdf94881c52201f588873b67875b4c007dc6861d003f807094398ba090b4158e292e8664091cbc083f5c1e75761dc4e45a8561d6d8407d430194fca0e2c6e18b71a1874003501c250aa2e9e80eb424688e270b8661a9c3e1b34142f3c62128e3c1cce72578e45a8561ca52a06b552e7006100000a0d21f9c6160164d94762303ad070423895344c00cd2380c72680c51700ab3800a34100a15f009f7a7c67bdb8669b38645003f81502202178,
  0x13484783225a223357423254a230c0459800508bc10888170e739b07e245ce8242d505880034828bcabc43b5c043a50e5060e71375c5834bdc809957e09353453084c227e4b027f4c827ef6c27dcca27d43cea8f6e1906d3934b14053531417ac14248234cc00571f64d35355310e6fea3120c5ebe0c973c0c85f40c7f0e2f0645716fe4771746122f9e682f1eae0015e399c0a981de7f342d6084387c005081a1b0200baf039b4006e05bd6585a3747403d763402500134068200b8b239ac30f933c5a93a24e4d7654031d28e65578e67af8301cf02fd9a02f96585a386002776802359001f9314595763459300142068204f86ca70e69225ce892f0c0050af0578e670c5ce81ea245716ef0e2ee5d1d00e7786e1f4327c0a981de7f342d6000508201b29c93874580af039d4e7d3a174afc8e656e15e01ecb201dd6e00b5dcf183dd9516965052eb5de7f1da008e18009dd8d164c005081a0822c39d64ea7120398d6a11a661809e77701a30015c33121d640e616685a5e8c4300eb41f1601d9c2c34159cc883ad5a8469998407ad10074ddc068cae5b3000570cc890ecc70add2ba4aedf791c397d6a1832611a665382077701a7001f2570cc500e5d5a846de060aea2206e52a0684007b15c33172396d6a182ba11b784a81a98881c3001ec48078570cc228e5931ec720974680a9cac34bc26048ca0b14b00a24c8dd8fea1102550d04389c66b6c3275c8378cf6f70c435dcc20acd7e0ac4c639542c520001b0fc9f88810896378e5737d754668260b045a428009f896128c63956cc07020f0d82132289ed5db267089e35009eb6409e75c89e54d89e94609e10eb56a158e511196ebe846b488c4ad486c4a9485c4a74f04c74784c1484c4bdb52e08404757284b97fb9e000543506c671f2970963f0bc7b0141089022016394ce410881dd3d01c73b2cc0d81cb5c821970821722b38643ae5001d74db0c462e4a0164adb18539c4440b2000543506c671f2970fc2f1ec10888a305639442e0fada0486e519b563f012191e60a9be160d2f322742c23432a481a0b63f9941c8a25f82b13082b3720de3db0c9d310d77003a26f1289f0ac432200b0e4fea31285b3c381f4e1342d600050af039d4e853a24b23935b876802f5b8021765c5a9763c597933430b93142ff3a04e49779fc001421e29c93a02fcaf039d4e853a24a84fb4a392db876b445b8c4539f7a8d0b587d0c9f779fc00142a724e80bf2bc0e753a14e892a34a3a04e4931f46cf71200f800,
  0x1021d7c01fce0030d30ee05c273f4c19866218b72c19c4ea3a5c4c14000350240c0220218c4e8e993c9a819ac94194f820e67ca0e2f982ea56c2e4daa2e5c0e35800350240c0220218c4e8ea3a5c38b96a4653e60ba5558f26a8b971b8e93618e916a0e23038d61305000054068d4090303d022021783a54cbb2680b52380874c3b81709cf7a74683d3066198862dcb0671000240c3f8021784e86e3a4ccbb17008b2389cd2689cb4c0187a7468398862d3ab4268837b6a8379528371d2037f1305000054068d4090303d1783e9863a44df91708cf4c0c3b558f2038d613050000d4090303d1783e9863ab423125d1d16dc001514248092a70e8db308a082c1c083d761dbc083a25fee78028a000290167302815898c73de2ba6242a8add3f0ae52bb46424896c380a0d0c0106015d36840b1200e0c9a83a03db1e81131a80ff2fbc01fa963c041b4a3569d86db6f06d9bf06b9a886b79306a56c3065182e0184003010000d2260fc190a473096020283a242e0486d51986a571812d4b0103003a2260522905eaf88ed43b66c7300a3684332b842912016d2f81634203fb1fb8c3c03f34e03f13a03ef0d01330486d50601370c812b1a81291e81279c2c701c586ff8e06cf7186cd03010541620005434838149240f8e8534c416b80e2121e8c5b93c36e4e45a8601e24562cab6088daee2afa36dd22336d51e36cd21b36c521736bd21336b4003d0fc6725c7b0209488ac480a1209db0c89d71e89d33c040736840b002de6290e113980a29cc110123a059a1690e0b194402147901218ad24b86bb71812fa8811b510e7d0018a9402613980a29cc112ded5066cf00a1e8940c81175306dd9f06bb191e63f0121a0b63f9941299a1695488ee825a06f9c58e39002de62a500984e6028a73044d5066510e7d0276a04d39a19250402c57c01fe58b0df74c195e62188d3a3244fa3c89439e56c348c9a31648e316ce0315d4a6d12231d46efa05c39cc0e3584c1418e660045981e3b80ac2000080bc10838221f4228cfb182b444d17c023d860df5a20dedaa0de5740e5530ee3fa18bf4819078219972c198c4c1418e6614a6d0045981e3b80ac2000080bc0e0b43a8f4e1242858fad250e790d7f6818953a3244003f1442220fa9069a89a20a7e838568837b6a837961839b5d0395f28655d20641e08665558f26a0657038d663998529b4000d42f038220ea3eb46cd30e75387c92032ca802e76e19cfe6197cea233d3a,
  0x146ab41f25cf919c80a72ab314df800150a4059cc0a05249058158eab17b5d6b38fd5e01042e391564881d1d3145de7f01a096c84f0a120b35200f81ee922034bc3c3a9d7ec29c80b64c89d36c09a4b08d0c2958ca920d05c102fd8682d8fe6507228b7a4680015058560861082c3aa4e4b2c8e4dc3831baf83199a03116585c757804186003f91545b9592207474c510b8e4548036f21038f078849980c63706a68f286594e8c913e8f2250ea5268c59238c5b529b41bbe8173b05e2b008a4a3d0060c2041305063998010dc03af800054109e468223b4003c3a9ccbb4c009d7a74675e6863f003f80e18c2d242858943a945ed75ace3f5780410b8e45592207474c51779fc06825b213c28482cd4803e07ba4880d2f5fb0a322740f1e02c23430a5632a483417040bf61a0b63f9941c8a21299adb0c9d720de3310df5278ea11697a00054160865695c090ea3391c1ee901a379484f0a2034bd7ec28c89d03c31ecb08d0c2958ca920c6608d05c102fd8682d8fe650722884a66b6c3275c8378cc43a7d357157534b14c534f14cd35314d45a5eaee15afac15c400150582195a57024278ea134bdc80994c227e57e27ccb027f4c827ef6c27dcca27d43cea8f6e1906d38001613494d353514d15359571355310e9f39c508245444028343a6cda102cf0101c48038326a07a044e761b6dbc1b66a21adc9012e54007bd9007ad2e1225c206de1a1d759e1d6ed493a221ced600abdec09f5f2dd35a34bcc227e57e27ce7e37d4b027f4c827ef6c27dcca27d43cea8f6e19a0fa9e4357c6a03fcbef01140f3d380f2cae0f1c36fbb5466a4c1a96401a9c601ce53606957206851806742c459357141c142f35dc1ca7101c00c041460b806100028a2fa137534b14c534f14cd35314d45a5eab41f19c80a72ab2ee15afac15c77a46a5cf9314df800150a4059cc0a05249058158763a753417008b5f2de4100c3809c92389cd2689cb4c01898862d3a8f22506775b03637e83555d03956a064768837b6a8379528371975c3a9980436f97e435fe0839dd2037f4e8e99948171c586fd9c2443b5e0e952f3728206ed25b0e0e38c4a015b13050038d68e06cb1b0e1f4883e922041110b9c011666b01331e01072a0ea0e8bd34209074f811d07884b9306a52b83c79006a7a886b76f06d93a03dbbf06b93c040736840b9d86db5182e0184000a280005429016730281492415898c73de2ba6242a8add3f0ae52bb4640d0e9b4d09a02d50402c48e,
  0x14c0c3b038d66a0e231305000054351786d8240c022020ea3b240a0d011d1a817b1200e0c9a82f956a886b780547096f06d917abe5182e0f8ec54b81c91e8d03889da2582135db260184003010060f804b7000885b000607c8361492464a3a2613e1926a7b0ec733445e0554be058c3204ac6a04a7201c7da41bbf161bfdc61b34001482a49192b78448ea000f8ec532dcb232ce9c32ad64881203b040a981de7f342d615e399c001514294af024a3a1e0ec3ea2be0cf73cd126821d64a117d47456e1d6b38fd6400add9534370e0c0f120bfdf40bed6e00864c7166dd8f1666ae002183444b232ce9c3a340a981de7f342d615e399c001514294af024a3a1e1203b057e4f8c7d0b8e45779fc00054508928e8782a0ebf31f41ac0120070c84d481ee486cce12a1ce680d291c300d841da54e1ddd5c34cdec34dd6034fdf2dd3101457a614a5f615567e158c960b04900aad36528052e0a01409845834bcb00a84c20a14ca099cc809576c09457e0935c8284c3cea8f6e190c35dda0fa900f59e4357d06d3800150ec180c43af41db470bf96bbf2670d3d7cb74ad053f9f85634d94a011882952582c1160eb7430d77403d6d519a0b0eb90dbeebe84dd50021f460215c507839b87813916a16a36970d49000542b0ec568cc0eb4ebb392cb239370e0c6ebe0c66680c4596171d5e01061800fe45516e564881d1d31442e39141ac0120070c84d481ee491cb313607b590068dc2067d84a9a80de172396d2a998ba1d0e6300761c0b8448de5208245800150ec33046c70aed8902c3ae41db6bbf2470bfb5802af6702977b027d570eadd68d2f7cb744d5c55d308285328267320255db02515f89f39f8df52c09fd3db86683ea403d6790d5f41b4ebb856beb0571970d49000542b0ec5683ad11858310eb76682cfd8c4d3a23ba087209845a8d80049014568263ad66c3689133c090f3a090b1f89174209154509114e090d2b890954162000d20a0183e00a0d01330c812b1a81291e812712016d2f81637186cbc586fd7438c9c2443b0e832030100088000054350ac491cc19852632064d84ec0e0443ac47813916aad82271809ef001583318c8181c3abcd2f720265db02513209fb3089f95f89f32c09fd3289f53db8641b4e4d2c5014d4c505eb0509208d33000ac1615c4d15355310ead34bdc80994c80954c227e57e27ccb027f76c27dcca27d43cea8f6e1906d3b546682c3aa4243a8c763a77ac15c6ee15ac5a5e935314d534f14cd34b14c77a,
  0x10d0ee13b4c6e3b64bcdc838e32301626081bb6381b2c42e7264117d28056dac04cc3a2f4d08241e76f1c744e02bda3344da102cf0101c48038326a2761b6dbc1b64ae0f1c7a3b55460b83e3b3c183e00c0400610000150eca75cd2818520a924648282b25224a3a3501a731526028a4384643b7cecb1200e0c9a89d86db6f06d92401f96787672e8742e20c683c22a0edb17abe2fbc01a80ff9306a51e8ed59006a7053cc772ba1d87020a2641825b5182e0f8ecf060f8030105a022b9b87895611a56a36018401e0ec38b02eb78aa4658e358482cd409540116607ba41b3dc3190a04b7076024bd707a57a18875aec2582135db262a8a0279ce1881e36bb222307c2197a00885b000541805a0d8f64f8edd325eae0021800fe9c3885d1d31456438ec0a981de7f15e399c783b0c001514294af024a3a4f8a83b6c45f9dbc71d6d86a1f68cd17c0c0eb0c812ba80cbb2680d57186cb7a746837438c630eb108864db38ed717008b2380873800835f007f98862d130500e832000543b2061492464ade110ac94a3a3501a199cc6028a800244d846e3b6418fc8071d878d179db445fc586fd6d86a19c2443b7c0c0ef5e0683d11347a7ccbb2680a54c009d0012464ade11252fe06673180a2a001f86e21d784908b4b38ed74d10403bc9a02945c022c8e021d7c01fce0030d30ee1f011a879a19366218b72c19c4ea3b4cbcdc838e3042e7264117c3a9b0da107d080fecf00fce76f1c76081bb6381b2ce82357da062d28053dac049d505884c140ae0f1d380f2d140f3c00150d21482a64828248d4068665487a3b548cf4e8d215d08c92d0ed1688ba1529b400054248d46d824088083a8ed3330c8e031c9a02150402053001f76e199ece190f1a1875563c9a8191f820e77480dfd3a2ea56c2e6c4c141aa2e5c0e358001509235024088083ab982d0ed1049e003b15c61b34001482a49192b78448e83e3b3d3417008b5f2de3809c94100c2389cd2689cb4c01898862d003f8068243ea4fb9e60fb13ed4fad1b8ecd32ec8e021c5c02649a0255300235e9d1a0e6218b7fa18ecea3b24f43a54bcdc838e32081bb6381b2c88104442e7264117d8c10ee70b1bf528056dac04cc3a2f4d08241ce823f676f1c75fd1345c4e02bda33440c040183e04c140ae0f1cf0101cda102c00150d21482a491920a25224a3a3501a4f8665498a6021e5128a732003b2d342680852380b71700ab3800a34100a15f009fc6861df98651b38e2b558f2688ba1,
  0x19db444f03010060f813050639980121c000d2648280f0382d066a2a3a0e8e83bc5e0108ceb1ca26618a7fc40701b8c0ba8134572ba238ab1268aa3380a975f0a89410a8f4abcc600be32606a70c88e1548ee743966c0d0c011881e36bb222307c2197a54162060f804b7000885b08a4a3410e5e2b0409546dbd278aa4130500121c00060168360f0b419a8a0e90ed7010e9bcabc4384eef33a424781862a0ece0274728986e302ea04d3101c08e2ac49a2a8ce02a5d7c2a25042a3d5cae9803b947a053d2af33201c75a41bb4981a9c5e23b676d1155b01075520f3c96084d76c98aa2809e739d8092f5c1e95e8621d6bb00c040183e012dc002216c22928d0439b6f49e2a904c14004870001805a0d83c2d066a2a3a0e9143bb66c36841f45041d1fb8c4203fb3c03f38206ed8e06cb4e08db3a08d92b88d74a01516b01295416200054348520a8280e0661a8eeb2f8c3223850e59b0aee58981a9d523b9c3430047e117d08116cda115d141154f0114ce8113e76f1c77da3b940c04150588183e0003485264828990668ea0073180a28ee99b1380f2cae0f1c0043f50e143a50edbc9c00e9523b9ccd10c818f002de1123a801cc6028af68ee5829860eadfa0e4d740ef56c0ee662b19ae63b1a765d719f4fa3c89437bc5cec1a22e85aa2e5c223b4cbcdca081bb528055d44028343b854a6d06e3b663014458c10ee64117ef61125220fa442e703a9b108116cda115e70b1bf676f1c75fd1345fda3344f010fc3205f674d1c2e0151c26c208ef6a1e56447ba46e43b20b7e9e180e4e50d14e893936684134a6e2be0c95da011d6e01164771745d3f173d6438ec84f0868831f61d1601d9d8407e4643b7ce80f6efc1ae52e072622768e6302ae002183444dea129c3a35e40f93e3b747a3b546a03fcbef01140f3d380f2cae0f1e4c1a96401a9c5eaf9460b83e3b3c14f31dcae8761c08289906096c783b0d8e6604c1400e3595e399c04599de7f00a9822c0bac6cf719638d6120b341ee922034bdc8378f6c3274c43af5e2a917ec28c8dd8b00a24c20accc6428ca0b1502550e2372c96084d6808add8092f5c1e95e8621d6bb0061000c041505882685062078cd0438183e012dc002216e24b3140081d90074d36081576c98aa2809e739720745c2073d1808566e1e25584695a8d88a076daec888c1f0865e800150ec1805a2b0ee33b4cbcdc838e32081bb6381b2d28056dac04cc00150520a892350661f8246d8ea,
  0x117e66190ed5e4019d6b38ff988292218d55e294e18292d7422affa024d8e661de7f01e3b80a185d4a6d004870001805a0d83c2d0668b1088481a2a24e3a9a83eb4fb13ee53a380f092eedb8173f3cd11d3d011c1e3b8004d01a2a2f0768f07001b8173e9c1695d3d0115d9700b4004d0a8bc1205b8f0532ed30ee1e9d19ff2c19b65d70ea48e2aee62b0e6c4c14000110d4630bc2d03a420481b2126a216618f0332ed30ee1e9d19ff2c19b65d70ea662b0e6c8e316c9a3164fa3c93a33ac6efa00e3584c14004870000f1560e18c2f2642d06c84888108f012f4cda2414f02404e823f44e02848064c32063f201c75081164ae11340c040003499211066a2a2c0e980801cc9dbceff0283404ccbe058c48064c5e064432063c7a062dc61b2f161bf7201c75d0e3270910ee76d117c001505249192b78440e18c99066a287e3bf4163600ee51781911e818bc586fdc8071d9c2443b9db445f0e8ef976024bd707a57a18875aec03010060f85e2b0409546dbd278aa41a8eeb5182e0f8e855a022b9b87895611a56a360184008a4a3410e04b702582135db262a8a0279ce1881e36bb222307c2197a00885b000541805a0d83c8e8efb89906783101c04233ad5cae9862a1d2af306e302ea04d0981a948e2ac49a2a8ce02a5d7c2a25042a3d2cf01803b945e06447a049f201c75c61b2e76d116dd00fedc03bccf03bdce83bc5143bb578ac102551b6f49e2a904c1405cec004870da3bd46a3bad460b83e3a1422928d043862078daec888c1f0865e806100183e012dc00c04002216dd8092f5c1e95e8621d6bb16808ae6e1e25584695a8d896084d76c98aa2809e7380015060168360f23a0e8ef989906783101c04233ad5cae9862a052af306e302ea04d0981a948e2ac49a2a8ce02a5d7c2a25042a3d2cf01803b947a049f201c75c61b2c5e23ae76d114dd00fcc62078daec888c1f0865e9d8092f5c1e95e8621d6bb00c040183e012dc002216c22928d043978ac102551b6f49e2a904c14004870001805a0d83c2d066a2a3a0e8f03bdcee52f81631781551e814fc8071dc586fd6906ed9db44579c244336c041f0002a49192b784419a8a8e8da3bd7962606a70d0c01af0eef548ee754162060f804b7000885b00060168360f0b419a8a0e90ed4385c043a6f23bce0a529b47e8a5f5b0a5b6a8a6d5d0a65688a75618a7d1b8c0ba8134238ab1268aa3380a975f0a89410a8f600cd1c8071d1e88d51788e70c88df,
  0x13b060168f1b3bccda107d141075080fecf00fce081bb6381b2ce8235528053dac049c5cec0048707e3bf46a3bac96084d76c98aa2809e739460b83e3a1406101b6f49e2a9178ac10255022928d0438183e012dc00c04002216dd8092f5c1e95e8621d6bb16808ae6e1e25584695a8d862078daec888c1f0865e80015060168360f07a3c64ce91b862b618aafb380a5988085858f1138394410f133d006091e03fa841ca26248423e98c0c4070700ef37b1da572ba36841fa001c94abcc8206ed3f06b7238ab94508ed262be3c08eb3a08e74a01559f01191881e36bb222307c2197a2582135db262a8a0279ce060f808a4a3410e5e2b040954022543190a6dbd278aa4038d60121c5182e0184000885b04b7000060168360f1562d0a4a283a178f17193cea315f9a028c000e0bca1842383943c9a818d46e18affa02466202040055a8610922410f13ee2a04d32c19b57c01fe62b0e6e62188d3a33acfa3c86e302c0e3584c14004870000f1560e18c2f2642d2421b04285b84d10f11302c9a03150402848e021ce0020f6e19cece193e6218b4ea3c34423c043081068831f61d1601d9e5210dc92108d8407e670b1bf6081bb4641b65fd105b528055d4c039440283204adc61b2dd00fedc03bcc343004da115d141154f0114ce8113e76f3bfc9438dc08950c64285cec0048723a3bec7e3bf46a3bac96084d76c98aa2809e739460b83e3a1406101b6f49e2a9178ac10255022928d0438183e012dc00c04002216dd8092f5c1e95e8621d6bb16808ae6e1e25584695a8d862078daec888c1f0865e80015060168360f180801cc3c3e0a6888c15d08bd909344c0f0b380f09618f036a83897e83855b03834100b15f00aff28659d30657268c593e8f2529b4060f804b7000885b038d613050639980121c210e1f590bed9a0bab078ee0286171e03d39006a7053cc772ba1d87020a26419e0108f010c2041a20c7d8745807676101f91906d95300e9484379c2c6fd7f4416d5a022b9b87895611a56a362484238206ed4a01572582135db262a8a0279ce6dbd278aa4022543190a5e2b04095408a4a3410e00060168360f1562d0668b03a420483a8f0d6e16e28cdda28d4b228fd5e293e182915de7f0002d1429393a4c0f0b001b818469c17f5dcd01dddaf01af4a6e1da3c1d6e3c169e111674d1c2ec208ed3e0f976a1e56fc1ae6447b92e072646e422276bb20b84e6302f61a3cdea1196,
  0x10f3c0c0400034898111cc0fa8a8021e139143cb4609bc0e6776b406ffc8f2948036f8b03c34ea0a68837b6a837998e4697980c633d20641558f26a06235d08ab7e88a95b08a7fe8093c680836dbd2e113478ac84100b15f00afa75d88d30cfd7e07a5a784452a040d94843724842307884dbd024b7026c64871f9d347139d86e33c08e3f6818f805c17d531a88780a0d0d0145041d4e04193a04173684332b842912016d2f81638206f19c2c701c586ff2582135a022b1e8d035db269b87892a8a05611a4c2e22798256bf66302d343254238c5b268c59529b488ecea72f0e411bbe8340291091e01c8a23d0063f9940c2041a0b6038d613050639980301054162053cc4b81c92401f9060f81a8f232902e198f21b0823bda8795911ee91aea6787672e8742e112889da398c037948772ba1d8702091601840008800121c04b70000541802c2d03c0d83a730383cac03f74745b7808f250b8cb76585f975ace3f9a0bc7779fcd0b58592202c8f27068e1f02a60000545086c848848e93efc8f2917242e32cdd3f012400150844d0782c8f27ea33c0d27120c8f0e0c6ebe0c665051836475172e45516e5f4327c2e32bc00150844d29a3a34788e93e93bf239d6f080b4a3c94e410225408a4a31982341709f8a0ad07c7cb26673225382134401e30a86ef1486cd4a01516b01290121c091e01c8a23d0063f9940c2041a0b6000541802c0f0360f86a3c8c17b8054709a28f1d000604aa80610d20da6a0e9cc198f21950c6608bc39067e28022929f2c98d05c14e082eb41f06c387d9cc887806a4a807c510076c1ee49dcae8761c0824599e1d9cba1d0b8448048702478072288f4018fe65030810682d800150600b03c228f1f30044e028da102cf0101c48038326a0e80f6c7a044cbef02761b6dbc1b66fc1ae6a21ade4c1a94183e09007e52e072414f3012dc00c040001812aa01843483a73066a28363c75e0108ceb1ca266183c3c407098e469f572ba3e8f27c0c0eb4abcc1b8c0ba81342606a5238ab1268aa3380a975f0a89410a8f4b3c0600f0f1e8f19178f171f8efd8e8efb1a8eeb5182e0f8e85173b013050038d66dbd25e2b008a4a250e370121c2b0ee3060f8030100184004b7076024b5a022b2582131881e300885b892cc4602155002074d82052281db6401d35c81d17081cfd707a59b87895db266bb227a1885611a2a8a02307c75aec78aa456a3640954279ce2197a3410e00054,
  0x1730440e1220d8f4734046efa022928d05c2b41f19cc8910078c521b35ac04cc4e02848038326a07a044c5e040cbef01bc1b8ea21b064c1abc6a3c8ca40b8661a9cda0f44e8d998a1046500fa552e703a3d0c183e09007e52e072414f3012dc22434148a3c7c0c04006100022004c14030810f4018247800487072288fe650682d99e1d9cba1d0b8449180675360695dcae8761c082459c206de22768e6300de5204a6685a3c6cc43af400150ec180b40f0f453c89419d5a8195c6e18ade9f0357e602d6620216163d05863cec6c3ccd78ac102fdb7a46a5c1e26b608ad241c0670910cef29b1080fee381b3c62078daec888c1f0865c0f60a3500928383905b6f4808951e2b20c660a9d76227e281f81e95f2c9af4092d4e084d921c7c2a1bbca40b8661a948e2ae51423b4f023ad3823a4e8239cae2397da06452805552c040dcc3cc535f37542478072288f4018fe65030810682d80e35806101505888a3c7d3c372414f31dcae8761c082458183e012dc0022000487000150600b0b40f0360e8f4332ed30ee1e9d19d72c198d563c9a832454a6d06e3cfc4c1418e660e03cf40e358002d0d410888908bc6313a858f414d17c02fd0402053001f76e19cf1a18ac002d042fe2422f3848586e3cfc65f3a8c57d300b300042222862f0e03cf49c93a8c57e10f37410f395d0395e0839d268aabd2037f038d6238ab9000542d0d4109221103a178bc088da249863cec643558f13e680a10004248a8608a58b410f39330d30ee2ce190f2c198d563c86e3cd40e3584c1414a0dc5a8191c002d0d4908bc08a58b85b84d10f374d17c02fd300636e19cc002d3f8908bc858fa9e13441b8f354d0e003c57cb7930061f031a8cea3c9043c4c9419956c0e45a8191d4a0dc662b0e6c9a2aaf480dfd3a8781e3b80a179c0e3584c1408e2ae43404cdc604b400150b435135d10922470ce1103a178bc99022881c03686c3cce6c3688f92b88ef5100a2f8f2f450f2d4203fb3c03f34e03f13a03ef0d01330c812b1e81278e06cf7186cd1881e36bb222307c219704024a0e0f2b1a8f232902e198f21889da398c037948018400301054162053cc772ba1d870209162401f96787672e8742e112b0823bda8795911ee91aea060f804b70008800121c000541802c2d03c0d83a730f31102ef29b2761b8cae23454c5595058800348281903a0f90e143950e97010ed2f8f2ff018002a4c1abc4823dd52,
  0x134be4c1abc266e9c8378f6c3274ca920c2958b08d072288c89d19e1d9cba1d0b8449180675360695dcae8761c082459c206de22768e6300de520061000c040f6f08a83d44682d84a6685a3c6cc43af400150ec180ac34a409d9cc1103e260f53391c1a096e2034bd7e0ac4c660a7e281f2340e00028343a848038326a06a03fcbef01bc1b8e4c1abca40b8661a9c266e89007e414f3012dc22434141e3b88a07c40a1755c8378f6c3274fe650ca920c2958b08d072288c89d0682d99e1d9cba1d0b8449180675360695dcae8761c082459c206de22768e6300de5204a6685a3c6cc43af4061000c04000150ec180ac34a409d9cc110a83d44a07c8d03279828000a430e470d0107213c206825b07ba4880d2f5fb0a34170ad07c673224401e31200e0c9a81a80ff2fbc01486cf6f06e39306af2902e1986a7099ba2401f9053cc04b70890d05228f4d488f497438c720de3db0c9d3f99432a4830a562c2341c8a2322741a0b66787672e8742e11246019d4d81a5772ba1d870209167081b7889da398c0379481299a168f1b310ebd0f0f4501840030100088054b9c628411000543b060f78b435042220ea1f9cc110383d3c38ff286554ea0a7e88a3f980b15d0395d1134e08665380f3d022966c3065182e048f4b0fae60a9be3f012261ba31982160d2f5b03635f008f68837b6a83794c009d9f8a05fb0a9804631fe862fd20641e6863f7cb2634170558f253820bad07c6a2681b0e1f42040f3d83e673221e01a92a01f14f81c14401db07b923f99432a4830a562c2341c8a2322741a0b6772ba1d87020916889da398c0379486787672e8742e1121305063998018400301000880529b43a3663c3403683d154b9c4e0405453ba628411268c59238c5b038d62b83ed7438cbf3f4000541835a30542c2d0ac35042220ea1f8383d08a3d349d1600c99002de1090e143a6f243950edaf1c0050123d2d344c009d380083e6863f988cff558f24100b15f00af6a268d30cfd1e01a92a01f1472cc0d8f4746019d4d81a57081b76401eb5001ef1305063998529b4268c59238c5b038d6000ec1812af7a80610b435042220ea1f9cc11038488f4902848038326a07a044c6a03fcbef00343405bc1b8ea21b064c1abca40b8661a9c9007e52e072414f3012dc0061000c040022018a1044e8d98da0f4552e72500fa4001812aa01842d0d4108883a87e,
  0x1c98aa2809e739de7f19628240a9801ee48001808a0f05a7b0f713db4b03d9cc83d97ac14e535714deee14bc8634f48c778c2b70cab59aee282c3d74543d6dc83dac0016060228ac3dbd9a1690e31386400cc1880f5fdb0f69000ac081345128c213074c19163eed68f6d284f54378c00181c83daf4ed50c9d1c82510036c3da59a1690e3109fd4002890004a4d64b03d9d9a1690e3109fb403760004a4d54c83d959a1690a313d64302b33402850004a30adc6685a550c4357e23b0b14fe099c00128cab599a1690e3109f3400cc1b88d2f000582b0204d144a8835a3054c213074c19fb8f5f2809e609f2c990c0ac54e082ee234bc6c387cf6096ca807c47806a59e1d9ddcae9c8378cba1d0c89d36c09a4761c0c4d38b08d0c2958ca920b8448682d8fe65082458722881ee480016060228ac0b0f5d096c7806a62034bddcae97ec28c89d0761c0b08d0c2958ca920d05c0682d8824587228ab41f04a66b6c3275c8378d9cc885a3c6cc43af510076c1cd40ce27b40016060228ac150f5bc2ae234bcd05c0266eab41f0141acd9cc892cf0110076d800291cb303427746a275436dc048276c32275c7a274c280b8663d5c3e3d54f6f08a83d45080fee38cf8383d3dc8378f6c3274ca920c2958b08d072288c89d0682d9180675360695dcae8761c082459c206de22768e6300de5219007ad4007bd9e1d9cba1d0b84484a6685a3c6cc43af43c3d14061000c04002200e8d98f0d00da0f4552e713810158a104400150ec183de2d0d4108883a87e730443d64d2f09a145fb0a34170ad07c673224401db472cc0dbcc18b802606a7720de3db0c9d32a4830a562c2341c8a2322741a0b646019d4d81a5772ba1d870209167081b7889da398c0379486401eb5001ef6787672e8742e1121299a168f1b310ebd000543b060f78ac901d0880663d5cc9b2fa90532b86b388191e614a14160d2f5fb0a34170ad07c673224401db123e20c81011ea32472cc4b23e0dbcc260f53720de3db0c9d32a4830a562c2341c8a23227446019d4d81a5772ba1d870209167081b7889da398c0379486401eb5001ef6787672e8742e112030103dbc22a0f511a0b61299a168f1b310ebd000543b060f78ac34a409d9cc111d00f8f550283404cc48038326a1c61b35bc1b8c62078c7a340c9007e62434148a076daec88aa2808c1f09e608865c10c0ac500c286a03fcbef02e2,
  0x1779fc768f075b8f0502a60001422a3f24801ad2af0860f89176c2e39addbf0154004d0202481a2c8f87829a20ed5860e3e61b1a2fca1955aa22d5fa22c56c22bdee10397e602d6164d1043e0c8e021d7c01fe623e05740e5530ee38219972c198d563c9a89a14a6d06e3df58c3dece03cf45c39cc387d008950c660a7e281f2c994e082c6c387ca807c53e07047806a59e1d9e22769dcaea920b84ba1d030810e6300f4018761c024780543c7eb2cd0b8448682d8de520fe65082458722884a6685a3ddcc4ea8ac3dbd8e6604c1400e358045981ee480016060228f85829aa0e25860dbda20dafca195660318cdfa228d6c2287e602c7fa02458e6614a6d00035122221203a8943ed5043e0e0a6a88bf7e88bb908f7f61835f68835b5b0353da0621268085410081639985d0395e08665000d410af6068bc088b4e10fa9252623e043b3986c68b3ee60a7b840df7e837521d534962cf3713050639984c3b8cb06635d0395e08665000d4bd8bc088b4e10fa925344858fade613a908f7f32071a18ac00fe042488222d1781b8f7d4d17c02fc8e035c9a02150402053001f76e19cde9f1a171a18acea3de44c140e03cf40e35800350422201a2f0222d18c3dec35f4ea0ada06216888c1c68087908cbb2680d56a8e47e8cc5d03954c3b87a746759754677e08665cb0663558f26a2685b0b93529b4038d61305063998000d410888068bc088b4630ea3de7a8af85ccf08e7d242808f75c38327c483232c804959004391d45cb74f45c92a01f16787672e8742e20c680c7b1ca26c4070572ba4a81a9068e694801c33fa84a034ae98c07b0f710b8006e0be79a0bc794822324820b9b87895db265611a2a8a0150f1b56a3640954279ce3190a3410e02a60779fcd0b58073503389ed578e67658a0907b92000602283c168f776e1da014d6e0145dbf177e4f50cc4e85ea33c3dcdf4327dde7f342d62682f1d5e399c0050af00806ca724ed28e813a26023dd4039de1b8747c5bb76b449154315779fc578e6700142bc020a724ed2a02cf0f73d10e7dea07456e30e0c9f120c8cb20126475172dd3d1724a807c59e1d9cba1d0b8831a0810887d0247807289b101c15c39641a398ebe0c35f40c1e1800cd6e00b56400ae4cd169dd9516953e07062276b42d6022928d043808950c6428562c9aee288c1f0865ea3a090f5c1e95e8621d6bb2682f1d5e399c2e001b82f9e52088e6e1e25584695a8d8543c6c1cd40ce27b492082d76,
  0x15280a0d0ea17810312016d2f81630c812b1a81296f06e39306afc586ff7186cd2902e198cf362841154b9c0184003010060f8000d2108880d82826064148a84901a8007e3ea40a0d011d17810312016d2f81630c812b1a81291e8127a886c19306afc586ff7186cd2902e198cf39403e954b9c0e8fa50184003010053cc4b81c9060f804b700088000060350424892aa01840da6a1489a619240693e3e9c3e57026cbf06c1368aab292be4508ed3c08eb4e08e93a08e72b88e59f0119730fa30c8aa91a8aa71e8aa52f8aa30184054162053cc4b81c9060f804b7000880000603512aa01840da6a1489a619244f83a3e940a0d0c0136843312016d3c03f33a03ef9c2c701c586ff8e06cf2902e198f210184003010060f804b70000603492aa01840da6a149240e9808028a879cc3e8c0a0d0c0136843312016d3c03f33a03ef9c2c701c586ff8e06cf2902e198f21178f9f0c8aa91a8aa71e8aa52f8aa31f8f990184003010053cc4b81c92401f9060f804b70008800006035042221224aa80610369a85226986490783e843d37026c9006af368aab292be4508ed3c08eb4e08e93a08e72b88e54b01030184054162060f800880000d40a0981489a618780e85e3e7c71f292bef68191730f9b01840053cc000603492aa01840da6a149240e9808028a879923e740a0d0c013684331201933c03f33a03ef9c2c701c8071f8e06cf2902e198f210184003010060f804b70000603492aa01840da6a149240e9808028a87992730f9b0287a044c48038326a034041c5e040c6a03fcbef02a21b05bc1b8e4c1abca40b8661a9d8a1046500fa552e70061000c040183e00034842221220a0983f0641e07e3e67a8af8325cf0315c38303c482ff7d02fb91dc5d1915c5bf931c59b000e8d080a81e0e756e0f97ea2be0c973c0c570e0c0f120bfdf40bee6821be477174645716fe4c7166d961686ae324dd8f007c0a98342d6000508202a0921e1643e57a8c38345af8325c48317cf03157d0313939c60391dc5d1915c5bf9a086fab8006585c5a70593747c037763c01f939b8860f91768f8f5b8f8d2c8f8702a60779fcd0b5857b4600142080a8a78924801a3e4c5c5bc0f89747c03f00142080a8fc92006b4a860f9116d6f03c1dd9500bc004d0a84801a768f8f168ef03c15d8d0084004d0a84801a5b8f8d21bce752fb64e6e2183e256e3c15da3c1c0a981de7f000508a8fc92006b4a84af03e2cc616e05cf9a09a74f404b,
  0x190878990a861892a79a20029c176d96175db81665dbf0155d3f0125d8d0094004d0782a0922cb9816a5200dbe4cd0c3e6033025043c4ce893924941a5ebe0c9663b0f0f120cbe47717363a182e4f517742e001b816f59616866821d5dcf01d5d3d011dd1d00edd9500bdd8f008c7453ee40a9800e358045995ed19643e540050842488b408216e12421e2642a18624a9e80b4a6a83253a14e4b91dc5cdc38fb1480f050b8006585eb6e05999a2a076f405174f40457634021de1b802a60779fc57b46001421e0a824a4ea7a02d287453ee5b88609a2c9047688755baa039d4fb5590f9557b468b03c31b039b98e469fe0866d7c0c0ebdbbb8e803b721038fa80cc348036f986c68ff28659b38645980cc093e8f2410f132516c4e8f415e2b040bf6de91a970789ad822b4907019c24433bca6c4203d3068fad380f3d022546dbd23198278ac89f8a0a75d887cb267e07a5538213bd024b0a86ef9006af64871f292be238ab94508ed3c08eb4e08e93a08e72b88e5f681914a01554b0103779fc038d61305001840541623d0063f994a482e1acb34053cc060f804b7000880011662694a150f450701ad772ba1d870209161881e36bb222307c219701299a1690e4024a313aa000605083c10888088362d0ea0e85e5d0045de1b874fc5cd8605c91d43253a15fac38fb1cf0349768075c4832f2c8055941460d773460b93d45dd76f45db0b8006e0f9702a60d0b586585f975ace3f590f9557b46779fc948df300142080784f8a8a78928e8e753ed64239e7a8808e4bd0b58001421e13e2a3f293af039d69cd28e8139f4e893a15fa6e21801b56e0085daf17fdd8f165e4e50d164c50c0c00a6878a7bf293a9cd28745c38fb132ed30ee1e9d19d72c198c00fe0b485a422f18c2516c4d10403bd7c01fd30ee1f011a56623e072c198d563c9a89a04c1418e6614a6d0e03cf40e358003504222022bd8b43aa1690a642f01a3eb46ef292be4a0155730fa30c8aa91a8aa72f8aa31f8fa92582131e8d035db262a8a027982432542f066598ac39b248f934f8fa71e0fa15a022b9b8789e803b721038f5611a4ea0a56bf66883b588eeb0986c68bf28655630675558f26a06576a88b55d08b37e88b15b08af7b840e57a7c0d5f980b5038d663998018403d0063f994a482e1acb34889da398c037948053cc772ba1d870209162401f96787672e8742e112b0823bda8795911ee91aea060f804b7000880529b401166000605083c108880b036148203a89a,
  0x1520fe650824584a6685a43900928c4ea84c1418e661740dde58b0df54a6d0387d0e03cf40e358045980050820858422d242618883a8bc1803c3f346c12902e9f01131986a7800fa91e0f999403e954b9c0e8fc921038ff28655f980b1d11345f18e5a022b9b87895611a56bf688eeb04c3b86316ccb0663558fc51881e32401f94b81c9053cc04b70130500184000880380f3d038d6011663d0063f994772ba1d87020916889da398c0379486787672e8742e1126bb222307c219701299a1690e313aa4024a0e1f40014208216108b490986220ea2f0600f0363f2cfa30c812b1a81297186cd2902e198f212f8a8f1e8a911797401840772ba1d87020916889da398c0379486787672e8742e112b0823bda8795911ee91aea1881e36bb222307c219701299a1690e313aa4024a060f804b70008800116600142108b4220ea088600f036491040e8fc93e8c3204ac6a04a47a049dc61b34a40b8663c84be2a245e5d07e3e641a3e071a01fc061014a6d0e03cf40e358f4018fe652920b86b2cd014f31dcae8761c0824592e072622768e6300de5209007e59e1d9cba1d0b844ac208ef6a1e56447ba46ba862078daec888c1f0865c04a6685a438c4ea900928183e012dc0022000459800508422d0883a8bc088600f036251245f18e2a15c03cbd80028343004da115d14115448064e76f1c87201c7dd8092f5c1e943204ac6a04a47a049cf00fcd380fc4e80fbde8621c61b36381b3dd6b20a40bac6f48663c86646885e5d3a00edc840e3c7e3e66a0330e61b1a3fca19641a9a2ce1914fa3c9043c4c4c1418e660061000c0414a6d0e03cf40e35a920b86b2cd06c0e6f82618f4018fe65014f31dcae8761c0824592e072622768e6300de5209007e59e1d9cba1d0b844ac208ef6a1e56447ba46ba862078daec888c1f0865c04a6685a438c4ea900928387d0183e012dc002200045980050820858422d242618883a8bc1803c0d9563f17b8a80cc3cb066db386453e8f2410f13250665038d613050000d410822488b43aa162f242e09864d17c037d0403bd30ee1ee31a2df011a572c198d563c9a81a3c0e3584c14000352f62d0ea858bce124299261b4e8fb13a27a80b800af85c6e05cf76802f6585a1c48b4cf08e7d2429a09a74f404b765c033763c027809aa779fcd0b5857b46590f952cb9802a6000142109222d02085b84,
  0x11220e261ba018400088001166078ee02a98000780822422826418620a12e60200878343fbd6a11a2a158b22e8742307c2e20c2197a2719a0b0b6869ea681e60011009b540583ad190fed30d55846b14df95a3ad5681c0e70b10e71605be6e08858c3a965217b5563c9d6b38fc2e32dda83245643e54b2e6186322d5ed186c056528b008e316c9a31654a6d208a586efa0bc7d084326c30c794cae18ab11de7f00e3584c1418e6600c040022005c322424aa952978045981e3b80aa60001e0202282605044511808021e0d0161f83e0eb53e0e096240feb0b866b483e8f9c604be4cf8800e8814188281220e0b83e384466b483a3005c604c4f02404e823f40610000348208908a18828bc8a60d0fe702834041c48055c5e05546a05447a053e4c1acda4e3800b7896110780521e600123f94cc34100b14c008db38645d30657fe86393e8f2489862506650e1f4038d613050000d4080422d382980616908883a8bc3f8e362719a0b116de91a310c03c4070970789580767572baad82156101e54a819dc70fdd00224180ae93b11c3f849e9488dc8000604d8fdf15d5680b5d36528045834bd7e27cc3cea8f6e1a23b35ff54668b03d9cc83d945a5ebac1485357141eee13fcc2b70cab595a3526b41f0de34df101c02c3415581e1d9cc88e6d295cae9c2067e6e08651007462206e52a0687de3f6dc83daf6c3da400182243b11cc70ae93f74fd91d8739770fd500060890ec4731c2ba7de3f6d9a1697a0b148ad07ce98c0673227b1da4401cfa001b72b74fd7313aa2b0fd300224c70ae9470ec183de570fd96685a3f3c2c3414c4ea8ac3f4c761ce5dc3f5400182243b11cc70ae9f78add3f5ecc5001a76401a370819f002243b11cc70ae9f79dc3f559a310c211697a4d3c5332e0d3fad07c2e8769673220b148bb851b6781e74401cfe98c02b76cc7b1da5001bf6401bba00fd1000ac8931cf78ae9570603b11c3f4cc21bb8dd72e0d3f160d2f3202555f824d2e8c033db8641b4ed519a168fcf4d3c51d2c0f6730adc32ad6378d370b0d0539b4a7081b7720f6beb0509208d33db0f69000602b224c73de2ba55c3b11ca00fd1b3140081d90074d76c99aec88aa2808c1f09e738865e80018224c73de2ba4ec470add168fcf4d130ee17c01fd043e0f2c198e621885563ca5f90d7da89a13e07047806a51c3414363f2dc206dc1c06b536069518067622769dcae8e6300f4018761c0de,
  0x127b742a877153820f4095478aa45fb0a3410edb0f690001c3a8463077ee3064bc10858168c214185450901be634a40140a98000151421e0a824b241d160a98b88319e07dda081000070461683c0c10173b0c1a096e120b346cf722c0bad9638d4c642902551e2a900016906151423d9015e3928057c2a133c080835fe1db54e710283e00220004215c007c81c058181590133d2c989e824f5210b612a9980c040ae2424e8242d382434f0243d142444da244d082454283e00220004215c00070160615c11901138343cea9a0fa800348a6160c4403cd2f3d82cd0f24a5fb0a409543410edb0f690035afb8c19308458088c1d8485a40360c2719a681e6310a110b11200012190b809900b3a65783a540035054068f4090220213a0c10090286ace834ff87a8c85e04b4bea427c1aed2cfc1acb49460b84883818245c061000c040022000421443e978001f81a941520512e18a1e0a10073e2d96175e52343dd3f010dd9700ae4e6e1de7f15ed1a1834456e3e35da3e3c7839169c3a353e400c0a9800050854248a8d290053927120cbcb201570e0c6ebe0c66680c464f51775dbd176e45516e42e001b8325d96171e1800fd6400ddd1d31440a9815ed180050854248a84f900302b6a0330d040287e6197ece193c00fe038858b4908881b900118ecea3165ecb0254000e12222286268fff18ecea233decb02653a3485a223357423254a230c00351224f85c3ff4f225063f6a06351b862db380a7fe8097c680870003848a860908e3fec0ada80cc34100a1f9865fb3864f3a8ff71305001166078ee02b08000200e1222206c2f2162d2423fe5344c009d380093e686497b2c6355f00af3e8f2d30e752506415b0373962c37d4e8ff5410c557e8b91038d61305001166078ee02b08109f4000200e1222206c2f2162d2423a8ff7829aa0e256c0e0da20dad740d9fca196660318dcfa3c8943fcc0e3598e6614a6d10431540035038488882f2162d2423a8fb14e8ff52274fad8288754d1740e54e0030da20dedaa0de53002778219972c198f4819079a18fc4c1418e6614a6d000350382f2162d2423a8fb1d113a250ff3281f21dd49e60b30133d0c6f8000982c058465382a3fc56a11877515876d2a8a0279825db381299a24815b1690a6906efcc04cf431be258feb190fed08b3e48011f1809ed743889f2da4f04992902e7484a319ad20e8c01298fe77181313c09013a08fd6bb8a3134e060f836b04,
  0x1fa900f59e4357d06d3b5440d76c3da400481dc1609c440e42b10371f0865c19c2c900c28cc5aae234bc60ae8c89d0f60f8761c0b08d0c2958ca920682d8fe65082458722884a669c8378f6c3da4004412077058270e42b35440d59a0b2ea310df5a6d5ee27b7468447912a877100176852c582704640ce0a6a88b57e88b15b08af8593423902f5f0a414c0a3f410a43170d21688b99618d1b3d01c7a0378398c037a847903ed290054f9003213c21a20c7d874582a66781f75d0b9f038d61305063998529b401085707ba41b3dc3190a0005a070463ab84150f60883040c60a6a88bf7e88bb5b08b963998000d43ea4fb54eb9823902fde0e630222071cdea11223475e40fb4a40153e400c84f0868831f61d160a999e07dc8840ac5cec004215c1ee906cf70c6428001681c118ea108bc150f60683840b60a61836d7e88a34803ed11343fa845f008f5d039568837b6a83794c009de98c09804631fe862fe08665d20641e6863f7b378558f28881c76a268488e41268c591305063998529b4238c5b5b0d23173b0380c57038d60108570005a070463a8422f0543d81a0e08840acceb618849173b050901b081f40c10171c825d6dbd25e2b008a4a32ad630adc4095478aa4323762c02893410e010857093d44aa661d870209027000581285a070463a8bc0f1029407c0895024780ac409472898c6428001604a1681c118ea20902740541ee922034bc203304cab58c2b717ec28c8dd8b00a25c8378cc4f58d043b6c3da4001604a169062b102540541ee922034bc2033043c7817ec2872898d0438b03d9c9c669c8378fac2d9442407cc437d42640849edd0aa1dc496e394e083d28057c6e281c283e00220004215cc83d95357141ccab58c2b702c45b6c3da40007018118822f10234289c6690c6f8c42844000484a0a8264085f40c101708a4a2b0f6d15101b07901d1ca2678aa4409543410e2c0f672719a720de3eb0b65310df5010857bb84ff320f654d5c50732ad630adc0b11627b742a877153820f0001c3a846208bc10858407cceb6dbd25e2b008a4a2b0d2f3dba4618849170847320f654d5c50732ad630adc0b1165fb0adb0f69000d43a88210858d68c2140223bb181e4074f1124b2421038f4100b1f28659d30657268c590c101706835fda06253e8f24e8ceb238c5b173b0250e376dbd25e2b008a4a2b0d2f3d9015380c57038d6010857720de3310df5,
  0x12490037474c5159220213c206825b4803e07ba4880d2f080cc130a5632a481a0b63f9941c8a21299a0f24a313d62c0289323765fb0adb0f690035a1609c08900416c1df08a4a6bb222b10252307c1ca262197a3410e2719a3110570b116720f6b000601601c20905934bcb00a857e27cc3cea8f6e19a0faaee13fccab58c2b70c83d942c459357141f6c3da400d6858208c4415c1ad092aa772ba54a5e1d870261ba209161c8a21299a1690a310a01431be4d9c56325905327b742a87775d820d000340f87e070600202641541316b388150ed38e33e1081ad9902470e01df772bad707a56bb221d8707a1882307c14a1420a2675aec2197a3410e2719a0b0a2419ba051051310d771b01593182c14a2c00116607884b1b8a0b82296000340f87e07060020262590536e218009d64007dda00ed6e00e5d8d1685d1f171cb23c9ef03b0ca8c922c06561205bc2004c7da1c8dfd11c0dace2276f117670b10e638cfa64091d8c089c38077f5c1e966e1e25aec89e862192ca95846924a088c1f052851d6bb1e2a915a8d902550865e8d04389c6682c45b101c15cae92a06b41aff824aa92c8f9529780a981de7f15ed181e212c000d03e1f81c1802624b5405105127c43adfbafa371c0029836a50ebf1b04218b045906bfc0803f97026c1fb3e9db47236c2c074388c80189692fe71a906000a2bb960301054162078ee0285d50ca70018403a3663c34054a5e1ea324b23e000d2258222a0141106276144bc83e43950eda29cc13904d028343a84805b47a049c5e040c6a03fcbef01bc1b97161c1dc61b5e4c1acc00b78a805090189688784404904b4d08e031d7c02fd300375040384e0038c00fe1ee32d216cb10494d09a03157c02ff6e199c5c23348e2307820e644c1400035008252a0d13843a9a2411c5632582c14d94a01430d77d519a0b2eaa6d5ee27b7468447912a877100026852d762704641156eb52e0398c04b82837a840002616846058fe410ed88f27a1d87005026120a2600026168460587241042e198bff36b0401840000d2088145a062258a40a103f2c07e112c34047d080f9e74f1c467cb6a50b98fc0480034920a4826419e4682c240044b183e40f47997a188a28c4fb75ac87602f5000260b056059e240ec127800d157186d7002de5a062110968e9d80490391ca4cc5a95c099460284f5a34bcb00a84c20a14ca099cc809557e0934f6e19a0,
  0x1648240e01a5086673180a2820480840224e39d5075028480383204ac34041c6a03fcbef01bc1b65c61b2e4c1a945eaf9460b9d0e303e33343a0c8045981e3b80aa60003b2060a3a2b7844190982b2001493610e07841ccd2f2c02a13082855f824d3209fb3289f50f3aa3db86683ea403d641b4e4d2c5494d5c54ddb0f690035a161f631107134bcc809557e09343cea8f6e1906d3b54668b03d9cc2b70cab582c41b6b41f19cc8910077c2241ac4206b5dcae8761c3ac1424824165c83daf6c3da400180582701c41bce4b2c8e4dc3831baf83199a0bc791545b96585c757804186003f0b8e452490037474c5159220213c206825b4803e07ba4880d2f080cc15fb0a322740f1e02c23430a5632a48341701a0b63f9941c8a2db0f690035a160242182c41b50672c234322741a0b61c8a21299a31106940105b218d3d231de6b81dd720f6b1d870209059000601609c0702241acead0f3aabb852f4d5c53700058572b4311069387ca80e34920e765a9196e62b19acfa3c81e21249418753a37df4c02b66201f5a22e86a0417c78418daa2e5e64091cbc083f5c1e9576c99e8620aa281d6b209e60ac60ba50c0ac6e234bcf641945c4185742e7c8807d52207159e1d9e22768ba1d0e63003c780b8448de52072289c83dac6e282c0e3584c14004215c4206b5dcae8761c0824164ca0a0cc20a176c3da4001805807022340c2130742c419d342680f32380d73800a34100a15f009f7c0c69b7a7c67bb386453e8f2250df99902474c0c3bd707a56302277a1889b878975ac85611ab182eb56bf68e8fb588ec2cd9a03299485ed93d45dd0b8cb775ace3f2cb98590f9557b461b3dc319829f8a07cb2653820f021063779fc02a60213c2e802df06825b4803e15028d07ba4130501c8a23f9941a0b6acb344881c5889da398c0379481710615d0b9f2201f56787672e8742e112038d61b8a0b0108570006007024088d00b0f64194627da035d3e8f24e8e9925061d5e0c3b98807da8105f130501710615d0b9f038d6000d43a824088f40c078021063233d3a3485a223354a6d000350ea3ed45c4185342380c72680c53800a34100a15f009fdb8669b386453e8f2250df9000eaa1bf8090223d030022a02d105f014ddbf177c7453ec64f50ccce893dd59617e7120c5e5217b645716ec2e32de1800fdd6b38fd5e01056400ddde7f000508204f878a786c747f4a4174e4b2c8e4dc3831baf83199a0bc791545b96585c757804186003f0b8e45,
  0x1140043700e192c0009022021b62a0302d0ea42350611b8ecd6888cd6a88cb5d08c97e88c75b08c55288c313050000243501a17108b41846e3b35a22335aa232d742325fa231d6c23154a230cb4421c54420cbcdca081bb528056c6c387ca83aa9e060c78041d3e04744e02848038326a1220fa48810446a03fcbef020151c26a21addbc1b66fc1ae6761b6e4c1a945eaf9460b84c140043700e192c000a3a2b7844190983f26a800520a8240887e508a44224c3ba8105f1b8e93630e9961908513050010dc03864b00024088303d01a21092020202d108718766201f5563caa0417c6e3b35a819ada20e2d740ddd6c0dcdaa0d65fa0d554a0d47820e765a90e3e58b0df65f90d7c4c140043700e192c00090220c0f40688424808080b46190853b445c41846e3b35740ec56c0d8da20dedaa0d65fa0d554a0d466190ede6010dbf480dfe5f90d7d3a40244c140043700e192c00090220c0f44801ae809202054420c0a1200e0c9a81a80ff2fbc06f06d99306a517abe5182e0f907f0d084b00028e8ade11064262001482a648240887e0790814d10403bd7c01fc8e029c9a0295300275f011a866218b79a1934e03374ea3b4e64117cbcdca76f1c86081bc44c140043700e192c5c211d86212420c206c179d343b8000a992090221f81e0f907f028be3cbd1410746a04a4f00fcd380fc4e80fbc7e214448064c5e064432063e081bc5c61b36381b3cd43337201c7ca441ec20c2108213434212d343b94241e40c040183e0003b0d281828190983f0ac800520a9920913610e107d02848038326a0bef006a3badbc1b664c1a945eaf9460b8061000c040183e0003482819098800520a8381385429107b332f120c5f3c0c55f40c4e45716feae001961715d1f00de4e41dcbcdca081bb69c332528056cb23e1d5ed186c387ca83a93e04745404cc4e028480383204ac6a03fcbef02a21addbc1b65c61b2e4c1a945eaf9460b9d0e303e33343a0c804599de7f00a9807841cc183e00c04006100003b0d281828190983f0ac800520a9920913610e14241e5b88609a7688755baa039d5075779fc57b462c8f871b0e1f02a60000d20a200149920903806942199cc6028a08120210089390773c2ea04d05c032c8e031c9a03150403057c02ff6e19a4fa336ce03375dcd01e5863356026e2643ba5da00ed6e00e62c184e45716fdd1f16f6ae0025052eb5962fac4c1400459a9c3324b23e1c0a9815ed186c387dde7f0003482880052,
  0x19306af6906ef7186cd2902e1986a700028e8ade110981e0528002a9010a931ac08157c2214ee64162c30154cf41494007dba6352b49f9d610a30429dfaaf85cc48b4cf08ec38fb1809b8578e676585c576803b5b8039747d05d779fc1510a3001424f878a78a81b24ea70e75d290a5392cb239370e0c6ebe0c66682f1e45516e596171d5e01061800fc2e391492400dd1d314564880005093e1e0a81510a33904207d008157c2214ec30154cf41495361333c7ee71140f3d380f2cae0f1e40427c043700ebe0244265d8092c96084c62078f5c1e947a340d76c99aec89e8620aa2808c1f1d6b209e608865c2c60ba50c0ac500c28e2372c061000c040183e012dc002216c14f31dcae8761c0824592e072622768e6300de522c208ef6a1e56447ba46ba800180ec0d9f61902c2b17e428509d1e010724815b15013307884b8e8cd11380a2fbc01a81291201931781910c818f9306af6906ef7186cdc8071f2902e1986a700028e8ade11098800520a99290109f398e680be564007e4c51655d8d164d3e39a42e426c00508201b22c06909d6e1da01d61800fd6400dd5e00a56e0085dcd1865d1d1715d8f168ef039b4b239ac0a185dde7f0008b1420806c0682e426ced30810871b0e1f2a108d1e10931b90911710972204114883e99d86e3bf06c1531569f01116000a0d109599045f2f3721a81291201931781910c818f9dbc7216906ef8206f17186cdc8071f2910890790810e832010dc03864b0e107d8c05110184003010060f8000ec34a060a064c40983f26a2b2001482a648244264c7d2100bb48009b1b00c90800a9d306617b2c63dcb0671e6864d3a906106908b5d08c9010dc03864b0002408942020f40c05c425c64d3a9061b380a95d08c92d109306908f24815b150133010dc03864b00064090221f9420f9ac4a0086d8344255344c007d2380c72680c53800a34100a15f009fc68627db8669b386453e8f225061fda035d4e8ba9688ba15b0b9b6a8b971b909113050010dc03864b00024088086d8782d10934d10403bce0020d7c01fc8e029c9a0295300275f011a866218b79a19344c140043700e192c00090226d8b41b90914d10403bce0020d7c01fc8e029c9a0295300275f011a866218b79a1934ea42345c422c881046761b8d4c3a884387c4c140043700e192c00190240887e5083e021b60d06c06908f4d13002b48e031c9a0314e0028d0402857c027fe6196f6e19a6ce1914fa3c894194fca0e353a37dda22e85742e7daa2e5c4c,
  0x14c0c3b1b90914883e922041163043b99045fbf06c19d86e39c2c7019dbc7212902e1986a5530ea9f011d4b01071380a0e10731210bb0c90bd2f90bf1a90c11790c3000ec81828e8ade11064260fc2b13e1e0a8a1bf814924648244d847e2d200431471f292bef68191003a2260526485e430c2e0f86cd1986a56b01294b00ff00028e88981486a43042e0f86ff1986a57f441634b3c000028e8898490be42fc2e1986d90f86cd531a86b012b00028e88641483242f42e0f86ff1986d97f4416d5300e00028e88644904842ec328c10b51fb9c170c89000ec819f6113a62b07835020ad092de9521090b902834041cbef006a04a448064c5e064432063c7a062e4c1abdc61b37201c7ca40b8661a9c000a3a2b784426078149929010b73244fa3c986322d4a6d0943a948e316c6efa0bc31d49a3ffd7815cc2214ec30154cf414940e3584c1418e660007dba635020ad092de8422d23042d5f402055f08853b0c05534d84321fb9c09109976024bd707a57a18875ac8b182eb8e860b773c0719390ad0b8006590b16e0f979a10af9010a92582131e8d035db262a8a027982433dc388dcb0184003010060f804b7000885b053cc772ba1d870209164b81c9889da398c037948b0823bda8795911ee91aeae802dfacb3402a60d0b58011661881e36bb222307c2197040028b1510a3213c21a0b606825b1c8a24803e3f99407ba4000603b0367d8640b0ac3d86c42cc055d2905d76f45e974745c5001424f878a78201b19642c4bc757bf8001421b26842bccbb2380a72680a54c009d7a74683e6864d3a90631710972204114883e99d86e3bf06c1530ea9f011d1380a2f816363043b1201571781552f3720c812b1a8129c586ff9c2c7016906ef8206f17186cd2910890e10730e8328c05111090aba75d887e07a5bd024b648ec75a022b9b87898b060f5611a941434d56bf63a14e4d88ec2cdc383039485ed6585d7931c597773407775ac06174fc0497634025d290a5388dcb4b81c9889dab0823bda8795911ee91aeae802dfacb3413050011669010a92582135db261e8d032a8a027982433dc398c0379481881e36bb222307c2197040028b1510a3213c21a0b64803e3f99407ba406825b1c8a2053cc772ba1d87020916060f8030100184000885b04b70000603b0367d8640b0ac3d86c93a9c39d50ad0c87ee7230429c003b2067d844e98ac352b49f9527584242ac0a0d01072fbc01201571781550c812b1a8129,
  0x14b81c9889da398c037948091e01c8a23d0063f9940c2041a0b61a90c1053cc772ba1d870209160184000885b04b70000600d9840b03c800526490d1950c6608bc198e7e281563c9f2c99a89a14e084d4a6d02a1bc46e18adb0108f6eee26201f46c4276a04d23a116c540fec1e21345c2afce02a5d7c2a248e2ac5042a3c9a2a8dc03cbd80028343004da115d141154f00fcd380fc4e80fbc48064e76f1c86381b3f201c7ca40b8663c747e43340c040183e222768e6300de520247807228830810682d80e3584c1418e660048703242f49007e46a430412dc05e430c14f31dcae8761c0824580610002216d78ac102fdb7a46a5c1e26b608ad24432c00180366102c0f200149920690cf3dec5c39cc089501e212cc66084e02a7e280bef0038e3048064df2c9a4c1abe381b3f201c7d4e084ca40b82a427c661a9d52e700c040183e004870247807228830810682d86a430412dc05e430c14f31dcae8761c0824580610002216c00180360b03c80052879926301a1f90cd4d1043e0c8e021d740e5530ee2623e057c63b8219972c198d563c9a89a09a5294a6d06e3df45c39cce03cf408950c660a7e2813e04758c10ec5404cc38e31f2c9aa21b0670b1c05c61b36381b3d4e084ca40b82a427c661a9c1e212c783e66500fa552e704e0283a3e74be42fc4842ec0c040183e12e072622768e6300de522c208ef6a1e56447ba46ba82478072288f4018fe65030810682da920b86b2cd00e3584c1418e660048703242f49007e46a430412dc05e430c14f31dcae8761c0824580610002216c00180366102c0f200149924910cb1934ea4186ce02a5742324b443143841cc7a431c3a0ca3014444242e64042ddd8092f5c1e95e86216808add6b226e1e26c60bad5846a3a3ed55afda680ca623b0b364f517765217b42e32ddd6b38fcb2e61643e555ed186c42cc62078daec888c1f0865c1000a2c54428c4c1400e35804599de7f00a98084f0ba00b7c1a096d200f81ee922034bd7e4284e2372c061000c040183e012dc002216c9007e59e1d9cfe652b2cd0ca920c2958b08d072288c89d0682d814f31dcae8761c0824592e072622768e6300de5204a668c441c4b834fcba334dc83dae243f841c41bc8a3e15363f7f6c3da40018058270ac43242e0f86cd1986b76b01279f011300028e88fc1487a431d342380f52680f33800a34100a15f009f7c0c69bb386453e8f2250df9,
  0x1060f804b7000885b2401f9053cc772ba1d870209164b81c9889da398c037948b0823bda8795911ee91aea0121c091e01c8a23d0063f9940c2041a0b6000603b0366102c0f20014878439574730fa32f90bf5a022b9b87895611a56bf688eeb01b90d9630ae0e0c75b0823bda8795911ee91aeaa482e1acb34130500c90bd1a90c1018406dbd278ac8a75d887e07a5bd024b6490d1170c890121c1f8f994b81c9889da398c0379483d0063f9940c2041a0b604b702401f9053cc772ba1d87020916091e01c8a200885b078ee02a98000600d9840b03c800521e0202f0e83b9cda107d080f4d140f3e081bc64042a4e80fbcf00fce381b3c000a3a2b790fd11098800521e03a0f82a4384d0786006376807559004f75a45ed773460b76f45db0babc57b46e803b748036f8483a91b039b986c68b980c6339754677e08665558f24e902f6a06236888c15d08bd7b840e7fe8097c680879090d38b10d52694a529b41b90d90e0c753d0063f9940c2041a0b6a482e1acb34038d613050170c89091e01c8a20121c779fc078ee02a98000600d82c0f052990780818c2f0aeea2680c76be0d0f3c0c570e0c0f120bfdf40bee475174e4e7180e45716fe4c7166dd3f010eae32564e32dcb2436e1832c742d615ed18a837cc1e3b80aa60001e0208e8929493ea782eaf0006586076e059976bc06b763402502a9800078a782e2c90db41249a0295ee11a4f6e19cf9a193400bdbf82d0bc0886e43650492680a57b84693db8673e6864d3a90d50e0c7502254319829f8a05e2b07cb2640bf68e845b538213de91a7026c0a86ef9707892b88ef4a0157ad822b5100a490fa32f81890d0c01f687233684574504550301054162060f8889da398c037948b0823bda8795911ee91aea091e01c8a23d0063f9940c2041a0b6a482e1acb34130500121c0c90bd2401f91a90c1053cc772ba1d870209160184000885b04b706dbd278ac8a75d887e07a5bd024b6490d13a03ef4e03f13c03f38e06cf000600d9840b03c800522d03a508200f9cc9db50d71a5e63b0f0d563c93a40bda8188da223057422f71a021e42434c9a5294a6d0247807228830810682d80e3580487000180360b03c14a642d1420822c630bc3a90d53f353a3d0404870001803c108882d1420818c2f0ea85a42434cee73684573c03f33a03ef9dbc7218e06cf2902e4203d34503cf198f1d9010b71f8f990690cf1790c30301054162060f82401f9,
  0x1f6818f531a804b705416200885b63998268fff529b4238c5b1bbe813050038d63a04174e041945041d36841f8206f12582135db262a8a027982432542f0c753d0063f9940c2041a0b6091e01c8a20121c000600d8640b03c0e03a2d0200f8327020a5d08ab5b08a7e11347e83bb61837d68837b6a83794c009d98e4697d20641e6863f1305063998529b4000d40e2162d0203aa4221d74499094368f471bbe8170cf91380a1200e0c9a81781031a80ff2fbc06f06e39306af2902e1986a762841154b9c0184003010060f804b7000885b2401f9889da398c037948053cc772ba1d87020916091e01c8a23d0063f9940c2041a0b6130500121c08a4a000600d9840b03c801001faf23e071a021d563ca423eb5a89a09a5294a6d06e43645c39cce03cf408950c660a7e281f2c994e084c2a1bbd28056c6c387ca83a85404cc1e212c4e028480385e040cbef0038e31bc1b8e4c1abdc61b36381b3ca40b8661a9d8a104552e703a43b4784395b6f49e2b229d7621f81e96f4092d9243446a43043242f4061000c040183e012dc002216c9007e414f31dcae8761c082458247807228830810682da920b86b2cd00e3584c1418e6600487000180ec0d9840b03c80052450c01368acf3c0acd3a0acb1380a4e8d21178ac72f8abf120ac96888cd5d08c95288c32d0f003010060f80121c0c90bd2401f91a90c1053cc772ba1d870209160184000885b04b70000603b0366102c0f2001483a43b4f81c68087558f2908fad6a2682694a529b41b90d90e0c75380f3d02254319829f8a07cb265382130a90e9078ee02b08150f45091e01c8a23d0063f9940c2041a0b6a482e1acb34038d613050639980121c6dbd278ac8a75d887e07a5bd024b6490d11e10e5000603b0366102c0f2001483a2d0f01bbca4af9280555cc4e00610002216c14f31dcae8761c08245800180366102c0f2001481a0e8b40802a43a440d9d86e3210e1f531562484236000a7026c0d0c012b844d12015736841f45041d3c03f34e03f13a03ef9db50d76906ef8206f18e06cf2902e198f1d0301054162060f8889da398c0379480c90bd2401f91a90c1053cc772ba1d870209160184000885b04b70078ee02b08000600d9840b03c800520683a2d0200a9cc4e0f2117abe5182e0f90e12582135db262a8a027982432542f0e8150f451f8f99170c89018400301054162,
  0x11a90c12f90bf5a022b9b87895611a56a361790c34503cf90109f2582135db262a8a0279ce1881e36bb222307c2197a76024bd707a57a18875aec1e950060f80301001840008800121c04b70000601683c0d8b40e898199103829740e55860df78219b74819276eee2ce0274000e0bc3f14203ea5a83eb4fb13ee7984c1101ae8761c12af3082898981a9d06781520f4c423c441a427494301e3a116c92108c8e2acc9a2a95042a44e02a65c09b07e117cda115d141154f0114d382f8e081bb676f1c75460b83404c43e1b3432045c6a03fcbef00e82354ae234fda062d28053dac049e7c044e4c8c808950c642978ac102551b6f49e2a904c140061015058862078c96084d76c98aa2809e739d8092f5c1e95e8621d6bb0183e012dc002200048701e3b80ac20543c6c1c077c22928d0439aec888c1f0865e8001805a0f0362d07a540c7508a4a170ac1341701f83e9ad07c02254bf06c167322319822902e4401e39f8a01986b71490c77c8d039f01138007e0c2043d006091e00121c2b10c94b81c9889da398c01a0b6379483f9941c8a21299a311071060f86787672e0d3f0184004b702e8cd300885b890fe107106f720f6b4d8fdf228f85000601609c43f4c01368acf3c0acd3a0acb1380a4ea0a178ac72f8abf0c8ac51a8ac3120ac96888cd6a88cb5d08c97e88c75b08c55288c32d03a1faf234170ad07c673224401e31491403010060f804b7000885b639980121c000603b0366102c0f2001f82e0f86ef1986a54a01554b0103731082582135db262a8a027982432542f0c75150f4504b700184000885b053cc772ba1d870209160121c091e01c8a23d0063f9940c2041a0b608a4a34170ad07c673224401e314914000603b0366102c0f2002d03a3b9cf0101d080fe6761b8dd0e22401abd4c559c6a412cf01800283270034340448055c6a0544da107d141074e8105da41bbe081bc4a40b8663c84061000c04150588183e012dc002216c9007e414f31dcae8761c0824592e072622768e6300de522c208ef6a1e56447ba46ba87ebc86efa04c14096084d76c98aa2809e6090c950bc31d4f4018fe65022928d05c2b41f19cc8910078c30810682d824780722880487000180366102c0f200188b4081cc42038ff286594e8c913e8f2250da6dbd278ac8a75d884100b15f00af7e07a5d30cfdbd024b2a040d7026c64871f9d86e33c08e32b88dd,
  0x1236676d113d0e14434be559bc1b65460b83e441c4842ec3242f49007e59e1d9cba1d0b8831a0810887d0247807289b101c15cae92af3098441408950c642806100543c6c1c077c22928d043862078daec888c1f0865e896084d76c98aa2809e7396808ae6e1e25584695a8d9d8092f5c1e95e8621d6bb0183e012dc002200048707a540001805a0f0362d03a443c6ed6c110b4a0151a291090d0c015e2b0409546dbd278aa4060f82b84013c040736840b9d86db5182e0f91071210bb0c90bd1e9505a022b9b87895611a56a362582135db262a8a0279ce1881e301840008800121c04b702401f96787672e8742e20c68204221f4091e01ca26c4070572ba4abcc261105150f1b0701df6bb222307c2197a022543190a08a4a3410e000601683c0d8b40e90e14434a95d10f112484237026c45041d4e041954162008804e8ceb3e8f21b8f3f38394038d62516c268aa7238ab5130500121c0003c0e0bc63264110b40e842af10e9bc90e11a9b0442c0a5858ea5e6863f558f17238ab97300a5e2b0409541305003010060f82f9566f06d95182e0f91071210bb0c90bd1e9505a022b9b87895611a56a362582135db262a8a0279ce1881e301840008800121c04b702401f96787672e8742e20c68204221f4091e01ca26c4070572ba4abcc261105150f1b0701df6bb222307c2197a022543190a08a4a3410e000601683c0d8b40e84ea29109028343004be058c5e0554da107c6a04a4f00fcce80fbf161bfda41bbe081bc5c61b36381b3c0c040183e000348281482a492000ea1e5103e441c423700ce536841f1b109d3c03f33a03ef8e8ecf8206f11e10e18e06cf2902e1991030184003010541621881e32582135db262a8a0279ce5a022b9b87895611a56a3676024bd707a57a18875aec060f804b70008800121c078ee02b08150f1b0701df08a4a3410e6bb222307c2197a1e950000601683c0d8b40e89844160a5d08ab618aa1e11344c11016883b56a83897e83855b03834100b15f00af986c68ff28659d306573e8f2529b41b9001a482e10c204acb901a20ca6d5ee7d8746844795580767852c23b6101f92516c9a87091910bd238ab7268aa9805c17d8780a1201576906ed6c04231b109d1e03d30d0c01700ee73684573c04533a044f9dbceff8e8ee9022543190a5e2b0409546dbd278aa4038d6130506399854162078ee02b08150f1b0701df08a4a3410e,
  0x1763d127779fc02a6000142fca521e34abc20293912917b42e001d6b38fdb8166564007c004d29afca521e2f0763d1276e218009d64007dda00ed6e00e5d8d1685d1f171c001529afc878d29964494c956e05998600272c8f27480c7176345a12a324bc0ec306bfc8b04598484357026c4504319db47239c247034e08dbc8018dc58e39a280a030105416202a60779fc57b46060f83a3663c340000d25a1d8248548794213828512f20fabc902000e98073112338e45e04b4bea41fd11c0dace2270b10e638cf800b78625a0225e04e111440f87e4486ba4a81ad1d870090ed39902472f020f0e01df2090591b8a0b0108571b3dc3b0ee3880d2f080cc10f111dd707a55db266bb227a1883282c52a8a03082b32307c2c0289323765fb0a75aec40954279ce3190a2197a3410e2710fd720f6bdb0f690006016111f1b2d460b9d0e303e1b343a2b05ac049e0002832446c48446434445c5e430cbe42fc6a430414f31dcae8761c082899067804232241a42763a03e492032df031a8f6e19ccea4185742324b444541e3b8183e00ac21d8092d6808ac96084c62078c12dc0543c6e243f840c040061001c077c02201b6f48089502292804871363f7c8a3e14d0438c6429e2a91aec888c1f0865e976c98aa2809e73a6e1e25584695a8db5c1e95e8621d6bb09c43f400180580f111d1b2d460b9d0e303e1b343a2b15ac04ac06100183e00220000350380a05217032446c6ed5182e6c3720f86ef0e8ac94a015701840060f800880000d42f0280a85c1211190b83e33d4661a943a30052c041cda2414f02404e823f4061000220004870001683c0d8281e0980d1117192658b0df4fa3c93a33a49432846e18aece02966202161644448ecb8247807289b101c15cae92af30981a952c041c1a427492056e52345c4e02a3a3b9432063cbe058c48055c5e05546a0547201c77161bf5a41bb5460ba76d117e70910edb0dc83e33d43a443c7a54008950c642978ac102551b6f49e2a900e3584c140061000c04096084d76c98aa2809e7396808ae6e1e25584695a8d9d8092f5c1e95e8621d6bb0183e012dc002200048701e3b80ac20543c6c1c077c22928d0439aec888c1f0865e8001805a0f0362d111519ccea316f2c031c000e0bca184223b2e19fe5d70ea5e9f0344fa3c93a33af443c446e3cfc945b04c140e0e500e35804870000f0382f18c990b48486c10a169091113bfe3a3bc45e239c6a,
  0x14c0c3b2201f56787672e8742e20c681e6240b8d3c3403a3661ea321f912154a5e4b23e2bb96198bff29103f36b041220e060f8030104928240954038d6130501b8a0b6302279b87895611a56a360ca7014a143410e0a9be3190a0184000b0216111f00060168d40881c25014138b4703840a11399b11423b53823a55058800349c00a2f2af03a43850e917913710c50ed9b27091c0d38236f1638e68a0280c04150588183e000349688784e70028512f20fabc0ea0043850e9601cc44d50550e8c0129103f04b8e4a015b3689053c09013a08fd00b020a9be3190a49282409543b0fe122820b5db262a8a0279ce0d81e36bb222307c2197a14a143410e16111f4d8fdf0006016822020920503444cc0a12016d1e812706010b1781031a80ff2fbc0c587077186d79306b30a112f0301049282409540ca70261ba1ca26c4070572ba4a81ad3b0fe122820b5db262a8a0279ce0d81e36bb222307c2197a4d8fdf14a143410e0a9be3190a0184000b0216111f00060168d4088921504225142139131831a0799f61d090b11601d9e76103d8407d4a84135c09b03030ed381145140fd6a04d276d1c8dd0e206ace85c2afce02a5d7c2a248e2ac5042a3c9a2a8f200625c6a427c044580448c5e44b47e4484f0d00e8d987a8c9529792c8f8aee58a440fcdac1048838183e00c0415058924a090255192ca9e2a900e3584c1406e282d8c089cec3f848a082d76c98aa2809e73836078daec888c1f0865e9363f7e6e1e25584695a8d8329c052850d04382a6f8c64280610002c0858447c001805a3502224854250145084e0a112f17b5d6b38fc2e32dd64881200f9e50b98fc048fea13a6301ec76a800714f418bdecb44ad040384e002cdee11a1fe619453030eef608dc8807d76a1e559e1d9cb23c9e447b8ba1d0a8c9246e40b88301aff21210d7b2f11a0799c09b2c21c3e7091c0c90ae08e2ae51423b45c2b1d3823a601505ff1605adbca195058924a09025500e3584c1406e282d8c089cec3f848a082d76c98aa2809e73836078daec888c1f0865e852850d0439363f7e6e1e25584695a8d80a981de7f15ed18183e002c0858447ce8d98f0d00001805a350921509450828bc83eaf2400e85e44b5342680955f008f003f82d242a8384d11ecb44afa8af833dc38303c482ff92845f5931c59bab800cf3449a0875a705ed1d15b87d0c9f75ace3fd0b585b8021,
  0x16bb222307c2197a14a143410e4d8fdf16111f00060168d4088082484e2d2c23802845342e0f9121198b850e8a974b3c00184003010060f8000d218968350225e04e38028510be452c2e0f870f19ad2805418171812f003a218ac20a048452436d480f9398046311e10934881c51081ad889da772ba398c01d87037a8420a2621040fe8044779012419ba7026c4bada052702b88dda881178780a3c042f4e04053684434504413a043d1a8a9b1e8a999c2470362ac49d3c7111f91212902e1986f9c58e390184003010541620a9be3190a4928240954078ee02b0815113b4e8cdf990247d707a57a18875aec191e61a20c7d8745807676101f50c0651d300b3558f26a11416302279b87895611a56a3613050038d61b8a0b3b0fe122820b5db262a8a0279ce0d81e36bb222307c2197a14a143410e4d8fdf060f800b0216111f00060168d4088082484e2d2c2380287318051114730fcbe321c5e05fc1aff20171c3d52979c044e4a440fc48838183e012450c329c0fc048986e864798fea107289868833a6303101c1f61d1ec7695cae9601d9e8007152a06b58407d4f418bc2418743030edecb02366201f6a04d00610002c0852850d04382a6f8c642924a09025500e3586e282d8c089e6e1e25584695a8d97c02fd0403048e031e6af12b2e429b57b9a111e5614b08de921a1dee341244c14058447c001805a35022070202504e2d216cb38445140a17815512016d2f81631a81291e812706113d6938ec587077186d70301000b0214a143410e0a9be3190a492824095416111f000601681c13af687812450d344c00cd1700cb2380c72680c53800a34100a15f009f7a7c67bdb8669b38645003f808808249786a114141249a03176e199f820e753a8785c4185740ec66191a25ee11a1c4c140004d74d402092470ce3aa205084e7029225113fe429b57bbb2f11a111e56c21c5614b08de017061c58447c001805a07012062f644f410b1110399306b30a1139380cdf8b061742084d6188491708474d0ee5091310d1133261ba1ca26c4070572ba558f24a81ad6a0e23090ed30301000b020a9be3190a492824095464b2a78aa4038d6130501b8a0b6302279b87895611a56a369902473b0fe122820b5db262a8a0279ce0d81e36bb222307c2197a14a143410e16111f4d8fdfd707a57a18875aec00060168d4088082485444ed345f0a89410a8f268aa36011351791372380b7f98651,
  0x142924a090255058447c1e3b80a179c6e282e64091f5c1e95e8621d6bb0001805a088081b04e070b4049163ae92a06b4761c0240434828992c1ad5066e858447c001805a07012060984587bc2d115b1b8a0b3b115d24915700060168d4088080d115f6e872898143f97101c0283f9c182cf55cae816128cbe058d2a06a43204ae7212671605bc1a4275c604c4ce27b652088e3a090c543c6d1c3f85363f7c0c0402a6f8c642a6e1e25584695a8db5c1e95e8621d6bb036078daec888c1f0865e852850d04381e3b80a179cda241402c0858447c001805a1b0343b115d1c0828995cae9066e92a06b4143f9424424c1a42741824563a065c5404cc32275cbe2745c02777201c9dc61b5c28456664091c0c04052850d043992ca9e2a935c1e95e8621d6bb01e3b80a179cae23ecf0240402c0866d59a405642a6f8c642858447c001805a088081b0342d01c456d0552902e0e8c01018403a08fd3c090136890500b0216111f00060020345181c0a115941543a3004a40b812e3866b4928056dc604c4da2414f02404e823f44e45445cef09a454d563c9a845045444ed8c089c6e282cec3f848a082d363f7c0610002c082a6f8c642976c98aa2809e73a6e1e25584695a8d836078daec888c1f0865e852850d043858447c0e3584c140001805a3502202092455d0615d08c9000d43a85cef20a61839d68904798ac6674c00ad4100913800836a88b55d08b37e88b15b08afcb00c5f980b57b2c09598808563998529b4000d4020923a894269153330d040286ce190c8e22f7480ddcfb5829860e75a20e65aa0e5dfa0e4d6c0e4662b199d30ee32c453d8e6614a6d1563c9a845058c089e6e1e25584695a8d84c1400e3586e282cec3f848a082d76c98aa2809e73836078daec888c1f0865e852850d043858447d363f7c001805a3502202092138b485915104ae1e450dc61b5c2845378445166af12b2e429b57b9a111e5614b08de921a1dee341245444ed563c9a845058c089e6e1e25584695a8d84c1400e3586e282cec3f848a082d76c98aa2809e73836078daec888c1f0865e852850d043858447d363f7c001805a3502202092138b485b2c453c2e0fab8198b856f2864b01037311472f914b121149060f8018400301000b024928240954191e61a20c7d8745807676101f50c0651d300b3558f26a11416302279b87895611a56a3613050038d61b8a0b3b0fe122820b5db262a8a0279ce0d81e3,
  0x174f40456e0c437d0c9fde1b8480f8bd0b58578e67768f07659179590bed9a10af779fc210e1f078ee0285e70006c06a128b202d2917b341e18018dda017d5e00a5d6917e5d8f168c00a681a84a4e6591794d08e03d4e003c57c03b49a02150402053001f5f031a671a1875563c9a81a74003aa86fe0b46d82498ed1774d0e003c57c03b5f031a666390f162c42745438af9a330c8e035c9a02150402053001f5e9f19e71a1875563c9a819f40e3584c1405cef01e3b80a179c00350ea089786d86c0939806986975d175341e18018dda01d56401c5d6917b5dcd182c2e0015e399d9645c53e45bdb845ae2c11661210d676d1c8c1aff27091c0f200635c044d71638e68a0285e45a4f0d00e8d987a8c87e4485529792c8f8aee58a440fcdac1048838061000c04052850d04382a6f8c642924a090255192ca9e2a918c089e6e1e25584695a8d8183e012458c5cef06e282c02c0858447dde7f01e3b80a179c92455cbc083d76c98aa2809e73838077daec888c1f0865e804215c001804e0705a879800511736e16e01cd5e00d4b2015618009dda008d64511dcf186dd9716d5dbd17a5d8d1685de7f26842bc1e3b80a179c001b0788e920659171459cb2015564511dbd17a6f045b66842bc1e3b80a179db845ac001b07894a3a4f916f01c64e459ddcd182cb200942e001d8f449d5e399dde7f01e3b8004d07894a3aab93ebc116dea2be0cc73c0cb70e0c0f120bfdf40bee4f7178e4c7166f42d626842bc1e3b80a179c001b0786e116b459cb23c9ca8428d64881200f9e50b98fc048fea13a6301ec76a800714f418bdecb44ad040384e002cdee11a1fe619453030eef608dc8807d76a1e559e1d9e447b8ba1d1563ca46e40b8831a8388fb2f121210d5a0798200fe41aff2c21c3e7091c0c90ae1d0e21c044dc8e2ae601505ff1605adbca19c604b40e3584c1405cef06e282c52850d043924a09025518c089e6e1e25584695a8d81e3b80a179c92455cbc083d76c98aa2809e73838077daec888c1f0865e804215c183e002c0858447ce8d98f0d00001801c16828bc83eaf2400e85e45a45fbbc0e6775a4065fc9165000789493e50a4ed2916717b42e32ddd6b38fdde7f000508789493e93b4afc9165402df61d0901b95601d9d4c05258407d430423484387c78424c423264984585082454da244d142444f0243d382434e8242c440285e05544805b4be058c3204ac6a04a47a049da4e3b161c1dc61b5c0c04002c0852850d04382a6f8c6,
  0x13800a34100a1fe8639b386453e8f225061f238abd980c36dda035d038d613050173bc000d43a822090f411078120660e9084f986466c2e19918d0fab81200e0184003010000d21389025968110285311993f94326a0be2745bc1b9400b781424096112bc1e012465c7077f441750a0f8000d263168061195028326a05e05546a05447a053c4805b4be2745bc1b95a4e3b161c1c284644aee580c040003484e05090258245a01a1111939b108ff07eaa952fc0da23e64cf891410c53810b4e810acf0106d4446367091bedb0c1946463c0c04150588aee58003484e05090258245a01a110284644b8d423fc1faaa14918b54a5e2902e0184054162000d2050900901aaf02851918f38e45e05acbebf9fd11be528d5800b784e259681114419918d9b114ee908ff07eaa8da0f44f00fcd380fc4e80fbd8ab115297a381b3c0043f4142402406abc1483e462ce1f2a038d24839d96a465b98ac66b0788493e8f225061dd300ad98807da8105f4e8e991e10632201f54881c51081ad678767889da772ba2e874398c01d8705e11852e11237948209161299a31118727b742a87775d820d16111f038d613050173bc1b8a0b010857000600709c0880846245632582c14d94a01430d77000269f8c4461d05f4c0c3b2201f54881c51081ad678767889da772ba2e874398c01d8702e1123794820916038d613050173bc1b8a0b0108570006007022021780b118545cc329c0be4604662ffc7e4484aee58a440fcdac1048838986e87289b101c15cae92a06b42445fc183e012458c92455e64091d8c089cbc083c38077f5c1e966e1e2576c99aec89e862192ca95846924a08aa2802a6f88c1f052851d6bb1e2a915a8d9025509e738c6428865e8d0438061000c04002c0858447c5cef06e282c04215c001804e0705a460cb8d190f2f4e04514204214503f59db47236c2c074388c80189692fe71a903a3663c34054a5e000d2188967606c0a0140fabc0e9462f918100fdd1d31460245ed203e2cb245f55e399d9645e42042763a0f1663b45dd642fb6520eae5d745d484387d3a2ea478424d6c2e6da22e85aa2e5c0e3584c1405cef1de7f26842bc1e3b80a179c00350ea088085e1b61b02445fc31b3a24e4d91545b9af83010b8009314baf6e0611cf0e0773407708109d659179590bed9a10af779fc078ee0285e70006c06a128b0b245f7a8c4834baf8325cf0321941c60f91dc5cd0b800c38bb97734073,
  0x1282c04215e7e281f2c994e083c0846245a460c001804e070220b11b5aa83a2f6552fc000348144b89025824700441992c46ccee506015f1781551a81511e814fc807272f89d16938e002de2f0967623aaf01246c51ad19b061fb7236841f45041d4e04193a0417000d2138bc0509025824069c06c11af277c283e04446ac001381424024069c043850e543b6f23483a5191ad1acd2c2df428463d0e99b0aee5950588003484e050900901a7010e143950edbc83a5184446ac727f68cd10a02e178aad1a8aa70c8aa92f8aa31e8aa519b061fb728204210fa5e903fc0609150184003010000d2350bc050966a09a6181a7606c8e90846a486f6585c539d4bed747c03702a600014206a1208164469c5c3a17a8809b8c3833f9a0335c48317cf03157d031376803b5b8039928c5f3915c5bf747c5bdab800a70cc92a0f8b659179779fcd0b582c8f8702a6057b46001205081a8482024a4e4694f0b618a85590f953e8f21b04211510a32516c6c2c021040f4803e7a81345f0a89238ab1410a8f692fe7026c268aa3380a976000a453ba4e03dd1faaa3683d13c3403a3660c810162ac4942e654a5e4b23e2902e19918d1211a117a861a8fa1e894531199049197078ee02a980691932bb96061195490eb5de91a970789ad822701840030105416200b02038d613050173bc1b8a0b010857261ba1c8a23f0123f994191e61a0b60a9be319829f8a07cb2653820f02118916918316111f1081ad772ba1d87020916000601381c0882c6311a38824e32bc20af0b2436e1832c69c467ca837ce2c116676d1c6d92ca9e2b229d7621f81e96f4091db645de6390f07982ea5aa0d665f9467586466d5ed1a1210d7a0111d200f9c6c1085c09b07eaaa74f1c36501aed52fc27091bedb0c19460b83e8f8da23e51423dcf023d53823cce823c60150606a2046e4cf8806101505884c140fc048fe6526af12b2cd122071622768e6300de5216c2e6c4206b5dcae8761c0824585cef1742e7c8807d59e1d9cba1d0b84486e282c0e35804215dde7f01e3b80aa6012465c64798682d8986e8722880c04002c0858447c001801c0882c25968112bc1e0484684d0786006376807559004f75a45ed773460b76f45db0029a24a52fca3aa7119f44ad300234e0028d040287fa18e6ce19166030da4fa3c88e40bcfb982894187da20d6c4c1418e6614a6d1fa2e740e3596c2e6c5cef000350ea088243d0fb54ea5f9467512b4c008d,
  0x1c8910077c2246dc4206b5dcae8761c082458aee58986e8722884a668c446e45a460c02c0858447c001804e071b611028470c2e0fab819ad26f28671812d003a2240620a05ea2044b9d3c70d0e8a9180541798000a1a91bd3c041b6c3060a9be4503f531982743809f8a051918f7cb261e035d53820f4ea0a02066997e46277e88a3cb00c1988081d11344c2e26302279b87895611a568eb55a0c3f0c91bbc58e390301063998529b43f0123f994191e61a0b69abc4acb345b03b95d03bd6a83bf6883c198ed1775f00ed3800f12680f32380f57c0c69b3e8f2250def4881c5889da398c037948173bc1081ad772ba1d87020916bd8237da8795911ee91aea13050038d60108571b8a0b2bb9636b041220e261ba1c8a214a14341701299a3111b9169183ad07c673224401df0891b70184000b0216111f000601381c6d8440a1807311bf2a55c09b07efd2501aed38236ce82366a2ce95058800348d44b8f46a044af028bc9046186643b50e91a91bd4d130b890403058c089f6e19a66e1e24bc083d5846976c995a3ad4aa281681be49e609460b90c6f83e8f8969c24c04040610002c08986e87228852850d05c2b41f19cc8910077c58447cfa3c89437bd22071622768e6300de5205cef04206b5dcae8761c08245af608df6a1e56447ba46ba84c1400e35804215c6e282d7c03b4e003c49a03cc8e03d4001801c0e02c7c04287f443246ec0a1210bb0c90bd1e90c71790c32f90bf1a90c1060f87602f55a02d72402ab1882954b828050261048a11b18d8f88ecd7f683ea403d6790d5f41b4e018400301000b0200026138c446e453f1882954d94a01403d6d519a0b11b5218d3d231de6b81dd16111f169183000601381c0891b79b0da110c7ec7a74f1c358a1b751423b4e8239e01505fdbca19cc02848f887a8c92c46cd3811446a063432054cbebfa76d1c6fda1c6528d5946463c183e01246c4f0106cae1055b046bd0846a62c427492469564469d92ca9e2b229d7621f81e94540dfe520eac780d741e2126f4091d3a2ea5b61a6e5f9189d3e328daa22d5f0103ce620216164d08e035da2118e0028d0402857c027de9f19ee5d719f658b191ece1914fa3c89437e53030ed8c468d742e7d6c2e6c8807d52207144206b59e1d9e22769dcae82a6fa6af10ba1d064798e6300fc048761c0986e8c660ab2cd0b8448682d8de520fe65082458722880c0415058802c0858447c0e3584c1405cef06e,
  0x10023890276bf10847550a321040f0803f9700b874e03dd1faaa078ee7438848103d62ac4942e654a5e02a982902e06918f19ad271a906011d136b040491c978ac8a75d887e07a5bd02476d91c52bb960611c7bd82371081adda8795772ba14a14911ee9abc4191e63f0121d870261ba3417091aeaacb341a0b63f994209161c8a21299aad07c673224401df0891b716918301840030105416200b023111b916111f000601381c474e0a618a9f5d08abe11346883997e83935b03915f00bf98ac66bdb86696a8b972f020f700b0268aa9238ab75db261faaa2a8a054bf0279825182e4100ef4c00eb431be0fa3e7c051bb25a709301018780a1a8fa1e8945311cfc58e3963998529b43e8f2250def4881c5889da398c037948173bc1081ad772ba1d87020916bd8237da8795911ee91aea13050038d60108571b8a0b78ac8a75d887e07a5bd02476d91c51220e17a880491c92bb960611c73f0123f994261ba1c8a20301014a1434170ad07c673224401df0891b7191e61a0b61299a3111b91691830184000b0216111f000601381c6011d133656e3c15dcd182d964494b229042e39153e428d5e2945862a341aff08754d1de7f00a98152fc130b8a2c116484103c200fe41e2135042a448e2acc9a2a94e02a664c8c98c089dc02c20002a6e1e247ec786a0635584698a1b75d0e0276d1c6fda1c655a3ad5460b96830fc3eae0326a00e3584c1405cef06e282c04215c8807d59e1d9cba1d0b844992ca9e2b229d7621f81e96f4091db64714488385ea20124724aee5818471cfc048fe650986e8722880c04052850d05c2b41f19cc8910077c2246dc64798682d84a668c446e45a460c0610002c0858447c001804e071805311cf33076c3da400160c1d3084c194035a2b3ee0811cd34bf6c3da400d68582b0c19fb8c213076e2883ec02848038326a07a044c5e040c6a03fcbe2745bc1b96a21b0e4c1acc00b784e0512e24044af01247246d76b01370a0f8000d20e0620611c702848038326a07a044c5e040c6a03fcbe2745bc1b96a21b0e4c1acc28470caee580c04002c08986e872288fc048fe65064798682d84a668c446e45a460c58447c001804e071b61111c5428c84103c200fe5200f9dc02e1d380f747eaa81e3b9d0e218ab1250b99529780aa60a40b81a463c66b49c6a418046fc5ea20dac100610150588fc048fe65064798682d852850d05c2b41f19c,
  0x10184000b0216111f00060138440a0620e11edfa0ea3d642446cc30c783a9b108103d381014e8100d5058802c0858447c4c140f0106db0c185cec000180ec1109073014af2f20e12ef7884350961990ed1512c9d91ebd10e7dea07456e2be0d37120d2df40d1cb201dd6e01ce507184ddcf1845de7f342d615e399c0050af0809b8938e753a262c47a51a55911a7001420692024a120811e7326c7a25000b784451084879806f11e5476dd0e21a4bf9c6a4180326c7a8c98ab114cae12c8f80c04064798684774aee58986e872477c02c0858447c001804e11062731440e0848783e478f888e11db692fe71a9062ac46000a2902e1a8fa1e89419918d5311990ca70492820a9be409543190a0301017a88191e61a11dd2bb961220e261ba1c91df0184000b0216111f00060138440a0620e05a478509d1e01a98e824324820b470e5f4602155002070d81e3158b25c81d17081cf772ba078eed707a59b87895db266bb221d87002b087a1885611a2a8a02307c20a26150f1b75aec56a36279ce2197a2719a0b0a24d8fdf3111b916111f0711d300060138621c91dfea2be1733c239f490a023dd70e0c9f120c8cb2012564010e475172dd3d17242e001b82f9e6842bca807c596282652088c92082d1c3f8742d61de7f036078d9e1d9c1e3ba6e1e2576c99aec88ba1d00ac2158468aa2808c1f0b8830543c6d5a8d89e738865e89c6682c2d9363f7cc446e458447c1c474c001804e188684775f40c31e092aa022960ea6c6c2c04203f90a9be150f1b3190a2719a0b194790124bae6bf11d94e04055416200b023111b916111f0711d34503f53683f73a3663c34054a5e00060138440e128af1cc0fa3805276476ce5f22820b159c45001ef7081b70dbcc5c81a146019d5db26678767889da772ba2a8a02e874398c01d870279822e11237948209161299a1690a431be1b00c925ac0cb0671822963abbc2f0e730788472d11d70c31e3d3f4092aa0108510ea6c4211d54d8fdf5416200b023111b916111f0711d34503f53683f73a3663c34054a5e4e040500060138440e128af1cc0fa3805276bf11d93d257206859e1d9e22769dcae8ba1d0e6300761c0b8448de520824584a6685a4290c6f896b0208a586efa0bc31d4c446e458447c1c474c4c140042144001804e110384a1cc0f87e10922220b4475d0a321040f4803e706bfc0803f907884d,
  0x134956c348c9a47fda22e65742e554a6d06ef805c48148ecb8e0e50887d022480e92112cf4fd1b611757810e408a583a2f6508ff274f1c36501aed52fc20150606a2046e4cf8a76d1c6e7091bedb0c194446340c0400e3584c1418e6600459824464c003484e110144b890b094206ba00809225968939d81992090316163cff6e19cc00fe0422f384908b41bbe019cf2c032ceaef000350922f05c481464d3abbcb380a92d1201011660014206ba00824e108bc6326448af60892033c2d860edea047f661b4e89a47fc8e021d7c01fe6247ece0315c6e43640e3584c14004598005081ae824e108bc6326448af6088b44804f26a068d2506757b840e57a7c0d500286632f63a89a47fcf13d11342516c00286fe0422f18c488b4e1087590aa08591fd3c8943e05a8188d4a6d0e0315c6e43644c1400e35800068d4108bcbd8222d26247ec6453e8f2e68cc32516c038d613050000d42f18c088b43aaa085b449091f93dec5c39cc04598005081a108bc630222211f7ae8761c12af30823016243f848a47cc986e872477d363f7c58447c1c474c001804e110281891f5479c6c3804a807c53e07047806a59e1d9e22769dcae8ba1d0e6300761c252088cb8448de5208245a6e1e244a669584685a5515a3ad623ba09681be71638e4bea41acb49460b83e47c45447bc1ee480c040c446e41c474c5ea2064798684774dac1048838986e872477c0610002c0858447c3847b4001804e110281888a47ccb874203f91fb3e7438871a906000a4e04051a8fa0c81011ea3262ac4532b84b23e03010541622bb96000d2138441889073014bc944088200f91f13d55529798ab10a40b866e0238cf83a0c8e21275d2126e3037745ea200610002c083c928d00a5458447c043700e192cce27b572279521b36c400180ec1102818890050222285447bc6dd9d91eb932328000a1a818df6871964b2a78ac8a75d887e07a5bd02438b11e9c3833f9a033559005b928c5f375ac5f1ab800860d11a70e8d0811e76f11e59482239b87895611a2fa904503f5568eb56b2d2743805a118d5182e0f91e30ca700a9be319829f8a07cb2653820b1b0e1f0116602a602a01f14f81c11e01a9658a0907b92470fe10dbcc5c81a1678767889da772ba2e874398c03f0121d8702e112379483f994209161299a1691e14d8fdf030103111b90711d317a88191e61a11dd2bb9636b041220e261ba1c91df,
  0x119a4fa3c89437bc224625aa2e5c5cef14a6d0bc083ef608dd2207144206b46e282cec3f848a082d76c98aa2809e6085a4290c6f896e3928056c6c387ca83a878041f6a1e55bc1b9622769dcaea4c1ace447b864798e6300761c0986ea46ba8682d8de52082458722884a486436dc1363f7c58447c0e3584c1418e660045981e212c4e485c0018012486d15f2f020f0e01df3b115d5db266bb2224815b2a8a02307c6938e279ce2197a0a90212719a0116607884b139217310a1116111f000600484a48644a39c849914a14150f1b3410e2719a0b1215298b3d3389ed470fe10db700a0f81112130711d33111b94d8fdf00b0216111f0006013921737b7b413be1011d6447ba6af10761c0986ea46baab2cd0824587228921336b521b36c522336d4a62cf51c3f841c474d363f7c36dc0283e044484c02c0858447c001804e0b1215e58986eabc4834722884a6685a484428482c02c08c446e458447c001804e111213028be058c3204af161c1dc61b5d24a085285102550d04380c04002c087a274ce8105c6a27553810645e276514107448276cda107e08483c000984e1101216921102848055c5e05546a05447a053da4e382a40842c483432275cbe2744f0106cae10540c04002c08000984e1101282120f472464798fc048986e8682d8fe650722880c04002c08000984e11012af02c48360a6883b561838f986c68bf286556a88b55d08b37e88b15b08af7b840e5f980b5558f2858fad6a268238087529b49891fb1b8f7d6311f71712056d845d022969db47236c2c00c31e0e38ca4844b3d3f4c80189692fe0e8b87600c9b3683d142040f4e03f1123e20c81019d3c711942e654a5e62ac48e06cf4b23e2902e19920964b2a78ac8a75d887e07a5bd02438b061177340791e894809b8091193531199590ccb490eb5c48317cf03157d031376803b5b80390a9bede91a915c5bf747c5bd31982970789ab8009f8a0ad8223a70cc97cb268491e72c8f8753820b6399813050038d61b0e1f578e6701166779fc02a601501dba782332a01f14f81c11e01a9658a0907b92470fe10dbcc6bb22da8795678767889da772ba2bb962307c911ee9abc42e874191e6398c03f0121d870261ba2197091aeaacb342e1121a0b6379483f994209161c8a21299a1690e402141891f54d8fdf01840030105416200b023111b916111f0711d300060138440a120b0d94fb182a60318dd860edcfa3ca61b4e8945b1aa,
  0x1484c48d4f0499059041be8497478467485c463842d81d87020a26419ba74a9a3916a158b22307c2197a14a143410e00b02180ce000ec168264411c2e8202607e3880a0d0b27120b1d0c81532ba6cc4a2c04601e5822966787652f1f47284b52fbc00c31e1a8fa1e8949306af62ac4532b82902e17a88060f801840030101986a754b9c000ec34862258addf78ae589046470ba24020260a62bb4e2108381f82881823dc72ccbd07a14d8da1a28c4f3000ec7e0addf78ae589046470aed486d3c3f848a082c36078d76c99aec88aa2808c1f0528506c45749e738865e8d04389c668c4be81c48942c48844e485c58447d363f7c00180cee291c300d107796034fd9c34f5f61556b414fc900aac620a553652804543af5a0fa900f5858447c1c489400180c4bebd44a873910b9c570d3390109f1e90c7c405157602f52582c11882954b8280502614d94a01b18d8f430d77403d6790d5f41b4ed519a1692230184003010060f80e8c0104921b3c09013a08fd36890513921700b0216111f0b122100060071225457cbc083c38077d76c99aec88aa2808c1f09e738865e8045981e212c4e485c001801c16922333142240fd24a082a6f88c1f0528503e97902550c6428865e8d043a40aaa3c11cc9c48744206b60627bd3cd42fa3704ec3f848a4799007ac36f319e1d9ddcae8ba1d0e6300761c0986e8b8448de5208245872289363f7c3a300412486cf02404e823f4da24144e485c02c0858447c001802c4884475298b2b8f0deb3389ed0e8c0104921b3c09013a08fd36890513921700b020dbcc772ba1d87020916261ba1c8a216111f000600b08a478ca3859342380d7688463800a34100a15f009f7a7c67b975c67db386453e8f2250df94c0c3b6302279b87895611a568eb55a06f9c5816f9491672cb98590f951b01594a3560a9be319829f8a07cb2653820f5d0b9f5b0b9b0211890e0cc52307c219704021418ad27181311510a32106e48011f06bfe5306dd9f06bb4b3f05182e0fa5e9db1ebf3f4902aa8f0473173bc2201f54881c51081ad8189ef1b8a0b4f350be8dc10184002a60038d6130500116607884b0e8c0104921b3c09013a08fd36890513921700b023f0123f994191e61a0b6889da398c0379480dbcc772ba1d87020916261ba1c8a216111f6401eb6787672e8742e112000600b09c07121d0ec4fb582a6191a45860e75a20e65fa0e4d6c0e45ee341249a031662b19af6e,
  0x138394038d601166078ee02b08000200e0422f0b4859225592450d7d3a82b681895fa0d95a22e65742e54fa3c94a6d16c348daa349660330246ef80e0e50887d00849047848f5043c4cf4121e8c5b8e6300dea106c1085e404a1210d4943a95b0b012eb6a7091c0c9a2aa48e2adc5c2b15a4054ea2045f1638e61e028bea41ace2084103e380fe5c09b0ae48dcf048d4da110e74f1c4514ee9381014e8100e6af118ab12b2e40a40ba9b57b978d50664635a111e47d030d4482c776a08be6e0874ae9b31180586a3e87a2505ea214c4664124844342987e38818471c2212742411ce0634c521b4f11e119d217118e10b61403974761c016410482899066e8aa2809e739584695a8d9e8621d6bb02a6f8c642924a0902550061000c0415058802c09c2073d72074590074c36078c52850d043921312352231256fa125c6479868831f61d13c1265d2a68e45a8562c88c1f0865e80e3584c1418e660045981e3b80ac2060338003b05a09910470ba08098490e0a6a83977e836568835b5d03575b035398ac66b980c637da06253e8f2618c8b529b41b923f1305063998410f13038d601166078ee02b0800020108382d2428595624922021241330d30ee2ce193f2c19c400fe0382d24285b440206e48fccc34c3b8b3864fcb06713a923b2f12394f91672cb98590f9513050410f13038d601166078ee02b0800020108382a0b490a1655a52249221e123d4d0e0020d7c01fe62188d303c2cfa3c986322c0e3584c140045981e3b80ac2000080420e0b490a1655892d124e020ea48ee0a7e8365688b995d0b95618d1b5b0d236a8d25529b4980cc091bbe038394221f41305063998410f13038d601166078ee02b0800020108382a0b490a1655922480bc48e40a2f88d10c88dd03010000d21104e0a1cc8028a510ae48defe6000a4a2c00c88e382041b03010000d2258441382873200a29440f8f048d4ee73c041b4203f93683f73a04039006af6c2c0450f2d7438862ac4692fe71a904b3c02902e6000a19918d0c8aff120b15030105416217a88018401e8941a8fa531199000d2188965a22424020260a61103a1382846016b31362c9d182c7c003b0d22b77de2b9624470a62bb4342992110d09dd0a2064203f97438c0a9be3190a191e61a20c7d8740904730611c708849d818d31486d3c500e5d2a8a0279ce0d81e36401d35c81d17081cf7a18875aec488c495,
  0x1089257b31182cc5402ced362ce4164105066e8143d2c243b2488052664066cbc057dbc1b97201c9da4e398c465438471c6e281c283e1082454da244d142444f0243d382434e8242cae242404213c2a6f8c642924a090255192ca9e2a900c04002c09c2073d72074590074c36078c52850d0438e45a8562c88c1f0865e86479868831f61d020494c60338003b05a09910470ba0612554d17c02fc8e02dce002cd0402076e199fe619471a18749a454d563c9a84507820e753030ec6c45fc88052664066cbc057d3a2fcc5cef0342775bc1b97201c9da4e38423d2d8c465438471c6e281c283e1082454da244d142444f0243d382434e8242cae242444494498490c4c1400e358045981e3b93c1264f60a2c0ac2135f376c52850d04382a6f8c642924a090255192ca9e2a900c04002c09d2a68e45a8562c88c1f0865e86479868831f61d060338003b05a09910470ba0812537d008a5824aa830c79b0b002247c5529798ab11a4bf8a40b9800286646346a3e87a25048838dac105ea214c466412484434493c3a492d24a09025500c040329c052850d04382a6f8c64280610002c08003b05a0991047090080141112511c0e70b10e71605bd8c3a9652459d564904b2e61643e546c056528b008e316e08a589a3ffc6efa0bc7d05c3224f4fd022cf920047c24aa830c78841b81affa50b99d0e227cb69529798ab114cae12c8f8a40b8124934fc048fe410c66b48a6491dc604c4ae23ec2a6f8c642924a090255192ca9e2a90061000c04002c09c2073d72074590074c36078c52850d0438e45a8562c88c1f0865e80e3584c140045981e3b80ac203a492c60338003b05a09910470900801411034493d09d24815b8e90391e11976938e078ee02b080006225968762de24020050440d2bc04924d427492056e3a40e478465da4e38283004da2414f02404e823f4ae23ec4e492452850d04382a6f8c642924a090255192ca9e2a900c04002c081e3b80ac20001682624020050440e924be22380fe5c6a41c02e34a40b9800286646346a3e87a250488385ea20aee594c466412484524a09025500c040329c052850d04382a6f8c64280610002c08001682624020050440e84e4924a6500b29000ec348addf78ae58911c29834491d101a81347e83655f007f980c637988623410f133e8f263998529b45b0d23688b99221f46a8d251bbe023b2e13050,
  0x12b10251ca260b1163410e00082d685a3084582205449acb8d421c21f8ae919918d6000a2bb960492110c8aff1aa24120b15178b0d0d124703010191e6261ba061255492820a9be00b026bae41e8c2c72cc4d8d9f070dbb228daf500da5708d935c8d95640d990da943190a409541a20c7d874180ce000a6485cba169061882649a53c500da7000ec471f82b77de2b962411921b499c473109261818d310ea6c4f085542084d5092633684439d3c7119abc4acb90a6d5ee6844791da822f5416200b02484c48d488c495be849774a9a3916a158b22307c2197a485c4634784673a04034e0405453ba180ce0005a09910150a68f1219af03e9d90e982038351364994e4dc38345af8325939c60391dc5d1ab8006585a39a1047634025a70e8dd290054f90031e125fe804471b042121040f7026c1f9261090473818d314f125d02a605416200b02484c48d488c495be849774a9a485c4634784673a04034e0405453ba3684439d3c7119abc4acb90a6d5ee6844791da822f3916a158b22307c2197a180ce0005a09910150a68f1219af03e9d90e982038351365092630492eb98fea12fcfd3a6301ec5bad4121d22390408a5830c780016826118540fa7682038350e21087e4987241b042121040f000549da085087842125f9b07e496d080f9e50b98fc048fea13a6301ec5bad412153e496612137c1a11bd5058802c08e8100d38101514eebd030d66e0875584695a8d8da110e74f1c466af12b2e429b57b9a111e476a08bc603380016826118548f2bc0fa7643a6080e0d44d9424f125d3c9a818dc94187e6010dbf680d753a3fd5fa2e446e40049a3ffc8e3fec423904f4fd008a5830c780e3584c1405cec000152768203835078482fc1f925b459cb23c9d64880a8428c0a98000151421e2524f9259459cb23c9d64880a8428d2012168c5ba12137ce6303d030d4dea126e0875e4048ae9b312eb69182bfea2045e1e028bea400a981ace201a11bc1e215638cf8ce34c43a0c804370e212743c9280e192d584695a8da3037740c04121312352231256fa125dd2a6820494d21b4f1403974aa2809e739e8621d6bb1217118d1e119e10b60761c0828985ea207a2506a3e94c466524a09025506479868831f61d048055ca40b866d582a6f8c64280610012484434491c164104e45a8562c88c1f0865e836078c52850d043990074d720745c2073c02c0818495460338003b05a09910470ba1c928,
  0x10005a15038108bc48af69903c4a04a853e8f2a81344e8ceb250e376dbd25e2b05f0a89410a8f268aa32b032700f2f4095478aa41bbe038394173b023b2e13050010dc03af8002063b05a349361110280f90e143b50e94394be190540e0422f03a49fce41081f408b3e092aa022960c31e3d3f40108510e8b874211d562ac454a5e4e03dd0001443f6bc0faf2bf2388209049f4e41081f408b3e092aa022960c31e3d3f40108510e8b874211d54e040574388942e654a5e6c2c062ac4692fe71a9036b042902e600c3f19918d2bb96049211178b11120b190d0b23060b35f7acc7092790ca705416203010018403f012191e6261ba492820a9be14a1400b0216126d6401eb1a20c6787657d8740da947284af228db7070dc1500dab3190a409541ca26c4070572d88f046b2c02893410e72027f3fa84e98c07b16eb504814db0c4429a2307c2197a9c8497180ce0004629afac705a2e927b3904207d022cf824aa808a5830c78f4fd00421443a2e1d084755381015d0e2250b9952979b0b018ab11a4bf9c6a40dac10a40b98030fc664634aee581248445e2c3c482c5c342c84182ccc36a5124a09025500c04150588329c052850d04382a6f8c64280610002c08002985a098142412e709279329183644603380089121349dc2172b75267ad8c357a1885611a75aec56a362719a0b148310c03e98c05822a7b16e5c8d97070dbd228db1640d9bc505a8684a9b5047b180ce0004689121b49d45554d94a012e0d3f2402ab163ec7202972e8c035f89f30f3aa3db86683ea403d6d519a1692712c0f6730adc32ad6320f65eb05390b1164d5c507bb84ff218d3dc40702315e572d8070dbf228db37484938f0467000468911e49cecc5c821970821746332ad8c355387755611a2a8a056a36279cecc04c1c504a4d8da3500da9228db3070dbf640d9d180ce000468911e16927149a4528505849b46883072898d0438b03d9c9c669c8378fac14e42c458c4300df61d08634f7101c1608a88c5795cb601c36ec8a36be1a129dd2123e3c118c00118a6485d26f7d05449ac30810247800895022928ac40942c458d0438c6428728980020b5a168c216805849b7241b0f1121038f4100b1f28659d3065706a684e8ceb268c59529b43e8f207901d1bbe8173b0250e375e2b0409546dbd278aa41305063998380f3d23b2e091e0038d60121c022543190a08a4a,
  0x1180ce00044348281394473200a2820742b4059ca3b1ec4a56362719ade91a310c030b11697318582e8c40709b82176781e757072d2b76cc770fd56401bb5c81b922b8a5001d74db0c462e4a0164440b23316a1196eb52e08f27a4bada0523ea881179301018780a2fa906b3882902e19b8001840030100d8dcd180ce00044348281394473200a28207419c059ca3b1ec1892933f557206e48ae2936c3118b912a1cb680591102c8cc5aad4342446b612eb6a3c9eaa2045c1447c61e0284804bcbea41ace2052ab00c04002200045981e3b80ac20fe65036fbafa2dc5d24a348c1f0865c0ba1d0b8448e6300de520761c0824584a6685a43900928c4ea87a2506a3e85ea194cae0603380008022bc8443b03c2403e139d005929148dc4823bc00348448028a73028138ae4a3ce5f22b8a462e44d81ed5001a770819f4429a612a64aa663916a5c8e5b15a020dbeebe8b71180ce000203b15c7b160671d24a34321fb3e0f24a002063b1004d84448e0d408928b3c9a81a349418fdee10396ce0296164a1db6117692112cf4fd03a49fc6ef808ecb8e0e50e810f5141105380f744c1405cec0043700ebe000818ec168d24d84440a03e9d36fc43a4be9dbc6415038108302f1289d10e7dea07456e2680cd6be0d0d64016f0e0c0f120bfdf40bed6e00864a317ce4e7180dd6b17c64c7166dd8f1666ae0021834469c3a353e4a16523b0d964494b23c9c1a0d7d5ed1b42d61de7f00a9836818862c0f0ca80e346c0e6fa00edc1e21271a01fd3a8288754d1fa0eed0403bd3002766391a5df011a565a9194f8219979a18fd564a0e61b4e98e6614a6d16c348d742e55a22e65aa34946ef805cec08ecb84c140e0e50043700ebe00015038108302f122bda6485928732de9c32ad64881de7f342d615ed18001514224a3a1e34a4f928532de9c32ad5ed1a2c0f0c6c0e6cb23c9e6391a7f8219b564880a8428f42d61de7f00a981f0303af6eee01a0d7d200dbc1e2126a04d13a8297c01fdfa0d9768189662188e6033025043c4cfa3c98e6614a6d06ef804c140043700ebe000150422d0bce12423eb522990fb5e60fb9859564a0c3c398e469f8e8cab7c0c0eb0b8cb72c8f27a8134592202a32457b4606835f5f007fd0b58779fc02a6048036f1b0f11da0625988623078849980cc09410f133e8f22691ff4e8ceb250e375e2b0409541bbe038394173b023b2e13050010dc03af8,
  0x1280c9248153e3ff4eaef01a422c54ec01e211c0035122090382f2640c05c4a9cf75c38333c4831793dc5df915c5bb76f4053747403b1d15b8779fc578e67001420806cbc29cde24e80b4a4a94f75860033c38327c483232c804959004376545a591d45cb74f45c90b8002a00b96e116bf9865f02a60658a032492054f8ffd3abbc06908b153b00788472d129f000382f18c488d4090884a8c907700bd33689053c09013a08fd2b88fb1380a178ac7120ac90c8ac51e8ac12f8abf1a929d060f803010008802d129f000d40e0bc63122090880e8284a8466d98ac39bdbbb8249003081101a813448036f21038f0788496a83895b038338009368836b5f00af4e8ff5f286597b2c635980c637d306577e8b913e8f2410c55529b4250ea51b90011305063998238ffb268fff038d6000d40e0bc63122090882d129f19b662b0e6f6eee092400c204406a04d1200dbc840e3c1e2125aa0e256c0e0d7c02bda20dad3a3fd7ca19674c195e6033025fa2e44fa3c90431554a6d0943a946e40045c2b0ce02a6c4c1418e6608e3fec9a3ffc0e35800350382f18c488242203a1106a4a756a158cc711ad81d87020a26419e0109245250ea53d0065e2b00225408a4a2b0f6d098127a1883fa8475aec409543190a3410e2719a720de33112998f27a4bada0523e268aa9238ab7170ac5a881179301018780a2fa906b3882902e19b801492972c0f67320f6530adc32ad60b148e98c07b12950184003010130500116607884d8e03f9bb852f4d5c537eb05392307c869ea0d8dcd180ce0003a110d20a04e42064511cc8028a082b4058ec4a6fec7202970991b95f89f30f3aa3db86403d6bb852f2307c32ad630adc320f654d5c5372c0f67eb05390004ead04a3112992a153a3fd4fa3c9fa2e444231e4943a9430810f401978ac0089506e302c22928ac3db42685068830fea1102550c6428d04389c669c8378cc4300c8ae29f61d2a04d110a69608a85c2afd7c2a248e2ac5042a3c9a2a8ce02a5ce45a980028568083242f672ab0061000c0400e3584c140045981e2136ee14bc8c1f0cab58c2b70c83d9535714dcb03d9c2c523a6301ec4a561a7aa380fe7ac14e460338000e84434828139081914473200a2820ad0163b0524a5d26d09a14c40701a20c3410e720de3572662719a2c0f67310c03770fd50b11222b8a4db0c462e47d8745c81b94429a5822aa03783916a15a029caac189293eb05392307c0d8dcd,
  0x1348c24780f401872898fea13101c3a63015cb61ec5b8e45a8564af6d4b823c9e8363735b6f49e2a91aa32a4c4ea9a20ded740e578219b76eee008950c6428200df7481924fa3c8943a9578ac1025504c1400e3586e302d040245ecb02349a02d74c02b48e021ce0020e6201f422928d043ace02746033800351300f0b416986210983f0164afd648881c7398c03b0b7337a8422822179006948ec34892836591250906275b03532c8f27da035d0692bb708217643ae5001d7adb18539c4440b238008323808798807d2680b5d300ad2307c2197a2a8a0279ce5611a56a366a8ca9313aa68837b5d03958b03c398e469f7c0c0eb6dbd278aa408037dd2064908a4a3410eb3809d02a60779fc57b461b039be0866ddbbb8022543190a078849001300f0b4169566a186212248428c1592bd2dcc1cf508ac012a1cb4761c082899067804218965f90d7d40075d102c88c1f0865e990eb94e710aa2809e739c2085eb6c61584695a8d8000f05a6a186892101581a4aed6a118793158799a207bea28c4fb298cbf4d9c53f760727b087151886d76b012b805c17df6818f2197a7a18875aec180ce000d20c85a161a110492b90e14fb14ad7ca19654a2264fa3c86e302c945b03081178ac02292808950ac4acc0e3584c140d043902550e0020e6201f5040245ecb0234003523a2d24285858fb8c1930850c30775a169a0ec9304e92b70e578219b4fb5828fa3c9a20ed5aa0ece61b4abd6c4ac46e0600e3598e661e2a936eee0e0020e6201f4945b00895178ac1025504c140003523a2d24285858fb8c1930850c30775a16bb24c13a0f0fb13ea52b54014b228fc84f086cf701ee9220fb02047357e0ac4002d058fb8c1930850c30775a401a04c13a2b12b3467c2e4aad5e293dde7f06cf72120b359638d41ee9220fb02047343c4abe6190eb57e0ac4d043902551e2a90e0020e6201f4003523a2d24285858fb8c1930850c30775a16bb24c13a3a96c4ac53aa482e16dbd202254000d42d2428590cb1bb2e10ea986c3c4abca57af09d10609df000d44c16c0e8122f92ad285ce79ea2ae0026821bc0a98342d633c28771228870e28a6be28964e3c2c002d1304e96c5082ebc12ab0236a0330c9a0315040307fa18eece193f6e19cc00fe1220e0bc908b41b92a90d3e507183ce893935dcd01df4a4a96be0c361800cd6400ae4cd169dd9516956e3c142e0023a03e48402edb845ae6842bdf031a8f4c19840a98196,
  0x134896110285103e801cc13abc43850edbc9c00e8904b85ee91b9068452cdecbc4a207be0d8dcd180ce000161682009a929a92dff808ecb8ea4b64e0e50244b6c5c481408950229283637363c9e80e3584c140045981e2124d0438c64286033800058986189208084e826011683c4b756a158cc711ad81d87020a26419e02307c2197a7a18875aec180ce00224840201683c0912db4b542a133c18471dfe4b5c52ab1d24b4ce63034444acdea13fa18e5e4018266e9224914720974028a04c1405c481408950c64293032e49a02948e029f9a19242c2d8ba1d0b8831a08108819665a90e3e6aefbb44b36447ba46e43b20b86f61a3cfa3c80e358045981e212494190422928d043a58b0df66190edc3637346033800058986189208084e826011683c3ab841092d9b3118cc94006fd9006ec8ad493607b57207a5c2079d4e1dd680de01c40a584a98e45a8561db4aa2809e73808950c64286033800890841683c3a84a580587b1fe4b5ca918000a1fb9c0c81531a80ff0d013112012f17812d2fa909006a74a3569306a56b2d25192d10301001166078849000d22618624820e805aa49a11b084216104188442592d5b319006ed40075d18b908ad493607b57207a5c2079e80de01c40a510a6984a98e45a8568088c1f0865e808950c64286033800890841683c3a84a580587b1d24b4c0a0d015b1781552f81771a8129123e21ea326938e0c92b980547157186d74b06b50a12cf03010000d22618624ba016a926846c21610411096518624b441851392cb805c70f1211492902e01840000d261ba0a4ac24104425946188284b3cb73070239708217643ae22b8a5001d7852c78fadb18539c4440b23316a1187932307c2197a2a8a0279ce5611a56a36180ce002240805aa49a11ed12cd9b0f02a4d38236e8a4b24ae4b1cbe2a3c7e112d08111cda110d141104e810f45e05fc7a05e674f1c460171c3d50588045981e21240034986e829241044258280f84e512c24b2c8e143966c8780a3c12350301054162000d2110960a03e13944801cc43850edbc9c00e980af28a4b252371a88d71e817917817f000d211028139448054ae4b1fa8af85c9a09ad0b5800142bc0e7939f4e813a26184b14d0776805f86003359002b75a45ed76545a50b800578e676591714f916f6e116b02a60779fc001421e2528e86c4b0c10713918d9306a5002de2607825968111441992c14a0d6c,
  0x134c4045980a98120070c1ac0084d493c36e41ee491c397d3607b41c342e80de12a99984a99ca8aa10b6121749bd1e49ce8c5b972396d403974e45a8564bcd18891c20d922331fc164bb68a028ba1d0326a0b8831bc1b8da07980c04002c098a102caa2809e73921b3054e6300dea11e40492eb9afc0f8d584695a8d8bea41ace2052850d043a380fdd21349dc36fbafa2dc4761c0828988c1f0865e89c6682c289066e81497a400f44c435dcc60b0460338000989611144139cc8003a0f8da1912f534c4e2df13cd40ec2dcc8a4bc521727190eb940075d1e1307d0f914e711d2809102c9fe1db521b305521349dc36fbafa2dc522331fc60338001103a671f29715c7b1601a8a62b74564bcc72d8f04737730010a681e32421038f4ea0a5d039568837be0866dd20649dbbb8b3809da81344100b15f00af6a83897e83855b0383d30657f286593e8f2529b41b90010c04b77292ef250ea55e3540235e08849d170ac3380a9b268aa7238ab56399813050038d6818d31011661b3380838a4f0db907b92484d2770dbee488cc7f4784c1485c9c180ce000440e95c7b12254865601a8a615b306ba725db142292f134746e4aa42411ccf4121e101cb68c591dcc0222070f4a401478c913e400c84d488812d584ba04c140045981ee4800571ec5805622854248e2908b40e0bc7292efc9084d486cce01ac0020e281ee491c2dcc1c4badc2079e805912a1cb54e7119032f540075d84ba0cc5a91e1305103fb61a7a8464106d4b823c9e9fee78aa2809e739584695a8d8e6300dea11e404836fbafa2dc4761c0828988c1f0865e8ba1d0b8831a07989c6682c289066e8c435dcc60b046033800098961103a260fc1906a0592ed31d45c2b0cf4071c24f500808343007dc22077404215c001103a1a9ae67976772220712eb38e4bea41fd11c0dace2124a085285102550d04389c6682c2d9a079890b1270b10c676eea380fd400b7826d50445104e7303e4512e910bd0e99b27091c0d38236f16059e8a4b9592ca924a09e2a91025509c6682c2d9a0798904b8550588c435dcc60b040034826258440a144139cc8003a0fabc7010e1bc90ed4b9c7239dbc451c8018943966c6012c93c123554162000d2258440a144139cc8003a0fabc7010e1bc90ed7628a4b94742e20c582e8681e6869ea0001616826159841912e39b0f048d53810146a3e98ab114cae15058800,
  0x14c7500f0991b9000d2138a631131b32fd36714fc26850865e8d043800348522985a4c65b85900378600577680535b802174745c576fc5eb763c5a30002006a9a24bf2d29964c5fa87d0c9fc38327af8301cf02fd860027c4832f9a032959004f91d45cb9314595763459393d45dd76f45db0b8000008406934a68e8d24bf2d2aaebc13152f4d08241cda2414f02404e823f4ae23ec003483a0a0349605552402ab4d94a011610717202af2e0d3f683ea000c4581311461c5837d4009f8c44c3d04516103300176852c4627130d330d3001f50402871a18aece193c00fe0b41083890a161b930b1a14ea316de9d035c00a18420e18c2393090d6f9882b681895aa22d4fa3c86e18ac9432857422cdfa22c56c22bd4a22b66202140e3584c1418e66000350b4108386313a26930702874448fece193cea4c0c0024a86fe020938b41083890a16558084c140c1db8669d1123b3e8f200092a1820938b41083890a16558083a930330d55846b14d515a8d98c3a949c669563c8c439bd34f152da83244b834fd86322c8e316c9a31654a6d0ba1d94bc7d06efa1ca12d40e3584c1418e6606033800248d4678202d2b6108464d544a570e20e0884c04fb10b8003a252c56e05cf76802f6585a1c48b4cf08e7d24274f404b765c033763c02702a60779fc00142fc8782a34a93a9e8612ff3ec4e894b15da00bf3c239f4909d9700ce024befa008d614b1e46447ba46ba84a6685a5eab41f19c4a36721274384bdf120cbd9617e64f5177652459c2e32dcf4121d2039668c5b8c439bd34f152d3571534b834fcb2e600a9803012ddca8a9d6b38fd643e5454c9084d4984a995ed19de7f05c32242411ce10b601ac012a998e45a8045981ee486033800330ec5815c22892389ec4bf7a8af8325c3830f91dc5cd933c5a974f4047765402fcf0f737d0c9f1d14fb9d0b586585f994916775ace3f779fc9a0329c4832f93d45dd0b8cb7590f951532457b462cb9802a60001422a0782493ea7a024becfb9860a47768a372cb9802a60590f9515324001422a078248b4a793a5f12f902bc8754d34c1954e022a65a90e14fb1829740d5d6c0d4da20dedaa0de7681885040207481905303c2f1a323d56490586322d4a6d09a3ffc8e316cbc31d46efa00e3584c1418e6600459800508920824e108882d1220e12f730d714d526e08858c3a9652459d564905643e54b2e606cce14e1dd730d78bc31d4221275d24a343012dc2411ccf4121c5c2b0c9a2a9c8e2ad44c14054428e06,
  0x130160a99ec396d9e07a7de3f548ac02ae0021834452a99a9c467d5e399dde7f00a980761c07809646cf722c0bad9638d41ee908289820473620fb10640941c07761240343c928e45a8cab58c2b71c8378cb03d9fac2d94c6429e2a917ec28c8dd8d04389c66918b9136c306033800890cc12b54161ae08933f4389c66900928c44c3cac0c82cba89edd01cf529b57b8aa1dcd2a999a111e4e3014448234cc0035022110248183acc3b4570464cf407da80cc34100a1c68627b386453e8f225061f2388bf2688b5da0359038d613050173bc000d4088ea091aa4ced344c007d2380f52680f33800a34100a15f009fc686277c0c69bb386453e8f225061fda035d4e8ba96883c16a83bf98ed1775b0b9b99019b10810b1b8a07038d61305001166078ee02a9800078088124b3da2d0184ce4189f687196013335182e01840000d21381476316290620a1337459d643e54b2e601e3b80aa60001e0209493e248a84cd4e391220e060f8018400301017816b000d20504e18b16600284ccd2c3248df300078948a85093e8e9331096620fb106409426a083c9297ec2902550d04389c669c8378ccab58c2b70001e0224904a3084c1dd5132f668c44c8c5a8daee15ac005704a56932d5a8461ccc561ca460338008f1dc1d932b041c4e02a4c1a946a4304061000c040183e07a062c32063c5e064448064c00348780a06614bda600984ca464d3abbcb380a901166078ee02b08000200885c4c9d0952f37299045f0e38c8206f19dbc7218e06cf2902e1986a54b010706909d8e8243d7079d7e0d4f10b9c90109fa75c58d1e90c70ea58060f87181316901597602f52582c12402ab1882954b828050261048a114d94a011391b941b4e790d5f403d6683ea430d77b18d8f0184003010008800116607b9224820b5d87717cb749f930f000c422846080264c945150502614d94a01160ead208d3341b4e0f3aa4d5c55d9f930f0013453115c4c8ee4c70eb94429a08128d9c849d818d314f131f2307c219704021416131d5001a7be846b72a2aa316e4aa66842d82e874398c01d8702e11237948209161299a720de331131b169319486d275479273484d277485d26f0da94488cc7f00880010dc03864b3916a180ce00022138523b0cc2993211265d24a3454428d2012148412cc1a11bc1e2154003b15c7b1608f2d48699c4f131f5c2b414fd00416d36532fc5a4c6402200043700e192c000885229b5a0b058,
  0x1133c52ab19213ed24dfa14b1e3eb6c614e711102c9fe1db5d280a8a11e67d0f90cc5a8461e4e881ef8a632fd36715ec061000c042447b836fbafa2dc4603380034ba0a6d59c7ca5c8e9f80695c160249a93599607e11244e463674d1c2c0c0400034a6a5a096112f60a144199357fc240aa946463e4cff83a960ae23ec4e464c003481a09168258440a014241355343dd9700ae4e4d453e4d3e183446ae0029c467d5e399dde7f00a9800015142bc2528e89206a9e4d4db82c90476887539d7a8c4833bcf033992845f575ace3f779fcd0b585b806976bc6017d0341af8343c38345939c6030014294bf2809b8a7a4e4d45b8590ccb2c803176802fc4830bcf0309765c5ab933c5ad2a0edb860d115b806976bc6017d0341939c603ab800a7119f578e67779fc02a600005450af094a3a2481aa793e4d3d0250f1e0000241285a161064d34edb213c24803e1a20c3fa847d874e98c0582a67b0e5b6781e9f78e5f22b001e02591b3dc8b02eb8482cd658e3507ba40811cd883ec4190250f1349073d470819f4aa663916a32ad630adc720de32c0f67eb0b653190a4095478aa45fb0a323763410e2719a462e44db0c5001d708933f180ce00024890cc12b54ec8586b95c4d2d0492680f37b84693db86737c0c6a33aaee0c2041a20c7d874582a667b52592202a10a3481345250e37173b006b000838a07b92472cc130505c9341a482e16dbd2022540121c3190a78aa4462e44db0c5001d7640e6147927370819f073d44aa663916a180ce00024890cc16bb26b8385703c4d25343808ab4c0f0b3ed60a4100b12380e75f00df6883b561838f6a83897e83855b0383d306577b8c68d986c68ff286593e8f2268c59529b4038d6130506399800038352f6508b455884938883aaee829aa0ecd6c0eb5860dbe61b1a3e60318dcfa3c94a6d1a22e65fa2e45742e546e4aa48e3fec884a8cf4018fea13a6301ec396408950c642978ac1025500e3584c1418e660048701ac012a998e45a86033800090cc168385703cbd88a2d15648134523e6f29b14438e50810d51410c4e810ac5e05ae7091bedfd11be524dfbd030d66e08840c0415058834960028a0603380005a5c22866af10e543a43a60028112124d0d2a30c2043d0061a20c3fa847d874e98c0582a67b0e5b6781e93916a022543190a5e2b040954180ce000243305a0e0d45703c5c9341325c84f09200f868830fea11f61d3a6,
  0x1a8b3a0d8dcd54162038d613050639982307c2197a7a18875aec0982614503cf5182e0fa5e0184000a285c82194d821d22b004aa663916a1d87020a262719a0b0a2313861e0259419367180ce00016350283d84215092050b485a42e114c43843a5490e99b8cc1a93718aa1a7a8ba1d0901b74b883276103da0f08a83b6d204db59638d41ee92120b35025522c0bade2a909c6682c289064d9cc4e1800058f6150925306611a7c42136f5bad4b80e63012e1aecdea12fc0f9de40f800058f61686611a7c421204db40a1788e71a88d9030102f9560c9a81200e000d21104e532003a136b0b866fc03e978989ea104d95042a448e2acc9a2a94e02a645c2b05bc2524c8c806100349607ee70028a000058d411028258f610900430725487a4da7c21a0b62a3241299a06825b16901507ba431386000f615092419367831f61d1a04acc264b8d60ba2a04d19e07dd860d7d7c01fc889a368189662188cfa3c94a6d0945b06e4c2d7808940808342207761a7a8ec3f549046648ac0172086536c3118b9124df92a1cb6b6c614e711102cbd0f90cc5a846b60761c158468aa2808c1f0828995a8d89e738865e89c668cab583c09747809642c288028a03637340e3584c1418e661c8378cc4e18c8dd8b00a24c20acc6033800058d411028258f6109004304e530b4e121690b44840724d94ee51e81271789d91a89d52f89d1c807277186d7002de8e86276044af10e543b4128c019b6d8ed3c807272f11b10e11c71b8a070a0f82b89090301000880000d4150928e82418896760184d85355060f8000d2068245a096050900a135f10443a962761b6c4e4635460b83eeb03007dd84ba21a7a8904d54dac1048838329c01240e4989e818404c2a133c52ab19213ed24dfa101cb4a634c5dcf50e2df13cd40061000c04121349dc36fb9fe1db521727121b1691e1292230b06033800349f28e81a57122558024b0856c528a39c81c4d741677f44163a292e56011352bb9617817f4504411faaa423fc3c3403a3660d3fe1ea32805c70f9d3c71154a5e4b23e000d206824b096876096110140a21e512f20fbac0fd50ed4b95d0e206ace9c6a427c04458044d45e44dcaee587eaa908ff0f0d00e8d9834ff87a8c9529792c8f8a40b8664d5cdac1048838329c0989ea101cb41240e69208e5dcf5018404cec2dcc8a08d5c2085d90eb940075c2a,
  0x10eb5a0b058070bc15b306713833c9a8195c941907e602be58b0df48754d13a3fd530b89fa2e450431558c4a84427d00808354e710aa4dfc6e4004f4071c3007dc220774ecb308ae297206e59006ed4006fdc2079d3607b518b900e3584c1400089028cc0561602cd6a22679ae3503a8824285b842d0204e07ec0f2545f82b12f020f319825d876f9f8a032a4830a562c2341c8a2322741a0b600330158580b35a8801c2a937f2809e609f24de50cf70924cd6120b3502fdb7a46a5cf90cc5a8468ab14dfa1a7a9681c0c90ae0a40b8664dec8c1f0ba1d084f08e6301200f81a096c865c0b8448682d8de520fe650722884a6685a439000a2c544ddc5c2b0ce02a6c9a2a9c8e2ad404598c4e181ee900610270b10c4182444028a1bc3eb16059c122755380f76500f8460338000583a4506a3d937d5a8468a85680a1a7aa72ab0901b7462e02380fd676ee860338000591453160670664decff93d01c70c01f702020d0881dd3b2cc5c81e97081e7643ae22b8a5001d74db0c462e4a0164612e8539c4440b23316a11a2ab52e0869ea4bada242b80d8dcda8b3a6f0fa180ce000161aa42858b4081ec5819c1b1f20f9379428c84f09200f81a096c682d8fe650722884a6685a4290cf70924dd41ee90c4e1800059141a8f690a16e10b41513775a8461e4c56f92881efb14dfac21c45681c0ca40b8664dce447ba46e43b20b7e9e4d4e2c0bad5846a120b359638d5e2a915a8d9025509c6687809642c289064d9c06100028a270b10c674d110716059c122755380f76500f841ee90c4e186033800059141a8f690a16e10b4150924dd60a5d035761839d6883996a83977e8393da062598ac66b3e8f25b0d232f102d529b4250ea51b930b5e0225093d43b0fd508933f46023d22b004429abd07a14aa664d821d5c82193916aad8c35158eab9caaca28c4fb0f871109a82c537e18b807607199a87095a06f90d8dcd8e03f59d34441c58167805c17bc8018d0489d54e03dd9403e1178119a8b3a038d613050639980116607ba41e0259409542307c2197a5611a56a367a18875aec1d87020a262719a0b0a231386419367180ce000164506a3da4285b842d054248664dce0a5d035761839d6883996a83977e8393da062598ac66b3e8f22f102d529b4250ea55b0d231b930b08933f4429a9caac18b04bc8ee742136f5e02253b0fd546023dbd07a1a28c4fb760719c8018d,
  0x14d81ed612e8869ea2413870489d54e03dd9403e16f0fa9dbba0184000a282e8742e1123316a119385180ce000164506a0b0bc0e9391428c1a47dd78ac120070c84d481ee4902fd91cb337a468204e059006ee5cf928059314dfad4b81fee79681c0d2eb682a1bc41c077540075d18b90a40b9102c8664dec8c1f0865c1009283831d45c2b0ce02a6c9a2a9c8e2ad430810f40182478004870363735b0107670b10c4182446a2ceb16059cfe650e6300de521c8378cc4d387228826798682d9c2079d7207a53607b584ba21a7a8904e1c122755380f76500f85bc3ea76ee806100028a0ba1d0b8448cc5a8464e14f64df46033800059141a82c2f03a0f138f4904943a9422416cd05c2b41f19c2c9aee2854400c6cce120070c84d481ee491cb30f401978ac02478118cc8ac0c94e71230157caa2809e6090c4e2c1c4e245c2b0c9a2a9c8e2ad44c140f64df404370e2d787ea580e750363734182444fe650ca920c2958b08d0c89d1c8378cc4d387228826798682d9c2079d7207a53607b584ba21a7a8904e1c122755380f76500f85bc3ea76ee806100028a0ba1d0b8449fee782a1bc5b010759006ed4006fe80592d4b812eb6aa2ce8e6300de5205a8d902fdb7a46a5cf9314df9681c0e70b10c716059ccc5a8464e146033800059141a82c0f8084e37ec0f2545f82b1003ee3064c2130775a160088810c4e2dc45d820d2a937f720de33134e1c8a20002c15858cc0088801c4e242e1986dd0fac4003a26294c0a0904e1c2e1986dd0f8711191ea9abbe72a2aed07930184000a289dbba9d344416f0fa0489d54e03dd9403e12e8742e112911ee91aea000164506a0b0464e14e4daf8325c3833f91dc5d1928c5f3949353ab8006585a3a717e9a10476340258b03c34f9003d2900598e469721038fe803b71e035d6d8245f28655986c68b97e461fbd3ce558f27a1881b0e756a0657779fc02a6075ac85b089d7b840dff980af078849b182e921d5344e8ff5b8bec4c2e27e8b910f1e0410c556312a1108e411b9001a482393d01c70813810c01f7852c78fa0164612e8a207beb52e0869eab087114bada242b80881dd2902e440b219937b0d8dcd018409d34441a8b3a6f0fa0489d54e03dd9403e13d937d32a4830a562c2341c8a2398c037948322741a0b62e8742e112911ee91aea038d613050238ab5268aa7380a9b170ac301085706091100a28180ce000164506a,
  0x1067c1c40a4fa3c94a6d12a9999039854039746e4004761c0308108249b468831f61d1608a8e45a8564e64943a945c2b0ce02a6c9a2a9c8e2ad47ee31e86215846978ac0aa2800895022929d6bb15a8d9025509e738c6428d04389c668b03d9d8e6604c1400e358c4eabac374c04870363736380fd4182446a2ceb16059f2006351e12ae1a7a8904e1c122755380f76500f85bc3ea76ee806100028a02c4e5c6033800059141a858d683c4e6c2e0f870319b804937e14aacf43e474a020184000a288e03f59c2c431c581670489d54e03dd9403e12307c2197a5611a56a36000164506a168564e65344c009d5f007fe68649988623962c37d410f133e8f24e8ceb250ea56dbd25e2b01b930b78ac840bf63d00608905ba75d88de91a2b0323417009106d7e0799973e4071389ad07c150eaba28c4fbc537e7f876d67137b18b807607195a06f98c055f2a8a05182e279821690a0f938d43138b170ac3380a9b268aa7238ab5130502f13913d937d010dc3884b51f841103865d0c1395099e6720de33316a2e874322743134e2c23430a5632a481193852e1121a0b63f9941c8a28e03f5060911c58167c8018d178119a8b3a869ea2413870489d54e03dd9403e16f0fa9dbba0184000a28180ce000164506a0b13975922206eed4b80ae5b312eb688ae2940075d18b90a40b9102c8664dec8c1f0865c1000a2c54428c84f09200f81a096c1ee9220fb17e4e4c1c07dc3c810363736a2ce8fe650ca920c2958b08d0e6300de520c89d1c8378cc4d387228826798682d9c2079d7207a53607b584ba21a7a8904e1c122755380f76500f85bc3ea76ee806100028a0ba1d0b8448cc5a8464e146033800059141a82c0c1395070d3e400e805906cce020e2884d481ee4ad4b811cb312eb6990eb940075d18b90a40b94e711102c8664decaa2808c1f09e608865c10c0ac500c28363736a2ce8e6300de521c2079d7207a53607b584ba21a7a8904e1c122755380f76500f85bc3ea76ee806100028a0ba1d0b8448cc5a8464e146033800059141a82c3b17e4e4c1c34f9003a01641b3380838a2135207b92b52e0472cc4bada643ae0713835001d7462e42902e539c47f876d440b219937b2a8a02307c27982219704302b14030ab8bec0f138f3d937d0d8dcda8b3a32a4830a562c234398c03794832274720de33134e1c8a2099e61a0b67081e75c81e9,
  0x13700ebe0244d2d2a99ab2e40761c29b57b88249b5a111e4c68832881ef9f61d2c21c35604dee01505e5bc2520002832054cbebf928d580c04274d11044823dc34240c182444f0d01380f76500f84ae100676ee86a4eadc8378cb03d9fac2d94d0438c642902551e2a9118b9136c3140075dc2085d72086590086eb630d5584695a8d87ee30224cfd10a688c1f0865e89c66a72ab062e00e45a8564e8c981a9d520f3f14df9681bee70b10c4363736380fd45e23b4028a060338000591416066d504a0a0964ebd3531e0259e802df8b02eb8482cd658e351b3dc07ba40811cd41902588139d32ad630adc3190a4095478aa4323763410e000161635a1285a30844625bb22b13ad4cfc38e3110a683a4df48c1f2204e74865e83c4e6c9c669c8378cb03d9cc44c3fac153c9edd1f61d0aa1dcd608a8e45a8564e8c264ea672ab314df8981a9c62e01681be5460b83e4e9dfee782a4e7c2c4e5e1a7a8904e1c12275716059d280545bc3e836373406101520f3e380fd676ee9b0107434240c028a1380f76500f846033800059141a93ab6685a438c446e500850001384a148264ea52e93111b91613a5030101208f70d090306091100a28178119a8b3a000164506a0f93a74e85c8378cb03d9cc44c3fac153c9edd1f61d0aa1dcd608a8e45a8564e8e1a7a8904e1dbc3ea76ee82c4e5dfee782a4e7c122755380f76500f85280545b0107406100028a0981abd2c03fd520f3f14df9681c0e70b10c716059c6033800059141a83e1613a54cb77a468762f365cf90003484a053d0160564e8d3538b02ebe802df1b3dc84900d1e132f658e3578aa4080f6dacb90318e550e38c2719a320f65a6d5ee27b740e937d313864d5cdd1bb8dcf07ba468447932a877388139d8e03f532ad630adc0b13977fb9e0a939f0489d54e03dd9403e14a01516c041d0184000a285a07039c2c431c58167a207beb087119d344410f139b000164506a0f858d68c211193a10b83e1bc4661bb400e8a08690280a939fdd8c1dfb0d04397e0ac49c668c63954c44c3c9edd0aa1dcdfee78cab58c2b70000584a1635a2b220118c2125939db311808f5360876f41e86b630d68a313ef14df9d81c65681be5460b83eb68fcb828c5b8e6300dea11e4019724d052218dc429a08ac026010dbc78c913e400c6c0e6c840e3c1e21242044053a829740e55a20def8219b74819276eee2ce0276a04d1aa0e25fa0e156c0e0d0402c57c02bfca19674c195dc2,
  0x15880c040986e802c0858fb0f61603c31ed7ec28c89d0b08d0c2958ca921e2b20c6608d05c102fd8682d8fe65072289c8378e9d76227e282b41f04a668c44c8df8f39f27119c2c8761ca45a8daee15ac7a30b5c08f576cc9aeb912a06777a468cc5ab1cb325c4f1c4649bdc2364c1c36ec8a36bd40369536367d90366572365436a5060338002992174f2cb89423de1f9366000a0c8aff060b311aa24120b15178b0d0d12470301064b2a3f012261ba191e614a1400b02163ec3d8580f0c7b31982341709f8a0ad07c7c9c4670b21e8c25db326bae4c72cc7081e7612e82e8742c2345f82e97202d93202cb3082c93282c52e1121a0b63f9941c8a278ac840bf612932da75d88de91a1d872b7e0799973e43316a1192755c8d97070dbd228db1500da74d8da1640d9ba28c4f3c505a8684a98404650da94180ce000a6486d3c95a856f904649bf142706033800970a6485d3c7879080f9c34047e50b9a7cb68004d74b450a204e9204b8ce4703e4f161e0d01594204214a3566c30600135d2d1428813a1b0ce470961993c3030f2c19b7844d262b0e6d3001f492c931a189c840e3f680d74002f3f8090542d1421e1a885a5a921d744909864f07241b0f1121038f4100b1078849f28659d3065706a684e8ceb268c593e8f2529b41bbe0173b0250e37081f423b2e38394038d613050639980121c6dbd278aa40018c0f0bc22038168424efcc790912a3000bc63088350384893bd831a049b5f61d3101c160a995c9999e079ddc3f54addb30b00a25c8378cc4f58d0438008905a11858c70ae53b11cf78aed2ba53bb9b1080f9cda0f8c0043f50ed4810e143950e90eabcbf13b9345f161c1c32054c7a044cbe0445281bd6a21b0c5e276400b782a9492e43b5681128a0493b7b31360875c2085d18cc990eb800891763b3de2bb51c9b93b50466a21b0dcc3a04be2744280b8664ec43e1bc4ae1004e8d986a4eac18244434240db0107676ee9520f3c061000c040028a096e794e1dd4aa2809e738000585a119fe3b12ef78aed471144ececc7082174db0cad8c354429ac537e9caac5a06fb18b800d8dcd2307c2197a5611a56a3646332643ae8e03f59c2c431180ce00016168465d8ecf78aed471141993b14965203964e63001ac02124d0cdea111cb301e2125e431ec207d01c40a53a33ac72097430811b6f4978ac008950ac4eb46e4c2c8e2acc9a2a945c2b044c14004,
  0x17f84c53913d3070dc14894d31488cc7f486d3c9485d3cb484d2770da94180ce00206298ce4874bc0e0d44f7c0f97c0c6a38b109d2492053abbc1e0c89078ee02b08000bc35264108201713dd03e5f031a8e2c4274924814eaef0783224b44f641e3b9080fe4f60a2c0ac21b61174544a2676d1c8f2006258002a92112c24aa87a8c86acea74f1c45529792c8fa7cb689049f4f0106ca40b8dac10664634aee5a500fa5b0dc9d0e30322c2412484524a0992ca82a6f8fc048986ea6af1135f376c3a0c8584094d0438c642902551e2a92b2e429b57b9a111e4e88113a40e3584c140061000c04150588524c645e2c4e30148c884f54f44f5cfea10182cdc482c6c342c9402200ae5b31c2079c8a36dd4036ad36c317207a584a98ba49ed18b9110a688c1f0865ea72125c7289b101c15cb623c11ac9c6682c520c44c3c9edd0aa1dcdfe1317a6301ec5b8e44f4ed412041c370522534c522331fd21b4f252174f2d21349dc36a506033800818a633921d2f038350ac4f6c68d7b840e53e8f2859245250641962c37d4ea1e1bbe03839423b2e078ee02b08000ce470bc0e286fe04e48935d10af608220700b44f66e6bf3f42902e19918d0e832049211492820a9be3f0128c0ddd1610250f0063190a40954018400301000880002063b04a16906790d413944110f44f5e5e2902e19918d902aa049211492820a9be261ba0e83216134d0f1e010bc68c05230b1483190a40954018400301000880002063b0de169062f0383504e51044221224f57c6022540c2043d006010dc2b13cf03af808905b09106d0993cd78ac831982a75d889f8a07e3ce7c9c4d7023d5db32c72cc4d822f5c81b970819f852c78fa01644a872d640cbd911ee32274398c01d8703417091aea1a0b6379483f994209161c8a21299a720de31697a311311ad07c2e875d672023316a0da948f046bb504819c84977284afa2044e9228db7070dc1500dab180ce000a64876fa3913d37d054390400350bc109220e088f193671b3dc883ec0811cd32a4830a562c2345fb0a0035a4190030750c160ac4f3cb89421901f91c6000a0c8aff060b311aa24120b15178b0d0d12470301064b2a3f012261ba191e614a1400b02228db7070dc11e8c20da94000a6be906791a0400ae52b77de462c60993cd9b0e82b44f02b55382b4d142b5d08708da4607e2ba4aee5980028322bfc182cc46a890482c545e2c3434491d50,
  0x122d5fa22c56c22bdee10396163eb5860e6d740e55b6117782199676d1c8c8e021d563c992caa6247eda89a1e2b207811b69d76209213263c4c7df8f3b301dbdcaba28c5935c08fd4e08059e07a62206e41cd400e3598e660761c082458e6300de520ba1d0b84494a6d06e43645c39cc30c798ab1064798682da92112e74f1c466af12b2cd04c140045981e2154004f02c0983ef699c2a8561f8222f0425c93e92e35085c87e2bb41227458030fc664634aee58322bfc182cc4482c545e2c3434491c0c0406479924a082a6f8fc048986e85285002c08584f3c3c31ecd05c2b41f19c2c9aeb931cb317206e5c2067e805912a1cb4c89d0e6300761c102fd8c6608682d8de520fe65082458722884a669c8378c5a738c44c477a46a7e280ba1d765cf91f21db4cc5a84649cd9036741c36fc8a36cd4036a536368f1412b301305ca12aed411f63c119c36a5060338002991ecd80a1ea321ab3a2fafe4b23e9f2da4a2c02902e19918d822960c8b09049211492820a9be3f012261ba0e8321610250f2542f13df8c05230893e33d13d7178b13060b37120b1b0d0b251493190301001840008800113e12b96cc5c81e97081e7612a62e927b4db0c462e415a024429a2307cacb903fa841ca26409543190a2197a2719a31130f0b14827b74a6d5eec4070e98c02a87736844793572d87b16e3913d3500dab070dc1228db7a2044e97f84c59c8497b504818f046b4894d31488cc7f484d2770da94486d3c9485d3cb180ce00206298ce4875a60287a8c86ace8bea412c8fa7cb69ace20a440fc329c2384a2c12484524a082a6f8fc048986ea3014ec584cfcd0438865e8c6429025509c668061000c040022000081a243b04ad5106791ae330d41884e51044730224f8fac2902e36b0419918d0ca70120b1b03010018400492114928264b2a0a9be261ba9abc414a1400b021e2981610250d084b4d0ee10af80f21c06084f50966a18dc0da943410e3190a4095478aa4000a61285a41bb2640044f85245250ea52691ff1bbe01713dd23b2e383941512815e2b0a482e1091e06dbd22b13db3d13d7060b37120b1b0d0b250088013050038d64095478aa41ca26c4070572d88f046b3fa84acb90a6d5ee6844793a2044e92b96cc7081e7228db7500dab4db0c5c81e9612a62e927b462e44429a2307c2197a9c84972719a0b148e98c07b16eb5048131130f27b742a8773,
  0x1f029d76208412cc54126d2012158030fdf8f39caba2728628c590322c0f5c08fd9e07a51007462206e436a500a9800c040e6300de520ba1d0b8448fc048fe6515ed186c131dfe1db4aa2809e6090c6f85ea2064798682d8dac1052850d05c2b41f0124834aee580610002200045981e2154002993c0b04e11144098145a02a1588c5c93fb06e7de3f56805912a1cb6d412163c11bd3e400c78c908412cdcaba19e4fd536c30201265102c9d28081e21541cd408a36e4761c082458e6300de520ba1d0b844860338008913c0b0ae515892c719c4fe41b9f78fd5a01644a872db504858f046f4f90031e3242104b372ae86793f51b04c77f876d4db0c462e40804992a93ef440b274a023313210e13f12307c219704021418b888e127d6c2c0c80189692fe71a906000a3683e30c811754a5e4512e9942e69f2da17a861a8fa1e8942902e53119919918d0da9407350228db90184003010541621d87020916398c0379482e8742e1128c0ddd3f0123f994191e61a0b604920d2bb960088001166078855339a647b36180ce0020629b540b04e2b944451026051682593f7b317207a5c2079d18b9136c3140075c00890ec470ae56b99e4fd437f4e8c91962c647000fc508854108883ea5a84fccccd0f02910735001166078855002064f13610f852340384fc437f4e8c91962c6473e8f22513ed2693eb6d845d9db472364b2a78ac8a75d887e0799a28c4f78e860b773c0751d15b82c8e4dc3831baf831986003f5900375b8f05578e6791545b974745b7658c719a10af0b8e454f84832484c92104b3b5131fcc076f72ae806846f5381ff6781e784072d2b76cc770fd55c93e9529b41b90d9170e73380f3d0c31ea4844b092aa022960e38c0e92e14203fb5001d74db0c462e4080499440b274a0207350228db902a60779fc038d6130506399800880011660788551d87020916398c0379482e8742e11204920d9d3c7119abc4acb3462ac4191e61a0b63683e3942e63f0123f9943a366180ce002244f02c138ae51114409abc2583e801cc43b640f6a087419c2a8564fbd02f6888c1909345f0a374100ef61839b5d03954c3b87c04695e08665cb066313050529b401166001422f3842d0ea1b1da992162513ed829a20ed5860e6e61b1a2f821995563c9a8195daa22d57422cdfa22c56c22bdee10397e602d40e3598e6614a6d000350bcbd8883a86c2693eb0ed79882a61b1a2daa,
  0x14c6d36532fc003484e0a84a160a6503dce2719a9f8a03113117c876d2e875dcc04cf7284b9000900a84a1581650341c73b032a01643884b73316a7284b91196e298cbf8c0525b50d09398c00f0064d9c515099ba379483f994209161c8a200880180ce000d4110980e8903f0303d02c502c3f9700ee7743883c08f571812f541620088001166078ee02b083a0403453ba000200f8629daf25483a121409e22380fe5c6a41c04b95800280c040e8100d14ee98ab10ae4a3c121b945ea186a3e87a2514cae002200045981e3b80ac20000803e1884413890bc83a7609687944501e0a7e83bb61837d98e4697d206415592456a8d25688b995d0b953d01c7a0164b52e04bada268aa9a8811763998221f4529b45b0d231bbe023b2e1305038394038d601166078ee02b08000207b0380f844058561083a072642f0b40c9405621d6b21f8331ec60ba48c1f2e2fb08641b43c780ca920c2958b08d0c89d0682d9c8378cc4d3872288363734cc5a846b623c9e8a632fd367145402200045981e3b80ac20761c08245860338000802c8805826024500ccfdf980af2a0c9721d4cff410081ab8bb786004bc68c8d5592419a086f74fc043618c8b238c5b9392f71bbe82f3c6268fff170ffd0c31e092aa3d3f40ea6c4e03dd423fc3c3403684434504413a043d62ac4942e654a5e2bb969d3c711191e63f012261ba9abc4038d6130505416200880011661c8a23f9941a0b6acb346593172c8f8757b46779fc078ee02b08000202482c0693e0e03e1104e0994011be7164cdd460b806100003484e051680a062760a44ffd2f7170c890c31e092aa3d3f40e93b93c03df4e04193a04170891f162ac454a5e4512e9942e68206f12902e4f92fb198b858612ff4b3c0e804eb590f952cb98600c3fed078f06846f0c8b01da822d84072d15049b2b76cc770fd59ca184db0c07350228db902a6003010541621d87020916911ee91aea3f0123f99457b4617a88191e61a0b636b0414a1434170ad07c04920d2bb960184000880011660788555c93fb6713f946332539c41b04c77f876d2a8a027982431be0da94180ce000a64f3540b04e2b944451026051680a8562a0aed6b93fd325eae00218012d9616ce9c164c783e55d3f010dd9700add8f007e4e4bdc5c3ff430c7824aa8f4fd03a2e2508108c2247c58ab115297a50b9a081bc4a40b992ca8662e15e2b212c,
  0x12366a2ce9505880034866af10ed0e8284b90e94806a50be6c42040f4e04053a0403629387191ea72a2a2e8742e20c6f11e5683c2018400301054162000d2168f605846af10edbc83a60144110288790e921142d9b138236cf0106e8a029b0c18329c02a133dfe1dd5760834bc47dc3007dd84a98ba1d0b8831a0f09080f94a8400d200f8fea13a6301ec5b87a044ce80f6ed4b82a21adefc1ae4061000c04150588aa2809e7381ee906cf70c6428ae0fb5140fd4da0fdcbea405e04b44804bc1804d4349607ecf9d0e00121b5dacb4802200043700e192c0008866168f606854058460506207042630fc50acc71779fc0803f94f83e506bfc07884d7026c1fb3e3a3663c3403683d10010fd65a4043950edaf25008a3850a54190d0a051209db6f06e56938e00196bcade1109025812509ca070a0f80006e34818509523f2680b52380874100a1d3066198862db3864f3a942125141f13050000d402030090b42a0f40e14234d0e002cd3002b7e6196fca0e348e031c9a03150403057c02fd3a50776e19a4fa3c9aa2e5c0e3584c14000350080c0242d0a8558ea508409da80df9e6863f00030fe0242d0f40e094507c0ada8134f9865b3808abf283873ed60a6883997e83935b03912380c72680c54100c15f00bf98ac66bdb86691305063998529b4000d4020302d0ea3ee53a6a141d387ca81034780f4c92108c1e2134006c18a54908506c0a0c9a82f9561e814f1a815117815500044b784e5112853141955980029bc1b8c32238d8a101c0c0407a053c6a05445e0554121bd5a41bbc000f84434864139440a8f0505d4130b140b02066b488637e0839398043653ec60a5d0a69220c914bae63e8f2688a796a8a71618a81bf03df25063f2592e143a66cb3809d5b0d23529b44203f93683f7a81341b930b743885f0a89238ab1410a8f268aa3380a97170abf71a906000a0486e517a861a8fa1e8943a0403532b862ac4038d6130506399803010541620611c70088001166078ee02b082b83c74e03cb4503cf0525e000200e03e1884e5483a109448789050550a2719a431be3111b9161411000621104e26042510903a82a3f0303d0d42f04a504d3d73fa841ca262719a07101f311299c4070e98c0218d3d572d87b16e2315e3916a3884b715940db52e08f27a7284b97484a329940f00880180ce000d4188441389810944240ea0a8fc0c0f42f04a1614117389c66a7e158cc4,
  0x18a9360875720864e45aab630d4564e8c2250d5c8378de86215846826a08c4f58b00a24c8dd9d6bb15a8d902550c6428d04389c50fcc2b70cab582c50f68a313edd81c6e76f11461a7a90e59b0902f6508ff152fc0363735505880e3584c140ae0fb5140fd4da0fddd0e00f0106db0c1b14df96846344804bc0c0424c8c8e82354028a0121b5dacb485c2b04e02a649a2a948e2acd042a44fc1ade7c044c603380013816068960e844350621987a05144137a42646e75466800138d2189244b8141904a27143f302c2250c4ea50ec9450e578ac030810f401824781b6f48acfb17e0ba5e2b2102fda9d76237a469f81e665cf90cc5a8468a9c8378cba1d026798c89d0f6096cc4d38b08d0c2958ca920b8448682d8fe650722884c1406033800068d4f40b4e121690b44191caa2842c50f6683e8f2529b4038d6639980001a35042221563a943b03aea032edf011a55e9d19d400fe0b485a429918c25143960a7e2810c4e2df21dd4263fc730133cca920c2958b08d0c89d0682d9c8378cc4d387228800058468802c0214e0a943740c4e0020c6e43666247ec5c48148847dc0808354e1dd730133c9650ce9208e578089424f50ec0c81804d47ecf9acb49d0e0214b1e4452ab0e21276447b9d2a692a99a46e42ae002183445ae4cfce45abb20b7e9c467eb630d456f90761c29e4d4d5ed19de7f00a98314df83637348289a2c0bad9638d46cf701ee90a632fd064094203db6124034784cbe20fb136715d55846826a08aa2823014ec8c1f2ee14bc3c928c8dd97ec29e2a915a8d9025509e738c6428865e8d0438b03d9c9c669c8378fac2d944c14002200043700e192ccab58c2b7060338000886612924d5143513edd81c6e8a11e8676f11475c09150e59b2641a5508ff1f0303aea032ede9d19d5563c9a89a03040c54a6d06e50c5042a448e2acc9a2a94e02a645c2b05524da4e82356000286a50bcf4071e80de0e6300dea11e40f93e325c8450b4f0106db0c18329c04c1418e660061000c04150588d0439e8621d6bb15ed186cf70c64281ee90ae0fb5140fd4da0fdcbea405e04b44804bc1804d4349607ecf9d0e00121b5dacb4802200043700e192cfc50ac24f512a998989ea10b60761c0828980008866168f6068541c81611a026e0620718c25943344ad300277fa18ef9a19344c140043700e192c00089222d38490b441b94314ee6501aed38236ce8,
  0x1508e1f0285e724945f2a14591714579902477604fd5a04e71884a30e01dfd7079da28c79f630eafc507839c95e6bbf27e02f79702db670297d6bec0982ab191ea25b9e298d312201f52f020f38b7c4f3500108573b0c0322944567876515875d88ecd7fb18d8f3db860f3aa5f824d32025541b4e328267790d5f3082852c02a1683ea488cc19484d277571323bb85477d874479273486d2750d8cd35813111690e403d65d8771485c4bfbe84c5cc07737cb749f930f180ce000c406846869461454d563c86e1936ce0296165175a845040e3584c14000350080c178088b424945f829860e75aa0e5e62b199f2c516dfa0dd56c0dcce002cda20e2e58b190fe619465a9194f9a511d563c9742e7d3030ed4a6d06e512d8e6608e51440e359a845044c14000350080c178088b424a165175344100c15f00bf003f8908b485aa0e132c516d44d26944f239451038d6000d4020305e0222d0a851640a2f89d10d09dd1e89d31209db0c89d71a89d50a02e4e04191986a73a36642040d36840b3c04072b84018229654b9c9db1e0e94551790c30f8ecf0504758b00f72100bb8f07337c046a1d306610614254a81ad3abbc09108b0184003010008800108570007606846070080c0160a89014924649b61714571b954c3a8289604e0287a2b046a2b0c482b24322b14be2afc0c040185094eaef0022000035090170a87303a5154671db80c93abbc2d144d26944f210e1f239451038d60001a350080c178089421b14533c9a819a49419446e19372c031f4c02dece029c0002030a1822239451829860e35a2411e5a9194d563c9aa22d5a819a53002b46e1935040244e0020d7422cdfa22c56c22bd4a22b72c0317e602d6ce0295ecb02566202140e3598e66000350080c0222a09a513cf22506516a0645d300b3e69447e114494c0c3b1b944b038d613050000d4020305e0222a0b490a165134cbb4c009d7a74683e6864d003f85e0222d2428586e512d344100c15f00bfdb8667e083973ee60a7e83755b037361838d68838b962c64396a4653558f26a0645e694475d0b9f4c0c3b529b4038d61305063998000d4020305e0222a0b490a16e10ea5124cc34100a1003f82d24285aa0e69447387ca807c492082c1ee4800069845388a51159a16aa4313eab1b2a1a02ab001922404a0994434acea04d1860d7d7c01fc3c81368189662188c8850ecfa3c86e4c2c9450e424f51b60915780894ec3f548ac012a998761c08249b4688311808f5f61d2f41e8560,
  0x1009f00186d30007606846070085e022148160a8644902869147f11d4981a9e3c1ccd52e712a06b424422c3a9b0b4518d08108c8851dc04215d505881851bc027c0e8105d381065141074da107e084e7cae1004f0101e761b6d460b83e1bbc061b4c001d81a1181c02178088520582a191240a1a424947d3b45a22e846e42445c422c4206b5dc4cae1011d4981ad64cff84e0284804bc5ea186a3e87a25032054cbebf86c51c5ac1b554c1b9d281bd404215c0c0401851bc027c0061b4c001d81a07008089b6148160a8644905404947b0283404c44804bc5ea186a3e87a25032054cbebf9ac1b554c1b9d281bd42851dc6c51cc30518c5c4c9c0c0401851bc027c0061b4c00068d402178088520a864491920814791bfca40b9fd1058c661b65800294c506434056c5e05546a05447a053da451d44842ec3242f40c040027c0061b4c001482a19124110882482851de6c1f84113c04072b84019d86db42042336841f45041d4e04193a04175182e82139f0f86ef54162009f0003a20a864220920a1a451d66c45041d4e04193a041782139f42040d1f841136840b3c04072b84014a14190d0ea9d86db6f06d95182e1210bb0494710f8ecf8b109d210e1f0301054162009f00186d3078ee02b080001a1482a1912464844080881b147304bd4438e45ea18340564bebf9ac1b55fd11c154c1b9d281bd40c040027c0061b4c001482a191241106c0494711bd5a40574283e000020d20a81851bd09d8e824324820b07b92470c03150eb7581311de91a9714675d87717cb749f930fd7079d7e02f7d6bec09946b5f824d32025541b4e328267790d5f308285403d62c02a1683ea3db860f3aab18d8f180ce000c4068463b146d076c204c951c300c1c51a75c1e7442e71aefc9f8353e40427d9c51969d716347a431c3a960183e00c04006102c20b8c960b04620a552e0a136528044e46e412402dd80bd4900aac14098402c0906d39e4357d00f59a0fa90c35dfb2361ec6363df61d1604c45761dc5f2dd27e4c3c003101a1182651ac15b1b108f6906ef2910899902470e01df2f020f1e90c707884b0001a53898190280d0fc1482a9aba2b78441f910092f407146915d5680b5d365280458415dc80b6d5a352623b35ff101c15c4c8eee151df61d1604c44003125c519ca011610574d9c53f720297218d3d403d6c4070571323bb85477d874581311000c41499c5194ee508e1f0285e724945f2a14590001a350b4020305e022518cee,
  0x12305f0103d74c02dc0c04150589742e7c0e359aa4cec6e52345c422c4c14004215e58b191c183e04842ecbe42fc06100028a000068567a01619098070220c0242f1a80a8284908e524cee73c04079006a79d86db4204231fb7236841f45041d3a04175182e82139f0f86ef4a148f7604fda28c79bbd02476d869d98e43c58b06117734079809b8590ccbc48317cf03157d031376803b5b8039915c5bf747c5bdab800659317a70cc92c8f8757b46779fc02a604f836d15037f2a038d1b039b0788494e8df768838be0866d96a465b9804639dbbb8d300ad7b2c08d03010541625d0b9f038d66a933b1b948d17108b13050010857962c647060f81210bb2f90bf0184000a280001a159e8058642601c08830090f42f1a80a8284913052442e1986d90f871f531419f68ee50d015b1781551a81511e814f00064e8ade0a0445118024a3a64928523d343800834c009d2380c72680c54100c15f00bf98862de6864ddb867300022093f82d0bc1b948d4d0e0030d7cb7904031300632c19c4ea50849a513c84387c920e756c0e4662b5225aa0d65fa0d554a0d465f90d7c1e21253a3a6578518c8e51440e3584c1405c422c00068d4088300915602148b4d17c02bce0272504031300609a272f4c1984ea3c9a819ad740e54000c286fe0b455808908fa93ec4fb998ad489128ca634c4525214e2df13cd40ec51b6725799c0a5f5afb02651aefa131521712ff301dcd21b49d51e49ccf6e183cea97e0934c8095506d38ca099de4357cc20a14b00a85a0fa9f2dd27e4c3d223306521349dc36334d604c445a43900f5860338003101a1194871bfca40b9fd1058c661b65800294c506434056c6c520c5e05546a05447a053da451fc4842ec3242f41251ec2051e41851bdd813f568139c9012e496e78a6403c0c040027c0061b4d5c4c8eee151df61d1604c47301dce1a5187141e0e8a31e7c04215cbc083d761dc5f2dd27e4c3d8c089e6e1e065c519c38077daefc99c0a5e64091cec51b75c1e75f80bdf5afb02651ad7e0934c8095506d38ca099de4357cc20a1500f58b00a85a0fa8f6e183ceaac6363c003101a1185252144119d86e30e91072902e1986d95314810c1453210e1f078ee0285e70301006146f009f00c90bd1210bb0186d31e814f0001a350085e0221482a191240a1281b14833a84e506400b7844511282a14c52066c1f841142040d0c1453210e1f078ee0285e724947d3c04072b84019d86db36841f45041d4e04193a04175182e82139f0f86ef01085754162,
  0x12f14a9523cbe42fc4842eda45254183e0061000c041505880034864260920a9248e9922f028529fe25111e506014b0c81532fafe4b06b55306e74a06f500064262de2102a0c01252979ecc076f0a94a13e8f21b948d53820f02148b250e2917108b13050038d64881c51081ad2201f50e01df0108577cb749f930f97146767875b7707297e02f7b18d8f88873b7b027d2404b986875d0504758f072b571323bb85477d8745813116ba187484a3670297d6bec0982955f824d32025541b4e328267790d5f3082852c02a1683ea3db860f3aa403d63316a119487180ce000c4068620581c528c0a0d3fe123e206014b17a861a81291e81270c81532fafe4b06b55306e77186d74a06f50a149f0301000a280015806856189e8058642601c08830090f42f1a80a94a1cf9d0e20a40b83a2a8dc6a40661b658052654c520448055da45275d813f68a31e6c84387ef4091c92479db61a6e520eac540dfc1e2125f0103cd3e328d3a37de16511da21188e035e5d719f5e9f19ed3030ed8c089e6e1dffd0139d24526c183e0061000c04150588028a1742e7c0e3596c2e6daa4cec6e52345c422c4c14004215ece191658b191c005601a158627a01619098070220c0243d0bc6a02a0a149f3b9d081034f0101e401a9e761b6c7edc8da107d141074e8105d460ba084e7c3e1bbc0019098e890fd2f02a0a0a869149d3b9d081034f0101e401a9e761b6c7edc8da107d141074e8105d460ba084e7c3e1bbd28526484387c1e3b80a179c92525dd813f68a31e6ef4091db61a6df0103ce16511c8e524d305244be42fc4842ec061000c041505884c1405c422c04215ece1914183e0028a000068567a01619098070220c0243d0bc6a02a0a124526c0a0d2580c818f1fb72c8071f8206f12902e1986d95314811781551a81511e814f0184003010060f8000d2190bc0a82851180648a84a14991c7ca40bbda063c661b661e0294c506434056c5e05546a05447a053da452540019098e8ade43f4bc0a82811144601922494973b9cf0101e401a9e761b6d08108c7edc8da107d141074e8105d460ba084e7c3e1bbc0019098e890fd2f02a0a0926914953b9cf0101e401a9e761b6d08108c7edc8da107d141074e8105d460ba084e7c3e1bbd28523e2c1845dcd01e6026e164332f120c5f3c0c55f40c4dda00ed6e00e645716fdd1f16f6ae4c55964c5d5ed19d813f4b23e1c6c387f42d61de7f00a9828a31e6c540dfca80e341e2126f4091d3a37ddb61a6e5a9196da2,
  0x1151df61d1604c440452c460338003101a0701e52ed41d3e8f26a8b97038d6000d40c0242d13a558083a94b9af9cc3a24061000034864260523f096020282914b7522c3841ecbc52543e1bbd2852cc7a431c125294061000c04150588022008807d59e1d6c9012e41411d63c1cac6252bc20c20a817546c179d343b89438a45c422c4206b5dc1ca55c4c8eee151df61d04c1400452c52e1226d4939ec09f75afb02646e434212d7e0934c8095506d38ca099cc20a1500f58b00a85a0fa8f6e183cea9e4357ca6698e2df13cd411e12ae1a1d74cc5a846521d604c4460338003101a0701e0a94b5518c38e30bcdc98c089c3a3b9cda107ce80fbe6e1dfd143cb4f0505e401abe081bc6381b3fd0139ca40b92442fd2cf00661b65800294c506448055c5e05565c519d505885c422c4206b5dc1ca5082134183e03242f46a43047a431c1252948807d59e1d6ca81755343b80c0401411d63c1cad5c4c8eee151df61d09012e46252bc06100022000452c52e1226d4939ec09f75afb02646e434212d7e0934c8095506d38ca099cc20a1500f58b00a85a0fa8f6e183cea9e4357ca6698e2df13cd411e12ae1a1d74cc5a846521d604c4460338003101a0701e0a92852ccc0322b9207085750966581311000c40114b10287a044c6a03fc3404c45e04b6a21ade4c1a95acb49460b83e1bbc32054d28523cbe42fc4842ec1252948852b41851bcbc52a5d813f68a31e6ef4090e2c1845dcd01e6026e164332f120c5f3c0c55f40c4dda00ed6e00e645716fdd1f16f568139eae003141dfd964c5e9c3326b6088cb23e1d5ed1a12479c96e786cce3301dbc04599de7f00a9813e0704a807c54e511454076c1ee491c300c1c528dae8600c040061012e12241411d5d2128c9012e4028a1f2dd27e4c3e5c519e1a1d759e1d6e3c1cad5c4c8eee151df61d1604c4630377d9c0a5df80bdec6363ed493a221cedec09f75afb0260a557e0934c8095506d38ca099cc20a1500f58b00a85a0fa8f6e183cea9e4357ccc5a846521c60338003101a1881652bd48f6914752f90bf1210bb0494ab36841f822960e8323884b5000ac72936119098e8ade3b084350920a9248e992020442214ad479432054cbebf848276d4c1b9d281bd400192de2102a112f20494ab04dc223dec2404357805cc4402848f88341b85ea186a04a47a049c32054cbebf8305295fd11c152c1ad54c1b9dc61b5d281bd428529c5c48140c04000068623486426084350920a9248e992,
  0x1470c030714c9581311180ce000c4068bc533cc753d012309010d0881351100a12012f17a861a8fa1e8940c81532fafe0c14a59f06c54b06b56b06d55306e74a06f50a14cb03010008802a01f11712051b3380114b12404b90504758f072b571323bb85477d8741894af4b8489b524e7b14c125b9e299a63884cd4f0db94784ab86875dcc076f539445470c030714c967875b5813113316a1194877cb749f930f180ce000c4068bc1394cd0b83e1bc4661b65b0dc94c506448055c3a0c9a45254183e03cea8061000c04150588022000452c46cce23015849012e41411d63c1cad5c4c8eee151df61d096e78a6698e213353c36e51e12ae1a1d77301dbd4e51151c300c1c53259e1d6d604c44cc5a846521df2dd27e4c3c60338003101a2f04e0a14cb3cbc7edc8e80f6d08506d380f2d143cb6761b8cf0505e081bc6fc1b06401abca40ba7c04452cf00661b65800294c506434056c48055c5e0555a452547a431c6a43043242f4183e01252946c387ca8531c96e7b301dbd4e083c0852fd2e12249438a41e52ec6252bc1411d49012e45c422ca66984206b48807d4e2df13cd41f2dd27e4c3c4c140061000c04150588022000452c59e1d6e3c1caddc1ca55c4c8eee151df61d11e12ae1a1d75604c46d4939ec5304cc5a846521c60338003101a0714c90284804bc18052c5ea186a3e87a25032054cbebf9ac1b554c1b9d281bd428531434530c0c040003481a0c064260523f0bc0a8a8531cf2f1fb723a03db42141b4e03cb450f2d9d86e33c14178206f1bf06c19006af2902e9f01114b3c01986d96000a53148112015717815569149d1e90c71a90c10c90bd060f8018400301054162000d219098148fc2f02a2a04e0a14c51bc5b0dc8a40b83a960661b64121ad54c3aa4cff806100003481a190982f02a2a034530c5294b8284d94a0116105772027d378d37790d5fc4070571323bb85477d874581311000c47b14c10e7662b19ac6c387d3a52e4fa3c8a850846e52f422522c0e3584c1405c422c003501a0c024508085594bf48fc8e021c9a02d50402c66218b74c198400fe030090b4020381b94bd48fc8e021c9a02d50402c66218b74c1984ea52e422522cbc083d761dbdfee782a52d49438a5ec09f75afb02646e434212d862124f6e183cea97e0934c8095506d38ca099de4357cc20a1500f58b00a85a0fa9f2dd27e4c3c4c1408807d59e1d6ca6698e2df13cd411e12ae1a1d745c422c4206b5dc1ca4cc5a846521d5c4c8eee,
  0x12b145242f7da063e1e028be537c7ea58f048d5b0b00a4c3848055c5e05546a05447a053c36334c5a438061000c0419c0a5df80bdf5afb17e0934c8095506d38ca099de4357cc20a1500f58b00a85a0fa8f6e183ceaac6363c142f349053561a1d751807959007ad4007bd9e1d6d7206853606952e1226d4939c206de221cedec53044206b4bc083cec300c8a06a5dc1ca55c4c8eee151df61d01a5375604c45761dbccc5a8461dcdfee78a6403c260b050c35ddf2dd27e4c3c183e0022000452c46033800310962484e0a1285384f2f3a03db4203d34e03cb450f2dbf06c19006af0c81019f01114b3c00694dd050bcd571323bb85477d8742414d586875d5813114b8489b524e3316a1187737fb9e7cb749f930f7b14c129900f0982c1430d77060f8008800114b1180ce000c42584e0a200a29cc0f90e90e8be537ce0d0982c105b9e0a94dbcc076f539445470c030714c967875b3316a119487683ea430d770f3aa5813117cb749f930f008800114b1180ce000c40694dd04bd44479432054cbebf9ac1b554c1b9d281bd42853652e12246252bc142f34a64c6c2646e434534c1851bc0c040022000452c63c1cad5c4c8eee151df61d11e12aed4939ec53041ee493c36e4a807c46cce14e51159e1d6d1c300c1c5324bc533c9053561a1d74cc5a846521d604c4460338003101a0a94db534442e708810443a9b0da107ce80f6d08506d380f2d143cb6761b8cf0505e081bc6fc1b06401abca40ba7c04452cf00661b6580028ae4a3d4c506448055c5e0555a4535c7a431c6a43043242f4061000c041505881851bc02200003501a50892020640a84e260523f02853640e6f06d95100a5182e17abe0f86ef2fafe030100c90bd1a90c101840000d21902a1104e260520a2006914d73834260aac1612e5a0fa83cea8022000452c400311ca2414d511d4981a9ca669952e70e211c4245345460b88851d43a9601252ac061000c0401851bcda2414022003e1bbd28056c003501a84121d508ce210920202a0d064534e0a61839d5b089d98ac66721d534cb145b6a83597e83552680854100811b86612380b73800b34c00ad68838b5d038752838197e461fc6861df9865196a46535594bf17108b1305063998000d406942248080c02453454950486b54a015b933fe1394cd25b9e0504752404b9299a63884cd0184054162008800114b18f072b571323bb85477d8744784ab86875d4f0db9cc076f7cb749f930f1b33853944567875b3316a119487,
  0x10982c1430d77008800114b17cb749f930f571323bb85477d874581311180ce000c4258340a14ede32381b3c3a960a40b812e38661a9528056d2c041c4e53a406100142f3462128e7286110077c22538cec300c8a06a5dc1ca55c4c8eee151df61d01a5375604c459c0a5f5afb17e0934c8095506d38ca099de4357cc20a14b00a85a0fa8f6e183cea900f58cc5a8461dcdfee79f2dd27e4c3ca6403c260b050c35dc022000452c46033800310962494eb02832040418052c6a05447a053c4804bc5e04b4bea412c1ad54c1b9da4e39ac1b5428539c0c040142f349053561a1d748807d59e1d6c62128e7286110077c22538cec300c8a06a5dc1ca55c4c8eee151df61d01a5375604c459c0a5f5afb17e0934c8095506d38ca099de4357cc20a14b00a85a0fa8f6e183cea900f58cc5a8461dcdfee79f2dd27e4c3ca6403c260b050c35dc022000452c46033800310962484e53a4c8b4e94b91503fb1b94bd250e297026c170ac93688f95100a3c03f34e03f13a03ef450f2d2b928f1794e51fb8c8e06cf2914b71e90c71a90c10c81532fafe4a14e1060f8038d613050018400301054162050bcd2414d586875d4b8489b524e7b14c12201f567875b1081ad2f020f5d876f1884a39ca184401df0894e33b0c032281a9770729571323bb85477d8740694dd581311670297d6bec5f824d32025541b4e328267790d5f3082852c02a1683ea3db860f3aa403d63316a1187737fb9e7cb749f930f29900f0982c1430d77008800114b1180ce000c42589213828539c66b3e8f2e0839d1b94bd4ea1e250e294203d3170ac79006af4b0103038d6130504d7c50bc4070078ee02a984f046d8f072b2201f567875b1081ad060f81fb8c8e06cf2914b71884a39ca184401df670297d6bec5f824d32025541b4e328267790d5f3082852c02a1683ea3db860f3aa403d62f020f3b0c032281a97707290694dd5d876f4b8489b524e7b14c1050bcd571323bb85477d8742414d586875d3316a1187737cb749f930f5813110894e37fb9e29900f0982c1430d77008800114b1180ce000c425892138281794e54d0e0030d3002749a02d50402c57c02bf2c19c79a19374c1984ea418c5c425c8e51440e3584c1400452c41e3b80aa608807d59e1d6c4206b5220716221cedec5304bc083cec300c8a06a5dc1ca55c4c8eee151df61d01a5375604c45761dbccc5a8461dcdf2dd27e4c3c6033800313300894e3424e64091c38077f5c1e6dae8628a113f5d2128d921c7c5c,
  0x1fb02646e57e0934c8095506d38ca099de4357cc20a1500f58b00a85a0fa8f6e183ceaac6363ce8105d381065141074da107cae1004f0101c60338003104e11180879446c0666289853dd45b4c007d3800f1c686277c0c69b268f9fda035ddb86699902474e94b93e8f2d7079b1b94bd250e29a2844fd238ab9170ac76490c37300a1200e2f9566f14f31fb8c8e06cf2914b71e90c71a90c10c90bd060f80494f10d14ef1884a39ca184401df0894e32f020f1081ad2201f53b0c034b84892281a92414d55d876f050bcdb524e77072967875b86875d3316a1187737fb9e7e02f767029729900fd6bec0982c1430d77b18d8f3db860f3aa5f824d32025541b4e328267790d5f308285403d62c02a1683ea7cb749f930f571323bb85477d874581311038d6130500184003010008800114b17b14c10694dd180ce000c42594f503c784516df031a6d30b889a031664091d8c089c8e2aef6e19a75c1e6e6e1dfd3a52e4fa3ca8a113f7d0139c6e52f49438a5921c7d2442ec5c2b27da064dc09b144028da102cbe537d143cb4ae4a3e761b8c5ea1a5c519c0e3584c14150589f80bdec6363c4206b4183e03242f46a43047a431c06100e80fbd380fc4f00fcc7ee32381b3ca452dc1253c43453bc8807d59e1d6c0c040bc083d761dbd2e1226d4939ec5304142f349053561a1d7462128e7286110077cec300c8a06a5dc1ca55c4c8eee151df61d01a5375604c459c0a5f5afb17e0934c8095506d38ca099de4357cc20a14b00a85a0fa8f6e183cea900f58cc5a8461dcdf2dd27e4c3c22538dfee78a6403c260b050c35dc022000452c46033800310966f14f3028bea4032040418052c48055c5e05546a05447a053dac1b552c1ad54c1b9da4e3800b7896260640c0521381253c50a308013148011f2106e6b06d59f06c55306e70a14ed078ee02a982414d586875d4b8489b524e7b14c11884a39ca184401df0894e33b0c032281a9770729571323bb85477d8740694dd581311670297d6bec5f824d32025541b4e328267790d5f3082852c02a1683ea3db860f3aa403d63316a1187737fb9e7cb749f930f29900f0982c1430d77008800114b1180ce000c42583453bec0820e0b2914b7050bcd2414d586875d4b8489b524e7b14c12f020f5d876f1884a39ca184401df0894e3670297d6bec5f824d32025541b4e328267790d5f3082852c02a1683ea3db860f3aa403d66901592494eb06010d4b01071081ad3b0c032281a90694dd7707293316a1187737fb9e29900f,
  0x1b507459403e9a001c53d14ff0e01df2201f57b14c10694dd000c405846441841f866020246d81c54242e0f86ef1986d94a01575300e51150501840008800114b12594f5000c413828191507128c521b3e72861d0e3110077c22540d8c089d220714ec300c88104442e70bcdc88a06a43a3cbe6e1dfe221ceddc1ca5080f4d381064e8105ccc5aa401abe761b8cf0505e081bc4461e0d143cb4a40bbd0139c5ea186ace8661a947a8c92442fd4c55a7c04452cf018053f55c4c8eee151df61d1604c465c519c06101ec53041a53749653d4a64c6d9c34f6b44a642c28906d381453e4183e0022000452c432540460338003104e0a064511505029616512f9a1934ea418c5c425c8e51440e3584c1400452c41e3b80aa601a53740031008090303d178089503189f680d766201f53a37dea0511da20f06ce191663b45dcfa3c9aa4ced742e7c6e42449438a49a2aa48e2adc5c2b147edc80853fe64091c38077d2207144206b48807d4ec300c8a06a75c1e6dae862221ceddc1ca59e1d6e8a113f4cc5a9921c7e081bc446578a40b9d2128c661b645242f7da063d4c6a15c4c8eee151df61d1604c440e3584c14006101ec53041a53749653d4a64c6d9c34f6b44a642c289f80bdf5afb02646e57e0934c8095506d38ca099de4357cc20a1500f58b00a85a0fa8f6e183ceaac6363c183e0022000452c460338003104e0a0640c9501424c5c425c1e3b80aa60001e030090f4089b60214ff1b6d8a53dd460ba084e7c3e1bbd2853ec061000c0409653d41453e4183e0022000452c4003104e0a064511808794fd0285e05546a05447a053c00b784e111446021e4a14fb3b0e1203662c03dc6c0325e9d1a0df011a872c19c4204c9d96280ceaef0b4424e64091c38077d8c3abcbc083c4206b4e2df0ec300f5c1e75aefc9761dc48a06a4e45a9dc4cac562f361011d5f2dd27e4c3d5c4c8eee151df61d1604c465c519c1e3b80aa601a5374a64c6c022000452c59c34f6b44a642c289f80bdf5afb02646e57e0934c8095506d38ca099de4357cc20a1500f58b00a85a0fa8f6e183ceaac6363c60338003104e0514f90714ec3aecf4425c204c9cb4424e64117c38e3276f1c76381b2dd813f462128e221d168a31e7e72578e45a85693a8c1224fc1adc88104442e70bcdcbda062dac049e7c044c3a9b200029080f4c5e040c6a03fe401a9e4c1a977a46a5c519c0c04150589ec53041e3b80aa601a5374a64c6c022000452c59c34f6b44a642c289f80bdf5a,
  0x1357cc20a1500f58b00a85a0fa8f6e183ceaac6363c183e062128e72578e45a856503464541c9653d59c34f6b44a642c28906d38a64c6c0c04006100022000452c41453e41a537448545460338003104e0a03a8015210287a2a94322aa40c04002200003504e11180a29cc5103a26951f32ec9a035400fe0b4a82427a7d51d30ed8c089c8807d4ec0c87ee70e211c42454646e545c0e35a30377e3c9e9761dc5f2dd27e4c3e6e1e065c519d9e1d95604c45ca12e64042ddd813f68a31e7df80bdf5afb02646e57e0934c80954ca099de4357cc20a1500f58b00a85a0fa8f6e183ceaac6363c183e062128e72578e45a856503464541c9653d59c34f6b44a642c28906d38a64c6c1a53740c04006100022000452c41453e460338003104e0a0b44c151b0029c1725961685b845add3f010dd8f007c92082ca807c64e3c2d1c300d860d741c089e5f9189d7819ecfa3c8941875604c440e3580452c41e3b80aa601a53766201f5e9d0334003114ead9842d1303a824546471df693299db445f5182e0e8320f8ccd38849f0701df6d86a108864d0694dd8c0ddf060f86bbf21884a39c95e670d3dad12997604fda28c79f7e02f7d6bec0991b95f824d320255328267790d5f308285403d62c02a1683ea3db860f3aab18d8f2f90bf5a04e7c507833916a15940d1915072594f50b0a241b4e97146729931b0514f901840008800114b1b3809d7c0c0eb180ce000c4138284c06e545d5132380c73800f17c0c69bdb86693e8f225061fda15115d03bd5b03b94c2e298ed177688ba16a8b97529b41b950f17150d08950b24820b470c03150eb707150963043b99045f9c2c6fd9dbc71d10b9c2f3725182e0ea6c82139f0f86ef3688f93c08f53a08f1f681937f4416d4a0157de91a038d613050541625d87717cb749f930f6bbf26787655813117284b95a04e7c507839714672b83c74e03cb4503cf4203d39010b77604fda28c79f7e02f7d6bec0991b95f824d320255328267790d5f308285403d62c02a1683ea3db860f3aab18d8f060f81884a39c95e3916a15940d1915072594f5670d3dad12990b0a241b4e29931b0301001840008800114b10514f90694dd180ce000c413828121515031616516c00908b4e13f8a832c544e0a61835d7e8355639980114b10694dd000c43ea4fb9e60fad3ed76854440d58590012380877a746830c14bd98862d003f8020245e0382d06e543c671db80c93abbc000d40206c17150d4c9cb4424c001e008091b608022542c4893f06b9,
  0x15034cc5a84654bc2c28906d380c040a64c6c022000452c4bebf832054d281bd49653d47a8c848f892c1ad42854b41453e460338003104e11153138e45eaf9fd11c1462128d68139e7257b141e0e5c519c061000c040a64c6c022000452c59c34f6b44a642c28906d38bebf83e1bbd281bd49653d448f892c1ad42854b41453e4003104e1104654bc6cb6b01275182e8000a7438c0f8ccd0c911b38849f0701df08932715152b2d15290e95231215151790c31a90c12f90bf7604fd1884a35a04e7678765a28c79f9c95e6bbf2c507833916a15940d7284b9191507060f858131197146701840030102594f529931b008800114b1670d3dad12990b0a28c0ddf7e02f7d6bec0991b95f824d32025541b4e328267790d5f308285403d62c02a1683ea3db860f3aab18d8f0514f9180ce000c41382854b7242100bb1b150dd306612f020f2201f53b0ebb0f3aade91a971467078ee02a980694dd5d87713916a7cb749f930f3abbc0114b1180ce000c4331841705454ac0f59095277c0c69b3e8f225061fda15116883c15d03bd529b498ed1776a933b5b0b9b1b948d02109399045f0e38c9dbc71d8e06cb5182e0f86cdf6818f6b012b8780a1e95254c151b038d6130502f90bf5a04e7c507839714671a90c11790c312151510b9c0e95239010b77604fda28c79f7e02f7d6bec0991b95f824d320255328267790d5f308285403d62c02a1683ea3db860f3aab18d8f060f81884a39c95e3916a15940d1915072594f5670d3dad12990b0a241b4e29931b0694dd0301001840008800114b10514f9180ce000c4138282d152903ce16511df031a6ece191400fe0b4a80226da426a1527424e64117c38e3276f1c76381b2cbcdc9460ba084e7c3e1b37da062d28053dac049c06100022000452c41a53749653d40031028149921f8242d07a54943f343a66c8e06cb36841f5182e82139f0f86cd3a08d54a014f6b0127801521541622b83c74e03cb4503cf4203d39010b77604fda28c79f7e02f7d6bec0991b95f824d320255328267790d5f308285403d62c02a1683ea3db860f3aab18d8f060f81884a39c95e3916a15940d1915072594f5670d3dad12990b0a241b4e29931b0301001840008800114b10514f90694dd180ce000c4138280e9523115ef29b276f1c75460b8f0238ce8237fda063c3e43861e02950588be42fd68139f141e0e5c519c6a43045e430cae0f1d380f2d140f3d080f4e4042ddd813f68a31e7df80bdf5afb02646e57e0934c80954ca099de4,
  0x11986a51095332281a905047588873b7707298f072b67875bb18d8f3db860f3aa5f824d32025541b4e328267790d5f308285403d62c02a1571323bb85477d87458131113050018407b14c102a982594f50ea58298e1704953d4b01070694dd139537683ea008800114b1000c41595476e0b201555e010618012dda011d6e011564511dbd17a5d1d1715d3f1766f0550dde7f26842bc1e3b8004d06cab88408154555070e0c9f120c8cb2012564010e475172dd3d17242e0001e3b8004d06cab884082f0550d2c5cf08e7d242808f750029c0824e1b0e89bc142d28e815505344100b14c009d3800835f007fd30661e6864d98862d23945126944f3a94210e1423038d613050000d4090303d0082d1562a153f4bee184bffa0061520047d643e54b2e6054c920171c5e7c1b148452aec213bd2e12249050368811e36d4938cc5a84654eda110b9d5e399ca6403f5afb06c0565962814264085281bd7b2361cf6e183cea97e0934c809542c28906d38ca099de4357cc20a1500f58b00a85a0fa80c041ec53041e3b80aa601a53749653d4da24144e54dc022000452c41854e460338003101254f4ec38b019508013184816ff687256b06d57f447057604fd1884a35a04e7a28c79f9c95ec50783971467078ee02a980694dd658a051b01594a06f513953729900f008800114b16702977e02f7d6bec0990212594f50b0a25f824d32025541b4e328267790d5f308285403d62c02a1683ea3db860f3aab18d8f000c40484654ec9dd0a0f8420915008800114b1139537000c4061539829860ea5aa391fa331a20d6d740d5e5d519ff681894fa3c89419d5e9f54753002b7e654d4887d16c348c8e4c25b606642204d57805ce52088fda1c95ac1b55fd11c151c300c543addd813f462128d68139c1c408e8a31e7e7257a6e1e07141e0ce45a8561ca52a54cce0315c5cef14a6d02404346e50940805744454c52c1ad5281bd42854b41453e5f80bdd9c34f75afb0a64c6eb44a642646e6c6363cf6e183cea97e0934c809542c28906d38ca099de4357cc20a1500f58b00a85a0fab101c15c4c8eee151df61d1604c477a46a5c519c0e3584c1418e660022000452c49653d460338003104e54de0a7e83bb61837d6a837968835b5d035798e469fd20649da06257c0c0ebb3809d3e8f2a81342506512680b54100b15f00af038d61305063998529b45b0d23173bc000d43a842e10200e26490830f99535300c1c06b48a06a5604c441a537400310424a95330285ea186a3e94c1b9c90,
  0x14b23e9abbe191ea3f2e02627aed079372a2aa316e842d8911ee2e874398c01d87091aea2e1123794820916002de058441183e6021ee802c55752ff8092fbe802df4803eacb343f9941299a1690e40028b57b462cb98590f95078ee0285d531360000922a0201e0f6556d2ff8092fb590f952cb9857b460286054803e213c215136706825b07ba4e802df881437acb341a0b63f9941c8a21299a169ce9f8a07c8775cc04cf5d820d299a638b7c4f350478dbf31360180ce00008070921182a5564de331360001c8f20b6531360003ac55554772414d50c01f7868765611509990247d7079d7e02f7109533d6bec77132b0982618404752606a52f3725182e3b0c0382139f0f86ef22820b4a015b1b15511884a39c95e6bbf26715495a04e7c507835d87713916a159547298e170ea5804953d0615394b01071395372594f50694dd01840008800114b1971467571323bb85477d8747cb742c02a13082853282673202555f824d5813119f930f0f3aa3db86b18d8f683ea403d6790d5f41b4e180ce000c4d80dfd5182e470c030f86f107020f6c37202154f21154515154b6e116b5813110184002a982594f50ea58298e1704953d4b01070694dd139537683ea008800114b15d87713916a1595477cb749f930f180ce000c41b15511044305166761b8c38e318c10ec905356381b3e70b1c061a1d94a40b98407c46637f51c300c1c55345c5435604c44061003a96168139f141e0e5c519c62128e725799c5524e45a856551ca6385c1254f52c041da0fa8022000452c54c3a884551454552db845ac0aa601a53744e54dc60338003106c02154f0b83e1b8c661b6c9053561a1d958a10458407d430516438077d8c3abce2df1604c465c519c061003a9601254f4022000452c5aefc99c5524e45a856551d4c3a84e54dc6033800310a8020b407154d4d08e029ce0034d7c033d3002749a03550403479a1935e9d1a0cea3c9a8388c38077c5c5434bc083d8c3abce2df09438cdac04ccec3aec3ceab7a46a5c519c0e3584c1403a9601254f44e54dc022000452c5761dc5f2dd27e4c3daefc99c5524e45a856551c60338003106c15154b0a5458415c525195c80a5d00f5b101c15c4c8eee151df61d1604c44003119c55244fd648721a28c79b9db445fbd02476d94ff0e01df6ba187e02f7670297d6bec7484a30982951486cd6b01330815452a153f250e2917150d6e116b24815b2f3726906ef8206f14881c52201f52902e3b0c03,
  0x14e749c668b03d9dc8f23ac5554c4d8000b7816110462583e6021e2a0544804a2b2526805855ac742e20c5822a681e6869ea242887300a0d3fe1ea321ab3a4b23e9f2da120d27261ba14a143f0121c90413f90431611cd323760f2543410e318e552c0f672719a30adc32ad60b15671e156503010060f827b742a87737fb9e299a638b7c4f350478dbf2fafe0c81534a2c02902e19b060184000880010dc039d40a955982296723c8eb155531360180ce000080707e24828118a80815690285ea186ace834ff848f887a8c94cae27cb692c8f8647a8fcb80989e9ca8aa8c5ba10b60ba1d0e6300761c0b8448de5208245800b7816110460f9808781a0b15670285ea1834047c6ace848f887a8c94cae27cb692c8f8647a8fcb80989e9ca8aa8c5ba10b613e4becba1d0e6300761c3a05574b8448de520824584a558e185585643e540c040a6698e2df13cd411e36fc183e0bebf832054d28b00a40b866c180610002200043700e7502a556608a581e3b80a175460338000201c1f8920a0462a0201e156507d430c799e1d958ab11ca12e46479868831f61d160557c5c322424aa8f4fd15297a50b9848349c986e924a0852850fc048724104fe410c584734c8dd83c95102550d0438c63954b03d9c9c668c2b70cab589edd0aa1dcdfee78a6698e2df13cd411e36fcbebf832054d28b00a40b866c180610002200043700e7502a556608a59c8f23ac5554c4d8060338000201c1f8920a046508201e24e12956307d430c799e1d958ab11ca12e46479868831f61d160557c5c3ff4f4fd250b9848349c986e924a0852850fc048724104fe410c584734c8dd83c95102550d0438c63954b03d9c9c668c2b70cab582c55752016942e001b8173d9616869e4bfdd3d012dd9700cdd8f009c0c040183e09edd0aa1dcdfee78a6698e2df13cd411e36fcbebf832054d28b00a40b866c180610002200043700e7502a556608a595ed18b2e61643e541e3b80a1755c8f23ac5554c4d8060338000201c1f8920a0462a0201e2185587888e33e7181310e12f7138c3d17a880c01f7191ea612a672a2a0184003010299a638b7c4f350478dbf060f84b23e092aa54a5e180ce000d20707e248281183e6021e50820938625a014511222d160557c0a0d018517a861ab3a123e21ea32805c70f532b89f2da,
  0x13d957b1c8a200008338927011c04a00a29cc510a80b026560557d191e62902e19b060a9be16138b3d957b211577322742c23430a5632a4831982acb341a0b63f9941c8a21299a169ce9f8a07c9c43316a119575060f8018400301000880010dc039d45d820d82296723c831360180ce000080707e2482855fefe4a2c06000a0c811712011b9f2da0d157917a861a8fa1e894532b83f012002de6c09211106793b22a026258900f957d556c544d9c1a096c00249062a0f655ed2ff590f952cb988092fb151003e8018506bfe48011f805c70f4b23e9f2da9abc4261ba3f01257b46078ee0285d500092419e4ec8a80f834099579479448046c32054cbebf94cae27cb6928b00a40b866c1864798fc0482a6f8584e2cf6f08061000c040183e002200043700e750c89d1c8f2000021b00a1e46810cfb8c1930848455dd1e5123e2532b84b23e191ea2627a72a2a842d82e8741d8702e112209161295732a156f0c81532fafe4a2c02902e19b060a95590184003010299a638b7c4f350478dbf82296060f800880010dc039d4180ce000080707e248281195756e8584f3c7289b101c15cb623c9e8148fa4cf894447954cae06455c4c8dd83c9517e0ac4d0438c63954b03d9c9c668c2b70cab580c04002200043700e7509edd0aa1dcdfee79c8f23ac5554c4d800002016110462583e6021e2104a55cfec099e63dbc21a20c7d8745822a869ea323763410e723c80001611884fb8c19168c21b88ac1915717a8900aadca8a858fb0ba1d0f60a8cb8831a055b61217ce4a10cfce893936be0c94c8dda47717443c9517e0ac4d043aae00196168cc63954b03d9c9c668c2b70cab5a9c3a3668411d8d00942c559d3e400f4a401478c902055a41e3b80a17540c040183e09edd0aa1dcdfee78a6698e2df13cd411e36fcbebf832054d28b00a40b866c180610002200043700e7502a556608a59c8f23ac5554c4d8060338000201c1f8920a0462a156f30f434047c5ea212c8fa7cb6848349c64798986e924a0852850fc048724104fe410c5855ac061000c040183e0d0439025509c668c4d8000348160a0462583e6021e2a0544804a2b25268156d0286ace85e05fe7cb6a0171c3c48f887a8c8fcb826aef92c8fa8c5bbb41e4c989e8e6302447ba10b60dea1246e40761c03438f5e40fbb24eb48249b620,
  0x13f2e02627a72a2aa316e842d8030101d87020916398c0379482e8742e112000d2058121104e0b04656451c9191ea3f2e02bb962627a72a2aa316e061011842d83916a159c42a8a02798243138b09958d2e8743dbc232274398c01d8702c23430a5632a482e1121a0b637948209161c8a21295892a15871209db1789d91a89d51e89d30d09dd0a157f4204230301000880010dc039d45d820d299a638b7c4f350478dbf3a04174e041945041d36841f82296180ce723c8000080707e24958f0e7662b19ad3a52e4fa3c894507c22562e64066f201c9d92ca9e240ec5cef0cc5a888052522048442042c6e509446404444028326a0be0445bc1b964c1acea21b0c64798986e8fc0484c1400c04002200043700e750a6698e2df13cd411e36fc72288fe650682d8761c0824584a562460338000201c2481213a00a29cc5108409958d421c543b4c78418c5cef0043700e7500002092210ea090f40c1b608958b517c5cef18c46546e509438471c88052524a08444844524ea5bc1b945856146455c42a5564e45a856710aa2803c9517ec29025509e738c6428d0438b03d9c9c668c2b70cab5802200043700e751760834a6698e2df13cd411e36fc6033bac5554c4d80000201c2481213a00a29cc510841295891b954c0524643fb43051645cef1ae07758c46546e509438471d24a08444844524ea45856142a5564e45a856710aa2803c951025509e738c64289c6682c560c02200043700e751760834a6698e2df13cd411e36fc34277460338c4d80000201c249c004a00a29cc510a8561c9d16000a2bb962627a0c92b9061011842d8911ee1d87091b9020a26ec93ad41902503010299a638b7c4f350478dbf2719a2c0f67723c8eb155531360180ce000d20701213a00a29cc5104a2b0462585856151c9191ea3f2e02bb962627a72a2aa316e061011842d83916a159c42a8a02798243138b0995812e87432274398c01d8703d957b2c23430a5632a482e1121a0b637948209161c8a20301000880010dc039d4299a638b7c4f350478dbf22820b5d820d0d09dd180ce723c80000807092700128028a731442a02c560d13f559421173bcbd818722014910810b1b94251100a0c9a82f811180547156f06e59306b3a886c39abc4191e6261ba3f0124d7cddb0301000880010dc039d40d09dd078ee0285d53f9941a0b6acb34,
  0x12e1121295a1180ce000080707e0a2201195a31d0b8831608a9a079a1a7a890a21cc0287a8c86ace92c8fa7cb6848349c34056432054cbebf8986e8fc04928b00724104fe410ca40b8e45a866c18567102a6f852850aa280584e2cf6f70c8dd89e738c6428d0438b03d9c9c668c2b70cab58061000c041760834a6698e2df13cd411e36fe08a5892563c183e002200043700e75060339c8f23ac5554c4d80000201c1f8281295a10aada055dc6455c4fe410ce45a856710aa280584e2c3c950c8dd97ec28f638d49e738c6428d0438b03d9c9c668c2b70cab582c567412566ef0565c205515b845ac1a387d760834a6698e2df13cd411e36fe08a581e3b80a179c92563c60339c8f23ac5554c4d80000201c1f884567cc9b2fafe12011b0c81171e8944a2c09f2da532b82902e191ea3f2e019b0672a2aa316e0a94373916a159c42a8a0279822e8744315773dbc2398c02c23430a5632a482e1121a0b6379483f9941c8a201840030105d820d299a638b7c4f350478dbf060f800880010dc039d4180ce00008071b0210280b159d1f0865c19c8090085272ab062471c224ce64c1acf201c9c986e992ca9e240ec584dfdf2710cc5a8464044f6f08761c0682d882458722884a5665fee782a51bc44565434281402201760834a6698e2df13cd411e36fc5c5434043700e7501a387c1e3b80a179ef0565dc8f2060338000201c1b08404959b1acc986e92c4ce4724107201c9c38471ce45a992ca8524ea456710584e2caa280c8dd8f638d5e2a909e738c6428d0438b03d9c9c668c2b70cab5802201760834a6698e2df13cd411e36fc5c5434043700e750205515b845ac1a387c1e3b80a179c445654342816f0565c60339c8f23ac5554c4d80000201c1b0840484a5664051de1b876fc5df76b4493d432d39f7a87d0c9fc48323c3831baf831986003f59003791d45cb91545b974745b70b800578e67779fcd0b589a10af2c8f270815456e116b068e1f078ee0285e70006c212f0565d38b3dbdc323760992113190a3410e2c0f672719a30adc32ad60b1593723c8eb155531360000080706c210121104e565796af120d261ba16138b319829f8a07c9c43316a1195913dbc2322742c23430a5632a481a0b61c8a200880010dc039d45d820d299a638b7c4f350478dbf723c8180ce0000807084048441382c564d1c92bb96191ea,
  0x15a8c89d0b08d0c2958ca9204656a4682d8722884a56cc02200043700e751760835c8f2060338000201c048582a06c56d538b3dbdc323763190a3410e2c0f672719a30adc32ad6723c8eb155531360000081606c1295b3281f27109e738cc5a89c668468a82c2d8ba1d1a0798b8402c60338c4d800053812191ca0995b11d1608a8b8402e1a7a89056b4986e8724104e45ab201c9c567105285192ca924a08aa280584e2cf6f70c8dd9e2a91025509e738c6428d0438b03d9c9c668c2b70cab582c56ac28569c84567c5c543492563c043700e751760834a6698e2df13cd411e36fc60339c8f23ac5554c4d80000201c1f95af423438471c42042e64066c6e509488052444412dbc1b940c04002200043700e75032063e4c1acc00020b42a0125a062f68142415ad423438508d22048442042e64066c6e5094880524445064343a9bc1b96a21b0e4c1acda4e3b201c9c64798fc048986e82a6f992ca9e240ec584e2cf6f70c660a7e281f2710cc5a84656a4c89d0b08d0c2958ca920682d8fe650722880c04002201760834a6698e2df13cd411e36fc5c543492563c043700e75084567c48276c28569cda107e08a59c8f2060338000201c1f82c56ac6e5191ea530ea72a2a139591061011299a638b7c4f350478dbf1d870209162e8742e112180ce000d2070a80482c1195a90285ea186ace848f887a8c834056432054cbebf94cae27cb692c8f928b00a40b866c182a133c647a8fcb80989e9fe1dd5ca8aa8c5ba10b60e45a856710aa2809e6090cf72205694ba1d0e6300761c0b8448de520824584a5684183e0061000c04002200043700e751760834a6698e2df13cd411e36fe08a5892563c60338000201c1f828569c0a17a861ab3a123e21ea320d01590c81532fafe532b89f2da4b23e4a2c02902e19b06191e63f012261ba0a9be16138b319829f8a07c9c43316a1195a301840030105d820d8229624958f060f800880010dc039d43f99432a4830a562c2341c8a2322741a0b61295a1723c8180ce000080707e0a22056940a0d01592fafe17a861ab3a123e20c81011ea324a2c0532b89f2da4b23e2902e191ea3f2e02627a19b0672a2aa316e842d80a943701840030105d820d299a638b7c4f350478dbf8229624958f060f800880010dc039d41d87020916398c0379482e874,
  0x1bb852f2197a0f2543190a3916a159c42a8a0279ce2719a5d820d723c8180ce31360eb155500008070a812864573cbe343966c1894413a08d58015cb1a942f42040d36840b3c041b4513af9d86db6c3065182e0f956b0c9a82f956018400301054162080f6dbb852f2197a32ad6323763410e30adc2bb962627a842d81d87020926d099e61a20c7d8745822a869ea2719a2c0f67060f80d2580088031360eb1555723c8000d40583a0a0a82584a2b04619252069204b94c57351377300a3a136b03010060f80d2582f9560c9a81200e000d20e828af14c43a6f27028a8015cb5a8461dd456710aa2809e7389c6682c571f30133d760834a6698e2df13cd411e36fc60338c4d80000201c2a02a572555b06825b1b3dc15028d88138b4013cf099be0f254319829f8a07c9c43316a1195c5322742c23430a5632a481a0b61c8a25d820d723c8180ce00008070a80a82c571d82433dc9f8a08814372495597c87755d820dcc04cf299a638b7c4f350478dbf180ce000080702a0b04657155b30990212495590b15913916a1595c10d0ea2115bf25b8e4a15bd6f06e51915bb0609df00880010dc039d4299a638b7c4f350478dbf1f95af180ce0000807012570dbe319821615b79f8a012940d7c9c45d820d299a638b7c4f350478dbf1915bb25b8e4a15bd2115bf180ce00008070121595c14e2c266f8f6f08c89d0b08d0c2958ca920c6608682d87228a7e2804a5035f2710cc5a84655646c566d760834a6698e2df13cd411e36fc6456ec96e392856f5c8f2060338000201c0488456fd59b24815b2a14811394190301000880010dc039d40609df1f95af1200e6f06e51915bb00008070124a15bd5a8567104655c4aa2803c9517ec289e738c6428d0438b03d9c9c668c2b70cab582c564c341b8a856e54c1b9d760834a6698e2df13cd411e36fc18277c7e56bc6033bac5554c4d80000201c0486456ed5850d015b1201576938e0a95593916a159c42a8a00f254279ce3190a2719a0b15b71b15b500880010dc039d41e8941a8fa17a865306e70995b1869ea299a638b7c4f350478dbf5d820d180ce313600000807012190a856e4a0279827c9c443138b3316a322743d957b2c23430a5632a481195a91a0b61c8a200880010dc039d45d820d1b15b5723c8180ce0000807012160a80b15b74e2cf6f70c660a7e281f2710cc,
  0x10815d12bb962615dd1915cf3916a159c42a8a00f2543237640954279ce3190a3410e2c0f672719a30adc32ad60184003010541625d820d299a638b7c4f350478dbf060f80d2580495c31f95af00880010dc039d4078ee0285d50a95c9723c8180ceeb15553136000008070a81295e105fdcc02a0171c347a4da674d111e40ff00c040183e00220000350160a04e259004318087944198f61c81ae82c210a8a4215df6e8584f3c7289b101c15cb623c9e8c6428c8dd8d0439c8f20000585a2b0462615dd0f93e400e204e2c6c56cc26048fea13a6301ec5bad4b812e5764205744a6698e2df13cd411e36fc7e56bc183e012570c02200043700e7501e3b80a1754cab58c2b70b03d9cc8dd8d04383c950c6428e45a856710aa2809e7389c66976083464573dc8f2060338c4d83ac5554000201c2a04a6f014576d36d700bd9a8811b933e25100a0c81532fafe4a3565182e0f95d788138b0995d51e3244f90031b15d30184003010299a638b7c4f350478dbf0d258078ee0285d50a95c9323763410e3916a159c42a8a0279ce5d820d1e8941a8fa17a860815d11915cf0f2543190a2c0f672719a30adc32ad6060f80495c300880010dc039d41f95af723c831360eb1555180ce00008070a8129bc0512e57652e1453ba423fc3683d13a366123e262ac454a5e4b23e2b928f1a8fa060f80d25817a861e894000d20e828258906f0140683e575e5e903fc2913ff700b01493a93f9043492826494431a02ab1c8261060f80d2583410e4095478aa42719a31360000d20583a0a04a118900501a0995d546058030fc329c0a44ffc66463448349c524ea524a0992510c5856cc061000c041025509c668ae4a3c6a3e8183e03496012570c7e56bc5ea187a25002200043700e750c4d80000201c2584a241bc0512e1b15d3492c584734c8dd8d0439c8f20000e844fb8c19168c212b0900502057466c4504414e03dd423fc3683d13c3403a3669d3c711942e654a5e2902e1986d95315cd3f2e0a316e2bb969abbe398c02627aed079337a84842d8911ee7903e1d87091b904f90031e3248482cd20926dec93ad080f6d88138b1b15b3099e61a20c7d8745822a869ea0184054162299a638b7c4f350478dbf060f80d2580495c31f95af00880010dc039d4078ee0285d50a95c932ad630adc2c0f6740954323763410e,
  0x12a14c0815f7180e4e50d17a0111ce89393674f1c36be0c9601505fe4771745cc02aae0007a8c996168d2cfc268411d8d009640ff29c3a374a401478497c1e3b80a17546c108400b7844138a86021e51014b0a7619a0842120a285457d46039394345e804473a24e4d9d3c70daf8325805417f91dc5d17300aab8001ea326585a34b3f09a10476340251a942fa70e8d903fcd290054f90031e125f0815f11b04217015ef3c041b6c306453ba4e04053a04035182e6293870fab82bb969abbe191ea3f2e02627aed079372a2aa316e842d83916a159c42a8a0279824302001840030105d820d299a638b7c4f350478dbf060f80d2580495c31f95af00880010dc039d4078ee0285d50a95c91c8a21d87020916398c037948322741a0b62e8742e112911ee91aea1295e12f9560c9a81200e180ce00008070a85305857cd5e99caac0e15eb188542627a842d8093d44aa661d870209163d01c7a0378398c0379480c01f7612a63c041b6c3060a95c91715ed191ea72a2a3916a159c42a8a02798243020322741a0b61c8a25d820d2e8742e1121295e1299a638b7c4f350478dbf060f80495c3008801f95af010dc039d4180ce00008070a81606643850e543b4920815f10285e05fc6acea0171c367c1aee74d110efc0f8c7a8caf29b12c2f640c04150588be558326a048038aee58f0106db0c18003483a1104e2594c0512e242c21990e143950ed7015ef2b1dcc5154003503a110a82405c57b43853ec60af286555d03575b089df980afda062121d4cff41008168837b6a8379c68c8dd20641618c8b55943b529b41e0f951bbe89392f71305063998010dc078ee0285d5268fff039d4000082a0424888808038248b457ac7c219706729a40105b6b81dd1695e3723c80001c0b058119d20895e90fe5c09b1d0e00dac100610150588aee58183e034960003483a0a0141990e143950ed43a42018854556c544d9c1a096c6cf72204e2cca920c2958b08d1c8f2000020a8418c1d1610c0813cf0f0c7b409543190a3410e1c8a23f994322741a0b6723c80002c1605a578c17f805c70d7300a9d344431ea32bca6c4b0bd94215df1a942f3f2e0a316e093d49abbe398c04aa66ed079337a841d870911ee7903e20a2691b90a782dd1e3244f90033c041b419025ec93ad88138b1b15b36c30609a82453ba4e04053a04035182e5a11996293870fab81200e0c9a82f9566f15db,
  0x100008070a809884b02081085a4bf892580580029c02e1cda0f4448f88320405381015529792c8f98ab100c04150588ae4a3c6a3e8183e0349605ea187a250003481c5383a0a0a82582c6f0142403e2a0a07c9c4279823316a4302011ad8099ba8f27a5d820d299a638b7c4f350478dbf1c8a21d87020916322741a0b61295e1180ce00008070a82616034bfe024befa0111d200f9d643e54b2e6054c9274f1c4650b981a575e6af10fc048986e8584dfdf2710cc5a84657fcf655ed5ed181e3b80a1755fee78a6698e2df13cd411e36fc72288fe652b2cd0761c082458e6300de522447ba46ba8641b8d8a1035c8f2060338003481c5383a0a0a82582c6f1080f89258052ff8092fbe804474803e7590f952cb98153249d3c711942e60695d79abbe3f2e02627aed0793a316e842d81906e362840d57b46078ee0285d5000d20583a0a0a82595c7b1a116f1080f8921195ff5a8564e2446b60266ea3c9e814fc240ff07857ee4cf8944028f655ec32054cbebf86c108528d59b0c180c040183e03496012570c7e56bc02200043700e751fee782a5724a6698e2df13cd411e36fc72288761c0824584a57847a2506a3e85ea194c57e460338000201c2a1081995fd4bfe024befa0111d200f9e74f1c36501aee6af10fc0485857c5643e54b2e6054c90fe652b2cd04a5784e8100d38101514ee98a10355ed186c1085b0c181e3b80a1756a2046e01506054402832054c349607e56bc5ea18183e012570cbebf928d582a57246a3e87a2514c57e40c04002200043700e750000201c2a1081987857ed42fa295f54f90030815f71b04213c041b7015ef6c306453ba4e04053a04035182e2bb966293870fab89abc43f012261ba191e61615f31200e0c9a82f9560184003010060f80d2580495c31f95af00880010dc039d4078ee0285d50a95c91c8a23f9941a0b6acb341295e100008070a85315f91f19ca68865c1ae07750085272ab03857ac621505c57b4f0106c6c1085c057bd14ee9381014e8100d8a4e1e6af12b2cd0fc048fe651b0c19460b83eae00610024f512a998761c082458f4071e80de0e6300de5203007dd84a98e45a856f91584695a3ad4986e87228b14df9684664647985857cc682d82a5724183e03496012570c7e56bc02200043700e750a6698e2df13cd411e36fcba1d0b84484a578460338000201c,
  0x11616154dc4e02a6c9a47fc8e316d7808968a0286efa05cec2b630d45e0466400f442250d714df8e84daea21adef250b5684635bc47952e582c48f887a8c84c1400c040a6698e2df13cd411e36fcaee58183e0349600220004371584695a8d83007dd84a98e45a8ba1d0b8831a0f089c668f0106db0c18bebf832054d28d5860338c4d8000a181c0e828210141984a248f6150cc258901090edbdac2931613f894450b52cfc0da102e40ff276103caee58183e03496000348160e828210141985a3d81a1190ed43a5808790858458875ac87e07a1b182e9d70245b8bec9906970f2b098ec3c340bf64ea0ade91a5d08ab7e88a95b08a7970c35e11349b822568837b6a83794c009da28c4fbc537e630ea5d20641e6863f76071b5a06fb55aee9dbc4599c2c435592208e92852c8f2794925908160d4100b15f00af238c5bd30cfd529b41bbe8268fff0895e94813b99caac9406bb18a0e4508f74e08f3a8811b5111e5170c8953138702a6006bfc1b04219d840f07884d54bf03a0b7b700bd993160b0c81532fafe9abbea482390c01f7191ea3d01c73f2e0093d44a356ed0793852c791612a672a2aa0378a316e4aa660a94373916a159c42a8a02798243138b3c041b911ee2e8743dbc232274398c01d8702c23430a5632a486c159d91aea2e1121a0b637948209161c8a213050639980184003010541625d820d299a638b7c4f350478dbf2a16092bb96060f80d2580495c31f95af00880010dc039d4723c8180ce0000807014198580b160f4d0e0337d3001f66436b1a323556490586322c4c140043708e316c0e7500002042488922d038858ea21d74408160d57bd08103d14ee9381014e84dad8a1b75bc326c48f887a8c80c040bebf832054d28d58003483a1104e21014198964b890b0a4c582fe25100a4b0bd90c81532fafe4215fd4a3565182e0f8a8191ea3f2e072a2aa316e3916a159c42a8a027982430200988426160317a861a8fa1e8945315f92e87432274398c02e1121a0b6379481c8a21295e10a95c901840030105d820d299a638b7c4f350478dbf060f80d2580495c31f95af00880010dc039d4180ce00008070a85827e25100a4b0bd90c81532fafe4215fd4a3565182e0f8a83f012191e601840030105d820d060f80d2580495c31f95af00880010dc039d40a95c93f9941a0b61295e11e8941a8fa17a865315f9261603,
  0x1df13cd411e36fc60339c8f20c4d80000201caa16a159c41195dd2a8a00f254279ce3190a5d820d299a638b7c4f350478dbf051627180ce000080705a58a79e0a86f1cc162309961d6c159d129625869ea24161f2902e19961b2bb960184054162299a638b7c4f350478dbf060f80d2580495c31f95af00880010dc039d42a1609180ce0000807014589d6a159c41195712a8a00f2545fb0a279ce3190a3410e2c0f672719a30adc32ad65d820d299a638b7c4f350478dbf2a1609180ceeb15553136000008070641296255a8468a8564e24ba1d0f6f08b8448682d8a8582460338000201c72858cc02c588e6c453ba4e04050010fd0eabc43850e9bc9c09d96212e1d08103d3810158ab10da0f45529780043f43a21014af03e24161f2e1d08103d380f758ab1250b9864798fc048da0f4552978fe650682d80043f43a21014af03e0b0265874a07c9c4279823316a431be1195c52596191296171616155d820d0d2580495c31f95af00880010dc039d4180ce000080701419961b30d55846a6e08955a3ad714df98c3a95681bed56bba70b10d5648825249642058350402c57c02bf4c33f48e316c6efa09a3ffc2207769208e4f4071c3007dc24f5110a6a14b1e4680de184a992a998e45a8568088c1f0865c10085272ab0628385c2b25200f9d44479650cf14c4e1c1aff06c108676103c1e213552fc1c02f645e040c6a03fc32054cbebfa4c582d28d584c140061000c040a6698e2df13cd411e36fc183e1b05674a85824761c082458fc048fe650e6300de52064798682d8ba1d0b844a6af12b2cd2447ba46ba84a585c585854349607e56bc12570c02200043700e75060338c4d80000201c05066259619463524a082a6f84883902550c6428524ea49c668061000c040183e0c4d800034828138141982612961723cd0e59b14450b4da0f44e8d9952fc24c584d0858466aefa9208e7b41e4e14b1e4432054cbebf8f0106e447b9144ebd28d59b0c1824f5246e406455c42a55652a99bb20b7c761c0e45aa9e4d4c82898780964567122c0bae120b359638d41ee90204735064f3caa282204e2c3c950c8dd97ec29e2a91025509e738c6428d04386c56ccb03d9c9c668c2b70cab582c583d50589760834a6698e2df13cd411e36fca85824aee58183e03496012570c7e56bc02200043700e750c4d8060339c8f23ac5554000201c05066,
  0x134163b238ab74801c326951f8794fba01642fa90b52e06b3884bae68e03f7bf03e3bc92e11fa966c2c069163703010398c0379481695e3099ba0c2041a0b63d0063f994170c8906b004a872d091e01c8a22b928f1a8fa0486e50d06e17a861e89400880010dc039d43a0403453ba42040f62ac4191ea72ae867b522e8742e1123316a11ad88f27a1d87020916723c8180ce000080582c260962103c11092189429388a6f03e51163d030f8450c72c19c4ea58e5043c4c9450e5b6f4978ac1e2b2102fda9d76237a469f8f3a5cc635c09066e08863a4a16524964b23c9c20e29102c88c1f0380a44865c04c14030810682d8f4018fe6500a9805c32242478072288043700e750000202c158840f0925088a1e2164fa4234163b4fccfa3c94a6d18e6600437000a188810822151563a963902832054cbebf800b78448028a7304e511a458defe6000a4a2c00c81170d06e1a8fa1e894822969f2da532b80e83229162d12114917a88060f804a529abbeed078fda8235a7860393943433a17a8cf3441d15b859005b9a0335c38303c482ff7d02fb5b802175ac5f1928c5f3931c59b763c5993f2e0ab800860d11a3164948ec3a70e8d8881c3191ea6591254f928572ae82c8f2757b46d0b58779fc02a601b3388b024167b520838a06b0007b92470fd55c823f6484fb4db0c14aacbd3cea284799440b274a027a1882307c75ac821970b182e94030ab8bec018400301000880010dc039d4072a80d8dcd32a4830a562c234398c037948322742e8742e112911ee91aea099ba1c8a24a872d8c055f46332539c40a84cf38b5e7f876d2a8a03316a11ad88f27a1d870209163dbc21a0b6723c8180ce000080582c2627e210ac58d562f269153558f26a2125e145f239451173bc2201490e11c799019b1b94251114190d015b123e26f06e5c807276938e4b06b5130500301000880010dc039d40000826096189d8508922424e04a523c2d860e76a0549e62b19ac4c140043700e750000214224a4e6d8222d2426a21232ed3002b5e9d19d7e6194400fe0302d2426321625162fa59b0c183a0c9460b8183e00610002200043700e7501caa00002136125a062b0a40a162d281f27109e608cc5a90c4e2c46b60f6f08c89d0761c0266e8b08d0c2958ca920682d882458722884a6685a58a63c9e814589ca85824a6699760834e2,
  0x14c9d96280ceaef0b4594c380a45005935b6f4978ac1e2b2102fda9d76237a469f8f3a5cc635c08fe6e0867de592c043700e75030810682d82478072288f4018fe652920b86b2cd14e710aa2809e6090c9500a98000022240b058159dc2491c0f08450a4e1e038ff286594e8c913e8f22516512691ff529b41b964f63998010dc039d4000082488810922bd88463264088b4594c39d98ac6674e902f6888c15d08bdcb00c790943913050529b4010dc039d4000082498c990b43aa162516514d10402057c023ce0030c8e029c9a02953002771a18affa18ef2c19c79a19344c140043700e7500002042488222d06e593c0db7a7c6858491a54f8ffd3abbc1e0c892d12f7150ea708905b1695e30c2041a0b6091e01c8a23d0063f9945e2b0723c8000d40b0582483c50a4e88ed0059340db7a7c6858491a54f8ffd3abbc1e0c892d12f708905b5e2b0150ea93417040bf6ad07cde91a670b2973186bb0c9b93b52ba4fd5010dc039d4072a81695e35001a7463320c2041a0b6091e01c8a23d0063f994723c8000088902c16056771760f09250a4e473de592cfd54d81ed5c81e9000ec891dcc711c679649506434056c4803800b78442494c4a1647506434056da4e3828590c48039bc5904647a9caba19ed480c04002200043700e750ba1d0b8448cc5a846b623c9e8761c08245824780722886033800020160b098258840f0442486250a4e2296459b0da0fdcf0106c7ee70ae0f1dd0e01b0c1a401a9d08103d14ee9381014e8100d460b98a4e1c06101505883eae0003489825884108622414c0a164304bd4458ddacb4928d59460b83e58fc341b8121b945ea186a3e87a250061000c04002200043700e750647a9caba19ed48ba1d0b8448cc5a846b623c9e8761c0824586033800020160b098258840f0442486250a4e229bc5907185611a9b822156bf694925988ecea74801c30812f7340291a016408b3eb52e00e9621743884bada3688f93c08f571812fa8811b51163d42040f3a040362ac454162398c0379480c2041a0b63d0063f994170c8906b004a872d091e01c8a22b928f1a8fa0486e5191ea72ae867b522e8742e1123316a11ad88f27a1d870209160d06e17a861e89400880010dc039d4180ce000080582c260962103c11092189429388a6f03e58ff185611a9b822156bf694925988ecea70812f708905b,
  0x1643ae463327f876d539c43316a1196670184000880911ee91aea299202e8742e112398c0379481d870209161b150d1e0c89180ce000d41085c880080b1f22101459c40a17817f1ab3a805c70f9f2da9abbe3f2e0ed078fa3164da82318881bf2bb6cc22b524d81ed5c81e97081e7612e8869ea242b82f956123e20c81011ea326f16694b23e2902e19966d04966b2bb9601840030100614253abbc00880072a80d8dcd180ce000d41085c021ec581a112101605056c70ae52584e59bc0a178ac71a8ac31e8ac1120ac90c81532fafe1fa964a3566c306030100614253abbc00880000d4170082584e19966de7240d003a2b150e9275e1e53ec48055cbe2745a4e380c040185094eaef00220000350421709613abc04966ba59b0b003a2afda458dd80326c48f883204052c8f80c040185094eaef0022007a2506a3e85ea18003505c0208405096139bc0f9669b01a458de08a5848f883a575d2c8f8a40b86659945ea186a3e87a2514c598c1256443459842a50dd76cca6aef8fcb831c5924647a88ac03b41e4e8c5b984a99ca8a92a998061000c040185094eaef0022001caa06c5434761c082458e6300de520ba1d0b844a447ba46ba836373460338003505c06a200202c2101605046599cac95116371fa964a3566c306030100614253abbc00880000d4170082584e8028a730665996960e95ef6c30642040f453ba4e04053a04035182e6293870fab801840000d211008210142412eb089613828531663c1a08a59460b83a9603eae012e39bc1b928056c06100003480824884240960d1661ccb1c59254e1dd584a992a9988a4bf4e45a8561db730d7a066993c4f91ecd836a501caa06033800068082495c7b1607c88429920592518cc984ba12a1cb54e710cc5a846b621a12ce3c11bc8a36e46033800068ec571607c8848913c4f93f9339a6643ae462e438849d539c4440b274a020da9447b36000920b1f22982267056596d6211fa963c041b2b841542040f3a04036c30636b046293875182e04b8e0fab84a1647018400301054162000d2110082488405062258905316591e08ac012a1cb4cc5a846b623c9e8a632fd3671454266e80220004870761c08245860338000f1065081a0b008248848924e2601a47a70e0cfe680cd64a317ceae0021834463a03e652036e9c3a35f031a8de9f1a153e3ff420,
  0x1a506033800108b42f038671f29083058054248f47b0ce2996895a8561e64468aa8a313de1a12cc60338007e1602122c4f092698e213b53c13afb44b351ecd836a50165a0e447ba46e43b24abef64ea6190ede6030db69e180d2016be4e50d0e4cf0c34e85ea1f40bef3c0d270e0c9f120c8e6821be4c7166e5051856475174d961686ae324ddcf01c5d3f010dd9700add8f007e4e59f4a859e69c467d5ed186c4b0ce63022c0f0cdea126391a7de4019f0303bd2247f7444d2120ea49a02941a0d7d7c01fe5d519ff9a192768189662188de9f5474fa3c93002b4941907e654d658b0df4c60af4884efc0a981de7f342d601e21253a33ac6ef80e0e508ecb80e3584c1405ca79b6f49e2a9178ac10255022928d04389c66804870c4d80000f0422f04a0806c3f94be2744285a04aee583459fc18471c329c052ab02a133dd24b4dfe4b5c260b8e6aefbb44b34984b74363734061000c040022000487022928d0438ba1d0b8831a0812447ba46e409c66860338c4d80000f04a0c0ea618201e1047b092213a0980692ac8165a0d6211fb1e3a0403629387191ea72a2a3916a1593a36f11e54203f9c537e2fafe3c041b743805a118d4a3566c3065192cf36b041220e03010541620ca70018402bb96180ce000d2128306196008104213a0a4816052c21609618844138285a052cf19ad204b8e7181314a015b000d26182041092e8292b0896188440d167f4b173c0ce70e0c0f120bfdf40bee0244a64a117d64c7166cb20096ae001d8f449d9659edd6b38fc0a9829c467d5ed186c4b0dde7f0005087894a3a93967d6e0b201de18015dda014d6e0145dcf186ddbf17ac00a6a3a24bf29399659edb88600577680535b805176fc5ebbc3a0590f952cb9802a60779fc57b460014208078948920b8a859e4f979a09aab80080912902a60d0b58001420807894bf20b8a8d2a4ebc3a04f7454ec1b6f4822929e2a90d04389c6682c2d9a08108839cc0859cc1e211c04870c4d80000f0421729e332f120c8df40c1f3c0bf6475174e4cd16be4c51676ae2ede6821bdd3f010dd9700add8f007e4e0681459c4363734a6480a802e7e6197d3e3ff4aa280ba1d030810e6300f4018761c09e608b8448682d8de520fe650824584a6685a4286c54350c95196280ceaef00a9801e211cf6096c7832240487072097460338c4d80000f0421700859cf06822965182e0ea580fa3e04b8e933fe4a015b13966f0a84cf,
  0x12bb966293870fab8261643018405416204a2c03010000d21083021090258621104e53169fc783a9618a4e1c12e39bc1b928056c06100003483024884240960d169d0b8661c643eae012e3b200655bc1b928056c4e5a659213ee8a11e8418471f5c08f452ab02a133f1cb326aef8fcb814006fd9006edd24b4dfe4b5c8ad493607b57207a5c2079c647a81c40a7b41e4e8c5ba80de026410d84a99ca8a8e45a8565a4c363734a65a253c24a447ba46e43b20b84e6302f647fcdea12164d1e40190403bd3003ad2218ddf011a7e6010dbe63b0f0d3e49663a3b0c06100022008c1f0865e8aa2809e739584695a8d9e8621d6bb0ba1d0b8831a0810884efd7c01fe62188d964494b23c9ca8c900a9801a0d7f681894fa3c89438dc201b1de7f15ed181e21253a33ac6ef80e0e508ecb80e3584c1405ca79b6f49e2a9178ac10255022928d04389c6680487060338c4d80000f0422f04a24a525a6d3b91fb1e453ba4e04053a04033c1235942e662ac42902e19b566916372b92371a8fa1e8945323a17a8812114904a2c018400301054162000d210830211202412eb0896188447604e5a64b891fb1e42040f6293872616430184004a2c03010000d210830210904b896188447604e5323a506448055dbc1b95a4e3800b789025844138128b1419123e26f06e56938e4b06b50a16910d168f05168d9abbe3f2e0191eaed078fa316472ae8da82398881c76781f73b13b50611c72282416484fb5c82194937e5001d714aac0a84cfbd3cea284799adb18f43e4440b274a027f876d539c403010008800d8dcd180ce000d4108bc0e19c7ca5c7e030580541e0922122c480f426a927b1a11058565a4d3b91fb1e453ba4e04053a0403942e662ac42b92373c12352902e1a8fa1e8941992c153119917a88121149018400301054162000d20c0784809618968110904bac22604e0a1691590c12e39bc1b928056c00348422488425862240980d168f0b8661c643eae012465f200655bc1b8ae23ec4e5a2c061000c04018471c0220000350bc0e0541e0848b1202689618968760904b8145a377282125b942e662ac40e8c832913ff17a881220e0491c92bb9601840030100611c700880000d42f038150784809a18968760904b81413968b4fd590eb88a4bbd84ba1102c94e710761caccc5a8465ba1a12ded4121e1011c41cdf2066991ecd836,
  0x10dbe61b1a3fca19666033025043c4cfa3c81a50ec0e3580a9815ed181e212400350422d122222f6e10ea24a4261a16081565ad4fe398ac39b238087980c6374e8c919886233e8f21516392516b12693eb038d663998529b41b90d90e0c7513050000d4108b42f122222f61b16b34d10402457c01fdecb18ce6218866010dae5f90d6f985abc8e5ab5860e6d740e5530ee38219972c198ce03cf40e3589a4fac6e43643831d44c14000350422d0bc48888bd86c2516b119565a90e27e602c4fb982b443dfd8e6614a6d16c0dcdfa0dd658b190f9a511c8e5ab5740e578219946e436530ee32c198c4c14000350b42f088bdb8408a162513ae616af40bda223054a6d000350ea3ed53a2396ad341dda017e1800fd6400ddd6917b5d1d16dc2e0015e399d9631c53e4966120ea65d519fde9f547530ee32c19b662b0e6db845ac925aa41a0d7f681894fa3c89438dc201b1de7f00a9801e21253a33ac6ef808ecb8e0e51b6f4978ac022929e2a9102550d04389c6680e3584c140048705ca78c4d80000f0422f04a5aad6a11a2a15be48684b3c504df3396890596a7398c037a844f8ca5790067c0c0eb7b2c08d489283a80cbb2680d57a7467f975c3a994969b2a324639982307c2197a2a8a0279ce5611a56a36529b45b0d230788492e8742e20c682042213bf6a837968837bd2037f5d035706835fda06253e8f2250e370806c4e8ceb1bbe03839423b2e038d6130501729e6dbd278aa45e2b04095408a4a3410e2719a0121c180ce313600003c108bc128925aa6cc0701f72282215c82197082175001d74db0c643ae46332612e8adb18440b2539c43316a11a2a869ea2416a50d8dcd2307c2197a2a8a0279ce5611a56a362e8742e20c682042719a180ce313600003c1084a0c0ea2488484930481ec0596a75a8c7ec798ab10a40b8665a84ae4a3c6a3e87a2514c5a7c5ea20128b0345a7418471c52ab02a133dd24b4dfe4b5c260aac061000c040022013a33ac5ca79b6f49e2a9178ac10255022928d043804870ba1d0b8831a08109c66836373460338c4d80000f042128303a89221130481ec058905a953b93c03df942e63f12bf050b8d42040f453ba4e04053a0403541622902e01840008800121c0003c2d05a618844c1200589018828af1460ea765a8c12f5116376b2d24a356002de258621104e73200a28665a8441b43a56216c3061fb1e42040f3a04035182e36b04,
  0x11e4e447ba46ba80034816220460b29e0496d3829a20ed5860e3e61b1a2fca1955aa22d5fa22c56c22bdee10397e602d6164d1043e0d3e04744e5644180526a21b0dbc1b94a85b34285b25e8621d6b22c6f4a645b3c8a08d58e66002200f4018fe6517c01fc8e021e623e054a6d0e03cf40e35930ee32c198d740e578219955650ec6e4366920b86b2cd05c4c9c4c1400459a14b1e46447ba46ba8fcb828c5b8e6300de52052ab1d25b2c647a9ca8a8e45a8565b1d584695afda23bac18c47dc24780722881e3b80ac208c1f0865c0363734ba1d0b84484a6685a43900928c4d80603380008016220220f0bc06ba05b460a6183b76883b5986c68b6a88b55b08af7b840e57e83bb858fad98e469763998238087988f81529b4380f3d038d65d0395e0866555943b091e01c8a21b90d9a482e1acb341299a1690e4024a1305031360000d4220222d03c2f01ae82645b3d5910d0ea0601496f06e50a16c90088001166078ee02b083f2e0a316e3916a398c037948180ce00020058880882c068cc1891c2a1f86d8905b341dd3b128d4429a1d87020916398c0379482e8742e1122307c219701299a1690e3136000020088d0119d25b2ecc07024546023dbd07a1a28c4fb7616c5640e6147847da304890d8dcd5c8e5b1d870209167081e74d81ed612a62e8742e1125001bfa03783916a398c037948180ce00020058220b01a3311c7e1b6240281892e5b241dd3b16bd440b200020890226725c1596c7ff84e47c52c8f8a40b8665b04dac10484524989ea6aefa10b63b41e4c761c08245a447ba46ba8183e05ea200610002200045981e3b80ac2000080160882c068900a0624b9d81196c5056c4e47c5a41bbca40b8665b04dac10488385ea20183e006100003482224820189d82412e0502a0a16c32e243404c5080fe47ecf9acb49d0e00003482208062760904b814110665b0415f110fe56938e002de2f07805096879800496bfb3190086d720865c2085c8ae2940075d36c3118b92b6c61102c800672240825c3b0565af531f84046d7284b1a30483073500015c7b1606713e2a0784f16bb4a367212741cdf06033800571ec58022670203896b94bfe024bed643e54b2e63a00edc840e3e61b1a2fca19541a47edee1037fe602bf1a01fc0a9815ed181e212400350422d0bc222f608892618202513e5f16b74bfe024bed643e54b2e63a00edc840e3d20,
  0x12307c2197a180ce000e2169ac13826748901103a571445bc504d21161f1220e5416217a88018404e0405453ba62ac4000d2a284e2586276022240440a03eaf2f20e8145bbd4632201491e13392f015f173bc6f06e59306b3c807276938e6311950e11c71b94250a0f800880000d4258625a1d8050900616edb020849f5a458ddd0e2250b9848838dac105ea20a40b8aee58124844061000c041505882a6f8c64287a049c6a04a466b4852850d0438003485a098144b8906b04e1116eb11cc427d210b603012dc761c1ca56c48289808d78901b95066e9fe1dd54c3a8143f9576ce084565c1a427492056e3a40e5a4e3992ca924a082a4084585b9ce45a8565af45404cdc61b5c525b9558468aa2808c1f1e2a915a8d9025509e738865e89c6680c04036372c1cdf1962814be2744ae23ec32275cf02404182455c0277402200045981e212dd2127c60338c4d80000d0e2228120e04a5ba44738412db1096ab02138b2b0f6d0d8dcb32ad630adc2c0f673190a32376bb852f2197a3d828b3410e2719a723c831360eb1555000e2128201616e7ab0a64c640034a72168525b95247228db907350640b255c8b23708b21008800116607884b0da94180ce000342993c5b8ce3917816b2f9561200e002de5304413b165b870ab895713410e2c0f672719a30adc32ad60b1127d8745822a869eaeb155531360000162b046210645b7d9a0b0b61690e682044024a31360000220c03c5b7435fda06214e96adc680875d05690943997546772691ff55943b1b964f2f11f76dbd25e2b0a482e13d0062b3ec5f82e978ac8a75d887e3ced7023f40bf6f78fd5de91a0701dd4db0c462e49716c7440b22307c22b00219704a872d40105b1695e30914038f27a099ba038d61305001166078ee02b080d8dcd1713273f994acb3432a4830a562c2343d825b1c8a21d87020916322741a0b6723c8180ce00020058880881a0b0562616db53eda41bb4322385b010650e52e04962f640c040bea41acb480034862240144b8445104e1983a7012c5b642e19ad20fa3e718131933fe018400088001166078ee02b08000201881a050280d16d7547c6a2a9cbea407ecf9acb49d0e01460b83e47c4183e05ea20dac100610002200045981e3b80ac20000802218814240285109a1396d5564434060c1805260151c55bc1b94647a9ca8a8ba1d0b844a6aefbb4,
  0x1b9110a68e45a85680816128e7212740610150588022000421648c1f0865e87a049c6a04a42a6f8c642924a090255066b4852850d043860338003885a6b04e098225bfcd0776805f86003f590037578e6775a45ed74745b76594290b8e45bf11d506bfc2b83ed4503f5779fc62840d0010fd08a38508542a10e5422529016fd1035c09b2761b8cf023d53823cce823c54c0395058800348640fabc43b6f20e8a81216fb2864e79ea26842bd5658e71228873c28770e28a6be28949240142437dcfad828b228fe4e3c2d4a6d1aa29b5742995a229d5fa297d8629f46e19350e14b9ece0275081036a04d2761b8ce02a5d7c2a249a2a8d042a3c8e2ac45c2afd4c506580029a458dc0e3584c1418e6600c040022007a049c6a04a43204af42d6000351ac1382625822110281903eaf10edbc83a22142150a8731445be4f27d292850285b106bfc8b04590803f907884d4803e72a104d7026c942e63a3664e04513f0121b118154a5e9db47233fa84261bac80189e98c01ca266000a3c12357b378c4070178b13120b1b8881bb570e5f2b96cc0d8dcb0737c03010541621e81271a81290c812b0a9be3190a64b2a78aa42b83ed4503f53683f71fb3e743882902e049211018400088001085919ad27081e75c81e9612a62e8742e20c681e62416f30616f55001d74db0c462e44429a0584a314a143410e3916a15a029c849d2307c2197a180ce000e2169ac138260891c5bdecc640b375c8b35708b33228b3d0d8dcb0737c00880010859180ce000e229b1c2ba4aed0616f53964e63013e428cdea101ac0084103c200fe41e2135e40491c3f55c09b12e349d722c64f023d5445bc52a998761c0828982c289066e8145bbc7ecf8da0fdd14ee9381014e8100dd0e218ab10ae4a3c5ea20a40b812484436372c1cdf00610150588022000421647a049c6a04a42a6f8c642992ca9e2a9066b4816128c52850d043918b9136c3110a68e45a85680a7212748c1f0865e860338003885a6b04e09822240445bce84e98c0790127b0e5b4bae6f7accbf13b922b004f90031e125f1b042121040f07884d6c2c00814077012e13c12356916370d8dcb0737c03010541620c812b0a9be3190a64b2a78aa4462e44db0c5001d74429a2b928f1a812917a881e81273a04034e0405453ba62ac43683f7743882902e049211018400088001085919ad214a143410e640e6147849370819f4aa663916a15a02,
  0x1274e4c1acf201c9dc61b5c32275c280b866e00f00fcd380fc4e80fbe384a2c061000c04002200043700e192e303774d00a54e21275d2128c00088a43b014099d80586211171d5a85680846de08c1f0e6300865c0de5204a6685a43a72ab10085060338c4d8000a0026058520e0ccb939b8860079c48317cf03157d031376803b5b8039773c611915c5bf747c5bdab93152c8f87578e671b109d2a0ea1e0107150133658a058ea306f06e59306b37186d70a02e19b808e128b38849d7484a334029501840030108c0ddd2b88fb4e08ff45090300880010dc03864b02a60779fcd0b5807884b00022290ec050267601611034240620888fbaf124d13a2c0a103f0616ed2615dd190fed299a64f049938849d74a9a030100088001166078ee02b080f24a0a9be3190a14a143410e49282409544792733916a1596c75611a56a362307c2197a180ce313600005a08022760262922444171723eebc49344e8b02840fc3e5c4d3e070638cf8329c2221d143a492c185bb49857768c1224643fb4a6698e21275d2a68e45a8562c9aee293c36e51e36cdec34dc8c1f0865e8061000c04002200045981e3b80ac21925c342a6f8c64285285124a0902550fc04858fb03c9297ec28c83d95357147ccab58c2b70b03d9cf60a2cd0438fea109c6682c52060338c4d81c8f23ac555400378200888a5c540a2fa9017a861e8940d011f12011b1ab3a6b388532b89f2da002de1892e24044879d04803e5c4cf26a064925063f00286e68ead20385c457a2719aad07c0b1703670b205ae03316aa3170b11b7831360180ce000d2a01103f1ec5c3fec09b2a0f24a3d828b5fb0a78aa43410e320f652c0f672719a30adc32ad60b1484d5c51f723c8eb155531360000206482237970d5a85659046de06033800a028c7b170b5c1c5439169c1695d9700ac0050878480a8591709001b845ad961684923e55d8f007c0a98000508782a0200b9645c1d6371a88db1788e903010060f8000d2801440a04e691385c14cbf4d9c52909812379483f994000d23f0a60b17035a8561cb44699860338004aa105717011c15c99882899dcc01066e8780f4c1497a405bf61210d67091c0dc0572cf023ad3823a71605adbca19cc5be4485bec84d4820e281ee491c5bdc3012dd84a99ca8a8ba1d07ecf8da0fdd140fd4ae0fb4b8831d0e21a0798a40b8905bcc124844185bd540075d36c3118,
  0x13064c21fba3a162423074b44c3b2682164e97574ad5c8f20003505a2d10c3087ee30643c3074584e9303ec616eca3a908fa95d5526d723c8000c2116858680825d4d26b723c800058220c211685420975136e460338002293c5d3cf67eb15550004a2c174d3db5c8f20003084c19fb8583075345128ac08174bcf0c4d80007328a138261118062ade940665d24dcd180ce000160da2efb860338004894365d156a180ce000cc390d830d46033800973d0ad9741df06033800070e25cfd1cd723c8000c1d3064c2116100fb8ac08173dfb1c8f2000b88c213067ee3074582b2200c0b71180ce0015c672fa220ce1313600004a089928497374035c8f20003067ee160c1d30845a08a125cd4fed31360180ce0002619016441733668c4d80001289c4c8de53136000024270580689e5cbd06d723c8000241602c21972d416dc8f200016022271005cad1a55911a71501334f811d1b0159078ee1396370285f712016d7186d79493b7c587071496e54937e74a9af40c356bb0c4513b39b93b52ba4e5f22b000088270301610d8dcd2307c2197a5611a56a3646332538775500e5d70819f4aa663916a15876d2a8a0279cecc04cf25b8ea886c3180ce0001269200a29cc0585a570443b3de4b81a5ca7ec3d82eb323765fb0a78aa43410e2c0f672719a30adc32ad6723c8eb1555313600022c2b058129727c011c592518cc81c404584a992a9994e3fc4e45a8561db4aa2809e60b30133d0c6f896e3928057c085c8cba1d0761c0b8448824584a5c84880525bc1b94645c7c784ce664066c521b545cef24c1acf201c9c423264be2745c604d46e5094283e1082454da244d142444f0243d382434e8242cae24240c04002200043700e192c363734603380008814099d8058185c94e1f2a108d2494d10788494e8df75d03bd6a933b6883c198ed177173bc13050010dc03864b000223a8246d81a0c0085c8e825a16ed409540a90212719a0a0f80088031360000d405026760181889012972145fc923b44205b1d8c4654bc057d5846924a088c861a4e395a8d902550cc5a82a40849c668468a82c2d8ba1d21a7a9103fb5a0798b8402c363735d2128c521b55c604d4283e1a20f0663b45dc5cef06e5094022004c140043700e192c60338c4d80000882605818091b619171f408496e382c2d928056da07986c427478041c5404cc900881e212e3a3b944e028bef0048064c5e06446a27547a,
  0x1cca10b612a9994e1dd5724d04e4361403974561db4761c178ac0aa280089508c1f02292882899025509e738c6428865e8d04389c4c82c289067800487002209c0c0584368bb30133c96e3800049a4058440903c5dec74582a62e20c67b52682042a3242213bd0838a1b3383d0064713bb3fa844db0ce98c04429a7b16e9caacb52e01886d74b86c36b01279f0113801637121777078ee0d010702a980301610990212307c2197a022543190a5e2b040954500e5d5c93410121c08a4a3410e640e614792730da2e46332538775073d44aa661a80ff1781039306b32627a842d8390d815876d2a8a0279cecc04cf25b8e1d87020a26271320b0a2419e00001269016110240f0785de50492680c57b84693db86733a9775a482e1acb90a6d5ee6844791da8235a7abc480e592a0f95398c0150ec337a846585a179006763c01fa7119f4893bd93967d57b460c2048482211b3381a20c8b02414713b57d874170ac9bd07a1ad97415822a1fb8ca28c4fbc537e869ea8e03f77607275a07072406e5bc89dbf681937f4416d5300e0da2e1305032025532ad630adc2c174d022543190a5e2b0409545611a56a367a18875aec500e5d2a8a0279ce5c93410121c08a4a3410e073d44aa66390d81d87020a26271320b0a2419e0779fc078ee02a9800012058440903c160cc5d878121777029e423a979a18fd563c9a85dcd865dc49a31640e3584c14000090d43077ee30645a3084580e18c1e0b48e9a022084ecaf63a977522af844d0fb5829305d5da20ed5aa0e25fa0e156c0e0c8e039d0402c57c02be61b1a3fca1965ee31a374c195c4c1418e660c64294a6d000350c1dfb8c19168c21160b48e9a0223b2bd8ea8593a6a17733c9a8196494187e5a90e3f680d740009088a1878210ea61977150d4c4d80000884a490665dbd3fd31360000a60982a05168111446b84e2a0aed158ae50b13c5db53f7313600004e2582c098a6110ae5510145a2065dad3cf723c800058307500430ac4197694ebcc4d8000058961604a0a1141998c4eb5c8f2000258c21128ac1681616046ec9784e75c8f2000160ac880c2112816258465d8d38b723c8003ee3064583074c21432200217614d2cc4d80008915c3304a16024ec9ae5d7d33f31360002241604a330226b975d4c75c8f2000088582982c14975b4ba4c4d8000b783e1102613944731145d652b7723c8000d44305a,
  0x1842d872a2a390d832829b3227430a562c2341c8a21d87020916398c0379482e8742e112500207000a6680580b0d43894e331797a69aeb908c1f31c3ae4865c0205b2d005cae72127436a501cca05a578ce436000298580b0e22bb4cc0897954bfd643e56024becb2e6054c915ed1ba013ad2012141a11bc8412cc6c131fb41e4e8c5ba10b61ca8a9fe1dd4e436056711764880a9801e2154761c082458e6300de520ba1d0b844a447ba46ba800299a01602c351f24f0f408bcae93f552a99a14b4c3572396ce4360565e3d18cc836a501cca05a578c761c082458e6300de5208a5d3c00299a01602c351f24f1764893678803008173d0f178d5fb0a34170ad07c6713f91b04c77f876d0da9432829b3227430a562c2341c8a246332643ae000a6680580b0d47c93c5d8565e3d3b55c81d1adb186ba185001a7560ea974849b4a97010815eb8f046f2113e1e0242f3c61729e0c2043d006073283f9941d870209162e8742e11222974f09172d08972b34170ad07c6713f91b04c77f876d46332643ae0da941695e3000a6680580b0d47c93c5d8560f178d12153e49668c5c2e12137e2206ffd0f90aedb31583aa53607b57207a5c2079c20583584ba10402c57c02be1a12cf4c33f4a81081cca0e6300de520ba1d0b84481e21548a5d3c9a3ffc0e3586efa04c140bcf18245cb4225cacd05c2b41f19c4fe518cc990eb836a505a578c00298580b0d44f17615892488882d0780915eb1532400142248420e122220b4020782a04232fd3671454264834141accae235d2c03fe8a58dc48039281bd5bc1b94968b05e04647a044ea21b0c0c04082458fc5c0c002984e348440b09004978732fd36715542679800298d27d9a0191785698e25cfd3cd411ecd8002981cca177f2b88fb64b2a4928214a1413921119100b16177d2615dd3410e4095478aa4030100b1120a86f500012110ac168d22e128058465e041337186d708124d0009005062b79d8258125a044af0345dfd2b98794fb911ee0d015b91b901b3dcec978880305fb0a323762c02893410e3082b33190a3282c540954030101201570a86f52fbc09306b32615dd00012110ac168d2129280584616177d5b8e6302d4b80dea112e5ca5e40187a049d224ef5c61b5c30810525b9468831d2a69f61d1aec3160a98ae9397d9e59248ac00785de45e040c6a03fe4c1acc989e81cf51c2067d18,
  0x15c2f8219961032f66e086e2206ed5658e4ae54fe4201264ce698e2127518b91d2809102c8cc360465ec51ecd8165ebc585eb4365d16fa2206e43646c5acd36714fc8c1f2920b84ba1d0e6300761c0865c2b2cd0b8448de52082459009285ca784a5aac0e3584c1400220038f18002f0d42204248884050520f17b32c8cc4c85ae4fd434491c8ad497206e590068dc2067d84a9a80de12a998365d16fa2201cca0003482221052571ec5819c298465ec41dd3b13f522b524429a612a6390d86401bb15a02a00389caac00022210525819c890260597af4fd48ad4910a681c57a584a98e4361903984568091e119e72ab2102f3ca65d6cba1d0b8448365d16fa220761c0824580034822210141482c6713651617ad180fa00ede4e50d153a828e893935a20ed6be0c9661b1a2e4771745aa22d5fa22c56c22bdee10396ae002164d196168c8e021d7c01fe68411d8d0095043e0e9c3a366247ef4a40153e400c78c901e3b80a17558e660e03cf46c5acd4a6d130ee32c198d740e578219955658e46e43644c14038f180e358002f0d410922222f62d0542a292103dc02f658a4e1e4c582c34961bc47947ecf8bea41d0e01acb49460b83e5e9cdac1048838183e00c040329c00610000348224b89605090b086221028bdb888e33e71a900ea6c2b92c7600c9b0d06e1e89442040f453ba3a04033c03df4e03dd805c70f532b862ac4942e60301054162060f8000d20892e242c218a1e21028512f20f97a7b931c3ae510a681c57a4365d16fa2208c1f0865c1005cac5a578c761c082458e4360001602c088cc2bb4547497a5b9110a6b1c3ae5403974e4360205ae4565e6e7212741c5cfce6300de520ba1d0b8448365d16fa2208c1f0865c1005cac5a578c761c082458001602c7c8223897a3f1830810f401824780ac0c0f65e7c225e6ccc3617e0ac4461dccc6609f2dd0fe650ca920c2958b08d072288c89d0682d8042165fe1334001602c2f0e22797a1f08a855ec6cf7072288682d8000b10c3d979f4d9c6cf72200c03c018207d122f18fe650ca920c2958b08d072288c89d0682d97e0ac4001602c2f0d443038220425e747c219706720240172b9c849d1695e3000580b0e2158225e6fc22a02088176132829b3227430a562c234001a016106430085e67c22a020881761319829f8a07c8775cc35e2f3c60897953d04870904730c04b7a316e,
  0x11d10c5e64e6300761c0865cb4b8448682d8de52082458722881caa00089024748081602c5f46022307c330d82197a1197bd2713200016748981297cf277c283e044990346d9080fec7ee30f00fcc00190d25a03825854148a47417cd5f1c4804bcbea41ac5f0c00190d25a096150522910e913844992580489dd000d20e9c00d1b653eda4e3832275c280b8664634061000c0400034968258a443a444601441397c7e583423ec0034814110ae9e16e17f446f96f06d95182e0d01330486d503010009f00186d30005215168110a4191ac5f0c7119abbe9d34441ed079343b66c911ee4203fb91b900838aec93494713bb1d8700701c76401bb5c81b9209753a03781a20c398c01096ab7d87448ba237a84022545822a7917bf2b16df869ea24161f2bb963683d154a5e0d2580486d50601377186cd541622c174d3190a462e44db0c5001d72617bd3a03ef4e03f13c03f31fb8c08975d4429a390d815a022307c2197a9c96e50da2e29931927132009f00186d30008414858129d00f97c181068830884ef404871f61d178ac008950f4019608a8ac5b7e1a7a8c642902550002105a058460e1e41917bf78072898425aaf101c0089515cb60ac57763c9e8c64289c4c80012816118985ef57ad4d9c53f2307c2197040172b1695e3000d208884050520b0582f20a6883b561838f986c68bf286556a88b57e88b15b08af7b840e5f980b563998529b4000d422084bd8ea250fb5268080ed79882a61b1a2daa22d56c22bdee10396165ed5860f0dfa0eee6391a5db6117676d1c8d92ca9e2b21740e569d7623821995f82495658e54a6d23a4a146e43646c5ace92112e74f1c47200624a40b980326c7a2506646354c4665243ad77a469201214b23c9e5cc628c5c2c1a11bc322c2c482c6e6e086e2206ee105c04ae54fd5dc592584ba05c39cc0a9802012661a12cc345b8c8a5d3c1e2154ce6983a0c8e2127518b91d2809102c8cc360465ec41cca11ecd8165ebc365d16fa2208c1f0ba1d0e6300761c0865c0b8448de520824584a4c85a439008523037744c1418e660061000c040e03cf40e35838f18183e0022003c5ecc002f0d422042488842582824014b08520997b70ed661b4eb985abc8e5ab5740e578219946e43644c140002f0d422384088b4bd8949913a8597b50ea65249641e21553a5ab6425b25d519dc9a47fd78ac102fdb7a469201215740e541a11be5cc628c,
  0x12ba780611954937ef417419b822194925907b925611a56a365e2b02b0303d825906b004717df0817db08975d4db0c462e44429a4aa66390d815a022307c2197a1d87020a2641934d5fb0a323763410e32ad630adc2c174d40954271322617cf0b17d90997d70da2e9caac00a2800016090524f8925f9ff0902aa933e20e9343510e392f81890d016f17816b3c042f4e042df687197f446f99c246fb5182e01840030102ba780611954937ef417419b82219492595611a56a365e2b02b0303d82595fb0a323763410e409542617cf00a280f97e32a10a306b004aa6607b924717df0817db08975d4db0c462e44429a390d81d87020a2641934d15a022307c2197a2c174d2713230adc32ad60b17d99caac0da2e0997d700016090524f9d80a17e55f06381b3c0014858128840f97e38f8a40ba4c0404661be61e53ef1638e4061000c0405e055448055c00348145a0440a04e4a1805f853410121c2b0303d97dd1a20c3fa847d874e98c0582a67b0e5b679649f78e5f3190a5fb0a323763410e500e5d2a8a0279ce70819f073d44aa66390d80022409058fb8c19168c213315cc70ae90e0544717df400c84f09200f86cf701ee900043054791a03d97dd4d0404873de397cac5d2c8ae28cab58c2b70b05d34c8dd8d043aee14bc865e9403974aa2809e73918b9136c30225d75c2067c1cf512a998e4360761c082899064d349c4c800890241604a331ae0817db4a34543ae41cf5140075d18b912a99910a68e4360568088c1f0ba1d0e6300761c0865cb4b8448de520824580089024748580b17d94a34543ae41cf5118b912a99910a68e4360568088c1f0ba1d0e6300761c0865c0b8448de520824584a4c94006fc5a43a800e100850368ba72ab00005824148265f5ee4c70eb94429a390d815a0208128d2307c2e874398c01d870219702e1123794820916129325001bf1690ea0038402141617d3072a80da2e9caac00016090520217d5400c84f09200f868830fea11f61d3a630160a99ec396d9e5927de397c8ac01c2067d36c3118b912a99910a69403974e4360761c0200a2c1ee905680878096482898aa282205d848c1f0c8dd9064d349e738c6428865e8d04386c56ccb05d349c4c8c2b70cab582c5f441caa00089024748081617d3b931c3ae510a69403974e4360aa280204a34568089e6088c1f0ba,
  0x110000348620522c760a45a0285fdd25b0801319406bb6284116b2d2a8811f0c169d6c3725182e1393ff02162d04919708971d1b15971916df6585a10fa5e2a1709763c01f902aa9397f10e8322ba780617f30f1e03f01264b2a492820a9be1c90411617ed3fa8478aa4409543190a320f652c174d2713230adc32ad60b148e98c07b0e59018400301000a2801166078ee02a984d5c537218d3d2315e7484a31497eb8c0511208d33073d44aa662627a388473842d8390d800016091201e0cc5708a5fd51c708972500a280001618814099d80617f33f94be2744285fbc3e97a40aa83a0c8ae9e00c040045981e3b80aa60329c0061000034824188784d84ec0520625968760ac938445fc567d8b019584816ff687197f446f95182e1393ff01840078ee02a98000d218878051687624e290285fbe0a6a8e45b039f975467f3e8f22506757a7d51d4c0f0b618d1b59170921352612a65d0b95688b997e8b91529b42e8741b92a92e20c1712a7682042213bd238ffb3d0066dbd208a4a5e2b02b030021761038d6130506399801166078ee02a983190a4095478aa45fb0a3410e3d83e00024480781188afb8c19168c213075e41617ed829aa3916c0e7e5d519fde9f5475303c2d645c2484d4984a99860dbcba1d260318dcb8831fa2e44fa3c94a6d1742e55a22e65a08106e4aa4884ef48e3fecf4018fea13a6301ec39653e5fa49438dd78ac0ac0c05cec18e6604c1400e358f60964045981ac001ee491c5f7c205f6c225d7536c3118b912a99910a68e4360761c056808828988c1f0c8dd97ec29064d3502550865e8d0438b05d349c4c8c2b70cab582c5f64265f5c085f5672ab0368b800058241497eb5afc324ae4be2744285f959213ee8a11e875c09063a186ddcd01ec2a133ff24495fe1dd6f0565d76ce0925f9cae9e018465524dfbd05d04b23c9e6e0884a8428e5249640c040028a0085f54985f3caa2809e739584695a8d9e8621d6bb2447ba46e43b25d7c0a981de7f01ee4978ac0ac0c0f609641ac011c5f7c205f6c225d7536c3118b9110a692a998e4360568088c1f0865e8761c082899064d357ec28c8dd8d0438cab58c2b70b05d35025509c4c82c5f64265f5e72ab0368b800058241493e5fa56476f11e50c92b969177b1217772f89d10a17e56484fba2847a1d702418e928553820b030107a18875aec911ee91b90ec975f2c8f272a10a302a60,
  0x16dbd278aa41220e36b041497eb2617bd0184000a285001a7073d44aa6625b9e5387755c934115876d2a8a0279ce01166078ee02a981d87020a26419e01096ab022543190a08a4a3410e27132000161e0281184a4f83c7f83a604c0a1e88d50c88df1a88d903010060f8000d20a14413980730e860454fb69139f0c88e16c04190184003010060f8000d20a1440a84e60138603cf0b618a85592203e8f20803f9a81341b8c0b25143974388380a975f0a89238ab1410a8f268aa3170abf71a907026c6014fb45041d4e04193c3403a3660c81016906ef8206f154a5e4b23e0301054162038d61305001166078ee02a982ba78000d21e0440513e0f18c0e26418944bc82a0e84e0f980d0966200c1064094cab58c2b70b05d357ec28c8dd8d04389c4c8001e058128ac602d3b94e03dd3c3403a366942e654a5e2902e1998070d2581f98054513b33f2e0a316e398c037a84790064893bd0c2041a20c7d8744937e582a6f417416796499b93b5073d45c9341500e5d2297f54aa661d87020a261220e41934d1497eb1096ab08a4a022545e2b00da2e01840030105416201166078ee02a983410e3190a409542ba782617bd060f800a285611a56a3615876d463325387752a8a0279ce27132000161e1fe0a0581184a4803c602690600e3917816b6b2d27f446f9002de110625116813866601c11f138b859f06bb4b3f05182e0fa5ebf3f4902aa0184003010060f8000d20a01448024189683d12e1f9805831a0811f61d0881045608aa761b6e1a7a890600400480781185a2f03c1f8960a0660d0161514c600d6e398c0b52e037a844b86bb79006bf125b4893bd6293870c169d0184000a28011665e2b04095408a4a3410e6c372a8811f2a3241b01594a356078ee02a9800016480781185a2f03c1f8960a0660d054530906004fe52f89d1002de1e014112bc25a1e0497ff08f71c5926f41e8584a99e8620ba1d1d6b20b84484a4c85aa92c6caa8a313ec368b80005846770ec470266497fd0283204047a8c83406546a0634be06252cfc3da1c64488385ea21460b8125fe5080f4c3e97a40aa83a0c8ae9e0185fcc061000c040028a0525fac045981e3b80aa603c78072098400058241e13613b014818262422c7617fb40842c483434277496465c00b78780502624044af1c00497f91c67200655460b84e4ffc06,
  0x1b70cab5aa2047d3e606d08241c121b5dacb4818471c22cf9d0e00028a0000587e0d0660506225846128ac0698230c026048f60f8fea13a6301ec5bad4b800005846fb8c19168c21307520b88ac3f18210f8fea12205d8fa630026a09ec5b9681beed4b8270b10e52e1aed8c3a96fcfd15650ec9a316522f18b05d35025509c4c86ef80e0e508ecb80e35808a59b0c184c140042144000587e198382d0961184a4827c2b01a10888607c38f4ea0af286557e88a3f980b1d1112b68837b6a83795d03954c2e2fe862fd20641e08665630ea555943b268c5948bc60c169d1916df00a28639985b0d23529b41bbe03839423b2e038d61305000016350340e0b4258922f0462b01a1088460748a33ec60ad1112b61836d68837b6a83795d03954c3b89804631fe862fd20641e08665cb06635b0d23529b455943b3839423b2e48bc61bbe80911b3933fe1e18190c169d1916df0f18173f06b72a10039f011d00a28038d6130506399807884b173b00801316b2d208b3e743800108511b01594a356022966c306000161107e0d1c019814188961184a4f981b1be524a0b1605bc58602e5249641e212d025509c4c8000d0661504a4f8ac1e181908f71c4eeef41e848a0885360875724d068a313eeb65d04564e8dd81c6714dfb200655681be63a4a171605bc1cf5140069d90068cb23c9e5249652a9981aff8761c12cfc02641048289a40aa906780425aac028a0368b80421440a98022cf9d0e0008a59b0c19584695a8d9e8621d6bb09c4c8a8400c6c056528d582004c5acb481e212c000587e0d06605062258461293e0f1817df9681be7d05d071605be6e4ed65249648ace02004c492056c4e53ec320404bea412cfc1acb49460b9a44e7c3e979b0dca40aa83a604d724d054e1dd4561db496e78368b80c040045981e3b80aa60183e0aa2809e739584695a8d822928d043848838525fac985ef406100028a140069c1cf512a998761c08289906780425aac08950c64289c4c800058780a0461293e0f1fe60556371ab3a1ea324a14fb9f06bb4b3f00c88e3bf03df9034043a66c3a18114e180f3f312398c037a84790064893bd0c2041a20c7d874582a667b524203f92a13351512591b3388482214713b5ad9741c537e17812d2fa904503f55a18076b2d2743805182e0f980d0d2580da2e03010541622ba78060f82307c2197a5611a56a365e2b040954,
  0x1110960e983b50be8a57d53e400c200fe46c1084f0106c84103c1e2135d0e01b0c19c057bd460b914ee9381014e860443eae18a4e1cbe558488385ea21bc60dc1247240c040ae9e0329c00610000348144b890b0862110960e84e60e51d57438862ac4942e654a5e71a90700b8d2902e6000a1996a11a8fa1e8940ca7017a881220e0491c92ba780301001840000d20512e24062110960e84e6f18371086c05641e212c8447941a559c4e58dcbebf86a3e87a8c928b014cae12c8f8488385ea20a40b8123d2c66c1908475514ee9380f74da0f44f0d00e8d9a08a59d0e318a1046500fa552e700c040647a9ca8a8ba1d0b8448ae9e018471c329c098a3806100028a000058460b042488882d0620e0082587e60d49dd0a02e4211d50f86cf7438c0898310982c1432542f182f9caac0184000a2801085119982b2628e54b9c091e01c8a29403e93d0063f9946284110c2041a0b6000161f834258460f02c1498338088c1f0cc5e94865c0205b2d0092940069d2a998761c082458001183c0b1d21602260c6920816cb4024a2117b30e3c63d0063f9940c2041a0b6a482e1acb341729e091e01c8a2000d4118140f02c149d22f182f1c0824595cb604a5ef63c9e800058462628ea48205b2d00928845ecc38f1a920b8430810f401ab2cd0682d8fe6504a5aac245fae72ab06260a45c48146c056528d5808a59b0c18042144000587e0d0961183c1981460afc60c2043d006091e01a0b63f9941c8a208b3e12982774380010851022966c306000161f834258460f0660506260a46e5318032a32406bfe4b3f0902aa1096ab2b18254f981b2713207884b0801310611c708b3e743804209070486d76b2d200a281b01594a356022966c306000161f83419814188961184a609d3871916df6f06e9d925b2a3240698239406bb3f18210184001085107884b0801316c3061b01594a35632ad630adc271322c174d320f654d5c537218d3d2315e7484a35f82b1318e5527b742a87737fb9ea8811f4f981b4209070486d76b2d20611c708b3e7438000a28000161f83419814188961184a2b182534774a40146e4aa488607c8460748ecb824aa952fc24cff80e3584c1401e212c5cec02004c40421446c056528d5808a59b0c18f4fd2501aecfc60857e0ac4c639549edd0aa1dcdfee78c83d9535714dc8634f48c579d2128cb05d349c4c8c2,
  0x15aac5ca7804870000583c1f8bc19842616d8550ea5801840000d20a0d448842222f62d02a2f03461652ff590f958092fb2cb9857b46e80235213521b338480e59470fd5150eb94633253877515876d2a8a02798243254072a8852c791911ee91aea5001a74aa661d870209165c81b9a0378398c0379484d81ed612a62e8742e112078ee02a98002241182c0f0787f808615c15b69139f1b16b36c372003a20a0d448842222f62d02a0d07e2f185561441aff92cfc240aa8425aac266fb30133c089509660acac188c64289c4c898a383a960028a000058460d028790661298536055206024000f0580a1fe1181612878614580b06984b099be259827148522628e0ea5800a283190a2713200016118340a1e41984a2b0621b2dd0e31ac04cc225d74205d2c5680910a682685272ab0368b8c209acb0198cab58c8dd8d043aee14bc8c1f0865e89c4c800058460d07e79066128ac1485259241caa184a98bcdc88ac00ba1d2084e7d2a998b883128056c761c1a05f746cf708289918cca200c1065da4205d2d4e1dd4266fb30133c368b8061003a960028a0c209acb0198cab58c64297ec28c8dd8d043aee14bc865e8aa2809e7389c4c800058460d0287904a2b01a0a984b60541aff920047d2cfc27c1aee40aaafcfd0425aaf30133d22e88089509660acc6429460b83e611cfcb828c5b8e6300dea1026410c9c4c82c6503a96098a3806100028a000058460d0283f83c6127a22b180b3d3f406bfe942e64b23e0b194000140d07e3f8584b83e611d6ab0217612b180b3d828b0990433410e318e552c174d2713230adc0b19432146328267791843092aa54a5e2902e19ad27181310696d70184000a282628e27b742a87737fb9e04983d7438c00016118620e0961f834081845523a63004a602dec5b82604ad4b812eb9afcfd03c0192257ac6c056528b0208a58bc7d030c798ab10646104841b94c60fc5c322424aa95297898a3804214400058460e0961f834080780f9e4610d80b0f204099e61a20c271320b1127d8742204115822a9d86e3869ea000161187e1e03e6f0646105127d874129325822a1697bf869ea242b82a0ea00016118380d03e7914c60fc3f91501337009dd7186d7000628e03404983d565c92591ca83a9a4e3996509dbc1b9428960da24144e60e40c04000348144b890b0862,
  0x1780425aac08950c6428ac61dc06100028a09c4c8000a03a11844518161286224187ba41ace218002a3847546ace85ea218ab11c02e367cb6a50b98647a8fc3425ca8aa8c5b8ba1d0e6300b8448de520fe6500c04034960ae9e0027c152978488387a8c83204052c8f898a38a40b8000a03a1184451ba2188160b1879a41ace218002a380fd46ace90ed4ee5380f767cb6a50b985e44dcfcb813e29108ff28c5ba200c078602ce630026410cdea11e461d57ec28d0438c83d94b05d349c4c8c2b70cab580c0415058834960ae9e0027c048838dac107a8c83204052c8f8e8d98f0d015297898a38a40b935714dc8634f48c579d2128c000a03a1184451ba2188162b04a61dd837532b81918733f0120a9be1618710d2582ba78009f054a5e2628e2902e3190a27132000280e84611146e8862058ac129e461d4742e20c5822a681e6869ea000460585a0986461cd6df240b8d2a02a36817dd423fc880301e180b08174b2628ebb852f32ad630adc2c174d320f654d5c537218d3d2315e7484a33190a5fb0a3410e27132000280e846518d218816af2402b04a7905861c58071220e00028e8ade1104e198145a062191807120d273f0124928214a143410e409543fa84271320b14800028e8ade1104e198de09890071cec0ca80de2301494e6300000e84411a06350f42b3a661ad94790061296ab000bc108f40f186907dcec0c984a9a30154cba1d0000e84435206118302b1f6619c4238206f1700b8d2902e018402ba78060f8000d20a03a050922402a1894661943df43a66c9406bb420423a8b3a82139fa280a4a14fb0c81011ea324b3f09018613a18114e180f4503f52fa90743806b2d203010541620d2582ba78060f81220e36b0401840000d20a03a050924b82a189cc06866618e6c423fc3c3400010fd0eabcbc81a43b50e543864061856494633222b00538775612a61e18574aa66390d815876d2a8a02e8741d870279822e11220916129321690a43254072a8002240f1fe02185ffc098a3a4c0404e43621e53ec565034bea402c289acb4a40aa906780525fac42616c641b654c506448055d460b9a44e7c3e1bc5b0dc8061000c040183e0028a000058280f02a1387e2f185d360568084660be72ab08c1f062e00865c238cf9009283831d430810f4018981a9c682d8fe65152e704a,
  0x161851411045e05fe74f1c460171c3c0c04150588028a0e8d98f0d00da0f4742d600e3584c1418e660045981e3b80a17540005844af03a138660fa408021e5110e52a2c2622d82f0217992b030099be25988769163717a86700b8721161f532b8010dc191ea1a81294e03f103af872a2a3683d1123e21ea327186cd8e06cf0917eb9caac911ee2e87432274398c01d8702c23432a4854a5e4b23e3d979f18987991aea2e1121a0b637948209161c8a22902e1298850184003010541625f82b13082b32ba78060f82628e0d25800a2800016430460a03a5198891085b0b009257fc028a0000a03a118160f95c7b1a116f0a8421282598877b9a111e4e46e42881efbb20b7ec21c469e4d4e74d1106120b359638d46cf710ed6186200c22c5c9c78602c205d2c3c620c1e3b80a1755380fc4845f8c26852381b3c245fac626206ee14bcc8dd97ec2902550c6428865e8d0438b05d349c4c8c2b70cab5950588ae9e0e8d98da0f4552978a40b806100028a098a38000a03a11844518161298855aac08950c64289c4c800128420f1883e21c6a42380fd5800290ed9b05e44dd0861fc6ace9380f767cb6a50b98fcb828c5b8e6300dea11e4019224a843081068831f61d1608aa1a7a89061ec425aad78ac0089502292804870ac61dc0c0415058834960ae9e07a8c832040448f892c8f8e8d98f0d00da0f4552978a40b806100028a098a38d0438c6429025509c4c8000a03a11844518161286262040c5859001db86733aaeea482e1acb90a6d5ee6844793592202a10a3250e37a207be0803f9b0870f74388238ab9170ac7805417f71812d73187d4803e706bfc07884d54a5e1ea320c8101123e24b23e2628e2197a13050073d44aa661d87020a26419e0942e61ab3a9f2da3f2e0a316e398c037a84790064892a10c2041a20c7d8745822a869ea08a4a3410e5e2b040954022543190a0121c000280e846110160f85a1883c0906442187f3c2d865dc6a04d06e4004e02a5d7c2a248e2ac5042a3c9a2a8c5cec164880a8428d80028204a6c0c04034960028a00e3584c1401e2134000a03a110168021e512b435038090ec19088a29081e13e73187d0fe5d0e2054497dc6a41b0b002a133d80029a458ddfe61446a3e81e21341a463c5ea218ab114cae1c02e340c04034960ae9e07a8c832040448f892c8f8a40b898a3826410506,
  0x10f98914e18976f0943a08d500a282fbc01a80ff1781035a06f9c581653c3403683d154bf0932322628e6c30651988900016430460a03a1e89618924e429b57bbb25d56a04d1a111e45fa0e157c02bf6a08d7ca19674c195e9eaf0fa3ca9c1724945b1865dc54a6d1d3f010c3081178ac06e302c089505c2b04e02a649a2a948e2acd042a444c1400e3586c45bca84cc64e59f4544964ac602c0459a2c0906120885205fd41ac001ee491cb301cf504262554039752a9991808f536087590086d720865c2085c761c2f41e86b65d04825d4de86215846868831d6bb15a8d902550564e8c225dbcc83d94b05d349c4c8cab582c44935714ddf61d08634f4aa1dcd608a88c579fee7a1a7a9d2128c265d242a4e7c901b74521b2cbef0128053dbc251ac049e4c8ca00624e8a313ef14df9d81c6d681bec6a236c5e23a676f114670b10b5b01066761015d00fc6fc0f74368b8061000c040c20acc98a38183e034960028a1466224000590c118280e938625d4411e180b010dc0f188303af800016050440e84e1987a188961604a1098955e64682d872288bc3cdc4a5dbc38348f480dccfad8294a6d06e18ad8629fdfa2985a229ddaa29bd74299e6201f6a04d0e02a5d7c2a248e2ac5042a3c9a2a8c5c2afd8e6604c140043700ebe0245fac62b48266f9c6a4096d5980029a45c140c040183e0349603223845e23a44823cc6a236c028a1681bee70b10b4000590c0a03a199388018935a842a1bc4521b3c6a236c5e23a5b01065d00fc50e5623c7a8c92c8f80c04098a38183e034960028a1466224000590c118280e83e62466c42187f4518c1096ab1497e3099617271320b1120a86ef7d8744a1419022545822a6f06d92b16df869ea24161f2a188d03010541622ba78060f80d25800a285198891ea320c8101123e24b23e3a3663c3403683d154a5e2628e00016430460a03a0f90e5623c6db62840d242b87011376f2867300a1a817b2f81778054709b0988b03010060f80d25800a283a3663c3403683d1000160a2bc0e8660fa408021e5110e52a188d3c9a818949428c65f90d6f98829fa28adaa28bd7428b56c28a4e89ea2be0cf7120cef3c0ce5f40cde4a117bc2e5c1d4a6d24e3c2c6e18ae1210d4540fee6842bd862a1e6201f67091bee381b3c245fac92108ea04d1241bfc62b4a081bc4e02a5d7c2a248e2ac5042a3c9a2a8dfd1058dc6a4096d5980029a458dc6a3e85c57b54cae0641b6d8a1035c09b01a,
  0x17498310e3c6091e00c2043d0060121c2b030322740217992c23432a483d979f1a0b63f9941c8a200a285f82b13082b32628e099be00016430460a82c62a73aa280a9f06bb0c88e3bf03df43a58a52fa906b2d21e98a34e18975198891f985d17a881220e0d1859060f801840030102628e3f0d09a316e398c000a2837948a482e1acb34191ea72a2a2e8742e1121729e14aac7498310e3c60c204091e00217993d0063f9940121c2b030322741a0b6099be5f82b13d979f32a482c2341c8a23082b300016430460a82c0a18a74d10402457c01fdecb18ce6218866010dae5f90d6f985abd860dfe58b190f9a511c8e2adc9a547d30ee21e53ec6a05472c198da44e7d5658e5b0108c20151c09b00c04150588e03cf40e3586e436438f184c1406c5accdac10ae9e0183e1140fd5d0e00e86044bea41acb48346164488380610000348140a8bc35122222f6108b4188287303a1990e543a58a55acc24782920b8430810f4018ac0c0c89d0085e64b08d0ca922b2cd0682d8fe650722884a62845c2b04f6f700459892108c1e2135c09b01a6185141076084e7c266fb30133c96627cda0f44f0d0152fc0e8235528053e4c8c806101505897e0ac4c20accae9e0183e098a38028a146622538625c000590c118280e87a628d80b0f1851000460a0581e0167f84a6285f40c01f7022a83b128d0896cb1503fb612a67015ef45137b9abc42e874191e61d8702307cacb342e1121a0b620916398745219701293a9a00384021416189d8e06cb0917eb9caac189242628e060f80d2584e18976b01276f0943a08d500a28a304893f06b79f011351988900016430460a03a1e896627c300f182f322740217992c23432a483d979f1a0b61c8a2129685f82b13082b32ba78060f84e18973a08d500a2854bf0932325198892628e9caac010dc03af80917eb1892400016430460a03a1e89616189d618478602d146303c620d50588028a0da0f440005828af03a1990e5438640258421604a5a20a5d039568837be0866dd21711dbbb8b3809da81346a83897e83855b03835f00aff28659d30657619771529b43e8f20c2041b8c0b250e371a20c10989508976f099617271320b1127d8745822a02254869ea2b16df170ac1380a99268aa5238ab3410a916399813050038d62406dd2a324011669d925f1b042107884d080547026c069861450b7f541622ba78060f80d258,
  0x1958b08d072288c89d0682d84a62e4000582a108382612fb8612ff590f952cb9857b46e802351b338480e592135206b0007b9202b08471649150eb90718bb4633253877515876d2a8a05001a727982852c791612a6a03784aa664318a90da2ecc04cf1d87020916398c0379482e8742e112911ee91aea1298b9000160a8420e046053c60c01f73d01c7022a8010dc03af8000420e2226781c62ed7dd1a20c3fa847d874e98c0582a67b0e5b679649f793bb0718b74d822f0898b5852c791911ee22b0091b9046332640e61500e5d4aa66ec82df5387754792731d870a79353390d820a268482cd658e351b3dc07ba415876d4190258b17271e180b08174b880302a8a0099bebb852f323765fb0a40954279ce3190a2197a3410e0f18832c174d2713230adc32ad60da2ecc04cf000160a8421298b9f808ecb8e0e50ea40b408aa04c1405cec0043700ebe0001085a3d854068460e01c62dcd171e81271781031a80ffc587070c92b92f89d17186d79306b30a18b34937ef417419b8225630f7b0c10313800831b90d92ba789891fb171205a48239061011022a81496e53b2cc74a9a5c81d16b975d0301000a2813050010dc03af82307c2197a099be5611a56a361b3dc3190a8482cd409542628e500e5d640e614792730da2e4633253877570819f22b004aa664d822f852c791390d815876d2a8a0279ce27132cc04cf000160a842128f61501a571a110898b54e7db0dc928056c3a9604e62c406100525b95d2a69ae5d74266f8c6428368b8e4360561db4aa2809e73b30133c8c1f0865e89c4c8028a0000582a12892088bc111785a02862cd1212902e0e988519864030101220e2628e0184000a28000161284608862111785a0281398b10745ae5d77de4eec385f7c1cf50cab58b05d352a999403974aa2809e7389c4c800890c1911858128ccc70ae51515c470ae90918af6224661907e6174346125e4019224ef43081068831f61d124df960a9bd05d059e59266e4ed48ac007862841262ac1cf51724d054039752a998761c08289818471d064d34525fad78ac02292842620c0895004870368b8061000c040028a098a38266f8d043902551584695a8d8561db518cc94e1dd4aa2809e7389c4c82c62a730133c000590c1182a0f18ad5ded281bd4000582a0f0241101262ad6d11501331e010713959106010ba796d37186d79306b30a18a714aac,
  0x166118cc8e03cf41e3b80ac214a6d06e43644c1405c4c9c043700ebe00089042089dc8899eda9762f088082f64e98d90ed79882a61b1a2daa22d5fa22c56c22bdee103958e6614a6d000352f63a93a250fb52698d74d10402457c01fdecb18ce6218866010dae5f90d6f985abce03cf530ee32c198c8e5ab5740e57821995563c9a832454a6d18e6606e43644c140043700ebe000108222f0882d2f64e9228598d55ab57422f6423d0586634454632c9a47fc1a3ded78ac102fdb7a46a5cc626e63248a4b81c077540075d36c3118b91102c88c1f06e4364865c2920b84308105ca78f461a5005cacac0c0085e64f65e7c266f97e0ac4c66085a73a7e281f21db44c140043700ebe2b2cd0ca920c2958b08d072288c89d0682d8008902a7f8420b0221598d3039dee31a36425ad4fa3c894633c4c1406c5acc04370e03cf49a47fc0ebe000108bc488b4222f63a98c1e0206198d16e0b201ad6400de18015dda014d6e0145dad181dd1d1715dbf17aef06337a00edd200dbe61b1a2e60318ce120ea5ee1039ffa025e5d519de425b1de7f15ed181e3b80aa6000fe0bc488b4bd892630788582061894633fa8af8343cf03157d02fbc38327c48323939c603915c5bf931c59b91d45d39a086fab8c9374fc0439391672c8025763d127779fcd0b5857b46078ee02a982a1335000921e0209493ea7af063343a99498c397546774e8fc559639380f3d2691ff1b90d913050078ee02a98068f7b010dc03af800042088bc488b4222f663054632ecc64021b5c821970821700224c70ae92bb4ec4726e6325344100915f007f7b2c633988621980436b97e435be616af2396ad380f3d4c3b8cb0663268085d0395e086655596391b90d9130502a292010dc03af800042088bc488b4222f61513a3f1344100915f007f7b2c633988621980436b97e435be616af2396ad6198c38498c1268085d03954c3b8e08665cb06635596392a2920838a07b923d1869380f3d0c2041a0b61b90d9a482e1acb3413050010dc03af81729e000420b022158bc0f1ae2292e0dbd3e496660318cc1a47effa025f1a021e423cdd043ce7480dfc043700ebe000108222f1222d2f6e11421509485a526198c30ea53a5ab65d519de425b178ac102fdb7a46a5cc626e08844c141740e57821994003502c158bc0f0b43a88a252168498c1810885e74ac0c0085e64f65e7c266f97e0ac4c660a7e281f21db4cc3604605330133c043700ebe0ca920c2,
  0x162e438260368b8000582a108bc22020bd87863ac1071395919306b300a282628e000160b046110780498e9cea8a02a7c1aec7a2a2c32238efc0f7d0e9629538603c7ecf8bea41d0e01acb488754d1460b89a5b543e47c45ea20dac1048838346164061000c040e03cf5043e0d740dde58b0df530ee32c198c8e025decb18cd563c9a818dc6e43644c140043700ebe05c4c9e6010dbc003482a108220512e240bc2202011122bd986480620a18e71e868a313ede8621d85b0dd6b2052ab2c60ba5d257a6e20c0269a83461641256a4840e3fca19575c0917e602c6644eb444d08e039c9a039530ee1ee31a2d7c5adf2c198d563c9a81a3e6190ede9e638cca920c2958b08d072288c89d0682d898a38fc34268c5b8028a0fe650647a9ca8a83c0af4e03cf4184044f60ae46c5ace6e08958c63453a63646e43644c140043700ebe05c4c9cf4071cec397c8a636e14b1e46447ba46baa80de140069d18cc94e1dd4aa2809e6090c62a572396ce6300de521c2067d2a998761c0824593607b584a98e436056634c3826330133c368b8ba1d0b84484a62e4000582a108bc22020bd8784f98e54bee184bfd643e54b2e60846384269a8346164125b4c028a098a38647a9ca8a81840455ed186c5acc1e3b80ac226e08958c63453a63646e43644c140043700ebe05c4c9cf4071cec397c8a636e14b1e46447ba46baa80de140069d18cc94e1dd4aa2809e6090c62a572396ce6300de521c2067d2a998761c0824593607b584a98e436056634c3826330133c368b8ba1d0b84484a62e4000582a108bc22020bd8784fa9e638c0a1e8ab30c8ab71a8ab51fb3e2fa90743806b2d25182e0f91f117a8836b041220e148bc909344100b14c3b8d30655268085f16b7cb0663558f26a065996a438f0184003010380f3d1b90d913050010dc03af81713275d0377962c37d000d21082c08814240bc22020112f6618924f828138582118e146a5c5d055a3ad714df968191460b83e47c45ea20dac104883852850d0b08061000c040028a098a3800058221189008044ad828138269aaac7496cb188295000160884608026342c24bee184bfd643e54b2e615ed1ba008d484d4920070c1ac006cce01e3b80ac20007722267b6a5d8202298db4bee182927a008d484d4920070c1ac006cce34444ad1c5927fa18bc1c071d2263549a635c8e5ab5740e5530ee38219972c198d563c9a832458e,
  0x10e0981298b90da2ecc04cf000160a8422f088763720e8ab382139f8000a4a14fb0c81171ab3a9f18fb4e180f03010010dc03af80d18f51220e01840000d20a842088144b8bc22044bd9220a08e189cc601926294f00f7c7ecfa501aedd0e01460b83eb6806100043700ebe05c63dc003482a108220512e2f088bd9220a0627310e59f18fb1f0865c19c5ebd00850582f0028a0368b8ba1d0b8448000582c088142105263e4e73078847000422f0881718f739ccb461641e212c043700ebe0003482a108bc222f6488280d18f51f0865c19c5ebd00850582f0621b5dac04cca856a44e5644028a0368b8ba1d0b844898a38184044761c082458000582c088461501c0498f308e6f6258ec397c8a636d72396e80de0e6300de52214b1e46447ba46ba9c2067d40069d2a998761c0824593607b584a98ba1d0b844918cc94e1dd4aa2809e6090c62a4e436056634c382604a62e4368bb30133c000582a108bc2202063c4f83d11344f811d26808a886c32a15a91395910a02a4c3b8cb06632380875f007f55943b9891fb1e18eb5d0377962c37d4e98d91b90d913050010dc3f0d09a316e00a283f994380f3d03af81713270610113d01c73b0e5f2298db852c791911ee91aea5001a7463325387752a8a0279824318a95c8e5b70819f4aa661d870209164d81ed612a62e8742e112a0378390d81598d30e098cc04cf0da2e398c0379481298b9000160a8422f088082f6258fad6d96c92696d57a1881220e75ac814aacb182e97495e9b883009a6a0d18590184032a4830a562c2341c8a2322741a0b62628e3f0d09a316e00a283f994191ea72a2a0f02bd0610111b90d9130503d82b91b16b33d01c79b8225630f7b3b0e5f2298db852c791911ee91aeaa03785001a7463325387752a8a0279824318a95c8e5b398c03794870819f4aa661d870209164d81ed612a6390d81598d3cc04cf0da2e2e8742e1121298b92380879891fb1e18eb1713270e098010dc03af8000160a8422f088082f60a02a57a672ab0269a862639c3461641263a53e63966e08958c634498a38fc34268c5b8028a0fe650647a9ca8a8184044f4071cec397c8a636d40069d18cc972396dc2067d3607b46e43644c140043700ebe05c4c9d3a63654e1dd4aa2809e6090c62a614b1e46447ba46ba984a98ba1d0b844a80de0e6300de5212a998e436056634f30133c761c0824584a,
  0x15e8aa2809e739584695a8d9e8621d6bb0761c230144482899064d349c4c80005824128582b190f1b654c3a9460b84e4ffc3eeb084f08dac10329c09012e468830989ea1a1d75f61d2101cb5604d75dcf52fa125dd2128caa2809e7384845241240e42a6c99213ee8a11e65e8621d6bb124dfbd0f91584695a8d80c040525fac06100028a000058241695c06a3a3dac21584407190d0286a06347a8c85e04b4bea4034609fda1c652cfc1acb49460b848838128c03e979140f3d380f2e40aa83a0c8ae9e0184d859213ee8a11e875c08f71c62bc562dcd3608bce211cc8ac001cf5140069d90068dc2067c329c214b1e4610b612a99898a38368b8061000c040028a02a6c8525fac8c1f1584695a8d9e8621d6bb0761c230144482899064d340459a447ba46e43b20b7e9e4d4c6cf70c64299638d41ee92120b350255078602e2c5c9c205d2eee14bc865ea200c17ec28c8dd8d0438cab58b05d34c2b709c4c80005824128582b046642c791da822f911ee2ba58af91b9022b00ec82df4aa66a793531d8708482cd658e351b3dc07ba420a2608174b880304190258b17271e180b0f18ad099be5fb0a320f65409543190a3410e4d5c537643ae463322c174d2713230adc32ad6218d3d5387750b19052315e390d815876d2a8a0bb855b2799077484a31497eb109903cc04cf0da2e000160a9b20c0f65e7c266f97e0ac4c89d03c780b08d0c2958ca920c6608682d8722884a4c85a738000a82427990764054e1dd4561db41cf50aa2812a9989e608761c10c62a482458368bb30133c42640c000582a1182c6415d80c01f7022a83b19015387752a8a027982612a64318a9390d81598d30e0982e8742e1121298b90da2ecc04cf000160a842640d8db471649150eb9a0378398c037948612a62e8742e112852c791911ee91aea5001a74aa66390d81d8702091646332002240b0cc5d8ec64042e0f97a719ad20c810171a904b3c06019217a8836b041220e1498f990934268085f009f4c3b85d0387410f39b38643cb066396a438fd2037f5596394e8fc1b90d92a2921718f70498f33d01c7a482390610113b0eb90818f1380f3d0184013050010dc03af82628ea0378852c7915001a74aa661d870209163f0d09a316e398c000a28379483f994191ea72a2a2e8742e1129abbeed0793911ee91aea463325387752a8a0279824318a9390d81598d3,
  0x15c242e00084565d5e399d9631c53e4966126475b845ac125ffc329c02a6c806100ae9e00c040028a1de7f01e3b80aa6000058621116876054050788003a1b192364747eaa87a8c9529792c8f8a4647e524b0c92646c125ffc329c02a6c806100ae9e018471c525fac0c040028a01e3b80aa6000058240f0385a1d815156050788e9921d59a40565460b84e4ffc06100028a02a6c800058625a1d8050281b0a4647e6c4204354504314e17059c247034a14fbc593333c3403a3662f918154a5e198642913ff0d25803010541620ca700a9b22ba781220e36b040184000a2800016188445a1d8050281b2128003a64744359c24703701137c5816b7319191faaa3c3403a3661ea3254a5e4b23e2917ef59005b75ac5f1ab800a70e8d948ec34f92856591252c8f272a32457b46173b00121c1220e36b040497ff0ca700a9b22ba780611c7030101497eb0184000a28779fc078ee02a98000160903c0e16876054558141e23a24991b10d67091c0dc044d71638e4be645c0c04018471c34960028a000058620f0385a1d8558b487abc0a142512f284a4e0fa0043850e90e9cc6464a857012e54e8f0b3e8f24503f5a81341b8c0b743881ab3a380a975f0a89238ab1410a8f268aa371a909f01110a9b2038d6130500121c0611c70d25800a28000161883c0e1d8558b4af02850944bca4e0fa0043843a730be645d125bc0ec32c8f272a32406991304903957b46779fc02a608b02418482211b33807b920301000a280a9b21497eb000160915c110565da6ed7168760542299150fd50ed4b95d0e206ace9c6a427c044580344c5e44dd08ff07eaa8f0d00e8d9834ff87a8c9529792c8f8a40b8666444dac1048838ae9e0329c0989ea101cb5dcc0006100028a02a6c8525fac000582457044159687608a0a01a644ff0902aa933fe0ea5813918d030100a9b21220e1497eb0184000a2800016090445a02806814199911ff92cfc1460b84e4ffe40aa83eeb03a0c8dac10329c0e211cc989ea101cb5dcc011c2dcc1c64344845241240e4184d859213edc2085d24df940075d90eba8a11e66b6c63d0f91102c94e710cc36046642e6a4d6646e43b20b7e9e4d4c0459a120b359638d46cf701ee90205d2e200c22c5c9c78602c368b8061000c040028a02a6c8525faccab58c2b70b05d34c6429025517ec28c8dd8d043aee14bc8c1f086,
  0x1099e6322743d825b0f1e02c23430a5632a48330d81a0b61c8a21196d31297370c31e0e38c00a28a28c4fb000240581a648127427619212a787e64f509d24815b07884b8e8ee51501331394fb1201571e814f1781031a80ffc807277186d72f89d16938e9306b30a1939030100ca701497eb0a9b2018402ba7800a2800024058440501a76193bfc1460ba40aa83e8f83a9624cff84e64dc06100028a0000901611014069d80a193961847eaa952fc24c8ca0058dce860453811446a0635140fd45e04b676d1c6fda1c65d0e01acb49460b83e64d52853ecbe058f1664cc0c04150588329c02a6c8ae9e16864c448838dac10525fac06100028a0000901611014069d80a04e64dd3aba280a43b58611791374e1705423fc1faaa3c3403a3661ea3254a5e4b23e541622ba7836b044a14fb1220e0ca701497eb0a9b2018400301000a2800024058440501a0a04e6003e64d46ff291337000d218814761240a04ec599330fd50ed4b95d0e206ace9c6a427c044580344c5e44dd08ff07eaa8f0d00e8d9834ff87a8c9529792c8f8a40b8666444dac10488381264bc0c040329c0525fac2a6c806100ae9e0028a0000901611014069d85a1931427492056c5404cc1e212c4e53ec48055dc61b5e3a40e4be2745a4e380025862b784487abc069d85a01264bd77f1391930a135f030102ba7800024068d225862111d85a01424192d53ec48055cbe2745a4e38284ffc0c040329c02a6c806100ae9e0028a0000586211168760142904e64ac16b7f447037319199c2c435592209492594813c57021e6199273f2e0a3170b398c037a84790068881c74893bd0c1925869ea24161f2a3241b19230d2581faaa3c3403a3661ea3254a5e4b23e2917f78e992136b041220e078ee0497ff3d825902a9803010541624d7cdd5022543190a5e2b040954038d613050250e37173b00121c4f3500ca700a9b2018402ba782627a84072d773d43b0b732299156484fba2847994937ef43e4bd3ce7a18875aec5001d7440b2643ae539c42a8a0279ce708217adb182307c2197a5611a56a360da2e1d87020a260611c708a4a3410e1497eb00a28000160905a1c83c158541e1929544ce0020c8e2735300636e19ce6218b5a20ded4a0dc4ea5dc7480dfc00090bca1bf8150b41e08422186649c742e20c582e8682046781f70005a0f056071ca0c192538fdd6917b564,
  0x13190a08a4a3410e2a8a0279ce5611a56a367a18875aec0d9745be8881d8702307c2197a26195320a26419e027132109883008800121c0001a0f04a1619265678871a908e03f560113543b52e51791371ab3a423fc1faaa3c3403a3660d3fe1ea329f2da54a5e4b23e29195536b041220e04992f24192d0ca704905750a85633f05291493194d94cbf05993b2ba780619510184003010279ce56a360001a3485a0926416014223a676195710443a962761b6c4e4ffd460b8061000034814221d818968190282919552dcc8ac001cf5140069d90068dc2067ccc3612a5c04465ef63c9e8a632fd3671455584695a8d8365d16fa220761c08c1f0865e89c4c800068d212824c40582619531c9fda066c283e00034a64760186544cbf0584fb4d9c58d000d2a75c58a28d92653d12b3800c32380a74100814c007dfe862fcb0663e6863fc6861d003f8090b40e0bc3d09465340a7e6863f9096c559947268c591b99496199450c204a482e11a20cacb907d874a6d5ee5822a6844793390d81587997a1885e2b075aec409540215b32713230adc32ad60982610b0a22c028932376419e03402912b194308993f1f993da207beb08715805c183e805fd76bc06bd29b8948e21869ea86002759001f5b8f8d2406e576345934f8e6962840d530ea17108b6399813050038d6768f070b8e6d211597578e6701166779fc02b0824815b658a057009dd8e183d07884b8b01951501331394fb120157f687257186d72f89d16938e030107fb9e0ca701497eb0a9b2018402ba7800a28388473840475a28c4fb76193b00024058440501a04994b41249a0315ee11a4f6e19cc00fe0b42f2f61b99495dcc9a3164fa3c80e358008e8d42d0383074c21163ee30645aec9a0bd8884e9563a994732ec8e029d304405e9d19ff9a5c449a3164fa3c86e3b35740ddd6c0e0c9419dda2119aa0d65fa0d554a0d4658b0df7ca0e365d70ea65f90d7c000901a080a8a1bf83f14b4848382f18c221866515321697810b2ea7d874a6d5ee5822a6844793390d81587997a18875994100a286938e0a9b2869ea000161101aa28412193b42b19430c17e0ba426798c89d0f6096cb08d0c2958ca921e2b20682d8722884a4c85abb000068642b1d66504b22307c330d86b81dd21972d11933d3b032099e68c05111d8700f1e01a0b6209161c8a212973700024cc044819923506484bb40e82264fec8b182e9a75d88b88307e0799,
  0x1020d7c01fe6265b50403bdf011a5530b898c3a948e316c9a3ffcf4018fe6515650ec6efa05ca7830810682d824780722884a65844c1400e35804870000683c0e26465be0a61835f5d03575b089dda062121d4cff63998268fff038d63d0063f994529b46a837968837bd206414100ef7c046957e83bb98e469755943b1bbe81729e13050091e01c8a20121c0c2041a0b61299610001a0f0389926265b4ea555943b239309268fff1bbe80899695e2b040bf6de91a97196522b005001a770819f099ba640cbd4a9701050475038d6130500121c1d870209163d0063f9940c2041a0b61729e091e01c8a21299610da2e4784c17fb9e0a9b2330d80001a0f0163921065ac35fda06214e96adc680879094396dbd278ac8a75d887e3ced7023ff7acc4db0c5d056440b297546772307c2691ff559639219701b964f0816db4024a038d6130500121c3d0063f9940c2041a0b6a482e1acb341729e091e0072a846332539c42a8a027982432542f19675e2b040bf6de91a9719650da2e099ba1c8a21299610001a0f016158982b94add2bb51c0899693dec385e74c60af40487030810682d85ca7824780722884a6584000683c1618c2f19673dec385e74c60af578089408aa0ec658eb6c600487030810682d85ca7824780722884a6584000683c890562b94582b74aed4725c6596542f3c63198208a4a9f8a0341707c9c4ad07c5d93b5670b730121c091e01c8a23d0063f9940c2041a0b65c8219adb180003c0b224158ae52b74aed4725c3b19632dcc8ac001cf5140069d90068dc2067ccc3612a5c04465ef63c9e8a6657c14098458656c365d16fa220761c082899584688c1f1067815a8d8865e842620c9c4c8000683c1299612dcc8ac0140069dc2067ccc3619032f52a5c0446b623c65741cca11ecd8365d16fa22000068246725c570a6657da64f046f38847347b360001a090a68f195da11e401ba6655d224ef43081068831f61554904d7c1264bc329c12415d42a158c524c6536532fc1664ecae9e018654592656498654c061000c04002200048709e7395a8d822928d043808950c642978ac102551b6f49e2a90828990678042620c9c4c8000683c12858656eaa54a5e0e98892902e1999114937ef417419b821d2ba53bb22b00073d446023d04994b4aa66bd07a10611c7640e61500e5d5c9341390d81497eb1587994784f5298cbfa28d94f4d9c58d01840,
  0x15c1009284a6584000683c89056088bc671344100ef4c00eb5f007f380083238087003f82d31a859f0323005b93967b75ac5fbbc13538483a997546775e197d7a740cda81447b3864357b46d2037fe802358b02411b3380838a472cc5c823f130500121c1729e462e44db0c5001d70701dd440b22307c219704024a70822d779fc07884923808798862197e435f091e01c8a2129961643ae0001a0f22415822da986252165db5c65ff189b82215611a9483ab56bf6975c67988eeb00003c0b05661894229e9f5e197defac265dfb41e3cfc5c3f6a08c5ae075e2206fcaed65948ace0920e7662b199f2c544d3a3234e0020e6265e592653e8a11e65e8621d6b22c6f4a6465bdc2085d24dfab6c63d0f915846990eb95afd94e71223bac130b88aa2818c3a949e608260b055650ec8e316d0c9509a3ffc6efa0bcf180e3584c1400220004870f4018fe650e6300de52030810682da447ba46ba85ca7824780722884a6584368b82a6c8cc360989ea1065ac000683c058e40e197b0e14fb182bca1955860d7d740d5d6c2277e602bf68188487533fd0402058e6609a3ffc0e358f4018fe6514a6d1aa0de5a20def4819055650ec6efa05ca784c14024780722880487030810682d84a6584000683c0e26265e54fb06010b2fbc00d01971201930c818f6938e9306b3c807270a19758b117b2c8e4dc3831baf8301948e2191545b993145950b8006e0c976585c757804186003f5900377474c519a10af48036f24839d210cfd980c633779fc02a6098ac667f980b1fe809108037d078849cb1513d11344e8c8d3800835f007f03010008800a9b22f3c6d206414c2e2630ea5238c5b268fff3d0063f99455943b1bbe81729e0c2041a0b6091e01c8a212996113050038d60121c0001a0f016050385a1d84bac2c6997723e6f29b14438e51410c4e810ac5e05ad3811450810847ea58f0106c340564bebfa7091bedfd11be676d1c6db0c1928d59460b83e65cc6265c4ae9e0183e0061000c041505882a6c800068d2058140e0085a1d84bac21b2120a19754b947ee311411045e05fc6ace908ff0da0f44e8d9834ff848f887a8ca381b3e74f1c460171c3e7cb69529792c8f8ae9e0183e000068d2258140e1d84bac20a0520f9973b0208a59a458dc3a64745e05fc6ace834ff87a8ca0171c3e7cb692c8f8a4647c48838061000c0402a6c8183e000068d205814021687612eb086c848281899714d0e0,
  0x1870000683c058e4761686657382496514713f56d845d612e89db4723869eac8018d240c3da296372f81114a2c0a886c12691ff822969403e95e11210da2e0a9b20701dd643ae1ea324b23e00286b7922582f62d01615814089ae18a1e021763a894111d85a03e510fc139cc1f9993a59b0b003a6185a458dd1411045e05fc6ace9380f74e8d9834ff87a8ca74f1c460171c3e7cb6a50b99529792c8f8dac1048838a440fc061000c04150588ae9e000068d22581408862020445a2c24b8286644f4b0a0f84209153689134509113c090f4e090d3a090b2b890903010000d21081406198f544c8e5ab4e02a5d8044d45e44dc7e44876e199d08ff0f0d00e8d9834ff87a8cb820e5d529792c8f8fb9828dac1048838a440fda20d6d740d5d6c0d4c1264bf681884ae9e1fa0eef1a2313003ac1865466391a5df011a55b6f49e2b229d7621f8f3b5c09063a662c9a454fa008d46cce01ee4a1208851c658c205b1eb6c61584695afda23bac18c662586661dc208b44c1418e6600c04140075c1c0775102c8329c052ab1d28088c1f0865c100928989ea1065ac2a6c8061000220190eb94e710aa2809e6090c9515650ec30810682d94a6d06e593cbc670cc360368b83865ec5ca782478072288f4018fe6504a658404870000683c058e476168da998d016e4e59edd6b17eef04d4dde7f15ed1800068549494224a9e8e998b2fb66821be524d4d96181ddaf019e4e3c2c0a9822c0907a008d46cce020e281ee491cb317208fef4f39e8621d6b22c6f4a6450e6a032ec8e5ab5741589a47fe5d519dde9d19d40e3584c142920b86b2cd05ca7918b9136c3140075d90eb95650ec24780722880487030810682d84a6585c208b4000683c890566b8ec5d8eada93a631989b229d7622c6f49f8f3a6450e75c65fc9a47fd7866146e18ac8e021e6218840e3584c14004872920b86b2cd05ca7824780722894e710aa2809e6090c950bc6704a6585c208b65f90d7c000683c8905608b6a61894661d4474c00cd269153b386437a7d97d1b338d2037f4719630816c75611a56bf688eeb0130500121c1729e091e01c8a25001d70701dd440b22307c219704024a643ae539c42a8a027982432540003c0b22415822020add61894908ea5e198546a5cc615afda6e632623bac08a4b98c3dec0487030810682d85ca78247807228918b9136c3140075c1c0775102c88c1f086,
  0x1050460d19a9520484565dbc1b9492056d962814647a84e5645ca8a8e4669448055da4e380c040ba1d0b84482a6c818663c24780722884a65840220004870000683c058140499a77a9caba0901b959e4fd54c52048ace084565c92056d9628144e53ed90eb8329c14e71052ab0aa281d2809102c89e6088c1f10c9501caa0865c0bc671009283865eccc360061000c040ba1d0b8448368b8be2744ae9e018663c24780722884a6584022000487048055da4e382a6c8000683c05814048e4669509d15013324815b07884b8e8cd11394fb1a80ff1201931781911e818b2f89d17186d76938e9306b3c807270a160030100ca7014aac74a022307c219704024a0e197b330d80a9b2018402ba7806198f091e01c8a21299612627a84196b008800121c0001a0f016391d82eb66438599d54a5e2902e19999f0184014aac74a022307c219704024a0e197b330d806198f2627a84196b091e01c8a2129961008800121c0001a0f016391d80a1605a847a5104349606a06347ecf85e04b7da1c65d0e01acb480c040022002a6c800068d40581408862111d80a066667d6371a93ab1791374a14fb43b599b1f843b2f8163423fc3c3400d3fe1ea329c2c701c586ff54a5e4b23e030100ca700a9b22ba7806198f091e01c8a25e2b040bf6de91a973e4c537e5a19951220e36b042627a84196b14aac74a022307c219704024a0e197b129961330d801840008800121c0001a0f016391d80a10e10f999d666538665d50588ae9e018663c24780722884a65840220004870000683c258147612463028512f243843e43b599b10ec3a618670b1c0552978000690fd052bc4918cbc90e143b50e50f99998ca004b952c8f8a40b8661c6c7e0fa508ff06a236c3423fc5e23a676f1146fc0f75520f2c06100f4018fe650ae9e018663c24780722884a65840220004870000683c2581476028512f243850ed4e1997236e8a4b950e59b07e664d1411045e05fd08ff0f0d00e8d9834ff87a8ca74f1c460171c3d529792c8f92e6644dac1048838a440fc1264be6aefbb41e3f6a66340e3580c04150588ba1d0b844a920b86b2cd2447ba46ba9102c8329c052ab1d28088c1f0865c1009282a6c8061014e710aa2809e6090c9515650ec6e593cbc670cc360368b83865ec5ca78f4018fe65030810682d8ae9e018663c24780722884a6584989ea1065ac0220004,
  0x10683c160e466f4f7b0e3c65e2b00225440bf631982de91a9f8a09719657c8f422b005001a770819f339a6640cbd4a97013884710121c1d870209163d0063f9940c2041a0b61729e091e01c8a21299610da9447b360599b7330d80001a0f0583921066eccbf4d9c515099ba000d241b102989866e596b11a8e8f27a0519b50001a0f01666deb063143940bf6268aa7238ab5de91aa280a973e417812d1e94410d2582fafec537e6b2d21f99ad4a3565a103f5182e0f99b34100ef4c00eb7c0469536b041220e0ca706dbd214aac78ac874a02a75d882307c7e079955943b21970a28c4fb1b964f2f19c4024a760ba0e197b330d81199b10499a706198f130500184003010008800121c3d0063f9940c2041a0b61729e091e01c8a21299610da2e0a9b20001a0f0160519b54d0e02a5d7c2a248e2ac49a2a8d800286a236d0e561847e117d1411545e0644e8d9834ff87a8ca76f1c87201c7d529792c8f84c1400c041505885ca78ae9e018663c24780722884a65840220004870000683c0502864a6487944bcaa0d103e66cd82f9caac18b888e127d022966c2c00e95d7692fe71a903683d1532b8942e660156754a5e2902e1999af0c81014b19ab191ea3f0d0972a2aa316e0184003010541623f994398c0379482e8742e1120a9b22ba7806198f091e01c8a2129961008800121c0499a70001a0f0160504666c55ef4508ed3a08e76f2867316371a818df6871942042164994f24839da2847a198ac6677a188cb151375ac84c2e24e8c8d380083b1bd2630ea555943b238c5b98997999196f268fff1bbe8089831d7023d0982c1c70fd543254072a82f182f9caac18983b1f99ad4e17056c3064a356038d613050030103d0060c2041a0b61729e0da2e0a9b206198f091e01c8a20499a70d19a922b004aa661d870209163f0d09a316e008800121c3f9945c81b9a0378398c037948191ea72a2a4d81ed612a62e8742e1129abbeed0793911ee91aea1299611ea32123e24b19ab0001a0f016050461999afa58bc616db0c182a6c8000f042058661f99ada58bc616c3a2f6508ff152fc1b0c19460b83e8f8061002a6c818663c247807228812669cfc34268c5b8e63000220004870de520fe650647a9ca8a8ba1d0b84484a6584000683c058141192c66ac2e19982b0fa3e0ea58933fe01840008800121c0a9b20499a70001a0f016,
  0x1072a800880010dc039d422974f339a647b365001a70001a89206020561083829b10770ae55802c6744328c053d1f88aad07c6000a670b20c8aff1aa24120b15178b0d1e8c26bae4072a80301000880010dc039d40d16e3339a647b36000ac89206020560e0a61111897176b490eb50a9be16020319829f8a0120b197c876df7acccc04c74db0c2493f9440b22307c219704019cb2104b372ae8679649072a822974f70819f5001a71c8a2322740491c91917851a0b62e0d3f2bb960d16e3339a647b363f17030301000880010dc039d40001a89206020560e0a6770ae55802c0504456b1c560f934f94011519c9e804ebed078f1b04c7da822f7f876d2ba4fd52a8a05c81d1279826b976d431be25976b2902e1220e1986414a14490eb5160305fb0a0f19c7072a8018400301000880010dc039d407885522974f0d16e3339a647b365001a732a4830a562c2343d825b1c8a2322741a0b6911ee91aea0001a89206020560e0a6770ae50b0141102856b1c2a100672ce4dc3833faf8325928c5f391dc5d1949353ab8008b0c4b6585a3a70e8d9a104747403d76340254f9003d2900502a600001a508a824a9e1519c957ac543a9c2292902fd8d05c37a46ab41f25c658d9c4fe540069dc2067d18cc99032f52a5c054e7106c131e3c11bc844f88a5d3caa280ce6989e608e267050c951fe617cbc6714cc36046670c1cca11ecd836a501666dc5ca78ba1d030810f4018761c024780b8448682d8fe65082458722884a6584000683c671d9c0e3c60121c091e01c8a23d0063f9940c2041a0b61299610da940599b7330d81199c30001a0f0bc67142954024a1493210e3c60219c1159963560781ad82150d1247818b75c716495c81b922b005001a76401a370819f4f046fbe846b612a6a03784aa66842d8008800121c091e01c8a21d870209163d0063f994398c0379480c2041a0b62e8742e112129961486d3c907328484d2770da940599b71619bf0001a0f046670d85fcc35e0003c890e20219c16595581e04cc5e5eb6085576cca062dd71c59248ac0140069d90068dc2067d3c11befa11ad84a992a99a10b60e466f404870682d8761c082458ba1d0b84484a658521b4f241cca121349dc36a501666dc000683c1619bf617f30d78bcf18225e6e066993c11be1066eccc360048702478072288f4018fe65030810682d84a658436a511ecd81666dc00,
  0x1e40c63954c83d94b05d349c4c8c2b70cab582cbaa9b57b9a111e3f6a08d43c671e9e672478c901ee489edd06cce14e7100025a6aed13551588a151f22a19e5672484d486cce020e281ee4ba008d51c4fd614b1e3d84ba2881efa1a7aac21c3c90a2201505fdcc58dc6a678590eb94e711102c8cc36046559cbebf834ff848f883204047a8c928b005233352c8f8a40b8123d2c66c1914107538106508ff0da0f44f0d00e8d9a08a5952e703a0ca30157caa2809e6090c5e6426677c8c1f2447b8ba1d0e630086677646ba8b8448682d8de520722883c671c1caa0061000c040368b82a6c8ae9e018663c02200043700e750000680810838818160502c678d0034801c3213521b3380838a07b924713f5612e8a0170b869eab52e0242b84bada6f0faa8b3a0da2e643ae000ec059ec5803e159ae5d86a67856371ab3a17a880d3fe123e21ea324a2c09f2da148ccd4b23e2902e048f4b19b0645041d4e0419423fc3683d13c3403a3668229654b9c0e832191e63f0128c0ddd0f19c7072a801840030102ba7806198f00880010dc039d43f9941a0b60001a020420e206258140b026677d6371ab3a0d3fe1ea324a2c09f2da4b23e17a881220e2902e048f4b19b0645041d4e0419423fc3683d13c3403a366191e63f01214a148229654b9c160300e8325fb0a8c053d341700f19c7072a801840030102ba7806198f00880010dc039d43f99432a4830a562c2343d825b1c8a2322741a0b60001a8180810838258140b0866776cc5c823f4db0c46332bd3ce440b2539c47a1882307c2a8a075ac82197027982b182e94030a431799b883032274099ba3d825b2c23430a5632a481a0b61c8a21299d35001a770819f640cbd4a97010504750f19c7072a84784c17fb9e0a9b20001a89008158163915c47210676d9d511ad81d99d78f046f22974f339a647b36072a80001a8920602056108382999d94ed540075eb6c614e711102c958468aa2808c1f15a8d89e738865e89c4c97206842c459dc1ca7101c000890ec1591c1d99d71d1606744b84484a674d40069dc2067d9032f52a5c048234cc1caa08a5d3e3c11bcce6991ecd80006a2481808158420e0a63915c6754b732307c5611a2197a56932d27132002243b0564715c2b94add2bb44a674d8c94d821dadb185611a569584625c06198f2619b91c8a20f19c7,
  0x1060f80486e5532b800b02038d61305001166078ee02b081493a96494430a9be3190a2a8a0279ce5611a56a367a18875aec0d9745be8882307c2197a1d87020a26271320b0a2419ba0003e098901394408098bc8bc2999fd4cd41ac0120070d1c494e1210d484103c6c1085608a9c04b9e1a12dc7ec78887d2066982267d53c1265d2a69ae7b280de0e6300dea11e404a7091c0d2eb69722c0d182bff1605a6a2045e1e67dce8100d14ee98ab10ae4a3c524ea592510d24a0902551b0b002a6f8c6429a458dc5ea186a3e87a250183e0121b954cae00c04002c091ecd92a998e4360565af41cca1584695a8d8365d16fa2208c1f0865e8761c0828989c4c82c289066e8000f8262404e51020262f22f0a6108e6397c8ae2936c31403974aa2809e739c2067d2a998e4360565af5584695a8d8365d16fa2208c1f0865e8761c0828989c4c82c28800080723b31cf79ae7b06af54b9c4b3c00e94076000a1e8941a8fa17a86532b80003eb78901104e510202606276096bc8428799f76993c1264e212751ecd800080a608a7267d449974928d339a60732847b360595c3896b92307c2e874398c01d870219702e1123794820916402141293a91891f10e1f4092aa3683d154a5e17a86060f80486e5532b800b020c31e62ac40003e09890139441f8bc080141d8d815a0211ac29caac4021400026080221499c0595c4c8456596c1cca0002484e088520b19c7c8a667bd2ff8092fb57b46590f952cb9802a98e804471503fb1b042107884d4813b921161f0695d77012e70d2588e127d1fa966c19eb541629d3c7119abc4acb343a3663c3403683d154a5e1ea32123e24b23e4e03dd942e617a86532b8453ba62ac4191e61a0b62ba78060f80486c39f2da3f0123f994261ba1c8a200b020a9be0003e0b0264300867b56370d01594a2c024957d211577acb3432a4830a562c234030101ea32123e24b23e261ba1c8a21ab3a060f80486c39f2da3f0123f99400b0217a86532b8191e61a0b60a9be0003e0b026430086c19eb798585e64c6608682d8722884a4c85a73800020642799e9f0a200c03c9517e0ac468830264b8cc63954c83d94b05d349c4c8c2b70cab582c449f61d160ba19ed48a867949edd02a6ca1a7aa881ef800020161926a4d5456228547c99e70c0f60b7c26f117e0ac6b2,
  0x113e4b22906641a5c8754d263b0eed040206120884fb182b1a3236b65d05860df714d513002b74819058c58bfe61945a22e65742e55aa34956c348d564914887d0e0e5008680fa008d41ac0120070d1c397d3608be14b1e46447b94a6d246e406e4c2fb2f108e2adc9a547c5c2b16c21c447ee7274d110e400f440e3584c1418e661e8621d6bb1403974aa2809e739c2067d2a998bef006a03fc5e040e4c04044804bc3404c5ac04ac2267d42411ce10b60761c08289a80de0f4121e8c5b8e6300dea11e40492eb6aa2045e066993c1265d2a69ae7b1722c0d182bfc02200045981e3b80ac20e4360565af5584695a8d81cca036a508c1f0865e89c4c82c2891ecd800080a6098720c8440f8da681439398ac6673ec60acb00bf5d03575b035321d560dda062141008168837b6a8379c68c8dd20641618c8b5592411b338538775cc35e038d663998529b41b930b1305001166078ee02b08000207c8460e0e2109222d2169088a021a030e4e62b199cfb18296c0d4f2c544ce002cdaa0de76818853001f7e619474819071a3235564905a22e65742e548857ad86322d4a6d0f4121c6e4c2e8c5b82267d4e6301d2a68dea11ae7b1e40482411cd722c0d180592eb6a10b6016a389a2aa48e2adea2045c84103c6c1084e43605c2b16060ca1e501dc04b9c565af47ea583c9501caa0bc67fe303774e8100d14ee98ab10ae4a3c0e3584c1418e660045981e3b80ac20524ea592510d24a0902551584695a8d9b0b002a6f8c6429a458dc5ea186a3e87a250183e0121b954cae00c04002c08365d16fa2208c1f0865e8761c0828989c4c82c289066e8000f8262404e51020262f2680684e98c0790127b14054bada1713dda881171fb1e6d82458799f7221f4bd3ce090cc70896c73b16bd330d811a8e8f27a2999fd0301062ac4060f80486e5532b800b0201166078ee02b081493a96494430a9be3190a5611a56a367a18875aec0d9745be8882307c2197a1d87020a26271320b0a2419ba0003e098901394408098bc8bc67fcff56197717e8b911b9001238ffb268fff3d3f408b3e942e62a0f95171205743883f01293967d1b12c30c31e71a903fa848b04f78484df0e94076000ae98c0a2847a1f417410c8b037b0e5bd7023f9b98c9f79ec4db0c462e44429a9c849922974f339a638847306995f108e6842d8500e5d390d81596bd0732847b360301062ac41e8941a8fa17a86,
  0x1c183e67b42a6f8585e64125e1cc6608682d8722884a4cb46467a77a46a7e280342cbc761cae5cf91f21db4cc36046685d381015080fe5140fd4ae0fb4da0f44f0d00e8d9afcfd208a598a1045d0e3152e70061021011c5ca12d730d78bc7d2d4121c182cf4365d16fa36dc02200045981e3b80ac20000808a67976388420e0883d3d02987e6864f4b0a02e261ba0fae619b061ca263f0120a9bec40703fa843190a571a091616e7271324d5c5370b1901e98c0218d3d15876d7b16e2e87652315e2a877101840030100088001166078ee02b080d9745be8db707173f74849f000202299e5d8e210838869fea31b09410e143a6f2af10ed7010e5119a17337e6436b844d04c140045981e3b80ac213002779a18fc00080382d0ea90a164e89421d744685465fd300b93abbc000d4220a8172443e564e59f46c4b0e2c116676d1c8e1210d72006367091c0e8a02b165b845e04b4bea41bc1b8dace201aff18a1036380fe5c0683c90492c0c040ae9e0329c02a6f8c642848838dac1006100e8d98f0d01529787a8c92c8f8a44ffc12484524a090255192ca9e2a9002200045981e3b80ac200008044098a8168620504e0e9a114b9d145d645e44dc0c040003484409896af04e0a144bc83e43850e98003a701a0f7986883090492c9c4c82c44800080440e826050b868343d1549415bc9a01191e61a20c7d874581a090904732902e0899f5842d819980774a9a1d870492822307c04921120a26409542197a1493a9271320b0a2419ba01840030100088001166078ee02b086bb8a4d5cdd90002029a1e11844139440e8e222826261a0b59e69c17b6120885d6b38feb64c05643e555ed186cce14e1dd730d78bc7d084d483012dd84a99ca8a9de7f0aa2809e7389c4c85c32241ac012a9982411ce10b60045981e3b80ac2000080463888a4d544a57038581a094b9d0810347e104484d491c59243012dd84a99ca8a8ba1d0b8831a079a761b8c906804da6816066993c1265145d65d2a68a40b8183e1ae7b066d583404c44804bc7a044c121ad45e040d722c0d182bfce8237cae2375a4054d4c6a1ac04aea2045e4c0404061000c04002200045981e3b80ac211ecd82a6f8c64292a998e4360565af5584695a8d81cca08c1f0865e836a50761c0828989c4c82c289066e800080a6098980c9a07af06c4b0e9c182e2c0905dcf01c6f41e864e459e8a3,
  0x1020580a9a37b31402ced362ce5722cd5c22ccc8a2cf436a50165fac42042c62471c447e24c1acc2858b43e67b4c60b041caa00c04002200043700e75118cc990eb8986e87228864798682d8000e2060213615d8260b0ac259a35565d96281492591ca852044e8b1bc1b9448055da4e3800b789025812111f8a11e404ba63012eb69ec6786a2cea8a345c5e05fe1208860171c3eb6c626a679d4e710cc3604661cca669910076d3c5d3d1e36cd3573764aa2809e739584695a8d81caa0ba1d0b8831a079800152de0985a1103e87a00021807f44648188a7a0ea555943b268c591bbe813050239309038d6000d40e0b4068426308868befe4a2c0600c3d8229617a882f076030100ca701220e018404b23e000d2099682586205020110281383e1f89068b5a1f213520c04b7612a672a2a0008a388460803810892581a2b6824225c5454c93a63001ac01ec4bf52a9981ee4935714dc865e89c4c82c64054e082c365d16fa36dc84d4984a98e4360002488a3b0e233160571a29998761c1dcc00825d4478602c205d2ccab58c2b70b05d34c8dd8d04389c4c8002293452b04612888161a271db4aa280cc3609e67a4467c8902aa76c788812d41caa03c670466c1a08a58182cf416e7b30d7836372c00348083888a5d87e70096729a25998761c1dcc00825d4c78602c2679868830b05d349c4c82c6405f61d0561db5608a8aa1dc4003b2242b1fe2297672864119f227744e8b0280b83eb10061000c04000349c0259461118a240aae782a6c8a668643a68768a313e6641a55f0303bf44685714d517c023d8c3a97fa18bd563c9a8324586322c9a31648e316d4a6d330d786efa12257acbc7d05c911ca12d40e3584c1418e660045981e3b80ac218407c54e082e1011c4000808a2a092388420e088687cfe736b04139a11261ba0490391ca268b0241c4070bd07a10584e7571a090611c77a18864b2a0a9be492824d5cdd91496e575aec78aa4409543190a1616e7271322e87650b1901390d8159a1b01840030100088001166078ee02b086bb8a0d9745be8db76101f107173f74849fcc35e00020228a85d8e28f03886808f428a10e9a1d60ec18471cfc048986e8528502a6fa6af10585e64d05c0c660ab2cd0682d8fe650722884a4cb46467a77a46a7e282b41f0761cae5cf91f21db59c2c800349108f038021fef403a159a1b0b866,
  0x1692536110998f111a452627a8417011e01a900880010dc039d40a9b21d870209160838a440b214aac74a028c055f1b338539c42a8a0000080582c228566727e2b23a7612a691c0a0d3fe1ea3217812d2fa901a99e14b23e1220e6b3882902e048f4b8e33e3c34042042319b0636841f45041d4e04193a04170e19e354b9c8229609193b2ba780e832072a80301038b5e7fb9e398c0379482e8742e112440b20ca7014aac74a020a9b20184000880010dc039d4000080582c1599c4d8576248ac7601a0504469140a17817f1ea322fafe0d18471a99e1805c70f4b23e4a2c01220e29162d0ca70822960490399abbe6484fb1496e50e8324937eed078f2e875ba28479974a0206198ff413a33f2e0330d82627aa3170b11a668417018881c3da82356101f17730053820b4401db471a41911ee91b90398c0ec82df37a844f8edba7998b213c27917dd8482cd658e3507ba409190f08174b8b17271e180b1d8707a1888c055f8817610f2542307cbb852f20975375aec40954279ce3190a2197a1b15b32c174d2713230adc072a8018400301000880010dc039d40a9a3732829b32274299a3900206020586804a690efe60156b4a2c00ca702902e048f4b1496e53c34042042319b0636841f45041d4e04193a041774a9a54b9c822966bae42ba780e832c70e5f4d822f06198f70819f852c7912628e4aa665c8e5b500e5d390d8159a3f072a8018400301000880010dc039d40a9a370da2e2307c2a8a08c055f279ce1d87020975309190f299a394f8edb658e35213c2398c037a847917dd911ee91b90ec82dfa7998b1e180b1b15b307ba48482cd4095408174bbb852f2197a8b17270f2548817613190a2c174d32829b3227430adc2713200206020586804a471a414ed572086540075eb6c61102c94e7108c1f0865e8aa2809e739584695a8d8003b2241691c159a3f68ec46b623c11bc8a5d3c368b800020165701a4f1a3d36056676c0047008068168915c3921068ecb73330d85001a76401a370819f11ad84a97018f046f1d8705611a2307c1e025941979920975356a362197a881761318e552c174d2713230adc0b0f42a8a027856522974f4d94cbf339a647b360da94072a800880010dc039d40a9a3732829b322740020602058680a668e5799319821a0b61c8a212940f9f85630d16e34d94cbf339a647b36059b200880010dc039d400206,
  0x10f99ed64b2a0e1a353182c178903b38b5e8c055f27b742a876f331901072a80da2e7fb9e0a9b2000080582c11062050ac5d826695ec0822966916370e93b93c03df12011b453ba4e04053a0403942e69f2da62ac42902e2b928f1996a11a8fa1e8943f2e0531643a3170b17a88049f80d16618881c3191ea4fa20091e072ae89396452b163567b522a324081a531b338539c42a8a006b0027982330d84a970143179911a8e8f27a099ba01840030105416200880010dc039d40a9b21c8a21a0b61d87020916398c0379482e8742e11207b92000080582c22844188986955a154100b15f00af559241d30cfd618c8b238c5b1bbe82a042268fff0c2043d0062b173d08972b34170ad07c170c89670b20914036bb8a13050010dc039d43f99432a4830a562c2343227407b921695e33d82b91b338539c42a8a027982431799099ba1a0b61c8a2000080b08a260561e020694c1591391f14a2c02902e0e18351999ad822961510a317a880e983b21352191ea9abbe3f2e0612a672a2aed0793a316e480e59390d8159c45db38249a4f1220e36b040497ff2ba780ca70018400301000880010dc039d40a9b21d87020916398c0379482e8742e112911ee91aea07b920699c73d0063f9940c2041a0b61729e091e01c8a22a8a02798243254000080582c2283c11062051a511f0865c19c2c900929aee283810854c90846934cc64054e082c1caa0368b8ba1d0b84481ee48f4018fe65030810682d85ca782478072288125ffcae9e01a671c329c02a6c8061000c04002200043700e75000020160b08a0f04418814249a4fa583a587db0b00a40b8665a85a458dc6a3e87a2505ea214c5964345984647a9caba19ed480c041505882a6c8ae9e0488380610002200043700e75000020165808a110620502824856211a4d58dd28b006a3e87a2505ea2048838a458b608a594c5964127e03a0c8186924345984647a9caba09858d59ed48a8c901ac012a691d9213ee2c09068a11e66f4f39e8621d6b22c60ba6e20c01caa0061000c04002200043700e750e2d79fee782a6c8ca920c2958b08d0c89d0ba1d0b84481ee4820e29102c852ab1d280a30157cf60ae46cce14e710aa2809e6090c5e64682d87228800020160b08a1599c160ac692d36110998f00880000d425854188928e9d805018,
  0x1228e2290462584a188540502669cd35f109a2f1e181948011f9f06bb0f0c7b3f0123fa84e98c07b16ebf3f4b504874893bd171205022966c3061b01594a3560116607884b3410e3190a1c82615e04399c246fb4928240954271320ea581a02ab00028348343886611896128540e01409890221a718a8ba1d21a12dcb8830886555a079924a090255192ca9e2a90000a0d2388a41185a188140986469bd92f1e01070ca7064b2a4928213921114931978aa440954271320b0b6681e6241f89306b301840030102ba78000d205026298442581269b6cc640b1b5c8b19708b1751118d490eb5de91a973189b98c94db0c440b2331a69461a67501a65229a632307c219704021418983b9abc4191e6398c03f1703acb341a0b6378901296170d2581fa966c3064a3565182e81962d072a8018400301000880010dc039d48c0ddd0da940f2540a9be000080502629844430a40a1a6bb31360815c207fd72396d90398576640436a511ecd8761c082458003b0a60b1ec470aedc70cc69a56371aa24120b15178b0d1e8c2030100da94000d2298446904e461a676404562c94e081dae075c003b2240b19c501a653ad77a469681bee5cc6270b10d66e0886524965200f9c1aff2501aed52fc2a2046e4cf8944698420e29102c8cc4bf41ee481caa0e6300de2400c04006100761c082458ba1d0b84488c1f0865c1008506260ec6c1085c0697e6af12b2cd064798682d84a585c349607ea5802200043700e751b0c1800020140984425828388664b88a698d5f54f900362938721160b6f2864b01037300a01840030102fafe0c81534a3560d2581b04216c3061e81271a81297186cb7403fb701a5f18983b000d205044258281983a4b890b0942151446987ba62938743b55ef6f0fa4e1705a296373a1811123e21ea32179a5d4b0bd901840030102fafe4a3560d258000d205044258281983a4b890b09c0697d5ef4508ed3a08e76f2864e17051ea324a356123e24b0bd9049f803010000d2050904bac2258441984e7003a179a5d5fac625fcc42663c447e02858b592ca8e2d79e240edfee780c04002200043700e752303774000202c05056240ac0989629016696f0a34170b8830ad07c3d82b9671a4b431799099a5733190153820b072a80da2e32a4830a562c2341c8a2322741a0b60f1a51261a55000080582c2284418892696571d,
  0x11c65f03233164cdd460ba6231cc3eb99b613e6fcfd136c328a11e643a60ec5ea2048838329c1102c9921635e86205214fc8c1f1d6b20865c2c60ba500c2836a501cca0061000c040183e0fc5c0c9866e48245872288645e14b8448682da6a15ee46ba98e66118cc990eb94e710207d14a6d09a31646efa05c63dc4c1400e3597206e54006fe805c2ed4121d22f1808d79fe1db4225e8c042166066993c69fcaa2809e15942a69f434f6136532fd1ecd8e6300de5200029828348580b056508422217e6a0cc751729e0c2043d006091e000106791a0350382f03c6a0566350f40788551a0b6000a6161f20b13c69fff6de91a88eeb0973186318cb9b98c90804994db0c462e474a02440b2501a65330d82307c1187732185417f84c914975b1b16b30e3c622974f1729ea482e10c2043d006339a6010dc2b0303897a103af83d979f5f82b1322740217992c23430a5632a48091907319827cb74acb341a0b63f9941c8a29f856312940f0da9447b36073284d94cbf000a63484e1602a69f57971a0b65d8771129327cb74169ce9f85634d94cbf099be319a79259a77390d8158b2f819a6471247011664f16e3708b215c8b230ea58640b2507884b0da9447b3607328000a60a0d20d3d863d408d7a9213b43012dcf4121c2411cdfe1dd7b41e4dca8aa8c5ba10b60aa282447b8ba1d0e6300761c09e60976640646ba8b8448de520824584a4c85a428e4360562cbe066993c5b8d1ecd91c491d902c95722c8dc22c8436a501cca03a9609669dc002982834834319a796e85840947289b101c15c657c3c671c42e7078041e401a9e4c1a941469d5584688c1f15a8d8865e89c4c82c64054e082c6c056528d58562cbe066993c5b8d1ecd9460b83e38451c491d902c95722c8dc22c841cca03a96036a5006100002982834834259a77620cac602c2411cc1ac0210b612a998761c082144d36532fc2669cce4360203f9c524c649c4c82c64054e082c6c056528d59460b83e384406100562cbe066993c5b8d1ecd83a960da24151c491d902c95722c8dc22c8436a501cca00029828348342581469d46bb3f012bf3f43fa84488d1de98c01bbe07b3783839423b2ea8811f8881c309135fd290054f90031e32421169d221a71191a6f49282038d613050171205022966c3061b01594a3560116607884b409542713208b3e743805182e018400ea580002834834,
  0x12e1120f2041a0b6000580b0420c0bc0e0f66a5caa19b569db1e6901594209070ea58139a93049f8191ea72ae86781f73b1a8b0611c714aac22b38643ae74a02440b2539c40301000880010dc03af88c05530f2041510a307ba40a9b2299a870d9745be8884f16bb213c21a0b606825b1c8a24803e3f994398c0379481d870209162a8a0279822482b943179f2e8742e1120002c108302f0383d99c159a950fe5c05885d0e20f023d5c604bd4458dd28b00da107e086a44ae4a3c6a3e87a250e8100d4cae18ab10a40b8666a3c7e6a3550588920ae50c5e7c54428c84f08682d9200f8fe6501a096c722881ee905ea20127e02a6c818471c0c040647a9caba19e07dcba1d0b84480610002200043700ebe0000b0420c0bc0e0f6058561881c139a930b3502fda524b0f7a46a2c0bae5cc61e2b226e08969d76218c5b1f8f395649175c0914f4502e6450149a2aa52eb9a1e50544823e6fc0f8e400f46f25884142e35081084f0106ce6300de5204c141505888ecb85c3224e8100d8ab10ae4a3c6a3e87a2514cae0a40b8666a3c7e6a34920ae50c5e7c54428c84f08682d9200f8fe6501a096c722881ee905ea20127e02a6c818471c0c040647a9caba19e07dcba1d0b84480610002200043700ebe0000b0420c0bc0e0f6058561881c13a086a44945306dd8017059d962143966c3a18113c041b12012f2fa904203f93683f74503f52b83ed6c3064a3566b2d2743805416217a8801840000d208096188900a04e0e8666a3d6a11a8fa1e8945306dd518aa4204219db1e6c37217a88049f80301001840000d20c0bc1b096188442404e1f9a8d5a843404c45ea186a3e87a251acb494c1b75462a9081084647aa76c79b0dc9caba03a0c99e4fd40c040022002a6c8e26a2400580d40c13612b0bc1b02089016159ae2b951c188443b1a8bba19e4fd61a12dc1c5cfc0058030890566b8ae5470e26a253f522b38643ae612e8440b2539c4330d811a2a8684b7819a60732847b36001600c06c7c99c33a24299a87428c84f09200f81a096e200c17e6a0c207d0ca920c2958b08d0c89d03c6a0408d79fe1db4225e8c042166066993c69fcaa2809e15942a69f434f6136532fd1ecd8682d8fe650722880029828348580b05650842221a85c906cce0840e3d1cb313a3247ca1965c2070fa3c81a50ee000286a0634941a54be058fda,
  0x10f1ab14d5c537218d3d27b742315e2a87732628e7fb9e1f9a8d049f8062ca0a9b2030100088001166078ee0285e73884b77284b9191aaf7484a3000301b0162f04e188466ace6c3a08d94204213c041ba296a16c3064518c1e98a35198894e18970982ab0b0b63182bd68204541621f9a8d17a882ba7836b042628e049f8191aaf7484a3062ca0a9b203010018400088001166078ee0285e7000301b0162f04e188460f1ab1810ac5d8cf6f70688302661ccc63954b05d349c4c82c449f61d09edd1608a8aa1dcce4360566ab61a7a9fee782a6c8000c06c058bc9c8646abdaab5001d74db0c462e44d5c537081a9f440b2218d3d231aa1000301b0162f272190566ab5aa9109883271320b0b6682040699c72b1aa70006c05864158544d571c0c0ae92bb5aab7807264a4000903c1e05405856169aa907dcec4ed57208648ace1844b8eb6c614e710580c158468aa280f6f717ec295a8d89e738c6428d0438c83d94b05d349c4c8c2b70cab582c6a94368ba1a7a8000c06c05864158544d571c2ba4aed2b1aa7b308ace190eb94e710aa2809e6090c0ac6e20c0f66a8c1c07dd7207a5c2079d84ba0ba1d026798c89d0b08d0c2958ca920b8448682d8722881e3b80a179c000c06c89064728561531c2ba4aed2b02c6a950a3213c24803e06825b1c8a23f9941a0b6001421502c3d9aa36a5e200c0225cad7ec283c810c89d0b08d0c2958ca920d05c0682d872288245cb44a4c8265ccc5a5e9ae862b41f0000c0162f27219056231aa10c0f65e7d7e0ac4c66083c8102679a7e280c80b2c682d9f271102fd84a4c976eb8b08d0c2958ca9237a4685a68fcae54fd4727b25c5af41c07dd7207a584ba0ba6a748ae2918b91102c88634f4368ba1a7a8000c016190201599c6a7d74b0f2040992e31a20c320f652c174d2713230adc32ad60b11267875b7d874bb852f4d5c537000300586408056ad0ba6a754fb1209db0c89d72f89d16938e002de2584413abc43a6f2049a9be3928057c283e000348962f018b29a8d0d184514aac0e83274928d191ea3884b70718bb06198f612a672a2aa03782628e390d8159a950a9b2299a870d97454f16bbbe8882307c2197040173d2a8a01510a32482b927982213c24803e43179f06825b07ba43f99432a4830a562c2341c8a21d87020916398c037948322742e87400880010dc03af88c0553,
  0x1100127e00c040003484e110961b0620e92e2407a6b1c2e1987090fada805c17ba8b3a003a24ba6a0a06a6b16da2902ea8811b1996a1511abb17a88049f80301001840000d2138442586c1883a4b890af200a29ac36aecae4a3c7a6afc6a6af44845241460ec5ea20127e00c0400610002200045981e3b80a179c001b0961104e188900e92eb09ac13b9d081084f0106cda0fde401a9db0c19d0e0114ee9460b98a4e1c3eae0e82355bc250061015058802200045981e3b80a179c001b096188900e8282607a6afc2e0fada1986a5a8b3a4b00ff003a20a12e2606a6af56213683e33a04034204213c1235942e662ac46c2c02902e6916371996a15416217a88049f803010018400088001166078ee0285e70006c25844138622403a4b944af200a29abb4a1c9a47fcf4071e9208e6805c2e14b1e3ce6302447b8dea1246e40200fe46ef82d4b81e404a881efbb2f11c09b1d0e205c2b252e349ec24524da23e4f023d5c604bd446adce0e508ecb824f512a5c04761c082899066ea3c9e8146ad514ee9381014e8100d8ab10a40b8665a84ae4a3c6a3e87a2514c4665b6091578089422077592ca924a0af4f3ab6c61102c8580c1e8621584688c1f0f6f717e0ac5d6bb1e2a915a8d902550865e8c63954c83d94b05d349c4c8c2b70cab580e3584c141505885ea20127e00c0400610135715349edd0aa1dbd4e083cec0c8e212dc7e6a3418b280220230154cb834fcba1d75ca12e4646abdd2128c045981e3b80a179ccc360466acdfee782a6c8000c06c058bc138622b04a6ae5287a482393d01c7852c78fa0170b081405911ee170ac5398c091b9026951f8794fb37a84a207beecbc42fa90b52e079012b087116b3884bae69d344438e03f7bf03e3bc96214204216c2c03c1235691637541620881dd440b22307c2197a6d8245bd3ce7a18875aec330d8119ab32b928f3a040362ac42902e1996a1093d44a97011d87020a26419ba8f27a051ab51a8fa1e894531199492824095464b2a78aa417a8801840049f8030101f9a8d191aaf7484a3062ca0088001166078ee0285e70a9b2000301b0162f04e1881c16826511ab7028be460448838329c0ae4a3ca40b8665a840c0400610002200045981e3b80a179c001b0961104e1883a0a1cc76200a28146ad4300996173dbdc5f82b1519885318e55320f652c174d30adc32ad60b1127d9867,
  0x15e1dcaba0645e14ba1d0b8448682db7a4685e2c3c482c5c342c84182cce101cb44a4ca5cc609866e59e4fd4addb31dc3f545a68fe6e6324727b08ae2936c3118b9002200045981e3b80ac2036a501cca08234cd7206e59006ed4006fc00080a61595c7b2226b9ae15db48412cc965dacce6991ecd99006ed4006fc0029856889ae0502c1104e5121a09968819adf0b83e47c466190dac1052850d05c2b41f19c5ae4387d02411cc061000c04002200045981e3b80ac20ba1d0b8448000815c7b0140b23c1104e511cc24028099682f088389add7d0306a242411cc225e8c08d7a06699fe1db53c3d0aa2809e159536532fc2a69f402200045981e3b80ac211ecd8682d8ba1d0b84484a4c85a68fc8ae2836a501cca000080a6158ae56ba3c138586b6cfd55c81b94aa66a0378002243b15c7b31c2ba51c119ad969ac3e67b4c660a7e281f21dd730d78bc7d02411cc3012de10b61ca8a9766404e436036a501cca0761c082458ba1d0b844800110202982c050260e0e20a0cc6b5d73d323763410e0f18832c174d2713230adc32ad60b1ad30002024842509d2161ad562ed84a9a80de0225b2ce436056808ec4a348c1f0865c1006b44ba1d0e6300761c0b8448de52082458005082024842748580b1ad358357c02bd0402074c33f71a323c9a3ffca810986322c6efa05ca78f4018bc6a04308101a671cac5cf4225cac0e3584c14004598fe6505a578cca920c2958b08d072288c89d0682d80050820248421602c401ad10b83ee2066b4800e89ac74028189acfea1f42856be288f3c286f12287f0e289cfa93cd40819c4ea6b2e4e3c2d8629f50e19b36eee1140fd5081086a04d1d0e21b0b00e02a5c8e2ac49a2a8d7c2a25042a3c5c2afdc6a41a458dd80028da0f8cf00f7d380f7448046c32045e50b9a7cb68a40b8665a84061000c0415058b42d626842bc4c140045981e3b80a179c003484e110961b0620e92e0a2bc8028a731acd2864e79ea1563cb122886be28973c28770e28a5a82964fad8294a6d342d626842bc0e3598e661fa297da229d5742995aa29b64e3c2d8629f6a04d17c2a245c2afd042a3ce02a5c8e2ac49a2a8c4c140045981e3b80a179c001106c0e8be3a0ea6b2dac32b928f1e9ac71a9ac517a88049f80184003010000d2138442586c1883a4ba6a241ac91085b0c19c05b65460b848046c3e8f8986afe7c044e4c8c806,
  0x1c08001104a0f84e098085710e143a6f2a29cc3888a151afd31c53e4966f03b0dde7f06cce22c09061208841ac001ee48205af54e712f4f3ab6c611c68fccc3612a5c0446a3a3c9e8aa2809e739584695a8d9e8621d6bb0365d16fa2208c1f0865e800168ec2615c059afb397d362c75722c654458dc6a3e87a2514cae05ea206479868831f61d160a999e5925c2067d18699d2a99816a39403974e43605668fc061000c040aa2809e738365d16fa220761c082899066e88c1f0865e800110d21683e13828188263b1a42611c6be52110d183d000448e05a09862049af7b49460b9c604c41227744e6bcc3e97852850986e8580c03c780c2958ca92072288061017ec28c8dd8b00a24f60a2c00348204002411152702500b1af5028bea406ace83204047a8c9acb4a7c1aed2cfc05ea2048839460b8124834061000c040ae0f1c64798682d8fc048fe6503e978986e872288003484454a500b0261884e6bcf3aa280a9f06bbbf3f4489aef0c81011ea324b3f0902aa109f417120503010008800004e350442207e4b81419820249800e1cc510bc6bc5343800935f00af7b2c635d306573e8f2250641962c37d4e8ff5410c557e8b914c2e21b92a96313bd238ffb268fff038d613050109f4000d4220200e0bc2d1226bbdad109172d34170001420b02021892161aed0ca30154c7ec783c81000350ec819a07d8449d8306baf1e221ae70699d9092aa3d3f40891f154a5e942e662ac40e98652902e19864490eb5de91a971ae536b0417a881220e0497871b04c70d16e3339a638b5e7f876d539c42a8a0279822582c1431ae301840030100da9447b363f17030088001166078ee02b08191e61a0b6911ee91aea000202995c7b3de050260b05618844021ae968550402c57c02bd5649074c33f586322c8e316c6efa0a81089a3ffc0e3584c1405c3224045981e3b80ac20000800824838488421e0886b9db82c806b5900378600577680535b805176b460774745c576fc5ebbc18cde804eb48048506846fed078fa3170b84072dda82318881bf770fd52bb53b54d821d8484dfadb18f43e4779fc0da94073284633222974f57b46078ee02b08000202995c7b3de6844565d93c24a5c6b95a6b049f80f99ed0a9be191e61a0b6002de298140982c11008431ae369ac3e67b4c660a7e281f21db730d78bc6b74306a26066b7d243ad4586b6c12,
  0x12b83c72a8a0279ce5416214931900880010dc039d4390d8159a3f0da94072a80a9be3190a0492110005a020a6470440f84e099526c2422f852c7912ba5ad9911ee398c091b9037a84ecbc479012b087114bae69d34443bf03e3390d8159a3f0005a3b2244703e0995cc70da6c1c791911eeda822f91b902ba5ad9ecbc4398c0b0871137a849d3444379012bca6c4b9acd420421541622b83c74e03cb4503cf3c12351e814f1a81511781551201571fa966c2c0691af914931904921100880010dc039d40a9be3190a3a040362ac4191e61a20c7d874582a66796494aa661d87020a26419ba46332538775cc35e819b030525e2a8a0279ce390d8159a3f0da94072a80005a020a6470440f84e099521b1b056be528b008a5d3e08a58ce6983a0c802c0a30377452850d04382a6f81248443c950c6428043700e7511ecd8166bec761c082899066e81caa0001105a0f84e09808262066c0ec49d925f191e607884d1a20c7026c0698617d8741fa96081a074e08e14517592b928f582a66c2c08794fb1201571e814f679649691af9229aff463325387754aa66390d815876dcc35e2a8a0279ce14a143410e0a9be3190a049211030105416200b020d9745be8882307c2197a059afb1d87020a26419ba072a8271323a3663c3403683d12fbc01a80ff1781039306af000441283e1382602098900e26c04487489ae7a316e0c31e398c00ea6c37a844203f979012741acf0899f54b8d2771812f74a9a511a016bb8a151afd2b928f453ba4e04051e89462ac4532b8191e61a20c7d874581a291b33806b002307c2197a14a143410e049211018405416200b02059afb072a83a3663c3403683d11a80ff1781039306af4aa66538775090473842d8390d815876dcc35e2a8a0279ce1d87020a26419ba27132000441283e1382602098900e2229aff3a9556bb978d529213b7d05d07b41e4e6e0886447b89a31648e316e5249656488246e406efa1203967b2f10225bfce6302c24525c604bcdea114458dde455dd28b0030c7a08a583a9b108103ca8c90cab58c2b70b05d35584695a8d852850d04382a6f8c6428061000c041505884c1401ee485c32241ac012a9982411ce10b60043700e75138101514ee98ab10ae4a3c7a2514cae06479868831f61d16068a46cce14e1dd4e43601caa0561db730d78aa2809e7381248449c4c802,
  0x1a10ba1d1e4048b88312eb69a0799c20daa2ce89030f68a58dc5e6c4c0c04124a0902550329c0061007a8c848f88183e0bebf9286c4434f60121acd2c8f8986e87289b101c15c6c35186c3c2a6f8e43605668fc36a501caa230157c3c950c6428aa2809e738524c6402200043700e750000205a2991c0f8262b95b15b314008c53607b614b1e4584a9a447b8ba1d246e40b8833b2f11a079ac21c3c90a21722c45c22c3e01505fc06100524c6402200043700e750121acd2c8f8986e87289b101c15c6c35186c3c2a6f8e43605668fc36a501caa230157c3c950c6428aa2809e738000205a2991c0f8262b945e6c4c05b75ac5f1938f0bab800618a85a70e8d948ec33e8f24f928565912525063f2c8f27b3809d2a32457b46779fc02a608b04590803f9a81341b923f06bfc07884d9db47230896ff741acf1b1181380a97238ab1268aa35f0a89410a8f170abf701a0f81832c8018971a901fa966017e16c2c0072a813050018400f2548c055f279ce0a9be492824095464b2a78aa43a3663c3403683d154a5e1ea32123e21996170b19ed3190a2ba78060f80486b34b23e00880010dc039d400008168620f8260504e4a1b110c87ea58e2d79b0b01fe1dd5a4699c182cc4342c7d76cc81caa002200043700e75036a50007c8082b1361298460f896461b0f5bac981abcfc049c6a412cf00fea118053eda458dfa6300322c0c482c65ec6b67deb31366c2d526c2434f60183e0121b945ea186a3e87a2514cae06479868831f61d160a999e59240c04002200043700e751403974aa2809e7399039851ecda10b61c2067d2a998e43605668fc36a501caa000168082991c0f8265731c6c3449d818320e12651fa966c2c069163708125374a9a120b1d6bb0c2307c2197a0f2548c055f279ce03010486d3c9390d8159a3f0da94072a80a9be3190a62ac42b928f1a8fa1e89417a863c340549b090d3d8060f80486e5532b8191e61a20c7d87400880010dc039d40005a020a64703e09a3c2e9366c2c22f2ba5ad9852c791398c0911ee37a8491b9079012ecbc44bae6b08711bf13b99d344474f9003a799c921040f1e03d307884d081a01700ee7369b071b1b053a040362ac4191e61a20c7d874582a6679649463324aa661fa963c12355387751d8706c2c01201571781551a81511e814fcc35e20a26691af9819b03419ba0525e4503cf4e03cb,
  0x1529b41b930b1305063998010dc039d40000850892108842d2169092293af6558386cbc8f55112e143a5621541621e894532b83a040362ac4000d21103e2584e0a2bc43b5c00e890732f26cb6d88f04731d87010b9c0e940920a26901b01511a01419ba051b2962ac4191e61a20c7d874581b270b1901072a80da941b338538775390d815876dcc35e2a8a0279ce0a9be3190a49282409540896ff819a64f174f471b19291b2347b363683f7741acf049211061b251493190184000880010dc039d400008168a60984e6b0206cada0d1f9a2d000d2188440f8262596813828080b8240146ca6aa0e9a1154a5e261ba1ca2621352c4070109a2b612a6571a29390d8000ec168621103e228e2330920984e0e020581b27b31402ced362ce5722cd5c22ccc8a2cf5902cdd182cc41caa002200043700e75036a5000020a6061b25b308a6c86066982c2d9402ca5902c95c22c85722c8d362c9d182c7d3c5b8c5404cda07984e4845c61b5c907e0286c7c1caa00c04036a511ecd8524c6402200043700e7502a6f8c642924a08586c6d02550000205a298a4111b235ba4225c5daee2992ca9e2a900016a2429026048340804a3888a6c8412f5118076b2d20d3d85182e0184003010000d22986229168110286c7c12f5118076b2d20d3d85182e0490390184003010000d229862290965a1d88e8446c77d81393ff049039061a4926051520a2664858d4905750a85638b17271b15b30b15e341976908173d4d94cbf03010279ce56a3675aec323762c02893410e3082b30f2543190a3282c54095414931900880010dc039d400008168a6290586c6e84e98c07917dd7b1ad91a20c4d822f7d874852c791582a6911ee67964991b904aa66ec82df1d870461b0fa7998b20a268482cd07ba40a85638b17271b15b31e180b0b15e34197698803008173d4d94cbf099b1700880010dc039d45fb0a323762c02893410e3082b30f2543190a2a8a08c055f279ce3282c540954390d8159a3f0da94072a800008168a64703e6c64124bada3fa84a8b3ae98c0a296377b378178b138881bb2b95b154a1b110d3d8060f80486b3123e21ea324b23e261ba1ca26c4070571b0d461b0f0a9be030100f2543190a2a8a08c055f279ce14931900880010dc039d4390d8159a3f0da94072a800008168a64703e099b1706fcaedb3280de13607b57207a4e630184a98de,
  0x12a8a0279b3b161b450d9745be84c500008111fe051b475e64c6608682d8722884a4c85a73a7e158d36532fc166c8966d0c02200043700e75000020447f8586d1666773001d870471b1920a26291b234190251e180b271320b1901538775390d815876d2a8a02785654d94cbf05b9e072a800880010dc039d40f185f0d9745be84c500008111fe160966d0c6d70a3d86b0133139b31419ba051b3f819a605b9e4f174f0a9be14a14471b373190a3410e271320b1901538775479273390d815876d2a8a0279b3b072a800880010dc039d40d9745be84c500008110547f8266d059919abc43f0120e1a2facb903fa8417244a6d5eee98c00c04b768447917b3785e0439092aa729a25da82358881c3423fc0e9861a799c94f90031e324211b3d4504319c24703c593332fafe4e17054a1b111ea323a36636b041220e0d3d84b23e54a5e049a6d2ba78018405416200880010dc039d414a143410e0a9be3190a492824095407b921b338291b230000811054098465d85a228a6388146cfe0c7d874681e6582a6241b3967b5214a143410e0a9be3190a00008110261185a2289205144600846cf79e299ae30a9be261ba319821c8a212932169ce0301000880010dc039d400008111fe0989e6ced1e5531659030100ca700184000880010dc039d40000811096248901881451180211b396c64a46c8c16e782a6f8c642800020447f8264705a6cdd6371a8fa1e894002de1104e511cc691bc6cd4f0b61837fa81447962c647b38645003f82d1421502285a42939a86cccf0b61837fa81447962c647b386453e8f21b964f0e1b2f2514396d84f95e354a2847a1f41741d702419b8221a484ed8e9285949259592203d0487ed0793480e59a316e911ee238ab7398c091b9026951f8794fb37a84ecbc42fa9079012691637b087116b1acf4bae61208f99d344438e03f7bf03e3bc9b2d1a8fa1e89417a88532b8191e62c8f271a20c1fb9c170c892a3244203d37d87409047306b00581a29842d84aa664503cf2b83c71d870901b0120a260502611305001840030105611a56a367a18875aec14931900880010dc039d402a6007b920b1901072a80da941b338538775390d815876dcc35e819a64f174f47b362a8a0279ce471b19291b230a9be3190a049211061b2500008168a60984e150726cc60a61839d6a83977e83935b0391688b995d0b9598ac66b222ee3e8f2,
  0x18c0ddd0000811026259b5b6b3dc604c6384a2c5431f4381081aff86c05645c91120047cf4fd04e30f430c7a7cb6a50b981e3b85ea218ab10fc0480a17546461ccfe410c8455cce436024aa85668fcbebf92c8f9529788a6d5528b002c67b448838a458b4126d5c329c0ae9e0986e8726d34368b8a66d2d92ca924a0852851e2a9102550d0438061000c0400220208a583a0c83c950c60b04e2d79fe6d263037741caa0043700e750000204409896169b595ffc1a64bc00b7844258625a1d8052bc878126d5cc3d17a88191e8c593330d3fe1e1b538b02418482211b338bd3ceadb18539c40816bd330d8119b511ea321220e4b23e04b8e0c81532fafe4a2c0018400301000880822960e8320f2543182c138b5e7f9b498c0ddd010dc039d414a143410e2307c2197a2a8a0279ce49282409545611a56a367a18875aec0da2e261ba1c9b4d299b4b072a807b9200008110262585a2283e6d54c71bc0ec34f9259779fc001421509294a3a1e1b53400c6c0564203fbd20047c4e30f67cb681ac005ea20fc0492a9986461ccfe410c8455cc0c04124a0902550368b81ee482c67b44883852850d0438061007a8c8766d3d2c8f812e3832054cbebf928b0208a583a0c83c950c60b04e2d79fe6d26303774986e8726d341caa0a66d2c02200043700e7500002044098961688a0f8466d44c3d17a880d3fe1918731e01a9390d877132b15872b0301049282409548404751220e14a143410e01840000d211026168160508a6021e0a24c1d9b4f1c15c6bec82898140984003b026168161c9b4d5d3d1c6c64ce698a46c8d1e1304e2d79fe6d240002044168a66d2d41512012f1fb9c6b1b2b901b010d3d8049f8191e61a20c0904737d874842d8581a091d87020a260c9a07419ba051b4708849d291b2374a9a819a605b9e6bb8a4f174f0a9be2307c14a14471b373190a2197a3410e271320b1901538775479273390d815876d2a8a0151b41279b3b4d5cdd9161b450d9745be84c5072a80301000880010dc039d400008111fe6d25e61a20c240c3d7d87417812d2fafe581b276b1b2b4a1b111220e0d3d84b23e049a6d0ca70018400301000880010dc039d414a143410e49282409541b338291b2308849d74a9a6bb8a151b412307c2197a819a64f174f471b3705b9e0a9be3190a271320b1901538775072a8479273390d815876d,
  0x14100b15f00af612e8238c5b529b47081cfd30cfd2c8f278684b31bbe86ba18268fff2a0420699d9173b074849b08928b081ae9741acf14a14341705c93fbad07c6713f9643ae539c4331b5d4906ffa4844b3d3f4092aa4608ac801897f4416371a900e8b876000a0c1aeb0c810142042336841f4e04191201571781551a81511e814f9d3c71162ac4942e64b23e54a5e8206f16906ef2902e199b690491c92ba782a8a09abc42e874191e6398c01d870261ba3f170327982acb342e1121a0b637948209161c8a202a60129321b04c70d16e322974f078855169b4b339a60da94431be059b2259b5b8c0ddd072a8130506399801840030105416200880010dc039d44784c138b5e7f9b4900008110266dad9ef2307c0e029121970402142b1b65189b6106846f841b670d16e31b04c7339a638b5e4784c17f9b492a8a02798212932169b4b059b2431be259b5b0000811026199b694ed5720866b6c61584695a3ad56819052850d05c2b41f19c4fe518cc94e71140069ccc3619032f52a5c0446b601caa00610036a508a5d3c6c131c761c082458aa2809e6090c6f812472464798682d8ae9e0986e872288345b8cce698e2d791e1305fe6d24fc5c0c4a4c85a6d2c166c8966d6c0c04002200043700e750000204409866841b67eb8ae54fe54e71118970cc360466d8c2267bc8c1f0865c100850626d861011b41caa036a50345b8c6c131cce698e2d791e1305fe6d24761c082458e6300de520ba1d0b8448aa2809e6084a4c85a6d2c166c90c6f8966d6c0002044098662b0786d9531f72a2aa316e000ec4f15c7b1608f19c119b63028322bfc6a8907a30b1c6d74566d7d58468bea415a3ad5acb484845245ea21681901caa00610036a508a5d3c6c131c761c082458e6300de5226af12b2cd2447ba46ba8aa2809e6090c6f812472464798682d8ae9e0986e872288345b8cce698e2d791e1305fe6d24fc5c0c4a4c85a6d2c166c8966d6c0c04002200043700e7500002044098661e0626d8570bb504858881bf4f92592bb53b5081ae55c82198484dfadb18f43e4539c40da9407885522974f000ec2993c2495c7b1a117c878970566d7da69500e5d1d87020916398c037948000ec2991c0b1f2c70cc6d75f80a02e191e60f99ed1a0b612932169b5919b06822960e8320f2543182c1072a8018400301000880010dc039d438b5e7f9b49,
  0x160ae20c0ba1d10c5e64c89d0761c0f6096cb08d0c2958ca920b8448682d882458722881caa0061000c04002200043700e7502a68dc266dac368b8a66993c6dd4e2d791e1305fe6d243c671c00020440682c6df5b350d0159532b84a2c029162d1220e17a88049f82627a191ea841a3b72ae8119ad96793f54db0c14aac643ae46332440b274a02539c4229a4b0184003010008800a9a370da2e299a64f1b754784c11d87020916398c0379482e8742e1122a8a02307c219704030ab88303d825b3227432a482c23430a56822960e8328c055f279824317991a0b61c8a2099b6b38b5e7f9b490f19c7072a8010dc039d4249b79000081101a0b0566dee7a841a3b051a45119ad96484fb4db0c46332a284799440b2539c4229a4b331b77072a80da2e299a64f1b7538b5e4784c17f9b491d87020916398c0379482a8a08c055f279824317992307c219704030a7a18875ac8b182e9b88303d825b0f19c7322741a0b6099b6b32a482c23430a561c8a2000081101a0b0926de6fe6015674a2c00ca7029162d14aac049f874a9a191ea6b93f522820b72a2a612a62628e640e615d9901390d80184003010008800a9a370da2e299a64f1b754784c11d870209162e8742e1122307c219704030ab88303d825b3227432a482c23430a56822960e8328c055f279824317991a0b61c8a2099b6b38b5e7f9b490f19c7072a8010dc039d4000081101a0b092331b7768f4a668e4761c0682d8824584a6dcc786dc46c131ce2d79fe6d24266dac00020444f1b751c15c68f482898a66d2d0640949c4c83c671c786dc46c131dfe6d24266dac00020444f04a6dce543190a2b180b271320b1b6f000584f008248786dc53f9643ae46332539c4330d82a8a0119b63279822e874431799398c01d8702e1121a0b637948209161c8a2072a80d8dc984046d231b6d000081613c248780b1b6f5c2ed412162206fd3e4964aed4ed612137d7207a6b6c63d0f914e71184ba0cc360aa2821a12cc465789e608a8c91d2126cba1d10c5e64e6301583aa4245cb4206bb4b8448682d8de520722884a4c85a5eab41f01caa01e21543637248a5d3c00020584f0921e08c6db469798ec3c36d845d4ea0a9db47235d08ab7e88a95b08a764b2ae113478ac868837b6a83794c009da75d88d20641e6863f7e09255aee8e928559220480485a3170b8881bf2bb6cc4d81ed,
  0x17e88a95b08a7fe8093c6808384072dda82316b81d78881bfe1134770fd52bb59634c2e24d821d5c82197082174937e4100b15f00af6302d3adb18f43e4d30cfd2c8f2788ecea7560ea92a042081ad5072a863998018400301054162008800a9a370da2e078ee02a981d87020916398c037948911ee91aea46332643ae539c42a8a027982431799229b83268fff3d0063f994529b4238c5b1bbe8170c89069b7f0c2041a0b613050010dc08972b34170ad07c672029caac299a64f1b7538b5e4784c17f9b491695e3099b6b091e01c8a2129b81039d4000081103c15852249b8f028322a744823d45e23ad0e9990906e2c346d9080f4e406e247a2a646a2a6cbe2a5c0c04002200003504425878148545a0e04b814b09868b1d82903a6e342e199a5f049f80184003010000d2110964b814b08a40e9c0241b8b275e1e3f94280b8661c6e76f1165c06e1cf0d00061000c040003484425878148545a12e052c28b1d82903a602406e25a5f5182e19264049a9b0d1b601840030102ba783c3403683d1000d211096148545a12e052c22903a901c06e1e6c4504411fb8c4203fb4e03f13683d13c3403a3669d3c7118e06cf54a5e0010fd1483815014b0abc0f9b85829860dbda20dedaa0de660318cf481905563c9a8188d7422adfa22a56c229ffa024f1a020f844d130b890402c57c02bc8e316d4a6d13e49658c0b4f4c33f46efa09a3ffe12088623b3a9c225caeb6c60d05c1583aa6b41f0a8c919c808206b5672ab06269646cce04c1418e660a66993c6dd4e2d791e1305fe6d241e3b80aa605a578c30810f4018fe6505c3224247801a6dfc043700e7514e710aa2809e6090c5e64682d872288266dac4a6e0400020440f056229b83950c6428ac602c9c4c8266dac1a6dfc0002044129b8169351c68fccc3604655cc32054cbebf8525f8d28b00a458b4123d2cae9e0f0d0108108cda107d141075381064e8105c986bed52e7208a58a80a8c761c03a0c8ba1d2200c08289a30157cc8dd8b88317e0a650640949e738d043824643da0690c6c56ccb05d349c4c8c2b70cab582c6df43c671c1caa00c04002200043700e7502a68dc266dac368b8a66993c6dd4e2d791e1305fe6d240002044069b7fbf980559d28b00329c0a458b452ab0127e1d2a68647a9ae4fd48ac01ca8a984a992a99898a39903984e4360566dee08a588c1f03a0c8865c230157d00c289e,
  0x1440b22307c219704024a0e1b9b072a8018400301054162008800a9a370da2e299a64f1b7538b5e4784c17f9b491d87020916398c0379482e8742e1120c2043d0063f994170c89091e0069b7f010dc039d446332643ae539c42a8a0279824317991a0b61c8a2099b6b129b81229b83149b99000081103c158206e8d1f11220e36b0417a88018400d1b9d000d21106208022240280f8146e85a8f1f99ad000d2258160f0421882024028138666e7dacf8e33e7181310ea5801840000d218820088280d1b9d0e4e62b199cfb182b2c02fd740d5d6c0d4c8756857681885040205563cb1a323da83245860df5a20dedaa0de7486e5c8e316d4a6d06efa09a3ffc4c1418e660043700e7500002088109222d0200e1b9b0e4e62b199cfb182b2c02fd740d5d6c0d4c8756857681885040205563cb1a323da83245860df5a20dedaa0de7486e5c546e548e316d4a6d06efa09a3ffc225cacd05c2b41f19c80a72ab04c1418e660a66993c6dd4e2d791e1305fe6d245a578c266dac30810682d8f4018fe6505c322424780722884a6e041a6dfc043700e75000020440f056149b99544ce0020f6e19a662188cfa3c93002749419079a5c444c140043708e316c0e75000020422d0383ab486e5c17d80547158797ff0a02e1986cb7417cd6b17c3241b8b4203d3901b931f9b910f9b852ba789abbe2627aed078f3f170f84072dda82316b81d78881bf770fd52bb59634d821d5c82197082174937eadb18f43e4560ea9072a801840030105416200880010dc039d40a9a370da2e069b7f1d87020916398c037948911ee91aea0c204091e03d0063f99446332643ae539c42a8a0279824317991a0b61c8a2229b8308972b34170ad07c672029caac299a64f1b7538b5e4784c17f9b491695e3129b81099b6b249b8f000081103c15852151b95275e1e5ffc280b866c1a081085c06e1cf0d00061000c040ae9e00034844258781486c151684b814b08a40ea406e4cf4b4211d53c3400a02e36841f45041d4e04193a04177438c9403e962841154b9c1999ad82296018400301000880010dc039d4000080583c2204248838052bc2907e6e44f4b3c3400a02e42042336841f45041d4e04193a041754b9c1999ad822960e9b8d0f9b856484fba2847997a18875ac8b1bd299069798ec3c38e928548036f4ea0a68837b6a8379980c633d20641558f22ba789abbe6a06232627aed078f3f170f5d08ab,
  0x188ecea7340291089bab091e0081ba33f994072a80da2e46332539c42a8a0279824317991a0b61c8a2099b6b1d87020916129b81299a64f1b7538b5e4784c17f9b490301000880010dc039d4000081103c158a46eb562142125f6293876f1b353a18113683f712012f0d2582fafe3c041b2b8415743806b2d21f99ad4a3566c3065182e0f9ba917a88049f8191ea72ae86793f5440b22307c219704024a072a801840030105416200880010dc039d40a9a370da2e299a64f1b7538b5e4784c17f9b49078ee02a98069b7f2e8742e112091e0643ae539c42a8a0279824317991a0b61c8a2099b6b129b81229b83149b99081ba3000081103c158226eaec06901598229624b240ea582106e139ba7532b8078ee02a98069b7f081ba3049f8191ea72ae86793f5440b22307c219704024a072a8643ae539c42a8a0279824317991a0b61c8a2229b830da2e2e8742e112129b81299a64f1b754784c10a9a37099b6b38b5e7f9b490301000880010dc039d4000081103c158220f9ba9588508497c7ea59b0b00f048d5a46cd448838dac10989ea101cb5dc3f55726e94ae4a3d505881e3b80aa601a6dfc761c08245918cc8206e8d36c305ea20127e02a68dc0c040526e640610002200043700e7506a6784e6300de5207a2514cae0e8100d8ab10647a9caba19e4fd5102c88c1f0865c1009281caa190eb94e710aa2809e6090c5e64682d872288266dac8a6e0c368b8ba1d0b84484a6e04a66993c6dd4e2d791e1305fe6d2400020440f0560883e139ba7a583a6aedb0b00925945a46cd5b6f4848046de2b227cb6a9d7620fcb81f8f3a8c5c2f5c08fe2206e55658e430810206e8c9a47fd78ac102fdb7a46a5cc626e632536c3140699518cc86e593c5c3224247801a6dfcf4018fe652920b86b2cd0ae4a3c5ea20526e64061006a6784e6300de5207a2514cae0127e0647a9caba19e4fd5102c88c1f0865c1009281caa190eb94e710aa2809e6090c5e64682d8722888a6e0c368b8ba1d0b84484a6e04a66993c6dd51e13042a68dc266dace2d79fe6d240c04002200043700e75000020440f0560883e139726e973e0ea6c4203f97412913683e33c03df942e63f2e0a3170b8881b9f78fd54a97018f27a051ba12b928f453ba4e04053a04031e89462ac4532b81a99e12902e199b9f0d1b9d17a88049f8191ea72ae86793f54db0c,
  0x10ca7014aac7498310e1bb59abbe191ea3f2e0ed079372a2aa316e0498e92628e390d8159bb1091e0018400301000880010dc039d40a9a37099b6b299a64f1b7538b5e4784c17f9b49078ee02a98069b7f1c8a2398c0379482e8742e112911ee91aea129b81000081103c6edfd278ac8990697a75d8898ec3c37e07a14ea0aa28c4fb5d08ab7e88a95b08a776071b55aeee11349dbc459592204100b15f00af8e92854813b9d30cfd2c8f279406bb2a0424508f73c08f54e08f33a08f1a8811b1b04216c306511a61701b8b5182e1f9b910f9b85189bb34c2e2d7023d68837b6a83796302d3c70eb9d21b97238c5b529b488ecea7081b9b1bbe8268fff340291072a8130506399801840541620a9a370da2e078ee02a980c2043d0063f994a482e1acb34170c89091e0500e5d1d870209162a8a0279824317991a0b61c8a2099b6b0498e9069b7f2ba782628e00880010dc039d43f2e0a316e398c037948191ea72a2a2e8742e1129abbeed0793390d8159bb1911ee91aea129b81299a64f1b7538b5e4784c17f9b49000081103c0e1bb560ec7e60d4022002a68dc266dac30810682d8f4018fe6505c322424780722881a6dfc043700e75098a38fcb828c5b8e6300de520647a9ca8a8ba1d0b844a6aefbb41e4ce4360566ec6447ba46ba84a6e04a66993c6dd4e2d791e1305fe6d2400020440f038189bb305bdfd11c0e52496670b10e520047c3a9604e6ebc5e05fc7a8c86acea0171c3d2c8fa7cb68a46eb448838125ffc329c0ae9e26aef8989ebb41e3cfc5c3e101cb76a08c5ae075e2206fddc3f54aed658d360875720865c2085d24dfab6c63d0f9130b89584698c0b4d5afd88e316e23b3a9c6efa09a3ffcd00a44226eac206e8c526e648a6e0d90eb918cc94e7101caa04c140061000c040022002a68dc368b8a66993c6dd4e2d791e1305fe6d241e3b80aa60761c082458e6300de522447ba46ba8aa2809e6090c5e64266dac30810682d8f4018fe6505c322424780722884a6e041a6dfc043700e75000020440f0566ec534380a975f0a89410a8f1fa966c2c06916376000a130500301000880010dc039d40a9a37099b6b38b5e7f9b4900008110b485a42a821e5103ea2a007304e6ebc640d2585182e1f9b910c2043d0064937ef43e40497ff0ca70149b99018400a9a37069b7f2ba782627a84072d770fd55c8219229b834d821dadb185611a56bf6,
  0x1229a4b0da2e2e8742e112299a64f1b754784c10301000880010dc039d40a9a370f1bb78c055f279824317991a0b61c8a2099b6b129b8138b5e7f9b4900008110621599c151bc54fd590eb9102c94e7108a692d84ba0cc3621a7a84663a4907e02858b43e6efc52ab1d26f054069948c1f0865c1005cac1caa00c04002200043700e7502a68dc368b8a66993c6dd4e2d791e1305fe6d241a6dfc5a578cba1d0b8448aa28230157c9e6090c5e64682d872288266dac4a6e043c6edc0002044089bc35e94204a3456808761c082458e6300de520ba1d0b84488c1f0865c1005cac5a578c003b0580b0222bb5d26f05bb99f2da0801313f2e0139b351e894a3170b532b88881b9191ea72ae8f78fd56793f54db0c46332440b2539c4330d8640cbd4a970111a8e8f27a229a55051bbd12012f17812d6b1acf0184003010008800da2e299a64f1b754784c11d87020916398c0379482e8742e1122a8a08e33e2307c2197040172b1695e304b8e4a2c0822960e8320f1bb78c055f279824317991a0b61c8a2129b81072a8010dc039d40a9a37099b6b38b5e7f9b4900008110220f8626efd9e1440b2539c4330d811a2aa280a869ea0d1b9d241ba1151bbb1ea324b23e03010299a64f1b754784c1398c0379482e8742e1122a8a02307c2197040172b1695e32fafe0c815317812d12012f6b1acf04b8e4a2c0822960a9a378e33e0e8320f1bb738b5e7f9b498c055f279824317991a0b61c8a2099b6b129b81072a80184000880010dc039d400008110220f862051bbdc90846ce46c0564647a84e58ddcaba06a67859e4fd5102c94e7108a692d9006eccc362805c2c465bad434252eb6aa26ee40c04002200368b8a66993c6dd51e13041e3b80aa601a6dfcfe650e6300de520ba1d0b8448aa280bebf928b002a68de08a583a0c83c6edce2d79fe6d2630157c9e6090c5e64682d872288266dac4a6e041caa0043700e7507a8c92c8f800020446703e189cc51014151bbb4fd590eb984ba1102c94e710cc360465b7e1a7a89059848a6964a8428c6c056520047c4e58dc6ace81caa00c04002200043700e7502a68dc368b8a66993c6dd4e2d791e1305fe6d241e3b80aa601a6dfcba1d0b8448aa2809e6090c5e64682d872288266dac4a6e043c6edc0002044671a4189cc51200152a26ee50a3081ba14817132902e8e33e1999ad212f60e983b,
  0x1099bd36f2c1e3b8d05c00a1756b41f08458d59c8089e608cc3610c5e6446a38266e814663e72ab0245fac02200043700e750a66c94446f3c72288682d8000202c2b0526f458e9390d80a162d15a020f86cf9caac189bcd2307c21970401bcb7438c089bc30e8320f1bb78c055f279824317991a0b61c8a2129b81078ee02a98069b7f299a64f1b750a9a37099b6b38b5e4784c17f9b49072a8010dc039d400008111bcf6114546ee44e6cd47a2505ea227cb694cae128b00647a8fcb80a458b448839ca8aa8c5b81263a498a38e4360566f24061000c040022002a68dca66993c6dd51e1304e6300de520ba1d0b844a08a583a0c8e2d79fe6d2630157c9e6090c5e64682d8722881caa0043700e750226f0c8c1f0865c1006f2c3c6edc1e3b80aa601a6dfc266dac4a6e040002044189bcd6a8e200c0205cf57ec28ca920c2958b08d072288c89d0682d800161420b0ac401bcb06e7de3f56805c2d2a5c06d434263c9e92eb681483aa2046d446f1c546f14306bad8ab114cae0a458b45ea20127e0647a9caba19e4fd536c31102c88a692d4069941caa0061000c04002200043700e7502a68dc368b8a66993c6dd4e2d791e1305fe6d24fe650761c082458e6300de520ba1d0b844a30157c3c6edd18cc990eb94e710aa2809e6090c5e64682d872288266dac4a6e04000204418856671bc9ea31228e70e28f6be28ef3cd10fb5829961685fa228d6c2285f45f26821d5d8f008f4468547453ee5a20dedaa0de5564c157c4be6184bfd86322f486e5c9a31648e316d4a6d3a006146efa20171c3c24aaa6aef95297bb41e3c989eb6a08b6101cb4addb31dc3f557208fef4f39e8621d6b22c60ba6e20c1643e54b2e60f60ae55ed185c9106c05648447944e6cd44c1418e6600c04002200368b8a66993c6dd51e130742d601e3b80aa601a6dfcca920c2958b08d0761c082458c89d2447ba46ba8226f0d18cc990eb94e710aa280bebf832054d28b002a68de08a583a0c83c6edce2d79fe6d2630157c9e6090c5e64682d872288266dac4a6e041caa0043700e7500002044158aed470ae97303e6f088081446f1dbbb1220e2627a84072d770fd55c823fbd3ce7a18875ac8b182e9b88303d9aa3078ee02a98069b7f32a4830a562c2341d8702091632274463324db0c17a880184029162d049f8191ea72ae86793f5440b2072a8643ae539c42a8a0,
  0x136b0417a883f012049b570ca701918733f904364b2a4928214a1416102578aa4409543410e27132390d80b11615872bc407003010541628404752ba78062ca0a9b2009f001a5a02126000142b0164190c1d9be7ff878428c4e0288447946a3e87a2501e3b80a16c400b7844879cc5124c4f980151bc6f9585313992b5182e049b572ba780ca70062ca0a9b203010009f001a5a02126000140584a118625a1d8790a46f8f2a7617f31497eb16190f10998f261bdf0f25478aa43190a271320b1bdd299b25111bcf00880010dc039d400008499ba1617691ca26c4070571afb072a8299b25111bcf323763410e0f2543190a271320b1bdd00008261bdf679c20636d1c592518cca14b1e3e805c2d4e71184ba2881efad43424cc3612a5c061a7aac21c552e1b0c46a3a3c9e8aa280901b96017061e7c048414663c9e6094c0526920b84f4018247810c95030810ac6f6e447b8ba1d13571534e6300761c246baab2cd0b8448682d8de520fe65082458722881caa0283e002200043700e750368b8a66c94446f3c000202c6f7461d55948b98807d1e1063a8105f2201494881216f06e5a886c3191ea3f2e010998f72a2aa316e2628e390d8159bd90e11c7149bd1130500a0f8299b25173bc1b9425111bcf00880010dc039d4398c0379482e8742e112000080b0ac6f6c38d96a465b4e941dd300ad6a8397a8144798ac66bb386453e8f225162f26944f5e1459211635051bd72394512201496f06e5191ea72ae86793f5643ae440b2229a4b539c42307c2a8a0219702798240172b4317991695e3099bd3072a8130500a0f8173bc1b94250da2e299b251c8a21a0b62e8742e1120e11c7149bd1111bcf00880010dc039d4000080b0ac159bd95c8c784ce6646547201c9d9213ee8a11e65e8621d6b22c60ba6e20c0f6f08a86f564c1acc42663c5cef06e5094ca920c2958b08d0c89d0880525bc1b94647a9caba19e4fd5102c81caa190eb94e710aa2809e6090c5e6472288682d88a692c8c1f0865c1005cac5a578c38471c526f44266f4c368b8ba1d0b8448a66c94283e002200043700e750446f3c000202c2b056051bd758bc9a513d7851655650844c1405cef06e5094446f3c02200043708e51440e75000020220c0242a1bd5696c64798986e8a66c943eb0208a583a277c283e02a51bc02200043700e751a40574446f3c72288682d8000202c2b056,
  0x1710cc3600a16c4aa2808c1f04661cd58469206fcc9e738865e85840955a4cb49c4c82c6ff4368b8002b0164190c570ec190fc6ffc3032274098123d979f1a0b63f99432a4830a562c2345f82b1000ac4190c3f02c6ff6906b1acf6000a8e1bf10d2581f9bf9089bef4b9beb62ac403010062ca009f01d9be70ca700a9b21220e01a5a54a5e1ea324b23e1a8fa17a8602126000142b0164190c3b0281883e6f0906fec8a33ec60ad1112b61836d5d039568837b6a83794c2e29804631fe862fe08665d20641631a2f55943b1e1bf75611a481bf356932d271320b1bf5529b45b0d23081f41bbe823b2e48bc6380f3d1718f76399813050038d60c31e092aa01085102126000ac059064315c3b2409d8fc0e07e6fe4221adb18471a3f330d81190439492597901216180b078ee02a980da2e27132000ac058ec3f0541293e970786fdc1216179d3f994021260010c3f038350422202c6fd570b8881c3398c0471a3f37a84330d879012119821161769323763410e0da2e32a4830a562c2345f82b1b52e0000ac05906430ec3f120169bf3497db0b00200fe41e2135a46cd5c02e1c349601a575c0c04150588ae9e018b28027c0dac1048838069685ea193810158ab100849800050960a0620f9bc242380e9bf1497db0b001e2135a46cd5c02e1c349601a575c7ecf9d06fb4206e840c04150588ae9e018b282a6c8027c0dac1048838069685ea193810158ab100849800050ac0590c570281883e6f090089bef301ec394cde395caa2808c1f1584689e738865e95a4cb49c4c82c393da40564f6f7092c92a2047c1aff81e212c30c7824aa93e6f944e0288447943a2e1cbea41080fedac6b3c0c04150588ae9e0329c0dac1048839529787a8c92c8f86a3e85ea193810158ab112e6fac206e8418b282a6c8027c006968043700e192c0849800050ac0590c570281883e6f090089d06fb5be52fa90081ba14817136b1acf0e3c60108518e127d3d3f40c31e092aa6c3720e9be9942e603010541622ba78062ca009f00ca7036b041220e01a5a54a5e4b23e17a8662ac40212600014258281883e6f0904b9beb60dc3496018b28027c0069680849800050960a0626f0904b83a6fa5ba1151be50e3c60c31e010851532b82fa904817136b1acf8e127d3d3f4092aa6c372942e64b23e54a5e62ac40e9891291be31220e,
  0x119b6a04d262b0e6d0402c53a32474c195c92c90fa3c81a50ec941a55f032317c01fe6231cc9a31654a6d06efa08ecb8e0e5024aa952fc24c8ca000286a0635b61177da1c6676d1c6d925ff48a076daeb931c3ae40c04018b28027c006968bebf928d582a6c80e3584c1418e6605c9100421441e3b80a1754e436140081d766404368b80849800050163b21e510667302c0987e0e0882a04e331dc151c0f347488f186ef80f4fd08ecb8e0e52501aec2446cea2047e4cff85cec13e400f4a401478c906c05642004c508241c1e212c8447944e6cd40c04018b28027c006968bebf928d585e04b40e3584c1400421440849800050960a21e510667192e2407e0e1bc70346bbbf3f43f1bf3a8811f488d1d4f9003d290052111e5531c099db1e1bbe0221a2f23b2e38394173b013050038d609193b011661e1b535e043984816f0801310ea5807884b1b191f9c246fb7f446f908903f1393ff8b17f764b2a492821617693237678aa4409543410e03010062ca009f00ca701220e6b2d22fafe4a3565182e0f9c0701a5a0a9b202126000142b0164190c3b0281885a702f526112e3471a3f330d81198732a0ea2413870da2e003a2058ec0a05a098346294c70259e5a207beb0870f805417f7300a0d0ea213520816bd6112e3471a3f330d82a8a02307c1198735611a4d5c56f279ce2197a16102556932d271320b1c051ab3a9f2da3f1bff242b82f9566f1c031ea324b23e030100da2e062ca009f01d9be70ca700a9b21220e01a5a02126000142b0164190c3b0281883e701c30099e6322743d979f1a0b632a4830a562c2345f82b1000ac4190c1902c701430099e6322743d979f1a0b612932169c01241bfb32a4830a562c2345f82b1000142b0164190c3b0281883e6f1c0334746ef80f4fd08810448ecb8e0e503a683c224135145d6434ff84c1413e400c5c48174a401478c900ebe1081034045986cce024645484d481ee4af4f394e712b6c60205af5844b8d1c68fccc3604661cd92ca924a09e862158468aa2808c1f0585da4c8dd9d6bb1e2a915a8d9025509e738865e8d04380c040368b8ae9e018b282a6c8027c0dac104883806968e8d98f0d01529787a8c92c8f86a3e85ea1a761b8d380f7650b98fc6ffc906fec766f9c0849800050ac05906430ec0a0620f9bc169c01400c84d486cce0205af5844b8d1c68fc1e3b94e,
  0x1a08329c1e2a91025505270745840949c4c82c7014907e00c040ae9e018b28027c0069680849800050ac2590643012708f2a7623078aa48b109d1610252713224815b4509034e08ff07884b1501330b1c051394fb1201577186d72f89d1241f86938e1e17ff0a1c1b0ca70149c1f030102ba78062ca0a9b2009f001a5a1d9be702126000142b0164190c3b1c213ae4204a3518b9110a68e4360568088c1f14006fc865c2800e100850580c0ba1d0c89d0e6300f65e7cb8448682d8de5204a707672ab0368b8ca920c2958b08d17e0ac4002b0164190c570ec149c1f850d04385840949c4c8002b1061484a70757fd4aa66228221390d8ad97415611a15903bc537e568eb5b1b2a5a06f97617fbc5816f8e9285949259481c192c8f2706bfe4b11b3388473109c1702a601b015908013107884b139c1342040f2a1c110c31e6293876f1c0d08b3e0e983b9abc43402958c0ddd160302e87432274191c053f1bfd3d979facb342e1121a0b612932169c0b17812d743806b2d24a3566c3065182e0f9c071220e0ca70840475062ca0a9b2009f001a5a32a4830a562c2345f82b11d9be702126000142b0164190c3b028189c1b1aeefc496ea2047c0421440019a084b87e0e2760d0541e12070652852c8f2706943b2506957c0c8c988c738b01956d845df687199db471b64b2a78903b331c1548011f9f06bb268c59bf3f41bbe848bc6038d6130501b01594a3560a9b202a6007884b173b001085102126000ac0595c3b0660b12e0987e0e0882103415042705c195f687198e92856497fd2c8f2722820b06981d4aa665d9901390d80da2e1b01594a3560a9b202a6007884b173b002126000ac0595c3b0660b0263503821034150424f8cc705438f4e8c91f286593e8f22506957c0c8c988c73268c59529b41bbe81718f70911b3932328000a1a818d6d845df687199db471b6497fd22b52612a64aa66390d815be45611ac537e568eb55a119903010062ca009f02fafe4a3560a9b2038d613050639980108510c31e42040f62938701a5a02126000140595c3b02887944199cc4b890580261f83853084139c13fd2506bd640aa9226bbd080fe4427d054703d2a998e436056f915846b14df95a3ad56846645c910343a818b282a6c8027c004214422cf830c798a4e1c06968084980005016570ec0a21e510668e1cc0b090099001f94c2a1c11ee32c,
  0x1212d460b98a4e1c4e46643eae004215ce6300de5203a60ee6af12b2cd018b282a6c8027c006968084980005016070280b12e240260e0625a14c70fcfaa280a5311990d1c3b089c371e81132f8111a89c3317a88191c29492821220e0ca705611a40954149c1d16102556932d2713203010062ca009f001a5a1d9be73b1c21049c230a9b202126000142b0164190c129c3d071e8070952234752e70374a40154c4e1c845a7676c786ef808870c48ecb8e0e502464ec786d4d7810e61205be7091bedfd11be46c647e2c5fdd460b83e70e45cec02004c53e0475ac70b43a9601e212c18b28027c00e3584c14004215c329c02a6c8488380696924a090255192ca9e2a900849800050160702816826188909f0380d1c3b07d59e62ee80709430c7824aa92e6fad8ab114cae1529782a6c800050160702816826188900e07e0f9c3970d4a440fc027c0069682a6c800050ac0590c57028189682402270deb86f1bef000ac0590c57028188142403e089c3540fc3870c42464ed7810e4305a74a8400c7860667091bec6c647d460b83e70bc2004c4bea41ac70b520047c3a9601e212c4e70ac18b28027c004215c329c02a6c84883924a090255192ca9e2a909c4c85ea20069680849800050ac0581c0a04a09862242a270cda2f173b0000d41501a2218c1083870c5be5532b84b23e03010009f001a5a000141121e510907313e600540f9c2f7d024aa830c795297822cf98a2a8a40b85404cdd06b3c66b4818b2908241c3a960027c0069680849800050960a062240346b1c2d0fa43a6fc4f4071dd06b3efc1b06807095c6709d2e6fac7a250a44ffd4c46640c04018b28027c0329c02a6c8488380696924a090255192ca9e2a906ace8084980005016070281682618890a884e70ac189f68723600e3917816b9dbc4597f447038e92859c2c4352c8f279492592a0c7d1b19230803f9741acf719c2702a604803e706bfc07884d701a0f0d2581ab3a1fbf49f2da942e63f1c251ea323c3403a3668881c74b23e54a5e4893bd2919555e02250c01f7adb186112e30881dd330d8441733119873030102ba78062ca009f00108570ca700a9b236b041220e01a5a492824095464b2a78aa402126000140581c0a05a098629706470a40a17812d2fa90002de1121e51200a284e719c27300dea11ec5c2de404ad4b80000585a09a803f1c256d5d92ca924,
  0x11e668a313ede8621d81c65d6b23200656c60ba63a4a16e20c0b23c9cf66a8d2070642004c46c0564a83a81e3b84e0280aa607a8c81a401d2cfc0ca920c2958b08d0c80ad4260b044a4c85a4290c7124329c0488385ea21b0dc8be5598a4e1d28d59acb486acea7c1aed460b83eae1bc7104127e018b282a6c80c040027c0069680849800050ac059060e0622412e1f8569415271558875ac87e0799b182e9a28c4fbb883076193b3d9aa31e1c510788494e8ff57e8b911b92a9173b0081c4f238ffb268fff9403e91098bb3d01c7062ca009f001a5a32a4830a562c2343202b50982c10a9b2038d613050010857330d8119c4d6101f50c31e089c4b129321690a431c4902126000142b0164181c511cc4b87e60276199c6889c53428c845dc520496c0e359b0dc830c781e21240849800350381fa76092fc150ea6187871455456e116b2a24406908b249af12d1aef0d013102b080212600014110d40e1447312e1f980198887192209020713d8bb093d4a03784aa661d87020916398c0379480002c07038678467135ba12902e1529219b80212f68e33e1718f7049f80e983ba482399abbe0c01f73d01c7191ea3f2e0093d414aac852c791ed0793612a6a037872a2aa316e4aa667495e9390d8158b22307c2197040172b6b81dd03010062ca009f001a5a0982c10a9b21d87020916398c0379482e8742e112911ee91aea129321690a0108570212600014058c607022712f805182e8e33e0f9c350e983b149c476b81dd0e1c459abc41603032274191c053f1bfd3d979facb341a0b6129c3d049c233b1c211d9be75f82b1062ca0a9b2009f001a5a32a4830a562c23402126000142b0164190c7124d811a9a15a022307c21970402149caac000160b02644052711cd815a0211aa62307c6798bb21970a0038402149caac0917eb189c432e8742e112000140581c0a02c4b8900983871141c7a03784893bd390d85e022515be4ad97415611ac537e568eb50c31e5a1c3f6293876f1c410e983b062ca0a9b2009f001a5a010857398c0379489abc4acb3402126000140581c0a02c4b89009838189c437035acb49460b83e6fac329c0488380696800050960a12e240381887e6f1c4168bc2464ed92ca8784965e240ed20047ccc3627c1aec46de2fcfd222071d224ef45cec17810e61205bc2004c67091bedfd11be430c79ac70b41e,
  0x1038d61305001085702126000acfb8c193084c1d1602c07038190562204271adf415013309194b1394fb1201571e17ff7186d72f89d16938e030102ba78062ca009f00ca700a9b201a5a02126000140583818888049c696a6c3460f4280b83e7194661b6cda0fdcf0106d8a1045d0e31b0dc80c040ae9e018b282a6c8027c0069683007dc0849800050167b01c0e0621919e1f9c67b812eb9a8c5c2efcfd22262ed22f1824aa95297804215c3007dc0849800050167b01c0e19e1f83e71942e0f927d1986b99403e97438c6c3720e9c613d01c7a0170bb52e04b9c5b36b04049f803010541622ba78062ca0a9b2009f001a5a398c037948129321690a089c4b431c4902126000142b0164181c18890718c25b880301e1c5d5f82e962938778ac8a75d887e0799a28c4fb6f1b35760b8b4a3565182e0f9c5f0d2582ba7832a4830a562c2343202b50982c136b041220e17a88049f8062ca0a9b203010009f001a5a330d81196eb52e0398c037948129321690a431c4902126000142b01641862240fc0e9c616b3dc6709e386fc46a3e87a8c94cae12c8f8329c04883834960127e018b280c040027c006968084980005096188900e83e717d62142125f3c041b081a8f6c306541620d258049f8062ca030103a0403078ee02a9802126000d225abc18890bc83a9d878199c5d497c1e2135c05b641a51064c8c8206a3db0c1a005a85460b86a6b158a4e1c3eae2c260edbc6fa4349607e716404215c488385ea20127e018b282a6c80c040027c0069680849800050ac05906070622412e716c245bd3ce9906957a1887c0c0ef75ac8d1112bb182e9fe862f4c2e2b883055943b631a2f3d825b1e1c571bbe81718f723b2e38394092aa549c55bf3f44881c5889c53330d8119c4d6101f56b2d20c31e5182e6293870fab82f9566f1c4132a4830a562c2343202b50982c1129321690a038d613050010857089c4b431c491220e17a88049f8062ca0a9b203010009f001a5a02126000142b0164181c188904b87e716466d98ac39bdbbb824b24a813421038f4100b14e8c91f28659d306573e8f22506957c0c8c5f007f988c736d8245bd3ce7a18875ac8b182e9b88303d9aa3078ee02a9863998330d8119c4d6101f53839423b2e081f4529b4268c591bbe81718f713050038d601085702126000acfb8c193084c1d1602c07038220421e1c57,
  0x1040027c0069680849800050ac059060c03861042721c0efd1112b4c009d7c04695fe862fe6863f00038e1242fe2643d0b4251c851f0865c19c80900c28cc362e20c046a98f66a5d9e07dc88720672ab0245fac6271fc22712cca920c2958b08d0c80ad4260b042a6c8ba1d0b84484a4c85a4290c71240849800050ac05906071c835c2b41f100c299c80ae20c0cc360f6096c46713478715d8407d4ca920c2958b08d0002b1063074580b01c0e042748887205c7d3a9c7525194d489c7b171c79239c73069c6d109c6b0d2581220e36b04049c691f9c670c01f7612e8330d811a2a869ea241c630ca70030102ba78062ca009f001a5a32a4830a562c2343202b50982c10a9b2398c0379482e8742e112911ee91aea129321690a13050010857089c4b431c4902126000142b0164181c189c7f03176e19ce16400408498000e0b490bf82206e71f435d97e461f4e8ff5559c757e8b911b92a9268fff038d613050239c730d258062ca0a9b203010009f0171c7901085702126003a205abc68441c0e062878562203a0a2f2510241e12271ed597658a032a2442492053abbc02126000d42205c71e40f37c0c6a38590013a9c7525194d13050239c730d258010857062ca0a9b203010009f002126003a205abc68441c0e062878562203a0a2f2510241e2643d0b471ddc6fa81c716a83897e83855b03834100b15f00aff28659d306573e8f2268c59529b4038d663998239c730d258010857062ca0a9b203010009f002126003a205abc68441c0e062878562203a0a2f2510241e0b4558ea71d40a178ab91e8ab32f8ab11a8ab5002de110d48783a5104e239c7308e6f61a3e14b1e3e6190ed6881efb9882ac21c3d864f04a40b8200fe5d06b3c66b49c044dcf023ace8239e01505fdc6709dcc0287a2a646a2a6cbe2a5d7422af844d00c04018b282a6c84c1418e66034960027c01e3b80aa614a6d004215d6c0e0dfa0e15aa0e240849800e8816af1a1107062878560e828bc944090782d0ea859a896a4875d12a0909c71829740e55a20ded860d778219b7485c465f9189f6eee2ce02766201f40849800a18fc50e0241e0ea3ea5a83eb4fb13ee53071bc799a28c4fb7a18876193b759941062ca0a9b2009f001a5a02126000142b016190560901a71b46956d82457c0c0efbd3ced1112b7a188fe862f4c2e275994155943b631a2f1e1c571bbe848bc61718f723b2e38394,
  0x1070e9e67246ef801246c74a40153e400c78c905cec06cce22c090484d4820e28329c11c4fd59213ec52ab190ebaf4f3a8a11e65d2809102c94e7100c040368b8ae9e018b28027c006968e6300de522447ba46ba8aa2809e6081c720e30154cb8448e0e508ecb84c140043700ebe08c1f0865c100c29e8621d6b22c60ba6e20c0f66a5c24723d84722cc80ad4260b042a6c8ca920b08d0c29584a4c85a4290c71240849800050ac059060c038508567247524713f52a324643ae081a9f069c6d440b2539c4330d811a2a1b1aaf869ea241c8901166079c8d2307c7497d91497eb21972d3884730da2e8404750982c10a9b21a0b62e8742e1122a8a027982129321690a431c49071c8302126000142b0164183067824723c23dbd07a1c70e5f390d81587997a18875ac8a28c4fbb182e976193bb88301e2983dba422b924d0ee062ca009f001a5a32a4830a562c2343202b51d870209167081e75c81e94d81ed501a652307c21972d0982c10a9b2071c83129321690a431c490da2e02126000142b0164199e0901e72340a1ea321a9ac52f9564b16d9b09b8b518b8d6f1be93f1c610f9c5f42084d0d084b1f885150966351c8917a881220e0ca701497eb109c87049f83884b7191ea72ae8330d811aa6030102ba78062ca0a9b2009f001a5a1a0b62e8742e112129321690a431c49071c8302126000142b016418300e184722f240801311b01592106e07884b06bfe1396a16b2d24a3564b3f01a8fa1e8945182e902aa5313870fac40e8329d9aeb8c055317a88049f8062ca03010009f001a5a02126000142b096681f63b0302420609062351c894d104290d303c2c9a0395860d7d7c01fdee31a3768189662188cfa3c894721692112e74f1c366aefbb41e3d64007e01506176a08b5d8d00969e67246ef80addb334a401478c905c4815220fa48a07c5b611742004c46c05641e212efc1ae484479676d1c6c4e5a85acb492e7104488397208fd9213ec52ab136c3032054cbebfaf4f3a8a11e65d2809102c928d59e86208c1f05ea186a3e87a251460b9d6b20865c14c4e1c3eb12c60ba500c283a0ca766bac4c142e20c004370f66a5c8ecb8e0e500ebe0368b8ca920c2958b08d0c80ad4260b04682da447ba46ba81c720e30154d1807959007ad4007bce212dc127e0647a9caba0cc36046a98ba1d0b84484a4c85a4290c712418b282a6c80c,
  0x1398c0379482e8742e112911ee91aea2a8a027982010dc03865d8c1c9f0c1c9d501a652307c21970401ca10982c10a9b23202b52c23430a5632a48071c83129321690a431c490da2e02126000142b01641862191ca3e92200c1426f2d7ec28002b3ee3064c213074580b100728570ad053b40172b0e3c63d0525090511209163794812932010dc03865d021260009c160888c1c9fba19e7264cc360468aa1a7a890726c66e0052ab1d26f0540699638cf88c1f03a0ca766bac865c004370e25e8d005cac0e192c38725630154c368b818b28027c006968260b042a6c8682d8ba1d0b8448aa2809e6084a4c85a4290c71241c720c0849800050ac059060c1c9d0b83eb10127e00c04018b28027c00849800e889662946241c9b709c34ff87a8c86a67852c8f8a40b848839ac6b3c1246c59213ee8a11e662c312de8621d1d00f5d66504902ab4a40153e400c78c91080fec6cce084d4820e291c4fd40c040ae9e0e6300de520329c01e725c66e0052ab1d26f05406994368ba38cf83a0ca30154e766bace25e8c18b28682d8043700e192c1c720cba1d0b8448027c006969102c88c1f0865c1005cac387254260b042a6c990eb94e710aa2809e6084a4c85a4290c71240849800050ac059060c056679c994fd590eb9102c94e71184ba0cc360465b7e1a7a8902a8a817548ae49082135343b8368b818b282a6c80849800348ac059607c8ec6299c5181e725f924713f5643ae509c91440b2539c4331c932307c219704030ab88303d9a97091c8f611c8b0da2e32a4830a562c2343202b50982c10a9b22a8a027982129321690a431c49071c8302126000142b016418300e1c95b931c3ae510a68204a3672ab06271054c4e1c3a0ca766bac127e0e212dc647a8fcb81ca8aa8c5b8e43600c04018b28027c006968682d8761c082458e6300de520ba1d230154cb8448043700ebe14069948c1f0865c100c2ae20c0f66a5c24723d84722cc80ad4260b042a6c8ca920b08d0c29581c720c4a4c85a4290c7124368b80849800050ac059060c038331c934d09a039504290d303c2dee31a35860d7d7c01fe92112f68189662188e74f1c34fa3ca01505e49472160002834047c6a0635b611745e04b4bebfa7c1aefda1c6676d1c6dacb4928d59460b83eb9afcfd26aef83a0c8fcb83b41e3ce2121d64007e8c5c2f6a08d448839223475d8d009622,
  0x1c3831baf831957804186003fb182e9591709658c7176545a591545b974745b72693eb9a10afb88304f90a30b8e4524b243d9aa306bfe0801316b1c2d139cab211ca9529b41b9949a4844b9d3c7119abbeed078fda822d2b76cc229ca7679ca54db0c46332440b2539c4330d86401bb5c81b91196ea0170bb52e04b9beb1a8fa1ea32532b84b23e1a0b62e112398c037948911ee91aea2a8a0279821305063998171c79010dc501a652307c21970401ca10982c13202b52c23430a5632a48071c83129321690a431c490da2e0ca707284b917a881220e049f8191ca3062ca0a9b203010009f001a5a779fc380f3d03865d0c1c9d02126000142b016418625087e1083e72b7b8a8134cb066d4100b198ac39b4e8c91d3065724b243e8f206943b5f007f251c85988c736d845d9db47236484fba2847997a18875ac8b182e9b88303d9aa3268c5948bc6081f423b2e08b3ec80189741acf6000a719c2703010062ca0a9b2009f01305063998171c79380f3d529b4010dc03865d02126003a22b016fb8c193084c1d1602c2206287828731445087e1083e8028a158ea2a04e72ac0b1d1112b4c009dd30655fe862fe6863f23b2e558f24883e908b3e6a0659bf06c1741acf96a438f9f0111719c274ea1e6011e50d06e3dbc242040f4f04b34d7c55103010009f013050171c79010dc628411380f3d03865d1a8fa02126003a2111a07d88818a1e0a21a511421f8420f9bc800fc470ea211ca94a14b23c9c1a50ec947215b6117676d1c8e2c09059213eef4f3a8a11e646efa08ecb9e8621220fa422cf9d6b22fc1b05d06b3ec60ba72006267c0445c6709ee20c1804794341b8f66a8d20070c6cce0a807c420e280c04018b282a6c8027c04c1405c71e4043700a980e03cf40e19746a3ea805c2d102c8cc360465bad4b80e6300de5208c1f0865c10072840849800e88ac05bee3064c213074580b08818a1e0a1445087e1083e6f2003f1766108a729d0034801c31b338213520838a4713f56401bb002243b142889766b99e729563717817f4a14190d3fe1ea32805c70f1a99e16f06e34b23e2902e1220e048f4b9abbe423fc3683d1ed078f54b9cda8235091c6da799c91e3241b338213520838a07b92472cc440b21986db453ba4e04053a04033c041b6284116c3720e8324d81ed5c81e97081e7643ae46332612e8539c4330d83884b511a2a869ea030102ba78062ca009f001a5a,
  0x1171c7913050010dc03865d021260008810838079cbb45bd200f8920ae6120b362c0bac1a096d02fda200c37a4697e0ba65cf91e2b20cc3629d7620465b9f872bed4b812e1aeea2ceb14dfafcfd28a5a8568191226bbc3404c45472dc7a8c822cf92cfc1acb49d0e01460b83e9785ea20127e240aa864728c3a0c8525face211cc0c0421011d418b28027c006968ca920c2958b08d0c80ad4fe650e6300de5204a4c81c720c5c71e4043700e197630727c307274260b042a6c85a4290c71240849800050ac05906091cb9bb86e652692112e74f1c366aefa0150617b41e3e9e180f6a08b64e50d0caddb30e85ea136c3118ccb3cd11102c94e7107456e0cc3608a070d9006ed7206e6680cd564016f0e0c0f120bfdf40bed6e0084946534465ba805c2e4a317cdd6b17c64c7166dd8f1665220fa6d4b82183446ae002fc496d2e70669c3a359644953e4a14b23c9e526d4ca8c915ed1a2c06546c056742d61de7f04e5a841e3b86a06340aa63da1c641a64ed9213ee8a172cde8621d6b22c60ba6e20c0f60a34e6300de522447ba46ba8aa2809e6084c1405c71e54069948c1f0865c1007284c80ad4b08d0c2958ca9204a4c8368b9b0dc98a10445ea2128d5822cf9d0e007a8c92cfc1460b83e978127e064728c525fac0c04240aa83a0c8e211ce1011d4043700e197418b28027c0069681c720e30727c307274260b042a6c85a4290c71240849800050ac059060905472dc38f4e8c91f286593e8f22a1cb1251c856d845d9db471b6484fba285cb37a18875ac8b182e9b8830529b43d9aa31bbe848bc6081f423b2e08b3e743805182e0f9cad380f3d1305063998171c79010dc03865d0c1c9d501a652307c21970401ca10982c13202b52c23430a5632a48071c83129321690a431c490da2e049f8191ca3062ca0a9b203010009f001a5a02126000142b016418625087e109cb508f6f41e871c3ae4e4360561e64008902c3b0aed151f8a285cb3ee32c19b6a04d262b0e6d0402c53a32474c195c92c90fa3c81a50ed7c01fc9472166231cd8e660e03cf48ecb8207d122f189a31654a6d06efa05c71e44c140043700e1974084980022142108382a26472c4799330d8a28c4fb1196e760b8bb52e00a9b2002de058447b062199f8138fc72bc69f98ec3c37c0c8c4e8c91988c733e8f20896392513ed6d845d9db4723c801958e860b6484fb773c075a2847991d15b87a1882c8e4d75ac85b802d,
  0x15b0d2368837bd20641639988b1727991c8555943b1bbe81e180b1712051b3dc3190a1305023b2e380f3d48bc6010dc03af809190f8803032ad62c174d30adc2713202126003a22b016b88c1d12858570880e0cc73369a6b975d390d815a029caac189cc90da2e0982612307c2197a271320b0a2419cc1000142b01622022732e581398b1049cc71f9cc54937e390d8f41741158b29b82256b81dd3b1cc3062ca0a9b2009f001a5a2307c2197a5611a56a36630f7b1e180b1712051b3dc8803032ad63202555f824d2c174d30adc3190a27132010dc03af809190f0982610b0a2419cc102126000142b01622022189cc95df5a4e3818b282a6c89c4c80849800348ac0584a16046049cc7ff92c8f84e62c4a40b8123d2c66e0108ff0da0f4514ee9381014e8100cf0106e38cf952e718a1045b0dc80c040ae9e018b282a6c8027c0069680849800050161281a1088808978188465a07e7314edb2116df481821390d81593a34badac537ea8b3a5a1121a296374a14190d3fe1ea326f06e3241c354b23e17812d2902e6b1acf1220e048f4b3683d1453ba4203fb19b803c03f34e03f13a03ef54b9c6284118e128b0e832030102ba78062ca0a9b2009f001a5a8b17278482cd409541d87020a26658e3508173d3410e07ba48c053b2197a630f7b1e180b1712051b3dc8803032ad63202555f824d2c174d30adc3190a27132010dc03af809190f0982610b0a2419cc138849d7484a302126000142b01622022188ec730d1e52fa90532b82a05d56b1acf1220e2902e4d0ee049f819b80509cb5191ca30ca708e33e14aac0e832749bc13897a30e1cbf091cb9501a652307c21970401ca18c1c9f010dc03865d0c1c9d071c832a8a027982129320982c11690a3202b5431c492c23430a5632a48030100da2e062ca0a9b2009f001a5a02126000142b016419cc11226d4121cfc7186060c87e72d464728c52ab1d272f41e72ed22f18207d0368b818b28027c0069681c720c043700e197630727c3072748c1f0865c1007284260b042a6c8c80ad4b08d0c2958ca9204a4c85a4290c71242472e40849800050ac059060e1cbfb9110a6b1c3ae4e436056809406994008902c3b19c151d272f48a33ec60ad1112b5d039568837b6a8379fe862fe08665d206414c2e255943b630f411e2986188494d0ee6399823b2e48bc6529b45b0d23380f3d268c591bbe8,
  0x1a4844b9d3c70d5e043980541856d845d9c246fb138649db471b519cd99abbeed078fda8235471a3f030100da2e062ca4937e6484fba2847997a18875aec0ca700a9b21220e1496e574a022307c2197a009f001a5a1bbe023b2e3839413050010dc03af802126000140585a06842150b4e81a110c056c50280e07e3b1cdbd518c47fe067346164a1cfc734cf47355b6117676d1c8f20735e92112c5e05fc34ff87a8ca74f1c460171c3d2c8f890726ca40b80c04018b28027c0069686ef808ecb8e0e504c140043700ebe276c780849800050961681a108542d030c51687621e0a1440e07e3b2c2519cd90286a0634be062400b7844879448004e73320735c69f98ec3bb7c0c8c3ec60a6a83b32680e561835f68835b5d0357986c68f7b8c68dda06259886233e8f2251c8563998529b45b0d231bbe023b2e13050010dc3839403af8021260001a108b40e2f63d26473552872691ff6d845d5e04399db47239c24703c8018dc58e39a280a2f8111a886c19403e903af802126002de11042150305a1d8879440e0ea1f83e8004e732f63f122734d1ff5e05738592874d852896d845d9db4723c801896000a1ab3a3d3f49f2da942e60301056a3603af83c041b6c372a4844b02126000d21105a108540c1d887828510383a87e3b03e19274d8004e732064b9cd1b98a40b8fcb80661bee8c5c2efcfd270b10e622070c1271a43a0c91c4ed41c09157208fd40075c525b94e2d5124dfab6c62f4f39102c9d28094e713d04e8ccc7334e6300dea11e40f93e2fc53a829fa228f4444ad740e55a20dedaa0de7fa18be6472178219974819063015cd30b895650ed6c348d4a6d18c68bc6efa122f188ecb822732ce03cf4368b818b282a6c8027c00696878602e2c5c9c8c1f0865e8aa2809e739584695a8d9e8621d6bb0761c0828985c48146cf72200c0cab58c809557e0934b05d34c2b70c64289c4c84c1418e660043700ebe024643c2609842c2890673040849800050ac05888733c2e19871b0fae66484fb9dbc45dbf3f4a2847a10e986bd7023d388487c713bb4d822fa316e3f1821049cc7229a270718b7852c7915c8e5b500e5d640e61390d80da2e062ca009f04784c17fb9e0a9b2bb8dcf2a8a0279ce7a18875aec911ee91b90ec82dfa7998b8482cd4095407ba408173d3410e398c037a847903e4f8bf14ea0a7e88a3d1112bfe862f4c2e2631a2f529b46a83795d0395e08665,
  0x18482cd4095407ba41712051b3dc880305f824d3190a010dc03af808173d3410e2713232ad632025530adc2c174d09190f8b17271e180b0982610b0a2419cc1009f001a5a02126000142b0161886673b58270ea58009f001a5a0a9b2000140584a11828188660d1ceb2ffd245dbd46739cdac10525b95d2a69ae5d74368b82a6c88c1f0865e812731ce436056739488733e447ba46e43b20b7e9e662e120b35025501ee905c48146cf72200c17e0934c6428043700ebe0205cf4d04389c4c8cab58c80954c2b70b05d3424643e2c5c9c78602c2609842c289067304027c0069680849800050ac0582273a556b4f90031a02a32fa902116df6b1acf241c358e33e2902e0e988503010062ca1d87020a26049cc70ca701496e574a9a6b975d0da2e2307c2197a390d8159ce5221ccf911ee91b90ec82dfa7998b8482cd4095407ba41712051b3dc880305f824d3190a010dc03af808173d3410e32ad632025530adc2c174d09190f8b17271e180b098261271320b0a2419cc1009f00a9b201a5a02126000142b01608946739c3753ec60a962c6476183b76883b56a83b33e8f2986d3a25162f2380875b0b935d0b9f380c57529b42691ff9891fb1b9949a4844b6d845d9d3c7119db47239abbec81cd75e1121ed078f17812d0d3fe1ea32da82356b1acf4b23e471a3f8e33e29103f0701dd0e1ce10e9ce31220e0491b10ca706484fb1496e54937ea284799440b274a02f413a3030100da2e2ba78062ca0a9b2009f001a5a2307c2197a7a18875aec271321305063998010dc03af802126000140584a1601a8e842150b4e81a110c05673943f543b52e5741acf1ab3a71a909f01116011351791371ea32423fc3c3403a3664b23e54a5e2913ff0d2582ba78062ca009f00ca701220e36b0401a5a02126000142581a5a062760280e9ce306160171c344e4ffd460b83e1c466aefbb41e3f6a08e674d112ef673552273749a737db60915780894ec736ef4f3ab6c61584695a8d924df8525b95d28088c1f0865e8027c0069699213ee8a11e65e8621d6bb000050161681a108542d3a068443015b140a0381f9ce11894fa3ca5f90d7c9432853a4c1e6202146ef808ecb8e0e504c140043700ebe00849800068422d0386309a737d62f5592835b0d236a8d25688b995d0b951bbe023b2e3839413050010dc03af80212600042150b40c0386326448a1673752872691ff3d1cd5,
  0x1a0902550524c64027c006968e43605673ec0849800050a6168260a022150422d01a73f5a64f174f38849d471a3f74a020da9447b36073282307c2197a000a616822159cfb829860dfdfa0dd658b191da20ed5aa0eccfa3ca61b4e89458bc8e021d742e7d6c2e4ce0315d4a6d09a47fe6247ec6e65244c1418e660883dec043700e192c084980008854108b40698c992f673e5a64f174f38849d471a3f74a02330d8119cf50e1cf36d845d9db4723c81cd7a4844b17817f9d3c711805c70f9a857b1ea3291b904b23eec82df1220e0d3d8291b1d09195fa7998b171205011660e9ce30490390ca70062ca1d8708482cd1b3dc07ba464858d4905750a856320a268803008173d4d94cbf8b17271e180b419025030100da9447b360732832ad630adc2c174d3190a279ce4095475aec149319059cf1009f001a5a5fb0a323763410e2307c2197a5611a56a362713202126000142b04a161cf7a6a721275ae5d76066985668fd3c11bc8ac0210b612a99836a511ecd81cca08c1f0865e89c4c8002984a1601a57022119cf53c9a81a349418fdee10396ce0296164a1c88f18f473540e3586e65244c140084980006854350b410af69903873cd7dd1a20c3fa847d874e98c0582a67b1ad96793f5462e44429a9caac189ced519cef0718b7089ce94d822f22b00049cc7852c7914aa66640e61390d8159ce5221ccf911ee91b90ec82dfa7998b171205010dc1d8702307c08173d8482cd1b3dc07ba403af820a26409543190a2197a3410e8803009190f8b17271e180b2c174d2713230adc32ad60982610b0a23202555f824d419cc14784c17fb9e0a9b20da2e009f001a5a02126000142b01673c7f4942e6488d1d3f1821d290054f90032116df242c49db1e2902e0e9885062ca0a9b2009f032ad630adc271322c174d1bbe023b2e1712053839413050010dc03af802126003a22b016b88c1d128425089215030118280e14673bcd1dd290054f90032116df3d1cd5241387a4844b6d845d9db1e9d3c70d0e98958054179801cd7f687199db471b6484fba2847a1d7023dc718c9ad9741c537e6f1b355a0640d1ceb17812d6b2d24a356030100da2e062ca5611a56a367a18875aec500e5d2a8a0279ce22b004aa661d87020a269abbeed07934d822f852c7910718b71bbe023b2e38394089ce9130500ca700a9b21220e049cc7390d8159ce5221ccf911ee91b90ec82dfa7998b,
  0x13d04870c04b70e9a11819a6213524f174fa316e471d01398c0612a672a2a37a842e874790122e20c4bada681e6a8b3a240c3da280a0301047b364928240954062ca0ca700a9be3190a149319009f001a5a54a5e1ea324b23e390d81596bd5611a56a362307c2197a073280da9401166078ee02b0802126000142985a0984e5103e0e02073180742e9a6bb8a151d079c849d819a64f174f471d01612a62e8742e20c681e6240c3da29c2717812d2fa906b1d03390d8159cfb0301047b36073282307c2197a0ca700d3d81220e1ea324b23e291b1f062ca0a9be3190a4928240954149319009f001a5a02126000142985a09828089d09344c78428c427414dac101ee4884d4920070e80de0e6300dea11e40492eb6aa2ce91c740584a98ba1d0b8831a07989030f4bea405e04b68a709dac740c1cca034f607a8c92c8f848838329c00c040e43605673eca46c7c18b282a6f8c642924a0902550524c64027c0069680849800050a6168260a022151d0739ccb473f47873fc1ee483012de066993c5d3d1c740584a9a8a709c7a8c91ecd9ca8a8ba1d0b8831a07989030f4bea405e04b5ac740c1cca034f600c04048838329c12c8f8a46c7c18b282a6f8c642924a0902550524c64027c006968e43605673ec0849800050a6168260a02215042741528b3896ff741acf3410e8c0ddd062ca0a9be3190a009f0010dc03864b02126003a23b05a188260a04e089ac740ecc5001bf6401bba0378398c037a84790124bada46224a8b3a0da94073287081e75c81e94d81ed000d22985a0983e1191c6786a74050a3480e5921352398c0612a637a842e874790122e20c4bada681e6a8b3a240c3da29c2717812d2fa901d932b6b16ff840471819a64a81a94f174f0301047b364928240954062ca0ca700a9be3190a149319009f001a5a1ea324b23e390d8159cfb078ee02a9802126000142985a0984e5103e0885410878229cff5d3d1cb30ce6999006ed7207a54008c53608bce213b680de184a9a14b1e47b41e4e447ba46e43b2f12c21c4674d112ef673e4e6300dea10ba1d1e4049b61174b88312eb6a76d1c8da079918891c20daa2ceb20735c9030f68a709c5e04b4bea41ac6b3d78448638cf83a738c0c04036a511ecd81cca192ca9e2a90329c034f60488387a8c92c8f8a46c7c18b282a6f8c642924,
  0x15e8aa2809e739584695a8d9e8621d6bb072098592ca9e2a90329c04883866585c34f607a8c92c8f8a46c7c18b282a6f8c642924a0902550524c64027c0069685cec0043700ebe02074442274249c4c80849800050a6128260a0421f8307464d1d3d13d7d290054f90033fa841b04c7e98c07f87757b3785dbae8881bb2b96cc501d154608a6000a179d131a9d014d81ed5c81e97081e72104b3612a672a2a390d8159a3f22974f078855339a6030100da9447b36073282a8a0279ce0d3d8291b1f062ca0a9be3190a49282409541493191bbe0173b023b2e3839413050010dc03af82e8742e20c681e62713202126000d22984a099060a21e512000e0541087e0c064819d171c4674d73466af10fc04ab2e40fea129b57bba6301a111e45ecde36a08c62206fd92ca9e2a9018b282a6f8c64286ef805cec08ecb8e0e504c140043700ebe00849800348ec168260a21e139440fa000e0541087e0c06481846731407455ee684479191b90da8231ecbc42bb6ccb0870f460b0d640b13805417f390d8159a3f0da9407328000d22985a0983e470addf78ae9179d135d3d1cb30ce6994008c53607b4e212de14b1e44887d184a99ca8aa447b824aa8ba1d246e403a683cb8833b2f11080fe5a079ac21c3dd06b3c90a21182c35902c4d722c45c22c3e01505fdc604b5cc743ce4360565af436a511ecd81cca08c1f0865e9584695a8d834f6048838dac10ae9e0e8d98f0d01529787a8c92c8f8a46c7c18b282a6f8c642924a0902550524c64027c0069682274249c4c80849800050a6128260a020744437d4ea0ad217117e88b1b380a5859245251d0d5d0b95688b996a8d253d13d73fa84e98c07b3788881bb2b953f54429a9c849922974f339a63884b7612a672a2a2e8745b0d23529b42e20c1bbe0681e61713dd221f423b2e383946d845d241a2d092aa0e9a0f4203f9741acf71a90601d0b9db4723c81cd70301047b361c826164b2a78aa40ca700d3d81220e36b042ba783a3663c34054a5e1ea324b23e291b1f062ca0a9be3190a4928240954149319009f001a5a089d09390d81596bd5611a56a362307c2197a27132073280da94038d6130506399801166078ee02b0802126000142984a09828081cc743e0a7e83bb61837d98e4697d206416399801166078ee02b0800038082643ea4fad3ee7983ed4947437c6092aa,
  0x1239c7301166062ca0a9be3190a03010390d8159d2507884d7081e75c81e94d81ed02126000d22985a09a1e139440fa00150240e878420b46788885892749db538482218b02411b338471a3fadb18bd3ce539c40da94073282a8a0279ce5611a56a367a18875aec000a6168541e142159d256d4e1208862c09046cce11c68feb6c62f4f394e710cc360467484ba1d0b88301e2135a0799c0683c90717e060c81a738c7e747c043700ebe036a501cca0aa2809e739584695a8d9e8621d6bb230377592ca9e2a90329c034f6048838dac10ae9e0e8d98f0d01529787a8c92c8f8a46c7c18b2924a0902550524c64027c00696822742420744412708c7209842a6f8c64289c4c85873dc1673c40849800050ac12842748c4598e92859db47231b1acdc81cd7179d132c8f2722b522a10a31ab3a4813b94e03dd9f2da942e63f0123fa84e98c07b16eb5048748bc64d81ed5c81e97081e70c04b7612a672a2a030105416264b2a78aa40d3d8291b1f062ca0a9be3190a4928240954149319010dc03af802a9807884d4503f57403fb02126000d22985a0982887944af10e143a6000e0541083a1e0e242160119d214d10402c530b8b4c39d58c68bd7c313c92400c78428e6472c4847475201214ce69a8c5b8e24984e43605668fc8a746ce6300dea11e40492eb9afcfd09a31641e72ed8a104522f18307465b0dc836a511ecd81cca0329c034f60488387a8c92c8f8a46c7c18b282a6f8c642924a0902550524c64027c0069696c348c6ef808ecb84c1405cec004370207444e0e502274249c4c80ebe00849800050a6128260a0421f9d1f0e3d3a3247ca1964fa3c8947215b6117676d1c8f20735c5ea206479868831f61d1608aa1a12cc0c04192ca9e2a9018b282a6f8c6428027c18e6614a6d06ef808ecb8e0e504c14122f18043700ebe00849800e885a188260a21e139440fa000e0422d07e220464f0847475c311e1b538482215e3548b02411b338adb18f43e4bd3ce539c4330d8119261819a64f174f47b362a8a0279ce5611a56a367a18875aec010dc03af86c372628411079cbb02126000a6168260f838150421f888229d1b13b7b46796f673cec2736478c9084d481ee49b613e46cce184ba11c68ffd0f928a11e654e710cc360468aa1a12de06745cba1d0b8831a079890726e76c7836a501cca135714dc86,
  0x1351008e0381092247272632f6081d3f49149458bc9a737c7874ec84d4984ba0544bbe1a12dd78d505c4816066986cce21208853c5d3c1ee491ecd84c1408ecb80e35888f1808498002995c7b160350381092215b149b976229d3d38fdd6917b5643e542e59e5de7f15ed180050a52248202a07874eda63884b74f174f72a2a471b5d390d847b36073282e8742e112000a60b1f2c7030331d39081caed3ae5766404e43605674d4207d024aa9526bcd220fa6fc74bc22cf9d0e0030c79460b918699d8a4e1c3eae1285065bc74b5584695a3ad56874ac0c04036a501cca0761c082458e6300de520645e14682d8b84484a74a4183e034f60027c01673c404214448838069680849800050ac098281f862259d37496612088520070d1cb314006fe805c2ed474cc1a74c536087590086d720865c2085eb6c63d0f9036a501cca0207d01e72ec08498002995c7b0d49731c220383d042159d35496520121612137cce698e2121d1ecd800298f415142c5078b51d335c05dc3f563c11bc8a5d3cce698e2d518c68bc36a511ecd81cca05c71e4002995c3531c2203810b14f78ae9069d316325360876b6c608ac0140069ccc3612a5c0446b623c65747871453a3fd5fa2e446e4aa4206bbc8e3fec9a3ffc42f18f4fd036a501cca00e3584c1405c71e430c7804214408498002995c1fa5c9db1c0e2fc74bc2e1996a10f9beb1a8fa1e894030103f1703060f80d3d817a881917851a0b6009f02e112129d29059cf101a5a000142b028188966f1d2d6fad4c4664a46c7cfc5c0c645e14682d8b84484a74a4183e034f60027c0069681673c400050ac0a0622596874ace3f75a45ed5917090b800211597578e67658c714f92598484359c24703c593332f91816e116b249d27268c591b9c7d0c04b7612a672a2a390d8159d2581832239c73173b013050038d62e87401166779fc2e20c07884d681e602a98701a0f241c5f069ce31faaa109d23081d11089d091ea323c3403a3664b23e54a5e1996172ba78291b1f36b041220e0d3d80ca70062ca049c2364b2a492820a9be1c82618c0ddd161cf714931978aa4409543190a2713203010009f001a5a07328059cf102126000142b04a74a402b7654d0da70e8d938f0b5b8a334f9285a81348b0459380a975f0a89410a8f9db47236000ac81cd7179d131a9d016199272c8f2722b522a32457b4664b2a78aa402a98038d613050,
  0x15ba10b61ca8a8e4360562c9aeb931c7536066993c75251ecd81673c4761c082458e6300de520ba1d0b84480421448c1f0865c10085062750c4a74a5d0e300849800050ac098281f838471d4f6090c6fa7e280964635f2710482c6d76eb8ae56a2488752c5e05ad7810e5fd11be67091bed243ad77a46a5cc626e632536c31102c8cc69a40c040fc5c0ce6300de520ba1d0b8448183e034f60027c14069948c1f0865c1008504a74a41cca036a507a049c3204adc61b2d460b83e1b3c0696862750e066993c7525d0e311ecd81673c400050ac098281f8384731c753438ff286592a1cb13e8f26d84f94e8f412516ca284799268c597a188079cbb1bbe023b2e3839475ac8090473b1b2a84072d760719770fd5c81cd75c81b912011ba0170b9f06bbb50487bf3f44893bd171c791d87020916398c037948038d61305001085102126002de890ec0b12e098441387e0e0668021e470e2c70562ba58c73088752ecc640b1b5c8b19708b1751118d0a9be319829f8a07c9d47490eb5de91a973189b98c94db0c440b2331a69461d4503010398c037948060f80d3d8009f0501a652307c2197040214129d29073280da94059cf17186cb5182e0f86cf01a5a189d43000142b0260a07e8e11c4f1d494fe46c131d90eb9fe1db54e710008902c6713cc70567c9d47028be228482c545e2c340c04036a50183e034f607a049c6a04a43204ac00348a60a07e6b13c461d45131c926d7c1a11bcce698e27507b41e3e101cb76a08c5dc3f54aed63248a74f53608754e711fe1db6b6c63d0f90cc74e488f18f4fd024aaa501aed52fc1722c0d182bfea2045e4c040422cf95846a1e709dacb49d0e015a3ad4aa2806a05447a053d460b9686c7c9e609a44e7c3e1bc50c6f89674dc48838d00a540c04036a511ecd81cca0fc5c0c761c082458e6300de520ba1d0b844a447ba46ba84a74a4183e034f60027c0069681673c4042145b0dc80849800050ac098281f862750ec8b1b2aa75d8876071b7e07999dbc45da28c4f9991cdd2691ff1bbe0173b0081d3fa484ed5e35474849f4d7cddb130503839423b2e038d6223c608b3e010851021260002c0984e1f90019a381092215b14472881389d4101addad17f74a3e2e9e03a652036c2e39b55e399c84387dee11a4de9f1a1596280d3e3ff4924814eaef0783224b44f641e3b93c1265080fe4f60a2c0ac200e3584c14008498004d744e,
  0x15c2e7c1aeed4121efcfd1224ef40c040fc5c0c761c082458e6300de520183e034f60027c00421441ee482a6f8c660a7e281f271176757578757ccc754c20e2918b911075454069948c1f0865c1008504a74a41cca036a52066993c5d3d1c753d1ecd81673c5460b83e1b3dd0e3062750c069680849800050ac098281f838221d6573742446ccf4fd24cf8a505d25446cd45ea194c4e1e76c780c040fc5c0c645e14682d8b8448183e034f60027c06a04a5c61b2c5cec004214508108492082db0dc8bebf928d582a6f8c660a7e281f271176757578757db67584cc754c20e2918b911075454069948c1f0865c1008501cca036a52066993c5d3d1c753d1ecd81673c5460b83e1b3dd0e3062750c069684a74a40849800050ac098281f83885830758ec8b1b2aa75d8876071b7e07999dbc45da28c4f90002c0987e198e2159b675851a568eb5973e45a06fbc53549c2c439000140987e198e215978757cffb10b2e9092ef8684b7221d5b3d0487a3170b4f81c1889d591b3381d87020916398c0379482e8742e112038d6819a64f174f47b36173b0010851331d530838a462e4441d51471d4f501a652307c2197040214189d43129d29073280da94059cf102126000142b0260a07e0e1767575701773008f04731e125b10bc66284110108516c3729403e9021260015c1f838228e21512048888756c719c81cd764b2a17816b78ac87f446f9a75d88490eb57e3cede91ad70241973188e92859b82212c8f2794925906b00123e24a97014b3f08f0473902aa109d570c04b772ae82a1003679ca54801c3030101d870209162e8742e112060f80d3d8009f01e81270c812b7186cb5182e0f86cf01a5a7438c02a6007b92819a64f174f47b36173b0010851331d530838a462e4441d51501a652307c2197040214189d43129d29073280da94059cf11b338471d4f000142b0260a07e0e176889d5919665a90e3cfa3c93a3d04945b17810e67091bed243ad77a4689a31665c74d46efa122f188ecb81673c4761c082458e6300de5204a74a40e3584c1400421440849800050ac0987e0e066c70b41588422042755dc45d9ca52a8773a0378612a6002243b1ec58142cc1ae158467554eb9390d8002243b02c2bb71c150cc754dad71501db158b2129d29060f8009f001a5a819a64f174f47b36059cf1000142b0260a19c0e08a441d51f18f4121c2411cc3012de8c,
  0x173c4761c082458e6300de520ba1d0b84484a74a40849800050ac098285111c671d710e3fca19653a3d04a872c41e72ecfa3c82411cc945b2101cb578b89dc3f56a04d06e71f57208fdb613e4e02a5d7c2a25042a3c9a2a8c8e71cc4c1405c71e40e1976f4f3a8a11e64221274042164306a25e86220669990eb9d6b213c751d4e712c6ca8aa281d81c649e60b20735d0c6f98038e45e05ac3205a47a0594964635fd11be5243ad77a46a5cc61d280a6e6324cc69a536c3118b900c0411ecd8761c082458e6300de520ba1d0b8448183e034f60027c07e75ad460b83e75b4069694069944a74a41cca036a501673c40849800050ac098285111c671ae75bccbd8f04732b95a89109245221aef3d0487a3170b889ae122b8a119d55440b2331ad725063f0896b9b3809d2307ca81347f84cd21970380a975f0a89410a8f268aa317145581832239c731305040214011661510a318b888e11d507884d4813b90698616000a719c27701621453ba17a861ab3a4e03dd123e20c81011ea323683d13c3403a36621161d62ac4532b89f2da942e64b23e54a5e03010541620da9447b36073283f17031d87020916398c0379481917851a0b62e8742e112129d298c0ddd0d3d8059cf12ba78060f8009f001a5a1f9d6b02126000142b0260a03e75b57b72a16bb3d3f4092aa4804850c31e942e654a5e06846fa3170b629c9b2902e840cbd8881bb19918d2b9576b121d69490eb50a9bede91a31982973189f8a0119ad99b98c97c9d4722974f339a64db0c462e438849d440b274a023313210e1d67501a652307c2197040214189d43010851030100da9447b36073283f17031d87020916398c0379481917851a0b62e8742e1129abc4acb34129d29060f80d3d8009f001a5a059cf102126000142b0260a07e75aecc640b1b5c8b19708b170da9407328000d2298aedc70ae94704875a470d9d3444b8054181bd91ff5100a1b866117a86f980b5531387859d639db1e221d655e1d5f2fafe4a3560a9be319829f8a07c9c45d9d5d331d530838a462e4441d51819a64f174f471d4f0c812b1a81291e81277186cb5182e0f86cf7438c0301047b361917851a0b62e1129abc4acb34060f80d3d8009f001a5a038d6010851501a652307c2197040214189d43129d29073280da94059cf1000142b0260a07e0e1d6749661208841a657c4274d6b6c61584695a3ad568463520070c48046e80,
  0x1130500108590e1d792a8a027982431be5611a568eb55a180703010819d778c0ddd073280da940805407884d7026c3c1d7b2ba783a181117a8836b044503f5743804e180f2fa906b2d25182e0f9d6d0d3d825983b14a1434170ad07c671d711f9d6b060f89abc4acb343f17031917851a0b62e112129d29059cf154162009f001a5a02126000142b0260a14447030760d1f9410a914c0f0b239c73801c27618d1b5917090c81171ab3a2115974f83e59f06bb659429bf1d7f248423821d7d5483d32691ff1b9949078ee170c8902a980301054162060f8038d6130504503f54e180f3a18112fa90009f002126003a24b8900982813abc0e866351447302a8e1c60890e9420540c18c10922bd8787604f26a1b332516c238ab7878c9b1e894531387592202a10a39d91d54813b90301054162060f8009f0038d6130504503f5078ee02a985483d302126003a224028af03a351448e18043950e10890e942054630782d0ea85afc75fdb333e8f2592202516c4813b9238ab79417498794fb1a815169139f9d925f0301054162060f8038d6130504e180f3a1811009f0078ee02a9802126003a20982813abc0e866351447302a43b5800890e942054630782d0ea85a0875f5af3bf03df90340000d20b0261104e188f075edd75221d735c8219adb18330d81195e74849f398c0379488c0ddd34170ad07c000d22b2243b02c098441383a198e24708c971f20e1d795981e2154d40c8ce6991ecd81cca0002b0a64d84440ea0675dc71b9dbc459700b064b2a8e83c578ac84ea0aa75d887e83657e079998ec69d980cc09a28c4f93e8f2410f13991287250ea55d0b95688b995b0d232691ff529b46a8d251bbe0173b0081d3f23b2e38394a484ed3d0487090473ed078fa3170b84072dda82318881bf7716492bb53b5463325e354612e8539c4adb18f43e4330d811a2a6399813050038d674849f8684b70108591c8a23f9941a0b61d87020916398c0379482e8742e112911ee91aea4d7cddb7438014a1402126000d2890ec0b0261104e0e86647100971f2f78380c0e275d570bb504878881bf4893bd2bb53b55e354539c4adb18f43e4330d81195e74849f81832010dc03865d02126000ac890ec7b13611103a4708c971f2f7838221d73f18f4121c2411cc3012dc221274042166066993c6d8dd2a6a8c5ba10b61ca8a8e4360562c9ae75bd1ecd81cca016,
  0x19684a74a40849800050ac0982851054909d8f496520070c1a657e805c2c4274d6d4121d224ef612088578d52b6c63d0f900421641ee4918b9110076c08498002995c7b0e2228541599c0e088971d8d5d246a50befc4ee53e496676103e120885c09b2b6c60e8604538603d58468a8c90bea41140fd55a3ad41a618cf075edacb49d0e0168601c5ea20dac100c0415058834f60ae9e06cce14e710aa2809e6090c6f89669841ee48fc5c0c645e14682d8b844a6af12b2cd07e75ac183e1460b83e75b4027c006968cc754d18b9140075d10076c4a74a41cca036a501673c51c762400050ac0982851054189d8b5234ea47e4423d05303c2d78d51860dffd0f9258b3cdccc6d75645c25042a4518308e02a6484103c8e71ce00709d8a5d249a547c1a618432045c6ace93e0f95526bce7c1aeefc761c5c71e430760c1e213420151c09b0f075ec3875e4aa280e8604538603d584689e608bea41140fd55a3ad50c6f9acb49d0e0168601c9660ec5ea20dac1052850d05c2b41f19c75c40c0415058836a501cca0fc5c0c645e14682d8b844a6af12b2cd04a74a434f60ae9e1460b83e75b44c1400421660675dc7e75ac183e0027c00696a3037741673c40849800050ac098285111c76255133800b34c00addb8673f9865f3a9d7f5e354f43e4331b5d238ab7460aff26951f878c9b1a8fa1e8945313879d91d52a10a35483d3069d854813b9030100da9407328130500805407884d7026c2ba78060f83a181117a881917851a0b62e112129d2936b044503f5743804e180f2fa906b2d20d3d8059cf154162009f001a5a171c7901085902126000142b0280e86638944470620aa5c7c82243a488bf1d873c86e5234945b04247dd78d53d0f90cc6d75a86ccc9a2a9d188908e71ce8a709d6400dc3204047a8c9d1d31452cfc084387c92618e40ff00c04036a501cca0fc5c0c183e034f600e3584c1405ea20645e14682d8027c0b84484a74a41673c406969acb481e21345c71e40421640849800050ac0a03a198e25111c1882a971f208908150884f81a7614f26a1b332516c5900372691ff239c737474c511b99490c81014813b91714554b3f0941af3210e1f249863903fc1e1d81a484ed3d0487090473ed078fa3170b84072dda82318881bf7716492bb53b5463325c82195e354612e8539c4adb18f43e4330d811a2a8684b71d87020916398c0379482e874911ee91aea038d6,
  0x10e3c61b9949380f3d0c04b73d0487a484ed09047372ae8a3170bed078f84072d3312fd17120513050038d667b528881c3da8235773001b1597819a601166471d9b2a0ea4f811da781831e0107658a054f16e307884b1397876f06e5a886c380547159306b30a1d999abc447b3607328acb343f17031d87020916398c0379481917851a0b62e8742e112911ee91aea129d29061d9d059cf1009f001a5a02126000142b026767ecc500b3b4d8b395c8b35708b33228b3d640b37460b310da9407328000d22981876752475c8b23640b25708b210da9407328000d22991c0d1d9b4695a3ad65cc61681bee6e088670b10d6524964cc754c20765d1cb314069948c1f0865c01e2135204ee41a618500851c09b2501aed52fc1902c6d362c75182c55722c65c22c5c62838da23e51423dcf023d53823cce823c6a2046e4cf89447655460b83e75b47e75acae9e0183e15058836a501cca0fc5c0c4a74a4027c0069681673c400050ac098287665d510896b96bb8a1d87020916398c0379482e8742e112819d771f9d6b060f88c0ddd472cc501a652307c219704021418a0e129d294d8b1d5c8b19640b1b708b17460b15511d95009f001a5a0da9407328059cf1000142b0260a020765e6c3a18114e180f2fa904203f94503f53c1d7b6b2d27438025983b17a8836b0414a1434170ad07c671d93151d8f239d9103010541623f17031917851a0b62e1129abc4acb34129d290d3d82ba785182e0f9d6d010859819d771f9d6b060f8009f001a5a8c0ddd059cf1000142b0260a1447655d510896b91d87020916398c0379482e8742e112129d296bb8a151d8f239d91010859819d778c0ddd1f9d6b0d3d8059cf1060f803010009f001a5a471d89000142b0260a144671d9371cc322adc00b78441383a35144239d910db53a82920070d740e55fa0e156c0e0e805c2f8219b660118e7ca1966d4121da20dedaa0de4fa3c9224ef7485c4494328578b8b6eee2ce0275ecb02366201f6a04d0e02a5d7c2a25042a3d8038e45e05adfd11be5243ad77a46a5c76349a31654a6d06e71f43012ddca4bbc0c040761c082458e6300de520ba1d034f600e3584c1418e6605c48140421660675de30377422596c8c1f0865c10085062762c6cce14e710cc754d18b9140075d10076c1cca036a50aa2809e6090c6f89669841ee491c7624fc5c0c645e14682d8b84481673c66af12b2cd07e75ac183e1460b83e75b4027c006,
  0x10d1db3360568084660ce72ab08c1f0865c100928386a04682d804870fe650722882a6c808498000f02c058341f85276c46b34b01070a3d8139dad009f001a5a0699c72b1da9000141102c299daf67d5d280854c90cc4c84845edc620a542a6fa6af105876ac125e1cc60af41e3b80aa601a671c6c5ace920b86b2cd05ca7824780f4018308108c1f0865c100928386a0404870fe65072288ac76a41cca0645e14027c006968b8448682d80849800050440b0a6139dada4884bd82067d66a15ec2a69f5d26f04525d6d36532fe46ba8f401830812920b86b2cd05ca7824780fc5c0c645e14027c006968b84494069941cca0365d16fa2208c1f0865c100928386a04682d804870fe65072288ac76a4761c08245808498000502c2984e0a05876ada85079cbb091da7331b5d229da508b3e74380461a670c31e5182e2a8a04a14196293870fab82785656f1d2d0e983b0a9a7d1220e0d3d8049da114853f219709a857b401ca14d94cbf099d9f061d9d191785322742c23430a5632a483f170391aea2e1121a0b61c8a2129d2907328059cf103010009f001a5a000142b1da92bf68a02bde3f547a8c92a5c052cfc23c11ce40aa836a50761c0824585ea20329c03a60ee6a15ee46ba8fc5c0cbe559460b83eae0645e14b844a066993c69fd1ecd936c31102c8cc6d748a7694aa2809e159518699d285065bc74b42a69f4488385214fd36532fc0c04034f60127684187674027c0069681cca01673c48c1f0865c100728426767cc89d0682d8b08d0c2958ca920722884a74a400050ac091da70ba6e20c1e2b20f66a8e9d7163420e29d81c65102cb20735ccc3607a8c846b612cfc23c11ce40aa842768c1ee48761c0824594069948c1f01cca036a505ea20329c030c798a4e1d18699d285064488380c042066993c69fcaa2809e15951ecd822cf9d0e01460b83eae1bc74b43a60ec2a69f434f601276845214fc865c1007284c89d0b08d0c2958ca920722881876766a15ed36532fc26767e46ba8fc5c0c645e14682d8b84484a74a41673c4027c00696800050ac229da5754c207d0566a1436a501cca01276840849800348a60b0582bb488c703850842768d7a1819a69f85634f16e3259f81397870301047b361917851a0b62e112061d9d4d94cbf02126000d22982c16012768534410f83268085d03954c3b82380875f007fe08665cb06639891fb55943b,
  0x13182bd1220e4518c098261419e02fa9017812d6b2d23c041b6c306519dbf390d80497ff0ca701497eb2ba780699c703010009f001a5a1098830b1dbd2b1da90a9b202126000141101633020139dc3300dea11ec72bde40192e6bc5224ef43081068831f61d160a999ed48a84cc46c45be2c0906120885205fd51c3f551808f6f41e868a313edd81c6720735c7a8c92cfc240aa81e3b80aa6178ac102551e8621d6bb0365d16fa2208c1f0865e848839724d040487022928d04381cf512a998761c08289906780bea405e04b5acb49360876b65d0714df9681914676fce4360125ffc329c0525fac42620c2a6c8ae9e01a671cac76a40c040027c006969584695a8d89c4c82c76f4084980005044058cc0804e1f9dc1aa9529783a6224a40b806968c60af4ac76a4084980005024058281194676fd7ff0a1db90ca70149dbb0a9b2299daf030100699c72b1da92ba78009f001a5a000141102c76f4d811982f15a029caac2307c219704024a0e1a811a0b60121c3f9941c8a22b1da902126000140b016149dbb8a8e43621a7a856f909070bf14df85e04b4bea41684485ac6b3ca40b9200dbe38cf86666b660318cc3a71cffa025e42511c9a02130ee1740d5ece190f2c198f680d77480dfd5658e53a3f0a8a482076dc329c0488380c040027c0069681a671c0e358f401830810386a04682d8fe650ba1d0b84486e6526920b86b2cd05ca7824780722884c140048702a6c83476cca676bd584695afda23bac18c76d4ac76a40849800050440b028189db90b83e6e84666e7c647a9ca8a8e4360565b1c027c00696824780ba1d0b8448365d16fa2208c1f0865c100928386a04682d804870fe65072288761c0824582a6c83476cca676bd584695afda23bac18c76d4ac76a40849800050440b0281882076dd8d56198d12691ff1518cb0699c7038d63d0060c2040e1a811a0b63f9941b9949a482e1acb341729e091e01c8a2130500121c021260003c0b18c76d77e5a0703f43e4c5816f330d89498c311a2a268085611a869ea5d035756bf6242b8da035d9c2c43988eeb06f06e5596394e8fc6318cb2a292081b9d149db12902e1999ad0ea580486b34b0107009f001a5a078ee02a980699c73d0060e1a813f9942e8742e112380f3d038d60c2041a0b61b9949a482e1acb341729e091e01c8a2130500121c2b1da902126000140b016,
  0x10f1dd9330d811a8e049dd74203d3902aa3c041b2b84156c3720184000a280212606362052d000016150780907e1394c777472d1d870773d420a263b1b4d419ba16180b271328f27a330d811a8e052d0000161e0242b04a776ca212932419e0169aa900054158161e0240f1dd953ec48055c32275c342775a4e38be27442a6c80c040028a018d880005abc43a5c0049dd7200d2774404213c0006362774444773c027c00696800052d06c8a6767496b2808498003481877452598484350803f94813b97011379c247034503f57300ac59333743882f8a97719c27e11344e03dd1ab3a4c1c6f942e69f2da6a83897e83855b03834100b15f00af3f0529f28659d3065737a843e8f2268c59529b425194d790061b9c7d4893bd171c790c2041a20c7d8555241c5f239c731ea321faaa3c3403a3664b23e54a5e291b1f36b041220e0d3d8049b570ca7064858d0a85634905754d94cbf149319059dcd0982615e2b008a4a419e075aec56a3640954279ce3410e109883271320b1dbd2ba780301054162009f001a5a038d613050639980121c078ee02a980699c72b1da90212600014111dcf04c5acb484e4ffd460b83e97a40aa83a772d9213ed24dfa8a11e67d04e8c546aa4cc771c125ffc329c0525fac2a6c80c0401a671cae9e0027c006969e8621d6bb09c4c82609850678042620c2c76f4ac76a40005044059dcd71dd224ef45c71e4306a7c90717ca44ffc349600487022928d043978ac102551b6f49e2a9048838dac10125ffc329c02a6c8ae9e00c040525fad24dfbd04e8c260984027c0069699213ee8a11e65e8621d6bb2447724ec5af5584695a8d8546aa41a671c365d16fa220761c0828990678042620c8c1f0865e8cc771c9c4c82c76f4ac76a40849800050440583a772c2e1bd8237acb90da878ba6d5ee0003c16856072447726aa54bf00e98a393232801cd7f687196484fba2847a1d7023dc70e5f229dc54d821dad9741c537e081dc35a0640d1ceb17812d6b2d2519dbf073d470819f4aa66500e5d5c9341390d80121c3182bd08a4a3410e2a8a0279ce5611a56a367a18875aec0d9745be8881d87020a26419e02307c2197a271321220e0497ff0ca700a9b22ba780699c703010009f01497eb1098830b1dbd2b1da901a5a021260001411016331dc74966120885205fd41e3b80aa60001e02457016330549b88a77158974394541f9dc13a1811,
  0x18a0fcb828c5c2e22070d3e4a14b23c9ca83afc6cce14e710aa2809e6090c0ac62c09051c3f557208fef4f39e8621d6b22c60ba6e20c0c89d0682d8f66a8c1e3b80aa60ca920b08d0c29581cf5136c3118b91102c88c1f0865cb4266e872288368b92a5c04761c08245a3c9e8e6300de5204a776c3c7764cc36046a380849814b4000058541e0241f9de37775bc479434041cbea424c1a95acb4946777c0c0404845266aefbb41e3f6a08d69e180e4e50d0ce85ea33cd107456e16e0085d8f166564016dd6b17c6183446680cd64a317ce526d4f0e0c0f120bfdf40bee4c7166f42d62ae0029c3a353e4a15964494b23c9ca83afe2c09055ed186cce14e710aa2809e6090c0ac5de7f11c3f557208fef4f39e8621d6b22c60ba6e20c0c89d0682d8f66a8c1e3b80aa60ca920b08d0c29581cf5136c3118b91102c88c1f0865cb4266e872288368b92a5c04761c08245a3c9ea447ba46ba84a776c3c7764cc36046a38525fac12775d080f4e40aa8f0106cae1055b0dc806100028a018d8814b400849800058541e0241fa1e77873e7417130e125b942e6629c9b2902e0a9b2018400301000a28011661497eb191ea72ae867b522e8742e1123f2e0a3170b8881c34f92852c8f272a0ebf1b338539c42a8a0279824302b18b0241470fd55c823fbd3ce7a18875ac8b182e9b8830322741a0b63d9aa3078ee02a9832a482c23430a56073d44db0c462e4440b22307c21972d099ba1c8a20da2e4a97011d870209168f27a398c037948129ddb0f1dd9330d811a8e049dd74203d3902aa3c041b2b84156c3720636202126052d000016150780907e87946777eee1b9949a4844b9d3c70d25194d4883e9bf125b805417908b3e8016a1743800c31e5182e6293870fab80a9b20301013050171205011669abbeed078fda8235a7860393943433a17a8cf3441d15b85b8021763c59959005b75ac5f1860d119a0335928c5f3949b53c38303c482ff7d02fb931c59bd0b58ab800a70e8d65912557b46779fc911ee91aea17a88191ea72ae867b522e8742e1121497eb1a9abd3f2e0a3170b8881c34f92852c8f272a0ebf1b338539c42a8a0279824302b18b0241470fd55c823fbd3ce7a18875ac8b182e9b8830322741a0b63d9aa3078ee02a9832a482c23430a56073d44db0c462e4440b22307c21972d099ba1c8a20da2e4a97011d870209168f27a398c037948129ddb,
  0x16bccf66a8c0459818d880034854339422d2060e84e18935d70152940222213a2b02c77d5ca1322742c23430a5632a4834170099af31a0b61c8a2129321697aad07c670b26b81dd3b0328c05530f16dd00a28330d811a8e06362052d000016352060e84e189f654a500883077ccb6682041298832b1def3d1deb8c0553221de9091de52e0d3f2e875d7284b9330d811a8e9003d1bf03e3052d000016150780e84e18890368fced2160e1df1f3b5c0915e8622644a1dd6b229208e6c60ba614b1e3ee20c2447b8c89d0b08d0c2958ca920266bccf66a8e46ba8682d8722884a77b4ec0c8028a0cc36046a385c3224045981e3b80aa60e211c42477963c9e80849818d8814b4000058541e03a1386254a50ed2160e0304d85222b1def7375b60915780896f4f3ab6c61e862158469d6bb15a4cb49c4c8761ca52a06b40015854108b4858380c1220704a77b5c258881c716180b271323b0320b140b0f186901166078ee02a983884718f27a8c05532e0d3f2e875d7284b9330d811a8e06362052d002126000161e0420e8903f0303d1deb071cec0ca80709630377458602c9c4c82c779c3c61a522f18028a0045981e3b80aa60e211c63c9e818d880849814b4000058781083a13862368fc0e08877a5c573b032322748c05252c23430a5632a48099af31a0b6379481c8a29003d1bf03e30f186948bc601166078ee02a980636202126000d21e0428183a13862368382202c779cff57e8b916199271b92a9268fff0c04b73d048708979b81832239d910d258121149049f81f9de39abbeed078fda8235a7860393943433a17a8cf3441d15b89a033559005bc38303c482ff7d02fb5b8021928c5f375ac5f1931c59b763c599ab800860d11a3170b191eaa70e8d8881c372ae84f928565912567b522c8f2757b461712052a0ebf949b531b3388b0241470fd55c823fbd3ce539c44db0c462e47a1882a8a0440b275ac827982073d42307cb182e94302b14a970121972db8830911ee2e87432274398c08c05111d870099ba2c23430a5632a483d9aa391aea2e1121a0b637948209161c8a2129ddb0f1dd91497eb0da2e0a9b28f27a018400301000a28330d811a8e779fcd0b58038d61305001166078ee02a980212606362052d00001615078091de50b866d583eb69a4054ea2045e1e778412775d080f4cf0106cae105640aa9b0dc82a6c80610002,
  0x12d0a80f1e0d6a04682d8fee88720974f461a44a620cac78242278049077e4247795d2128c8e764434960045981e3b80aa600c040028a00849818d8800058541e03a0a06251084782d2e316180b271320b1127d874582e86781f7221e073b0328c1e03330d811a8e01166078ee02a983884718f27a869ea06362052d0000161e0420ea42210640e0ac782465996a438f3e8f24e8f412514396d82455e0225bd3ceadb187a1885611a75aec56932d271320b1e05268c591bbe038394038d6170c891305001166078ee02a981d87294a81ad02126000561e042908840e0ac07088781dc5732274099ba2c23430a5632a481a0b61c8a2052d000078108382b01c2202c7815c9f0c05531695e32e11212980b098ddd000782b230780c320701dd8c053b440b2218d3d231aa10f16dd221dff330d811a8e01166078ee02a98388471091de58f27a0636202126052d000016150780ea72908841902278041dd3b0324417338c0ddd16180b0b1dfd0f1dfb6306757a7d51d4c3b8cb06635596391bbe0380f3d330d811a8e038d613050170c8901166078ee02a98388471091de58f27a869ea0636202126052d000016150780ea42210640888877fcb26b81dd2307c3b032219708c1c9f401ca11690a32274099ba2c23430a5632a48431c051a0b61c8a206362052d000056352060e864088882b02c77f58c90701dd462e422b524d81ed5001a7adb18440b2612e84a97015611a2307c2e8741d87056bf6219702e1122091688eeb04024a1298830da2e8f27a330d811a8e052d00001610884728225e03c77ec2e1bd8fcacb343d18691298832b1df761837f962c643e694474c3b8cb06635596391bbe0380f3d0c1df30e1df126951fa207be2fa90b087116b1acf4bae69d344438e03f7bf03e39003d1bc92e142125f453ba3a04036c2c0629c9b2902e4d7c5512b92371996a12e0d3f691b351a8fa1e8942e875d53164317a887284b90a9b201840330d811a8e038d613050170c89388471091de58f27a239d910d25801166078ee02a980301000a280212606362052d000016150780e828189442109077e41dd440b23b0322307c8c0ddd2197a16180b271320b1df500a28330d811a8e4f046d170c8901166078ee02a98388471091de58f27a06362052d000016150780e84e18935d70152940222213a2b1df70c81c077630727d10076c5a578d1c87826,
  0x1a1bf8108b4908ea85b44da1e25829a229cd74298daa29adfa29758629ed6c4ab54a6d2a04d06e3cfce02a5d7c2a25042a3c9a2a8ebc2745800288e76443404cc32040448055c5e05546a05447a053dc61b5d2c1ad5a4e3828787c2a6c80c040028a04c1418e6605c32242477940459852ab1d278841e3b80aa6018d880849814b4000058541e03a788da8108a4a2b1bcb34170099baad07c1a0b63f9941c8a2672021297cf330d811a8e0116602126052d000016509d278841dd0e18bb6112e3441733a01c2516180b271320b1e1d3b0328c1e030f1e1b869ea241c9b9d840f2a1e19b52e04bada2902e7026c19ad23688f94508f73c08f54e08f33a08f12b88ef71812fa8811b511e150a9b20184054162330d811a8e01166078ee02a98388471091de58f27a0d25800a2806362052d000016150780e828189e1f77f43007dc3862ed84ba2805c2cba1d0e6300b8448de52000158d410a060ea8c191ca2b01c0b1e1d77ec386a058c76d4682d8fee88720974f461a44a620c0849800058d4108847283c786d0376b81dd1690a0e32e099ba431bfd909e131c8a2129e174a81ad3b0328c1e030f1e0d4f90a324b2411a8e038d6170c8901166078ee02a98388471091de58f27a02126052d00636200016150780e84e188fc2a1e190775102c83862ec8c1f18407d6807094865e8306ae458602c9c4c8cc36046a380849814b4000058781084e188fc1b0ac0704a785dcb16d82450881ddbd3ce440b27a1882307c75aec2197a0c1ab9271320b1e133b0328c1e030f1e0d24b24211e0b239d9103010330d811a8e170c8901166078ee02a98388471091de58f27a0d25800a280212606362052d000016150780e828189447855e113f140b489e0f6d8245bd3ce191aaf7a188221e0575ac80881ddb182e9441037b88301695e332274099ba2c23430a5632a483d9aa31a0b61c8a200a280a9b2330d811a8e7484a324b244f90a34a81ad3b0328c1e033884718f27a0f1e0d170c8901166078ee02a98091de506362052d00212600016150780e84e18a422a02c784dac19a9ac9063620004e2583a188d21b0904b9e113024941a5c9a22c504228e63b0eee6010d94fb1829742e55a22e6586346daa34958e6614a6d16c348c6ef804c140e0e500e3580849800350422d2422a1200e03099122783e92a482e10c204acb341a0b63d1869129883021260005435042,
  0x1082bc211e3d4f64f4071c8ae2a924b7e80709510077cf60a2c585cf4ec0c8d0438c83d943c620cb05d349c4c8c2b70cab582c78e6881ef85c2b16c21c452eb9a1e50544823e674d110efc0f8e400f46f26cb47ec7908103d14ee98a726ca40b8665a84341b86a3e87a25230154d4c590c887d0e211c63c9e80e3584c140045993c12645ea2052ab1d278841e3b80ac20127e02a6c80c04006100028a1357153535f1544b834fcba1d75ca12e46478d4cc36046a382278dc0849818d8814b400005820af084109e3b4f669208e48ae2a14b1e3d10077e447b8ec6bacf6f08f4502e46ba8682d80e3584c140045981e3b80ac2135f154508103c7ec78887d00849818d8814b40001582033884241f60e0428184e9d8fc2d3b40b1e396b3e38cf9c6709c3a9b048046c32045cda0f8cf00f7e7cb6a50b98fcb828c5c2e2206e7de3f541c07748ae2936c3118b9108103d14ee9381014e8100d102c98a726ca40b88c1f0665a84865c06a3e87a2512a5c05005cad4c590ce6300761c0266e82478bcde52082458722884a4c8346e745a78cc368ba3c9e950588cc36046a385ea2052ab1d278841e3b80ac20127e06478d42a6c80c04006100028a018d8814b400005820af084089e370774ec5925102c918cc88c1f14e7108ad48865c0aa28184ba12a5c05006f2c9e608ba1d0761c0266e90c7014b844882458722884a4c85a78cc387d03c786c2478c43078ae1a7a8368ba3c9e8cc36046a38045981e3b80ac2014b400849800058202106478d56c75611a2307c56a362197a0da2e330d811a8e052d00001608022169e331c0828995c331d066e9e8620585cf43c4b6dd6bb0d0438c83d94b05d349c4c8c2b70cab582c78bd35714dc8634f48c78b4368ba3c9e8cc36046a39d278841e3b80ac2014b40000582021064091e31500cf6f08266e8682d87228814b4000080840902c78bd72d129320997331697a6ba18ad07c330d811a8e052d0000169c8640908c78b5aa1671a9f330d811a8e749e21078ee02b0802126052d000016080640c1e2b04cc4e6a6dc61b5c280b8661a9cda0f44f0106d52e71b0dc83a788c2a6c8061000c040028a052ab1d278841e3b80aa6018d8814b40084980005878af0422905478a4f22506656a062598ac39597e43570212600286108ea5d1e274d17c01fd30ee26218872c198d563c9a81894e0315c0849800,
  0x101fe62188cfa3c894792d3002b7e654d56c348d74789d4a6d0127e06ef80646a7c5c4f748ecb8e0e50887d1b60914220774ecb317208fd9213eef4f3a8a11e65e8621d6b22c6791c8ae2936c3118b91102c8368b8061000c040028a0cc3600e3584c1400459852ab1d278841e3b80ac20247904e6300de5219032f51e1305fee782a6c846a39c2067d40069d2a5c04761c08245a3c9e814b4018d880849800058202a02c671e556a3c7ee703404c6401a9dacb4852ab1d278841e3b80ac20127e02a6c80c040028a014b4018d8800058201089019ace5c4658b0df6ce02953a82a164915aa34958e6614a6d174789d6c348da20d6f681894fa3c86ef808ecb8e0e500e3584c140045981e3b80ac200849800080420e0b4558fb148b9a6b0c349607ec787a2518ab114cae06a6af4127e02a6c80c04006100028a018d8814b400005862af0302406c4b83e793d342688b14108a313050000d4e12422d0eaa808757e9e4d7435a20dedaa0de74819040008038990fa93ed4fad251e4b1a7df0323263b0f0c9a02963a4b0c9274ef9a5c46120ea41a0d7e58b0df53a829aa391fa331a20d6e5d519ff68189662188cfa3c89419d58e6614a6d174789d6c348de9f54753002b7e654d46ef80e0e50887d08ecb80e3585c4f744c140045981e3b80ac200849800080a8108389918c7924303d9a950f1a81221f40896c75611a56bf688ede455f82e90da2e330d811a8e01166078ee02b08091e413f99432a4830a562c234099ba1c8a2322741a0b602126052d000016080a80b19cb19e47ac18c76d4ac0c0f6790cca920c2958b08d0266e872288c89d0682d97e0ba414b40002a02cb1a23b791516f8482cd8b02eb24957b4803e06825b1c8a23f994000a80b2c688ecf6790d16f8482cd8b02eb40bf678ac8de91aa75d889716bd7e0cc7073d42307c24957b4803e06825b4a970121972d8814031d870099ba3f994209161c8a2129e3f0da2e8f27a330d811a8e052d000016080a8091e411c0828995c331d066e9e86208c1f0585cf4c8dd83c4b6dd6bb0865e8d0438b05d349c4c8c2b70cab58368ba3c9e8cc36046a3814b4000058200904a78fc7020a26570cc7419ba7a1882307c16173d0f12db75aec2197a3410e320f652c174d2713230adc32ad60b1e2f109e3b4d5c54d2e0d3f2e875d7284b9191e350da2e8f27a330d811a8e052d000016,
  0x12d882458722884a4c85a79ac5c71e63c9e8cc36046a380e3584c14004215c0849814b400005884070ac221e6d6e8587284722884a798c427995780894220776b6c61102c958468ca0b14c20acc8c1f0b00a24c8dd95a8d902550c6428865e8d0438cc36046a385c71e404215c14b400005884070ac2205a79ade65171c795e02250881dd0c01f73b13f522b52611e67010dc0f188303af8091e63643aeadb18539c4440b25611a2a8a02307c56a36279ce2197a271320b1e610da2e330d811a8e052d0000162106479a7c21a20c880307d8740992e3582e8330d811a8e869ea32ad630adc2c174d5fb0a323763410e271320f1883091e630b1e61052d00001621064611e6768bc78781c043708ecb80ebe0084980015884108ac07038630b4221e651cb4761c1dcf5082898ec6d35066e858643c3c671c7877963c9e8cc36046a3820796c9c4c814b40000584a091e63cc94e7131c5924aa2801cf509e5cbc78779442797c8ad4984ba12a5c045a578cba1d0761c0266e8b84488245872288368ba3c9e8cc36046a3820796e1a7a814b4000058841902c79841f7221c6b0881dd3b13f5440b22307c21970401ca10f1e1b010dc03af80da2e32a4830a562c234099ba1c8a2322741a0b6640cbd1d870209164784c17fb9e0a9b28f27a22b52612e82e8742e112330d811a8e869ea052d000016210640b042797de1d093d438973f0108573b164922b00612e84a97012e8741d8702e112209161293216a36de91a46023d973e4bd3cec537eb52e07a1885a07074b86c3759941869ea0f19c77f441639f0111241f81e1e236000a0a12371fb720d08fb1208ef1788e50c88dd1a88d71e88d38204150da2e0a9b28f27a0301000a28330d811a8e081e5b0636202126052d0000162b9e5d48dc3423ec4823bc6a235c7a234c5ea20127e2bc78f46478d4a8796452ab1d278841e3b80ac202a6c8061000c040028a018d880005820796de496d82455e0225bd3ce3b16bdadb187a1885611a2307c089e3375aec56a362197a271320b1e57091e410da2e330d811a8e052d000016080a87965a8108972b2b1bcb34170ad07c671e551695e3099ba1a0b63f9941c8a201166078ee02b0802126052d000016080a80b1e5767dc3496048046c32045cda0f8c7ec7a7cb6a50b998a726ca40b866b38fcb828c5c2e22071d22e69fa79357c,
  0x1a3170b2fbc08881c39306af1e8941a99e14f928554b9c0d168f531643291e292c8f270e9e23091de502a6006b008b02411b33807b92470fd55c823f17a88bd3ce539c414aac4db0c462e47a1882a8a074a02440b275ac8279822307cb182e94302b121970b88304a9701401ca13dbc232274398c01d870099ba2c23430a5632a481a0b637948209161c8a20da2e8f27a01840081e5b2b9e5d049f80a9b20301000a282e875d7284b9191e69330d811a8e0734c0f1e7506362052d0000162102c79dc221471963adb189498c35611a268085001a770819f56bf65d1e274e8fc559639640cbd4a9701380f3d88eeb01b8f7da482e10e1a811d8700c31e631db5acb341a0b63f9942091662ac41c825d3d1869129883078ee291e290e9e23170c89091dd902a9813050038d60699c70121c0da2e8f27a4784c17fb9e0a9b2330d811a8e081e5b2b9e5d191e690734c02126052d0000162103c79d51a56bf69731888eeb09b8225631db5129883091dd90699c72b3e6330d811a8e081e5b052d0000162101cd3198b8482cde802df07ba4acb90880308b1727a6d5ee099c25684478f8881c7a207be489cddda8239b087114bae6269cdfbd9cf39d34443bf03e31e1e23bc9b2d1fb1e42040f453ba629c9b2902e173b01b1ab91996a16d82455e02250881dd0d06e1a8fa1e894bd3ceadb18440b253164317a887a1885611a2307c5f82b114aac75aec56a36409542197a318e55320f65091e637497cf2c174d2713230adc32ad60b1e6f221e6d01840081e5b2b9e5d049f80301000a284d5c54d2e0d3f2e875d7284b9191e6901085727b742a876f53820f330d811a8e7fb9e0a9b20636202126052d0000162101c2b3e61e3e881efb6a08e6c21c46f673ce74d110c78788ef26cb47ec7908103d14ee98a726ca40b8665a84341b86a3e87a251b609154c590c5ea205cec2f4f3852ab0220775e8621d2809102c9d6b208c1f2c60ba424f50865c2e20c12a5c05007286447b8f6f08c89d0761c0266e8b08d0c2958ca92246ba8682d8824587228a3c9e806100cc36046a3820796cae7974127e06479a42a6c80c040028a004215c8879b418d8814b400005884070ac0b1e6f50ec947215b609147878146efa08ecb922f1af4f38220775e8621102c9d6b20e03cf48c1f2c60ba424f50865c2e20c12a5c05007284f6f08c89d0761c0266e8b08d0c2958ca92068,
  0x121970401ca1099ba2c23430a5632a481c8a2322741a0b6129e87330d811a8e3b1e7d0f1e7f038d601166078ee0285d5211e79052d0021260636200016108f47a2c0d1d1112b4c008d7a7467ffe8639975ce4980c3693ee60a7e83bb98e469f61835f68835b7c0c8cda06259886233e8f2489cdd251439269cdf639981e1e85221cb16d8245bd3ce7a18875ac8b182e9b88303d9aa3529b45d1e275b0d231bbe023b2e13050173b0081e5b383940881dd440b22307c21970401ca1099ba2c23430a5632a481c8a2322741a0b6129e87330d811a8e3b1e7d0f1e7f038d601166078ee0285d5211e7902126052d0000161098c7a240d1d1112b4c008d7a7467ffe8639975ce4980c3693ee60a7e83bb98e469f61835f68835b7c0c8cda06259886233e8f25b0d235d1e27529b4489cdd2514391bbe0269cdf3839423b2e173b0221c316d82450881dd5e0225bd3ce440b2adb187a1882307c5611a75aec2197a56932d27132081e5b038d6130506399801166078ee0285d5211e791e1e851d87294a81ad3b1e7d0f1e7f330d811a8e02126052d0000161084a7a1c1dd440b20e125b2307c942e62197a3f1e17271320b1e836284110c1e810d01079306af54b9c6c37224b244f90a3291e290e9e23091de5330d811a8e081e5b2b9e5d0116614aac749e21078ee0285d5211e793b1e7d0f1e7f052d002126000161e1e8540dc5a5cd5ae0774c89d0266e8b08d0c2958ca920387814682d87228846a392a06b4247794ec79f43c79fe5217b5d6b38fd645c255e399d9631c53e428dde7f02e391420796c1e3b80a17548479e4307a0414b4000058780b1e836a34646abc028a02a6c852ab1d2788492c901e3b80a17548479e434041e4c1abd52e703a788ca478a4ae797424779420796c18d880849814b4000058780c1e8178345ca782477641a671ccc36046a3820796c045981e3b80a17548479e414b40000583c79ff241b33806b00470fd55c823fbd3ce539c44db0c462e47a1882a8a0440b275ac8279822307cb182e94302b1219704a9701b8830401ca1322741d870099ba2c23430a5632a483d9aa31a0b6209161c8a2129e7b0da2e8f27a330d811a8e081e5b078ee0285d5211e79052d0000163b0ac79f5025099ba1ca26c4070571afb27132052d0000163b0ac129e7b4094266e87289b101c15c6bec9c4c82c79dc3c79d41cd3014b40000588479e40a12011b0c81179f2da3f2e0,
  0x1291b1f120b1d6bb0c191e63f0120492112ba4e5f1a20c3fa840d1d9b5c823f46023d7d874e98c022b0070819fbd07a15822a7b16e4aa66500e5d390d8158799018401493192a8a0279ce7a18875aec1d8700a9be3190a49282160cbf4d9c51540954271320b1e9b00880010dc03af8091e9f486de95059e9106362071e99052d00d9e930001ac423c728381528ca285ea5028322bfc6a890482c545e2c371c397c34766c8ac012a999360875720865c2085d403974e4362b65d0456f9314d518c19fcbe2a3c7a2a45e9f54774444ad300237fa18e65d73926030da44c1400c040aa2809e739584695a8d89c4c82c7a6c02200043708ecb8e0e500ebe0247a7c18d88367a4c167a441c7a6408498000695c0e8e20e0b43d1a86a9ea30d7d3a82b681895a20decfa3cb485c449418bdaa22d5fa22c6ce0295ecb02558e6614a6d174789d6c348c6ef808ecb84c14004370e0e500ebe0247a7c0849800068382d0f4269ea175dce221647e2144d4202301444d27a6c824584a7a743c671c18d88167a4400068247a7d025099ba1ca26c407057195f5611a2307c56a362197a271320f19c7052d0059e910001a0904a7a759b9209161c8a2052d0059e91000d20b1e9bca0167a4400071e99cd8167a4400479e974f24167a4400486de95a50167a44000d9e931c15c1cb482459dcf504a798c427a3cec79f43c79fccc36046a3a3c9e814b4000059e910d7d3a82b681895fa22c4fa3ca164a0c947a3492400da22e65aa349520783cf47a2d6c348d74789d4a6d08872c46ef82f673cdb60914e0e508ecb85cec2f4f38220775e8621102c9d6b208c1f2c60ba4865c2e20c1007284c89d0266e8b08d0c2958ca920f66a8c682d8722884a7a1ccc36046a3820796c0e3584c1418e660045981e3b80a17548479e4ec79f43c79fc787a140849814b4000058427a3e0a7e86061839b9864689e0866502126000fc5a48fa93ed4fad3ee7981b0947a342e0f9e4f1993c32490052c8a43d11342688b53ee60a7e9e4d61835f68835b5f007f3f2e0da0625988623a3170b3e8f28881c7251c85018402b9e5d6399814aac749e214f35022b004d7c50d208d331d87294a81ad1e1e85398c037948529b45d1e275b0d23049f8191ea72ae86781f72e8742e1120a9b20301000a284c0c3b631e891bbe023b2e173b03839413050221cb16d8245bd3ce7a18875ac8b182e9b88303d9aa3081e5b0881dd440b22307c,
  0x1c02f41e852a99a8a313e5360875403974e4362647216b65d0456f915650ef14d506efa122f198c70c45cec0307ab44c140aa2809e739584695a8d9e8621d6bb09c4c82c7a6c761c08ecb8e0e50227ac60675de3037745832fd367145402200043703c671c0ebe0247a7c367a4c1c7a6408498167a4414b4018d880006b100e8547acd4fb691af92fa90291b1f0c8b036b16ff049211f78e5f121d690d1d9b4db0c462e422b0070819f4429a4aa66500e5d390d89c849d159cfb030101493192307c2197a2a8a0279ce1d87049282160cbf4d9c51540954271320b1e9b00880010dc03af8091e9f06362071e99052d0059e910d9e930001ac40e2089eb16c1ef267dca46c7c4875a46479812484536c3118b906883034766d10494df61d08ac01608a92a999403974e436032681c565af40c040524c648c1f0865e8aa2809e739584695a8d8761c02a6f8c642992ca9e2a9124a085832fd3671455025509c4c82c7a6c02200043700ebe0247a7c367a4c1c7a6414b4018d88167a440006b10728207abd2653c12352b92376c2c01a8fa1e894691af962ac453119917a88291b1f120b1d6bb0c191e60492112ba4e5f1a20c0d1d9b5c823f46023d7d87422b0070819fbd07a15822a4aa66500e5d390d8158799a28c4f9991eab688b993d1ea71bbe0173b013050018401493192a8a0279ce7a18875aec1d8700a9be3190a4928240954271320b1e9b8404718684b7819d778c0ddd160cbf4d9c51500880010dc0f19c723b2e3839403af8091e9f486de95059e9106362071e99052d00d9e93021260001ac403a0c038151ead0d7d3a82b687895fa1810403849a02966191a25ee11a1f9a18fd567aa6f673cd8e6614a6d174789d6c348daa34946ef808ecb84c1405cec0e0e50043700ebe0247a7c08498000683815122e62647aac35f4ea0ada06257e88b13e8f285928363998529b45d1e275b0d236a8d251bbe023b2e13050173b038394010dc03af8091e9f021260001a0e05448b98991567aa43bb98e469f3ec60a61835f68835b7c0c8c6a9ea3da06259886233e8f2251c856d84f9a285ea5269ea1b50487639981d870840471819d778c0ddd160cbf4d9c515008800f19c7529b45d1e275b0d231bbe023b2e13050173b0010dc3839403af8091e9f02126059e91052d0063620001ac403a72838150f47a9d2652b92376c2c03c03df1e894691af9942e662ac453119917a881a9abd,
  0x1462e44db0c4429a9c849d70819f4aa66390d8159cfb271ed9071e99052d0149ee9161efd009ecf06362031ed3491f05059e910d9e931d9ef9231eeb2a9eed000e20891c7c1e82409ee1161efd001247c172a789ee5161efd001927c0dbe319edd161efd0002a7c04ddb161efd00135f7bfccbf009ecf059e914d9defb000587bf4515052d0209ef50013677bec70209ef5000767be425906b1a41b6e000f67bde26271ed941b6e000827bd588309134d2b180b099ba0b1ed7271ed906b1a052d000106db988759ee7001e8cb11a569ee3001587bbca0279edf000aa7bb47c219edb0008c7bad319009ecf059e91271ed9000527ba6ec271ed9001d67b9ea4271ed9001e27b9636271ed90015a7b8d54271ed9001027b85ce271ed90009e7b7d0a271ed9000c67b757a271ed9000867b6d320b1ed70009c7b65e9b009ecf0002c7b5d62009ecf001507b5410009ecf0000c7b4c40009ecf000067b4480013fa000027b3c50013fa0004c7b34d6013fa0000e7b2d66079ec500004fe9fc079ec5001de7b1cee02a620001e7b169806b1a0000a989025099ba1ca26c41ebf271320b1e9b00880010dc03af8091e9f0f19c7052d00001ac69eb10e1ebd819a64f1eb91d870059e91479e970001ac41ebf3605668fc4649848a746d8a1044307aec207adca46c7c126bddd0e30524c6524a085832fd3671455025509c4c82c7a6c02200043700ebe0247a7db0dc83a7ad6066993c7ae4761c01c7a64367a4c167a4418d891e7a5c0849814b400006b100e1ebd1c466a679674d112e88113b6f673cc84d49b613e584ba28a11e651c68fccc360468aa1a12dcba1d0b8831a079890726e76c780610135714dc865e8aa2809e739e8621d6bb02a6f8c6428661a9d52e72066993c7ae4761c0a46c7c126bddd0e303a7ad4524c6524a085832fd3671455025509c4c82c7a6c022005cec0207adc043700ebe0247a7c1c7a64367a4c167a4414b4018d891e7a5c0006b100e0307aecd811ad8159a3f8f046f22974f271320b1e9b00880010dc03af8091e9f071e990d9e930001a5713c7ae446f339a6842d83884b7390d8221f4729eaf1596bd2307c2197a5611a56a36271320b1e9b00880010dc03af8091e9f1d870059e91479e9702126071e990d9e930001ac4038081eb712dc887d1ca7abc547acc227ac60675dc3c671e3037745832fd367145402200043700ebe0247a7c0849818d88167a4414b400006b100e9eb563251808f48a,
  0x148dda46cd58a726cf010bd3810b67091c0d145d64664b04e860471638e44804bc5e04b4bea40227c442411ce10b60e43605674947a2506a3e94c46646479868831f61d1607c4c34f601e7b141ac69e8cb00a9880849804fe8767be49c7b64587bf418d882a7c040c7b4c027b3c067b45247c1414b40167a44003883e0a054229c67c5c61b773407bbc1597fc8f29079ec5002128e8841513e1b1f1519b4fa3ca62b0e6c9432853a3c2d78b8b6eee1645c2662319ea04d13e428e6472c50402c57c02bc9a316484d4b4c39d4306a1d84a989268a56c348c6ef808ecb85cec0e0e50227c442411ce10b60e43605674953c5d3c084980e7b2c4c7b341e7b141ac6804fe8367a4c167a44aa7bb48c7bac767be41c7a649c7b640038854229607c4d74f339f0d291b1f049f0f0838a471f074429a390d89c849d159cfb06362149ee9491f05059e91009ecf231eeb271ed9000e2089f1104cc4e4845c61b5c18d88587bf49c7b64527ba400150127c3cf225162f6a1b33239d911fb1e2218cb2691ff1b9949a49f0b629c9b191e61a20c5e3547d874f41741582a64204359b822167b52592209492592a10a33d0487480e59a316e398c037a84790124bada2b88dda88117879f093c042f4e042d9c247034517591992c13a1811c58e3912012f17812d2fa906b1d030d3d8170c89090473842d80838a471f074429a9c849d390d8159cfb039ecb131ecd079ec5013fa06362031ed3021260a9f01019ed1161efd271ed9561eef06b1a1d9ef9009ecf491f05052d0149ee9071e99059e91231eeb000e2088ce0f8287c366c1f844b3684439d3c7119abc4acb90a6d5ee6844793a2044ed541ed5161efd271ed9000e21183e43850ed43950e9af1c0a49f0b7b9a111e4e46e4288113b7b2f12f6632cf4fd2c21c3d78d503a9b0ae234e01505e7d05d04da0f8e000290810d66e088650b986a6af65217b4fc395dd6b38ffa63015e399d645c25ec39659631c42e39153e428c84d48306a1d84a989268a4ba1d0b8831a0798904665bc6cd52853ec5c32242411ce10b6020e291c7c1d10a6a721274e43605673ece86045145d653810b4f010be7091c0f1638e4bea404804bc5e04b5ac740c34f609c7b64587bf408499507b54027b3d587bbc18d880c7b4c14b40067b442a7c049e7b7dde7b1c1e7b141ac68767be4367a4c167a44aa7bb48c7bac1c7a65247c14527ba404fe800388223383e0a21e7c25af94a14fb2fa90291b1f0c8b036b16ff049211f78e5f121d690d1d9b500e5d,
  0x12518ab114c46645ea206479868831f61d1608aa1a12dc887d02411ce10b60e436032681c565af4547c9434f60227c442a7c0418d88027b3c527ba4587bf414b40167a45247c14067b449c7b6408498767be41c7a648c7bad587bbc367a4c003883e0a1f2967dc48055cda7c85a46be434f6032681c14b40527ba42a7c05927c0c18d880c7b4c9c7b641c7a64587bf4027b3c167a44000f828080422411c7c9e2a8684b72e8742204112e20c0e9f1f9d86e3681e6241f23531419120157691af9229f1b1bbe03839423b2e090473842d8390d8173b0159d25089f110d3d8271ed9161efd031ed306362071e99052d0149ee9009ecf02126131ecd039ecb1d9ef9013fa079ec5059e9106b1a000e20f828151f257c643a6cb58ab10ae4a3d145d65087c75b0b0066d5848055c5e05546a05447a053da46be434f60da7c848a7c6c2a7c0418d88027b3c167a44587bf4527ba414b401c7a649c7b640c7b4c003883e0a054241f23709c322bfdac6b3f1c6c1e380fdc7a053c6a054448055da46be434f6018d880c7b4c027b3c367a4c167a44527ba4067b44767be4587bf41c7a649c7b6414b40000f828470da7c861e618a7d4f04b3a81342a3245f0a89410a8f268aa31b1acb72a2a6018112e87443852e72e20c3692f5681e6390d8159d252b928f451759421f1d6c2c019b561201571781551a81511e814f691af90d3d84d7deff3d9ef7079ec5013fa06362131ecd06b1a009ecf0a9f01161efd271ed9059e91149ee9052d0071e99031ed30003e0a0542d242e10ea4703a191f1fa999e5924ba1d1182bfcb88321e029a0798bef0090726e4c1abe76497d520f4d2a998e43605674941c7a64367a4c027b3c167a449c7b6418d880c7b4c587bf42a7c04067b4414b401e7b141ac68767be4000f84e1511c8028a7314451a08421f1d300dea11ec3965e40493e0f952eb9afc4755520f4dc06cb47e7c64da0fdd14ee9d0e20ae4a3d8ab105ea21c67c5c6a3e87a2514c46646479868831f61d1607c4c34f605674949c7b64767be41ac68587bf42a7c0418d88027b3c527ba4067b45247c14167a441e7b14003883e0a054229f1b4985b0dc8227c442411ce10b60e43605674949c7b6404fe8587bf408498767be41ac68167a441e7b14003883e152761f9f197c54924a162c0906f41e868a313e4b23c9e644a1c88f1a524964a8428cf4121d2039668c5b8e6300dea11e404a927c2c9a547d2eb6908497c7e4986a2045db0b021e028ae,
  0x11e9f4d121f53063626b1f750021e7de525741b6e271ed9161efd691f49071e99229f33581f630e1f73001107dddd03019ed1071e99161efd149ee90d1f35049f3b271ed90e1f73001ac7dd5f6f461f71000387dcd4fb2f88a0c8aff121f53063620d1f35691f49031ed30d9e93059e91009ecf0e9f6d339f31001187dc68479012e98c04bae67b1ad9bf1d2f4d925d271ed9161efd291f43071e99229f331d9ef9391f3d0d9e93059e91561eef629f6b0e9f6d081f5f6c1f57841f372b9f593c1f5d339f31013fa079ec500038c71f6f6cb4027b3c18d89087d842a7c05147d6c127ceca47d0c5e7d44ae7d64da7d14347cd4647da4000e9f6db10a47d0c647da400629f6b798587bf4687d9c00191f698309c7b65f67d94001a1f671d1607d8c007d9f651dd730131d76cc892c931c59248412cd84a99ca8a8e47cf4aa7bb4ce7cc4207d7c1ac681e7b148a7ccc1c7a64367a4d2a7d1c00581f637c74a47d0c347cd5b07d5c8a7ccc7a7d346a7d3c5e7d44487d4c667d54207d7c00421f611d160a98b88319e4fd5a079910a68906806721264e47cf49c7b648a7ccd907cfc1c7a64367a4c587bf48c7bacda7d14487d4c14b40a47d0c347cd4ce7cc400081f5f48d4027b3c2a7c04a47d0c7a7d345e7d44347cd4127cec18d886a7d3c487d4c003c1f5d5d640c7b4c347cd418d885e7d44a47d0c587bf4487d4c00451f5b4a3c027b3c18d88127cec347cd46a7d3c5e7d447a7d34002b9f59b00a47d0c2a7c05a47d24006c1f57d582a7c05a47d2400199f55055da47d2400121f530555a47d2400179f510545a47d24001a9f4f053da47d24001e9f4d067d2a7d1c00709f4b6be418d88027b3c127cec8a7ccc347cd4587bf4527ba414b401c7a649c7b64a47d0c00691f49998767be4e47cf4004a9f477c84a47d0c8a7ccc127cec00369f456c7c027b3c167a45247c14527ba418d88127cec00291f433974aa7bb4767be4567ce400501f413984767be51e7a5c567ce400641f3f360567ce400391f3d48449c7b64587bf418d88347cd400049f3b68fc9c7b64367a4c1c7a648a7ccc00159f3911b41ac68ce7cc400841f375b8c167a44ce7cc4000d1f355d3cce7cc400229f336991e7a5c167a44e27cbc00339f317cb44e4844286c7c3e7cac227c4418d88587bf49c7b64527ba5247c14167a44027b3c00389f2f766c8a5ba42c7b5c027b3c167a4400388120e0347cb7888e1af77186d70a1f2906362271ed9161efd149ee9000e20f9f2b0fe5c06cb5d0e20da23e5c604bd44682d1c7c9cae4a3c7ec7914ee86a3e87a,
  0x1397c567ce41c7a65407d05187dc4367a4c767be5c27d2c8a7ccd367ded727df4007dfcb03059e910d9e93009ecf879f79001727df70c441f77001367dedc27031ed31a9f4f0d1f35]


def dictionary : Nat := 0x4207a9ec844635f07d47503543042394d6e67d79c0ef81049032b8056e034d3d359835c2ef41e1e583625aaaab4f405c82a407d13c22a840805e2da510627c68f080a6b4e1400aa6710bc274b3b13407ade507de2dd9e288526c01bd87fc1d83682f790fa6283641391b8a9723a00a19a884265067bc982e1492fd0f26c55dd4aa9132c2d4c3040d1ba09c01f26e1355bce47492c432d10f0e8e1e60ff1cfc1141044f99b041fd449444bde02f2bc11de203075901b10495b1ec03bd7f4d07ce834ca3a283a82802e11ba97048660d50534e692263145ea42d10f00084d19b14d843af1af8398c0c2452711ec46bc3983d850d06c6ee97949a59a986c68a78dc18dc3793a1a1b873636f841524e27e16800209403d8b151d81b11ffc43859d000c7542cf109209d7aa09260b50d49ac8e00501ab02d5099a71bffc476be29b7053e7f264284180318de73b1cbaf95ec240b1ab339c6b0989094857563339b1cf3fe828e127a6db4248853961aad0c169735f35e84ac0fc9b15d1ad2876242e35415f213061226c10c68103a722005256314313fa1ad00173af48b055074c4d4a241030fb2d19a511cf5a22412352b3f04bad180ab44ca29c12f1d5c250746c7fa750cde7f135e35c936a8126197e18ed4ade87a0afbf482620055f2174d9093ae82ebf08fba09f4f9404cfbf1068363304d2a4110049ab58fc5733f1aece6de6a63f0c1b4d744d230390ecd62bb28569f6cae26b21d09f5cd28c4d20f8e7c82ccd01d4b3e2970ce604e1af272e87f8563f4cfaa6ae09b137328c5775972454fc08732ba80197304396313fee12b0126f83131790b2f48795e0d4656d35521dcd6d05c358451cd7087b89710f62390f7899b18c13c759309af2400287520495e814487167e874922e43fa6790390f2ba1207e7834f50f648a0740c1260f8a309c4c1a69c269af759a34a335a911074a6114379851a20b0248c04e0d526a1a7109a8882c5f63b8275686c36221b300af2b9ca492c0e99642043e9a749aab2a67c9a8225e69a051ad089af10709bb0dd84e1d726d91144d66160e8abcd84c41026f111c4d84dd0e9938178841409c98550f8b8d2be937c9b2b9d00109b58ec13c30baf15718af2ca395ed6564e148cb17827a415050938c00ebdc09de7874f6000

noncomputable def decodeWord (fuel : Nat) (w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ next n =>
      Bool.rec
        (Bool.rec
          (Nat.land (Nat.shiftRight dictionary ((Nat.land (Nat.shiftRight n 1) 511) * 13)) 8191
            :: next (Nat.shiftRight n 10))
          (Nat.land (Nat.shiftRight n 1) 8191 :: next (Nat.shiftRight n 14))
          (Nat.testBit n 0))
        rest (Nat.beq n 1)) fuel w

noncomputable def certificateTokens : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ rest => decodeWord 640 w rest) proofWords

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate : ¬ FormulaSat formula :=
  check_sound formula (unpack 11 keyWords) certificateTokens (by decide +kernel)

theorem table_agrees : ∀ r ∈ rows, f (fun i : Fin 6 => r.testBit i) = table r := by
  decide +kernel

theorem lower (s : Nat) (h : HasCircuitSize 6 f s) : 6 ≤ s := by
  by_contra bound
  obtain ⟨C, hC, hs, hev⟩ := h
  have hv := valid_ofCirc 6 5 table (· ∈ rows) C hC
    (by have hsize : C.gates.length ≤ s := hs; omega)
    (fun r hr => (hev _).trans (table_agrees r hr))
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact certificate ⟨val 6 5 M, enc2_sat (by decide) hM hnf hlx⟩

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [2, 7]⟩,
    ⟨.or, [6, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩], 11⟩

theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = f x := by
  decide +kernel

theorem witness_mono : Monotone2 witness := by simp [witness, Monotone2]

end PEqualNP.Outside.L_meta_13047

theorem PEqualNP.Outside.L_meta_13047 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4004178602) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4004178602) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have hsize := PEqualNP.Outside.L_meta_13047.lower s h
  exact ⟨PEqualNP.Outside.L_meta_13047.witness, PEqualNP.Outside.L_meta_13047.witness_mono, hsize, PEqualNP.Outside.L_meta_13047.witness_eval⟩
