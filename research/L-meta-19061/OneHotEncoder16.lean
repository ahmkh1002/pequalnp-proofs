import Mathlib
import PEqualNP.Defs

/-!
# The minimum size of the monotone encoder for sixteen one-hot input rows
The 21-gate existential in L-meta-19061 has no witness. The construction at
the end attains the matching upper bound. The counting argument tracks how
many gates and output coordinates can still distinguish a restricted set of rows.
-/
namespace Encoder19061

abbrev Row := Fin 16
abbrev Trace := Row → Bool
abbrev Domain := Finset Row

def Same (d : Domain) (f g : Trace) := ∀ p ∈ d, f p = g p
def Full (d : Domain) (f : Trace) := ∀ p ∈ d, f p = true
def Sparse (d : Domain) (f : Trace) :=
  ∀ p ∈ d, ∀ q ∈ d, f p = true → f q = true → p = q
def Simple (d : Domain) (f : Trace) := Full d f ∨ Sparse d f
def Active (d : Domain) (f : Trace) := ∃ p ∈ d, ∃ q ∈ d, f p ≠ f q
def Zero (d : Domain) (f : Trace) := ∀ p ∈ d, f p = false

structure Node where
  left : Trace
  right : Trace
  join : Bool

def Node.val (g : Node) : Trace := fun p =>
  if g.join then g.left p || g.right p else g.left p && g.right p

/-- Count a gate only when its output on the surviving rows is neither simple
(constant true or supported on at most one row) nor a copy of either parent. -/
def Charged (d : Domain) (g : Node) :=
  ¬ Simple d g.val ∧ ¬ Same d g.val g.left ∧ ¬ Same d g.val g.right

lemma simple_mono {e d : Domain} (h : e ⊆ d) {f : Trace} (s : Simple d f) :
    Simple e f := by
  rcases s with h' | h'
  · exact Or.inl fun i hi => h' i (h hi)
  · exact Or.inr fun i hi j hj => h' i (h hi) j (h hj)

lemma charged_mono {e d : Domain} (h : e ⊆ d) {g : Node} (c : Charged e g) :
    Charged d g := by
  exact ⟨fun hs => c.1 (simple_mono h hs),
    fun hs => c.2.1 (fun i hi => hs i (h hi)), fun hs => c.2.2 (fun i hi => hs i (h hi))⟩

lemma active_mono {e d : Domain} (h : e ⊆ d) {f : Trace} (a : Active e f) :
    Active d f := by
  obtain ⟨p,hp,q,hq,z⟩ := a
  exact ⟨p,h hp,q,h hq,z⟩

lemma simple_congr {d : Domain} {f g : Trace} (eq : Same d f g) (s : Simple d g) :
    Simple d f := by
  rcases s with h|h
  · exact Or.inl fun i hi => (eq i hi).trans (h i hi)
  · exact Or.inr fun i hi j hj ai aj =>
      h i hi j hj ((eq i hi).symm.trans ai) ((eq j hj).symm.trans aj)

lemma kill_sparse {d : Domain} {f : Trace} (s : Sparse d f) {p : Row}
    (hp : p ∈ d) (fp : f p = true) : Zero (d.erase p) f := by
  intro q hq
  obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hq
  cases h : f q with
  | false => rfl
  | true => exact (hne (s q hmem p hp h fp)).elim

lemma kill_sep {d : Domain} {f : Trace} {a b : Row} (ha : a ∈ d) (hb : b ∈ d)
    (s : Simple d f) (hne : f a ≠ f b) :
    ∃ p, (p = a ∨ p = b) ∧ Zero (d.erase p) f := by
  rcases s with h|h
  · exact (hne ((h a ha).trans (h b hb).symm)).elim
  · cases ea : f a with
    | false =>
      have eb : f b = true := by cases eb : f b <;> simp_all
      exact ⟨b, Or.inr rfl, kill_sparse h hb eb⟩
    | true => exact ⟨a, Or.inl rfl, kill_sparse h ha ea⟩

lemma zero_inactive {d : Domain} {f : Trace} (h : Zero d f) : ¬ Active d f := by
  rintro ⟨a,ha,b,hb,z⟩
  exact z ((h a ha).trans (h b hb).symm)

lemma zero_free {d : Domain} {g : Node} (h : Zero d g.left ∨ Zero d g.right) :
    ¬ Charged d g := by
  intro c
  rcases h with h|h <;> cases e : g.join
  · apply c.1; right; intro p hp q hq
    simp [Node.val, e, h p hp]
  · exact c.2.2 fun p hp => by simp [Node.val, e, h p hp]
  · apply c.1; right; intro p hp q hq
    simp [Node.val, e, h p hp]
  · exact c.2.1 fun p hp => by simp [Node.val, e, h p hp]

/-- A nonsimple gate with two simple parents merges two singleton rows.
Removing either row makes this gate free. -/
lemma simple_pair {d : Domain} (g : Node) (l : Simple d g.left) (r : Simple d g.right)
    (ns : ¬ Simple d g.val) :
    ∃ a ∈ d, ∃ b ∈ d, a ≠ b ∧ g.val a = g.val b ∧
      ¬ Charged (d.erase a) g ∧ ¬ Charged (d.erase b) g := by
  have ln : ¬ Full d g.left := by
    intro h; apply ns
    cases e : g.join
    · exact simple_congr (g := g.right) (fun p hp => by simp [Node.val,e,h p hp]) r
    · exact Or.inl fun p hp => by simp [Node.val,e,h p hp]
  have rn : ¬ Full d g.right := by
    intro h; apply ns
    cases e : g.join
    · exact simple_congr (g := g.left) (fun p hp => by simp [Node.val,e,h p hp]) l
    · exact Or.inl fun p hp => by simp [Node.val,e,h p hp]
  have ls := l.resolve_left ln
  have rs := r.resolve_left rn
  have ej : g.join = true := by
    cases e : g.join with
    | true => rfl
    | false =>
      apply False.elim; apply ns; right
      intro p hp q hq p1 q1
      simp [Node.val,e] at p1 q1
      exact ls p hp q hq p1.1 q1.1
  have two : ¬ Sparse d g.val := fun s => ns (Or.inr s)
  simp only [Sparse, not_forall] at two
  obtain ⟨a,ha,b,hb,va,vb,hab⟩ := two
  refine ⟨a,ha,b,hb,hab,va.trans vb.symm,?_,?_⟩
  all_goals
    apply zero_free
  · simp [Node.val,ej] at va
    exact va.elim (fun h => Or.inl (kill_sparse ls ha h)) (fun h => Or.inr (kill_sparse rs ha h))
  · simp [Node.val,ej] at vb
    exact vb.elim (fun h => Or.inl (kill_sparse ls hb h)) (fun h => Or.inr (kill_sparse rs hb h))

def Source {k : ℕ} (G : Fin k → Node) (i : ℕ) (f : Trace) :=
  Simple Finset.univ f ∨ ∃ j : Fin k, j.val < i ∧ f = (G j).val

lemma source_cases {k : ℕ} {G : Fin k → Node} {i : ℕ} {f : Trace} {d : Domain}
    (s : Source G i f) {P : Trace → Prop}
    (base : Simple d f → P f) (prev : ∀ j : Fin k, j.val < i → P (G j).val) : P f := by
  rcases s with b | ⟨j,h,rfl⟩
  · exact base (simple_mono (Finset.subset_univ _) b)
  · exact prev j h

lemma first_fin {k : ℕ} (P : Fin k → Prop) (h : ∃ i, P i) :
    ∃ i, P i ∧ ∀ j, j < i → ¬ P j := by
  classical
  let s := Finset.univ.filter P
  have sn : s.Nonempty := by
    obtain ⟨i,hi⟩ := h
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨s.min' sn, (Finset.mem_filter.mp (s.min'_mem sn)).2, ?_⟩
  intro j hj hP
  exact (not_lt_of_ge (s.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP⟩))) hj

noncomputable def counted {α : Type} [Fintype α] (P : α → Prop) : Finset α :=
  @Finset.filter _ P (Classical.decPred P) Finset.univ

lemma mem_counted {α : Type} [Fintype α] {P : α → Prop} {i : α} :
    i ∈ counted P ↔ P i := by classical simp [counted]

lemma count_one {α : Type} [DecidableEq α] {s t : Finset α}
    (sub : s ⊆ t) {a : α} (at' : a ∈ t) (as' : a ∉ s) :
    s.card + 1 ≤ t.card := by
  rw [← Finset.card_insert_of_notMem as']
  exact Finset.card_le_card (Finset.insert_subset at' sub)

lemma count_two {α : Type} [DecidableEq α] {s t : Finset α}
    (sub : s ⊆ t) {a b : α} (hab : a ≠ b) (at' : a ∈ t) (bt' : b ∈ t)
    (as' : a ∉ s) (bs' : b ∉ s) : s.card + 2 ≤ t.card := by
  have z := count_one (Finset.insert_subset at' sub) bt' (show b ∉ insert a s by simp [hab.symm, bs'])
  rw [Finset.card_insert_of_notMem as'] at z
  omega

lemma separating_node {d : Domain} {g : Node} {a b : Row}
    (ha : a ∈ d) (hb : b ∈ d) (ns : ¬ Simple d g.val) (sep : g.val a ≠ g.val b)
    (hl : g.left a ≠ g.left b → Simple d g.left)
    (hr : g.right a ≠ g.right b → Simple d g.right) :
    Charged d g ∧ ∃ p, (p = a ∨ p = b) ∧ ¬ Charged (d.erase p) g := by
  have le : ¬ Same d g.val g.left := by
    intro e
    exact ns (simple_congr e (hl (fun h => sep ((e a ha).trans (h.trans (e b hb).symm)))))
  have re : ¬ Same d g.val g.right := by
    intro e
    exact ns (simple_congr e (hr (fun h => sep ((e a ha).trans (h.trans (e b hb).symm)))))
  refine ⟨⟨ns,le,re⟩,?_⟩
  by_cases l : g.left a = g.left b
  · have r : g.right a ≠ g.right b := by
      intro e; exact sep (by simp [Node.val,l,e])
    obtain ⟨p,wherep,z⟩ := kill_sep ha hb (hr r) r
    exact ⟨p,wherep,zero_free (Or.inr z)⟩
  · obtain ⟨p,wherep,z⟩ := kill_sep ha hb (hl l) l
    exact ⟨p,wherep,zero_free (Or.inl z)⟩

/-- If no active output is simple, take the first nonsimple gate and the
first nonsimple gate distinguishing the two rows it merged. Removing one of
those rows makes both gates free. -/
lemma remove_two {k m : ℕ} (G : Fin k → Node) (out : Fin m → Trace) (d : Domain)
    (left : ∀ i, Source G i.val (G i).left) (right : ∀ i, Source G i.val (G i).right)
    (reads : ∀ j, Source G k (out j)) (inj : ∀ a b, a ≠ b → ∃ j, out j a ≠ out j b)
    (large : 1 < d.card) (nd : ∀ j, Active d (out j) → ¬ Simple d (out j)) :
    ∃ p ∈ d, ∃ i j, i ≠ j ∧ Charged d (G i) ∧ Charged d (G j) ∧
      ¬ Charged (d.erase p) (G i) ∧ ¬ Charged (d.erase p) (G j) := by
  classical
  have sees : ∀ a ∈ d, ∀ b ∈ d, a ≠ b →
      ∃ i, ¬ Simple d (G i).val ∧ (G i).val a ≠ (G i).val b := by
    intro a ha b hb ab
    obtain ⟨j,z⟩ := inj a b ab
    have ns := nd j ⟨a,ha,b,hb,z⟩
    rcases reads j with h | ⟨i,_,eq⟩
    · exact (ns (simple_mono (Finset.subset_univ _) h)).elim
    · rw [eq] at ns z; exact ⟨i,ns,z⟩
  obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp large
  obtain ⟨t,nt,_⟩ := sees u hu v hv ne
  obtain ⟨i,ni,prior⟩ := first_fin (fun i => ¬ Simple d (G i).val) ⟨t,nt⟩
  have inputs : ∀ f, Source G i.val f → Simple d f := by
    intro f h
    exact source_cases h id (fun j hj => not_not.mp (prior j hj))
  have li := inputs _ (left i)
  have ri := inputs _ (right i)
  have ci : Charged d (G i) := ⟨ni,fun e => ni (simple_congr e li),fun e => ni (simple_congr e ri)⟩
  obtain ⟨a,ha,b,hb,ab,together,ka,kb⟩ := simple_pair (G i) li ri ni
  obtain ⟨j,⟨nj,zj⟩,early⟩ := first_fin (fun j => ¬ Simple d (G j).val ∧ (G j).val a ≠ (G j).val b)
    (sees a ha b hb ab)
  have stems : ∀ f, Source G j.val f → f a ≠ f b → Simple d f := by
    intro f src
    apply source_cases src (fun hs _ => hs)
    intro t ht diff
    by_contra ns
    exact early t ht ⟨ns,diff⟩
  obtain ⟨cj,p,loc,kill⟩ := separating_node ha hb nj zj (stems _ (left j)) (stems _ (right j))
  have ij : i ≠ j := by rintro rfl; exact zj together
  rcases loc with rfl | rfl
  · exact ⟨_,ha,i,j,ij,ci,cj,ka,kill⟩
  · exact ⟨_,hb,i,j,ij,ci,cj,kb,kill⟩

/-- For each additional row distinguished, either an active output or two
charged gates disappear when an appropriate row is deleted. -/
lemma capacity {k m : ℕ} (G : Fin k → Node) (out : Fin m → Trace)
    (left : ∀ i, Source G i.val (G i).left) (right : ∀ i, Source G i.val (G i).right)
    (reads : ∀ j, Source G k (out j)) (inj : ∀ a b, a ≠ b → ∃ j, out j a ≠ out j b)
    (d : Domain) :
    2 * d.card ≤ (counted fun i => Charged d (G i)).card + 2 * (counted fun j => Active d (out j)).card + 2 := by
  classical
  by_cases large : 1 < d.card
  · have drop (p : Row) (hp : p ∈ d) := capacity G out left right reads inj (d.erase p)
    have sg (p : Row) : (counted fun i => Charged (d.erase p) (G i)) ⊆ (counted fun i => Charged d (G i)) :=
      fun _ h => mem_counted.mpr (charged_mono (Finset.erase_subset _ _) ((mem_counted (P := fun i => Charged (d.erase p) (G i))).mp h))
    have so (p : Row) : (counted fun j => Active (d.erase p) (out j)) ⊆ (counted fun j => Active d (out j)) :=
      fun _ h => mem_counted.mpr (active_mono (Finset.erase_subset _ _) ((mem_counted (P := fun j => Active (d.erase p) (out j))).mp h))
    by_cases direct : ∃ j, Active d (out j) ∧ Simple d (out j)
    · obtain ⟨j,act,s⟩ := direct
      obtain ⟨a,ha,b,hb,z⟩ := act
      obtain ⟨p,loc,kill⟩ := kill_sep ha hb s z
      have hp : p ∈ d := loc.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      have l := drop p hp
      have x := Finset.card_le_card (sg p)
      have y := count_one (so p) ((mem_counted (P := fun v => Active d (out v))).mpr (show Active d (out j) from ⟨a,ha,b,hb,z⟩))
        (fun h => zero_inactive kill ((mem_counted (P := fun v => Active (d.erase p) (out v))).mp h))
      have e := Finset.card_erase_of_mem hp
      omega
    · push Not at direct
      obtain ⟨p,hp,i,j,ij,ci,cj,ki,kj⟩ := remove_two G out d left right reads inj large direct
      have l := drop p hp
      have x := count_two (sg p) ij ((mem_counted (P := fun v => Charged d (G v))).mpr ci) ((mem_counted (P := fun v => Charged d (G v))).mpr cj)
        (fun h => ki ((mem_counted (P := fun v => Charged (d.erase p) (G v))).mp h)) (fun h => kj ((mem_counted (P := fun v => Charged (d.erase p) (G v))).mp h))
      have y := Finset.card_le_card (so p)
      have e := Finset.card_erase_of_mem hp
      omega
  · omega
termination_by d.card
decreasing_by exact Finset.card_erase_lt_of_mem hp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def raw : List Trace := List.ofFn (fun q : Row => fun p : Row => decide (q = p))
def zero : Trace := fun _ => false
/-- Represent each project gate as a binary trace operation. Missing operands
use the operation's neutral element. Missing wire indices still read false. -/
def nodeFor (ws : List Trace) (g : Gate) : Node :=
  let join := match g.op with | .or => true | _ => false
  let neutral : Trace := fun _ => !join
  let args := g.inputs.map (fun i => ws.getD i zero)
  ⟨args.getD 0 neutral, args.getD 1 neutral, join⟩

def traces (gs : List Gate) : List Trace :=
  gs.foldl (fun ws g => ws ++ [(nodeFor ws g).val]) raw

lemma simple_const (b : Bool) : Simple Finset.univ (fun _ => b) := by
  cases b
  · exact Or.inr (by simp [Sparse])
  · exact Or.inl (by simp [Full])

lemma sourced_get {k : ℕ} {G : Fin k → Node} {n : ℕ} {ws : List Trace}
    (ok : ∀ f ∈ ws, Source G n f) (i : ℕ) {fallback : Trace} (hf : Source G n fallback) :
    Source G n (ws.getD i fallback) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact ok _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact hf

lemma for_source {k : ℕ} {G : Fin k → Node} {ws : List Trace} (g : Gate)
    (ok : ∀ f ∈ ws, Source G k f) :
    Source G k (nodeFor ws g).left ∧ Source G k (nodeFor ws g).right := by
  have hz : Source G k zero := Or.inl (simple_const false)
  have hh : ∀ f ∈ g.inputs.map (fun i => ws.getD i zero), Source G k f := by
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact sourced_get ok i hz
  exact ⟨sourced_get hh 0 (Or.inl (simple_const _)), sourced_get hh 1 (Or.inl (simple_const _))⟩

lemma lift_source {k : ℕ} {G : Fin k → Node} (g : Node) {t u : ℕ} {f : Trace}
    (h : Source G t f) (le : t ≤ u) : Source (Fin.snoc (α := fun _ => Node) G g) u f := by
  rcases h with h|⟨j,h,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨j.castSucc,lt_of_lt_of_le h le,by simp⟩

def Represents (k : ℕ) (ws : List Trace) :=
  ∃ G : Fin k → Node, (∀ i, Source G i.val (G i).left) ∧
    (∀ i, Source G i.val (G i).right) ∧ ∀ f ∈ ws, Source G k f

lemma rep_push {k : ℕ} {ws : List Trace} (r : Represents k ws) (g : Gate) :
    Represents (k+1) (ws ++ [(nodeFor ws g).val]) := by
  obtain ⟨G,hl,hr,ok⟩ := r
  let n := nodeFor ws g
  have ⟨nl,nr⟩ := for_source g ok
  refine ⟨Fin.snoc (α := fun _ => Node) G n, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using lift_source n nl (le_refl k)
    · simpa using lift_source n (hl j) (le_refl j.val)
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using lift_source n nr (le_refl k)
    · simpa using lift_source n (hr j) (le_refl j.val)
  · intro f hf
    rcases List.mem_append.mp hf with old | new
    · exact lift_source n (ok f old) (Nat.le_succ k)
    · have e := List.mem_singleton.mp new
      exact Or.inr ⟨Fin.last k,Nat.lt_succ_self k,by simpa [n] using e⟩

lemma rep_traces (gs : List Gate) : Represents gs.length (traces gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_⟩
    intro f hf
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp (show f ∈ raw from hf)
    apply Or.inl; right
    intro i _ j _ hi hj
    simp at hi hj
    exact hi.symm.trans hj
  | append_singleton gs g ih =>
    simpa [traces, List.foldl_append] using rep_push ih g

def legal (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma gate_sim (ws : List Trace) (g : Gate) (hg : legal g) (p : Row) :
    (nodeFor ws g).val p = g.op.eval (g.inputs.map fun i => (ws.map (· p)).getD i false) := by
  have rwget (i : ℕ) : (ws.map (· p)).getD i false = (ws.getD i zero) p :=
    List.getD_map ws zero (· p)
  simp_rw [rwget]
  obtain ⟨op,ins⟩ := g
  rcases hg with ⟨hop,len⟩
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at len
  rcases hop with rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil => simp [nodeFor, Node.val, GateOp.eval, List.getD]
    | cons b tail =>
      cases tail with
      | nil => simp [nodeFor, Node.val, GateOp.eval, List.getD]
      | cons c t => simp at len

lemma simulate (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (p : Row) :
    (traces gs).map (· p) = (Circuit.mk gs 0).wires (List.ofFn fun q : Row => decide (q = p)) := by
  induction gs using List.reverseRecOn with
  | nil => simp [traces,raw,Circuit.wires]
  | append_singleton gs g ih =>
    have h1 : ∀ x ∈ gs, legal x := fun x hx => hg x (List.mem_append_left _ hx)
    have h2 : legal g := hg g (by simp)
    have body := gate_sim (traces gs) g h2 p
    change (traces (gs ++ [g])).map (· p) = _
    rw [show traces (gs ++ [g]) = traces gs ++ [(nodeFor (traces gs) g).val] by simp [traces,List.foldl_append]]
    rw [List.map_append, List.map_singleton, body, ih h1]
    simp [Circuit.wires,List.foldl_append]

lemma bits_distinct : ∀ a b : Row, a ≠ b → ∃ j : Fin 4, Nat.testBit a.val j.val ≠ Nat.testBit b.val j.val := by decide

lemma lower (C : Circuit) (mono : Monotone2 C)
    (bits : ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Row,
      (C.wires (List.ofFn fun q : Row => decide (q = p))).getD w false = Nat.testBit p.val v.val) :
    22 ≤ C.size := by
  classical
  choose w hw using bits
  let f : Fin 4 → Trace := fun v => (traces C.gates).getD (w v) zero
  have eq (v : Fin 4) (p : Row) : f v p = Nat.testBit p.val v.val := by
    have h := List.getD_map (n := w v) (traces C.gates) zero (fun x => x p)
    rw [simulate C.gates mono p] at h
    exact h.symm.trans (hw v p)
  obtain ⟨G,l,r,avail⟩ := rep_traces C.gates
  have reads (v : Fin 4) : Source G C.gates.length (f v) := sourced_get avail _ (Or.inl (simple_const false))
  have inj (a b : Row) (h : a ≠ b) : ∃ v, f v a ≠ f v b := by
    obtain ⟨v,z⟩ := bits_distinct a b h
    exact ⟨v,by simpa only [eq] using z⟩
  have bound := capacity G f l r reads inj Finset.univ
  have cg := Finset.card_le_univ (counted fun i => Charged Finset.univ (G i))
  have co := Finset.card_le_univ (counted fun j => Active Finset.univ (f j))
  simp only [Finset.card_univ, Fintype.card_fin] at bound cg co
  change 22 ≤ C.gates.length
  omega

lemma refutation : ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 21 ∧
    ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val) := by
  rintro ⟨C,h,size,bits⟩
  have := lower C h bits
  omega


def pairs : List (ℕ × ℕ) :=
  [(14,15),(12,16),(17,13),(10,11),(8,18),(20,19),(21,9),(6,7),
   (4,18),(24,23),(25,5),(2,16),(27,19),(28,23),(29,3),(1,15),
   (31,13),(32,11),(33,9),(34,7),(35,5),(36,3)]

def witness : Circuit := ⟨pairs.map (fun (a,b) => ⟨GateOp.or, [a,b]⟩), 37⟩
def outs : Fin 4 → ℕ := ![37, 30, 26, 22]

lemma upper : ∃ C : Circuit, Monotone2 C ∧ C.size = 22 ∧
    ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false =
        Nat.testBit p.val v.val := by
  refine ⟨witness, ?_, rfl, ?_⟩
  · intro g hg
    obtain ⟨⟨a,b⟩, _, rfl⟩ := List.mem_map.mp hg
    simp
  · have h : ∀ v : Fin 4, ∀ p : Fin 16,
        (witness.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD (outs v) false =
          Nat.testBit p.val v.val := by decide
    exact fun v => ⟨outs v, h v⟩

lemma exact_minimum : (∃ C : Circuit, Monotone2 C ∧ C.size = 22 ∧
    ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val) ∧
    (∀ C : Circuit, Monotone2 C →
      (∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16,
        (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val) →
      22 ≤ C.size) := ⟨upper, lower⟩

end Encoder19061
