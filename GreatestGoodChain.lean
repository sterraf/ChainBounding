import Mathlib.Order.Chain
import Mathlib.Order.CompletePartialOrder

variable {α : Type*}

open Set IsChain

section Segment

/--
The binary relation of being an *initial segment*, viz., a decreasing subset.
-/
def IsSegment [LE α] (S C : Set α) : Prop := S ⊆ C ∧ ∀ c ∈ C, ∀ s ∈ S, c ≤ s → c ∈ S

/--
The binary relation of being an *proper* initial segment, that is, different from the whole.
-/
def IsPropSegment [LE α] (S C : Set α) : Prop := IsSegment S C ∧ S ≠ C

@[inherit_doc]
infix:70 " ⊏ " => IsPropSegment

@[inherit_doc]
infix:70 " ⊑ " => IsSegment

variable [PartialOrder α]

@[refl]
lemma IsSegment_refl (S : Set α) : S ⊑ S := ⟨fun _ b => b, fun _ a _ _ _ => a⟩

lemma ssubset_of_IsPropSegment {S C : Set α} (prseg : S ⊏ C) : S ⊂ C :=
    ssubset_of_ne_of_subset prseg.2 prseg.1.1

/--
The relation of being an initial segment is transitive.
-/
@[trans]
lemma IsSegment_trans {S C D : Set α} (hSC : S ⊑ C) (hCD : C ⊑ D) :
    S ⊑ D := by
  constructor
  · exact fun _ hz => hCD.left <| hSC.left hz
  · exact fun x hx y hy hxy => hSC.right x (hCD.right x hx y (hSC.left hy) hxy) y hy hxy

@[trans]
lemma IsPropSegment_trans {S C D : Set α} (hSC : S ⊏ C) (hCD : C ⊏ D) :
    S ⊏ D := by
    have : S ⊂ D := by
      calc
      S ⊂ C := ssubset_of_IsPropSegment hSC
      _ ⊂ D := ssubset_of_IsPropSegment hCD
    exact ⟨IsSegment_trans hSC.1 hCD.1, ne_of_ssubset this⟩

@[trans]
lemma IsPropSegment_of_IsPropSegment_of_IsSegment {S C D : Set α} (hSC : S ⊏ C) (hCD : C ⊑ D) :
    S ⊏ D := by
    have : S ⊂ D := by
      calc
      S ⊂ C := ssubset_of_IsPropSegment hSC
      _ ⊆ D := hCD.1
    exact ⟨IsSegment_trans hSC.1 hCD, ne_of_ssubset this⟩

@[trans]
lemma IsPropSegment_of_IsSegment_of_IsPropSegment {S C D : Set α} (hSC : S ⊑ C) (hCD : C ⊏ D) :
    S ⊏ D := by
    have : S ⊂ D := by
      calc
      S ⊆ C := hSC.1
      _ ⊂ D := ssubset_of_IsPropSegment hCD
    exact ⟨IsSegment_trans hSC hCD.1, ne_of_ssubset this⟩

instance : @Trans (Set α) (Set α) (Set α) IsSegment IsSegment IsSegment := ⟨IsSegment_trans⟩
instance : @Trans (Set α) (Set α) (Set α) IsPropSegment IsPropSegment IsPropSegment :=
  ⟨IsPropSegment_trans⟩
instance : @Trans (Set α) (Set α) (Set α) IsPropSegment IsSegment IsPropSegment :=
  ⟨IsPropSegment_of_IsPropSegment_of_IsSegment⟩
instance : @Trans (Set α) (Set α) (Set α) IsSegment IsPropSegment IsPropSegment :=
  ⟨IsPropSegment_of_IsSegment_of_IsPropSegment⟩

/--
A subset `S` of an initial segment `D` of `U`, which is also an initial segment of `U`,
is an inital segment of `D`.
-/
lemma IsSegment_of_Subset (D U S : Set α) (hDU : D ⊆ U) (hSU : S ⊑ U)
    (sub : S ⊆ D) : S ⊑ D := by
  exact ⟨sub, fun x hx y hy hxy => hSU.right x (hDU hx) y hy hxy⟩

/--
The union of a family `F` of initial segments of a subset is an initial segment.
-/
lemma sUnion_of_IsSegment {F : Set (Set α)} (hF : ∀M ∈ F, M ⊑ C) : ⋃₀ F ⊑ C := by
  constructor
  · intro s sInUnionF
    obtain ⟨M, MinF, sinM⟩ := sInUnionF
    exact (hF M MinF).1 sinM
  · intro c cinC s sInUnionF cles
    obtain ⟨M, MinF, sinM⟩ := sInUnionF
    exact ⟨M, MinF, (hF M MinF).2 c cinC s sinM cles⟩

/--
A proper initial segment of a chain has an strict upper bound in the chain.
-/
lemma exists_strictBound_of_IsSegment (S C : Set α) (hSC : S ⊏ C) (cha : IsChain (· ≤ ·) C) :
    ∃ sb ∈ C, ∀ a ∈ S, a < sb := by
  obtain ⟨c, hc⟩ := exists_of_ssubset <| ssubset_of_subset_of_ne hSC.1.1 hSC.2
  existsi c
  have : ∀ s ∈ S, s < c := by
    by_contra cle ; push_neg at cle
    obtain ⟨s, hs⟩ := cle
    have comparable : s ≠ c → s ≤ c ∨ c ≤ s := cha (hSC.1.1 hs.1) hc.1
    by_cases s_eq_c : s = c
    · rw [s_eq_c] at hs ; tauto
    · have : s ≤ c → s < c ∨ s = c := LE.le.lt_or_eq
      have : c ≤ s → c ∈ S := hSC.1.2 c hc.1 s hs.1
      tauto
  exact ⟨hc.1, this⟩

end Segment

section GreatestGood

/--
A partial order with an *expander* function from subsets to subsets. In main applications, the
expander actually returns a bigger subset.
-/
class OrderExpander (α : Type*) [PartialOrder α] where
  /--
  The “expander” function.
  -/
  g : Set α → Set α

namespace OrderExpander

variable [PartialOrder α] [OrderExpander α]

/--
A chain is *good* if the successor of a proper segment is a greater segment.
-/
def Good (C : Set α) := IsChain (· ≤ ·) C ∧ ∀ {S}, S ⊏ C → S ⊏ g S ∧ g S ⊑ C

lemma ssubset_g {S C : Set α} (GC : Good C) (prseg : S ⊏ C) : S ⊂ g S :=
  ssubset_of_IsPropSegment (GC.2 prseg).1

lemma comparability (C D : Set α) (goodC : Good C) (goodD : Good D) :
    C ⊑ D ∨ D ⊑ C := by
  let S := {M : Set α | M ⊑ C ∧ M ⊑ D}
  have segs : (∀ M ∈ S, M ⊑ C) ∧ (∀ M ∈ S, M ⊑ D) := by
    unfold_let; simp only [mem_setOf_eq]; tauto
  have UnSseg : (⋃₀ S) ⊑ C ∧ (⋃₀ S) ⊑ D :=
    ⟨sUnion_of_IsSegment segs.1, sUnion_of_IsSegment segs.2⟩
  by_contra incomp ; push_neg at incomp
  have UnSne: ⋃₀ S ≠ C ∧ ⋃₀ S ≠ D := by aesop
  have UnSprsegC : ⋃₀ S ⊏ C := ⟨UnSseg.1, UnSne.1⟩
  have succ_segC : (g (⋃₀ S)) ⊑ C := (goodC.2 ⟨UnSseg.1, UnSne.1⟩).2
  have succ_segD : (g (⋃₀ S)) ⊑ D := (goodD.2 ⟨UnSseg.2, UnSne.2⟩).2
  have : g (⋃₀ S) ⊆ ⋃₀ S := subset_sUnion_of_subset _ _ (Eq.subset rfl) $
    mem_sep succ_segC succ_segD
  exact not_subset_of_ssubset (ssubset_g goodC UnSprsegC) this

/--
The greatest good chain.
-/
def U : Set α :=  ⋃₀ {C | Good C}

/--
The union `U` of all good chains is a chain.
-/
lemma IsChain_U : IsChain (· ≤ ·) (U  (α := α)) := by
  intro c c_in_U d d_in_U c_ne_d
  obtain ⟨C, hC⟩ := c_in_U
  obtain ⟨D, hD⟩ := d_in_U
  rcases comparability C D hC.1 hD.1 with CsegD | DsegC
  · exact hD.1.1 (CsegD.1 hC.2) hD.2 c_ne_d
  · exact hC.1.1 hC.2 (DsegC.1 hD.2) c_ne_d

/--
Every good chain is a segment of `U`.
-/
lemma IsSegment_U_of_Good {D : Set α} (goodD : Good D) : D ⊑ U := by
  constructor
  · exact subset_sUnion_of_mem goodD
  · intro c c_in_U d d_in_D c_le_d
    obtain ⟨C, Good_C⟩ := c_in_U
    rcases comparability C D Good_C.1 goodD with CsegD | DsegC
    · exact CsegD.1 Good_C.2
    · exact DsegC.2 c Good_C.2 d d_in_D c_le_d

lemma greatest_good_chain : Good (U (α := α)) := by
  constructor
  · exact IsChain_U
  · intro S Sprseg
    obtain ⟨d, d_in_U, d_sb⟩ := exists_strictBound_of_IsSegment S U Sprseg (IsChain_U)
    obtain ⟨D, Good_D, d_in_D⟩ := d_in_U
    dsimp at Good_D
    have DsegU := (IsSegment_U_of_Good Good_D)
    have SsubD : S ⊆ D := fun c cinS =>
      DsegU.2 c (Sprseg.1.1 cinS) d d_in_D <| le_of_lt <| d_sb c cinS
    have SprsegD : S ⊏ D := by
      constructor
      · exact IsSegment_of_Subset D U S DsegU.left Sprseg.1 SsubD
      · have : d ∉ S := by
          have := fun c (h : c ∈ S) => ne_of_lt <| d_sb c h
          tauto
        aesop
    have : (g S) ⊑ D := (Good_D.2 SprsegD).2
    exact ⟨(Good_D.2 SprsegD).1, IsSegment_trans this DsegU⟩

end OrderExpander

end GreatestGood

section good_implies_well

/--
A partial order with a function that assigns elements of the base type to every subset
(not necessarily members of the subset).
-/
class OrderSelector (α : Type*) [PartialOrder α] where
  /--
  The “selector” function.
  -/
  f : Set α → α

instance [PartialOrder α] [OrderSelector α] : OrderExpander α := ⟨fun C => C ∪ {OrderSelector.f C}⟩

@[simp]
lemma OrderSelector.g_def [PartialOrder α] [OrderSelector α] {C : Set α} :
    OrderExpander.g C = C ∪ {OrderSelector.f (α := α) C} := rfl

end good_implies_well

noncomputable section ChainBounding

/--
A partial order with a function assigning elements of the base type to every subset, such
that for a chain `C`, `f C` is a strict upper bound of `C`.
-/
class ChainBounding (α : Type*) [PartialOrder α] [OrderSelector α] : Prop where
  -- `strbds` below means *strictly bounds*.
  strbds : ∀ C, IsChain (· ≤ ·) C → ∀ a ∈ C, a < OrderSelector.f (α := α) C

variable [PartialOrder α] [OrderSelector α] [ChainBounding α]

open OrderSelector OrderExpander

namespace ChainBounding

lemma not_mem_f {C : Set α} (hC : IsChain (· ≤ ·) C) : f C ∉ C := by
  have : ∀ c ∈ C, c ≠ f C := fun c (h : c ∈ C) => ne_of_lt <| strbds C hC c h
  tauto

lemma ssubset_g {C : Set α} (hC : IsChain (· ≤ ·) C) : C ⊂ g C := by
  apply ssubset_of_ne_of_subset
  · exact (fun h => not_mem_f hC $ Eq.subset h.symm $ mem_union_right C rfl)
  · exact subset_union_left C {f C}

lemma le_f {C : Set α} (hC : IsChain (· ≤ ·) C) (c : ↑(g C)): c ≤ f C := by
  have : ↑c ∈ g C := c.property
  have : ↑c ∈ insert (f C) C := by simp_all
  by_cases cinC : ↑c ∈ C
  · exact le_of_lt (strbds C hC (↑c) cinC)
  · exact le_of_eq $ eq_of_not_mem_of_mem_insert (s := C) this cinC

/--
Class for chains in a poset.
-/
class Chain (C : Set α) : Prop where
  chain : IsChain (· ≤ ·) C

instance {C : Set α} : Top ↑(g C) := ⟨f C, mem_union_right C rfl⟩

instance orderTop_successor {C : Set α} [Chain C] : OrderTop ↑(g C) :=
  ⟨fun c => le_f (C := C) Chain.chain c⟩

/--
A segment containing the top element is the whole thing.
-/
lemma eq_of_IsSegment_of_mem_top {C S : Set α} [OrderTop ↑C] (Sseg : IsSegment S C)
    (topin : ((⊤ : C) : α) ∈ S) : S = C := by
  apply eq_of_subset_of_subset Sseg.1
  intro c cinC
  have : (⟨c,cinC⟩ : C) ≤ ⊤ := le_top
  exact Sseg.2 c cinC _ topin this

lemma subset_of_IsSegment_successor {C S : Set α} [Chain C] (Sprseg : S ⊏ (g C)) : S ⊆ C := by
  have : ((⊤ : g C) : α) ∈ S → S = g C := eq_of_IsSegment_of_mem_top Sprseg.1
  have : f C ∉ S := fun a => Sprseg.2 (this a)
  intro s sinS
  rcases Sprseg.1.1 sinS with h | _
  · exact h
  · simp_all only [union_singleton, mem_singleton_iff]

/--
A chain is a segment of its successor.
-/
lemma IsSegment_successor {C : Set α} (chain : IsChain (· ≤ ·) C) : IsSegment C (g C) := by
  constructor
  · simp_all only [g, union_singleton, subset_insert]
  · intro c hc s hs cles
    rcases hc with cinC | hc
    · exact cinC
    · have : s < c := by rw [hc] ; exact strbds C chain s hs
      have : False := not_lt_of_le cles this
      contradiction

/--
The successor good chain is good as well.
-/
lemma Good_successor (C : Set α) (goodC : Good C) : Good (g C) := by
  constructor
  · simp only [g, union_singleton]
    exact IsChain.insert goodC.1 fun b hbC _ => Or.inr (le_of_lt (strbds C goodC.1 b hbC))
  · intro S Sprseg
    have SsubC : S ⊆ C := @subset_of_IsSegment_successor _ _ _ _ _ _ ⟨goodC.1⟩ Sprseg
    have Cseg : IsSegment C (g C) := IsSegment_successor goodC.1
    have SsegC : IsSegment S C := IsSegment_of_Subset C (g C) _ Cseg.left Sprseg.1 SsubC
    rcases em (S = C) with rfl | SneqC
    · constructor <;> try rfl
      intros ; simp_all only [union_singleton, ne_eq, mem_insert_iff]
    · constructor
      · exact (goodC.2 ⟨SsegC, SneqC⟩).1
      · calc
        g S ⊑ C   := (goodC.2 ⟨SsegC, SneqC⟩).2
        _   ⊑ g C := Cseg

/--
There is no assigment of a strict upper bound to each chain in a poset.
-/
lemma chain_bounding : False := by
  have goodU : Good U := greatest_good_chain (α := α)
  have Good_gU : Good (g U) := Good_successor U goodU
  have gnotsub : ¬(g U ⊆ U) := not_subset_of_ssubset $ ssubset_g goodU.1
  have : g U ⊆ U := (IsSegment_U_of_Good Good_gU).left
  exact gnotsub this

end ChainBounding

end ChainBounding

/--
An ubounded chain in an inhabited poset.
-/
class UnboundedChain (α : Type*) [PartialOrder α] [Inhabited α] : Prop where
  strbd : ∀ C, IsChain (· ≤ ·) C → ∃ sb : α, ∀ c ∈ C, c < sb

section UnboundedChain

variable [PartialOrder α] [Inhabited α] [UnboundedChain α]

namespace UnboundedChain

open Classical in
/--
The assigment of a strict upper bound resulting from *reductio* applied to the statement
of the Unbounded Chain Lemma.
-/
noncomputable def f (C : Set α) : α := if chain : IsChain (· ≤ ·) C then
  Classical.choose (strbd C chain) else default

/--
`f` assigns a strict upper bound to each chain.
-/
lemma f_bounds : ∀ (C : Set α), IsChain (· ≤ ·) C → ∀ a ∈ C, a < f C := by
  intro C hC a ha
  have : f C = Classical.choose (strbd C hC) := by simp [*,f]
  rw [this]
  exact Classical.choose_spec (strbd C hC) a ha

end UnboundedChain

noncomputable instance : OrderSelector α := ⟨UnboundedChain.f⟩

end UnboundedChain

open ChainBounding

/--
Every poset has a chain without strict upper bounds.
-/
lemma unbounded_chain [PartialOrder α] [Inhabited α] :
    ∃ C, IsChain (· ≤ ·) C ∧ ¬ ∃ sb : α, ∀ a ∈ C, a < sb := by
  by_contra strbd; push_neg at strbd
  have : UnboundedChain α := ⟨strbd⟩
  have : ChainBounding α := ⟨UnboundedChain.f_bounds (α := α)⟩
  exact chain_bounding (α := α)

section Zorn

/--
Maximal elements of a poset.
-/
def IsMaximal [LE α] (m : α) := ∀ z, m ≤ z → z = m

lemma zorn [PartialOrder α] [Inhabited α]
    (ind : ∀ (C : Set α), IsChain (· ≤ ·) C → ∃ ub, ∀ a ∈ C, a ≤ ub) : ∃ (x : α), IsMaximal x := by
  obtain ⟨C, chain, subd⟩ := unbounded_chain (α := α)
  push_neg at subd
  obtain ⟨ub, hub⟩ := ind C chain
  existsi ub
  intro z hz
  by_contra zneub
  obtain ⟨a, ainC, anltz⟩ := subd z
  exact anltz $ lt_of_le_of_lt (hub a ainC) $ lt_of_le_of_ne' hz zneub

end Zorn

section BourbakiWitt

theorem bourbaki_witt_of_complete [CompletePartialOrder α] (g : α → α) (hg : ∀x, x ≤ g x) :
    ∃ x, g x = x := by
  by_contra noFix ; push_neg at noFix
  let inst : OrderSelector α := ⟨(g $ sSup ·)⟩
  have : ChainBounding α := by
    constructor
    intro C chain a ha
    calc
      a ≤ sSup C := DirectedOn.le_sSup (directedOn chain) ha
      _ < OrderSelector.f C := lt_of_le_of_ne' (hg (sSup C)) (noFix (sSup C))
  exact chain_bounding (α := α)

end BourbakiWitt
