import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10393_aux
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]
def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)
private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩
def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)
private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]
private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b
private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]
def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a
def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]
theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih
theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev Row := Fin 128
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩
theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _
theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl
theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩
def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs
theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv
theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega
def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp
def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))
theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))
theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h
def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this
def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R
def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))
abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^128 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2
theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl
theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega
def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))
theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL
def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d
abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) := by
      cases ho : opOK u c.1
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ ho hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩
abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && T.testBit p.1 && !(T.testBit p.2)
def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]
def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p
theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega
theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx
def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 128 && Nat.blt n 128 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 128) (hn : n < 128), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^128) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^128 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 128
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3
def hiM : Nat → Nat
  | 0 => 0x22222222222222222222222222222222
  | 1 => 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0x00f000f000f000f000f000f000f000f0
  | 3 => 0x0000ff000000ff000000ff000000ff00
  | _ => 0x00000000ffff000000000000ffff0000
def loM : Nat → Nat
  | 0 => 0x44444444444444444444444444444444
  | 1 => 0x30303030303030303030303030303030
  | 2 => 0x0f000f000f000f000f000f000f000f00
  | 3 => 0x00ff000000ff000000ff000000ff0000
  | _ => 0x0000ffff000000000000ffff00000000
def keM : Nat → Nat
  | 0 => 0x99999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ff
  | _ => 0xffff00000000ffffffff00000000ffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 16
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 128 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 128 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 5) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 5) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 5 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2
abbrev StD := List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))
def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop
def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 10000 then (match t.cuts[i]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif Nat.blt i 20000 then (match t.seps[i-10000]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif Nat.blt i 30000 then (match t.kws[i-20000]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[i-30000]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) st.2
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1
theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^128 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^128 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^128 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^128 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : Nat.blt i 10000
      · rw [h1,cond_false] at hi
        cases h2 : Nat.blt i 20000
        · rw [h2,cond_false] at hi
          cases h3 : Nat.blt i 30000
          · rw [h3,cond_false] at hi
            cases hg : t.perms[i-30000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[i-20000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[i-10000]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r
theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
open PEqualNP.CircuitLowerBounds
def sw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def sw1 : Nat := 0xcccccccccccccccccccccccccccccccc
def sw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def sw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def sw4 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def sw5 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def sw6 : Nat := 0xffccffccffccffccffccffccffccffcc
def sw7 : Nat := 0xfefefefefefefefefefefefefefefefe
def sw8 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def sw9 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def sw10 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def sw11 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def sw12 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def sw13 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def sw14 : Nat := 0xffffccccffffccccffffccccffffcccc
def sw15 : Nat := 0xeeee0000eeee0000eeee0000eeee
def sw16 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def sw17 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def sw18 : Nat := 0xfffffafafffffafafffffafafffffafa
def sw19 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfc
def sw20 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def sw21 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeee
def sw22 : Nat := 0xfffefffefffefffefffefffefffefffe
def sw23 : Nat := 0xfefe0000fefe0000fefe0000fefe
def sw24 : Nat := 0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8
def sw25 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc
def sw26 : Nat := 0xa0000000a0000000a0000000a
def sw27 : Nat := 0xfffffff0fffffff0fffffff0fffffff0
def sw28 : Nat := 0x88888888888888888888888888888888
def sw29 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def sw30 : Nat := 0xaaaafefeaaaafefeaaaafefeaaaafefe
def sw31 : Nat := 0xf000f000f000f000f000f000f000f000
def sw32 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc
def sw33 : Nat := 0xee000000ee000000ee000000ee
def sw34 : Nat := 0xfffafffafffafffafffafffafffafffa
def sw35 : Nat := 0xffffffaaffffffaaffffffaaffffffaa
def sw36 : Nat := 0xfafafafafafafafafafafafafafafafa
def sw37 : Nat := 0xfffffffcfffffffcfffffffcfffffffc
def sw38 : Nat := 0xffffffccffffffccffffffccffffffcc
def sw39 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def sw40 : Nat := 0xfffe0000fffe0000fffe0000fffe
def sw41 : Nat := 0xfffffe00fffffe00fffffe00fffffe00
def sw42 : Nat := 0x2aaaa0002aaaa0002aaaa0002aaaa
def sw43 : Nat := 0xfffffefefffffefefffffefefffffefe
def sw44 : Nat := 0xaaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8
def sw45 : Nat := 0xfffffffefffffffefffffffefffffffe
def sw46 : Nat := 0xaaaafffeaaaafffeaaaafffeaaaafffe
def sw47 : Nat := 0xfe000000fe000000fe000000fe
def sw48 : Nat := 0xfffc0000fffc0000fffc0000fffc
def sw49 : Nat := 0xffff000affff000affff000affff000a
def sw50 : Nat := 0x55555550555555505555555055555550
def sw51 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def sw52 : Nat := 0xfffefefefffefefefffefefefffefefe
def sw53 : Nat := 0xfefefe00fefefe00fefefe00fefefe
def sw54 : Nat := 0xff000000ff000000ff000000ff000000
def sw55 : Nat := 0xffff00aaffff00aaffff00aaffff00aa
def sw56 : Nat := 0xfefefffefefefffefefefffefefefffe
def sw57 : Nat := 0xaaa8fffcaaa8fffcaaa8fffcaaa8fffc
def sw58 : Nat := 0xffff00eeffff00eeffff00eeffff00ee
def sw59 : Nat := 0xaafeaafeaafeaafeaafeaafeaafeaafe
def sw60 : Nat := 0xeeeefffeeeeefffeeeeefffeeeeefffe
def sw61 : Nat := 0xaafe0000aafe0000aafe0000aafe
def sw62 : Nat := 0x8888fff88888fff88888fff88888fff8
def sw63 : Nat := 0xfcccfcccfcccfcccfcccfcccfcccfccc
def sw64 : Nat := 0xfffff000fffff000fffff000fffff000
def sw65 : Nat := 0xfff00000fff00000fff00000fff0
def sw66 : Nat := 0xaafcfe00aafcfe00aafcfe00aafcfe
def sw67 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def sw68 : Nat := 0xffffffeeffffffeeffffffeeffffffee
def sw69 : Nat := 0xf3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2
def sw70 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def sw71 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafa
def sw72 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def sw73 : Nat := 0xfffffffafffffffafffffffafffffffa
def sw74 : Nat := 0xffffee00ffffee00ffffee00ffffee
def sw75 : Nat := 0xffa00000ffa00000ffa00000ffa
def sw76 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def sw77 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def sw78 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def sw79 : Nat := 0x3fffc0003fffc0003fffc0003fffc
def sw80 : Nat := 0xfffeff00fffeff00fffeff00fffeff00
def sw81 : Nat := 0xff00fe00ff00fe00ff00fe00ff00fe00
def sw82 : Nat := 0xaaaafffcaaaafffcaaaafffcaaaafffc
def sw83 : Nat := 0x99989998999899989998999899989998
def sw84 : Nat := 0xffccccccffccccccffccccccffcccccc
def sw85 : Nat := 0xffe00000ffe00000ffe00000ffe
def sw86 : Nat := 0xffffffff00000000ffffffff00000000
def s1_T : Nat := 0x88888888888888888888888888888888
def s1_R : List Nat := [0, 1]
def s1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem s1_B : baseOK s1_T s1_R s1_E = true := by decide +kernel
theorem s1_L : LowN true s1_R s1_T 1 := lowCount s1_B (by decide +kernel)
def s2_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def s2_R : List Nat := [0, 1]
def s2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem s2_B : baseOK s2_T s2_R s2_E = true := by decide +kernel
theorem s2_L : LowN true s2_R s2_T 1 := lowCount s2_B (by decide +kernel)
def s3_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def s3_R : List Nat := [0, 1, 2]
def s3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem s3_B : baseOK s3_T s3_R s3_E = true := by decide +kernel
theorem s3_S0 : SliceN true s3_R s3_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S1 : SliceN true s3_R s3_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S2 : SliceN true s3_R s3_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S3 : SliceN true s3_R s3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S4 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S5 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) s3_B s2_B s2_L (by decide +kernel)
def s3_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem s3_Y : ∀ s ∈ s3_Z, SliceN true s3_R s3_T s := by
  unfold s3_Z
  simp only [List.forall_mem_cons]
  exact ⟨s3_S0,s3_S1,s3_S2,s3_S3,s3_S4,s3_S5,by simp⟩
def s3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def s3_t : Tabs := (s3_C.map (mkCut true s3_Z),[(5,4),(3,1),(3,0),(3,2),(6,2),(5,1)],[],[])
theorem s3_W : TabsP true s3_R s3_T s3_t := ⟨cutsGood s3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s3_D3 : List StD := [
([sw0,sw1,sw2],[[0,1,10000,2,3,10001,10002],[4,1,10003,10000,3],[10001,0,5,2,10004,10005]])]
def s3_D2 : List StD := []
theorem s3_I2 : LevelN true s3_T 2 s3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s3_C3x0 : levelOK true s3_T s3_t 2 (s3_D2.map Prod.fst) ((s3_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s3_I3 : LevelN true s3_T 3 s3_D3 := levelStep s3_B s3_W s3_I2 (chunks 16 s3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s3_C3x0
  ))
theorem s3_L : LowN true s3_R s3_T 4 := lowSearch s3_B s3_I3 (by decide +kernel)
def s4_T : Nat := 0xfefefefefefefefefefefefefefefefe
def s4_R : List Nat := [0, 1, 2]
def s4_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem s4_B : baseOK s4_T s4_R s4_E = true := by decide +kernel
theorem s4_L : LowN true s4_R s4_T 2 := lowCount s4_B (by decide +kernel)
def s5_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def s5_R : List Nat := [0, 1, 2, 3]
def s5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem s5_B : baseOK s5_T s5_R s5_E = true := by decide +kernel
theorem s5_S0 : SliceN true s5_R s5_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S1 : SliceN true s5_R s5_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S2 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S3 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S4 : SliceN true s5_R s5_T (0x11111111111111111111111111111111,1,[2, 3]) := mkSlice (w:=0) s5_B s1_B s1_L (by decide +kernel)
theorem s5_S5 : SliceN true s5_R s5_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S6 : SliceN true s5_R s5_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S7 : SliceN true s5_R s5_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S8 : SliceN true s5_R s5_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S9 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S10 : SliceN true s5_R s5_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S11 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S12 : SliceN true s5_R s5_T (0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S13 : SliceN true s5_R s5_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) s5_B s2_B s2_L (by decide +kernel)
def s5_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]),(0x11111111111111111111111111111111,1,[2, 3]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]),(0x50505050505050505050505050505050,1,[1, 3])]
theorem s5_Y : ∀ s ∈ s5_Z, SliceN true s5_R s5_T s := by
  unfold s5_Z
  simp only [List.forall_mem_cons]
  exact ⟨s5_S0,s5_S1,s5_S2,s5_S3,s5_S4,s5_S5,s5_S6,s5_S7,s5_S8,s5_S9,s5_S10,s5_S11,s5_S12,s5_S13,by simp⟩
def s5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[]),(0,[(1,0,2)]),(1,[(1,0,2)]),(5,[]),(1,[(3,0,2)]),(6,[]),(0,[(3,0,2)]),(2,[(1,1,2)]),(2,[(1,0,2)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(1,[(3,0,1)]),(7,[]),(0,[(3,0,1)]),(8,[]),(0,[(2,0,1)]),(9,[]),(10,[]),(0,[(2,0,2)]),(11,[]),(12,[]),(0,[(1,0,2),(1,1,2)]),(8,[(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(1,0,3)]),(3,[(3,1,2)]),(0,[(0,0,2)]),(0,[(2,1,2)]),(0,[(0,1,2)]),(13,[])]
def s5_t : Tabs := (s5_C.map (mkCut true s5_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4),(7,8)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[2],[1,0]])
theorem s5_W : TabsP true s5_R s5_T s5_t := ⟨cutsGood s5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s5_D6 : List StD := [
([sw0,sw1,sw2,sw3],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[1,10002,30003,10006,10007,2],[1,10002,30004,10008,10009,3],[2,10003,30005,10010,10011,3]])]
noncomputable def s5_D5 : List StD := [
([sw0,sw1,sw4,sw2,sw3],[[0,1],[1],[0,30006,10003,4],[0,30007,10005,5],[0],[1,30008,10007,4],[1,30009,10009,5],[4,6,2,30000,10003,30010,10010],[5,6,3,30010,10005,30000,10011],[10003,4,10010,10011]])]
noncomputable def s5_D4 : List StD := [
([sw0,sw1,sw2,sw5,sw6],[[7,30011,8],[7,9],[10],[7,8,9],[8,11],[8,7,11],[12],[13,9,10007],[14,11,10003],[7,8]]),
([sw0,sw1,sw2,sw7,sw3],[[15,4,16],[15,16,4],[17],[15,18],[4,15,16],[19],[16,20],[21],[4,22],[3,18,30000]]),
([sw8,sw0,sw1,sw2,sw3],[[0,1],[1,0],[2,23,6],[7],[24,23],[6,23],[6,25,5],[6,26],[23,25],[23,25]])]
noncomputable def s5_D3 : List StD := [
([sw0,sw9,sw6,sw10],[[27,28,10012],[29,28,10000],[30,10000,10001],[3,31,32],[3,28,1],[1,28]]),
([sw11,sw0,sw1,sw2],[[0,18],[24,20,33],[34,6,35],[36,18],[11,18],[9,20]])]
def s5_D2 : List StD := []
theorem s5_I2 : LevelN true s5_T 2 s5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C3x0 : levelOK true s5_T s5_t 2 (s5_D2.map Prod.fst) ((s5_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I3 : LevelN true s5_T 3 s5_D3 := levelStep s5_B s5_W s5_I2 (chunks 16 s5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C4x0 : levelOK true s5_T s5_t 3 (s5_D3.map Prod.fst) ((s5_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I4 : LevelN true s5_T 4 s5_D4 := levelStep s5_B s5_W s5_I3 (chunks 16 s5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C5x0 : levelOK true s5_T s5_t 4 (s5_D4.map Prod.fst) ((s5_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I5 : LevelN true s5_T 5 s5_D5 := levelStep s5_B s5_W s5_I4 (chunks 16 s5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C6x0 : levelOK true s5_T s5_t 5 (s5_D5.map Prod.fst) ((s5_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I6 : LevelN true s5_T 6 s5_D6 := levelStep s5_B s5_W s5_I5 (chunks 16 s5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C6x0
  ))
theorem s5_L : LowN true s5_R s5_T 7 := lowSearch s5_B s5_I6 (by decide +kernel)
def s6_T : Nat := 0xfffefffefffefffefffefffefffefffe
def s6_R : List Nat := [0, 1, 2, 3]
def s6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
theorem s6_B : baseOK s6_T s6_R s6_E = true := by decide +kernel
theorem s6_L : LowN true s6_R s6_T 3 := lowCount s6_B (by decide +kernel)
def s7_T : Nat := 0xfffefee8fffefee8fffefee8fffefee8
def s7_R : List Nat := [0, 1, 2, 3, 4]
def s7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem s7_B : baseOK s7_T s7_R s7_E = true := by decide +kernel
theorem s7_S0 : SliceN true s7_R s7_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S1 : SliceN true s7_R s7_T (0x33333333333333333333333333333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S2 : SliceN true s7_R s7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S3 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S4 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S5 : SliceN true s7_R s7_T (0x11111111111111111111111111111111,4,[2, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S6 : SliceN true s7_R s7_T (0x3333000033330000333300003333,4,[0, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S7 : SliceN true s7_R s7_T (0x5555000055550000555500005555,4,[1, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S8 : SliceN true s7_R s7_T (0x3030303030303030303030303030303,4,[0, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S9 : SliceN true s7_R s7_T (0x5050505050505050505050505050505,4,[1, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S10 : SliceN true s7_R s7_T (0x1010101010101010101010101010101,1,[3, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S11 : SliceN true s7_R s7_T (0xf000f000f000f000f000f000f000f,4,[0, 1, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S12 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S13 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff,4,[0, 1, 2]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S14 : SliceN true s7_R s7_T (0x550055005500550055005500550055,4,[1, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S15 : SliceN true s7_R s7_T (0x33003300330033003300330033003300,2,[0, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S16 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]) := mkSlice (w:=16) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S17 : SliceN true s7_R s7_T (0x11110000111100001111000011110000,1,[2, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S18 : SliceN true s7_R s7_T (0x10101010101010101010101010101010,1,[3, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S19 : SliceN true s7_R s7_T (0x11001100110011001100110011001100,1,[2, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S20 : SliceN true s7_R s7_T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S21 : SliceN true s7_R s7_T (0x2222000022220000222200002222,1,[2, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S22 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff0000,2,[0, 1, 2]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S23 : SliceN true s7_R s7_T (0x2020202020202020202020202020202,1,[3, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S24 : SliceN true s7_R s7_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S25 : SliceN true s7_R s7_T (0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]) := mkSlice (w:=2) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S26 : SliceN true s7_R s7_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S27 : SliceN true s7_R s7_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S28 : SliceN true s7_R s7_T (0xa0a00000a0a00000a0a00000a0a,1,[1, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S29 : SliceN true s7_R s7_T (0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S30 : SliceN true s7_R s7_T (0x330033003300330033003300330033,4,[0, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S31 : SliceN true s7_R s7_T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S32 : SliceN true s7_R s7_T (0x44444444444444444444444444444444,2,[2, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S33 : SliceN true s7_R s7_T (0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S34 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S35 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]) := mkSlice (w:=8) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S36 : SliceN true s7_R s7_T (0x30303030303030303030303030303030,2,[0, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S37 : SliceN true s7_R s7_T (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S38 : SliceN true s7_R s7_T (0x50505050505050505050505050505050,2,[1, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S39 : SliceN true s7_R s7_T (0x55005500550055005500550055005500,2,[1, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S40 : SliceN true s7_R s7_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S41 : SliceN true s7_R s7_T (0xaa000000aa000000aa000000aa,1,[1, 2]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S42 : SliceN true s7_R s7_T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S43 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S44 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0000,1,[0, 1]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S45 : SliceN true s7_R s7_T (0x440044004400440044004400440044,1,[2, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S46 : SliceN true s7_R s7_T (0x3030000030300000303000003030000,1,[0, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S47 : SliceN true s7_R s7_T (0x500050005000500050005000500050,1,[1, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S48 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f00,1,[0, 1]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S49 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0,1,[0, 1]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S50 : SliceN true s7_R s7_T (0x300030003000300030003000300030,1,[0, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S51 : SliceN true s7_R s7_T (0x220022002200220022002200220022,1,[2, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S52 : SliceN true s7_R s7_T (0x5000500050005000500050005000500,1,[1, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S53 : SliceN true s7_R s7_T (0x4040404040404040404040404040404,1,[3, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S54 : SliceN true s7_R s7_T (0xa000a000a000a000a000a000a000a,1,[1, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S55 : SliceN true s7_R s7_T (0x3300000033000000330000003300,1,[0, 2]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S56 : SliceN true s7_R s7_T (0x550000005500000055000000550000,1,[1, 2]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S57 : SliceN true s7_R s7_T (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S58 : SliceN true s7_R s7_T (0x3030000030300000303000003030,1,[0, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S59 : SliceN true s7_R s7_T (0x5050000050500000505000005050000,1,[1, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S60 : SliceN true s7_R s7_T (0x50005000500050005000500050005,1,[1, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S61 : SliceN true s7_R s7_T (0x110011001100110011001100110011,1,[2, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S62 : SliceN true s7_R s7_T (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S63 : SliceN true s7_R s7_T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
def s7_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0x33333333333333333333333333333333,7,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]),(0x11111111111111111111111111111111,4,[2, 3, 4]),(0x3333000033330000333300003333,4,[0, 2, 3]),(0x5555000055550000555500005555,4,[1, 2, 3]),(0x3030303030303030303030303030303,4,[0, 3, 4]),(0x5050505050505050505050505050505,4,[1, 3, 4]),(0x1010101010101010101010101010101,1,[3, 4]),(0xf000f000f000f000f000f000f000f,4,[0, 1, 4]),(0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]),(0xff000000ff000000ff000000ff,4,[0, 1, 2]),(0x550055005500550055005500550055,4,[1, 2, 4]),(0x33003300330033003300330033003300,2,[0, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]),(0x11110000111100001111000011110000,1,[2, 3]),(0x10101010101010101010101010101010,1,[3, 4]),(0x11001100110011001100110011001100,1,[2, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0x2222000022220000222200002222,1,[2, 3]),(0xff000000ff000000ff000000ff0000,2,[0, 1, 2]),(0x2020202020202020202020202020202,1,[3, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]),(0xa0a00000a0a00000a0a00000a0a,1,[1, 3]),(0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]),(0x330033003300330033003300330033,4,[0, 2, 4]),(0x30003000300030003000300030003,1,[0, 4]),(0x44444444444444444444444444444444,2,[2, 3, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]),(0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]),(0x30303030303030303030303030303030,2,[0, 3, 4]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0x50505050505050505050505050505050,2,[1, 3, 4]),(0x55005500550055005500550055005500,2,[1, 2, 4]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0xaa000000aa000000aa000000aa,1,[1, 2]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]),(0xf0000000f0000000f0000000f0000,1,[0, 1]),(0x440044004400440044004400440044,1,[2, 4]),(0x3030000030300000303000003030000,1,[0, 3]),(0x500050005000500050005000500050,1,[1, 4]),(0xf0000000f0000000f0000000f00,1,[0, 1]),(0xf0000000f0000000f0000000f0,1,[0, 1]),(0x300030003000300030003000300030,1,[0, 4]),(0x220022002200220022002200220022,1,[2, 4]),(0x5000500050005000500050005000500,1,[1, 4]),(0x4040404040404040404040404040404,1,[3, 4]),(0xa000a000a000a000a000a000a000a,1,[1, 4]),(0x3300000033000000330000003300,1,[0, 2]),(0x550000005500000055000000550000,1,[1, 2]),(0x5050000050500000505000005050,1,[1, 3]),(0x3030000030300000303000003030,1,[0, 3]),(0x5050000050500000505000005050000,1,[1, 3]),(0x50005000500050005000500050005,1,[1, 4]),(0x110011001100110011001100110011,1,[2, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(0xc000c000c000c000c000c000c000c,1,[0, 4])]
theorem s7_Y : ∀ s ∈ s7_Z, SliceN true s7_R s7_T s := by
  unfold s7_Z
  simp only [List.forall_mem_cons]
  exact ⟨s7_S0,s7_S1,s7_S2,s7_S3,s7_S4,s7_S5,s7_S6,s7_S7,s7_S8,s7_S9,s7_S10,s7_S11,s7_S12,s7_S13,s7_S14,s7_S15,s7_S16,s7_S17,s7_S18,s7_S19,s7_S20,s7_S21,s7_S22,s7_S23,s7_S24,s7_S25,s7_S26,s7_S27,s7_S28,s7_S29,s7_S30,s7_S31,s7_S32,s7_S33,s7_S34,s7_S35,s7_S36,s7_S37,s7_S38,s7_S39,s7_S40,s7_S41,s7_S42,s7_S43,s7_S44,s7_S45,s7_S46,s7_S47,s7_S48,s7_S49,s7_S50,s7_S51,s7_S52,s7_S53,s7_S54,s7_S55,s7_S56,s7_S57,s7_S58,s7_S59,s7_S60,s7_S61,s7_S62,s7_S63,by simp⟩
def s7_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[]),(0,[(1,0,3)]),(1,[(1,0,3)]),(2,[(1,0,3),(1,1,3)]),(3,[(1,0,3),(1,1,3)]),(6,[]),(7,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(8,[]),(3,[(1,0,1),(1,2,4)]),(4,[(1,0,1),(1,2,4)]),(9,[]),(10,[]),(0,[(2,0,3)]),(4,[(3,0,1)]),(1,[(2,0,3)]),(0,[(1,1,2)]),(1,[(1,1,2)]),(11,[(1,0,1)]),(5,[(1,0,1)]),(11,[]),(4,[(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,1,3),(1,2,3)]),(12,[]),(13,[]),(0,[(1,0,3),(1,2,3)]),(1,[(1,0,2),(1,2,3)]),(2,[(1,0,2),(1,1,3),(1,2,3)]),(3,[(1,1,3)]),(6,[(1,0,2)]),(14,[(1,0,2)]),(15,[]),(14,[]),(1,[(1,2,3),(1,0,4)]),(16,[]),(0,[(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(3,[(1,0,1),(1,2,3)]),(17,[]),(5,[(1,1,2)]),(5,[(1,0,2)]),(0,[(1,2,3),(3,1,3)]),(18,[]),(19,[]),(0,[(1,1,3),(3,2,3)]),(0,[(1,0,3),(1,1,3)]),(1,[(1,0,3),(1,1,4)]),(4,[(1,0,2)]),(20,[]),(4,[(3,0,2)]),(0,[(1,0,3),(1,1,4)]),(0,[(1,1,3),(1,0,4)]),(21,[]),(1,[(1,0,3),(1,1,3)]),(9,[(1,0,2)]),(22,[]),(23,[]),(4,[(1,1,2)]),(11,[(1,1,2)]),(0,[(1,0,1),(2,0,3)]),(4,[(1,1,2),(1,0,4)]),(2,[(0,1,3)]),(0,[(1,0,1),(1,0,3)]),(12,[(1,0,1)]),(8,[(2,0,2)]),(4,[(1,0,1),(1,1,2)]),(24,[]),(0,[(1,0,1),(1,0,2)]),(2,[(1,0,1),(1,2,4)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,2),(3,0,1)]),(1,[(1,0,1),(3,0,2)]),(0,[(1,0,2),(3,0,1)]),(0,[(1,0,1),(3,0,2)]),(25,[]),(0,[(1,0,2),(2,0,1)]),(0,[(1,0,1),(2,0,2)]),(2,[(1,0,1),(1,3,4)]),(26,[]),(1,[(1,1,3),(3,0,3)]),(27,[]),(0,[(1,1,3),(3,0,3)]),(0,[(1,0,3),(3,1,3)]),(3,[(1,0,1),(1,3,4)]),(28,[]),(8,[(1,0,1)]),(1,[(1,0,1),(1,2,4)]),(9,[(1,0,1)]),(3,[(1,0,1),(3,2,4)]),(5,[(2,0,1)]),(5,[(2,0,2)]),(1,[(1,0,1),(3,3,4)]),(2,[(1,0,1),(3,3,4)]),(9,[(2,0,2)]),(29,[]),(2,[(1,1,2),(2,0,4)]),(2,[(1,1,2),(0,0,1)]),(2,[(1,1,2),(3,0,1)]),(30,[]),(1,[(1,1,2),(0,0,4)]),(2,[(1,1,2),(0,0,4)]),(3,[(1,1,2),(0,0,4)]),(31,[]),(9,[(3,0,1)]),(32,[]),(5,[(3,0,1)]),(9,[(2,0,1)]),(0,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(3,2,4)]),(33,[]),(3,[(1,0,2),(1,1,4)]),(2,[(1,0,2),(1,1,4)]),(0,[(1,0,2),(1,1,4)]),(0,[(1,1,2),(1,0,4)]),(0,[(1,0,1),(1,3,4)]),(0,[(1,0,1),(3,3,4)]),(4,[(1,0,2),(1,1,4)]),(34,[]),(4,[(1,2,3),(0,0,4)]),(9,[(1,1,2)]),(2,[(1,2,3),(2,0,4)]),(3,[(1,2,3),(2,0,4)]),(35,[]),(4,[(1,2,3),(2,0,4)]),(13,[(2,0,2)]),(9,[(3,1,2)]),(9,[(2,1,2)]),(4,[(1,2,3),(2,0,1)]),(4,[(1,2,3),(3,0,1)]),(2,[(1,2,3)]),(3,[(1,2,3)]),(2,[(0,0,1),(1,2,3)]),(36,[]),(3,[(0,0,1),(1,2,3)]),(37,[]),(4,[(0,0,1),(1,2,3)]),(38,[]),(39,[]),(40,[]),(3,[(0,0,1),(3,2,3)]),(4,[(0,0,1),(2,2,3)]),(3,[(0,0,1),(2,2,3)]),(3,[(1,0,1),(3,2,3)]),(2,[(1,0,1),(3,2,3)]),(3,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(0,0,3)]),(3,[(1,1,2),(1,0,3)]),(1,[(2,0,3),(1,1,2)]),(2,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(3,1,2)]),(3,[(2,0,3),(2,1,2)]),(2,[(2,0,3),(2,1,2)]),(0,[(0,1,2)]),(4,[(0,2,3),(1,0,1)]),(4,[(0,2,3),(3,0,1)]),(5,[(0,0,1)]),(0,[(0,1,2),(1,0,3)]),(0,[(2,0,3),(0,1,2)]),(41,[]),(42,[]),(0,[(2,0,3),(2,1,2)]),(0,[(2,0,3),(3,1,2)]),(43,[]),(4,[(1,2,3),(1,0,1)]),(0,[(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,1,2)]),(44,[]),(45,[]),(46,[]),(47,[]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(1,2,3),(2,0,4)]),(1,[(1,2,3),(2,0,4)]),(5,[(3,1,2)]),(5,[(2,1,2)]),(5,[(1,0,2),(1,1,2)]),(5,[(1,0,1),(1,1,2)]),(5,[(1,0,1),(1,0,2)]),(0,[(1,2,3),(1,1,4)]),(0,[(1,1,3),(1,2,4)]),(0,[(1,1,2),(1,3,4)]),(3,[(1,0,2),(1,3,4)]),(48,[]),(49,[]),(0,[(1,1,2),(1,2,3),(1,1,5)]),(0,[(1,1,2),(1,2,3),(2,3,4)]),(0,[(1,1,2),(1,1,3),(1,2,5)]),(0,[(1,1,2),(1,1,3),(2,3,4)]),(15,[(1,1,2)]),(4,[(1,0,3),(1,2,4)]),(11,[(1,0,2)]),(16,[(1,2,3)]),(3,[(1,0,3),(1,2,4)]),(12,[(1,0,2)]),(39,[(1,1,2)]),(0,[(1,1,3),(1,1,2),(1,2,4)]),(0,[(1,1,3),(1,1,2),(2,3,5)]),(0,[(1,1,2),(1,1,3),(2,2,5)]),(4,[(1,1,3),(1,0,3),(1,0,4)]),(3,[(0,0,3)]),(3,[(0,1,3)]),(0,[(1,0,2),(1,0,3)]),(14,[(2,0,2)]),(4,[(1,0,1),(1,0,3),(1,1,3)]),(8,[(1,1,2)]),(0,[(1,0,2),(1,1,3),(1,2,3)]),(30,[(1,1,2)]),(0,[(1,0,1),(1,1,3),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,1,3)]),(4,[(1,1,3),(1,2,4)]),(4,[(1,1,2),(1,3,4)]),(4,[(1,1,3),(2,2,4)]),(4,[(1,1,2),(2,3,4)]),(4,[(1,1,3),(1,1,2)]),(1,[(1,1,3),(1,2,4)]),(16,[(1,1,2)]),(3,[(1,1,2),(1,2,3)]),(1,[(1,0,1),(1,1,3),(1,2,3)]),(3,[(1,2,3),(3,0,2)]),(50,[]),(51,[]),(52,[]),(0,[(1,1,3),(1,2,3),(3,0,2)]),(53,[]),(2,[(1,0,3),(1,2,4)]),(1,[(1,0,1),(1,3,4),(1,2,3)]),(54,[]),(1,[(1,0,1),(1,1,2),(1,2,3)]),(3,[(1,0,2)]),(1,[(1,0,2),(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3),(3,0,2)]),(0,[(1,2,3),(1,0,1),(1,3,5)]),(2,[(1,0,2),(1,2,3),(3,1,3)]),(1,[(1,0,2),(1,2,3),(3,1,3)]),(0,[(1,0,2),(1,1,2)]),(0,[(1,0,2),(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,0,2),(3,1,2)]),(4,[(1,0,1),(1,1,3),(1,2,3)]),(2,[(1,1,3),(1,2,3),(3,0,2)]),(55,[]),(56,[]),(4,[(1,0,3),(3,2,3)]),(14,[(1,1,2)]),(2,[(1,1,2)]),(4,[(1,0,2),(1,1,3),(1,1,4)]),(2,[(1,1,2),(0,0,3)]),(4,[(1,0,2),(1,1,3),(1,0,5)]),(3,[(1,0,2),(0,1,3)]),(30,[(2,0,2)]),(3,[(1,0,3),(1,1,2),(1,3,5)]),(0,[(1,1,3)]),(3,[(1,0,2),(1,2,3)]),(1,[(1,0,2),(1,0,3),(1,2,3)]),(20,[(1,1,2)]),(4,[(1,1,3),(3,0,3)]),(4,[(1,0,3),(1,1,3)]),(4,[(1,0,3),(3,1,3)]),(7,[(1,0,2)]),(3,[(1,1,2),(3,0,1)]),(3,[(1,1,2),(2,0,4)]),(0,[(1,0,1),(1,1,3)]),(4,[(1,0,1),(1,2,3)]),(4,[(1,0,1),(3,2,3)]),(4,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(2,0,3)]),(3,[(2,2,3)]),(3,[(0,2,3)]),(4,[(1,2,3),(1,0,1),(1,2,5)]),(57,[]),(58,[]),(4,[(1,0,2),(1,1,2),(1,0,5)]),(8,[(0,0,2)]),(0,[(2,0,3),(1,0,1)]),(0,[(2,0,3),(2,0,1)]),(8,[(1,0,2)]),(0,[(2,1,2),(0,0,3)]),(0,[(2,1,2),(1,0,3)]),(59,[]),(0,[(1,0,2),(1,0,3),(1,2,3)]),(30,[(1,0,2)]),(0,[(1,0,3),(1,2,3),(3,0,2)]),(0,[(1,0,2),(1,2,3),(3,0,3)]),(0,[(1,0,2),(1,0,3),(1,2,5)]),(0,[(1,0,3),(2,1,4)]),(4,[(1,0,1),(3,2,4)]),(0,[(1,0,3),(1,0,1),(3,3,5)]),(8,[(3,0,1)]),(3,[(0,0,1),(1,0,1),(3,2,5)]),(8,[(2,0,1)]),(3,[(0,0,1),(1,0,1),(1,2,5)]),(4,[(0,0,1),(1,0,1)]),(3,[(1,0,3)]),(0,[(0,0,3)]),(0,[(2,2,3)]),(30,[(1,0,1)]),(30,[(2,0,1)]),(14,[(2,0,1)]),(0,[(1,0,1),(0,0,3)]),(0,[(1,0,1),(2,1,3)]),(9,[(0,0,2)]),(0,[(1,0,1),(2,2,3)]),(14,[(1,0,1)]),(0,[(2,1,3)]),(60,[]),(61,[]),(14,[(0,0,2)]),(14,[(3,0,1)]),(14,[(3,1,2)]),(14,[(2,1,2)]),(0,[(0,2,3)]),(0,[(0,2,3),(2,0,3)]),(9,[(0,1,2)]),(0,[(0,2,3),(0,0,3)]),(7,[(1,0,1)]),(9,[(3,0,2)]),(0,[(1,1,3),(0,2,3)]),(0,[(0,1,3)]),(0,[(0,1,2),(1,1,2)]),(0,[(0,1,2),(1,1,2),(2,0,3)]),(0,[(0,1,2),(1,1,2),(0,0,3)]),(0,[(0,1,2),(1,1,2),(1,0,3)]),(7,[(1,1,2)]),(0,[(2,0,3),(0,1,3)]),(0,[(2,0,3),(1,1,2),(3,3,5)]),(62,[]),(0,[(1,2,3),(0,2,3)]),(0,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(2,0,5)]),(0,[(0,2,3),(1,2,3),(0,0,5)]),(5,[(0,1,2),(1,1,2)]),(63,[]),(0,[(1,1,2),(1,1,3)]),(5,[(1,1,2),(1,0,3)]),(40,[(1,1,2)]),(32,[(1,0,1)]),(40,[(1,0,2)]),(0,[(2,1,2),(2,0,3)]),(0,[(2,1,2),(1,0,1)]),(0,[(2,1,2),(1,0,1),(1,0,3)]),(0,[(2,0,3),(1,0,1),(1,1,2)]),(0,[(1,1,2),(1,0,2)]),(0,[(1,0,2),(1,1,3),(1,2,5)]),(0,[(1,1,3),(1,2,3),(0,0,1)]),(0,[(1,1,3),(1,2,3),(2,0,1)]),(9,[(2,1,2),(1,0,1)]),(9,[(2,1,2),(2,0,2)]),(5,[(0,1,2)]),(0,[(1,0,1),(1,0,2),(1,0,3)]),(9,[(1,0,1),(1,1,2)]),(30,[(2,1,2)]),(0,[(2,0,3),(1,0,1),(2,1,2)]),(11,[(3,0,2)]),(30,[(3,0,2)]),(14,[(3,0,2)]),(11,[(0,0,1),(1,0,1)]),(11,[(2,0,2)]),(11,[(2,1,2)]),(0,[(0,0,1),(1,0,1)]),(11,[(0,1,2)]),(0,[(0,0,1),(1,0,1),(1,3,5)]),(14,[(0,0,1)]),(11,[(3,1,2)]),(30,[(3,1,2)]),(12,[(3,0,1)]),(12,[(2,0,1)]),(7,[(2,0,1)]),(11,[(2,0,1)]),(11,[(3,0,1)]),(11,[(0,0,1)]),(7,[(3,1,2)]),(7,[(2,1,2)]),(0,[(1,1,2),(2,0,3)]),(11,[(0,0,2)]),(7,[(2,0,2)]),(11,[(1,0,2),(1,1,2)]),(9,[(1,0,1),(3,2,3)]),(0,[(2,0,3),(1,0,2),(2,1,3)]),(30,[(2,0,2),(1,0,1)]),(0,[(2,0,3),(1,0,2),(0,1,3)])]
def s7_t : Tabs := (s7_C.map (mkCut true s7_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(17,16),(17,1),(6,4),(6,2),(10,8),(10,2),(18,16),(18,2),(12,8),(12,4),(20,16),(20,4),(24,16),(24,8),(10,16),(18,4),(24,0),(17,0),(19,2),(5,8),(19,8),(22,8),(17,4),(9,2),(20,8),(20,0),(7,4),(18,0),(19,1),(21,1),(25,1),(3,0),(12,0),(21,4),(22,4),(14,16),(7,1),(14,8)],[],[[],[1],[2,1],[3,2,1],[0,1],[0,2,1],[0,3,2,1],[1,0,2,1],[1,0,3,2,1],[2,1,0,3,2,1],[0,1,2,3],[0,1,2,1,3],[0,1,2,3,2,1],[1,2,3],[1,2,1,3],[1,2,3,2,1],[2,3],[2],[3],[3,2],[0,1,0,2],[0,1,2,1,0],[1,0,2],[1,2,1,0],[0],[2,3,2,1],[0,2,3,2,1],[0,2],[2,3,2],[0,1,2,1,0,3],[0,1,2,3,2,1,0],[1,2,1,0,3],[1,2,3,2,1,0],[2,1,0,3],[2,3,2,1,0],[2,1,0],[3,2,1,0],[2,1,0,3,2,1,0],[1,0],[1,0,3],[0,2,1,3,2],[0,1,3,2],[0,1,0,2,1,3],[2,1,3,2],[1,3,2],[1,0,2,1,3],[1,0,2,1,3,2],[0,1,0,2,3,2,1],[0,1,2,1,0,3,2,1],[0,3,2],[0,3],[1,0,2,3,2,1],[0,2,3],[1,2,1,0,3,2,1],[0,1,0,3],[0,1,2,3,2],[0,1,2],[2,1,3],[0,2,1,3],[0,1,3],[0,1,2,1],[1,3],[1,2,1],[1,2],[1,2,3,2],[0,1,0,2,1,3,2],[1,2,1,3,2],[1,3,2,1],[0,1,0,3,2,1],[0,1,3,2,1],[1,0,2,1,0,3,2,1],[1,0,2,1,3,2,1],[1,0,2,1,0]])
theorem s7_W : TabsP true s7_R s7_T s7_t := ⟨cutsGood s7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s7_D9 : List StD := [
([sw0,sw1,sw2,sw3,sw12],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[0,10000,30003,10006,10007,4],[1,10002,30004,10008,10009,2],[1,10002,30005,10010,10011,3],[1,10002,30006,10012,10013,4],[2,10003,30007,10014,10015,3],[2,10003,30008,10016,10017,4],[3,10005,30009,10018,10019,4]])]
noncomputable def s7_D8 : List StD := [
([sw0,sw1,sw4,sw2,sw3,sw12],[[0,1],[0,1],[0,30010,10003,5],[0,30011,10005,6],[0,30012,10007,7],[0],[1,30013,10009,5],[1,30014,10011,6],[1,30015,10013,7],[5,8,2,30000,10003,30016,10014],[6,8,3,30017,10005,30018,10015],[7,8,4,30019,10007,30000,10017],[5,10003,30000,10014,10015,6],[5,10003,30018,10016,10017,7],[6,10005,30016,10018,10019,7]])]
noncomputable def s7_D7 : List StD := [
([sw0,sw1,sw2,sw3,sw13,sw14],[[9,10,30007],[9,30020,10003,11],[9,30021,10005,12],[9,4],[9,10,13,10007],[10,30022,10009,11],[10,30023,10011,12],[10,9,14,10013],[10,4],[11,10003,30007,10014,10015,12],[11,10009,30000,10003,30024,14,30025],[11,10003,30024,10009,30000,13,30026],[12,10011,30017,10005,30027,14,30003],[12,10005,30027,10011,30017,13,30006],[9,10]]),
([sw0,sw1,sw4,sw2,sw7,sw3,sw12],[[15,16],[16],[15,16,5],[17],[15,30011,10005,18],[15,30012,10007,19],[15],[16,15,5],[20],[16,30014,10011,18],[16,30015,10013,19],[5,8],[5],[18,8,30000,10005],[19,8,30018,10007],[8],[5,30016,10015,18],[5,30028,10017,19],[18,21,6,30000,10005,30018,10018],[19,21,7,30018,10007,30000,10019],[10005,18,10018,10019]]),
([sw0,sw1,sw2,sw7,sw3,sw12],[[15,5,16],[15,5,16],[15,17],[15,30029,10005,10001],[15,30030,10007,10001],[5,15,16],[16,20],[16,30031,10011,10002],[16,30032,10013,10002],[5,8],[5,30033,10015,10003],[5,30034,10017,10003],[30035,3,10018,30000,10005,30018,30009],[30036,4,10019,30018,10007,30000,30037],[30009,10005,10007,10018,10019,30035,30036]]),
([sw15,sw0,sw1,sw2,sw3,sw12],[[22,7,8,23],[22,7],[8,30038,10003,2],[8,30035,10005,3],[7,8,9],[22,7,8,24],[22,30024,10003,10001],[22,30027,10005,10001],[22,7,10006],[8,30000,10009,10002],[8,30017,10011,10002],[7,8,10012],[30000,10003,10005,10014,10015,30039,30033],[7,10017,10019],[7,10019,10017]]),
([sw0,sw1,sw4,sw2,sw3,sw10,sw12],[[25,26],[26],[25,5,30040],[25,6,30041],[25,30042,30010,27,10001],[25,30042,10007,10001],[25],[26,5,30043],[26,6,30044],[26,30045,30013,27,10002],[26,30045,10013,10002],[5,30016,30033,28,10014],[6,30018,30039,28,10015],[27,28,8,30007,30000,30019,30046,29],[30,28,30007,10007,30000,10017],[5,6],[6],[5,30016,10017,10014],[5],[6,30018,10019,10015],[7,27,30000,10017,30007,10007]])]
noncomputable def s7_D6 : List StD := [
([sw0,sw1,sw10,sw16,sw17],[[31,32,10000,30000,10001,10002],[31,10001,30000,10000,30019,29,30042],[31,10001,30018,10000,30017,33,30047],[31,10000,30016,10004,30000,34,30048],[32,10002,30024,10008,30049,29,30045],[32,10002,30050,10008,30027,33,30051],[32,10002,30052,10010,30024,34,30053],[29,33,4,30,34],[29,34,4,30,33],[33,34,3,30,29]]),
([sw0,sw1,sw2,sw5,sw14,sw17],[[35,36,30038],[35,30054,10003,37],[38],[35,30055,30056,39,10004],[35,10004,34,10005],[36,30038,10009,37],[36,30013,30044,40,10020],[34],[36,38,34,10013],[10009,37,10003,30050,30057],[10003,37,10009,30000,30026],[10003,37,41,30000,10014,30009],[39,40,42,43,41,44,13],[35,39],[36,38]]),
([sw0,sw1,sw4,sw2,sw3,sw16,sw17],[[45,46],[46],[45,30058,47],[45,30059,48],[45,30060,10001],[45,30056,10001],[45],[46,30057,47],[46,30061,48],[46,30062,10002],[46,30063,10002],[47,30033,49],[48,30039,49],[50,30035,33],[51,30038,34],[47,30000,48],[52],[47,48,53],[48,47,54],[55],[47,48]]),
([sw0,sw1,sw2,sw3,sw13,sw14,sw18],[[56,30045,57],[56,58,11],[56,59],[58],[56,57,59],[60],[57,30043,11],[57,10011],[57,56,14],[58],[57,61,30064],[11,10015],[11,14],[11,62,63],[14],[10011,59],[10015,10011],[10011,59],[56,57],[11],[57,20]]),
([sw0,sw1,sw2,sw3,sw13,sw19],[[64,30063,30007,65,10008],[11,30017,30005,51,10009],[66,65,10011,30021,67,10005,30018],[68],[30018,65,0,66,67,57,30055,10007],[64,10008,65,11],[64,30023,10011,10008],[64,66,61,10008],[33],[11,30035,10015,10009],[11,66,62,10009],[13],[10011,69,67,30004,10005,30003],[10005,10007,10011,30000,30041],[61,17,67]]),
([sw15,sw0,sw2,sw9,sw3,sw12],[[15,70,24],[2,8,71],[70,72,8],[8,30035,10005,29],[73,8],[70,30000,30017,74,10001],[70,10001,75,10002],[70,30024,10005,10001],[70,76,10006],[24],[77,10005,30017,53,10015,30039],[76,53,10021,75,10019],[10002,10005,30000,53,10015,30024],[74,75,10002,76,53,10012],[10005,76,10019,10017]]),
([sw0,sw1,sw2,sw7,sw3,sw20,sw12],[[78,79,80],[78,80,79],[81],[78,80,18],[82],[78,59],[79,78,80],[83],[80,78,18],[84],[80,85],[86],[79,30019,18],[79,18,30016],[79,10017],[18,79,30018],[79,18],[10019,59],[87],[18,10019],[10017,59]]),
([sw0,sw1,sw4,sw2,sw3,sw21,sw16],[[56,64],[64],[56,30005,88],[56,89],[90],[56,89],[56],[64,30002,88],[64,91],[92],[64,91],[88,30017,51],[51,89],[90],[51,88,89],[88,53],[88,51,53],[93],[48,89,10015],[94,53,95],[88,51]]),
([sw0,sw1,sw4,sw2,sw3,sw22,sw12],[[30000,85,89],[96],[79,97,28],[28,89],[30010],[28,89],[98],[89,85,97],[97,85],[30013],[97,85],[79,85,28],[28,85],[29],[28,85],[89,28,18],[99],[89,53],[100],[18,54],[7,85,30000]]),
([sw23,sw0,sw1,sw4,sw2,sw3,sw12],[[0,19,17],[19,20],[19,17],[19,8],[6,95,21],[51],[30000,77,95],[75],[101,102,103],[21,95],[19,30004,21],[104],[95,77,101],[21,105],[19,30001,21],[101,19,77],[21,95],[19,30000,21],[95,10015],[19,49],[19,49]]),
([sw24,sw0,sw1,sw2,sw3,sw25,sw12],[[106],[107,29,108],[106,109],[29,17],[30010],[28,30056,30030],[98,30063,110],[28,30017,111],[28,30000,112],[30000,28,113],[28,10007],[28,112,98],[28,98,112],[114],[28,115],[98,28,112],[116],[98,53],[117],[112,54],[113,115]]),
([sw0,sw1,sw2,sw7,sw3,sw22,sw12],[[118,79,97],[118,97,79],[96],[118,89],[30010],[118,89],[79,118,97],[98],[97,85],[30013],[97,85],[28],[79,53],[30016],[79,53],[30035,30018,89],[3],[10019,89],[119],[95,10019,120],[30036,89,30000]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[96,98,10000,18,85,10001,89],[96,28,10001,10000,121,59],[10000,98,18,89,122,10004],[30010,10006],[10000,98,30030,89,10007,30000,10013],[98,28,122,85,118,10003],[18,85,123,96,10005],[30013,10012],[95,96,10007,30032,85,10013,30024],[18,122,124],[30016,122,10016],[122,30034,10017,10003],[30018,18,10018],[18,30036,10019,10005],[4,30036,30000,85,10007]]),
([sw23,sw0,sw1,sw2,sw7,sw3,sw12],[[15,17],[17,95,20],[17,8],[4],[21,95],[125],[126,95],[126,127,103],[75],[21,95],[21,30004,127],[95,126,102],[104],[21,105],[95,30001,21],[101],[95,128],[21,30000,127],[21,95],[21,30000,127],[95,10019,10022]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,44,17,105],[17,44,20,95],[17,44,8,105],[3,44,30035,105,10005,30000,10018],[30018,30000,10007],[75,104,10000,105,95,19,10001],[75,101,10001,10000,127,63],[10000,10018,30004,95,10005,30018],[105,104,10000,44,30000,10006,19],[95,101,10002,126,128,10003,105],[10002,10005,30001,105,10011,30050],[95,75,19,30024,10012],[10003,95,30000,128,10015,30039,10005],[105,75,19,30038,10016],[105,19,10019,30035,10018]]),
([sw26,sw0,sw1,sw2,sw3,sw12,sw27],[[129],[130,10002],[30016],[30018],[30000],[30013],[130,10002],[131,128],[130,41,132],[130,44,128],[130,128,30000],[130,128],[10002,133],[10002,44],[10002,128],[130,128],[130,132,134],[135],[128,130,132],[136],[137]]),
([sw28,sw0,sw1,sw2,sw3,sw12,sw27],[[138],[139],[140,30016,41],[130,30018,141],[138,30000,41],[130,30046],[30000,130,41],[142,143],[130,41,144],[130,145,146],[130,41,30065],[41,147,130],[143,148,144],[41,149,146],[8,147,30046],[130,41,143],[130,143],[150],[144,41],[151],[152]]),
([sw0,sw1,sw4,sw2,sw3,sw12,sw27],[[30000,10001,10002],[139],[10001,30040,54],[10001,30041,53],[10001,30056,54],[10001,30010,0],[138],[10002,30043,54],[10002,30044,53],[10002,30063,54],[10002,30013,8],[54,30016,140],[53,30018,141],[139,30000,54],[8,30000,30046],[48,54],[47,53],[153],[48,54],[154],[155]]),
([sw29,sw0,sw1,sw2,sw3,sw25,sw12],[[156],[98,30013,17],[17,30016,28],[156,30018,98],[98,30056,30030],[157],[98,30063,158],[28,30017,159],[98,30000,160],[98,30000,10006],[98,10006,10023],[98,160,28],[28,98,160],[161],[28,115],[98,28,160],[162],[98,53],[163],[160,54],[4,115,30000]]),
([sw0,sw30,sw1,sw2,sw3,sw12],[[17],[17,19,104,10001],[17,127,101,10000],[10001,104,30010,95,10005,30018,10011],[19,89,10007,104,10024],[17,19,104],[17,19,101],[3,21,30002,95,10005,30018,10018],[19,89,10007,21,10019],[17,10002,126,10003],[17,30001,10011,10002],[17,19,10012],[17,30000,10015,10003],[17,19,10016],[19,10019,10007]]),
([sw15,sw0,sw1,sw31,sw2,sw3,sw12],[[164,165,166],[165,164],[3,30007,8],[167,77],[3,95,167],[168],[169,165,95],[8,30024,77],[167,170],[167,95],[165,66],[8,30000,95],[167,77],[167,171],[165,66],[172],[173],[165,30000,104],[30000,95,77],[165,66],[165,174]]),
([sw15,sw0,sw1,sw2,sw3,sw10,sw12],[[25,175,139],[175,25],[28,30016,20],[28,30018,3],[28,30007,29],[176],[177,175,158],[28,30027,178],[28,30024,178],[28,30024,178],[175,178],[28,30017,178],[28,30000,178],[28,30000,178],[175,178],[30000,54,53],[173],[175,53,10019],[172],[175,54,10017],[175,54,30000]]),
([sw29,sw32,sw0,sw1,sw2,sw3,sw12],[[0,30018,17],[156],[17,30054,117],[17,30059,100],[156,10005,117],[157],[0,30000,75],[117,100],[117,100],[28],[75,179],[117,30001,75],[100,30000,75],[117,10005],[117,180,10023],[117,179,100],[100,148,160],[100,179],[117,148,179],[117,181],[10005,180]]),
([sw33,sw0,sw1,sw2,sw3,sw12,sw17],[[182,183],[183,182],[50,77],[30018],[30000],[30016],[184,77,185],[50,170],[50,41,77],[50,44,77],[50,41,77],[50,77],[50,148,170],[50,44,170],[50,44,170],[77,41],[77,44],[77,41],[30000,44,41],[186],[187]])]
noncomputable def s7_D5 : List StD := [
([sw0,sw1,sw4,sw10,sw16,sw17],[[31,32],[32],[31,30049,10001],[31,30027,10001],[31,30024,10001],[31],[32,30019,10002],[32,30017,10002],[32,30000,10002],[188,30019,29],[189,30017,33],[190,30000,34],[6,191,153],[17,192,7],[6,193,17]]),
([sw0,sw1,sw10,sw34,sw16,sw17],[[31,10002],[31,29],[29],[31,194,195],[31,195,196],[10002,195],[32,10002,10012],[10002,196],[10002,195],[31],[29,197,198],[29,199,200],[30,194,42],[30,199,20],[29]]),
([sw0,sw1,sw10,sw16,sw35],[[31,30024,10002,201],[31,201,202,203,10005],[31,204,205,206,10025],[34],[10002,10005,207,30050,10008,30045],[10002,201,204,30024,10008,30051],[10008,17,10002,30000,30066],[202,203,204,201,191,205],[14,203,202,208,10005,209],[42,206,201,208,203,210]]),
([sw15,sw2,sw5,sw6,sw12],[[96,8,30038,10003],[8,211,212],[8,211,213],[214,8],[215,75,171,10003,30024,30017,10009],[10003,104,10009,30000,30027],[10003,216,10017,10026],[8],[171,215,216,10026,10017],[216,10026,10017]]),
([sw0,sw9,sw6,sw16,sw17],[[217,218,77,30043,10001,30010,10004],[219,220,77,30044,10001,30011,10000],[10001,221,10000,30017,30047],[77,222,10004,30000,30048,10001],[219,217,141,223,224,225,226],[223,217,227,219],[34,217,223,228,207,17,53],[33,219,224,77,229,109],[224,219,227,217],[77,17,230,217]]),
([sw0,sw1,sw36,sw6,sw16,sw17],[[218,30000,231],[232],[218,30041,233],[218,233,234],[218,30060,10000],[231,30043,235],[236],[231,30063,10010],[231,235,237],[130,30019,219],[218,234],[237,233],[234,235],[231,237],[234,233,235]]),
([sw0,sw1,sw36,sw10,sw18,sw17],[[31,170],[33],[31,170],[33],[31,238,89],[130,170],[239,128,240],[241,170,10010],[170,10010],[31,170],[33],[130,238,89],[242,170,148],[170,130],[130,89]]),
([sw0,sw1,sw2,sw5,sw19,sw17],[[243,30022,149],[149,30027,37],[244],[182,30056,10004],[65,10004,67],[243,245,37],[243,30013,181],[246],[243,149,115],[37,30016,179],[247],[37,149,181],[42,149,148],[65,149,67],[67,181]]),
([sw15,sw0,sw2,sw6,sw10,sw12],[[248,26],[98,30067,28],[28,248,213],[28,148,29],[249],[28,30000,171],[28,171,95],[28,30024,178],[28,178,171],[95,28,53],[250],[251,53,10027],[28,171],[95,178],[171,53,30000]]),
([sw0,sw1,sw2,sw5,sw14,sw27],[[149,30038,41],[149,30006,37],[252],[130,30004,253],[9,41,67],[41,30002,37],[217,30061,254],[246],[67,149,115],[37,41,254],[37,149,253],[255],[256,149,41],[9,149,67],[67,41,115]]),
([sw15,sw2,sw36,sw3,sw6,sw12],[[257,258,8],[8,258,259],[8,260,242],[8,260,261],[214],[8],[171,30000,170],[104,30017,10003],[170,10028,10019],[262,30024,10029],[104,171,170],[171,178],[8],[171,10019,10017],[170,10019,178]]),
([sw0,sw1,sw2,sw3,sw13,sw37],[[148,30007,145],[148,30005,178],[178,30004,53],[171],[0,145,67],[145,263,178],[145,148,178],[53,178,115],[10002],[263,148],[217,145,53],[10003],[263,148],[10005],[0,148,67]]),
([sw23,sw0,sw1,sw36,sw3,sw16],[[264,17],[17,20],[20,17],[265,95,149],[17,65,104],[149,95],[75],[149,95],[104,127,170],[104,95],[170,10011,53],[95,149],[104,95],[104,149,127],[95,149]]),
([sw0,sw1,sw2,sw5,sw13,sw38],[[148,30038,266],[148,267],[268],[269],[0,267],[266,115],[266,148,115],[266,115],[270],[40,148],[271,267],[20,148,10003],[268,148],[0,267],[0,148,267]]),
([sw29,sw1,sw2,sw5,sw25,sw12],[[98,30068,96],[96,30069,148],[156],[98,95],[157],[98,118],[118],[118],[118],[98,148,118],[118],[98,118],[98,95],[118],[95,148,118]]),
([sw24,sw1,sw2,sw5,sw25,sw12],[[98,29,272],[29,109],[273],[95],[98,30056,253],[98,118],[118],[118],[118],[98,253,118],[118],[98,118],[98,118],[118],[118]]),
([sw23,sw0,sw1,sw7,sw3,sw16],[[274,17],[17,20],[4],[181,95,21],[17,181],[181,95],[75],[21,95],[21,127,171],[104],[181,171,21],[95,181],[21,95],[21,127],[95,53]]),
([sw0,sw1,sw2,sw3,sw21,sw27],[[149,275,145],[149,30005,178],[149,30004,178],[139],[9,145,67],[145,30002,178],[145,30001,178],[138],[67,149,115],[66,275,54],[130,149,53],[276],[141,149,54],[277],[29,67,54]]),
([sw15,sw0,sw2,sw3,sw25,sw12],[[278,17,156],[17,181],[278,171,53],[22,181,95],[115],[171,30017,54],[53,30000,178],[22,171,95],[171,178],[171,53],[262],[77,53,10019],[75],[171,54,10017],[95,53,178]]),
([sw23,sw0,sw1,sw3,sw10,sw12],[[25,17],[17,20],[3,54],[279,54,280],[53],[254,281,170],[178,30024,282],[254,170],[281,178],[254,30000,283],[178,282],[281,254],[75],[281,10030,30035],[281,254]]),
([sw0,sw30,sw1,sw3,sw10,sw12],[[17],[17,281,77],[77,30006,282],[149,170],[281,234,10024],[17,281,20],[3,282,54],[149,77],[281,234,10019],[17,30000,170],[17,77],[17,254,281],[17],[281,10019,234],[281,149]]),
([sw15,sw2,sw36,sw9,sw3,sw12],[[17,284,181],[75,285],[17,284,181],[181,95,53],[73],[286],[287],[75,53],[75,53],[75,95,286],[104,95],[104,53],[75,53],[75,53],[95,174]]),
([sw29,sw32,sw1,sw36,sw3,sw12],[[0,170],[17,30059,117],[285],[117,10005],[288],[170,117],[117,170],[98],[170,181,75],[117,181],[10005,148,181],[75,179],[117,10005],[117,181],[10005,148,181]]),
([sw15,sw39,sw1,sw2,sw3,sw12],[[20,77,178],[178,20,289],[20,170,54],[242,253],[290],[75,77],[77,170,54],[177],[77,178],[178,30000,54],[178,10029,21],[170,178],[170,54],[170,10028,21],[10011,54,291]]),
([sw0,sw1,sw2,sw20,sw21,sw17],[[292,170],[292,170],[293],[253],[292,95],[95,77,54],[294],[295],[170,296,67],[174,170,10016],[235,170,10014],[170,54],[7,54,293],[7,95,174],[6,95,54]]),
([sw23,sw0,sw1,sw2,sw3,sw21],[[9,19,288],[19,297],[19,298],[174,95],[19,288],[149,19,95],[174,170,149],[149,95],[283],[174,299,234],[170,115,67],[282],[174,10015],[75,19,10031],[10015,174]]),
([sw28,sw4,sw2,sw3,sw22,sw12],[[10032],[95,30070,54],[96,30071,170],[30046],[95,30046,54],[54,170],[53,95],[300],[54,67],[95,54,170],[301],[96,53],[302],[95,54,303],[304,54,30000]]),
([sw23,sw0,sw1,sw2,sw3,sw13],[[0,288],[288,170,20],[288,170,54],[305,95,174],[0,288],[104,170],[174,170,149],[104,95],[77],[95,126],[170,126],[126],[170,126],[104,170,126],[126]]),
([sw40,sw0,sw1,sw4,sw2,sw3],[[0,77,67],[67,170,115],[22,67,306],[67,77,53],[307,95,54],[30000,77,170],[253],[115,170],[77,67,115],[149],[95,77,54],[67,115],[54,77],[53,67],[77,53,67]]),
([sw23,sw28,sw4,sw2,sw3,sw12],[[0,170,30007],[22,20,306],[20,170,149],[149,95],[65],[10032],[149,30038,95],[170,30038,149],[170,30038,104],[104,170,282],[254,95,21],[282,149],[170,282,95],[170,149],[95,149]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,77,17],[17,20],[17,77,149],[149,95],[65],[149,77,95],[149,170],[77,95,149],[77,174],[95,77,282],[170,171,75],[95,149],[77,282,95],[77,149],[95,149]]),
([sw0,sw1,sw2,sw7,sw3,sw41],[[181,18],[18],[18],[18],[181,18],[18],[18],[181,18],[18],[18],[18],[18],[18],[18],[181,18]]),
([sw42,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,308,309],[98,96,77],[98,77,113],[98,157,77],[98,77,282],[181,98,53],[114],[113,115],[98,282],[310],[98,181],[117],[113,54],[113,181]]),
([sw24,sw1,sw2,sw3,sw22,sw12],[[98,77,96],[96,308],[98,96,77],[30030],[98,30010,77],[98,77,282],[181,98,53],[114],[282,115,53],[98,282],[310],[98,181],[117],[282,54,181],[14,181,10023]]),
([sw23,sw0,sw1,sw2,sw3,sw43],[[65,288],[288,65],[65,181],[181,282,149],[65],[181,77,170],[149,170],[282,95],[10023],[95,181],[181,115,53],[10033],[77,282,95],[10031],[30000,282,10022]]),
([sw44,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,283],[98,253,77],[98,77,300],[98,113,77],[98,77,253],[283,98,181],[114],[282,115,53],[98,283],[310],[98,181],[117],[283,54,181],[14,181,30056]]),
([sw40,sw0,sw1,sw2,sw7,sw3],[[15,77,113],[70,115,311],[312,77,53],[104,115,313],[314,282,21],[282,77,170],[115,170],[180],[77,95,115],[95,77,282],[235],[53,115],[54],[77,53,95],[10022,115]]),
([sw29,sw1,sw2,sw3,sw22,sw12],[[282,77,170],[115,170],[282,95],[30030],[67],[95,282],[170,115,53],[114],[282,115,53],[77,282,95],[310],[77,53,98],[117],[282,54,315],[14,115,174]]),
([sw44,sw1,sw2,sw3,sw12,sw37],[[282,77,217],[217,283],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,174],[30046],[77,282,253],[77,53,235],[30040],[282,174],[30041],[30056]]),
([sw0,sw1,sw2,sw3,sw12,sw45],[[282,77,253],[115,283,174],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,115,174],[30013],[77,282,253],[77,53,235],[30016],[282,174],[30018],[30000]]),
([sw40,sw0,sw1,sw2,sw3,sw12],[[0,77,174],[174,282],[316,77,149],[174,282],[53],[282,77,283],[174,283],[77,253],[77,174],[174,77,282],[283,171],[282,174],[77,282,174],[77,149],[282,174]]),
([sw40,sw0,sw1,sw2,sw3,sw22],[[53,77,113],[53,282,115],[235,53],[315,282,235],[14],[282,77,253],[115,283,171],[53,253,77],[10023],[235,77,282],[53,115],[10033],[77,53,253],[10031],[10022]]),
([sw40,sw0,sw1,sw2,sw3],[[0,174,67,77,10001,113],[67,174,22,115,282,10002,317],[67,149,316,53,77,10003,318],[113,174,307,235,282,10005,21],[253,282,10000,77,10002,10001],[174,115,10001,10000,10003],[77,115,10001,253,67,10005,10004],[174,10003,282,77,10009],[10002,67,235,115,10011,10005],[77,174,10003,253,282,10015,10005]]),
([sw0,sw46,sw1,sw2,sw3,sw12],[[174],[282,77,253],[149,283,171],[282,253,77],[77,67,10024],[149,282],[149,77],[149,282],[0,67,30000],[253,282,77],[283,171],[282,149],[77,282,253],[77,149],[282,149]]),
([sw47,sw0,sw1,sw2,sw3,sw12],[[0,77,253],[149,20,319],[253,77],[282],[181],[253,77],[149,170],[77,253],[77,174],[253,77],[170,235],[170,149],[77,253],[77,149],[30000,149,235]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[253,77],[315,283,171],[77,253],[113],[253,67,315],[253,77],[315,171,283],[320],[67,115],[77,253],[310],[253,181,67],[117],[315,235],[14,67,30000]]),
([sw29,sw11,sw1,sw2,sw3,sw12],[[0,77,253],[253,77],[315,170],[77,253],[234],[315,320],[253,77],[283],[235,181],[253,77],[315,235],[170,179,21],[77,253],[77,181,235],[315,235]]),
([sw29,sw48,sw0,sw1,sw2,sw3],[[0,30000,67],[283],[235,10034,113],[113,10035,115],[113,10036,115],[0,10024,174],[174,115,306],[235,181],[174,235,181],[235,30063,180],[115,30017,174],[115,30000,178],[235,115,181],[181,235],[174,282]]),
([sw0,sw1,sw2,sw3,sw49,sw27],[[235,240],[256,283,174],[282,253,178],[235,174,283],[256,240],[235,282],[240,235],[282,240],[8,235,10002],[256,283,174],[235,256,253],[321],[256,235],[136],[256,240]]),
([sw26,sw50,sw1,sw2,sw3,sw12],[[30010],[235,10002],[170],[95],[240],[10002,235],[0,256,321],[0,282,253],[0,235,322],[235,282],[10002,235],[10002,178],[256,282,253],[235,256,253],[256,235]]),
([sw0,sw1,sw2,sw3,sw51,sw27],[[235,30046,253],[256,283,178],[178,253],[235,178,253],[256,253,30065],[235,282],[256,235],[282,178],[8,235,30046],[256,253],[235,256,253],[321],[256,235],[136],[256,322]]),
([sw0,sw1,sw2,sw3,sw52,sw12],[[315,170],[315,170],[282,67],[113],[315,67],[240,315,282],[315,115,67],[320],[170,115,67],[315,282,67],[310],[170,181,67],[315,282,117],[315,30000,282],[14,67,104]]),
([sw53,sw0,sw1,sw2,sw3,sw12],[[0,283,113],[42,315,320],[42,315,310],[42,283,117],[14,65,104],[283,170,315],[315,283,170],[282,95],[283,240,315],[95,315,282],[283,171],[170,179,21],[315,283,95],[170,181,240],[283,10019,315]]),
([sw28,sw4,sw2,sw3,sw12,sw27],[[10037],[256,30070,27],[27,30071,130],[256,30046,275],[256,30046,10002],[130,282],[256,253],[282,180],[8,282,30046],[256,282,130],[130,256,253],[321],[256,130,282],[136],[137]]),
([sw23,sw0,sw1,sw2,sw54,sw3],[[323,240],[324,325,326],[240,170,181],[30035],[240,282,30000],[181,240],[178,170,327],[178,30004,104],[282,95],[240,181],[240,30001,101],[240,171,283],[170,30000,104],[170,282,95],[180]]),
([sw0,sw1,sw2,sw3,sw55,sw19],[[65,30046,180],[180,30040,327],[65,10004,178],[65,180,10004],[65,180,10004],[65,327,282],[180,115],[327,65,178],[328],[65,282],[65,62],[62],[327,180],[62],[65,62]]),
([sw0,sw1,sw2,sw56,sw3,sw12],[[282,170],[115,170],[180],[282,95],[115,240],[95,282],[320],[170,115,283],[282,115,67],[310],[170,282,95],[170,181,240],[320,282,117],[313,115,30000],[282,10018]]),
([sw57,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[22,282,178],[316,253,234],[307,283,180],[0,181,113],[283,171],[113,283],[282,253,113],[283,10007,10023],[253,282,77],[283,171],[282,149],[171,283],[253,149],[283,149]]),
([sw0,sw1,sw2,sw3,sw58,sw16],[[180,240,149],[180,30040,149],[149,195,178],[195,180],[195,180],[240,30043,51],[180,195,240],[195,240],[195,149],[180,53],[20,149,53],[170],[329,180,10015],[240,180,10036],[51,240]]),
([sw29,sw59,sw1,sw2,sw3,sw12],[[253],[117,170],[100,170],[117,95],[240],[117,170],[117,170,100],[117,95],[14,180],[117,119],[170,119],[170,119],[117,119],[117,119],[95,180]]),
([sw0,sw1,sw60,sw2,sw3,sw12],[[282,170],[180],[171,170,283],[282,95],[171,240,115],[149],[95,282],[170,171,283],[282,115,67],[20,170,310],[310,282,117],[306,240,30000],[170,282,171],[170,49],[282,49]]),
([sw61,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[149,170],[149,77],[0,282,180],[240],[180,77],[180,170,149],[77,95,149],[77,180],[95,77,49],[180,235,170],[170,149],[77,54],[77,149],[95,180]]),
([sw62,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[149,282],[149,42,330],[180,283],[0,256,322],[283,30000,149],[180,283],[149,253,113],[283,180],[253,282,137],[283,195,322],[282,149],[180,283],[253,149],[283,180]]),
([sw15,sw0,sw2,sw63,sw3,sw12],[[180,77],[20,77,167],[167,20,313],[180,95],[65],[180,170,167],[180,77],[77,95,167],[77,180],[167,77],[180,30000,77],[77,254],[180,167,170],[95,254],[95,180]]),
([sw15,sw0,sw1,sw2,sw3,sw64],[[180,77],[104,313],[104,77,149],[180,95],[104,65],[180,77],[180,170,149],[77,95,104],[77,180],[104,77,49],[180,171],[95,149],[180,30000,77],[77,149],[95,180]]),
([sw15,sw0,sw1,sw31,sw10,sw12],[[331,77,180],[332,333],[20,30007,28],[180,77],[334],[180,77],[77,30024,332],[332,170],[77,180],[28,30000,170],[180,77],[170,178],[10038],[104,30000,335],[77,180]]),
([sw15,sw65,sw0,sw1,sw2,sw3],[[8,30000,240],[137,240],[178,137,282],[240,10035,149],[240,10036,149],[8,10039,178],[8,10040,240],[149,215,336],[149,104,215],[149,240],[178,30027,149],[178,30024,149],[240,30017,49],[240,30000,49],[180,337,254]]),
([sw66,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[22,20,306],[20,77,8],[180,282,49],[0,51,101],[282,77,170],[49,170],[77,338],[77,240,101],[49,77],[49,171],[282,149],[77,282,171],[77,49],[282,49]]),
([sw15,sw0,sw67,sw2,sw3,sw12],[[180,171],[22,20,313],[20,77,100],[180,171],[65],[180,171],[180,30024,100],[77,95,100],[171,180],[100,77],[180,171],[95,149],[180,54,77],[77,10021,104],[171,180]]),
([sw0,sw1,sw2,sw3,sw58,sw17],[[180,77],[180,170,50],[77,253],[50,180,253],[77,180],[50,77],[180,195,170],[50,170,195],[170,195],[180,253,77],[253,77],[77,253],[339,180,54],[186],[50,307]]),
([sw33,sw0,sw1,sw2,sw54,sw17],[[340,77,180],[341,342],[343,77],[30009],[171],[180,77],[180,170,341],[77,30024,341],[77,180],[343,77],[180,30000,170],[343,149,170],[77,30000,180],[77,149],[10022]])]
noncomputable def s7_D4 : List StD := [
([sw0,sw4,sw10,sw16,sw38],[[180],[188,30018,344],[189,30000,171],[345,344,95],[188,171],[189,344],[345,95],[344,346,171],[95,171,282],[95,344,282]]),
([sw0,sw1,sw10,sw16,sw68],[[180,171],[188,95],[171,180],[10000],[180,171],[95,347],[10008],[171,180],[20,180,282],[20,282]]),
([sw0,sw1,sw10,sw18,sw38],[[347,30000,180],[347,283,178],[171],[345,180,240],[180,235,178],[189,347,348],[170],[40,347,235],[240,347,283],[20,283]]),
([sw15,sw2,sw5,sw25,sw12],[[28,282,98],[28,171],[28,282,170],[240],[171,28,282],[116],[77,53,10026],[28,170],[282,10026,180],[170,53,149]]),
([sw23,sw0,sw6,sw10,sw12],[[248,171,178],[178,170],[349,171],[240],[347,171,170],[178,170,349],[171,178],[178,171,101],[170,178],[171,349]]),
([sw0,sw30,sw6,sw10,sw12],[[178],[347,170],[349,170],[171,240,10024],[347,170],[349,170],[248,240,10027],[240,171,101],[170,347],[170,349]]),
([sw15,sw39,sw9,sw3,sw12],[[8,171],[350,351,170],[100,253,315],[352],[350,8,170],[353],[171,178],[170,253],[170,178],[10011,54,291]]),
([sw0,sw9,sw6,sw16,sw35],[[218,30011,180],[220,95],[221,180,195],[77],[180,195,178],[195,349],[17,195,171],[95,180],[17,180,171],[17,54,315]]),
([sw15,sw36,sw6,sw10,sw12],[[178,171],[178,354,170],[8,171],[249],[104,171,170],[178,170,8],[171,178],[178,171,8],[170,178],[171,54,30000]]),
([sw4,sw36,sw6,sw16,sw17],[[195,171,180],[45,195,236],[195,170,50],[51,195,171],[130,171,170],[171,170,50],[98,355,77],[95,54,149],[170,171,51],[171,355,170]]),
([sw0,sw1,sw69,sw16,sw17],[[256,171,253],[256,253,171],[256,283,171],[256,253,67],[356,95,357,10041],[253,282,10042],[283,171],[256,253],[171,256,283],[256,171]]),
([sw15,sw65,sw0,sw2,sw6],[[8,171],[358,171,253],[358,10035,54],[359,358,95],[8,10026,178],[171,215],[359,171,360],[171,30000,54],[359,171,95],[359,54,282]]),
([sw0,sw9,sw6,sw14,sw27],[[54,171,180],[282,171,219],[54,171,253],[361,180,10001],[180,54,282],[253,219,362],[219,171],[282,54,180],[219,171],[219,171]]),
([sw0,sw1,sw70,sw18,sw17],[[282,170],[45,170],[171],[282,180,67],[180,282,178],[54,282,10043],[170,178],[42,170,54],[170,282,180],[42,282,54]]),
([sw0,sw1,sw7,sw10,sw41],[[282,170],[180],[315,170],[282,67],[320],[308,282,77],[170,65,67],[315,310],[54,282],[170,282,67]]),
([sw29,sw48,sw1,sw2,sw5],[[0,67],[282,10034,363],[54,10035,195],[77],[67,282,178],[67,262],[178,67,282],[54,282,195],[180,195,171],[178,282]]),
([sw15,sw71,sw9,sw3,sw12],[[262,308,171],[350,351,313],[308,171,180],[352],[262,171],[262,353,364],[171,180],[180,171],[170,178],[171,180]]),
([sw0,sw1,sw72,sw17,sw73],[[180,170,282],[191,170],[282,180,95],[365],[180,282,95],[170,178],[109,170,30013],[170,180],[321],[322]]),
([sw74,sw0,sw1,sw2,sw17],[[182,293,366],[293,40,367],[180,170,30016],[293,180],[293,170,40],[40,170],[40,293,95],[293,77],[293,40,170],[170,54]]),
([sw0,sw1,sw72,sw17,sw68],[[40,170],[40,170],[40,180,95],[366],[180,77],[170,40,293],[367],[170,180],[29,170,30016],[215]]),
([sw40,sw28,sw4,sw2,sw3],[[0,95,30007],[22,368,306],[368,77,149],[368,95,149],[10032],[95,30072,149],[77,30007,149],[180,77,54],[53,95],[95,54,77]]),
([sw75,sw0,sw1,sw10,sw12],[[25,29],[54,95,347],[29,25],[203],[347,95],[347,95],[322,180,195],[180,195,369],[95,347],[95,347]]),
([sw23,sw76,sw9,sw3,sw12],[[369,77,180],[370,371,372],[369,95,180],[373],[180,77],[77,95,104],[77,180],[180,282],[95,178],[95,180]]),
([sw23,sw0,sw9,sw77,sw12],[[369,77,180],[370,95,374],[369,77,180],[65],[180,77],[126,95],[77,180],[180,77],[95,178],[77,180]]),
([sw23,sw0,sw9,sw3,sw78],[[369,77,178],[178,95],[369,95,180],[369,77,104],[180,77],[77,95,104],[104,178,171],[178,171,180],[95,77,178],[77,180,95]]),
([sw79,sw0,sw1,sw2,sw3],[[0,77,67],[67,69,375],[67,77,376],[69,180,54],[282,77,253],[54,283,171],[77,253],[54,77],[283,171],[77,54]]),
([sw0,sw1,sw2,sw80,sw43],[[282,95],[171,283],[282,95],[377],[95,282],[283,171],[378],[95,282],[379],[34,282,54]]),
([sw23,sw0,sw1,sw2,sw81],[[180,171],[370,95,178],[370,77,149],[180,171],[180,171],[180,283],[178,95,149],[95,77,282],[180,171],[180,283]]),
([sw0,sw82,sw1,sw2,sw3],[[0,171,180],[282,171,283],[171,283],[282,253,77],[22,282,149],[149,253],[149,171],[253,282,77],[283,171],[171,282]]),
([sw40,sw0,sw1,sw2,sw3],[[0,171,180],[22,95,149],[149,77],[180,171],[180,171],[171,283],[149,95],[95,77,282],[180,171],[171,283]]),
([sw47,sw0,sw1,sw2,sw54],[[323,95],[283,171],[95,283],[10036],[283,95,171],[171,283],[283,30004,149],[95,282],[95,30001,180],[180,30000,77]]),
([sw0,sw1,sw7,sw72,sw17],[[282,171,283],[180],[171,283],[282,95],[380],[95,282],[283,171],[380,77,54],[34,282,30000],[171,282]]),
([sw23,sw0,sw1,sw3,sw72],[[369,171,178],[178,95],[369,171,30000],[369,77,54],[283,171],[178,95,282],[171,283],[178,171,283],[178,77,282],[171,283]]),
([sw0,sw1,sw2,sw52,sw17],[[282,171,283],[171,283],[381],[282,95],[95,282],[380],[283,171],[379],[171,282],[34,282,54]]),
([sw62,sw4,sw2,sw3,sw12],[[382,171,283],[171,335,383],[171,283,384],[171,54,137],[382,283],[382,253],[283,180],[137,283],[335,149],[283,180]]),
([sw15,sw0,sw63,sw10,sw12],[[369,171,283],[385,20,372],[369,171,180],[65],[385,171,180],[104,95],[171,180],[180,171],[95,347],[171,180]]),
([sw15,sw0,sw1,sw10,sw64],[[20,171,283],[104,313],[29,171,149],[20,65,104],[104,171,180],[104,95],[171,180],[180,171],[95,347],[171,149]]),
([sw83,sw4,sw2,sw3,sw12],[[0,98,114],[98,54,109],[114,109],[95,54,67],[114,77,54],[382,95,53],[54,67],[114,54,77],[114,53],[95,54,368]]),
([sw33,sw0,sw2,sw84,sw17],[[369,77,180],[369,77,349],[180,14,372],[271],[180,170,349],[349,77,170],[77,180],[180,77,262],[77,349],[170,180]]),
([sw33,sw0,sw1,sw72,sw17],[[369,109,386],[109,14],[369,77,149],[271],[387,77,262],[149,170],[77,180],[262,77],[262,347,170],[77,149]])]
noncomputable def s7_D3 : List StD := [
([sw4,sw10,sw18,sw38],[[388,170,283],[109,283,77],[345,170],[109,170,271],[20,283],[109,170,77]]),
([sw15,sw65,sw36,sw6],[[29,389,283],[358,283],[359,358,372],[390,391,392],[359,283],[359,283]]),
([sw40,sw0,sw63,sw10],[[20,283,180],[104,283,347],[180,77],[180,77],[178,283],[180,283,77]]),
([sw85,sw0,sw1,sw10],[[25,77,180],[104,170,347],[180,77],[180,77],[347,170],[180,77]]),
([sw47,sw0,sw1,sw72],[[325,77,180],[347,325,372],[325,77,180],[180,77],[347,170],[180,77]])]
def s7_D2 : List StD := []
theorem s7_I2 : LevelN true s7_T 2 s7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C3x0 : levelOK true s7_T s7_t 2 (s7_D2.map Prod.fst) ((s7_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I3 : LevelN true s7_T 3 s7_D3 := levelStep s7_B s7_W s7_I2 (chunks 16 s7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x0 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x1 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x2 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (2*16)).take 16) = true := by decide +kernel
theorem s7_I4 : LevelN true s7_T 4 s7_D4 := levelStep s7_B s7_W s7_I3 (chunks 16 s7_D4 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C4x0
  · exact s7_C4x1
  · exact s7_C4x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x0 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x1 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x2 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x3 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x4 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (4*16)).take 16) = true := by decide +kernel
theorem s7_I5 : LevelN true s7_T 5 s7_D5 := levelStep s7_B s7_W s7_I4 (chunks 16 s7_D5 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C5x0
  · exact s7_C5x1
  · exact s7_C5x2
  · exact s7_C5x3
  · exact s7_C5x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x0 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x1 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (1*16)).take 16) = true := by decide +kernel
theorem s7_I6 : LevelN true s7_T 6 s7_D6 := levelStep s7_B s7_W s7_I5 (chunks 16 s7_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C6x0
  · exact s7_C6x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C7x0 : levelOK true s7_T s7_t 6 (s7_D6.map Prod.fst) ((s7_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I7 : LevelN true s7_T 7 s7_D7 := levelStep s7_B s7_W s7_I6 (chunks 16 s7_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C8x0 : levelOK true s7_T s7_t 7 (s7_D7.map Prod.fst) ((s7_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I8 : LevelN true s7_T 8 s7_D8 := levelStep s7_B s7_W s7_I7 (chunks 16 s7_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C8x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C9x0 : levelOK true s7_T s7_t 8 (s7_D8.map Prod.fst) ((s7_D9.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I9 : LevelN true s7_T 9 s7_D9 := levelStep s7_B s7_W s7_I8 (chunks 16 s7_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C9x0
  ))
theorem s7_L : LowN true s7_R s7_T 10 := lowSearch s7_B s7_I9 (by decide +kernel)
def stopT : Nat := 0xfffffffefffefee8fffffffefffefee8
def stopR : List Nat := [0, 1, 2, 3, 4, 5]
def stopE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17),(5,1,33)]
theorem stopB : baseOK stopT stopR stopE = true := by decide +kernel
theorem sliceCert0 : SliceN true stopR stopT (0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert1 : SliceN true stopR stopT (0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert2 : SliceN true stopR stopT (0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert3 : SliceN true stopR stopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert4 : SliceN true stopR stopT (0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert5 : SliceN true stopR stopT (0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert6 : SliceN true stopR stopT (0xffff000000000000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert7 : SliceN true stopR stopT (0xff00ff0000000000ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert8 : SliceN true stopR stopT (0xff000000ff000000ff000000ff,7,[0, 1, 2, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert9 : SliceN true stopR stopT (0xf0f0f0f000000000f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert10 : SliceN true stopR stopT (0xf0f00000f0f00000f0f00000f0f,7,[0, 1, 3, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert11 : SliceN true stopR stopT (0xf000f000f000f000f000f000f000f,7,[0, 1, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert12 : SliceN true stopR stopT (0x333333330000000033333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert13 : SliceN true stopR stopT (0x3333000033330000333300003333,7,[0, 2, 3, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert14 : SliceN true stopR stopT (0x330033003300330033003300330033,7,[0, 2, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert15 : SliceN true stopR stopT (0x3030303030303030303030303030303,7,[0, 3, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert16 : SliceN true stopR stopT (0x555555550000000055555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert17 : SliceN true stopR stopT (0x5555000055550000555500005555,7,[1, 2, 3, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert18 : SliceN true stopR stopT (0x550055005500550055005500550055,7,[1, 2, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert19 : SliceN true stopR stopT (0x5050505050505050505050505050505,7,[1, 3, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert20 : SliceN true stopR stopT (0x11111111111111111111111111111111,7,[2, 3, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert21 : SliceN true stopR stopT (0xff00000000000000ff,4,[0, 1, 2]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert22 : SliceN true stopR stopT (0xf0f0000000000000f0f,4,[0, 1, 3]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert23 : SliceN true stopR stopT (0xf000f00000000000f000f,4,[0, 1, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert24 : SliceN true stopR stopT (0xf0000000f0000000f0000000f,4,[0, 1, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert25 : SliceN true stopR stopT (0x33330000000000003333,4,[0, 2, 3]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert26 : SliceN true stopR stopT (0x3300330000000000330033,4,[0, 2, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert27 : SliceN true stopR stopT (0x33000000330000003300000033,4,[0, 2, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert28 : SliceN true stopR stopT (0x30303030000000003030303,4,[0, 3, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert29 : SliceN true stopR stopT (0x303000003030000030300000303,4,[0, 3, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert30 : SliceN true stopR stopT (0x30003000300030003000300030003,4,[0, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert31 : SliceN true stopR stopT (0x55550000000000005555,4,[1, 2, 3]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert32 : SliceN true stopR stopT (0x5500550000000000550055,4,[1, 2, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert33 : SliceN true stopR stopT (0x55000000550000005500000055,4,[1, 2, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert34 : SliceN true stopR stopT (0x50505050000000005050505,4,[1, 3, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert35 : SliceN true stopR stopT (0x505000005050000050500000505,4,[1, 3, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert36 : SliceN true stopR stopT (0x50005000500050005000500050005,4,[1, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert37 : SliceN true stopR stopT (0x111111110000000011111111,4,[2, 3, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert38 : SliceN true stopR stopT (0x1111000011110000111100001111,4,[2, 3, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert39 : SliceN true stopR stopT (0x110011001100110011001100110011,4,[2, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert40 : SliceN true stopR stopT (0x1010101010101010101010101010101,4,[3, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
def certSlices : List SliceD := [(0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4]),
(0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]),
(0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]),
(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]),
(0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]),
(0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]),
(0xffff000000000000ffff,7,[0, 1, 2, 3]),
(0xff00ff0000000000ff00ff,7,[0, 1, 2, 4]),
(0xff000000ff000000ff000000ff,7,[0, 1, 2, 5]),
(0xf0f0f0f000000000f0f0f0f,7,[0, 1, 3, 4]),
(0xf0f00000f0f00000f0f00000f0f,7,[0, 1, 3, 5]),
(0xf000f000f000f000f000f000f000f,7,[0, 1, 4, 5]),
(0x333333330000000033333333,7,[0, 2, 3, 4]),
(0x3333000033330000333300003333,7,[0, 2, 3, 5]),
(0x330033003300330033003300330033,7,[0, 2, 4, 5]),
(0x3030303030303030303030303030303,7,[0, 3, 4, 5]),
(0x555555550000000055555555,7,[1, 2, 3, 4]),
(0x5555000055550000555500005555,7,[1, 2, 3, 5]),
(0x550055005500550055005500550055,7,[1, 2, 4, 5]),
(0x5050505050505050505050505050505,7,[1, 3, 4, 5]),
(0x11111111111111111111111111111111,7,[2, 3, 4, 5]),
(0xff00000000000000ff,4,[0, 1, 2]),
(0xf0f0000000000000f0f,4,[0, 1, 3]),
(0xf000f00000000000f000f,4,[0, 1, 4]),
(0xf0000000f0000000f0000000f,4,[0, 1, 5]),
(0x33330000000000003333,4,[0, 2, 3]),
(0x3300330000000000330033,4,[0, 2, 4]),
(0x33000000330000003300000033,4,[0, 2, 5]),
(0x30303030000000003030303,4,[0, 3, 4]),
(0x303000003030000030300000303,4,[0, 3, 5]),
(0x30003000300030003000300030003,4,[0, 4, 5]),
(0x55550000000000005555,4,[1, 2, 3]),
(0x5500550000000000550055,4,[1, 2, 4]),
(0x55000000550000005500000055,4,[1, 2, 5]),
(0x50505050000000005050505,4,[1, 3, 4]),
(0x505000005050000050500000505,4,[1, 3, 5]),
(0x50005000500050005000500050005,4,[1, 4, 5]),
(0x111111110000000011111111,4,[2, 3, 4]),
(0x1111000011110000111100001111,4,[2, 3, 5]),
(0x110011001100110011001100110011,4,[2, 4, 5]),
(0x1010101010101010101010101010101,4,[3, 4, 5])]
theorem validSlices : ∀ s ∈ certSlices, SliceN true stopR stopT s := by
  unfold certSlices
  simp only [List.forall_mem_cons]
  exact ⟨sliceCert0,sliceCert1,sliceCert2,sliceCert3,sliceCert4,sliceCert5,sliceCert6,sliceCert7,sliceCert8,sliceCert9,sliceCert10,sliceCert11,sliceCert12,sliceCert13,sliceCert14,sliceCert15,sliceCert16,sliceCert17,sliceCert18,sliceCert19,sliceCert20,sliceCert21,sliceCert22,sliceCert23,sliceCert24,sliceCert25,sliceCert26,sliceCert27,sliceCert28,sliceCert29,sliceCert30,sliceCert31,sliceCert32,sliceCert33,sliceCert34,sliceCert35,sliceCert36,sliceCert37,sliceCert38,sliceCert39,sliceCert40,by simp⟩
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def limb (width : Nat) (blocks : Array Nat) (i : Nat) : Nat :=
    (blocks[i / 32]?.getD 0 >>> (width * (i % 32))) % (1 <<< width)
def certOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | k + 1, n => if n = 1 then [] else
    (n % 4, n / 4 % 16, n / 64 % 16) :: certOps k (n / 1024)
def certCut (n : Nat) : Nat × List (Nat × Nat × Nat) :=
  (n % 64, certOps 6 (n / 64))
def limbCut : Nat → Nat := limb 67 #[0x26893a26902208200000000011344924000000091a2690a78000000000001104b00000000000022092000000000000441280000000000000033000000000000000650029088286892048000000000000000174000000000000002e0018750d2148110420030ea1a20a12648a00000000000000178000000000260992800000000004c1324c000000000000000be00000000000000158000000000000002c80000000000013249000009a24899202880000134491324051400000009a2489922800000000000132500000000000002649800000004d1244c910000000000000822200000000000010445000000000000000a800000000000000130000000000000002280000000000000044,0x26498a42a600001424c90590d0c000000000262992800000491344c9014400000992689220288000000048d134854c00002489a26480a2800004c9344910145000000000000202920052110499134810000a42209926890a0000000000000000630000000000000009c004c5344490590900009c2829920b21220000000000449104a000000000000000b400000000013244d38000000000000002b80000000004c9134b00284a3a62992208a004c9474c5424411400a4262a1264882280000001324c5214f000000000098a64980000000000004052c00000000000080a50000000000000004d000000000000000920000000000000016000000000024091a380134491364851045,0x89a469200000000012444d1c00000000024690a3800004d14548d2142000000000091a42900000134491354850800000000000091a3800000000000123490000000000982468e0000000001104851c000000000000002300000000000010248000000000092220a20000000000000015400000000000088240000000000000004a00000a3a2089a06800000147441434850000002eca1a2481210000000000000006800000a1a048ac84800000000000000019c0000000000000032001425d9434053245000000000098a64920052131509324051000c3a8680a8499228000000000001214b000000000000242940000000000000016c009a248b2a6480a28000000000000004b,0x91a24940000143491354490c000000091a2489a30000048d1649113400000000000892269800001274514344d100000000002269927800000000048d124800000000008a2468e0000143491134490c00000000022480a5d0d284510644d0245002509a26c882248200000000013244d3c00000000024889a50000050d244d5124400000a1a8a89a248800000000000044d3000000000022489a48000050d2444d12440000000000992249c0000000001244c540000028c99260812100000000004c10248000009a2489aa428a0000000001344854000000000000090a400000000000012147000000000091a429200000000012348528000000000000002400000000000000047,0x2908826290264820000000449204415272a0a8e9026480a280000001234c521488ca86a3a0491a208a000000048d314853c00000000026481240000051d3150932450000000000002469600000000000048d2800000000024291a380000001344c9024100000a3a2098a608000000000013448120000024891a0b21a180000000004c523500025081a42a2c208600000000013048d4000a42609224a98a28011340d64c550242000000000000000a60000000000000013c000028e90a8681200000000000001324b0000000000002048c00000004490244150009a2489b24280a200000000000000060000000000099260a400000000000000184000000000000892380000000000011349,0x2429a00509474c53240510009928e98a8480a2000000013244d124f00000000008a2048c000014259315409040000000000000031000000000000102530000000000002049e00001424c9454c5140000284a3262992280000000004c90247000000000099262a00000000001244c5380000000a9e48882700000000004d1214a000000000099242920000137509414490800000000026498a600000000004c5124600000a128c98a24820000000001124c518000026ea0a84992200000000004c91247000000000090a64920000134519214c90c00000008926498a452523505034951040002908826498a0487324e141519204051400000009926289244c938505464810140,0x28c9920484000000050d424090000000000000000290000050d424d52043002488a26092a20800048d1359325441080089a46b264a88210000051d1044d2043000000000000262940000000000004c52400000000000090a30018051d315093245002489ba289822080004e1144913044100000028e882629820c0d4848d41415214500286a122682c42840050d4244d254410800942269028b0821800000000044902540000000000002628c004e1414c94548114009926ea0a8a902280138505424c9014400270a0a8c902648a0052131509354811400a128e98a6480a0001484c5424c9014000264a3a62a12028000000004812144150000028e88262992080000001214811054,0x26b1222090000000000000001040000000000000020000000000049110480000092268992208600001324d1244410c0000268922648821800000014349610400000092268992208800001324d124441100000000a1a2b102000000491344c910450000099268922208a000013449132441140000000a1a0b10a00018750d1050932440029098a8499220893452110499314090668a42209326281200000000000000004200248a3a2089a068200491474411340d0000c3a86882849921d253149d4048d10440029098284992208800001344913244110000000091a2690aa00000001244d132440000000000002208c0000000491344c91400000000000088238000000000001324a,0x24689ac992a2088004c1278c5458410c009824f18a8b08210013844930516104200286bb2488824686005213148d059091400a426291a0b2122001484c526501234400000000009a2208e0000000001344412000002849920b21a2800005093241643440000000000002069e00001474c1424c91000002689226a9022800004d1244d5204400000000008a2068e0000000001344813000002489a2648820000004d1244c9104000000992689222080000000040912441500000000a32209920801425d9434413243000000026498a42a800000000000048544000000000248882300184dd934495104100000bb28692a20840050932595434410c00a1264b2a868822001424c96550d1045,0x8a440a80061d414c9404410000000000020910aa0000051d104553241000000000092220a8000013050d25905000000260a1a2b21200013850546481324300270a0a8c90264880061d34441424c91400000000026890a40000000143456404000000a1264a2a60880000142519304c9100000000002649826000005d3654850441000000028682c828000001424c9454c1140000284a3260992280000000004c9305000000a3a60a12648a000000051543441000000000ab220a1a000000000004d1104600000002caa1a208000000000012444124000000000248882380134491654c9104300000000009a2428e00000000013044120000000000268902800134491654c91040,0x22681a208c00449378814584100000000000268902980148441124d6204100290882249ac4080004e12140d4580500000028e98242812200148441364850341002908826c90a068000000005193040910000028e8822681a0800000011044d0346000000000000264a80048d13419458850000000000026888250000051d104c94340000000026299242a800000005191050d000000000b2c86882100000000004d1204e00000000009a240a4000000059543441080000000a1a8a88200000000153c91104800000002a792220940048d13593254411400c3a64882689220000005d3654c91041000000000092220940000000001244413400c26e4b2a688820800005c96550d1042,0x81a26a2c20860061d104c93449100009a248b2a2099200012344d0651621440000089a06a2c2084004d124459324051000002688122b1920800004d1364850241002489a22c82c648a004d124459058c914009a24880a2a99220000044d035161043000000000000220a800613274412344d0000c264e8824689a08012344d64c95104000000000009a220a2000000054f24441400000000002688828000000000000132470000000000002649000001424c9454c5100000284a3262992200000000004c5014d000000000098a029800605474c1424c9140000286a126488218000051d315093244000009a2489aa42880000000001344853000000000024090a38000044d035161040,0x92246a2a608a00001245193048d140000000a0a8a98208000051d30491234500000000009a240a20000000000004c52000000009a282982100000000004512046000000000090a02a2000000044d458410c000000000000812a000000000000110510000000000002408c0000000000004c118000000000264982680000000004c930510000000000002608e0000000000004c51c00000000026099248000000000451025100000a126c882688000000000013148d30000000000000982780000000000013048000000000090242a20000000001454c10800000000028a9820800000013449132430000000000a1a208000001324510444100000020689a8b082100000451044c91040,0x91a40980000000519315010800000000026298240000050d265012344000000026489a24a800000000012048d30000028e98284992180000001435093245000000000000246a400000000000048d44000000000000002800000000004d13041000009a2489aa408600000000010240518009c20498a8b082100000000000012054000000000000260a20000000000000014400002629828b08218000000000491305000000000009a2028e000000054f244052800000000026091a4800000000048d30510000000268a0a60820000000001234c140000000000269082680000000004c93148000000000098a46920052131491254c10c000000000248982600000001464c53042,0x892208c00001474494044100000000098a608824800000014644112410000099262a2c20860000147441324c50c00a4246a0a0a90a0001324c50651621420027089260a2c208a000000054f1448138000000000248982680000001414d5404100000000009a42094004a14345115481000091a26b262a9021001184c903516104500000a3a2099226860000000000004853c00000000022480a8801484c52650123430029089a0ca120280004c5074c94584108009c22481a8b08218000051d1044d0241000000000090a40a80048d474c5255010c000000000262982300000000004c930470026893a829aa40860052131491354811000a42629328099228000050d234954044,0x29103a4291a26820000000001044851800002488a20a90a0000000000000132510000000000a1a80800000142519304c90c000000089a0688280000044d035161045000000028c882268600421374853449100009a2488326a90a00000045124495104000000002c992a2082000012445125441000000000a2a26882180000001615153042000000000000260a00000000001348414c000000000269082900000000004d1204700302a3a60a1264860000000000004413000002e9b024a8a20801315d3364090140002629ba04a2c02820048537881458050c000028e8826b1021000000000049210540025089a8d1022080004a113481458410400000000024080aa00000000004c10153,0x2648c00521104c93148100009928e88262902000148441244d521400026898a2482c848800509474c131485140098a8e9828490a2801484c1424c52145000000000098a42980000000001214051e729222e822268122801434911349510450000000000902208e000000048d134493800002869222690a2800000000044d214c000000000089a42a00000143491134851000000000028681a2000000000050d044500000000000028680000000045104441000000000892048823000004494688110400000089204a2c20820000000000004c14c00000000028a88208013149d468c101400026293a60a2c20820000000000004c1480091a268328b10a10012344d468152141,0x99224920000137491144490c0000000a9e2881240000000000409104a002849ba209a2248000000000012344d2800000000024889a7800000000049113480000000286a2a4086000000050d354810800992268128b082044d0251e32516104000000a3a6090a028800521104c9134090400a422099226812000000000004d2104700000a3a20a12648000001424c9159010000002849920b20a00000000135891104798a40a3c64a2c208331481478c94584102729228e882629020ce52451d104c52040a1a909026c882428800509314850590d1400a126290a0b21a2001484c1424c52144000009228689a4288000011350d24485100000248a1a2690a28000044d434912145,0x29098a6492a2084004c931481458410c009a2848926a8822001344c512515204500268a126c8822488004d1474813144914000000000260992380000001455093043000000000098264940000000001344812c0000286a126290a28000000000001204700000000009a420920000000001134c94c000000000264892900000000004d12046000000000000240920000000491434810c0000000000009024000000014348d20420000000000982208c0000000001348412000000000026890a5800000000048d314b000000000081220a20050d2444d2544110000000000262982380000000004c52150000000000089a428c00000000012144d180000000002269926000004dd244511344,0x90220a8004c913409458410c0000000a322081a0800004c9125161043002869222682a42800000000000004855000000000026490a880000001464c13242000000028c98284860000000001324c1280000000a9e488827800000000000130490000000280a1264800000000501434c90400a1a4889a4a88200013244d02516104500000a3a20992248600509474c1314851000a1a8e8926088200000051d1044930410000000000982648c00000000013148d1c0089a8e9824890a28014349d4044d2144002909824889a428b3148147841458c90c00000009ac48882a001484c9414c1104000000a3a209926083424c507485454c116929828498a0a90a2801484c5324162142,0xa1a4889a02880000143491134091400000000000081a8000000012444d2140000000026889a42820000000000004492400000009a24690a1000000000048d124e00268922268122080004913444d0244100009a24889a04882280000000004c5214600240a1a8498a208a0050d424c5204411400000000024689a7800000013449102440000000268922068a00000000012344d50000000000000812600000000004d2104e000000000092264800000000001344c9040000228a1a0688200000050d1440d1040000000000081a208c005223244d0244100000000000269082580000000004d1104b002910822681264820044d32409458410c0099226a34408820001134c9025161041,0x922068e000000000113449400000268a1226892280000000004c5324a00000000009924296004d142459034491000002869322091a0801424d11640d12410000000000992428e0000000000004852400000000022891a7000004d14249513430000000000992429400000000000048d20000000000246812580000000000010349000000000091a62a600001474411348100000028e8824889a0001435d924405134400000a1a2482c8486000014744132449000000268a120b18a1800000000048d02470000089a8692202880050d17491324051400000000022480a500138449434810140000000000091a629e000012450d134091400a1a8e882629020001484412444d0240,0x81a648e0000000000004091c00000000000088278014349d144c90144000009ba42a1a048000001474c12340900000028e9824881210000050564c1512410000089a60a2c208800000000010444918000000000000902780000001435150242000000000098240a400000000013048d2800000000026890250000000000451234800000000009222692000000000113485380000286a2a6081210000050d244c10242000000000099240960000000001124c9400000000a1a4881210000000000001034600000000008a2068000000000000044d1c000000000246812680000000004c91251000009a2849aa248a00000004990448d0000000000020491a300000411434d52041,0x9a28c90a0488000012450d134050000002869222680a000000001464411341002489a2ca8122686004d1245950244d0c00000000020490aa001134d124455204400268922268aa4088000013448d1588108000026891a4a882100000000004850254000009226889a048600001244d1314091000002049a24898a2000004d12444d0243000009a24898a04880000134491354411400000000024681250000049146441134000286bb22881246880000000000004092400002689224a88218013451d104951340002709222ca02268800000000012344924000000000246892900000001244d10244000000000091a04a40000000001234091800000009b248812080000001434913243,0x28682c82840000000001034c94800000000026481a90000000143515104200000002689aa208200000004d13544108000028e8826b10200000049e315160141000009a282902028000001314814584108000024698a8b08218000000146441204100228a1a048aa6488000012440d158c90400002489b24281a08014345116416324500228a1a2c82c648a0050d14409154c9100000262a342090210000000000001125400000a3a209aa248000001474413244d000000264a322089a00000050d31416424200286bb2288124686000013750905905080000248a326281220000049103515314500286ba24c882648a00000000013244d1c000028e98a4881220000051d314910345,0x268a3a248aa06880000000001324492800002869322891a28000000000001124a000009ba249a2048000521324d9014850400000000020491a8000000000000123460000000000892469800000000010248d2400000000020490a3800000000048d13480000000000992408c00000000000040d2000000000000099290000000000411434500000000009a20682000014259315481100000000a326089a1000000000044d0146000000028c882268000000000010144d1800000000024698aa000000000040d324c000000000091a0498000000000123481400000000b2a2881a08000000000449014e0000091a86a2a048800000004d1354410000000000020491a60000050d4548d0244,0x9a28c902468a004d1474852540d0c00000000000091a7800004d1454d52045000009a28a91a408a00000000012440d3000000000000081a3800000000048d30520000000000922069a00000004d9104d10000002869320891a20000051d324d51041000000000080a249a0000000001234c12400000000026481a5000000013240d204b00000000009a224a600000000012444d48000028e98a088821000000000044d014c00000a1a489aa408a0000000001034412000000000026481a700000001434111042000000000000224900000000001014494400a42629320891a1801484c526411234400000a1a8c88264800000000001044852000002ec81a429a200000050d264512344,0x2868a206840000000000004510400000000000081a880000000000010440000000000000206980000000001354110400000000000091a80000000143491234500000a1a4c822468600000000012144118009c2429828b082100000001464c113400000000000002049a004e1214c1458411400000000026281a400000001414d5044100000002c98aa04820048d135931540908000000000260812a00000000004c132480000000000002028e004c50748d458410800000000024080a30010848d315161042000000000098240a600000000013048d34000000000268902680000000004d1025000000000009a2028c00000004c5354110000000000026281a300000000004812350,0x268a3a409aa20880000134595244410c000026889a0b2122800004d1134164244000009a28c9022688004d1474413148104009a28e8826290200013451d214c5024300268a3a209922482004d14744132449000000268b2a46882100134491364412044002689222690220880000134491134811000000009228689a20000044d464c90243000008a28c992048800001145193240d14000028e9922681218000051d32451024400000a3a648a2068a00000000012344d34000026e922268121800000012450d13450000000000002049400001274113244d0c000024e822289922000000014348d104200000002869222086000000050d2444d140000000a1a4889a200000000000011350,0xa3a648a20686000017650d2140d1000002eca1a428222800005d943441234200000bb2868824886000012444d0590d14000024889a0b21a20000051d3049113440000091a62a2c2080004c5478c945841000000000a326089220000051d1048d314100000a3a2091a62800050d24499058c5100000000a322091a000000001044d621400000081a68a2a42840000000411258c50000002069a28a90a1800000010445632400000081a68a2a4288000000000134485180000268a324281a1000004d1464850343000009a28c90a0688000013459524441140000286b2a0690a10000000134416214100226a3c64a2c20820044d478c94584100009c248a322089a080138491464411340,0x220a000000004854544100000000093202822000000001214110140000000000092206a400000004514340d1000000000026890a8800000000040d024c00000002868a2068800000000000044d3400000000000080a600000000000010250000000022682206800000134491034091000000000026890a4800000000000113460000000000892629200000000000044d440000000002488820800000014345103430000000246a1a20840000000491434410c00002629028b082000000001464c1104400000a3a2098a4082000014744131481000000000a3220922000000001044d64240000000020892c8680000010359543485100000208b2a8690a28000051d324510342,0x9926096000000000134441300000000a9e4888268000000143451304500000000009a2209200001415932540508000000090a8a80a00000041d32516104200000a3a649aa208600000000013244d4400000000026489a680000000000010146000000000092260920000000001248c11c0000286a126a882180000000004d1214d00000002a792220a80000132593254410800000000000080a68000050d244d51042000000026c90a088000000000000048140000000000264982980000000004c10247000000000099204980000000001024c930000000000226882600000000004c9304e00000a1a289aa20860000000000004413400000000020680a880000001434d51043,0x8a28c992028000001474c91440500000024689a8b08210014844934495304300000a3a2692c6082000014744d3548104009a28e8924a98218013449126456304400000000009a204a2000013244d458410c000026881a8a90a20000051d214d13045000009a2489aa20840000134509354410c0000268a3242982280000001034d14144000000000082242800000000001214110000000009922690aa00000001644d5104100000000008a206900000000001014853400000000022090a8800005c936441434000286ba24c88264860000174d89154110400000009a22881a1800000000048d03530000000268a0a068800000004d14544114000000000246982a00000000004c90354,0x2a792220a40000174d8135485080000000b028a90a08000045d4348101400000098a40a2c208200001134814584108000022e9928b082180000001404c910440000000000992069800000000013240d240000206a3264a0a20000051d32505034400000a3a64a2a208a00001234c545841100000268a124a88200000048d315161045000000028c88246860049143499354410c0000000a966888238000050d62cd51042000000000091a40a20050d24499158c110000000000246902680143491264d51043002869224c8ac608a0000000000004494c0000000000008927800004d162515104500226a3c64a2c20840044d478c9458410c0089a8f0828b19210011351e105163243,0x9bc40a2c028400001478053588108000024698a8b082100000491464c5014000000a3a629220280000013148d45841080000000a322098a0800004dd2151610430000000248a0a028000000000013140524000000091a8b0821800004d1424152140000009920ca2c4284000012450d254c10c00000009a24b182080000001344d52041002629ba04a2c208400505474da0244100009228e98a4a98218000050534496304100000a0a689aa408200000000013048d440089a0ea346480a00014884113415324100248a1a4c8ac60880040d32593054850400000000026080a780184c1d214c9034100000a1a4892a608600000004c5458410c000000000246812780000000005152141,0xa12c98aa40840000164d09154810800000000026281a600000001045153145000000000099206a600000005193140d100000000a3262822280000000004d120540000000000002269400000000011450904000000000208a1200000000000001314c000000028c99208800000000000004c93400000000000098a6800000000050914410000000242a2c20860000000000004414c00000000028482200000000000001304d000000000000262a0000000050910411000000286a322081a1800004492051610440000000268a02068000000004514340d0c0000262a346480a0000004c523516104100000a3c6498a028000001478413148d040000264a34408820000004c9205160141,0x226a40000000001244410c0000000002488a228000000000001135300000000009222888000000000114411080000000b264a88210000000164c9510430000000000a2a208000000004514340d08000000098a408820000000000048510490000000240a2c208400000000014044110000028498a0a90a0000004c5065162141000000000081a62a2000012459325441080000248b264a8821800000014251510400000000284a2a20820000000001034c530000028498a4a8820000004c564c9510410000098a40a2c208a0000000519104850c00002e4a326281a2000005c9464c50445000008a28c992068400000000013140d44000000081a8a98a200000000004c9024f,0x92226a80000134515234090800002689226a812100000001454510341000000000092226a600000004d11440d0400000000000089a40000000000491134d000009a2489aa24840000000001234852c0000000a322090a0000005d92440d1343000000024882c868200000000011340d24000000089a4881a1000000012440d1342000000000089a068e000000044d2440d0c00000009220689a180000001144910344000000000091a26a200000004512440d140000286a322098a00000000000485234c00000a1a4c8222486000013449931409040000000002268926000000012444d0342000000024889a068600000004911440d1000000009222881a280000000004911042,0xa0ac98aa048400000004c1314052400002429028b08218000000000485014c000000028a8a2068a00000000011340d180000000a022681a00000000000491134e000009a2489aa428000001345092540d10000000000264812680000000004911351000000000092206a600000000013048d300000268a322081a200000000004d1104d00000002688a2068a0000000001144094c000000000268892900000000004c1024d000000000000204a20000000001134852400000000024881a8800004d1244d5024400000000000026098000013451530409100000268922608122000000000048d204e000000000081a46a000000000010348d1800000000024681a3000000000040d134d,0x98240980000000001304814000000009a26a8821800000000048d035400000002688a2608800000000000044d3800000000000089a7800000000044d034c00000002088ac848000000000010344d240000262b262a8120800000000040d2351000009ba08a12268600000000000048540000022e91a8b0821000004dd044d52142000009ba08922268400000005192141100000000000264982780000000004c1024c000000000092260a2000014351513441080000286a0a06882100000000004c9024e0000000000002069a00000004d90444d0c000000091a0690290000000000001234c000009a28a91a048800000000000048d3800000009222889208000000000001034a,0x2a382264a80000000000000010c009228e8826b10208012451d104d6204000268a3a209aa4282004d147441354850000000000026280a3000004d1464413141000009a28c88262800000000001014c518000000000228992a001184c9025161042002909928c8826088004c9305932544110009c24089a8b0822000004d1454d51043000009a28c88260880000000001104c1400000286a0a6a80a20000050d414d5014300000000008826098004d176491104c11000000009a24a88208012850d414c50243000009a2489822088004c931409458410800002849a26a8820801484c5244c1204498a04a3c64a2c20840048d1348145841100000000002469029000004d1244c12044,0x26892220860000000001258410000000009226888220000000000456204000000002489a2208a00000004d1244411400000000020b10a0000005d934495104300309bb2468aa088200001764d120451100000268a322090a0800004d146441214000000bb268882488600001474c1244411000000009a24a8821000000000048d13530000000268922208800000000011340d5000002269028b00a08000045d32516014300000a3a648a2608800001324c5458410800992608328b10a20000000153c911047000009a28c90a6088004c5478c9458410800002689224a88200000048d64c9510420000091a26a2c2088004d124499354410c00a422090a6b212080148441214d64240,0x248a2a208a0000000491454411000000009a248882080000001244d11040000000026892220800000104595144c90400002ec8a2648220800000000044d034b00000a3a6d10a08880000176411358851400000000026908280000000123516104200000922689aa20840000000491358410400000009226a882080000000004d21046000009a26c92c2086000010451935485040000208b2a6890a100000411654d1214300000822ca9a2428800001764d12544100000028e9b2428220800005d934485044200000bb26890a088600001764d1214111000002ec9a24a88228000000153c91105100000bb26892a208400001344d9254410800002689b24a882080000001244d11043,0xa12c992a02860000000001044851c0000000b2a0690a000000001654112144000000000082c6480000000000104485300000000ab24282220000050d6548d104000000ba6ca91a208200001325932544110000024f18a8b08218000049e315161042000008ba64a2c2084000013459524441040000286b2a4888210000051d32416414500000a3a6482c828800001474c9454411000002ec9a220922080000000004d51040000000022882c848a0000000451059091000002e9b2a2482210000000145491104200000002ca9222086000000051920451100000000000009026000000016548d104000000a12c992a208a000014259325441100000000ab220922100000000004951040,0xa3a64a2a208600001764d1215011400000000026b10a000000001045152142000000000092c62800000000411454850c00000000026281a5800000000045632400000000208a2a428800000000013140d3800000000026a90a00000050964c951043000000028c90a0884000000000134441480000000a3242822180000000004d11053000000028c90a088800000005952444114000000000268882a0000000000001214c000000000081a26960000174d95034850400000000024280a78000000121416434000000bb20899228820000176451324110c00000000026890a780000000004911050000000000082264a00000000519024510c0000000a32048a210000050964c950144,0xa3a209aa4280000000000121405180000000b2e02a1a180000000005153044000000028c88242820000000001014851800002648328b10a0000000014644132400000000264a2a20800000000001048853000000000020890a80000000153c11214800000002cb1a220860000132593254410c0000264b264a8822800005d92344143400000000000002209c0000000000004414800c26e6b2a48882080184dc96544d044100000b9aca92220800000173595244411400002ec9a2428220800005d9414c90140000008ba64a2c2082000000050135485100000208b2a6890a08000000110516324000000002209ac848000000004412590d00000028e9928a88208000051d325151042,0x2289ac808000000005193045100000024889a6aa0210000044d364964043000008a26c92c8088000000051a10485080000284b264a88208000000000492104a00000992c992a20820000174c99104c90000002e9932209920800004c964c95104000000bae4c88286840061375519104c90400002eaa322099228000000114515324400000ba26c90a068400001744d9104911400000008a28a992280000001434911042000000028c9922086000000051932451140000000a32648a2200000000004921048000000028c98a488800000005193149114000000090a8b0820000004de20516014000000a3a209ac4082000013748545841000000000a326090a20000051d104d52141,0x91a609c0000000001048c92c000000000268812580000000004913052000000000092206920000000001344854800000000026081258000000000001204000000000009a204a60000000001244051c000000000228822000000000004d1125000000000009a204a400000004d10440d1000000000024898a78000000000491315300000000009a2409200000000000048d50000000000228822080000000004510443000000028690a028000000004854584104000000090a8b0821000000013251610430000000000a02648800001764412350d000000286b2a2091a0000004c906516214500000bb220a2c6482000013241945885100000000a342090a08000044d244d54042,0x81a629c0000000000004c53800000000020698a78000000000001314f000000028692a2080000000044d2044100000000000000982500000000004811050000000000098a428000000000000048144000000000240882480000001205161043000000020c9aa428000000005152444104000000000282822280000000004c1104d000000000082442a20000000001244414800000000024091a48000000000412314600000000009a2049a00000000010488540000000000248882600000001424111043000000024882220840000000001144811c00002249028b08228000000000412315100000a3a62a0206880000000001314c134000000000248982980000001345010344,0x2a7922209600001174c94584110000024ea1a4a88200000045d325161045000000028c88264860000000000004854c00000000022681a700000000004c5034f0000000248a2a20840000000001134c1480000000a128a882180000000004c53053000000028c90a08820000000001045051000000000000090a00000050964c951042000000026c92a20800000000001414111000000000028a882280000000000013054000000000000206a6000000000104505140000000a32408a20800000012151610450000000000002248c0000000001344413c0000000a9e28812880000000004510250000000028c90a808a00000000013244100000000000268882700000001464811442,0xa3c0c90a648200000004c9054850000000000024280a8000000010651621420000000208a2a4282000000048545841100000000002428828000004c90651621430000083a6c90a868000001434193548500000020eb266a90a0800000013249510400000000000a2a20860000000001348415000002e9b126a88208000000000001205300000b9a8c90a08820000174d8525411080000000b126a88200000000000441034c00000002c4a2a208a00001478193244100000020e9928b00a0800004de20516014300000002809ac428a0000000459324050000000000022480a4800000011251610430000000000a024288000012750d054850000002648328b10a08000048d065162142,0x2249bc04a2c2084004e1214c145841100090a6f1028b082200000000004d2105100000a128a92a208000001314c14584110000000000260902a001324c5065162143000000000098220a20000143515354410c0000286a126488210018750d21501304400000a1a8a9aa4288000014351535441080000000a1a80982200000000004951042000000000092a2086000000000120441100000000000008821800000000000110440000000000902208c000000051a204410000000009028b00a08000000000485014000000000000028088000012751a1340500000024e89a8b00a0800004de1251601430000000000002609c0000000001458410c0000264a340a90a08000051e064d62142,0x98a40a2c208800449478c9458410800002469828b082200134501364961044000009a28092a208800000005192544104000000099260902980000001324c1204f00000a1a8a982208800000000012440d3c000000000226982600000491414c50343000000000089a60a6000000051525441080000000002269827800000000000113540000000248a2a208600000004914044110000028ab264a88208000000000485104c00000a2ac992a208400000000010448524000028ab264a882280000459064c910400000089204a2c20840048d1341945885040091a26b264a882080000000004c5305100000a3a62a0260880000000001314c140000000000262982600000515424951040,0x8a28088000000000125441040000000a3264882000000001424c91042000000028a9aa42880000137881458411000000009aa4a8820000000012051610440000098a0ca2c4286000000051a2544108000028f1b24a8820800004c14689510440000000000922209600001474d9254410c000028e9b2408822000004dd20516104400000a3a6092a20880000145593254410c000000000248882980000001354951041000000026a92a20840000000001244413c00000009b24a88218000000136481104400000a02c992a208800000004d9254410800000000024088298000000000481104f000000026a90220880000132449458410800a0a629b24b20218000051d325011044,0x26c92a208800000005192544108000000000226982a0000051564c951044000000026498240a80000143515354411000000009aa4a88220000000136495104100000ba64c8aa08820000000001144091c00002e99322a8221000000000049510440000000224a2c2084000012341945885040000246b264a88208000049164c951040000000000000264a60000000519215011000000000000099278000041d325161041000009bc04a2c208400001474c92544100000026e90a8b08220000000162515104300000bb26890a808800001345191048d040000268a322091a0000000013451510420000000268a2a208600000004d1404851000000009228a882080000000000010354,0x28c9aa208600000004850590d14000000090a0b21a20000000146895104300000a3c6c92a2080000013791a2544110000020ea326a90a00000041d468d5214300000a3c6c92a208a00001478d92544108000028f1b24a88218000000135891104d000000026b12220a200613374991541100000028e9b24a8822001371d3264554044000008388c9aa4286005e3470d92544110000028e9b24a8820001731d3264550440003099ba4c8aa088200000004d6244412c000028ca344a8822000005d3264550440000000000082c428a00000000010588510000000000269082780000001468951044000000026b122209400000004d6244414c00000009ac4888278000051e364951044,0x22681a20980000145501054851000000009922a812180000001324550242000000026a82a42880000000001324410c00000000026488220000051e32516104200000a3a209ac48820000147441358910000000008ac08992a000000013581121540000000264a2c2088000000051a254410400000000028b08220000041d468d52141000000020ca2c4286000010751a3548500000028f0326a90a08000051e064d62143000009ba4ca2a208000000000010488534000024e8b28b1822000004d146495104100000a3a6d12a2084000012451935841100000000a344a88228000051e32516104100000a3c64a2c208000001374914544104000026e9228a882000000001464d51042,0x26b0a204a80000147995214c11000000009326a882100000001654c9104100000ba6ca882488400000000011440924000000000228812a00000001564c12144000000000089a609c00000000011440d5000000000022081a480000000004c9034d000000000082246900000000001148812000000000020910a4000000000041221530000000000824429e0000000491454410000000000026890aa0000000165c414343000000000082264a80000000595104c9000000284a342a81218000050946855024200000a2a8d02a42880000000001204413400000000022881a48000000000411234c000000000091a06980000000595104c904000000098a608827000000012340d204c,0xba66c92a208200001474d92544108000028cb264a882100000515434d5104300000a2a869aa2088000014550d35441140000286a2a6a882280000001354951043000000026a92a208a000014651a2544108000028ca344a88208000051946895104500000ba64c8aa088a0000000001254411400000000000088228000000132516104200000bb220a2c64880000000001348854000000000026910a600000501464d62144000000026b0a204900000130419458851000002eb93220a1a080000001434951041000000028692a20840000000001344854c0000000a326488220000000165c414341000000028d12a208000000005964344110000028f1326a88210000051e654c91041,0x9bc8d12a2086000013791a2544114000020ea346a90a10000041d468d52144000000026b122209c00000004d62444148000028e1b24a88200000041c464d52141000008388c9aa428400001071193548510000028e9b24a88228000000000491104e0029113a2c82a6880004e227459054d100000026e9322a82200000041c464d5214000000a3a6c92a2082000014651a254410c00b98e99322a82210000000000496104200000000008ac4084000000000105885080000000a326a90a280000001464d52144002911ba4c8aa088000000004d6144094400000009ac2881290000000136495104500000ba64c8aa0886000011751932405000000286a324a88210000050d364951040,0x9aa428a00000000013548510000028f1928b08218000051e10516324100000a3c20a2c64840000147841458c90c00000009928b082280000001264414340000000026b12220a000000000014584114000028f0326b10a20000051e368951045000008ba0ca2c64820000117419458c908000022e8328b19218000041d468d52145000000026b022429000000004194588510000028e932209a2080000491464d61043000009228c9ac208a000013751a2544108000026ea344a882080000001058d12154000008ba0ca2a64800000000001248412c00002e99b24a8820001731d326455044100000b808c9aa4288000000051932441040000000a32648821000004de468951042,0x982209e0000174c19214c1040000000a326b08218000000110515324000309baa2c822648200001754991050d0000000009928b082080000001325161040000009228c9ac208400000004d624441180000000a326488228000000165c41434400000002cb882868a0000107593354850000002eb93220a1a28000000164c95104000000002cb21a208000000005964344104000028f32a6488210000051e654c9104300000a3cc09aa428a000014798135485100000000ab22099208000000156441324200000002ac8826486000000058135485140000000b1a4a882000000001604d521440000000000002429c00000000013244104000000000264882100000000000012152,0xbaa8d192208200001764c945841000000000002209920000005d910516324000000002ac99220800000000001458410800000000000088200000000106485434000000a3c0c9ac42800000000001344813c0000000a1a0a90a000000001065162141000000020ca2c4280000000051a0548504000020e8b28b19200000041d468553241000000026b0a2409000001478193588514000028f0b20a992080000001164153240000000020ca2c428a0000117419458c900000026e8328b10a1000004dd065162141000000026c82a42800000000001054850000000000028b08200000045d468c9014000000a3c208aa6482000013041945885000000260b260a90a0800005d3064d62142,0x93a2c82c8688000000059643441140000268a320b10a200000001654c9104000000002ac88264800000000001148813c00000000022910270000000000451034c000000000090a209c0000000001048c9400000000002091926000000000040d204c00000000008a2068c0000000001348813400000000026880a48000000135891014a00000000008a460980000000001148c12400000000020918a80000000000412314c000000000081a209800000000010448d240000000002088923800000000049230500000000000824628e0000000000004851400000000000090a20000000000001104100000000000022084000000000145841040000000a3464882000000001468413241,0x8826482000000000143441080000000002868821800000000050d21450000000000a1a42880000000596434410c00000000020919278000051e064d62141]
def certCutCodes : List Nat := (List.range 2056).map limbCut
def certCuts := certCutCodes.map certCut
def limbSep : Nat → Nat := limb 13 #[0x814103042610a2052032048224806202a01481410a022424441808902850300914092046030203810c08810a106041840c40a206,0x40308450582232110828048421202c0260070062181050824209084888842501420b404480e406088902420a4284180830417030,0x806c06904242608a0884128411809909d046827401a01d04a80541520260390128038484022423209900d044022412008504c424,0x91841e01c00a043821800600c40680480281180130096032230018102c12a00600c00a105080e207103400a80b212802600a207,0x409c0b083409908b1055069034046822c23283221484541530151140260114218049889414a42a09202302181280490288832113,0x9802c006803201880e0054029016009e07010b11304c423502380b10cc864132218843903842c418805803801541c08d0162829,0x87021611382e4034019]
def certSepCodes : List Nat := (List.range 198).map limbSep
def certSeps : List (Nat × Nat) := certSepCodes.map fun v => (v % 128,v / 128)
def certSwaps : Nat → Nat → List Nat
  | 0,_ => []
  | k+1,n => if n = 1 then [] else n % 8 :: certSwaps k (n / 8)
def limbPerm : Nat → Nat := limb 46 #[0xa3000000000051000000004b8c0000000025c00000000098c0000000004b0000000001300000000000900000014d4680000000a6a3000000029c68000000014d400000000538c0000000029c00000002d468000000016a30000000054680000000029a000000000a8c00000000053000000005c68000000002d4000000000c680000000005a0000000001500000000000a000000000b8c0000000005c00000000018c0000000000b00000000003000000000001,0x1463440000000a2d1000000028c680000000145a00000012e3440000000968c000000026344000000012d1000000004a3000000000251000000025c68000000012d4000000004c680000000025a0000000009500000000004a000000a6a3440000005346300000014e3440000000a68c000000028b8c0000000145c00000016a3440000000b46300000002a344000000014d100000000518c0000000028b00000002e3440000000168c000000006344000000002d1,0x28b463440000145a31a00000516a3440000028b463000000a2d468000000516a3000004b463440000025a31a0000009463440000004a2d1000000128c680000000945a00000096a3440000004b46300000012a344000000094d100000002518c0000000128b00000012d468000000096a30000000254680000000129a000000004a8c000000002530000053463440000029a31a000000a2e3440000005168c000000145c680000000a2d4000000b463440000005a31a,0x8500000000004200000000438c0000000021c00000000088c0000000004300000000011000000000008000128b463440000945a31a00002516a3440000128b463000004a2d468000002516a30000253463440000129a31a000004a2e3440000025168c000000945c680000004a2d4000004a6a3440000025346300000094e3440000004a68c000000128b8c0000000945c00000094d4680000004a6a3000000129c68000000094d400000002538c0000000129c,0x151a200000000a68800000002888c00000001443000000171a200000000b444000000031a20000000016880000000051100000000028800000002438c0000000121c00000000488c000000002430000000009100000000004800000084d468000000426a3000000109c68000000084d400000002138c0000000109c00000010d468000000086a30000000214680000000109a00000000428c00000000213000000021c68000000010d40000000044680000000021a,0x29a31a20000014d111a000005171a200000028b444000000a21c68000000510d4000005a31a20000002d111a000000a31a20000000516880000001444680000000a21a000000971a200000004b444000000131a200000000968800000002511000000001288000000121c68000000090d40000000244680000000121a00000000485000000000242000005351a200000029a223000000a71a200000005344400000014438c0000000a21c000000b51a200000005a223,0x94438c0000004a21c00000484d468000002426a3000000909c68000000484d400000012138c0000000909c000145a31a200000a2d111a000028b51a200000145a22300000510d468000002886a3000025a31a20000012d111a000004a31a20000002516880000009444680000004a21a000004b51a200000025a223000000951a200000004a68800000012888c0000000944300000090d468000000486a30000001214680000000909a00000002428c00000001213,0x10a344000000084d100000002118c0000000108b00000010e3440000000868c000000022344000000010d100000000423000000000211000000020b8c0000000105c00000000418c0000000020b00000000083000000000041000945a31a200004a2d111a000128b51a200000945a22300002510d468000012886a3000129a31a20000094d111a000025171a200000128b444000004a21c68000002510d4000025351a200000129a223000004a71a2000000253444,0x21351a200000109a223000004271a200000021344400000084438c0000004221c000004351a200000021a223000000851a200000004268800000010888c00000008443000000871a2000000043444000000111a20000000086880000000211100000000108800000010438c0000000821c00000002088c000000010430000000041100000000020800000426a3440000021346300000084e3440000004268c000000108b8c0000000845c00000086a34400000043463,0x90888c0000004844300000486a3440000024346300000090a344000000484d100000012118c0000000908b00014d111a200000a6888d1000028871a200000144344400000510e3440000028868c00002d111a20000016888d1000005111a2000000288688000000a22344000000510d1000004871a2000000243444000000911a20000000486880000001211100000000908800000090e3440000004868c000000122344000000090d100000002423000000001211,0x128871a200000944344400002510e3440000128868c000121351a200000909a223000024271a200000121344400000484438c0000024221c00002426a3440000121346300000484e3440000024268c000000908b8c0000004845c000a2d111a20000516888d1000144351a200000a21a22300002886a3440000144346300012d111a20000096888d1000025111a2000001288688000004a22344000002510d1000024351a200000121a223000004851a2000000242688,0x213463440000109a31a00000422e3440000021168c000000845c68000000422d40000043463440000021a31a000000846344000000422d1000000108c680000000845a00000082e3440000004168c000000106344000000082d1000000020a3000000001051000000105c68000000082d4000000020c680000000105a0000000041500000000020a004a2d111a20002516888d1000944351a200004a21a22300012886a3440000944346300094d111a200004a6888d1,0x8211100000004108800000410e3440000020868c000000822344000000410d100000010423000000008211000109a31a20000084d111a000021171a200000108b444000004221c68000002110d4000021a31a20000010d111a000004231a20000002116880000008444680000004221a000004171a200000020b444000000831a200000004168800000010511000000008288000000821c68000000410d40000001044680000000821a00000002085000000001042,0x121111a2000009088688000024222344000012110d1000121a31a20000090d111a000024231a20000012116880000048444680000024221a0000243463440000121a31a000004846344000002422d1000000908c680000004845a00084d111a20000426888d1000108871a200000844344400002110e3440000108868c00010d111a20000086888d1000021111a2000001088688000004222344000002110d1000020871a2000001043444000004111a2000000208688,0x2510d111a20012886888d1004a21a31a20002510d111a0009443463440004a21a31a00484d111a20002426888d1000908871a200004844344400012110e3440000908868c000909a31a20000484d111a000121171a200000908b444000024221c68000012110d40001213463440000909a31a00002422e3440000121168c000004845c68000002422d400510d111a20002886888d1000a21a31a20000510d111a0001443463440000a21a31a00090d111a20000486888d1,0x82888c0000004144300000410d468000002086a30000008214680000004109a00000010428c00000008213000108b463440000845a31a00002116a3440000108b46300000422d468000002116a3000020b463440000105a31a0000041463440000020a2d1000000828c680000004145a00000416a3440000020b46300000082a344000000414d100000010518c0000000828b00000082d468000000416a30000001054680000000829a000000020a8c00000001053,0x105111a2000008288688000020a22344000010510d1000104351a200000821a223000020851a200000104268800000410888c0000020844300002086a3440000104346300000410a344000002084d100000082118c0000004108b000845a31a20000422d111a000108b51a200000845a22300002110d468000010886a3000105a31a20000082d111a000020a31a20000010516880000041444680000020a21a000020b51a200000105a223000004151a200000020a688,0x2110d111a20010886888d1004221a31a20002110d111a0008443463440004221a31a00410d111a20002086888d1000821111a2000041088688000104222344000082110d1000821a31a20000410d111a000104231a20000082116880000208444680000104221a0001043463440000821a31a000020846344000010422d1000004108c680000020845a00422d111a20002116888d1000844351a200004221a22300010886a3440000844346300082d111a20000416888d1,0x828b8c0000004145c00000414d4680000020a6a3000000829c68000000414d400000010538c0000000829c12110d111a20090886888d1024221a31a20012110d111a0048443463440024221a31a02422d111a20012116888d1004844351a200024221a22300090886a34400048443463004845a31a20002422d111a000908b51a200004845a22300012110d468000090886a3000908b463440004845a31a00012116a3440000908b46300002422d468000012116a3,0x105171a200000828b444000020a21c68000010510d4000105351a200000829a223000020a71a200000105344400000414438c0000020a21c00002084d468000010426a3000004109c68000002084d400000082138c0000004109c000828b463440004145a31a00010516a3440000828b463000020a2d468000010516a30001053463440000829a31a000020a2e3440000105168c000004145c680000020a2d4000020a6a3440000105346300000414e3440000020a68c,0x20a2d111a20010516888d1004144351a200020a21a22300082886a3440004144346300414d111a200020a6888d1000828871a200004144344400010510e3440000828868c000821351a200004109a223000104271a200000821344400002084438c0000104221c00010426a3440000821346300002084e3440000104268c000004108b8c0000020845c004145a31a200020a2d111a000828b51a200004145a22300010510d468000082886a3000829a31a20000414d111a,0x82110d468000410886a3004108b463440020845a31a00082116a3440004108b46300010422d468000082116a310510d111a20082886888d1020a21a31a20010510d111a0041443463440020a21a31a02084d111a20010426888d1004108871a200020844344400082110e3440004108868c004109a31a20002084d111a000821171a200004108b444000104221c68000082110d40008213463440004109a31a00010422e3440000821168c000020845c68000010422d4,0x82110d111a20410886888d1104221a31a20082110d111a0208443463440104221a31a10422d111a20082116888d1020844351a200104221a22300410886a34400208443463020845a31a20010422d111a004108b51a200020845a223]
def certPermCodes : List Nat := (List.range 720).map limbPerm
def certPerms := certPermCodes.map (certSwaps 15)
def certTabs : Tabs := (certCuts.map (mkCut true certSlices),certSeps,[],certPerms)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem certTabsValid : TabsP true stopR stopT certTabs := by
  exact ⟨cutsGood validSlices (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
abbrev PackedState := List Nat × List Nat
structure HintIndex where
  cuts : Array CutV
  seps : Array (Nat × Nat)
  kws : Array KwD
  perms : Array (List Nat)
  next : Array (List Nat)
def hintIndex (n : List (List Nat)) (t : Tabs) : HintIndex :=
  ⟨t.cuts.toArray, t.seps.toArray, t.kws.toArray, t.perms.toArray, n.toArray⟩
def projectedHint (i : Nat) : Nat :=
  if i < 30000 then i else 30000 + (i - 30000) % 1024
def indexedHint (u : Bool) (k : Nat) (ix : HintIndex)
    (xs : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  if i < 10000 then
    match ix.cuts[i]? with
    | some c => cutEval u k xs a b z ka kb c
    | none => false
  else if i < 20000 then
    match ix.seps[i - 10000]? with
    | some q => sepEval u xs a b z ka kb q
    | none => false
  else if i < 30000 then
    match ix.kws[i - 20000]? with
    | some q => !u && Nat.beq (kidN xs a b z ka kb).length (k+1) && kwList (kidN xs a b z ka kb) q
    | none => false
  else
    match ix.perms[(i - 30000) % 1024]?, ix.next[(i - 30000) / 1024]? with
    | some perm, some st => beqL (sortN ((kidN xs a b z ka kb).map (permN perm))) st
    | _, _ => false
private theorem hintNotLT {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr (fun e => h (Nat.blt_eq.mp e))
set_option maxRecDepth 100000 in
theorem indexedHint_sound {u k n t xs a b z ka kb i}
    (h : indexedHint u k (hintIndex n t) xs a b z ka kb i = true) :
    hintOK u k n t xs a b z ka kb (projectedHint i) = true := by
  by_cases h₁ : i < 10000
  · have h₃ : i < 30000 := by omega
    cases hg : t.cuts[i]? <;>
      simpa [indexedHint, hintIndex, projectedHint, hintOK, h₁, h₃, Nat.blt_eq.mpr h₁, hg] using h
  by_cases h₂ : i < 20000
  · have h₃ : i < 30000 := by omega
    cases hg : t.seps[i - 10000]? <;>
      simpa [indexedHint, hintIndex, projectedHint, hintOK, h₁, h₂, h₃,
        hintNotLT h₁, Nat.blt_eq.mpr h₂, hg] using h
  by_cases h₃ : i < 30000
  · cases hg : t.kws[i - 20000]? <;>
      simpa [indexedHint, hintIndex, projectedHint, hintOK, h₁, h₂, h₃,
        hintNotLT h₁, hintNotLT h₂, Nat.blt_eq.mpr h₃, hg] using h
  · let j := (i - 30000) % 1024
    have e₁ : Nat.blt (30000 + j) 10000 = false := hintNotLT (by omega)
    have e₂ : Nat.blt (30000 + j) 20000 = false := hintNotLT (by omega)
    have e₃ : Nat.blt (30000 + j) 30000 = false := hintNotLT (by omega)
    simp only [indexedHint, h₁, h₂, h₃, ite_false, hintIndex, List.getElem?_toArray] at h
    change hintOK u k n t xs a b z ka kb (if i < 30000 then i else 30000 + j) = true
    simp only [h₃, ite_false, hintOK, e₁, e₂, e₃, Bool.cond_false, Nat.add_sub_cancel_left]
    cases ev : t.perms[j]? with
    | none =>
      change t.perms[(i - 30000) % 1024]? = none at ev
      simp [ev] at h
    | some perm =>
      change t.perms[(i - 30000) % 1024]? = some perm at ev
      rw [ev] at h
      cases es : n[(i - 30000) / 1024]? with
      | none => simp [es] at h
      | some st =>
        rw [es] at h
        exact List.any_eq_true.mpr ⟨st, List.mem_of_getElem? es, h⟩
def packedSlot (kk : Bool × Bool) : Nat :=
  if kk.1 then if kk.2 then 0 else 1 else if kk.2 then 2 else 3
def packedDigit (word index : Nat) : Nat := (word >>> (24 * index)) % 16777216
def packedBank (defaults : List Nat) (word : Nat) : List Nat :=
  defaults.map projectedHint ++ (List.range 16).map (fun j => projectedHint (packedDigit word j))
def packedKid (u : Bool) (k : Nat) (ix : HintIndex) (defaults : List Nat)
    (xs : List Nat) (a b z word op : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add xs.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
    (let i := packedDigit word (4 * op + packedSlot kk)
     if i = 0 then defaults.any (indexedHint u k ix xs a b z kk.1 kk.2)
     else indexedHint u k ix xs a b z kk.1 kk.2 i)
def usableDefaults (u : Bool) (ix : HintIndex) (xs defaults : List Nat) : List Nat :=
  defaults.filter fun i =>
    if 10000 ≤ i ∧ i < 20000 then
      match ix.seps[i - 10000]? with
      | some sep => xs.all (same u sep)
      | none => false
    else true
def packedPair (u : Bool) (k : Nat) (ix : HintIndex) (defaults s : List Nat)
    (p : Nat × Nat × List Nat) (word : Nat) : Bool :=
  let localDefaults := usableDefaults u ix p.2.2 defaults
  (opsOf u).all fun op =>
    let z := nb op p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (packedKid u k ix localDefaults p.2.2 p.1 p.2.1 z word op)
theorem packedPair_sound {u k n t defaults s p word}
    (h : packedPair u k (hintIndex n t) defaults s p word = true) :
    pairOK u k n t s p (packedBank defaults word) = true := by
  apply List.all_eq_true.mpr
  intro op hop
  have hh := List.all_eq_true.mp h op hop
  dsimp only at hh ⊢
  simp only [Bool.or_eq_true] at hh ⊢
  rcases hh with h | h
  · exact Or.inl h
  right
  apply List.all_eq_true.mpr
  intro kk hkk
  have hk := List.all_eq_true.mp h kk hkk
  simp only [packedKid, Bool.or_eq_true] at hk
  simp only [kidOK, Bool.or_eq_true]
  rcases hk with hcap | hk
  · exact Or.inl hcap
  right
  apply List.any_eq_true.mpr
  split at hk
  · obtain ⟨i, hi, hw⟩ := List.any_eq_true.mp hk
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (List.mem_filter.mp hi).1), indexedHint_sound hw⟩
  · have ho : op < 4 := by
      cases u <;> simp [opsOf] at hop <;> omega
    have hs : packedSlot kk < 4 := by
      obtain ⟨ka,kb⟩ := kk
      cases ka <;> cases kb <;> decide
    have hm : 4 * op + packedSlot kk ∈ List.range 16 := List.mem_range.mpr (by omega)
    exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem hm), indexedHint_sound hk⟩
def packedZip (f : Nat × Nat × List Nat → Nat → Bool) : List (Nat × Nat × List Nat) → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, word :: rest => f p word && packedZip f ps rest
theorem packedZip_sound {f g bank ps hs}
    (hf : ∀ p word, f p word = true → g p (bank word) = true)
    (h : packedZip f ps hs = true) : allZip g ps (hs.map bank) = true := by
  induction ps generalizing hs with
  | nil => rfl
  | cons p ps ih =>
    cases hs with
    | nil => contradiction
    | cons w ws =>
      obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨hf _ _ h₁, ih h₂⟩
def packedStateOK (u : Bool) (T : Nat) (k : Nat) (ix : HintIndex)
    (defaults : List Nat) (st : PackedState) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
    packedZip (packedPair u k ix defaults st.1) (pairs st.1) st.2
theorem packedState_sound {u T k n t defaults st}
    (h : packedStateOK u T k (hintIndex n t) defaults st = true) :
    stOK u T t k n (st.1, st.2.map (packedBank defaults)) = true := by
  obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨hb, packedZip_sound (fun _ _ h => packedPair_sound h) hc⟩
def PackedLevel (u : Bool) (T k : Nat) (states : List PackedState) : Prop :=
  ∀ st ∈ states, Impossible u (W T) k (st.1.map W).toFinset
theorem packedLevelStep {u R T E t k prev st defaults}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : packedStateOK u T k (hintIndex (prev.map Prod.fst) t) defaults st = true) :
    Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  apply stStep hb ht _ (packedState_sound hc)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
theorem packedLevelAll {u R T E t k prev states defaults}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (packedStateOK u T k (hintIndex (prev.map Prod.fst) t) defaults) = true) :
    PackedLevel u T (k+1) states := by
  intro st hs
  exact packedLevelStep hb ht hn (List.all_eq_true.mp hc st hs)
theorem packedAllChunks {α : Type} {states : List α} {f : α → Bool} (c n : Nat) (hc : 0 < c)
    (hl : states.length ≤ n * c)
    (h : ∀ i, i < n → ((states.drop (i*c)).take c).all f = true) : states.all f = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hi : j / c < n := (Nat.div_lt_iff_lt_mul hc).mpr (by omega)
  apply List.all_eq_true.mp (h _ hi)
  have eq : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt (Nat.mod_lt j hc), List.getElem?_drop, eq]
  exact List.getElem?_eq_getElem hj
theorem packedLowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : PackedLevel u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have found := hI q hq
  rw [e] at found
  simpa only [rootsW,List.map_map,Function.comp_def] using found
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
abbrev LocalModel := Nat × Nat
def localEntry (t : LocalModel) (i : Nat) : Nat := (t.2 >>> (24*i)) % 16777216
def localSearch (t : LocalModel) (r : Nat) : Nat → Nat → Nat → Nat
  | 0,a,_ => a
  | k+1,a,b => if a+1 ≥ b then a else
    let j := (a+b)/2
    if localEntry t j % 8192 ≤ r then localSearch t r k j b else localSearch t r k a j
def localDecode (t : LocalModel) (z : Nat) : Nat × Nat :=
  let r := z % 8192
  let i := localSearch t r 12 0 t.1
  let e := localEntry t i
  let a := e % 8192
  let b := if i+1 < t.1 then localEntry t (i+1) % 8192 else 8192
  (e/8192,(z/8192)*(b-a)+r-a)
def modelwlen : LocalModel := (6,0x13f4801174d00e76b00c06c00a004008000)
def modelword : LocalModel := (370,0x2e3fff2e1ffe2dfffd2ddffc2dbffb2d9ffa2d7ff92d5ff82d3ff72d1ff62cfff52cdff42cbff32c9ff22c7ff12c5ff02c3fef2c1fee2bffed2bdfec2bbfea2b9fe92b7fe82b5fe72b3fe62b1fe52affe42adfe32abfe22a9fe12a7fe02a5fdf2a3fde2a1fdd29ffda29dfd929bfd8299fd7297fd5295fd4293fd3291fd228ffd128dfd028bfcf289fce287fcd285fcc283fcb281fca27ffc927dfc827bfc7279fc6277fc5275fc4273fc3271fc226ffc126dfc026bfbf269fbe267fbd265fba263fb9261fb425ffb325dfb025bfaf259fae257fad255fac253fab251faa24ffa924dfa824bfa4249fa0247f9f245f9d243f9c241f9b23ff9a23df9923bf95239f94237f93235f90233f8f231f8e22ff8d22df8c22bf8b229f89227f87225f86223f85221f8421ff8321df8221bf81219f80217f7f215f7a213f79211f7620ff7520df7420bf72209f71207f67205f66203f60201f5c1fff5b1fdf5a1fbf591f9f581f7f571f5f561f3f551f1f541eff531edf521ebf511e9f501e7f4f1e5f4b1e3f481e1f471dff461ddf441dbf3f1d9f3d1d7f3c1d5f3b1d3f351d1f341cff331cdf321cbf311c9f301c7f2f1c5f2e1c3f2d1c1f2c1bff2b1bdf2a1bbf291b9f281b7f271b5f261b3f251b1f241aff231adf221abf211a9f1e1a7f1d1a5f1b1a3f181a1f1719ff0919df0819bf07199f05197f01195f00193eff191efe18fefd18defc18befb189efa187ef9185ef2183ef0181eef17feee17dee917bedb179eda177ed9175ed0173ead171eac16feab16deaa16bea9169ea8167ea7165ea3163e93161e9215fe9115de8d15be88159e86157e84155e83153e82151e8114fe8014de7f14be7e149e7d147e7c145e7b143e74141e7013fe6f13de6b13be6a139e69137e68135e67133e66131e6212fe6112de6012be5e129e5b127e5a125e59123e58121e5411fe4d11de4a11be49119e47117e46115e43113e42111e3210fe2e10de2b10be2a109e29107e28105e27103e26101e250ffe150fde140fbe130f9e120f7e110f5e100f3e0f0f1e0a0efe090ede080ebe060e9e050e7e040e5e030e3e010e1dff0dfdfe0dddfd0dbdfa0d9df90d7df60d5df50d3df40d1df30cfdf20cddf10cbde50c9dc60c7dc50c5dc40c3dc30c1dc20bfdb70bddb60bbdb30b9db20b7db10b5d8e0b3d8d0b1d8c0afd840add830abd820a9d810a7d780a5d750a3d710a1d6909fd6509dd5709bd52099d4f097d4e095d3d093d2c091d2408fd2308dd1608bd09089cf0087cea085ce9083cd7081c7007fc6c07dc6b07bc4e079b0007784f0757ed0737c60717c506f79306d79206b79106946006720a0651e806318b060fb205efa905cf9305af7f058f6e056f66054f42052f18050ef504eecc04cec204aea7048dab046d64044d61042d28040d0d03ed0c03ccd803acd4038ca4036c13034bf1032b45030ad402ead002ca8702aa5b028a390269f50249da02299b02097401e95301c93c01a90e0188ce01686201480801274501070a00e70900c6a800a2e70081c00060e50040e4002083000000)
def modelclen : LocalModel := (27,0x45ffc035ff8031fdc02ffcc02dfb802bf98029f70027f30025f04023ed8021e8401fe2801dddc01bd60019cdc017c3c015b9c013ab801199000f81c00d62800b37c009068006cf500488e002407000000)
def modelnlen : LocalModel := (45,0x67ffc05bff8059ff0057fec055fe0051fdc04ffd804dfd404bfd0049fc4045fbc043fb0041fa803ffa003df9403bf90039f80037f7c035f60033f54031f3c02ff1c02df0402bed8029eb8027e90025e7c023e44021e1801fdd801dd9001bd38019ca0017c3c015b80013ac40119f800f92400d7e000b65800937100702e004d62002963000000)
def modelcut : LocalModel := (1053,0xf3dfffeddffeed1ffdea9ffce9fffbe9bffae81ff9e7bff8e77ff7e71ff6e67ff5e63ff4e55ff3e51ff2e3dff1e3bff0e29fefe0ffeee05fede03fecdfffebdf7feadebfe9de5fe8de3fe7dd9fe6dcbfe5dc9fe4dc5fe3dbffe2db9fe1db5fe0da1fdfd8ffddd87fdcd77fdbd6dfdad69fd9d61fd8d57fd7d55fd6d4ffd5d4bfd4d3ffd3d2dfd2d2bfd1d29fd0d1dfcfd13fced0dfcdd03fcccf1fcbcedfcacebfc9cdffc8cc1fc7cbffc6cb9fc5cb7fc4cadfc3ca9fc2ca3fc1ca1fc0c99fbfc7bfbec79fbdc6bfbcc55fbbc49fbac31fb9bf3fb8beffb7be9fb6be3fb5bc1fb4bbbfb3bb9fb2bb7fb1bb5fb0bb1fafbaffaebadfadbabfacba9fabba7faaba5fa9ba1fa8b9ffa7b9dfa6b99fa5b91fa4b8ffa3b8dfa2b87fa1b83fa0b7ff9fb79f9eb77f9db73f9cb71f9bb6df9ab6bf99b67f98b65f97b63f96b61f95b5df94b59f93b57f92b53f91b51f90b4ff8fb4bf8eb3bf8db37f8ab35f89b33f88b2ff87b2df86b2bf85b23f84b1ff83b1bf82b19f81b17f80b13f7fb11f7eb0df7dafff7cafbf7baf9f7aaf7f79af3f78af1f77ae7f76ae5f75ae1f74ac9f73ac7f72ac1f71abff70abdf6fabbf6eab7f6dab5f6cab1f6baaff6aaadf69aa9f67aa7f66aa5f65a9ff64a9bf63a95f62a91f61a8ff60a8bf5fa81f5ea75f5da71f5ca6df5ba6bf5aa69f59a67f58a63f57a57f56a4df55a41f54a37f53a35f52a1df51a1bf50a19f4fa17f4ea0ff4da01f4c9fdf4b9f1f4a9edf499ebf489e5f479e1f469dff459cbf449c3f439bdf429bbf419b9f409b5f3f9a5f3e9a1f3d997f3c98ff3b987f3a97ff3997df3897bf37977f36971f3596ff34969f33965f32961f3195bf30957f2f955f2e953f2d951f2c94ff2b94bf2a949f29947f28945f27943f2693ff2593df24939f23937f22935f2192ff2092df1f92bf1e927f1d921f1c91ff1b91bf1a919f19913f18909f17905f16903f15901f148fff138fdf128f7f118f5f0f8f1f0e8edf0d8ebf0c8e9f0b8e3f0a8e1f098dff088ddf078dbf068d7f058d5f048d3f038cff028cdf018b9f008b7eff8a7efe889efd885efc873efb86fefa869ef9867ef8865ef7861ef6855ef584fef484def3845ef283def1839ef0837eef835eee833eed827eec825eeb823eea821ee981fee8819ee7817ee6811ee580fee480dee380bee1809ee0805edf803ede7fbedd7f5edc7efedb7ededa7ebed97e9ed87e7ed77e3ed67e1ed57d9ed47d3ed27d1ed17cded07cbecf7c5ece7c3ecd7c1ecc7bfecb7b7ec97b1ec87afec77adec6793ec578dec478bec3787ec0785ebf783ebe77bebd779ebc769ebb767eba765eb975feb875deb6757eb3755eb2751eb074deaf745eae743ead741eac73feab73deaa73bea9735ea8733ea6731ea572fea472dea372bea1729ea0727e9e725e9d721e9b719e9a717e99715e97713e9670fe9470de9370be91709e90707e8e705e8c703e8b6ffe8a6fde896fbe876f9e866f7e856f1e846e9e836e7e826e5e816dfe806dde7f6dbe7e6d9e7c6d5e7b6d1e7a6cfe786cde776c9e766c5e726c1e716bfe6f6bbe6d6b1e6b6afe6a6ade696a9e686a7e666a5e656a3e646a1e6369fe6269de6169be60699e5e695e5c693e5a691e5868fe5668de5568be54685e53683e5167de50679e4f677e4d673e4b671e4966fe48669e47667e46665e45661e4365de42659e40657e3f655e3e653e3c64fe3a64be38647e37641e3663fe34635e33631e3162fe2f62de2e62be2d629e2c623e2b621e2961fe2761be2660fe2560de2460be21603e20601e1f5fbe1c5e9e1b5e7e1a5e3e195dfe175dde145d9e135d1e115cbe0f5c9e0d5c7e0c5c1e0b5bfe0a5bde095bbe075b9e055b5e045b3e025b1e015afe005addff5a9dfd5a7dfc5a3dfa5a1df959bdf8599df6597df5595df3593df1591df058fdef58ddee589deb587dea583de957bde8579de7577de5573de456dde356bde2563de0561ddf55fdde55dddc559ddb557dda555dd8551dd654fdd254bdd0549dcf547dcd545dcc53fdcb53ddca53bdc9539dc8535dc752bdc6525dc4523dc2521dc1519dc0517dbf513dbd50ddbc50bdbb507dba503db94fddb84f7db64f5db54f1db44efdb34eddb24e9db14e5db04e3dae4dfdaa4ddda94d7da84d5da74d3da64d1da54cfda34cbda14c9da04c7d9c4c5d9b4c3d994bfd984b9d964b7d944b5d934b1d914add8f4a9d8c4a7d8b4a5d894a1d8849fd8649dd8449bd82499d80497d7d495d7c493d7b491d7948fd7748dd7648bd75489d74487d71485d6f483d6d481d6c47fd6a47dd6547bd64475d63473d62471d6146fd6046bd5f469d5d465d5c463d5a461d5945fd5845dd5645bd54459d53457d52455d51453d4f451d4e44fd4d44dd4c44bd4a447d49445d48441d4743fd4643dd4443bd43437d42435d41433d40431d3e42dd3c42bd3a427d39425d38421d3641dd3541bd33419d31417d2f415d2e40fd2c40dd2b407d2a405d28401d273fdd253fbd243f7d233f5d223f3d213f1d203efd1e3edd1d3ebd1c3e9d1a3e7d183e1d173d9d153d7d143d1d133cfd113cdd0f3cbd0e3c9d0d3c7d0c3c5d0a3c1d083bfd073bdd063bbd043b5d023b3d003b1cfe3adcfc3abcfa3a9cf83a3cf63a1cf539fcf439dcf2399cf1393cef38fced38dceb389ce9387ce5383ce337fce237dce1379ce0377cde373cdc371cda36fcd836dcd636bcd5369cd4367cd3363cd2361cd135fcd035dcce359ccd357ccb355cc9351cc734fcc534dcc3349cc2345cc0343cbe341cbc33fcbb33dcba33bcb8339cb7337cb6335cb5333cb332fcb132dcb0327caf325cac323ca7321ca531fca131dc99317c98315c97313c96311c9530fc9430dc8f309c8d307c8a305c88303c86301c822ffc802fdc7f2fbc7e2f9c7d2f7c7c2f1c7b2edc782ebc752e9c732e3c722e1c702dfc6e2ddc6d2dbc6a2d9c682d7c662d5c652d3c632d1c612cfc602cdc5e2cbc5c2c9c5a2c7c572c5c542c3c522c1c4f2bfc4e2bbc4b2b9c4a2b5c492b3c472b1c452afc432adc412a9c3f2a5c3d2a3c3b2a1c3829fc3729dc3529bc30297c2f295c2a293c27291c2628dc2528bc22289c20287c1f285c1d283c1b281c1927fc1727dc1327bc11279c0e275c0d273c0c271c0b26fc0a26dc0926bc05269c03267c01265bff263bfe261bfb25fbfa25dbf825bbf6257bf5255bf3251bef24fbee24dbec24bbe9249be7247be6245be4243be0241bde23fbdc23dbd923bbd7239bd6237bd5235bd3233bd1231bcf22fbcd22dbcb22bbca229bc8227bc6225bc4223bbd221bbb21fbba21dbb821bbb7217bb6215bb4213bb2211bb020fbad20dbab20bbaa209ba7207ba6205ba3203ba0201b9e1ffb971fdb951fbb931f9b911f7b8b1f5b8a1f3b861f1b811efb801edb7b1ebb7a1e9b781e7b761e5b741e3b731dfb701ddb6b1dbb6a1d9b691d7b661d5b631d3b611d1b5f1cfb5d1cdb581cbb541c9b4f1c7b4c1c5b481c3b471c1b431bfb411bdb3c1bbb371b9b341b7b301b5b2e1b3b2b1b1b281afb251adb231abb211a9b1d1a7b1a1a5b191a3b171a1b1619fb1419db1319bb11199b0e197b0c195b0a193b09191b0418fb0118daff18bafa189af9187af6185af2183aed181aec17faea17dae917bae7179ae5177ae1175ade173adb171ad816fad116dacd16bac6169ac5167abf165abc163ab9161ab715fab415dab115baaf159aaa157aa3155a9c151a9814fa9614da9414ba91149a8a147a88145a86143a82141a8113fa7e13da7913ba73139a6e137a6c135a68133a61131a5712fa5612da4f12ba48129a42127a37125a32123a2d121a2811fa2211da1e11ba1b119a19117a16115a14113a10111a0d10fa0b10da0710ba001099f81079f61059ef1039e91019e30ff9df0fd9da0fb9d50f99cf0f79cb0f59c90f39c20f19be0ef9b70ed9b30eb9ae0e99ad0e79a80e59a40e399d0e19970df9900dd98a0db9820d997b0d79750d59700d39670d19620cf95d0cd9560cb9510c994c0c79480c59450c39420c19300bf92d0bd9290bb9250b99240b791b0b59140b390a0b19060af8f50ad8ef0ab8ea0a98e30a78dc0a58d50a38ce0a18ca09f8c609d8be09b8b10998a709789e09589709388b09188108f87908d86908b85d08985108784c08584608383f08183307f82407d81a07b81407980c0778050757f50737ef0717df06f7d906d7cd06b7c20697b60677a606579b06379306178705f77b05d75f05b7480597410577340557120537050516f104f6e404d6cf04b6bb0496a104768804567304365a04163b03f62c03d61303b5fe0395d60375b703558a03356403152702f4e602d4ab02b46f02942e0273ed02538c0233500212ff01f28201d1f901b1930191120170a601503b012fb2010ec600edda00cd1c00ac1b008ab100690800473a0024b5000000)
def modelchild : LocalModel := (564,0x71ffff6efffe6ebffd6e9ffc6e5ffb6e1ffa6ddff86d9ff76d5ff66d1ff56cbff46c9ff36b9ff16b1ff06a3fef6a1fee69dfed69bfec699feb687fea681fe867ffe7673fe666dfe3665fe2661fe165bfe0657fde655fdd653fdc64dfdb647fda641fd963ffd862ffd662bfd4625fd1619fd0613fcf605fce603fcd5fbfcb5f3fca5f1fc95edfc75ebfc55e9fc45e7fc35e3fc25e1fc05ddfbe5cbfbd5b9fbc5b5fb95a9fb85a5fb559dfb258bfb1581fb057ffaf573fae571fad56ffac569fab55dfaa55bfa9559fa854dfa754bfa6549fa5547fa4545fa3537fa2511fa150dfa050bf9f509f9e4e1f9d4d9f9c4bbf9b4b9f9a4b5f994b3f984adf974a5f964a1f9549ff94497f93493f92479f91471f9046bf8f469f8e467f8d45df8c45bf8b459f8a455f88453f87451f8644ff8544bf8443df8343bf82439f81437f7f435f7e42ff7d42bf7c429f7b427f7a425f79423f78421f7741ff76419f75417f74415f72413f71411f7040df6f409f6e407f6c403f6b401f6a3fff693fdf683fbf673f7f663eff633edf623e7f613e3f603e1f5f3dff5e3ddf5b3dbf5a3d9f593cff583cdf573c7f563c5f553bbf5339bf52395f51391f5038df4f389f4c37df4b37bf49373f4736ff46365f43363f42361f4135ff4035df3e357f3d355f3c353f3b351f3934ff3834df37349f36345f34341f3333df3233bf30339f2f335f2e333f2d32ff2c32df2932bf28329f25325f24323f23321f2231ff2131bf1e319f1c317f1b315f19313f17311f1430bf13309f12307f11305f0f303f0e301f0d2fff0c2fdf0b2fbf0a2f9f082f5f062f3f052f1f042edf012e9efe2e7efb2e5ef82e3ef52e1ef32dfef22ddeef2dbeed2d9eeb2d7ee92d5ee82d3ee52d1ee32cfee02cdede2cbedd2c9edc2c7eda2c5ed82c3ed42c1ed32bfed02bdecf2b7ece2b5ecd2b3ecb2b1eca2afec92adec72abec42a9ec22a7ebf2a5ebb2a3eb82a1eb429feb129deae29beab299ea8297ea5293ea428dea2289ea0287e9d285e98283e95281e9127fe8f27de8c27be89279e86277e83275e81273e7e271e7b26fe7826de7226be6f269e6c267e68265e67263e66261e6525fe6225de5f25be5d259e5a257e57255e55253e53251e5024fe4d24de4a24be47249e45247e43245e40243e3d241e3a23fe3723de3423be31239e2e237e2b235e29233e28231e2622fe2422de2122be1c229e18227e15225e12223e11221e0e21fe0b21de0721be04219e01217dfd215dfb213df820fdf320ddf120bdee209deb207de7205de3203ddf201ddd1ffdd71fddd51fbdd31f9dd01f7dc91f5dc61f1dc11efdbe1eddbc1ebdb81e9db41e7db11e5dae1e3da91e1da51dfd9d1ddd981dbd941d9d901d7d8e1d5d8d1d3d8b1d1d891cfd861cdd831cbd821c9d801c7d7f1c5d7b1c3d791c1d741bfd6f1bdd6b1bbd681b9d641b7d601b5d5c1b3d551b1d511afd4d1add491abd431a9d3f1a7d381a5d341a3d301a1d2919fd2519dd2119bd17199d0d197d0b195d05193d03191cfe18fcfc18dcf818bcf5189cef187ce5185ce1183cdd181cd817fcd017dcc717bcbd179cb9177cb5175cb0173ca9171ca116fc9816dc9216bc88169c81167c78165c71163c6d161c6915fc5d15dc5915bc55159c51157c47155c3b153c2f151c2a14fc1f14dc1b14bc15149c12147c0d145c0a143c08141c0713fc0413dc0113bbfd139bf9137bf8135bf3133bef131bee12fbde12dbd812bbd4129bd1127bcd125bc8123bc4121bc011fbba11dbb311bbaa119ba6117b9e115b92113b8c111b8310fb7b10db7710bb73109b6e107b67105b61103b5b101b580ffb4d0fdb490fbb440f9b410f7b3b0f5b330f3b2e0f1b290efb210edb180ebb130e9b110e7b080e5afe0e3af70e1aee0dfae20ddad40dbac80d9abe0d7ab10d5aa60d3a9c0d1a8c0cfa830cda750cba6b0c9a5f0c7a5a0c5a4f0c3a460c1a3d0bfa300bda220bba190b9a110b7a0b0b59ff0b39f40b19ea0af9e10ad9d80ab9cc0a99c30a79b30a59aa0a399e0a199109f98509d97809b97209996909795e09595109394509194008f93608d92708b91b08990d0879010858ec0838df0818d307f8be07d8b107b8a707989407788e07588207387207185d06f84f06d84106b83506982906781b0658060637f70617e705f7cf05d7b605b7aa05979a05778705577c05377005175304f73804d71b04b7050496ed0476d90456bf0436ac04169a03f68803d67903b66303965203763a03562503360b0315f302f5d602d5b802b59402957b02755e02553b0235160214f201f4ce01d4a901b47f0194400174150153d601339001135300f2f400d2a100b2490091d7007135005095002b44000000)
def modelperm : LocalModel := (459,0x59bfff591ffe589ffd57bffc56bff9567ff8565ff7561ff6533ff1531fed52ffec521feb513fe8511fe5503fe44f7fe34f5fe24f3fd84f1fd74edfd64e3fd54e1fd14d5fd04c3fc74b7fbe4b3fb84b1fa84adfa54abfa44a9fa24a5f9c4a3f9a4a1f8d49ff8a499f87497f85495f82493f79491f7848ff7748df7648bf74489f71487f69485f66483f56481f4547df4447bf41475f40463f3f457f3c453f3b451f3844df37445f36441f3543ff3443df3243bf31439f2f423f2e421f2c409f2b405f29403f21401f1b3f1f1a3edf193e5f183d9f173d5f163d3f0f3d1f0c3c9f0b3c7f063c5f033c3efe3c1ece3bdeca3bbec73b9ec53b7ec23b5ebc3b3ebb3b1eb03afeae3adead3a9eaa3a7ea73a5ea33a3ea039be9d399e9c397e93393e87391e7e38fe7b38de6b38be63389e5f387e54385e39381e3137fe3037be2e379e28377e26375e24373e1e36fe1d36be1b369e18367e12363e06361dd635ddd435bdd0359dce357dcd355dc9351dc534fdc434bdc2349dbe347dbc343dbb341dba33fdb833bdb6337db5333daf331da732dda632bda5329da4327da3325da2323da1321d9e319d9d317d9c315d9a313d92311d8e30fd8b30dd8530bd84301d832f3d812f1d802e7d7f2e5d7d2e3d782e1d762dfd742ddd6d2dbd692d9d632d7d562d5d502d3d422d1d0b2cfd0a2cdd082cbd032c7d022c5d012c1cf92bfcf82bdcf72bbcf62b9cf22afcec2a7ceb2a5cea2a3ce52a1ce129fce029dcd329bccd297cbc295cab293caa291ca028bc9f289c9a287c99285c96283c9327dc90279c8c277c88273c7d271c7326fc7026dc5c26bc53269c4c267c3a265c28263c1f261bcd25fbc225bba4259b5c257b57255b54253b49251b4224fb4124db3f24bb34249b2e247b1e245b0d243afb241ab923dab723bab5239ab4237ab3235ab1233ab022faad22daab229aa9227aa7225aa4223a98221a9221fa8b21da8121ba80217a7f215a7b213a79211a6420fa6220da6020ba5e209a5d207a5c203a5b201a5a1fda591f9a581f7a551f5a511f3a4b1f1a481efa411eda301eba2b1e9a1f1e7a131e59ff1e39f11e19911df9901d798f1d598e1d398b1d19851cf9811c39791c19771bf9741bd9701b796d1b39681b19631af9621ad9601ab94f1a994b1a793d1a59311a39281a192619f92019b91f19991d19791a19591719390f19190b18d90818b9071899061879051859011838f71818ee17f8e717d8df17b8c91798c11778af1758a317389217186516f86116d85f16b84c16982716782216581d16381216180b15f80815d80315b8011597fc1577f91557ed1537e61517d114f7cc14d7c514b7aa1497a414779814578814377814174f13f73413d72813b71a1396f21376dd1356ad1336371315da12f5bf12d54c12b54912953a1275331254f31234e51214001193ff1153f91113f410f3f310d3ee10b3ed1093e11073dd1053d51033ca1013a20ff3940fd35d0fb35c0f93540f734b0f52e40f32cd0f11ab0e51aa0e31a90e11a60d31a20cf1a10c719e0c319a0c11930bd18d0bb17d0b91790b71740b51700b316e0b116c0af16a0a91680a71640a51620a31560a115209d14f09914e09714a09514909314209113508f13008d12808b11b08911508710d08510a0831000810ca07f0c607d0c407b0b407909307709107508d07308407107806f07606d07506b07406907006706c06506606306206103c05f03a05d03905b02405902005701f05501a05300a050fe004efcb04cfc204afb2048f94046f81044f63042ed9040e9403ee8003ce00038def036de8034d91032d84030c6c02ec6902cc6502ac4e028c49026c42024c2a022c15020bd801ebc601cbb801ab9f018b51016b3c014b16012a800109f700e9cb00c8c500a8ae0088530067c200465c002579000000)
def localWords : Nat := 0xfff1fff1fff1fff0ffffffff111011100000eeeefff0fffeffffffff5555550000000000a8a8a8fc000000000000aafeaaaaaaaaeeeefffeffffeeeefffffffeffffffaafffffffeffffaaaafffffffaaaaaaaaaaaaaaafeffffff0001010100aaaaaaaaaaaafffeffffaaaafffffffeffffff00fffffffeffff0000fffffffc0f0f0f0f0f0f0f00eeeeeeeeeeeeeee0ffff0000fffffffeffffffff0000fff0ffffffff0000eeeefff0fff0fffffffef0f0fffcf0f0fffcfffafffafffefffefff0fff0fffefffeffffffffeee0eee0ffffffffccccdcdcffff0000ffff000affff0000ffff00aafffffffffafafffaffffffffccccfcfcffff8888ffff8888fffffffffbfafbfaffffffffdcdcdcdcffff00aaffff00aaaaaaaaaaeeeeeeeeffffffffdddcdddcffff00eeffff00ee00000000000000aaaaaaaafeaaaaaafeaaafaaafaaaeaaaeffffaaaafffffefeccccccccccccfffc0000fffffffffefeffffffffff000000fffffffff000f000aaaafffffffffefefeeefeeefeeefeeef5f5f5f0f1f1f1f0ffffffff0000aafeffffffffaaaafffaffffffffaafeaafeffffaafeffffaafeccccfffcccccfffcffffffffeeeefffefffffff0f1f1f1f0ffffffffaaaafffeccccccccfffffffcffffffff0000fffc0000000efffffffe000000000000000efffefffefffe0000ffffffff0000000efefefefefffffffe3333333332323232ffffffff0000fefeffffffff000000feaaaaaaaaaaaaaaa8ffffeeeeeeeeeeeef0f0f0f0fffffff0000000eefffffffeffffffff000000ee00000000000000fe00ff00ff00ff00feff00ff00ff00fe000f0f0f0f0f0f0e0e00ff00ff00fe00fe0000ffff0000fffeff0fff0fff0eff0effffffff00fe00feffff000000000000ffffffaaffaaffaaffffffffffaaaaaaffff000effff000efffffffffffffffeffff00ffffff00aaffff00feffff00fe0f0f0f0f0f0e0f0e0000ffff0000eeee00000000fefefffecccccccccfcccfccfafafffafafafffa0000aaaafffcfffeaaaaffffaaaafefeaaaafffeaaaafffefafafafafffafffa00000000fffffffcaaaaaaa8fffffffcff0fff0fff0fff0af0f0f0f0fafafafaffff00ffffff00eeffffffffaaaaaafeffff0000ffff000eeeeeeeeefffffffeff000000ff000000ffffffffaaaafefefffffffffdfdfdfcaaaabbbaaaaabbbaffff0000ffff00ee00000000aaaaaafeff0fff00ff0fff003333333333323332aaaaaaaafffffffe0000ffff0000fefe3333333333333232eeeefffeeeeefffeff0eff0eff0eff0effffffffdddddddcffff0000ffff00feffff000fffff000a00ff00ff00ff00f0ffcfffccffcfffccffffcfcfffffccccffddffccffddffccffffddddffffdcdcff00ff00ff0fff0a00000000fffffcfc0000fffc0000fffc00000000fffcfffcffff00faffff00faaaaafffaaaaafffaff00ff00ffffffeeff0fff0aff0fff0af0f0f0f0f3f0f3f0ffefffeeffefffeeffafffaaffafffaaf3f0f3f0f3f0f3f0ffffffffccccfffcff00ff00ff00ffeeff11ff10ff11ff10ffffffffffff3330ffffffffccccdddcff00ff00ff0eff0effffaaaafffcaaa8ffaaffaaffaaffeeffffff00ffffff44ffffffffffaaffeeffaaffaaffeeffeeffffffffffaeffaeffffff0cffffff0cffaeffaeffaeffaeffffffffffeaffeaf3f2f3f2f3f2f3f20000fff00000fff0fffffffffffffffaf0f0fffaf0f0fffaffffeeeefffffefeffaaffaafffefffeffffccccfffffefeff00ff00fffefffe0000fafa0000fafaffffffffffaacc88aaaaaaaafefefefeffffffaaffffffeeffffffffffff00aaf0f0f0f0f0f0fafaffffffffffffffeeffffffffffff0044ffffffffffff0c0cffffffaeffffffaeffffffffffff0a0af2f2f2f2f2f2f2f2ffffffeaffffffeaffffffffffff8888f8f8f8f8f8f8f8f8eeeeeeeefffefffe00fa00fa00fa00fa00ff00f000ff00f0ffffff00ffffffeeaaaaaaaaaaaafefe8888888888888888ffffffffffff0e0effffff0effffff0e000000000000aaaa00000000aaaaaaaa0000000000fffffeffffffffffeeeeeeffffffffffcccccc00000000aafffffeffeeeeeeffeeeeeefffffffffeeefeeeffff0000fffffefefffffffefffffffe0000000255555556ffffff00fefefe0000000000fffffefeffff0000fffe00000000000000ff00fefffff0f0f0f0f0f0ffffccccccccccccffffffffffc0ffc00ffa0ffa0ffa0ffaffffc0c0ffffc0c0fffffffffffafafafffffffafffafffa00000000aaaafffcffffffff0000ffee0a0a0f0f0a0a0e0e00000000aaaafefeccccccccffccffccf0f0f0f0fffff0f0ccccffccccccffccf0f0f0f0fffffffa88888888fffffff800000000fffefefefffffffffff0f0f0fffafafafffafafafff0f0f0fff0f0f0ffccccccffccccccff0fff00ff0fff0effffffff0000fffe000000000f0f0e0efffffffffcccfcccffeaffeaffeaffeafffff000fffff0000000000000ffffee00000000000000eeff0fff0eff0fff0eeeeeeeeeffffffeeffffffffffffc0c0ffffffc0ffffffc00000ffffffffaaaa00000000ffffffeeffffff00ff00ff00fcccfcccfcccfccc0f0f0f0f0f0a0f0aeeeeffeeeeeeffeeccccccccccccfcfcffffffffffff3300eeeeeeeeffeeffeeccccccccfcfcfcfcffafffaeffafffae00000000aaaafffeaaaaaaaaafaaafaaaaaaffaaaaaaffaaaaaaaaaaffaaffaaaaaaaaaafffffffafff0fff0ffffaaaaccccccccffffffcc0000fffe0000fffeaaaaaaaaaaaafffaff03ff02ff03ff02f3f3f3f0f3f3f3f0fffff3f3fffff0f0fbfafbfafbfafbfaffffffffff0eff0effffffeeffeeffeeffffffccffccffccfffffafafafafafaccccccccfffefffef0f0f0f0fffefffef0f0f0f0f3f2f3f200000000fffafffaffffffffff55ff00fffff5f0fffff5f0fafafafafffefffeccccccccccccfefefff5fff4fff5fff400000000fffffff0000000000000fefe000000000000fff0ffffffffffff00eeffffffffffff000efff0fff0fff0eee0ffffffffffffffaaaaaaaaaafffcfffcdcdcdcdcdcdcdcdcf3f3f3f2f3f3f3f2ffffffffff00ff0effffffffffaaffaafffffefefefefefe000000eefff0fffe00000000eeeefffeffffffffff00ffeeffffffffffffaafef0f0f0f0f0f0fefefffffffafffffffaaaaaaaa8aaaafffc00000000fffffffa0f0f0f0f0e0e0e0e0000ffffffffeeeefffffffffffffff0fffffff0fff0fff0eaeaeaeaeaeaeaeaffffffffffff00fefffffffffffefffe000000000000fffefffffffffffffefef1f1f1f0f1f1f1f0ffffffeeffffffee0000fffa0000fffaaaaaaaaafffefffefffffffffffffffcffffffffffccf0c0fffffffcfffffffcfffffffff0f0f0f0dddcdddcdddcdddcfff3fff0fff3fff0ffffffffffffaaaaffffffff00000000f0f0f0f0f0f0f0f000000000eeeeeeeeffffffffffffccccfff5fff0fff5fff0ffffffffaaaaaaaaccccccccdddcdddcffffffffffff00fcccccccccccccccccff00ff00ff00ff00fffefffefffefffe00000000fffefffeffff0000ffff0000fffffffffffffafafffffefefffffefeffffffffffeeffeefffffffffffcfffcfffffffffffafffaffeeffeeffeeffeefffffcfcfffffcfcfffcfffcfffcfffc000000000000eeeefffffffffffffcfcffffffffffffeeeeffffff00ffffff00ffffaaaaffffaaaa0000ffee0000ffeeffffffffccccccccffffeeeeffffeeeeaaaaaaaaffffffaaffffffffeeeeeeeeffffffffffffffccffffffccffffffccfff0fff0fff0fff000000000fffffffefffff0f0fffff0f0ffccffccffccffcc00000000ffffffaafffffffffffff0f0ffffffffffccffccffffffaaffffffaafefefefefefefefefffffffffafafafaffffffffffffff00fffffffffcfcfcfcfffffafafffffafafffafffafffafffafffffffffefefefefffffff0fffffff0ffffccccffffccccffaaffaaffaaffaa00000000fefefefefffffffffff0fff0ffcfffceffcfffcefcfcfcfcfcfcfcfcaaaaaaaaaaaaaaaaffffffffffff0000ffffffffff00ff00fdfdfdfcfdfdfdfcfafafafafafafafaeeeeeeeeeeeeeeee
def localCutNames : Nat := 0x8078027fb7a37a076c76b76a7196e76e66bf66e66765b63263162a6296206115f84fa4f949f49c4967e07d87c87bc7a87a77a679878974474273d73872e71d71c71b6ff6fe6fd6d36ce6c86c36c26bc6bb6b86a86a368e67166b65d64563963863663462161f61e6186086076016005f75f55f25e75e15c75c65c55bc5bb5a559d59b59959859659258758258157b56d56c56b56a56656155c54053e53d53c53b5394fb4f64c04b14b04ae4ad4ac4aa49449248f48347b47647547046d45644144040e4044014003fc3e03cd3cb37a37837732f2e41fc1fb1fa1b71b31850e48018007ff7fd7fa7f97f77ea7dc7d77d67ce7c97c37bf7be7b67b27ad7ac7ab79c79b79a79479279179078d78a78878578377a76376276176075c75b75a75374f74e74d74c74a74974173e73b73773072972872772671e71771671570b70a7097016d26d16d06cc6cb6ca6c96c76c66c56ba6b76b46b16b06af6a26a069f69d69b69a69769468768368067a67967767567366466365f65765064762762461a61961561461260d60b6056046035ff5f15f05e65e45e05df5de5d65d55d15cf5ce5c45c35c25c05bf5b75b05a658a58958858658358057f57d57557457257157056f56e55355255154e54d54c54b54354253853653553453353252d52c52b52a52752552351851750f50d50c5075004f74f54f34f14f04ed4eb4e54e14df4da4d94d64d34d14ce4c94c64c54bf4bc4ba4b44b34a749848c48b48548447e47347246a46946746546446346245e45945145044743d43842642441f41541440d3f93f83f13eb3e93e33de3dd3dc3d33d23c93c83c73c63c53c43c33bc3bb3ba3b93b83b73b53b43b33b03ae3ac3a53a439e39d39c39b39238938638537537437337036f36d36c36936836636236035f35c35b35735634b34a34834734033d32d32632031f31e31c31a31430d3042ff2fc2f32f22e22e12e02c42c32c22be2bd2a729928928227d27927827727627327226e25825425224e24c2372362222091f41f11dd1dc1d41c61c01b21a81a719e19d19919118218117f16a16316015615513412f12e12d12a12411511410b0fb0fa0f80f70f60f50f40f30f10de0b303c03b0390387f87f67f57f17ef7ee7e97e87e77bb79778477976d74b7357337237217146f26f06ee6ec6a169e69c69568668567f67e67d67867463f62560c5fe5fd5fb5fa5f95f45d25ad5ac5ab54a54152952652252152051f51d51c51b51a51451351251150a5085065055045024f44ea4e94de4dd4d84d74d44d24cd4ca4be4bd4bb4b84b74a94a84a648e48d46844f44e44c44b44944844544443f43e42c42742342242142041c41b41a40a4094084063fa3d13cf3b63b23a33a23a13a039f39a39939839739639539439336b36a35d35435335034e34d34434334234133f33e33c33b33332e32832431831231130a3093083063032fb2f82f62ec2eb2e72e62df2db2da2d92d82d72d32d22d02cf2ce2cd2cc2c02bc2b92b72b52b42ad2ac2ab2a92a629328628326c26926325d25c24b24524023f23e23a23523323223122e22d2262252192142022001ff1f61e71e61e51e11db1da1d71cf1cd1c91a919819718717e17a17917817717217117016816615e15c15b15a15915815715215014614513c13a13912211e11d11b11a1191011000f00ef0eb0ea0e70dc0d90d80d70d40d10ca0c60c40c30c20c10bd0b70b20ae0ac0ab0aa0a90a60a209309108f08d08c08908107e07d07c07b07a07907607107006f06d06c06905b04e04b04404103e7f076676572071f5034c133a3352e82b82a52a42a12a026626226025f23c23b23422b22a22922822721e21d21c21b1d61410ee0ed0e80cf0ce0bc0a40a309f09e07507305f05705603503203103002101f0170b17dd62b37e37c7db7c57af7ae7a97a473c7227006c46a56a464361d61c61761660e5da59a59058b5304e64e04db4cf4b24af48a45d40f28b28a1b40e27747df7de7d17cf7c47c27c07b87b17aa7a579d78b78077f77e77d77877777676f76e75f75e73a73273172f72a7036f16e86cf6b26a769969869668c68868465164863b62661060f60a5c15b65b25aa5a45a35a257351650e5014ff4fe4ef4ec4e74e44e34dc4cc4cb48645c43743642f41d4163f73f53ec3ed3e83d83b138737636133832b32a3273253233022fe2e92d42c92a829c29b27e2202082071f91f71bf1be1bb1a31a11a019f19014f14e14913313112711110d10a0df0b609477b7f464c7f37f27eb77140b7347243e63e75f65ef5b45445374c34b64a51b136744d44642e42d4183ff19b3e53d037236e36335e35235134c34533731931330e30b3072f52dc2d62cb2ae2aa2a329729628128026f26b24624824724223822f2162042031e91e81e31e21e01d01c81c71c51c11ab18c18b17c16714414013613011f1181031020db0d60d30d20c50ba0ad0a80a509008507807706b06a06305c05a04d02a0260207737724c20af24133427526123d2152132121aa16e1611040d00a009c09507403601e01420b7e17d37cb75875774673962c66a6695ee5ba57c3da3ca3913881837b077075974071870c7067046fa6f86ef6e96dc6db65968a67b66666566165864f6495fc5f35d45b95b15a959e57655a5575495485474ee4774c837946045f45243540c3f63e43c23c13ad3ab3a839038f38e38a3713653643493223052f12ed2b12a22512011f31ac16915412c11010c0970677ed7ec3fe7674f82bf5d850b1a242b42942840734f27431030f2f72d52d12ba2bb27126725a21a1eb1d81d11ca19318a17515d1381371080c909208006204f0480432c126a14709b02e0137e263337f3307fe7fc7d27b47b37506d96445d05cd5975954664102c71867ca7c17b779579378c77c6e26e16da68d68266064e64a64063e5e25d95d35b85625564804e84b54ab46145b45a4584434344113f03e13db3d43af35531b30c2fd2232061a619614a13212901d78f73f12142a4193d534633927b26d25e2492171f51d91d21cb1c213f0c70be0580470252b310f05e02c49a7bd6ad6725ca5bd5b356555f48248147c4422051b97d07436dd69369168967c6305dd5db58555955554f5104c44b948948747f4554323bd2ef2952211af18010903a72568144a4173ef3362fa2ca2b229227f26425b1ec1cc1c41a417d17613e13512011c0cd0830722502940a70a17e45ed7c77b97b570f5c959c56855e5543d73d620a7cd7567556e56aa6ea6ae64d6426416025b55635465455194e238049147d45443c43a43943141e3fb3a638b32c31731629a2882872571f01ba1ad16b12b4d55c835a3f32ea27c2681d51c30cb0c806804502b0280b066820c18474571365a56755b53f53a4974031b87757546d763d63c63a5e55dc5a85a75a05695645244744d04333be3a72e331530029e2981fd1de1bc1640f20b524f27024d2391df18913d1230b808e0293fd22c09d09a71176972c6ab65e6235eb59152f4fd4a149547945738270257a65660659f51543b38c3293012ee2551bd0e600a3d92e510e0c006e05d02718d7517c662e7d578e78278169238178675d70d57849048846e4304253ea3e231d2af17416515f14d6d629124424321820f1ee16d0e908707f2590bb66c0048047da7cc7687646b94a249347a4023837ba7876765e355041238d2f90e000b6eb3f43f22532102240da0b409904680379f7996ac6465ea58e4a340568b6555943c035829f1f81f217b0f916c1a514c11379e62d7d468f5cc57928f7107087076d56b346f1b019c5283212dd25616203f7e679649d20d7487476df6284a429070e3bf0967e57d98057a149b6c16e46905313846f56e34785d75a14c746c45333220e1940e53aa2c523016f15106500580649e6fc65355d5be6fb6f946b1b628d6f42de7525e95e857755828e2111ef09828c05903d01164b6356e06cd5ae5094714133a91126d46de59328418814b0106f73ee10635918e4a058f37d7366f30542b60376540066f62f019a1280661266be71a7056373cc0bf7e36625af2f41161436a914205372b6bd6094992c65ec65c3311925cb24a00961b57e18f71252e10729d00c0071ed08614872d6ed0647a266f6a66226131171950881fe2b01ea58d1d366d3ce1ce00856021f0d50cc1e40ff6b658c3df2c86526c058401a6b537b15351e6d84f24fc67005127a2650001ae0fc0dd0010340e12850fe62f0ec08b13b1050500331250240820e317301b01c08404004904202f02202301600e02d1b50600fd06100f00200d0b908a05200301901504a05501801204c
def localReadWords : Nat → Nat → List Nat × Nat
  | 0,s => ([],s)
  | k+1,s =>
    let (i,s) := localDecode modelword s
    let v := (localWords >>> (64*i)) % 18446744073709551616
    let (vs,t) := localReadWords k s
    ((v + (v <<< 64)) :: vs,t)
def localReadCuts : Nat → Nat → Nat → List Nat × Nat
  | 0,_,s => ([],s)
  | k+1,q,s =>
    let (j,s) := localDecode modelcut s
    let i := q+j
    let (cs,t) := localReadCuts k (i+1) s
    ((localCutNames >>> (12*i)) % 4096 :: cs,t)
def localReadNext : Nat → Nat → Nat → List Nat
  | 0,_,_ => []
  | k+1,q,s =>
    let (j,s) := localDecode modelchild s
    let (perm,s) := localDecode modelperm s
    let i := q+j
    (30000 + 1024*i + perm) :: localReadNext k i s
def localState (s : Nat) : PackedState :=
  let (n,s) := localDecode modelwlen s
  let (ws,s) := localReadWords n s
  let (a,s) := localDecode modelclen s
  let (cs,s) := localReadCuts a 0 s
  let (b,s) := localDecode modelnlen s
  (ws,cs ++ localReadNext b 0 s)
def local4g0 : List Nat := [0x338674626066,0xd9e4ce5628e02e,0x62c99824043,0xcd625c626069,0x6af95c72030,0x415359000011,0x4ffb5b512020,0x1b2917514003,0x9a2bdaf88004,0x447fb6e842b0043,0x3e70879d8049,0x8ba60bd800b,0x268af6d9fc03f,0x13fed6d64e029,0x2398f05ae03a,0xb46311eea02c]
def localD4 : List PackedState := (local4g0).map localState
def local5g0 : List Nat := [0xb789253eb609a80c00e2,0x24f9a00dd92065f7588067,0xd3147feed51a72eebaa52572,0xaa22b796349b70a8a2e2,0x10325d526616,0xc4812fd5f7d9253f,0x3ea87fda9992d00ab,0xa3d4fc7e7ea481,0x62db531205f,0xeaeba00cba4b7e818468040c,0x3f385fd65161e686,0x2956df76f10358,0x495d4eac2ae1f6df181800c,0x39f110ff80ae8d24ae,0x7d061404a72580,0x1925f19688192,0x10c64277383203c7,0xb92d59d5ce13fa718,0x5ccd27f93385eb970e12f,0xc012cf7545aea0ba,0x10820ebecc676a,0x6c52d9232db0e216,0x4290528aef3e466,0x17c6fd7ac63254e743]
def local5g1 : List Nat := [0x2c6bffca01427f,0x7069b5aa6450a6188ca611,0x5217912a0384bd,0xc7e85ea0638763,0x12d9723fcc547761df00dc2dc,0x44c55d1208a5d8,0x305fa6a205ab5b9d21c5,0xbbf6db817c8bc19c,0x133e5463ae56cb66b0726481,0x1138b4070f1b16683,0x1caa6dfdd83a1,0x1faa3935bf6fbaca44bfa370,0x10123565cb9fed4147,0x638c745e90d89dfcf8300625,0x18a3be200a579,0x6c52d9233f60852e,0x58676ee014dde74153,0xf6246c8734826b,0x2c7535a7f6822355,0x240c8fa00ba67fbada676,0xb99af90aa861ca0e038b2044,0xb6d4b5b1e18914010,0x8ea030bc734b7edb1904a6,0x2aac3498b687b812b2243]
def local5g2 : List Nat := [0x9db22a63a4ffcdbdadae00f,0x1135bbf77b11b1d56764,0x94d5bd5c322189652c,0x26bc1bd9dbf3eed72d42c412461f,0x3c9e3a35659fa555,0x1c1f4a49946a4,0x4a4fe615bce558,0x2c13a6529dd4163,0x1665224dc9ea9c652c,0x6f7940cc4681aa84af,0x530e2aa43fe56b3004b,0x149b8dace44a159,0x7219f03fa2aa473,0x29fec38424,0x5d472bfe251,0xdd78d467849f,0x19fb4fed1020767,0x4964c2a564,0x17494ad5a86521c2,0x5c1db241b1,0x69a70eaa93ae67f,0x1b50165d277c6f6,0x81dc029f16f2556366,0x75578ebeda9c6619]
def local5g3 : List Nat := [0x4778e335975f3056c,0x1183b1337ed4cba071,0x15058c6320f42ea,0x1736ab8379,0x1ce6b8150147,0x90a47fe3e402,0xb3b0d30397,0x3145b76e4595,0x266d08f5632453,0x4a5c244f92131,0x13945d5e392,0x41cd74d88376,0x304db762da,0xbb30e08f14dc614,0x598349021bd,0x95729c446d5,0x6ebc48b45208d,0xb8d4649e33edc1646db,0x2a248dd9e3c6,0x1f2c1b48633b,0x3e2e1069b9f3c9f65b7,0x588002f24e2ba0f826c5,0x12ddbdd69d781237b,0x19bd124e6b583215f]
def local5g4 : List Nat := [0x414cb2a96569ce743,0x69a1769ae68c6de,0x14c377f31f46a1,0x415e300667d,0x1c8b37e5e406e36a,0x34fa5970441a,0x565b2ac2b7,0xe11739a7d0ba56c,0x13a970ed8c525,0x8dd208864a,0x4174c11d61884644,0x13ff4f2b243f1,0x1786f8434dc4e6,0x1340b5ea1fe20f7,0x53adf1d5ac2e3,0x198a7b21e0992c60cc,0x6b8ffe26d2,0x1522c1f6e764,0x86ee71a2726,0xa131b03f6d78b27713862617,0x1765f0b1c41f,0x8545791e90e403,0x2188286b5648897d6ba48e,0x17ce93bcee6c4058]
def local5g5 : List Nat := [0x1a4e40bfa629f,0x3ecac07ed1ba0257,0x20319a5950c6bb,0x22cc04da6d23c8,0x9b7e918e1da52f,0x1338b8596893845a,0x2a7366636a292e2e9,0x915adf063ba47f,0x2e8b9f14a4594500,0x1068ab1ebcb0227e,0x8cd7042570fc422,0xbe2b11563a539,0x27b77ce7062568,0x168b8ad0602804c575,0x8af5825e259aebb4d9cd82383,0x3230db768322aa217,0x1e737077e0479,0x23795d800ccee920a5,0x654bcbf83488621,0x67730692342a552,0xc9f6c2bed4aa8195,0x43eabc346509,0x1eab27eb892414,0x2da9214b25e24d]
def local5g6 : List Nat := [0x1ef6a37e314a06b0,0x5e07e627932c0380ec,0xb9c098448427eac20a58de40031,0x8a5299495418804ee,0x13395c855292ec050,0x1d1ddbcdca66f9,0x173ff67710f64d3c6146,0x5e9d2fdc8389,0xa96137c80a6,0x6ac73561ba2612,0x18f03b3ac464,0x182ca6b0e69c09b,0x537df00842c,0x94581bd02280a4ea271290606e,0x6ef0cd38fe8a0bb,0x4aa0b8b0660,0x149b8da84444,0x7de0e35ede73c5b1,0x9529000d157c0b7,0x1705f7a8e1fc413,0x61d8eb25949d180ee,0x5b30f0af28c9ec397,0xa9d3aa25389e4aa2fa,0x4290528c574c734]
def local5g7 : List Nat := [0x719997ea8180456,0x3054118c8a674a,0x2e2a4c47ec26f,0x1159d95320c8,0x39b67de0026e6c512,0x5cd325186c8,0x1bb7f264cc0d9,0x70c56d1698fc419c,0xeb0b926de306,0x16b35a0d2a5cbc4bf,0x29a2d1d9c894a5470f,0x137a5604ee2919a9a486bbae117,0x936628b3d6e3ae,0x3ff65310fba0a8,0x22d408cc0d4,0x7e0c3304b3c2d6,0x209b7fa336,0x8c48dba01de,0x5907a4c529,0x2d11fd91f0662,0xde279a6033c,0x7471f860c0f8,0x2b2d8a57505c9,0x67a396c606fec38a]
def local5g8 : List Nat := [0x1d380a8f48d3873b,0x1516e626648e,0x154fe3403d2,0xacaf86fa16717c9942a7,0xc9474d161df,0x2130a8a886a27a3f9,0x11375d9e89aea143a61a,0x16ac395836f49a60a,0xc3cfd273bf780d5,0x2205c0b1e1e3264d,0x10c865fa80f8086,0xd8f7683d9b4e29d,0xd32a4d89de2b7,0x46df88e82694,0x72a3ac32606d,0x67c2e2f5a361,0x12bb7d81dc2d4,0x6dccf8c2d4,0x418b7cc673454c,0x143d4d7abc418,0x29f6f81b4c02a5,0xa788890a42bc,0x167b600211f070ca7a0a0,0x3a795097d0cc27a]
def local5g9 : List Nat := [0x1b06d6e93a21d,0x645e103248d7a3f7,0x29d07493a179,0x113d58cc82ea,0x77909755213e,0x9fb4f6643701a7,0x56907a8a6235ef083c6,0x3ced8e4564416c,0x1d840d65b1,0x5d962ac6558,0x2ba952a3e4341,0x924866a239,0xb873ab3438c,0x2aabce9df85c72711,0xab9041c04f9,0x35e92e26a5ec,0x3bcc91afc08d,0x343e6b864cf,0x21144b48e1b1,0x58a02ad4c53f,0x222318e5269a60536,0x2aa656fb0e534,0x459a649a2a27a,0x459a649a2a27b]
def local5g10 : List Nat := [0x459a649a2a27c,0xbcc490d4a230,0x6c5cb96673364ad,0xd8fa03ed57013b,0x126d72a7471e,0xaff053a180e0de,0x63fcc1384e9,0xa4555504485,0x13cb682669,0x2d6c2d4cdc6c426214,0x1b840ac8ac2b34592,0x7cf41cc6816fa662,0xca0b04a37024b,0x2b27b991e84f3,0x19038184cd58b94595,0x771a4b5c86aa,0x87e8d51a313fafd05e1,0x1362ba078ff21a20b,0x13683c4e4418b,0x2a5423f0a4a5,0x6763e028550c40a9,0x181319e0e46a,0x78085b0504a61e1,0x332ac6257b]
def local5g11 : List Nat := [0x9933188ef6c629,0x89143a1a6461,0x30186de6ded8334,0x13683c4e4418c,0x2a5423f0a4a8,0x557e8cfc1dea413,0x459a5b60c63b0,0xc550811fa415,0x265a13c26ed,0x1bb050c11924745,0x515e557a4be,0xb3470732501e6214,0x1a4f5e4f0ad04c280,0xa87530f6a47269a,0xe202d3735e734296,0x4a88850c0f8,0xa0b43cc66c786484e1,0xec97fdcc81adbc38e,0x7e6c3965f98c494282,0x221c7dc5565c700,0x49ff6acebbacc680d1,0x1a9fd664f1d99810f,0x4a2af2ac745,0x5da06f6f104b3]
def local5g12 : List Nat := [0x818bb5bfa1bc,0x2096ddc7880a0285,0x221053d60de632,0x54e56be83deae08a,0x3261167935a0e1,0xa3b08c04cd984d6,0x6eb10aa3c1a7,0x1b8c0f531c5d4,0x17d46f26bf,0x593879264e0b6,0x3abd18074f,0x4ba9df26be15f,0x6c29974caba27f,0x92b3d9c0fd78271,0x341236c657ce350,0x374af0fd8bba329,0x55724731926667,0x3ded77a39ec1cb,0x6c9a0200727,0x380dbac5ec,0x3528ea9a23b,0x98c2738ba196860e,0x135c7bed266a,0x7c201bfc442]
def local5g13 : List Nat := [0x333e9882a35b,0x7c201bfc447,0x7c85fb12641,0x7c85fb12646,0x8a1969f341d5,0x2274382eb26da,0x8a1969f341d0,0x142affc487,0x352d2065e85da,0x3194aea4a1,0xe722c53b8421,0x142aff9a3b6,0x32cb91f5074e46a734,0x8bd57f6e6e4,0x20c2cd9144f65d60516,0xd0f18b839ab803ca55e,0x32a7cd6a382be70e,0x11d151129ec7c212,0x6bf4badad66e5aa34b,0x19e3e3299a191826de,0x4c8bf7f4ae780d6655f,0x5057c7a5ef488a5e244,0x25f09a8bd90fa26d,0x2c41947973052440c1]
def local5g14 : List Nat := [0xd4ed88703f4,0x182516811fdd46071,0x19fb8ea322565e734,0x88836269bf224ce5e3,0x1a501d5fac55154600,0xe2a788429,0x1bf6ca8fb62572,0x1c119801d1b57a1fa,0x29722baa2ca9806ef,0xaeaa49dda618,0x1330aec4730efe078,0x19483b22687c089,0xe2793b16c9523f2,0xef245d05ae66be,0x26ca6408e984506,0x2577d6098419,0x2cfb35be7c4387,0xda873e85b6e4340,0x6bac970ea392e82d3,0x231a563e569a1a0698,0xaa132c1d9,0x3067a3b66da,0x3990ff5e5c4c1c7,0x1a31f764eb]
def local5g15 : List Nat := [0x69c7ee4e525,0x433d2922ea602d8,0x36a3ca12c7d2288,0x1e66c4ca3de,0xa22214937de51d,0x27b777834aca0b5,0x33eb48f2a106,0x7c7f24c150,0x35861b0033a2fc,0x28612876e4e53c,0xf4161a8394,0xd3d0e879c1e358,0x4660b53b4ee5f4,0x33271305c62501dd66c9,0xa08abcab549ee2b8,0x177756151608109,0x16fae4d54f00b4,0x17b3874d14300d8,0xde514177186a4]
def localD5 : List PackedState := (local5g0 ++ local5g1 ++ local5g2 ++ local5g3 ++ local5g4 ++ local5g5 ++ local5g6 ++ local5g7 ++ local5g8 ++ local5g9 ++ local5g10 ++ local5g11 ++ local5g12 ++ local5g13 ++ local5g14 ++ local5g15).map localState
def local6g0 : List Nat := [0x237153c29fa6729538362f02524df67c7fffe28be8d84d41ea683b21de52d0c5270a465fe46b8f1963232d5e551eb951997a908b4f528f6ff24f3e769a8952a103bda3cb,0x1c6b0418e43a64a8c111846e9773a6449f3a0aa3a8aa0c27dc,0xabeb2a7f7e05382d0e1f8f1d6c698f769db1e7ef225ecd137a4de014293eff41e0d9fe52595,0x2e86eedb17d2422b32d6e846c70f73ec291a,0x9e0ac3ceafaed84624f3648e85e0eb0e53458,0x1ed4c2a9c1de9ab6400c7ef5ee88a1241165026efa5abd729a261,0x449acd3ca2d6643a0f3942b3b58e368953,0x3c6f9225044e70ff9208761c6e13d04985,0x462572a7e915196571397cd127d2f7283,0x4bf609fbb9e79e49e3ba78a70984,0x3cc07c653e3adb5b4576023705a590b39a1772bc319f4e2bc6b4fcce2ac5fc846873a0a384b2,0xcc7e02013839e19498069389,0x132e4be23a534a6d30db66cd0c12,0x16f2132592de674999bc77e23ce36a867512a41ea08f03b3a862832969aa753,0x476c05a16002e718bd9e6ff06ecb3,0x12762576a4a480ea83fb2168b,0x65ae842be4d7cd395d9c3298046028cdbb6e29c9dae41,0x20dd832b06127c1d2eb1f902d3f65b,0xa30b4926602e6376ce67c840681b46a434ff90ab9a530893d,0x5cc230de5289d547a1da1881250c6ec8c98,0xdd122ea9ec0050a3376393527734d3ba13053e15a8,0x18d639b26731eaa4a5298906f9ab5c9ce,0x9ed7e008badd2193efc77abb6d7e,0x119f104280e9ea539c802a8c3]
def local6g1 : List Nat := [0xcbb3b62e892df9640d976f1aafebd8f6ac,0x9d3c5462d87e158120ff983996ef7fc7732f31c7568131c7f66834ce9f83639492a99ece64fc022,0x55fa92d2daf7bf2c0a87c6ecb87dfbddf399ab40a60d846f,0x7cdad71e12c41ef388dca949882ae4,0x45469a7ae3b2688400ac3bb670f52717d2196c482e8f9db054b6153a87c671,0x1aee9e02794bc8265db6cad8227c21fd4da53034c,0x2bb6bcc8db1166b739c3232d47c17ebb873216b9e,0x1074510aa24f107d2e6607f7d1320a19241373af1292f785728c9cbd4416,0x1298fd6178ae5c61923e68ae4faed779d2c04539a757,0x3f3c317297e784d0f7501c48871bd755a2feb8de4f1887cca4b5d9335,0x4952b620658ae9284bb0e2f402,0x151cd65677b453dd459c0eb57364f3d1321dd,0x3615d8421207c1f21d7b71240c8ef,0x3d2d7f4f424ee9ff3d4483eae953,0x2d4cbb7a43f09e88b853837dccdd73d,0x30c5f8d77073ca1ee1766e2d70043b2ad8243cf54d,0x4d8e5f177d148d8ec2f8342c64,0x583bfb6f52ce52266f990cc7,0x2e2be08b42daa237b149,0x18857e24c6abb759a45c64d24aeebeca220,0x84d8cb4dbe430b39378949,0x7160193efcb015db9dd60407215,0xb8d665cf18df166,0x7d92ab694ede029620df710b8452635a]
def local6g2 : List Nat := [0x6c4564fa26dfea8dafbdccaa015a84c238791,0x6a5c7aec07ff5b335,0xd8876b13610606aaa2e,0xcf757651637151670fafb3a7,0x310dc7b65bf9fd0b84a016041097a,0xa7d65a748c60d4ad58f,0x1a396adad5043b93c248487d18d85,0xd619e679b36ded1e,0x411a752ad45792d5121d,0x8a4b928b689c13485,0xc1caaff5253a4abe66b549835ce802cf32,0x11e7188910296b611aaa3ad57b140b5b5,0xe6e4b55b0a327152428a5f,0x2acbae3df1dce919ab4bd680,0x59e3017ab766dcc2f,0x584549d03c3d32e19645fafda2972b27d80697,0x17c466c35bf0b1b921f0d7d692,0xf12f932b8bab95518a93f076ecd159c2c69c6514,0x159589ff3f43477facfc424b26d9f7d5bf8261,0xd1df1f582654f31fd125bcfe83737c11ac98,0x878ff8fe37e216bac7fa32f673bf492fd79372ccc,0x1a596f974a36bbe133e877e894abc588,0x6f37d70dd48d097d,0x720f99b8817ae5d7f2d6b3dceefb693c]
def local6g3 : List Nat := [0x2494ac7cb82733ce6b,0xc14e869c5e738d0004b21b08e18c62dd46960f1d83a5ea,0x41c304784132052af560d6f2d00831114,0x19b9811a217dbfb9d6e0d73,0x9d43c4400504e5b53e5bc197eed4a,0x1f63b56659e03ab31d72174cd8337cca6d493c6,0x186640e59f292064c625769b6916c,0x32fd542bd1d04a59164,0x34caccaf3565de82cda55460f20935d830e8,0x3ab6a245a555f00435f6b0047e583de3c95f657b74bd2beb,0x69371b7d9c4d5ba128998a9e55214,0x5d341555c036203a3571a5b6b66,0x4d9f0666222947aafbefea62314b,0xd52b289e6a2f20e654,0x10dca96f7cdc2992222b65d4f89b42dfa2874433,0x2e1fbeea3e53adad1e,0x1e9d93195157238ac5c6,0x68dc6f9fd2993d5809026d76,0x1624bbc847b2171de390b48e12c0,0x165b5e9993c5c838e72e83e,0x57520d213d10959289748a58,0x179a94e633f1af8e20ccba81783d703,0x8a2cb8d6bbc5f8c3180488f51,0x26cc5d48fee77eb2b]
def local6g4 : List Nat := [0x1279be015ef6b585f44acc3,0xb5d10927f83db26253e2ec3387,0x12f7fae5c7a1dbc41b3c0,0x24e078b93a7cab36a8,0x7b75ee149f389938e532c0,0x241f21026892a169e6c7d9,0xe0909cbc7b36d2a6,0x5b6295a0ea5c08313a7ca608d3a3ef,0x19e4c82d539a6ff9c9bf9a4ac7df4225a9e60baece4,0x108a54d07ddff2a9b4e6358e1dab7b,0xbf866e0b1bd60667c196df616,0x655baeb6d69f10dfa7f00f3bbc4b0d,0x50901c5d3a3575b5010,0x1cd18efafdd18a668bea,0x74f13f706d4ff5cd6bc293ba,0x2ccba6038d87a583a1de809cac688d0,0x2046b8cefedbd10ffc2bd8,0x83ccb4ee4556522c43,0xb4f14195f51d25486,0x16207d21df66c3d95322ac5c,0x43ca1f16a892657964a578197438,0x18e159a8592f78b922e,0x17d4ce31f83f3ce484d5a8e808be,0x4aa8bdfb85d2c8485abb4b8bf0ecb47]
def local6g5 : List Nat := [0xb69a1707b1500de2e1a,0xc04f7a5c08c60d4d67c212ea,0x26cc5d48fee77eb35,0x766b9e03c0d78af6d8a910,0x91d747715c622e0e132c5735c3b06c,0x4039bfe4667ac377a550df413a45012f,0x2a770a2f9f5ea3b3f6e01b1f2293,0x1d8b0103323f0d66f9b824c27705c3ab343,0xaebf63e99caff5a02ca69a4d70d7288e,0xbda3e480c63761af4fd0ce7498b0f320518c715,0x6eb7de81c400019ce91232e73,0x55a329d4888e9b26f8e3c7d5878e7abcc17139,0xf9a1bf5b0119d7b27ef07ea3ce754,0x4205abced3a974efe725,0x7efd294757373d3248051bd04e59102bd50ce,0x113fd42e1fb17c3e2a5086788,0xccc8877f16b29944e515e2154339,0x2a00404000e3d049a288734d4,0x41622e2d0b7c03d7cc1b42e91d0331de,0x982f796a7400c423ef3db378f687b8367ade5,0x18dbe4f5122fcde1ea287c2,0x328efdb93a9468f76063ae8eb97be1706815e314a,0xbd7b942833aa54df,0x43e95551af83b1c23621097573]
def local6g6 : List Nat := [0x15f14453d53a29b70d8,0x10a6b798fb4910b0fbb643b8,0x60c318251c52830,0x10fab40b4b1d18d,0x2661f9ea5fdd01d43884a9,0x3a722f8b1a1c35198,0x4162d93c7e5aefc2592f56333,0x137b38a92d4e9ba1149795b2cb37a1050c6b46135a4,0x64b40502e09e8f55c5bc2bb7445f17dd63dac68146e77b494db33bf27d121e566,0x9cb5cf52044b29027096b26fabd96080f,0xe11b2ce0eb65aa2b89360d09,0x11b7fd827a4f65b3172b1e4d6965a17d9f1c40645f83fe,0x6d98603992c9330c442fbb0062dcc272afc,0x132e0b1abeeff3877f7068e8cea80a,0x2c56dbf48a59c5867303fde5b3295,0x36a524f7b9b5b4ee1802af525f1883d742625753896977307272c9b1d5414ff0492,0x57de28246bf0a49d747bcfa6a0495967f4da01fbed311c8,0x10b62995042554e63035f19c3cd3d5ac,0x13368aa307b16ebc10afb8e90552bab,0x15bba98023c330d17f60d,0x9f4791cb84ba3907a1bcb340ac78be2d4db482,0x3508519d35bde61dcc3b54b387f0,0x8a8b54bdd94f99d450bde864e18f7437,0x10b8dbbc6f67b42e691c]
def local6g7 : List Nat := [0x5bb9af2ce1b65b82197209eb0e11ebed,0x8a61e62a17096aa942,0x8c5b27894c5043c65869ffd494e1ca73955c41a200a0,0x1617977e89410869ad7516215e30f1dbca39a,0x2071f31a26931949357e7e8d031c4c4aaf4354832b,0x260d973cdc4ae08e486e4142ff15645b,0xc845eef9984caeaee2d7803bf56bd73f644cf502e,0x20ac3ba2636771d2d68c02bd7878b016,0x81f312b1709f9cefa6a0778b9b5326c1432cfe53b,0x2bf35c7dd62c194ce12911394c617c38ce0d20,0x17b442e95d468c8b8e56c48,0xb93e74219242857a3bf3b150b8f46d505ad,0x9ba8139883405233fa762,0x1d78dcf445a2fb5cdda630a70c,0x4a90dad5867336dfec8cbde5a704eb4b28a,0x5a1f065f48564a8b770b5f,0xb2546197878fe928f324b2c45b664afa08c,0x359fb5000349e4944b2,0x10343e133008803d13d,0x9d4786beea8ab5b6bc6a55e1df1c1a6bff6e1194d31f218f4a563,0x11cfc73e48a08974933c9938878a48,0x1a89a4f1fefc82dd81e12a8f6d967e48126e5496,0x28a950fecdfb98257a703f5eb2cc3c3fdeaafe6a2353e,0xcfec96eee56516e44a4c87d]
def local6g8 : List Nat := [0x53a2106d39a03709c9d502c8da,0x6d8ddd1f087e6be4bbddf548cdf0ef66,0x1883b7d8a221dff7d697ac99ac06584fabac6b,0x1ed78e03c506bd38ca3ec67cfbe68d1,0x27ee7829b593c03a4b379768c88e,0x1e18c91f6486bd32f4f2630cf,0x87536ca970f7c66828c0e24,0x1220fd51424349b75c2fd1ee3e3eb6a2,0x32d73c3463cc641740014d3d3bd,0xa4f5d0b25c54497467,0xb6a16356885256f55dd6e743100af84,0x715ab8666cc5d447c360eb4db4839c4ce2,0x33baf13c4ee998e196b80c31,0x9174d8d17549f9ebff05a52f2c64a0ee8b6,0x1011fc8b9ac9d996f56,0x240cc6330152d2d55306,0x30cd8261535ea6ce4b092d951c7,0x12e5c0965cbfbbe03f2b3a8f43747af67,0x26ec2c2b822ec3c2367f46ab0d215,0x186f4853300d02494def42,0x45d786e32d6f0c57570980e2d,0x2db890558ea8039f8eb75b85882e62,0x33d7b9aa69a2b3a229ded02d9896f4466573,0x3f1cb019a47d6b6ed4429d4ba]
def local6g9 : List Nat := [0x8d3a1a4373e5490feab36af,0x13576df53684ab98ae79,0x8e50be53f0c9b5363669a6385bf1b0,0x9f24b783d3a0684f16b732b8a,0x1ab2ad595aad6d0d70f118a08576ff18c04d6a26426c842e22fcc,0x2b28c2488115128ddcb93b70a67e930cf5f831ea6c,0x24d79b8d39836cf8a91912fa1916fb,0x3f31f2ee8dfab1587f7e51c695b,0x933cb2fb9d002b8aa6dd59fa56ea23ce27f4389ac3d1206bf5,0x15650db214e3ccbe9d2c9ab278040ac09,0x6981bc0055f0614ec899a,0x34ed40f704028eca1,0x58e4bcb2104955fe9fcaaafa94aaa7314639ef6f590a8,0x1f61da015f8867fd960e1e826668af2,0x12fec51b964e7dd898649647217c6ae8,0x8ead32441d9ade6dd9,0x17d72a23ab2574f3a54648dbe8f8,0xd3c0c010fe148b5bf4f89,0x103b83c0cc300e793f95296c88,0x649d512a450f5631d50ad,0xf78a398a70e206527eea221ebf2aad80294e824f,0x390b68bad18bae62,0x4afecfce3896ced540ae41ca38f,0xf47e2f320848c849cb1aae56f0c3]
def local6g10 : List Nat := [0x25840823733bc3a2fba4245cb0291fa489afb34be1d01c,0x6162d6d1d8a274d3bf56c4e9ca01,0xd69ecd7e6cac50672f41474a0f8a2cab,0x23647abf8b9b502744be935ce34,0x138b6a402bf532fb512988eabfd,0x31856058494feb9d44c86543b,0x3836dcff507db8d63993f645fd6db6684f1dfd46842d,0x66fc7c586a4ef2f3f41b,0x2b49314390190d2,0x61a0d3fca7906bab23,0x210490dba8bb75f4,0x1b45b8dc41dadb2f0b59,0x555538e24d0c2acb64a9ca533a9a7,0xbb137e32be22bd42839f0f7e,0x16ddf33a84be46fd1dc195c0217a0df0,0x1133657e88749a044edb9315a2d85,0x4a7239c7c4a90bb5f02c8c,0x2d92bc19627d10ff387765267d1,0x788f3f31e534873aaed323,0x1216875452f7d1bd73a9144,0x80c8c5d6895b4d749e8f00e1e,0xb00d64754d4067557c63095d,0x1da59b1ffd3e107f6e323c,0x55e4fb784cced7be978ceef]
def local6g11 : List Nat := [0x3842d5c0031a69e9ef90cde204165c37eaac,0x22d64bbe9750dc038512e5dcf63a91d6ee072c741e,0x2d63ef6ab015479762ffbf76c505a2fda8b9,0xa163440507f24bf241a7c095390,0x33d539b9fc3cdfb7cfaac0c5ea471d1c77360a,0x12d09ac8c971f9a5a11c29146,0x1951e8decda47acb806a944e1b1d6c67666c46,0x919ab23d5e358cf7eae56ee5b,0x30ae9879a6b2d6131f97887a,0xa634de9c186fc053ad50e,0x1f6232846bb988af,0x595d04dd52a2e626d3c7494a233a4,0x277ab6ac2c5d34b6ef3b388b11,0x4f0ae5ad733b7b31d91d6,0x3f0299c524acc37,0x99598111f8ca15d4e0d59df87b6,0x532f3eeeec2d611,0x1becf13de49535f,0x12bd22de79640256ddf72c42d2819c074c1f2,0x108ea59c3868b276eccd,0xf61192f4e1d2c628d332caf905d,0x9ad210b9565cd98d83ea38fbc3129646fc9043a371bcdb41d93b256a408,0x8000cdef4421384afb,0x16f77d30564a0d615]
def local6g12 : List Nat := [0x9bc14e201dee734ce7604bec5f3f39f,0x212282010edec3e71461fb13c61d47251,0x294d4140653767c60b3076d,0x1e24361e47bdf8f66229a8ed1a,0x19839cdc9d35ed65e03093c2942d68483827b2b1de,0x2b5f987e18f76dfde58f0fee3a,0x9fb0f51ddafb40d,0x18ed97311178e3f4aa,0x4cd8f3e2e669f3ff9086c,0x6d8dc5db2ed1b2b97ee62d2f0069579,0x6ce05e634b48bdf8b9ffcebd,0xce1125466c99e0b4e123131775e649ed6bd6,0x53795fee15e437532b,0x4840e11ec9d9c83a,0x40d0847ae5d6fad583,0x1f6232846bb988b1,0x26489fa6eb804b9416b16,0x702e7bac9e684d69f377389,0xcefbb0d2e394f9,0x3da9c0e1263afb7cbb62a64,0x2b6bfe4df1e1f374,0x548c2dba871c09373330,0x85e6c8e2dea6aa5,0x2ae0c80d267f7226]
def local6g13 : List Nat := [0xe1f63f2701954906,0x527d0c2aabf2dbabcd,0x12eb1b08dff0aa59f750b57,0x3ee48d1eaf6758b7a38e3d2a1313ca797,0xb175dac2dd867c46a4a9bb,0x1356237fb9f91adbc,0x5f06222e136c7a0eee9836cb869ab,0x601de5eccc21e848c6fd664a1472,0xb8481a537ca11934764c,0x1e1eb3901da99889db,0x27da3f443f25d2f3c0,0x56b1b2db8fcb4e6bee3b79d90802,0x544a7504108360a76fba09dec7167efaf7af6ed0,0xe689f22dac92aebc5b5d01936f9,0xc1527b3ca428be113c8767e2d9946e115a565532bb974bc2b0a,0xfc6fbe239c7c44af8e83caba,0x328f386a667c0c428978454d67,0x5a47963adba92c85a61677,0x12db62f20e7d7188f2dab76f2,0x4818c3ba809ff068c1bb5cd553c901,0xffe713493557842ab234b1c70e6,0x9e47cdf6f07c45227ef,0x71a2b722a6a1643b6ce5b9e3aba2,0x3b5da868970e68c8c36bcd]
def local6g14 : List Nat := [0x1f058e224ce342ec09e94bcdadb0,0x13f004cdc3b2396bd00fbe7680e,0x415a10fa5d4789db02c755c793f33096,0x82173d31cf59b1ba82212c2ab15,0x2a58cee5f9d3869b1435af94,0x35650d159ab32ddc2b2b8fde8f9,0x1ec98bd3c1501cb3924add7285d20b7a8c3,0x1b86f3b34821ea25990b1e0e10d9d2462f15ca44cb75,0x3a36534ff09cd31ba7322e13080a,0xcc2ed3954bee723f01e892988,0xc408ecddcbdf8955437b9e76d,0x2ac9ff77e8d23c1495c79c9214,0x4c327041ff5bdba22e2af4cc42e8743c,0xbd91eb068dfa15f9b7381c20f8c13d1592,0x36c509c34c516bc4d548abd,0x145f1e463d8d333c,0x11791637454e3296fd333d7c83c,0x50d1ac346bf6886502bd3ee,0x39f297d99fa909e50d6c9,0x356216a98265cda3165f,0x4166a6fc09063e29004d117,0x390b68bad492951b,0xc0f3b9ab01b46f3a,0xa66c19ea3f534db]
def local6g15 : List Nat := [0x8bee5695620715dd,0xcefe6403ed5cbe9ac,0xfa7e4a78585daf14df8,0x1d091326cab39ffd0623921e45af3f9,0x1768383922d3eb598686522009a4,0x1bf6d0c35ce86face3f5e2b996ad381,0xa839ccdb5339b0f0b44da339f02d52,0x6c0d33447f0e7a1ca38c7b0cd7d5f0,0x4fbd72d5e330d8c3957dad934a9,0xa1abf59ce390264a77b,0xa090fec0cdb2876a1650376a1,0x8080a6277f3dd0ba6,0x7aded1fc8e64bd6332792e3aff6,0xbc9757f8f35fc706708ae44,0x6562e939ea6e8238c2c86c147f,0x5db8d34e32a41083637eaa2,0xb2a8ffb4a2b3f8724dabe0ae122d23,0x3c1be13436ccd68dbae2391b6cab0,0x6716bc163c1a21053f9bf40a962,0x227d4c2ad5cb4a550ce710b,0x49084e9dda28f57fdc38ff2bac826,0xe95c0cb4617a957a7b46ca07a13b3750c,0x3137a7a8b37eada792432ea0,0x5c0c3741c8bb57693c56aef6990dd1d069a258de812d]
def local6g16 : List Nat := [0x41bb3f8ba4cbdadd85a6c0be738bbd,0x1f42330318d2bd883a961840489,0x12f65e697874846e5aa113f73f,0x1708b4ab20a101b30d1431b4d4c53603,0x414ea9060839ec5fcceed9,0x53806db4fed262113cf45ace66a717,0x6e56c6c53b57b11813f1f9,0x102a5aedcd90ad60baa09,0xe38509d84bccdaee1f1620,0x2a2782932f3cf3df0ef6067268785,0x4ed2f3769a6a59f1117,0x8600ee64fe41006dc2,0xdb826af2c20f554a24c606,0x7540fd7213a8cf36b19bfb4259,0x32b2e1724da485e86484e,0x3a2d894bb8e11da23afe5a1e7a2cf4e9142691,0x254174817dbf1446fa9b402a592,0x1299e5d92eec4f61d,0x447357fac5e1c497433,0xd6030af054efa80cf5,0x1e52a848dd6761c22a6b1d46f,0x65441daaa17c0d0162aee,0x160ee7acabf43d5c305355,0x17156770443d5b90f6]
def local6g17 : List Nat := [0x4adb4bd4d2bb0eb1,0xa0d70e962cf113e,0x219020470ae4faa919a8bdd,0x1a48668da30e771494dcd7b4de08d68,0xe36bd234919c877fbf725,0x10356362d37a4df60ed40b,0x398640ffc8d53ecd59714,0xbb5028783a4c1b19837dc8c5b,0x726ade8f13a9ba17922f39,0xadb36f60d47339ef450,0x12d4adb40102a8f,0xb3c68f492f1a4afa4ee112acf,0x1856183c35bd01128a13e907f627,0x40e40ca6497d2558b4c9aeccce9,0xa4ca6c1f2fdc6eef08f383fb65c,0x2c7b5e19e429015e53548de8,0x9a2b167d6481ad3460e2f66a755cd,0x8e389f52e6541fe28ef64,0x1e2374993493ae44fbf12dbc3e49b5,0x244efa486b862953324e7069154a8f25831744,0x3afa96bf64e435699493d34f00a0eef297379,0x5ffe8492c4970839480960a414652b3b9,0x697f2e708d58a74041c9b630,0x63117c841aecadd50a5a1b70ce00f8d721]
def local6g18 : List Nat := [0x8e7892e3a7f96002da4f7a8354aa18f42c,0x6d4889336c4fb8b8ab105590e09,0x5aae051fcc7dee5ae6670fcb1478,0x12c40797784abad19fe29ce8b524,0x4758209398978f1f8ce8,0x66d76391a756bd40628737efd1e6bd7,0x137a830d6a45bfca7eecb79fea6bc7134cba,0x6f3db88c0ac778d279a9e5a2f6d,0x2b0d27c5a2ab8eccd30,0x2f86544656a075a9648389885ee41cc5668f5404,0x2bb0d7ba033c9750454b189373,0xf90942aa387f1288eb7eb85,0x6437a28a70cba17fdfd20597c8d4,0x330a6c33c19e77cb19ff46b4f,0xa4f890729f7aa301685c61469,0xd527be07db5cabbdbc6c091576,0x89e1b034944c6f2d8a69c93d,0x3f82c597d815f66e264f597eab537c05186,0xcb2da25c2374b38f18d82,0x6b4b029de6de2d5205d321be77adae,0x226a6922a2fdc8a7525f9bdeb6d3,0x582730508492f81afbf9bfd1c8,0x58999f10ac62e4ab0c152414d8142f85,0x1777a9e4462869c840e505ef673]
def local6g19 : List Nat := [0x305f75716b6712dfac5f32a29,0x2f9fe52b85bf9897ef683,0x8c640597c2b3ccaef8,0x1d192f59c81d9e60c7cdfed12,0x148f15d5f2a4690ec,0x2c5ec93043953c866a98865495f57ea697aca7903ee,0x70861b1ed62ef72cfd0e96ac47,0xd423105bc41b9993794f304a,0xa128ef432cf78cfd37b87caacdf,0x127969bb196a91a0ccf630db309,0xa2c05d0a1266131a6746be4,0xb298cd348f82289c9240,0x7161a92c198e777b5a7439427ad305c,0x3317d64951fe049815511,0x78b6b6c85b040f70280382f19889c0,0x10e11edb5467f45d57616,0xbe5c8b9c11136e538df8,0x360bc1110f7d928cf9a70b71e1724,0x1c6f454fa8b669e3f92d29d3,0xbc4c760aa52c067be7aac8ad184,0x1ff4d3a2e8e12d99470d3659f88f3080ebd387cf508968,0xdc53d4b180436ac502917e374b1,0x50f05a9b266eb96054c7e7e3fd89cb,0x1619896edf8dce9706517288]
def local6g20 : List Nat := [0x912274e0569d8f5f2,0x2bd229de14edeb3088ae,0x2a86db9caaa563ea2709a01375,0xe5f976c2b82ef7a9e68c0f8a83f,0x5bea9a77ddb6f90f57c9aea1f2721e,0x72b12eba0540fdfc8877,0x6d924afe0e38a81d8181c9a25415,0x88209ac75ea603ab8cf48c5950afd,0x226447b3acb230e04e8555780d33,0xa778d6ee9dea72dde43595,0xf05a88f6bee724d6bdbb03550f03,0x4531e91d74f00ce97345c10fa10becc1f1ad,0x3d3ae546f26d1098,0x18dc567ee2bd98643e8d9c32979d951509f7,0xdce9fc9f4644ce4,0xcf9fe0deaa6306a6f4bdb0f2,0x2add60261e2c5796ba4ce91f1df,0x39c11f0d067778f911ab6a7c81a,0x309733706954b8c,0x34fff37903efc4efb7662ec5db558ce9f,0xe2d5ae680189a799141e52a9,0x1194bc59f1386b31,0x40c9420031ad55d6b5,0xc71b449fb8a246f1cfbe04100c9ccb74fa]
def local6g21 : List Nat := [0x1a1ea1c2f7be51cb,0x32e8f48a860d52f121a81af8fafdbd6db584ebf,0x26f87e1e38ddb7b6f3f9f5880ab311dcd9003,0x18437e95bffad13d05b38816e91,0x89309b4da39e0eb31c985d2b1a9,0x251793d61791d16e7584fdd,0x344b2c10b2bf7ddcd4f5379,0x18505332d7d92c1c427339d28f253,0x59b930989cb62517a11fd8831,0x1a2b45181a8023f0b6f6f07f,0xace79901d842f678b,0x1100729369ef3a,0x309788ad0e8ece9e2d13a2aa8beeaf1ec,0x58f206cb2a924bff29ba2b17e,0x139283cf42972e1cdf47a,0x5f6af74e6ba1aaec500fa5,0x1edd3097e48a769e7e0164dac32,0x33aaeeb066aa250e454884d,0x431533d6b70be12f1c26bad3b1,0x100f02b75926018349c,0x1bdbf2cc472c896698b424f96d9,0xd8b9ade08f3d9e701624,0xadfe396c5f47a6e9d,0x24bd5aec1c8d123]
def local6g22 : List Nat := [0x12cce58703da852b1,0xe2f54a42ee4b248ecab9de9b489cb9f,0x15375577cb2d9504051a9ca2b8e,0xb61cd81178db1a083132b785bf16d53,0x6658cbfdca32a625f5081fe5b16f75f5,0x32eb15d40034ee01e5e9196b207,0x12b1edc3a2c0202eb08f27936e0ae7ba,0xaec6c378a94584318752d642134b1f,0x1dc6b7892ef4f92f556f,0x722877e78d6af78,0x2d45f4f74679ff85e9a9f5,0x5375b814c12b8806,0x8617fcbd9ad5a93e2,0x102b48a66ec26b84,0xa87b9b5c6e6afcaabb,0x2902eaa661cf138,0xb10be92630ac00d14,0x3e1f0b25f2e2ae0,0x79329013621568973f36ec6a,0x1246f796fa2d329,0x1c70e2fbd11edad768cc,0x86deec3dc8d1f190dedfd7d342,0x63aa0b990d2ebd86fbb,0x27e936310c9e4d27c2f65a]
def local6g23 : List Nat := [0x1234ff470499bf9c2823362e,0x2d1d50666ac302c9f70cfcd4a,0x5ab754abc45bf563,0x3d8b25a5dfa5f4509e2,0x4c67f07898146f4acb3a37248,0x451e0820ba8d3325deb62e84f,0x2addefa552569626b3f,0x89acf8057ee08deab0f6b,0x75c190b1cb7c62ec0d,0x39e512b4898cb5804d1c,0x4807a00b9a8372f3339c,0x252c4fe2c4ee9081146c5ccc6,0x496d6ea1cf0213b95fae13cb7f,0x31961998802d48971065a6960,0x6f1bfd00d6c6b8c6838,0x76d0b8eefc293e,0x127a7d7284013c2d0a2f5328,0x13430698ea4e60164f97e17fc877b,0x16171c36002650231b3822e96f7,0x43987d8dd654e88,0xadfe396a67261f6aa,0x421d0d499d3eb0ab1b2971c04f15,0x28d3b4ef86eef9cadc28c8,0x1a48a0f52988828]
def local6g24 : List Nat := [0xa15ab2bafa124b6b638716c57367,0x74d1098b5d3b0048927,0x11d1458d5c23b6ca1,0x8538ae21c764e724405225b2e6f662,0x1f669ffb1f4712bbc1f98d31b4,0x106600cec86e912fba0024e1d69616ff,0x30e83e914625917e00ca16c30641b908d8,0x11da6fd976a1a59476d1c45ca98c18,0x1b6600f4bf0a09fb3f70abfecc473cd,0x4d281b7aaa90b358f9f3ec63dc8fd,0x6c438608c5181aa7096a19e4517d,0x2fe6534df1e6789,0x3c0fa1d5a16a6281962ab71,0x2f7ff4167fd2097ff3cc0860,0xb5275860155909e2011cc262409cfeeea,0x6c8be061903676,0x26f2102abed6aaa7cddb32d,0xc50ca7849e1e47688b08a13,0x1970cbf3e199c0cb92b4e,0x8e076bfe344d312756b02,0x216253c4b348735c1eb408dc7d66b,0x5a25364ba2648bd2274dd6257107e3,0x4e53c9d13bc305b1e4,0x170524a6427ac9f236]
def local6g25 : List Nat := [0x3259adf9f362dba008993d2d589158ebb,0x12bb4a735fca682f725,0x15fc025071d05657b92b5,0x1a4f58cfe09be1eda63e4fb27b5,0x6066450fcc3fb4c08290eb3d6,0xd19e0e2bd669641,0x7ecbb8317b632990,0x41d1812890c14352ff5c153e,0x547d551bc06522e726a34,0x431b2b01e056e53,0x470ed9e11fe375d5f65cb39b,0x23c19b2a23a7becfc6,0x2f6d9f5d2b22ece53301,0xb3ebd571653e490bb,0x26a51c575646f26fcefd,0x81053f18c99834be,0x1df88628a2cc476fc,0xa43fb993b5975cd83,0x321f40ace7847b0087b,0xb14ca426a97fbaaad6a0cf89f2ec8a0,0x3ad9ca728ab11592c98797,0xb47ddae7d48ad413ededde,0x77be3c897c31fcfae1b,0x15cfe468e34e8e290b5e05d4870966]
def local6g26 : List Nat := [0x3ce5f5bf177a9013fd,0xb47ddae7d48ad4144c966a,0x2ed9459f4d92cad4c5087dc8c508f,0x62e56da5ec3af3c6,0x3515e16f45e92e86218e7f,0x20985a578b46a78114b0,0x28cf0e9729d6a1023b38f36cf56,0x42ddcc66e3a969d1,0x13630bc2832656b172caa0,0x83a9e22fe234db1fc22bcf2e,0xaa2f3df33b1ad75,0xe2e62f8fef9363dafe6,0x33e1d1d4e921f3a81c52d10a0f,0xbaa14cc47b0a6b802774,0x61ef2b0d917a618195a501fb479a,0x18561e56e3081d132cec2,0x8d6aeeb96d60c2d69fc,0xd81d5416b7ba6a8b5905c,0x34622cadfd324a0c,0x66874a9ff32b5a6,0x460aa693b63c6e7e,0x76db60aef8876db6ead42,0xc4a3cb9656f5eb6dcb151b2,0x84a9a4cbb4f5d1d9ec93d1]
def local6g27 : List Nat := [0x7bdac9bf00689561eb20,0x224c29e62d760a0f34,0x5873946c791f55f280a,0x922b525c4671013015,0x33e15df35cbf974d06,0x3716e5093d64ad118e,0x152b8556837f0e06,0xbaa150c0bee46ee74809,0x3c24b1a07d1f7bcbd7059,0xbc80b78b93aba2e2a9e,0x77f20317cdce70285e,0x293b1980caea1bae747d3,0x215e9f6ac1e06fc729b1,0xa5370b714009276abd,0x92a61928a82c1f185a3177,0xcd0d6db517d2c0d74023c21efad03,0xb940c4675c40eb9,0x3a82df88158e63497,0x4c613633ebae5229d6,0x1fbbe2bcddacbd19ecfd5ca299d,0x279ddceeaeafc7c34e9d72b7,0x23d3230958d7f03126f,0x3e0ac0cd4d499832b69b223,0xe14e2b867cc0887]
def local6g28 : List Nat := [0x779a745c92d68145b1d003380,0x2cca4903fc377e3578795,0x576bd9e370234c431540b,0x5b31e7bab181c3471d635290,0x2cd6f9aeb434a14da8ba0d199,0x1c98550514d876b,0x10b56db93033296ee5c15488,0x81a5345d07c5ced83ea55,0x5d64fbcea1c836cf2b7c,0x2bad5e1cb2138614f43c946e92,0x1c070490881025aea13,0x6fea3d8d4ca6908ef2fa7,0x9a8df43b0ba1d6a0,0x15d3f40c2f96bd0a70cee6,0x13a3a1318845259f12e1e,0x78725ebeadc37f0a530fe,0x5ef95cbee659d6d4a8f02,0x1eb0a40bd0f5019a19653,0x343bedcb9c72d512ff4f278,0x2f7cbd4a14d897e651dbc796ef2,0x2588edac6d6596f827de,0x17769ffcd2917b,0x66002a3144d00a3c62bce8a,0x21b66475a8333357c]
def local6g29 : List Nat := [0xe52935cc2fdd369,0x394a4d730be1481c,0x66c9f246f51a84bdbeef6c906d4a4b68c65b784e1c9f4c4e4ac55083b11559e6f3,0xf6be9d97283ca66f1b119aa2da3eb5b0,0xb4027fe9471dbed6e0caada,0x119889e62a5cc5fc2ac88ab5,0x6d3a30aa54813696e77cce13ae69,0x54b7c5c3c9ceef771c481e0abc47831cea7ff,0xbe1214394a0f5ae,0xcf0a095d889e9ca54c6c7c5,0x3a3df2fdfa5ff46643ccb866d63,0x82e12b7da34343be92c2daa0a,0x173eef49821e38ee3f6b0e,0x9a812554255a3852a571caeb669a8f0c60,0x64e269f2bbf5e8e7168264583d7cff9ec688b,0xddfa2244e65d4b477204,0x7ea04fe4d30a66026b540bbd,0x2db7332a5f42b79ae7c15211,0x136f5ecaad8,0x17a5d692fefded24aa2,0x106c988bcdc784c803cf57,0x10d1fd510e6e74f49780f9a,0xae5746d5e4e8a6a2e29ee,0x18bd149094884ea505b402]
def local6g30 : List Nat := [0x211abb9acf1090b72e,0x963bc5294a448b5,0xd30e26d5535,0x3907d0923c2a8272e4bfb25ef35,0x5f77745796d6479cde5ba29ba73c17e8cde,0x515a362823730230b7,0x4d8142d9c82e9c7a97c77e05010,0x61f31d02e05716457a7a4b35de,0x4bab510614d2ef25b0640b6875,0x19319524788,0x4a703aba7cc10edad72746930,0x3290a765883c20d1d3e3,0x2380c81d54b60,0xa0988be855fedefc51fe,0x23d27fab8fda2f54495d,0xd07477016df3714d8d31f8e2d5507,0x1b41512d22ccb5ff59217dce0fe37af88,0x129d1b339a9e685b9e341cfe00616b326,0x10dcb836eca6ff7310bf1b56b6695c6,0x3ff75459a0224b43f6390eed0d0f14f89,0x61fadf12ffbc25c0567bfad148fd,0x233c102a95abdd5c21f22d9b37278e5a,0xafe13cc348b2a8193586990f461,0xbf717316ed6d44af68e63dc4b8b]
def local6g31 : List Nat := [0x19aefe3488e398dc78e29f9e0f95,0xb3092e6bd282b4e,0x13cedcebce1ac960af1c104b35f531ef,0x563b4f67224f23717a3f4f22f,0x316dcd1518058386df037dcb15,0x23883c0795ee2a9cf7a494f4,0x398a0c0fe1d852147229,0xe274ab6b3bc9d3260,0x194239764e20,0x223c112eaef,0xc87aa03a8c930a,0x42d38d0e434e66,0x46a34d2b862c99,0x79ec4f4b8fd6,0x227b8dc288b3f,0x1d9ca2bb9e2d63,0x744793a85bcea2f,0x941c998cceeb3a,0xb79525bc51601,0x306fb59f02acd56,0x1dff8cbc7d085,0x301ee5b2ecf45,0x6824a3d4d4300f,0x24fea12ed1199]
def local6g32 : List Nat := [0x25cfc984c8c5f,0x149ac3f75b10653180b18,0x27eb8ee287c5,0xc7aca6b712a6,0x1640aa4e39af67e,0x2419d8f9771a261db14c,0x14e8a3b22a9a0d893632a14,0x7e0854a9aafcaa4,0xa88bf326fe6cf6c,0x57b5d97d1419,0xe0a2926078850bd4176baadea,0x12f20b6b05456b33b6,0x6a08403f0dfdb1ea21677f23b4f2949188,0x94bdba00473c803e666be2269ee444da0,0x1a8b733f83b76384a89244f5f95bda4a6d,0xc7c19504120be0d293dcd89774935483,0x2f5ab15740544fb660444c5a4e7ff5b5,0x2c33bcd7988c4,0x2ee3cdb30d6,0x10b5dac4da51759b,0x78ffcafce0c7909d04aae9195829174,0x737d9a6b8f0c0,0xbaea08ab8a,0xe2a788429]
def local6g33 : List Nat := [0x212597f6b8ef0469a7a230ae9f3244,0x25ae8a94e816b59807d1dadcc0b1a5,0x14e470882c4f3daf9a9fa7034604d008,0x26840a0a29db97c4a2a,0x703c9d09fb06094670e2ae395e8f411b2,0x3e58a82d538be4,0x1ff6c002ae08c3d661f2af48,0x11d79393abaec1,0x384add28acef7,0x8752019941cafca,0x9d3a2d06fcdb4,0x559a7c5721c,0x215441990e58,0x1b7a925770a8,0xd4f76a2357125,0xb045a60430dbc,0x12487be245651a4812c9,0x3639c135c2d606,0x503fcf5c51b134fd,0x9368baff42a,0xb2288b5a947,0x43dfe9f40927e4,0xd1c6ffc1fffde9c1dd4cb3d8,0x5aa2d1cf41f]
def local6g34 : List Nat := [0x2adffb48dcacdf,0x30d949bbd19b8a3254aa,0x4cb7e9f3bf125b,0x50241f1bfbf32617c03e93de,0x1f65589561c690818321a,0x4d81d643d28f8,0x1465580bf4c6c,0x26df1165106,0x3edbe539b7c299390100a,0x282f8e54e0c7f,0x22aaf528530859669,0xa5ee0b06cfaac6edccae168edd1,0x2c1ca0ecd4e339c7f81192,0x1e93f728a4b84738192d0f,0x2408c2c041652cc079d1bf,0x10622fcec34,0x132dfd7a907c0,0x2aca23b2d0cd,0x5f5bcff1f38d8f,0x8e515e28fab411,0x23238d934b4,0x18a6ba6a77994c6cab07eb5127,0x42692a296a34,0x10905a5ae975a7c2995]
def local6g35 : List Nat := [0x11881fa16edcc5b,0x332acf68a653adf7ee1b,0x178f666c2e8b,0x2aca21f710e2,0x11d28ae8fda1f568a,0xa0dc76ee90f0fd,0x3960df7c0c5dc4bca,0x123d024f8dd4879,0x35decdf90044f7377,0x22170a47a1f673d6,0x25b0be2053bab54,0x5b62bc6fc8f6583169a3a3e276d614ad,0x5f8a9d147a4,0x23f7826dc4f1b8,0x4ca05968a476e8ebe06411487d9,0x3d75ad2b911186bd,0x1cdf90562f6fd9,0x170bd451cf47df3404f582573b108,0x2ee388abc6219525e8c8,0x80a698d35da394673ef898c,0x61ec692f838692b7,0x8130fda73b49bd5bcbe0d1a1,0x11ee7abfe74bae10,0x69b5bec674c14]
def local6g36 : List Nat := [0x21f3555718f27eb41,0x3c12e8932a975f5,0x8520a9bb878ffca9ac80ac4,0x51c4265473210,0x575117b850028da1,0xf56aa148775557,0xc5729e5e81b0b39e548edc,0x938dd8c83f5abce,0xd52cbf1c45190cfc,0x7fce6b0a8f4,0x465de08bb798775,0x586b852d4923,0x185270c191a9404,0x202ecc4d42b1cc33,0x1b7ca978764ff947b,0x1b76a3d41bde3534,0x2eeb6dc9474156e74,0x1ead54290eef4e4,0xe439caf27ab,0x1c83ab9e67ec,0xd36b6f74a73ba,0x4c5ae1163ea36,0x4a958e8764db1855362c66473ef92770,0x7a18649f879f52fab958e3031]
def local6g37 : List Nat := [0x6a3473c81fbbbf89c4b5901d6bc11c73a4,0x25c754728ab506fbfe2155798c9e,0x1d9ddec980e5b2271c65aeef12,0x59d7d1e9d590854f0cbbff42454e5262,0x37269832fb2fcfa3f5d6f490d1,0x230774bf7581ab5ec950267ae8f2,0x5d897932deaee9bde9893c9,0x1a1cc607eb55127cfb7fea96e7b2e1f,0x10b374ca6853c1dc23bcc2b6a8b4,0x30ff8a19c65a4930cc53e9614e71065682b,0xaebe872a43eb7a06ba48528325f0a4,0x62db5317fc3c5b7841e51c12d6ac8e88,0x6e069d9858b9bb9f1929396bd30b14a30d4,0x87325eab4a470ca5c2d7f12a2,0x68169af41f893a645bec75125b0ce036c61,0xfe38e7b48a33de231a95bbc5d1164c0d00,0x23ba6a02137d6440268294503b,0x1be7ecf8bcfad2c34c1712364d5682d3ad,0xd669b3dc2699c42385a0a268b53,0x5ca302edfe050778cdc93294ec6c40c34e0c7d,0x165796d7c410b9264a1b,0xbe9d9498510ba8d4f5d,0x45b604a35f06e3a,0x4901f6f62fc2]
def local6g38 : List Nat := [0xc7b28cec50f3]
def localD6 : List PackedState := (local6g0 ++ local6g1 ++ local6g2 ++ local6g3 ++ local6g4 ++ local6g5 ++ local6g6 ++ local6g7 ++ local6g8 ++ local6g9 ++ local6g10 ++ local6g11 ++ local6g12 ++ local6g13 ++ local6g14 ++ local6g15 ++ local6g16 ++ local6g17 ++ local6g18 ++ local6g19 ++ local6g20 ++ local6g21 ++ local6g22 ++ local6g23 ++ local6g24 ++ local6g25 ++ local6g26 ++ local6g27 ++ local6g28 ++ local6g29 ++ local6g30 ++ local6g31 ++ local6g32 ++ local6g33 ++ local6g34 ++ local6g35 ++ local6g36 ++ local6g37 ++ local6g38).map localState
def local7g0 : List Nat := [0x2b46780103dd41851152231014062a8125fe2c6d77ff1a2471c660519281f04464ffdd896ea4faa2c2d122460d7889678cee4d8a8640c149c8471ce596f38bfc1060feac9,0x10320d395cee14709ffdbbb06169f92801fb1747e7297e36f601a59a3d32a749b35acfa61b8ed47c2afcf7d22265409e4b14c2c576d28,0xbbd00c3a3ff8f14c3c4377957b7f5037449c58698811ece5eb18f2ee5be552365f3b5989f00d5528ff6cde78dcc2de,0x1696045eddf8ec4c3e59149979995c36d53e147bb301bed3c9829bebc339984c0ec7dba5,0x9b5c9fcc57be650e0feb8fcbb896698720accef805562e694ad1f73a112b129ed71a4424f4a0dbf0fb5e2a43dd45e750dc5db4846059a3bbcd90,0xb72e13e16bde895e13e3344df5156d0b14698ca2a6e572ab08569bba889feb9bc33e17765768a4df071627,0x573ea2b7e391f254fa54fa1f5df17cec13f9fc5bcadded85d57,0x74038870194ed609e17039a4f972089245e570e791b89031c9dcb4d3f5ada2533b525d0ce6b3e9,0x13d7366f27838965d0edb19d42294b8637108a40e34a63a70fa55a37b23a5cf47ea70b32952089f207516307a8fd12d,0x562d1b6333e9131983ab1cda6692fcaa3b04438961be5a1d137a41149ed858fc2f5839e04876642804873e84a9464e,0x40f139ef1d8191ccca664bdc6666519ec78afeaef3bb7c6b13687a,0x3834e02a0de6a3d6480aef2daf1c05a2ca61e1991c83161f9536c80e1050ae8,0x272d5ced2e7a2fdd05586745a1135419439e14cd4f7d57425ab71453fa5ab199823f177eccb9cb6,0x17d884b5ab19379f2c7ba7e97c9c63835ffe5e86abb97faaf72340f788d26e39998a01bcfdd650a6b852018bbdcf0fe50b2403e22622bc0036e212277c77e1325,0x131fc698b24c5b6e8b9e482b191e1ac885a30f97efd6263d29303f0fd4b98e1cc06965f539edf695a3439a8bc24819e7e2,0x130059bd51e2f05f11b2c795de4dac162cec9b1d,0x8d9e4d54576f5fd0dcd278b68a6db1d7ea774d635923f0cf49c41,0x2cc2f706575474b76322ef9743792c0e9e96500f6fd1cc2f8e3695ed08502911c1802d8549d3fc5c85c4a1fd0094aeaabcaf3d54bb6cf990aa8c454b7fe3d1e3,0x403011bb0534de9b1804b5dba57,0x1086adea7d553493d4237bd8103c3888,0x199db8f2cbe777c50770cee9a4cb2dd30f178e524890451e3c72a72fe7fcf9247c74ecba,0x621fdee25e06f6221559bbfc47a4f5d03662929f8f1babb,0x19429d5dbd4878a0521b67625e2d7755a32039a496d3d056c9adb540fd87d250aaff467906313225a345fe2e6082b0773ca51,0x27e76c46178a097e76e97a912e927d4bddfc8dd7b]
def local7g1 : List Nat := [0xbfcfa0efced78bd2b4050ab4438bb3ea1ca2169152ee5e3d2e68d50d5d1217e35b0,0x237a435f63c74ee7859db35,0x20b17654c10be0d772084b0d9010ffd3cc017fca1bbd81c980c9b770b40,0x2c90fe1ef40848941a0ea28cc40297cb3c88ef7720477de429bc1c4527bce2358fabee69665194032adeeba2d15e337,0x146bb01bde47ac4f6f1107b7b359e495770871a8d36e9413e738b2c447,0x49ed378a162e6d2a9230bf2441d7346f38a76ca2ce7b10411f1ee50f2b3647b9e577f447d9a928cee7b3cc1ddd45c91554acc,0x830426819ca6203fe6c0ea11d8c11228b104572e34b24fffd8fd650e5f01bd3c5a82f,0x53836b3b6facbc185a113b1294bfbf569b4532e4d85e77af86882896392039d2601,0xb719490a98a9efcfab28d7822a0ce90857d9c3e13f63a3bd47f83871bba642a4,0x253003271f3f86b5d40236ef104acbac93e442,0x6817330fd21f4dcad478e4a03454556c0512179c2832631b67438ad87d9d13ed29af875623fcac02326c2070105ed373c81a502ffdd6cdc19594f1478052b9,0x5a87a44729526071facb967195ccef4cfca57a29305407dffc73a5504247af5b1448304203d8182af183794a516823,0x1bc8537d9b4dde6ea62023b7904f0c9be3672d36adb23ec66883fa2ead120e5175552f68644c56216a64ab8b3bef07a629c,0x2cb5189fa2df52a6c93ade99737dcc8d2d2a87d6d66bbe8f8adf1c60e,0x1d8fd78cbbad22429dd149506f276bdf90af94c429b62e181ce50f9a9b4ab0d3,0xee86ade86c0af8935a4fe29395f1c59e608dc9197300fc53c21b34326e0324913d709bfa7091bb70e202579e65e,0xa91a561c98a154b271840efa5cd481161aa6980daec5fdc9e2b3f136fb6a103e5458c56f81e5e435d416d65e0436c210f15ee3e4229da0b451b47389,0x3fde0bd90f39ee5c9037920f4580a65b460dc17420a673739fd190835f73fbf59ea204fd13e89572,0xacc56a54fbb2f2f64603bf57dff3e92f80d48c21c1a4070d98838ebbf8cd2e2fa04ea44206351c5fc0314a89d2dcb5659860014aeb8acf,0x1ad76c6a1e35cc2549b3236390ab111b5b21f6c1213c61cd0106fe5be37acf176f9fb2f,0x5a4c3ec77bbd1de9b73286356c0e79a82f8f9e37400c355535e0bcd058fdf24c01695e9e670f3abc4154da7b762cb5652973f9,0x20e58e640dbc29a29104955f778e3e5e3251142b6666e64f5b529a3a753005e3bbdfbeb9a,0xddd7d92a3221e0adcfa03d46321ce63676dd2429bb342b144012ac1da641ad5768fb30b461ff9d1,0x95580b43efc5b1801deea9242f3245eaff331ba9cdcf7459c45cbd29fcbfe6e5e2b2f9d531f42b3a797fb6fc40efe923703037c4157a]
def local7g2 : List Nat := [0xa8d849ed6778bc8ad11f8fbad7066d461afb74e0e4d61913f1c85f385a6c56180076e,0xea2bf8e0cc123635623b2e7bd321c71b7c5cfd3c1c,0x2393b6d88f206c9e6c385236508c138cf6e39aed62516c447a1b25638f4fba957e2a41df40fd936e6,0x23cb8cba6f70b4722a381f729337f4778d1bd6d5db5f301450f218,0xa09075d2a731bd7dd233f75005675704cb3c762e45a8006bdc54,0x5e9bfd08174999ce490e7e23b13b0f41654f0bab37441eaf84d2e1fe654a03,0x8596f27aed0b2cbe4e116fbfeb95a5d915817a69,0x272c28120669a4c3ea0e62619289a43911c0c2cc4851b5270ea23b767e80a32cda4e86d5cf4,0x8a87acc728b00042e8314ef2cb06a53ac8289781aa1b2d6609d789,0x142677600791c58ffd209605843e300ef0c07ef5baafea2e5fc6107ae7ec0ac7e4426f2e8a01d47de9fef4309a219d92dca540bae9db888e5,0x33eacb69bbd4fb1b83eb8240bbf33fee4d7f616d965fa45,0x5d24c29cf8c421a18ad931c0141de843d6b5f06f1200ea7a42c10d54d3610fdc622707600bcb051596318d7328be1,0x1715797b0a3eec99bfc2c2cc770bac04e5223b79,0x13011617db44d4182f3641d7299d948d5e107e3693c3c46afae9116f4f7,0x9e3fe85400cffae732cea089786b,0x5f07df23a3b036123b0d95214e6f145da09,0x19b40b394375a83be4a5091b9832b4e3a032b1d6eb46055ed27deabf3eb58aa9e61e0afd,0x1b2068d91eec83dff533cf5720c3a4a317604557ed06f41df658d4,0x3298f88d07c532b369cc342607d1994d16f988ca12d6e010e3b1d2efbfcae2092aee2983b818a9c35d8953c105fa76d6,0x33b33c34a5f3c0d8db4ba7fcffb21620a48103b4543b42,0x117cb2834cbc129906fc6b9f19bbd7b208855001b6803b390b9f02c59d3ae,0x7da39869e66eb8995095304b95ca1ae20ab8227a33ffdfb4384039a9a8d1c44ed0db8f,0x2820bb2e258cdf0fb4545912cc9bbc89b53419b94e90b4f7c9bd286cc09845a7af123a05c5b,0xdecbf84547bcfe289238a1359da3a08b41dd2bdaa564f3ee1fab0322e5d2488cbce4f16cdca300ff01a9ef08b1025]
def local7g3 : List Nat := [0xfe2828fe0c2178eaa1fb049a7ab3637d2f08094d938ca3836ce7c3b36b90e3ca9,0x433a954e9a3f1d5619f8e4a12f332c9a8fc9b27eb33c13b1f5185821,0x265d8c68a531ece14c637d3259c75ae62a2536093679732277aa1,0xb4d2560abe5551d3a826c5f38c35891270083249020ffbe58aef5671cdc2fa8635f21c7ca3cc735d4ab243,0x8c692216c310aaf26898c3bf09728c26ba18f728a39d1d9782b,0x90b39628604e2dc00ffea1bd5c66869b700c5c3c4ee2354db6e,0x4cf9840f48b0a5c58d6089c82f73d53c43e2acfac93d47e94,0x1f5fcfeeed60ce986dcfb9cd3193bdc061f9afdba1112b93a457ed1,0x3178a5ae9976b1e8aef545ceb917a5afbaa8cc2b7682d3cd4c3b93422686621d019b7512b7d71c,0xd72eda947a76562fdff31a879e6e4d9e193d5ea96c1b059f0e,0x10190e10cc97984885dea212cc84e985184c1e01b5a7f,0x11719debf3334fc0352fd576621c7f8fc185f6d18ee9e1be76,0x340fe8cfd9bb388c0675f741ae43adb1ff64ba01,0x8084b142f7b72a458ea1684ef2d77293c58013b8af,0x3cc73684609f2243d13adb17991e0fa9aa00ed6aa33780,0xb67d164fdc4843a64119ebd9bf1efd77ef2b16fefd19,0x536bb5f0039d2033f7abf239b4ec83d57fae6,0x24b6b8088964a123b59c020f6fb759099f8,0x1d77097b1ae219a77092b7ee82637ea9,0xda270a2a738b3042e81e752ed3c91fd9a,0x15bcb5644038a8deed6df2ac0e5877c59d488a3a9fb3505505ad89953262d13aa73f99db5a,0x5a95ab70cbaa03594dbf085f92816b10451d706fac07d10bc18cad199c,0x373cb8a34e2231286846296d1bf0132aa9a268a7b49ff5582c70ee639f4bbef990,0xc1d0f0697d1d2875f5864b1756eaad2c858f1a641865269d8d]
def local7g4 : List Nat := [0x6c40a7c81c680238fbde6dd6ff8d4f9ceaea97268957bfab494349e5d9b82,0x1c6aa33613582bb7f875af4bc3fc3d02801c8fef4,0x1b8ec8ef3ce96dd319cc1e7a70d8c9578f8d84b9f4dbb0,0x3aa8132845eab621d74e3c42ca6215e5d9642272c6db6e,0x73e9c919cda1a8deeeb838be112d65c6627c7c,0x13e3c984bb7728fc029d0d429006e04490ed7f81eada41,0x4230bca21ba7f0f804c19d6a4eb34ee85aa3f44df5c5b67140095cea30ce9679da4bbbe4a3fd46adcc4a7fd69ee83b33d1528,0x19a8209f14542882fcfd6ceb4cf55556274d0e999c4b2780750a8b1aab63c8e532b3590e6d,0x25bb5fe88dd0b9156f54ce4b3241b038d8b08dc7ba2869a2e1f75662ec30,0x7093bb62e8bec2a00bba7403988f1912b5d8a54ed7fd47d1e297af450964b88f55abd58f1,0x13c8c5cbe53b3d2a43138f8036d69529b690d29bf18be4535e4b9a6f,0xab7e6a541f674d9d087383eb7d1f4a40627e04c3ba80b7aca37b0489fca0780b29c1,0x12f18473c80c7a8af56a6dddf250b2e18d78a0ef6d54da80d30a329f3bff,0x2c157c8c9b2d5779e6e1eb33bab3e6590405fe376e1e7ec994acac2710f9c1eceacfe7ca7a8ec54,0x9ac1a83f2d45c93ca1606cc4d15618afb873e4cf624d5c35d3,0x20253da7d50572752a8e03dfc49de281cde4627f6f8b9f78e3a7d7b,0x3a4a4d433b15108ac87f117d472d465c99b59f23af0,0x28c221f50e231562b1a04237f1bbdf6ef80241c68822373661bdbcbdb63b9f3fe466,0x2f6f71f2a8f5a5c0bf4e802dc10ac9251204b1b7321d9dfc34bfdb3e518f60554c,0x181b23afff02a0ae6daebd48603f3395ec9e50ef1875cb7,0x2adeb30390ace9e1867f1aadfe852e34b64d9c6abcd921423295b82c0d,0x1453edc7cebb1aaab5e8292c582b5c925773c9d9b19c7bf,0x1d1f1f72def85334b2cad53ac795e0bc5a29924c6698c,0x423cc4b3d655bdc6fc27e29c18b5cd645da4]
def local7g5 : List Nat := [0xc92ff58cb13e222ac44e5a0d25bbf6fdba4f71c4b68ace6a0892fcb3,0x212d946922f2874797cf4f69bc8fd952a35113df74ae7954,0xb3ac02b0df137f1a1292d6c2213114453aeb562cfb5c,0xabe0e6e25af53e90e04eafeadb8c1a949d54,0x63b600cb6f492795c0bb6a3eafdb6676b1836,0x73c3000d31457000230c9c305b2ffd94bad5693019778,0x90dd1e08463d1fa4918c89a07d859eabdd59d5a0ed1e55141ce616f7b761a85cbadbe,0x9fa048f53c79e7f49e6fe8fcf2afe65446417c5948b01917f2b0a0b0a10a887ad92f6c78448368e474ec392f,0x58fc7ab151e59927c2152ca66859faac94b73cc90fdea,0x22a0d307922a6750b9db314b302180d7b1cfd4acce7558f25efeaab1a,0xcde3face2165ecb1c2a0a371059415b25cb43a7e841c7d6fbcecf3c666f121b9bd6a774d1d4bdeb,0xf8d477dc047f7e688434068ed058c41b1bf7663e87,0x589b9d7079c74f8757444d1401e21027ec885469cefcfef,0xbee6a03a96dc084ad0ded0fdbc76e06ffbe9de8cb9f4,0x579a1da8cbef31d6d524ffacc4fc0d70a12ad13d4f07e85bb12d,0x35c4fdab046e595defa,0x957198173d64d4d527775b01e9597f4583bbac9c96bad9c2a,0xa2cc3b41a9ae09b867916b78487e960a3ac4a8dc30087ee0441a919a5f873260524c4535a95,0x22dd1462ae0de58c69d88134dacc2299bd37cef9b4b36156c0d7fb95f3b,0xc60d1a6d5d10bd524e829af99c8cf681fa29885f72b8fb10,0x18354db7aa88725f3838180ab608ce1d68aecb55187fd987080bb192a,0xdd7e42ed6a4b04bff787468f178e9d6977ca5d219d5bc3b0f,0x14dc0a83de6ba1aee8c15499bac2b4407e85c519d245956,0x290eea5a66155531933117e5da9f4e2af599c00]
def local7g6 : List Nat := [0xa7b75e22b2bc0ff5ba51a7d7f3b67560776b8a3,0x3e34bb116e2b8142c315765ce3f3ca264430cb4209b11,0x2f23c28ae432a0a01669e6026ca747cafd690c3ef9,0x1713e4e90ef1f61f613f645da625b1ba463954a2f987f5ea7,0xd99efe7453da70564f11228e3b495c50391f08,0x77e10d187fbe9187bef12e401e9e8441a1d,0x1347979d72fe1ef8181a694bea494c37b123cf83de4,0x6b8bb1fd5df1eaa495f3f6acb01c230ded78902158327d375bcc24d3e400b62,0x10bd5a2ef2382f5e23a1fb8f4001d47fa88c7a4c519a05233b96,0x24f33ea40e6e0d221eaa89bb143f6a5bd9fea46ad6fa28740aaad2db43,0x245bfeb6dc2e82004873453e25d367d1b1a2a0ffc30afd3329a3f9dd7d8d234c39e67bd108edf88149e8cb4a170543d9714905e286143fb7a0e00,0x23c7e3727a3186bb7a065de83d7439c6a26b1c33,0x71037bd6715106db7bb1691941ac4ef85c61aa611a30655c10,0xb21abfaae44cb4067fadf5728074adcf4cf98d313dce,0x10ce6658415e0e11ee813912e6a97ddaf1,0x198388ceea607b40e26c9c0483dd4aa429da16ce5e7cda5ae99ba4df78a0331c7ab59474ce7b7fa7d,0x3d34ad7af2da30b6c139227a7baf3c0f0b41b5e094599aeedff09062db14,0x112b60837fe9368a78171617d4ca969fb214f40e9fbdc,0x195e359bc938dcc7ebb41ffe75b30dd134c60dda1e81c56bbb4d11edc85ca4d19c31,0x371f1586b5f9189ff641899c052e0dcee5aaa90bcc3f2a,0x27175cc0d729fd7c989548bb86fe16722a47e929879c21,0x2722af5b4d9a00a55f3a78913489fb893139fe3efe04,0x1a6098ceb3476464d76b4f87d5d9347e4a,0x18fa33f79cafa44a4dcde7d1aeac29f0ae48dfd3473460df648051e4937d54648f52c8fb521abacd8]
def local7g7 : List Nat := [0x2f0692a993426f80728a8cf195b079d4dd08b63a0ab924d973dda84cbe72,0x83d4ef52af633226ec83fe331e3ac08133566729ebd,0x7a1f4818c1d9175b274d1650aa52a6e3073baef9461b03d9df187ee822c56e234c0dc83d7686,0x5c67e23c1516aa81b4cfcaf112c70eb5ff815e29267d8459ee60bd87ee,0xa3933f1d0ee028a4f007bac5f7db8158b1,0x1c8a7fda09e407f8c3a46889ed122c35b631145b0301e94f2b5ad9af47d1f,0x2c72256cad96a8a10c14c8545709ec0fe5e8ff5c179f40618979d93f627b9ddb,0x1f36c82f985ce3370812c0529f4843064093964d026285b9da3,0x1831819e6a521f528729547db84f15252431f55b601c9c690f1983511c26ce97998c1,0x8dd2ac88fdab1cf6fb60db6661207fbdfc06523b03a5bdda4,0x29a072c27776fb445d345b248da457c66d1f3e0a3dee4977fe14,0x32f89c394d87f11ac1fdffefb92c5bd2ef91122eaef14d9a45,0xf0f74f6a302b416fef21ef930f9f39fb4de0553faea,0x80b0ed459f036dc7652a664413a3a28c7895e4c39a4c4e94194999d,0x1764fe5bbafdedaeb18913d7624f367b99f28dedddd15,0x38c9e9ffb87fc2cc52ac98e6cf1997619da00b47e69,0x5c81bacab9265d4fdb55a446ce6905dfcf6f2d29f507a02355ed236d51,0xb3e0025b52a0d5e106671a18acbfd057777c6,0x7bd96e5c1cd9e751fbdf7c4192c22cb19603b9ee9,0x12a52030a15103fcd37ff806197c20db097564207f502ee2af3775fb51bb5a326a19,0x1717967720f020160801522e2e03c408a79d5,0x1074d275cf9c05c87ce349fae0ea178fbc17a63f55b892490f03,0x6b16602ce5f5e7c47e8fe4603877802097efa756ffec5046b93b,0x8cd47fd830b305d103d8d8626ba084f7baa1]
def local7g8 : List Nat := [0x4964b283072d60a2caf15d19d3ea7,0x440f590c28e2c780cfe0e7cb03967f3ed70e6613e4985d1789,0xe214b3492a3b0c612d8c88161401e70aafe94bdeb,0x7a3036c389df21ea28356b5213b1a63,0x4053df58fe93d32496aa6a9104c1eb170d333d1abf47,0x4ac1bcc7f4142c1ff48a9bd484df06b3846,0x5a019efe05c0124f3fa813d1a73648359f70fc316f3a36,0x358521d86b034da98ea3b142e270e5bb06,0x25e8ebb270675073a6111bb7,0x3b48cd1eba3a327fac93c783444464f2f0a44d72b95b840ce424ab4d344e1bb4d51a8,0x3f9df8999251028300fea03ef19ec145d8e2,0x193554e91555e62b85c559629d5ae2fd6bbc78aa,0x3b93a55ae6ef36df08c6574991997779,0x9d8ea3fcc8cbd3c769463a964e2739ea033651f03aeec4fe3659d3b978b3,0x262261d44192db3577c3a51f79341e392e5f3d9f3f,0xcef80572d18c15c26fb8f564bc4d060c281bfbd8,0x34be15cb173b07c76fbf7d37c688ee1cbc75f54f487233e90,0xdc5fe75af3dc2a04527945d80b,0x136b200e605e9233b87476639c3aa281e11707d7e906eb80ae29f600695c,0x90b19b73db2ccf0e0488a2c23a157481b29ff9322d19345,0x51869e4aaa20be4441854c236ace7ba36e9bdb86c,0x14885533f5f59aa28ac190334f23f3e40cf65bedc4a2c431c943e97b1d8081d,0x2497f501d07a96bc23d902cea58d51adc1b39bed1417493e665d02117e,0x157b6a00d52e7e2609e58ba9fb4b1ebbe9ca217b94deef18f8b4c111d73]
def local7g9 : List Nat := [0x1a6ce40f16107e2c255dff9d791843f9df72f38ed05b5ec10a6bb0d,0x90fa087eb23ea35f74b1a41190c469abdbc986f6e1274dd2,0x226bbe9b015ac8dab03f3c7ea0,0x330b7c99b4f18152a386849f5ec13330ae647983cbf0ef660e7447d74792eb4,0x5ce137eaed0dd9cdc9852558077c36187d1532dc3ce2196e32a1bf6,0x2e9e75645a929260a255647de1866,0x647275d375a604215d038a25269dbe7cc5aad190787aca66d40b2f14ab23db0f104,0xa31cf445ce235c1fb0385294f97c94fbb41a71c12cbfdfb,0x3167839bb8805904b803ae17110ea2c7e19d4,0x341a98c9495949518bbbd1e8a5bd92b8e14c2637b7df0852fb33,0x847f861d61a28cad66c4406b535d0bdcc805089ed0692b680a507bd50,0x17cc5628328064091fd4108d0ba47720bd6928fc9b,0x3bcb901232e1f9d9e7fdb5207b97a8bdbf1,0x2a31a0f7a74ce75537e50c193707ad9ac7ce8d4cc90057a01fbbd82,0x1487c933538bb1927ccc9b3f830516e71ce74adb2341d5dac25d68,0x534e5ccb18a90207781a6eb356f2b0a2b6b44d1cefbe86bead2ad9932964e84faee7a57,0x5a8c076500555c921c285137ad88d89f16e32b574523dd66fd65,0x2783e1530e816bb80b80a89d77be253cbb8b67a1f,0x3170ac8f8717e5dcd79fd61dfaf1ef24468c76d3be3e,0x9b6053b1a824147a6f7ca0fb07dcd0e4aba1,0x2c98bd53527f6fc2f383909336beee537c84100688238605db9,0x530db0800bbed77c3e7eaac486cfc7aae7f34c0bf92c89dcbb51d314b9d,0x45ecfa68a8ddbec0e1f2858675d9de75ebd998,0xb6d4f348aa0f6114a8257f7f7ff9609b39c797551a192e5]
def local7g10 : List Nat := [0xca7b2d081cfaaae2f987e5a36d6d3159917d9a7aa8758d102da52ce322be9,0x5989b2cd11479c9b951f350ec3262fa0c79b9e8c2a2bbd5,0x1616b2364956aef2027ec8e1a438c24a27171053e2f971,0x2b5a69e21be4cb40155e78b0fcb169755d83374f26bac17429,0x121faf38d8f6664afc1f4a93c4aa4a97aaed248863beb6157a5da1791773,0x6d60670e79c706edd2a39d7efc26c8561c965b449c9c8ba8d,0xef9e4641463c8824c8be8e8e8bd7134fdb1966,0x284c58bc98301d5e31da1239e60a7e4157c745ecbacbc64b0ff19,0x18ddc607ae4cde3b1080bc5e93eaad28fb3b04b0e8b9bcf,0x5a08d5cae1c1059b439e424b5d8097121412dfad3ad6c249042c3bbf,0x80be0cc908e5a8665f8b81416a9d4ef417a953c1b,0x45bae19fc922d2a64ae1ecbe1793191b13,0x246d6ac38c052c2879dd9d1958e068ed376bbf09cce,0x5012c42c606a29f5ac7164df0e7469deb,0x20d61058792221eef1f7b28fafdfd0f097d0db005e8e717b64bec51923af31,0xb3c43ccfc6755dffda3d1047d5205bf50a86eab3d6716e9d1910f0c17,0x1809f01e80a7255308acd0e8ebbadd8207c7ab4aaf4383bd3,0x36dc84e8e464685da6b70de5ce3243521bb4f,0x13f351942841a73c966cc81ad025139efe96579575bbe,0x27deefb175481bf74e7b830678da2defacfe497971,0x553622cd2ee1fc876b367f3a25887b29d56db9b,0xc6b843a0566d00027d8a538d3e3f525179991bba51,0x9c3473e1af5e4bbd2b1942f37b67f3fc30,0x285af34b7bad65de88ace87a53238dc22ba25756]
def local7g11 : List Nat := [0x74fa429b82d5e6add2e95c79cc08496cedc87,0x31de01bae5867c1449a958d4a85221a0f5be20f845,0x17300374cd01dee23779102b328265c4b6bbfa1aa3,0xabea53bf09ad31423645097351d7bc0d,0x1911a771543196b507aab51bdff2b9488c6b63a7b,0x80b26857ce645cdf6dcd3c70965d92,0x927be9997d99dc5597246cfbcc97ad30d7f489963,0x1111316fae8c1319349f70995627f79a465a91ebd,0x2e18ddf140464edb5c9ab71219b59b5de7b99,0x45b454d97f7fb28c62b13de2fa2b231b1f,0xa0273bdf5020297ca45e2a01aa09c76442591a,0x35d03c4a60f2885209f8185d3fc21bc20,0x1a9708736d92e29db142108f6e5107bd2acfa2f8c97f1edb2,0x1726c04b44414d63ee7e835f31c01d34e1ebda680caf75d8d7adf635a9,0x2fb14400fabf30a17cd42c9834ff238980a,0x2b9f32435ef3647564d17210d3d457f77c358f2dfd38,0x7371648a95d0a35ce2921de7c5529d65814,0x1b1d4405518f656b56e06655e6c4beb80fcf8bc7b92,0x1486abc54ccc90d1e6e3376ba5caea80c50f73be9,0x2d9af7db7e4d992961f9f3b744c5c6df55a8c,0x2305ea8326ed4e1a10155544e17459c35ae3f8ae,0x1880d2eaf1d7d9f9741870e0bb8c84a0fb325995f,0x1d5329043c0f9e0b3355d96a65a8e1bafa79a3,0x6da7232d769e8beae1e757a36283568c213b16]
def local7g12 : List Nat := [0x3b8539db209569ec3d1fc43bd683ae0aa57017c4d0b39f55a6e,0xb28572f857b882c35ac0e66bbf5095d81c1cee5da66539c5d51,0x69f94f18526bb086309b601a63ff1b4eb3b926c08e2cb570a0fd42,0x23accb1637bf2d759d661c4cf476ce0fcaac68c62dd29,0x5555444c74e188427ead0ab7917ce0fa21969adf,0x380e7d75482bbff4933d72664628910aba595e,0x9dd1270a81eb98fd23184fe8a8db8ea5dafd15bdaf84f,0x13622463602dd4c328739dc722bb2716023e6e,0x16cdde27739df0ab605c5c0d2e23d2fe05,0x3ec1706722d266b8a9f5678e341f9a2,0xd418f92e36ad76b5ff8619cabbe665a9d22,0x25d83b750ec665a4276bad53079dff40e0bba39a8b900af1b1171188ef83,0xa439034a39767c40ee82db4651beac2f5626384e80657abd5ac6,0xb084cad7e07d73c7e4a160fa4669904d556c5840,0x1b6542aed56e78810cd2296e9970f885e8368a1ed821b26,0x14fca7b5d68c9587f85a92d30deeb,0x4b36c58d7b1815f6d9ba341cebc1b5e1671d41bd871c38,0x2d6cddf296a7f7bf424769e71ff21dd2c60de1c,0x3009e56a5297c5a263ee84428de88c94730f05663391b71,0x2e29abd19e8473e21a4aa89e419b8bba8ded7,0x2240cf3280612638caff54ad6fca5806c5cc8,0x6433ac1504c5c56a4cf011f62fa62485d59fc,0x3ffc6a4a87f15958b593c8e5637dccfa7e7b,0x3862cae1fea45431a47ffe9ec5abfa4b]
def local7g13 : List Nat := [0x46f87c57cf93822a4541515ba3f898,0x44177a747c149387df9f19bd,0x2173cb394447ad2ea7e1f23057d2f,0x10b02963a104dac6edc31989f1b826e1977e8,0x59712a9eeba6d70ecd44fd64211f5965,0x2e1a4fc631037ebfee0a5b1b3782c76abd8be,0xd27ec6ef0a4b1807c0b1d05056c55c5e,0x251f19f5fc935c9f13da21fd83c9f38dff392f5d00,0x768af3c30e507732ec9c5e98ed8bc4677503eafdb68649e5,0x4465799075136f91d077ba9f1f5c5ab10d701c0eec274ed,0xb2a82b42196339e4f93cd24710b1c6715f5b5591ca1ff30,0x27ff53eb216119b07651fd8b1c951589af78ef0212bdd86,0x1c05457ec792a80e483e41d04579c9db40c2a22bc4b0f1cef0b5,0x66ff65117203f8e590f4943665bcbb4b,0x2ff78158e01285266dfc12b85b53a2fe9500941733e94ff917,0x65a002f0aec56034df3aa79acb1dcaad129a3d58d416b170,0x21e1f6816cf1b1cc4700479653c96d005cfe9ec872a39d888,0x165f28ace134ff4e7def2614206fd9d95e,0x14ebe3d662be6cadfca8542a7cc5899a2f0e674ccf9,0xe6ac5412b2e06294f9d7c8fa91,0x1bb7d38d42428a8a2ca0c770bcc9037b3,0x173bc1e6ec46f769d587497524142982772e1e1b400e5b920faf2da331e5,0xeb74335d615c11429003336bc7d0e0448caccc7e03,0x563c827c4247dec7e5a2003821b9ee9f1e0a9d6a6e057819]
def local7g14 : List Nat := [0x28e094dd2783b42de7d364382db13c870fa85e37b32fe8bfb155b8b772,0x27138b7487fed713292ba183b4658115a873b77b4a,0x6376535630ebdecb3d03b04a081da6714abd8b2cba1df01f682df9bd8,0x59aa588ef5e08d957c0e1f59f8,0x69c69b91aeb38365100108d9ef3565e5c833600735d54,0xd93b6e5b6f88e8c2067cba4c,0x5d9b4b28accc2a142f930c30bd95ed5c44,0x4ff05436226478e0c9710f47d044286ff8ba04823e44739d0e0,0x1e7b99780d23ffd318f90c3c85,0xfc62e1106a3756af6a994c0e8a6913a1d,0x33be9368812092d6f6942dc07bf2283a81af6a,0x106147013d08a3eb774bc73c4b62d6c2527d4f3,0x6cabe1b3327752078b4d782be59ce3624512ce29a5bd61ac97ace4dc88299f52478c,0x16348cb0a102c26563f00f9a5e69f8c8242a3243ecff186c3b93091cf5cb3db17e1,0x6cdeed62f5e95bc92a3a03b5ac7d5979e9,0x808a2c40cafeb7bcd449ba6439eb318685b6f95bf0ea5d64595a46ef1915f,0x80b4e9e93303a825837e9de0597a9b892519c937a54,0x4de1aeeb57fb1c9d0bc0393b614df1f15c3ed3f9ccdebd6cf1dea9631323bebe6cf5b6c428d3ceaec9,0x66cb98f9b20fab25901ee2f44b072b28c45910b9cced0f377,0x9f7faf62a46ee90121f3e7cca06062beee6d92c3,0x18958a521d3556f04c0aabf7d4335e13bf905c46e686495fa8b2,0x2883ffa17650b468ac41ddbaacefc3670f79f36cbeb5b408b874,0x24b15360dfa49275782c27d51893,0x191e0432b9e08cff79d20beaae2d0293762b21c8857986]
def local7g15 : List Nat := [0x167548b5b98db979d5715aa8fbd759177903ba581166273a4d6078af6b9991b7c,0xda16d49febf1cb864faf34d831a5815e1cf86582c,0xaf19f635267b2ec150c3bac66952652f87677a7,0xb84cd0fd06f077bf8f17f6203f6a94eeec81acbb55af999,0x1f476c5a0593b70a9ef2024d82f02337706b96c8c170757968,0xecf32fce2656a48573fdbd99f86a642b7222da10f95d,0x165f3857db3bb5abe7564b9f0e23b4ce9d9296197d1f1143276ad57d8,0x12c765bcc2b4a2598ef0d0187c8376c6c5625b26acb374f,0x56a6d80b76ee8d451348d1ec75dfb,0x107a22fd40db64db629ee6f05b9f1,0x20a526cceacb3dba4f3258ab99fb,0x4d9b4d5517a9199a2cb7fb,0x2f7f67ec7f9ce5067ecc7b0a72744b3c0dd96389516cbb0890,0x4cac09b7d75609a7bc414aafc24d81c64,0x391c4bbf9b8a7a9dc141a70d3cb050a17f59d06,0xec3d7c997eb7a0d040dda484c6b40461c4b92f,0x15fae845a095ad2d3ec15cd796b8657b7c48dd0ce20e1b5c,0x6521b4c318af72dec1b7aa333e1cbfb3437b5deec,0x157597654083ff4e8cd7339f34dc994ec0b38a3,0x46c1fb33af468bffec45532280088091fe1b,0x14936b61b0b51d9a01c3ad927a14b9e7bbb904aced14aad7949,0x1594cb1b70ed0ed0d60b7d2987bbebaf602e611e741c922601e39b4,0x118b4a4c47b3044df69219f13c7b8fc4087d53a9103e55d4b769,0x66720e67fb5ae554452dc37fd5a6cdfba12]
def local7g16 : List Nat := [0x572cba07de97eec2f4b4d88be55,0x4dd25b3a25cdf5bacbaa75d0186c46f27bd43bd417d57788a,0x325bd8f5643526c1ae52ca7e2775f4cec4ecc0050250ed967,0x3400e3f24d645a5a06ea85ad51fdbdf3ec8dbf9a8,0x1b7ee97c197c79833c9fa16baa4845c7f4df9d2162d41692b0b9ce,0x3267b97e12a090f8477b45408f18e7b62,0xa5cf52103a49de4c018d8e4cf0ac8c4b2e86b1489ad8d1b92,0x3d72b49dc2d3160fac229b82f493debeffaa6,0xe7b98048960b3eb3c651792058e8ef4fcf51b853bf83d,0x1717e8ec72570a7ed1137f87706ef97a83c23454efc9fd60,0x66734d928954ad6f863,0x5d1226f6b2eb7068a67ef0,0x3d1459f7a890d0b4d76b573c3f0a08f7c7523ceff0e,0x1a1384b691b027d64a219ec5c04,0x52fada3443b33db578a92aa34b4d3e4fe7361e55,0x3b0be71c89b16e59c8e8e6af01eb3,0x169e933bbec59aab7baa,0x108b7f34a3bdbfffd75eba,0x300c268573965c3e6e3c83,0x12d977de9668b4e4a48e637e4979b,0x1516037684e7c828bd51,0x3522dd0f5ee56db0053a3fa790ecf277cd3f3,0x25425c6dcf7023772f29f2563d188e,0xf7c2ef16c4cfaac4d37c335b3c0e3932]
def local7g17 : List Nat := [0x4cb887ec47c8574565013c809d35,0x223ded7e39fec3f04da85ebbe1,0x18b59bfdfa3c92d8c50dd7e6483c75,0x25ad41e71e04eb8c2bd11cf7da,0xeb7181393590cafd33a533bddac769b7b,0x4245a695941c8b1c0c3af1fa0ea471c773b74841a33c9c4,0x1f52e271f633fabcc453a6f2bebadc,0x21c4b429f7368646617f1fbbb6cb73176248fa60,0x20560d9dc635769dab296d25b0f1d93cdd,0x4dca902582c36f0f45717a4a1ee4,0xd149a7f5656eaabb9ad459d48245c6b9749d87,0x13ee01eaf612c8ed5e790d6d2e8753699b14b8,0x5a3cd9ce4725630d307761a18077e3a,0xf256c48c0662a790e86d6537f6845f78168a3909dfb3d,0x7650b043756285528a26aba75907bdd039677b27c17e1,0x2557e4fda95174ca4767e8f0c0008466581238bcc074d95822,0x259e8c4badf07e0c591bbd0eaa2b66a99fed9c8f52b03153fdf34,0x1ca3080fa0255406025cbca8f824,0xd2c388bd62a36f49d6877318d74c18f90dadafba786e,0x1547f15001dc48844fb6ef10262a8b2859e70a435f3bfec9,0x1e2cee5974dac6942ab3a12d417460854b19df,0x1b46cf749930e2207f34a79d15079a77c2443f4b7df07d59ed1c7b,0x4fdbecfe6fef5f37de8bb3330b7c30d6be57f0f,0x112b23cfc2682a6227fe9b40649288b45187f85a71b1f4a29c3dfa3d46]
def local7g18 : List Nat := [0x14eca77d89ecc96992d3183a87be122dad6b1a40a32810dba1,0x3776b4cea569c62a5c80b2e76eca6ffa5a9dbfba8ba95b1eb5eedc97e,0x8a45dab12388a9cfa98829f506f57d5dc08ed5959b18423e4d,0xff40ef5e8ea3408b7ec99f6da40,0x843f868edefb0b672ea9eac59a0eb83d0713f1ba2ec66637854ac1c00e3aff081,0x3e72560134185a770a61a2e145cc38abfdfbd715634eba4214a610d8cd,0x47fda1fa5ea855691e1dfc0e7597b94e1ae0134a885e6a,0x34f5efee2b99207b409a94bb245bf492905bf3eb29f33ebd24,0x1d9f8a6af4e910411734114822e126eed7a4e,0x66640637ac2c4650bbe3b,0x137244eb05320189ad27673db6,0x2e2364b7d9f44796f454e5a25f6d86a9294457c1,0xaf7553fd15c11bdeba6d16617e2f,0x7908c989e01c2f8e0cb3b6aa01416c768b31b238fb,0x6d160ad5c127ec5c911862d18335b3ae9ad18d92d,0x7b15f19bddcddac49b44fdd2ad629d2bb4ea9077266257883,0x5e06e4dab105239dd4baf9a61d0d,0x2d0771e4b07ed5ee4cc7d14c7788ae25f82c,0x7cfd55e591bdea360a7739b5,0xd822b9a210d2177c89f870a073fc72cbc0537c,0x4a106116a84bcff78f718b5dfb77882c3de1,0x2063660d8190653ae1a2583f1bf6d3ded179563,0x295e0809b3121499ac6dccc1ea8,0x20a517d5ae6b177aad113d9d1]
def local7g19 : List Nat := [0x93af7a422c24eb22ba9ff19f643eee,0x47938a11a80e1c0d216893db8df9adf43,0x324fa9255203df39e8ddc9655cb5fa651d8f87a5014eff6bc3,0x3634774405afe6cd9910e2c812c98601e7833c432901b3b77,0xbe670e2aecd694c8ae226e659e7d,0xaeeea98be610116e814374d595dfd75,0xbec76489a4ef1e2b3412d2e8d7ae6122bec88877a9,0x41c6c97e2a7aa265c2fe2010dbc1,0x14667a40d14af600ea94ec79bc2b44c0322cc9344006bb33733a1105a2944e5451c10d532c42e08e115c,0x1148879268c7b50230b890,0x5547044ec7c900f9529c60deda4adc40b9a2ee41ce237bd29881c82af179,0x274bc4b34600ed8781f10dd5444ec09a186804eb38a3,0xc2e6f1d9eedb413add69b9c34da1ebf,0x666f4570fcf4a6880ae3a80a7249b8c0a3beabdd1,0x27c97120753a8c43fbb065257515484c41e337c38,0xc023669db23bbf90223bfc0eb3d499b0c7b197f4ffd1e4c,0x24c96f881c6768dfd7a233cecbc3f,0x46229d6f9e7f396a98ff93841890931ccecb7e85bbb6,0x12d0878c35357f8c9ad3e460a63af4,0x124498ba54d1ea9ee828b1fce6bf108dbc74542bebb7e65,0x11a25c2a5022a269d1638cfa708f583d695d43c703a64d57f9f0,0x230c9db3ff5eed20ad4d4c8818a8c33a44b31cb7f02,0x585322c430bb4544fab5ad890a160c7013945,0x82492de8241e2ec6bc4fe131be9]
def local7g20 : List Nat := [0x6462bee1fbd22d4abb81de950e5d89,0x63025d5a1033553de543ce4e9ff5d780,0x54595903b92dc7dbb42d4943c801af3a9821,0x434b3c9def948fdd64e7005d1bd8e7,0xe857c1db7cc0922332e0cdbb63,0x1bad9bb16c3701de736b0a6ebdf2707dda59a43e0f5125f930,0x1f487272060f7bd05ab1bd342cac9db0bfd4636b6aa,0xeb49035d07f827274cad4ac8a13b75376e,0x8d02baf4851b92681ced20495926c22f86bf1c635bf3,0x1068a1e6ed2046a789a5beb195745959ab950404e03bd1a,0x5cac9c8af678d08eaa1f2b3b3b69db694580e255b6c,0x2b9dc2a77b8d894d88b90d892fc3b9a161c4c,0x54b324edc5b48c7db5175d9ad959,0x5042438640491c2b7ed85bbbc190a519561391728a2dbbf590232a3e,0xb7b43126eb742c2b83366828b95f,0x20a0a5adc67124ec725cac824d1eb9d9cd993,0xe39ed7b48baee14947a44e6fdccd2e49a471b4598f8a639d22,0x3cef76bcddb2986cbc36f8483260a9127f8e295d6f,0x33e01683eae9ccd5eb9917ccdb1d48,0x6bfca78e51b4817581bcbd6b25a5638cd,0x291aac4396812e6a595abdc44ba731813e25bf2287b1184befb8c1,0x6c3fbfd2cbb315eab0398ddd65b9c4fc83b2561693606,0x20dca196dd7edda8c19c2b007fa879fb6c41ae28a0b47d8714b94e26b56,0xf17e1b3bb0a6c00de87980df032c1a5b7cb]
def local7g21 : List Nat := [0x70c34da22d65358025cf6dcefc4f6bd211aefd551b93538b45,0x23c345544b19fd959ebf1f9c2488bf0271a176d9cf9629a54eef18a8,0x24bc646de177aba12266501d3edb9c66c000c99d524b29e0,0x4f8c2d738f6ae77a01adc01e850ef34,0x4fd0fd296f35d98610537fbdd2edf312f26d8,0xcc3e3a3d6f0cba242f65a27ad6bdbfb035db1,0x93962a3e92b6847e744e19ba69e606157723956d7c64d7aa9be1f,0x708f76e50058c98c2e4e942aa942d0617c3eaa86033cf8,0x394b487d00d07b2ced305e9349dca59e33a033dc86f020413999e4,0x2c29ac2ceefb5a29b3f7b7c09f09,0x482ed37d8a2635201e6add15ac87ec536a4,0xe74ffefbb33f49a1eaca268c7aa47a7a9bf03,0x871b3ab19c9a6c42bb3c073c8579fbc407c473748,0x803db4eaa4f49edc1deff31b4c0e8061a0549768f8bc767fc15de1b4a64ba05ec42a3938,0x454ebcfcf0e4ae8c88b90927b0777b3db22,0x6810b58f07a77d0ae79ee606fbdf9,0xf7bcbbeb6a6af6de8a5b7f9f4feba66c74695cc72e64d59fba3,0x227f0b84c3a8eee2f09100299a7de4,0x440610167aa2a0ec7b84d5a9f42d16ef4c617f1503bd95,0x3bc2e562663fab248c3f88ddf73a2036bccf71395675d84,0x11c6c2d894b5c8b86dc909c59f9178a15ece,0xb17ac400a11bf54dda55e1496240ee6e0fb583da8db5788549c9c,0x6bab0babf10e5fb62e00d2cc2dc8847794,0x7d002f23462b70500c89be3bd56b347371a28fd56]
def local7g22 : List Nat := [0x1210945d4d99b30825979eb8,0x1b8e3e3707bb35c6e400d6dae8765a68299d2,0x1397fe82549672e43a92bf5e1dd7667a47be9f18a1bbacd899c9ff161,0x1218e8a64bc3eb51e4d29f9872461763,0xd5f3473d586f90e995044ef3b504c9d23c24f1ced74261fb2316d,0x1d89d7a1df417f7e8d634a73486e36f1ec9,0x14cd2eabf3fe1f07f6ce2b327bd5dd8bee5129d28ce,0x72a519e1f3ae5d16243870cd,0xfcc1fa35e201d103c191494fa61,0xe7f0c35cd89c6b029d2fa8a4e1ac3,0x90eaedb8ab286e4d0f9520faac4a921fd404bd3ee65549a0fe3,0x129c103ca0a863d4e4e1eeb487f8cdf917ecbdff,0x8f7d8c23441867ec94ca3d23bb59c0d24d04f71f4b1d18318db960,0x2c0189a36807c5dab53b3189afb08e5210590ee3a37,0xe03b4697a8b2917a736dd25917b84ba35c11,0x14c9fe50a16617e69a3abcf55b011ded62e0202567d1f21,0xa92e4c6d1760204eb969,0x5713e6dc73fe8f524b5b1f0d1807d6b1f98ac10e3c9bf9b8897f,0x32529435712a308584714f599320bd8ce,0xd8e351d5cfc3487742d177fe8c49004de02977fb08084532380418907,0x4a447dfe5ddfc08bea1bbae0dfa5b0f,0x311b7b6e96f9d94527b8a73998b09a4559072e6,0x55fbf9d6f30418ad0f4234ead7a73117dc6,0xc5170a82d8f989ea3086eb2089a2e74931a]
def local7g23 : List Nat := [0x3b1d77e5415117d085b09e633c5b73b5fcbaea5aace,0x6f9361ebb385c03a7859aa7e1af0f7f2a,0x7eb7f824b5344b109f4be4e06bab00f689cfd90,0x41f702a8dbd638f61a31dad,0x10ec11b65c4eca2f84e7a472039102ded7a0,0xd98fc919fa43980fba3c4558f5abd89194a,0x31a0c221b4e5529064cb24d0520eae558a8,0x175328c586dfa065968459a4da165333434727a3,0x6215ef5dd37f488ada89cfb67a1,0x56b4ac548cf3805567a9a6b,0xbfd16423355dd4c180b64b0ec9c3c,0x33b8c29768b1bf72694dd72791fbd195fc3e,0x3bb991e54fcfaeabdb73dd4fe049a4,0xd8aa4c49a1b9327082625dd55ea9719a9131e6448cf69f47f7dc2d282,0x44189005d221e2beadf727dd8aa6da3e3f271402cc9a46bf281b412,0x11cc6443764f9898269ab8,0xeed081e8ca1be4b94f08aceaeba314f040ea433ce109ee9c3,0x68f695cc794bd118b778097f260bb73d365500f271e878288acacfdf2,0x4a5d69f447eb2ccdcc1e919792a5a7dca7191ca97384536bad00d67d3,0xab89564f6b7711372d763226d19878d362a4b8a63c059bad2882a1cc0,0xf52daaaabbd19cea7d0dbc548515b8675ddc28302284e7a6d837,0x4782b90127022d2dabc3789dfd6cb79e3d71e8c0250be683bbf65795,0x69dc285e31b18480d77cdc4a078a35db822e68f670ae1c810aac559e85a9bc0fa48,0x18a520ffd1e9cea490a6390655d324d3e950dbe495404518fa52fd7c55]
def local7g24 : List Nat := [0xb06c3ff720ed1390a1b11814b1dc3628971ddecb27a9d,0x1a93071bee5fac4f99f9f07abdee7,0x321dc72b54b31a1a60c3375420b920,0x1579ed94e5ce3fef1c8e3f476702e9bddde4e867fe64]
def localD7 : List PackedState := (local7g0 ++ local7g1 ++ local7g2 ++ local7g3 ++ local7g4 ++ local7g5 ++ local7g6 ++ local7g7 ++ local7g8 ++ local7g9 ++ local7g10 ++ local7g11 ++ local7g12 ++ local7g13 ++ local7g14 ++ local7g15 ++ local7g16 ++ local7g17 ++ local7g18 ++ local7g19 ++ local7g20 ++ local7g21 ++ local7g22 ++ local7g23 ++ local7g24).map localState
def local8g0 : List Nat := [0x80d03562c69d9b3d16c59174735cd5b6e5af38c4dba4a81d02da3931705f87b006928927b8dbef419c4c2208ffbda8ca022a6c8737e472a34553bb9246d04e63409,0x3a53e672d3c89d1114f0005ef207c865d2f843ee3fc5cedac5543aeb86e1817d804f3a2364ca39091ff5a2187a32edeaaf23c47baed02e147f8e3125,0x7f9aaa764f5911ab4430e2333a9d3b9f699799ca26845a54288f759be289b6f6c1e856d7344b75cb90c304227d11b045d9,0x1358a2871296f6a5c1c6f5ecf9e89d3f9d219718f19478a2232b145a3264f6,0x18df9d10274fb5f3839750da882e910472f40a62f08927c48aa2e483d45f277656550ae559189afedf3e440470cc2643d00489,0x39bde3e0cdcc0b5c60c879d233c6477fcb3a413f153ebbae55058f37c2b96704207ee4ef5a04185344fb9d779b726c66f2bfa1ade0262c915cbe34aed1,0x4c4494f41cd0849dcd279a425b8b682dde66dce38f2ed5a2acdb2bba8b2e4f4fb4b69fdb79e2e82ef32de02c36a57393457beaea903aef0d5,0x83ea556590f120207ac443390ae4004b9313ab46fea76af24592a984744069790447deb91f5bfca5d0dfcf0b21541352f314573071c0f2bc07062139f8f4ec2c9cc94cdbea287013f78139d80fe86,0xbac0d83eaae06349186ad5f8c2ee5c74d035d0883b40287c3b41051d2d77c340c6fc87b386332f6ce42e4ffe2581009bb1ce585c5f5ff3831ed5c26e9d5218d6482778bda2a,0x55ae0114ca5fe7e02aba795bb84be79c3fe5bbcd4be420f8d85a050fca450f40c599c118bc97841ebf7397d03522315953ba45fc099fdc782b91,0x26dd342e933d9dd1628347897736c48d1cb7aee0cd42828f41b18a9bb6694128190ef9b7117,0xc2af27214a1fb3194ad2688206f0d05590a6bb7d7289c5c4498c9b33677e3a77f6875a5e7b95767b42240f3126dd2ee924b7b531a1c83592b8bf7abb482a4b61aad9f08bf1844552696144dbeda,0x10bd85e994d69edde9a6e4d11e5db17c2c6dd86b1fad0f50a311045cb929f1dd17343a2fa89862968fa987fe4d80f0d9702196b5e43e7eb979f522f722a52bc,0x1b06352531cdfc3e9692e6414f78673599a3c5dd483b9b4e9f0511162b9b1929d6914c1ad55afda,0x1567976dc4dabbaac4b99438662f08f075c4ebb9aa8ff33acdd80c296de83d6393a2711de25837,0xcfb2938d82e6f4a6ee173f0d41afc6caad237c735e13927862cc818f76a40b4a4df4a313cf3949370bf7729de1d31094651d5fe50303b19233bd066399c4faa22ceb6a5557158fcad0defd1b03b1fcb13176b,0x21a9bf9b24261b33bfc5fa2f730e91a3f56909f42c4a427355f27c9ceffa368322cb544a7a6b8299f96a6ec2d4e79efac16d1f6f635d949f608c05a77847f02ece6dd1622ca0dde2c3d9c2,0x17b560a7f4dae31b1abf8a68782fc01c6461b17bf14ec04afbe67802a12cb62f5f7213db773012ae12b3cca12a16ce0f25dac8bc8b4b173875a7a,0x77a140b00b261d6e7cb2f7bb81d2e627bb62118dad3be1fd3d3115408646663fb60d2463b6b7c4a37e4d463857ea9a7bf96,0x5858f8194dcb59ef5990c8e186cc755229a06e8f2e401a478c3af22bad7c1e367276e6bed3af5df39945efd90dc9fd8b5a0615f9c71e30d238739213d4992a90b673ee3b2f7cb21999b,0xb6494b7531315ff075c9cb84b89e855a08ff937631d0d866b4783c3026ba1f780216e55a97b1d3d65169ac2,0x8da4f22bf21aea0fb1d938153816fb40f26e9b11c41b3deba45eb6812f25f7fe91da8701f93,0x624c097be1a245809872f063835845197a98f0bc4fdbaa0537d318bb1660e76ce637654d59620400a676bdafdc5d29c4eb2f1c25,0x28af22b95c96daeb04f343de99c012bdcc82de8e2235c8d8f8fd9ff25bfdcda177d8709eac344b1920b3962bac00ad7c9d3bcf7c8f2ea0ed02d2981885859c7]
def local8g1 : List Nat := [0x1d531476232bae61e5400f9fc330a21149ddf9404606c270519957cc7ae8439cc7f9b9bf7ce48f99ef911de796bc301c38f0b94c1834ac,0x1e7d9ce1cc76a6abe0878949a006a9bae6d8802b6565857f1d90f1f7c3d0b4fa5e7dd9dc,0x502a56306a3cb03e0d62bad584918f31040d19dc0066df658d5de374156be40b8706f3be745efcfc,0x3da97df02c8c2edcd6754d2be7a4b778a3ff84928f6dd746e1cdab426189f2e26136d7bb33d12d8c75e5cd951117bff8668b0c3ec44ec89e8865fad,0x12d7435365873db788c8b0402452024ade8686d44ab7238d89e5bec4aa6b87eb92430895451c66754cb2cfe8f1bec74c518b08c2d666aff24f2a31cc9be3d7454d486981ae9a38457ad,0xa170e9d74f67ddb601c3610de05e2c780ebf77e16f9a2c3643dc43b3a7f17d86b447ce315eee7ca8e9b426601f0de04953e5b14dab4,0x18c4507a13639c313153bbc433dc747c6f62f56b18f3f5983a0971ae4ff78ff7532f811e2b7fd5fe4a9988bfa691c26,0x24725e71acae140ea594d3d5e48880ace2b41f02b2642067dadc1d011011b330b0894776a003abe70,0x7077062efd0aebdf531e05c1a4a8b0de16c9719cfd9c2016b258270a5205fd8cfdcef46ce9f55,0x7d89643dcc4835a72311ef498d3d240093777109c62a621fd72b5ae611be3f804feda5820,0x704ff380c40712effb76d40def5b7d2631832491b4fa92d9c93027cebd8dfae,0x359de15e2876eb39384f160975f4c,0x198d0ec5f2d7a32cc3e47f784ddfdf57f019a3cb17e454fbf3fca51b6eeb9a91d0f,0x47e064234344e69ea9ada207fbed57aefdde7aeb461ee39a49ce6c1ddc1b3b3f,0x98eaf786fe9dc18030a6c29dc840ec4344260652649cc45e1d2082102b178,0xe4ea499ccc06128b1a999d1741093da5450b7aa7424b3a1dbb7cd8dfe0,0x2c1467681d604fb0eeb73420ae4fe705518497d9dd3282a32ec1495969fae4e626ea0a741ac5fa3,0x29a81e5a1c3b3e7c788c0832bbdb5b20b979e07f3be4ba682525e3f570fdb7bcb3c9a957f17d0029c5c3d92fc1fd8dce84611788e882afa925656338e0baa8b511444e2e3c30d0e18397e553c811271da56690f0e77f7c21c4ad93e,0xf908def81475d5171a4bc082a10a3ffaf79939d4dba490eca02c903fc7b9c95f7e,0x5e4b6696e6b9b93d7080d918f51a2b3bca91c81439fc86ad55c9808f76ba8de73c83ba61aa40a2675f9a8eecc1ca57b879d51b881e8518f044a8033f8a21c9a1c39d5cfb,0x7242c1bde99bf1268f8ba323f4b19c93fa9735548d36b995f603e73a86b77fb1,0x682b74d76ba84faf90ea9b49f7d7825eafd55b496edf150d544f42c6b666784f45c77cc26c057f5b6b,0xb53dcf7b841a9134afec4cf362e879330860fbab9515459df86,0x4ab44e6236b3e3c44738f0e84381bf34591f382d0437643f66]
def local8g2 : List Nat := [0x95e9bd8b9718d0a5d32017a363519d706c46e1722cd9acb3eadd776cc0c46c968cc8828373422ff023f1155da7a723920,0x627e3a9c12656d3c38cecb7106310afaa463c3ad09844cfda,0x2e2ccdb416bae8acc78d786fe28dcbffdb15df61a7cc85a36c32938573db4453c7d68b8e6baebe82e5864ff07fe311eb,0x2089834ebd92a7d32fea38490e2d4171a45362f07a53f361b2bd3e4981ff720b3b7713,0x22a9603dc1af724cc1cedde9a81f55df2a7f4772b94010a37506a4be4547bc3e89e520b310e46e6dd0ce5f1b96d2f6c37002584a4ec323c769f5d8910da61e0a,0x8ef055c57efc49d2d03f5021d9e7539d0e66c39a07e30aa32260ceb110cb6b211c52,0x2c819e1f7d83e02b94ff0356693ae452a0883485e71a3bc65a8857285ed834c2c96bd29f671d2a1e,0x5fd56f2e687e261f3ec4a36994f64ef3cea04f768cbfbc33ce5647c697d6aa4a54b216b05313d,0x128341a94a398a7f29e92529dbb9db4305f13ae232dcb8e4e,0x29c391556a8ec0f69d9f4d61767ab5ec05cc6dc7a454ea8c02969f12539f71350532513c2c6e45b4b0bc85b18b24a64776,0xe20998b8a75f815c4f0d9a61565cf5f5803df5be8921bed1c5,0x90cb4cb61a2364a0626724ab7b649d9c2c3c0c7636566e45ad700e2a9bf0bbafaeeb195327d299253321828f6d1556c3f509b133423394c,0x19064e4bd615a284b3f79430ef025dd997c797d719d2988486bfa3,0x343e99ee570cdf1e8a06530554898c4ac4fd77cb5d0c988d81e05137487979edfa5fe498f894916b0019aea,0xf4206e54b3e363ca4de83af70f8362bc71f1b670748b4828ee5cd2d6304a5fd223fc7f,0x7362e3a346b8b3e0a3a9aed2f738ee268ba1649c1ebeb2dc6b04670543b3212d9683cffcbcb92a0d728a4d16f63d312d506a9f87,0xdb99a279aa4bb4a543c55dce389c8a63104482354e3173a7e7e12b9569deb89fd761895038cd093fc2f,0x7bb969b53f83d110cf3a65a113b62ecf3d415d97989a297be4e1d425179ef298a091663566fe94c5484ef0f8087e0174b8bbfe8,0xbba24364b66a6769dfb1d46d9edf40908a99252db8e3ceeb01705f6f,0xafb3978715f4a83dc4712433da7b924ff9e6c93d5831d3399b917436b32abbf09d2de8dbd21,0x11b21994be895973d76a207a633c93df0d1edfa7028d967ef0fe9294480db1bcabb6effb3f71,0x7dfe3f9c1e6aad9b8c24d4b4c4d3468b0954ed2f764cc6eec12b75b8d76bae82cd243f0d58b3effc5426dad287d27c65,0x6d843650d09b49bf6f0f240fef77e73d5565021a0c6347f3603935fc231f54c3b6e,0x1b520e3170b2dfef568d77e06ff9a]
def local8g3 : List Nat := [0x1ffdb0510ea445c6e8820574b2f08027d7eab035c76bb021aea30794d7b67,0x11457254513ab1f67ff5afe13bd25b361e1b0c2914c389c5ff5,0x10a28dc633b3864733746fcae092a81941a635b6b9f99a6f0a385f4c,0xab1266f9bce7319b0c89ac707ec4dfc046b364221f76,0x1a86d8ce1bc25f721cc3dfedca1d7a878b39108c0fbdfa9f5c1fe2,0x1eadc3c11ad9f5ffc1cfab8f444fa0ece68a0f44185cb67a27ab47759871bd61805,0x87e619ddddb49348ffbdf4e40861bb3db3ea5595423e1fa8,0xafd60e077dbe3f8e8947391fff60da966c475f5e1757eefff0dc86770827af91df67675150ab00a80cc9ab5,0x3f4f4b1f2f6a42dfc6a4dd6ad50834d8b870dbfe68727f60,0x2d6a921c31e9e928e393d7f1e7c11efeca2395b1b045a83e51408b5cb7e0eaf3610ce44c7cf2,0xd1c31f6cc9b5e52676c1e68df86fbeaea4d13ba3cfca20da9b9560d856da47a87d56a20a9489bb428710127dfa2,0x543cbf4a4a4639d87ac20dc0273b64d769ee69854b0c974c47f1a572c605d0045242f2b9bd8,0x642e4f982bdc86eb03a04709ec603fc892505ce59e3989f8bb17cfb63bd61f8820732edf2e425e1c9a2bfca,0x2b865e86fc3b5df588476e52f84f90b65318871a886e6b455c74dde165e8031916ff92,0x96db91f83f2315ff2e55f8b0cd774385c008d02d8652e6318724698237685e9c6193b94498f4,0x33185851dc46e478f2ffa1dcd246f228ad0aa347a82a998d1c735668c3fd9,0x199f8f5e3f2120a2e24a00efe3495e35f46d66d82c6f2f676d4871ca8db32bdb659df74,0x248c607232ef365884f8c5a97fff1bdb9d7f9bc524ec15d4db9883ccb427f66,0x41fbd8dbcc88db35f75a26d791421842a6bf82,0x18cd4f6b6684ebd08a51b6ecf6e6714c9daa8eea35be3d510513daa38a6f8a0580292ad0fdc3b93334398760a9c5996df66,0x38e4c3ff362ba387f2350d0ee46b7be083bc1fde13737fbdf6e509434a3f5e2eaf9b65f9f,0xaae51c0233afba404736381febcc5924926065585eeb06e15e0aa15c82af16a97df,0x6647bb3efce7f0f43e8bb459b0602d91f108cbb4d3bd164ed45,0xa882cc2ed9a5bfcbbcb30c1b14dce55120a21fcb8a106e8d7b8df7e]
def local8g4 : List Nat := [0x4c6f2d93161c6f0cc2997094e90bdeaa36bc24a938e55434482bdaf398227e800e248440e566a55768,0x1a24d49e2eec9969d7ae6f7a54a998a78efca951024f55023585ae93046d9a5,0xcda26ae76bc1ca883bd5ce0ffedce822534bf9e637f0e9e9950a3d728081bc1c1f5bbd5ced2fbdeae03046916212f47eb7d2824178857d845,0x57a1f2a33648625d0169b1ebeed091bb4de90436d0205f5fca,0x1357a2c0a11007032ecf9c5d49315e61acd578b3b6760f77dff630815067917c7fec9c415107214ed31756b992,0x8a7cfa416b7724ceb1ec72afaaca5213b95edd9882f667569fbb,0xcdcb4bf8dfadb9b7e578ee555015bccb86225abe0abe0e157e80308cd51565b88185a37f8ee676e7a5a,0x4ec250c281492cecd8e84970df16f752bfb26ff2874c4902e01269d679dfd25bead30d01e38089c965c5747d8c54246b2eaf06221f7c,0x10561a36da335848c379c531e5a69bdfa50932a98ae1de9bd543e708ff70b6018c44ad104b08146c4c6cfd8fd32,0x5c23159cfa084ebff416d435c4fed8a8eece50c0fee8b50278e6bc5f2ca6c9a0fefbb74b26bf5efeb58,0x1d763104dd9c324719571e165d532bd6014e69444c4067acbaf4e5878eea27f9e04357f07bddbc8b23cc5,0x2a6a6860b7b7dd746327f985958dc5a684e38f6afea3f483b31c5346d56e1059,0x1d013950db4cf42469345f429b83ff83c27bfea682e96e70b77f059b7750e1df8b90127a2478dfc60d21304844f2d2ed624a3911e82a13930fc5f1c3785d989,0x212a588590e05b8ad01beda36cb15404d135e99af3a86ba1e470fd735a7deb4ceab962,0x24bbe535699e2f90ed23d5ee89ae4f32c6e7c2108fda5f76523c4b47ecbe57a3823323e8ac8b8f2921f4e,0x45477f48b015125353bb52657d879edced71c11a16b4dbae3,0x1ef4c1db12172e4299df7296fbf1f07060f1eee108e2e5e0259ed2dac65b873afaf52,0x3612cb7f11f8eb74fbb46fcc7092986073607ed,0x3cb0edfcf51bf0d741dfb785be0de4336aabfb06157822da71f594dac498b715ccb55f8241ff71c396e0440ee362492b5e0c,0x463ca3ac4b486bde05e24353c9f852f6c10c752f4f96511d34b5ec7b122092f03d0cd2973f8a,0x1148b56117e04edfa666d9e6c5ae54fa27612b819b1773c3aa548d43807fbf4aa5fc3d00,0x2a447e7c0cb3f1944c99c576583b256036a3ece72d5bd72ff9fba14e1b33bcdfc7,0x269d138768e03b82ab5dc18b737871f646d6d21809ae82b05563544a69af4d03a0cc7d15,0x24bafbf956ab6f6bd3551fa53a7c3c1a3c2b7b59f68fa3ece2465d7546a5175d9aa21f7cb982694a467d85e1e16ff67d8e26241e9f30]
def local8g5 : List Nat := [0x1e4516a17f8503497aa632ac0394416bf1626bb7eb74ca4704b767aeae673578322adc0286486402efee9,0x1deae74b4836efc08361be9c7aebedb40bcbd1d7d6d45ee6ab548e3a5a78daec07700c27229,0x29fc0fa805c6da156ebf607eb526a894ce7332ed33d4212bc1f8c2,0xec9333d28c3789785de3fbe034d00ca6f3cd84259c5666c8cf2b5774c8c6,0x5449422b75e321c23e6de40e07b0073dfb765604f0773a,0x5252513b42e290319ca810599ddfddefa6f2ab8bb426a8309d527676d6f9dec0ff8593b2ee80d4b21cbf87be224620f93c21,0x3fe4134b06cbdd38a2065f936eaf35970db306db75d30be1aaa97e6fed8,0x1046aa08972d61404a31e1875f05995099d47e8cb470c1e58904220a6f3e119171b1a,0x1908710f755c2e6ef01c0f85333cb4139fb1420ce3de83b0009248ddd911e63c87854f1025e8d717cc,0x11bb916de540744c406cdf0f678aa0594b9695e26f751f4358dd2b3fea49b649eff55,0x65a6211b6c34acc0d49481f66a4ddad25d39c201d24de9511fa0b132bb8b76708d8c022f1869ebbd2,0x1983c039ffb9cea2d26136d4e4b50d11d153fe2a7f46111dc9abc1463f90e7964ffb6b57e4777fcd]
def localD8 : List PackedState := (local8g0 ++ local8g1 ++ local8g2 ++ local8g3 ++ local8g4 ++ local8g5).map localState
def local9g0 : List Nat := [0x6ba386f46173c9f6122a28f251338a630bbf473086ed0bfb56c4954af4db70b00a779d146812c7e1a66b2863d900e6149,0x187dec631f91485d248b2bf2057801fdb78900049fff5b1d3a4ab5e552996ac5c321aa751abbf1754f2ca3ebe0367aaf6a8cc14138cb0772e885a,0x7cbbe857d731a13ec593d8480d053299829cf4010c41c3706b78f7058e7d3c232762584e27ec838fcd781efd8004cdbe6e90025a1bd4f6818429849b278e3438f60a4b454281b1ed4,0x7a48c5d7f63d41f4e312aed6bc6cca114c62e0b4f0c29cc0fe93f96f2a715808ea41b0d890a09c14dd08710a4422d4495f6ed31efcb07441cb3636f0da73a9f4d927b27b95e7c70f469cbc4d,0x1f74f2132cf002b179356d023b01adcdf780087d490c08f87f2b338c155f2da81dbef2eb304760b8c227da225ab766d823833d9ca8bf5f7a8fb9,0x3020181746068ca8867dc6a32f9e80cfd7c4ec31b100957b17d6df827cc8184687169,0x10d9201a6e79688303b5c8318c0cb2f1da051fed41de60cb4cc176e5f50e7369e9a99a4f3e4d709c3242fd4bf82a073423836,0x25097c9670638e1b53e1369ba60ba37421648b0354b9d5602707f24594b5b071c819bc4b72e76425393e40f679bbc625c8b,0x2ee3e144a9303926e5831a1ac4216dd2d66398232015b2bb0a7ae612445e2b51b4092415cd801225f72,0xaf55c00cd30305a0495ae5baab8085b4a4e686d2bb348f4acea339a7f71f94aa017fc81cb06d45cd62ffcc1,0x45512f843b80f165c53a9af933ab25d3f52a868b59674b883b6bb15a415459d684bbb5,0x3346b016cd494f6a65ca8c549532b69849f0f9a4bc10015666c258ec5f0f81bd3e2d882d34e9bc7f76530af7a901f39be1671a8537d553afc7791fda60fd93f85481501c88ef43dfb6,0x1198efa67032daa5329c89cb69029d57aeb91645d252875032a1fc05eaa922599bb518173dac4150c500b19095b982cf8d69eb5,0xbe0261a53d5f4735c2e2587a244277fc44d1ca0f282cb4e86236b19097fefb216b9501e7ad162bf7f1f65368da,0x1161888597252eb7a9a4896b9b55b56aa876eded784085ebd8a39d547c3b,0x4b9a5211702c85edd560005126ff10b35cf66db82c4c7df9308a100155f28a0,0x852561caf9da665dc1618bc4a53140778957c68c59a5e0f9802c2ee5cf2052e314bfe22ea1be17823cfde9e06124420d6ad586e3b053f1c943e2b525e545dffcdfd7f5bced999af4,0x4014a2a1345e80193e2e60ee585a868ef27cd92338107cdf81c19e7d715d,0x1b04e5dfc3b735701114df21d3429667bea8a21e7f8a59f78824ea892bb70239c3a072e761c95ad1996964e83ddda13,0xb0c4685efe39b9b6ec816fdf248747c10e1bb09aca56bd785322cb55371f5099efc64ec8091d28f81585c2e7d5f5f7c,0x144376f03f5dfcd0c98a81b4b696433d39391c05735a51dd6c7fcc755298553108777d,0x4e7ca203ff4bb8afb3caf0455f87db74cce6bc8f6ff7aadb526c5431f0d0909abbecde7eaf172240aeeab36b48d54c1aa4fef4149aa764782a2838d2bfc6f21a2635ba8a277c4432303dfb424b01ee9ed35d0c8b7c121736a155cae515c37fe8]
def localD9 : List PackedState := (local9g0).map localState
def local10g0 : List Nat := [0x6a98441963129cf77ceacb8778a9c1837876979e900e99500f825f489bde6c72a5ee385e75fd903fe0b83e06f60266d292d1,0x13860035bd1a7ab5a99c49a09e658a9772ed40258a386c0495e95cb762f7a75c8fbd69594f5ee3a7f0d,0xb559576664464da925b3e2630b20203c8744046abddfda6d847171dfd9fee97838d8bf61dc653f91fd0a37,0x309f3e56bb03b6d5c55f50b5ff5f0931092e37ca426285738c319268c1,0x6e30f0d83c4c5ac31d1f31ef0e28629187328c9cd4865efa85f1a848316c94154f0369aeaa43418ff4384ba28b6f56c88bd4e32af5310f70225fa2bc9dc9af3da7c61]
def localD10 : List PackedState := (local10g0).map localState
def local11g0 : List Nat := [0xa833c10c2412c2cffc40944987e70063a17bd677e152c86f3b240b37eaf7a3e88df5ab70e88861a92a18]
def localD11 : List PackedState := (local11g0).map localState
def local12g0 : List Nat := [0x96ee7a31501260aec2ff0591b4cb146b0d87555e5d12d77ca4225a]
def localD12 : List PackedState := (local12g0).map localState
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
abbrev SepMask := Nat × Nat
def agreement (bank : Nat) (m : SepMask) : Nat := bank ^^^ (bank &&& (m.1 ^^^ m.2))
def sepCode (pick : Nat → Nat) (m : Nat) : Nat := if m = 0 then 0 else 10000 + (pick (Nat.log2 m) % 10000)
def fastChoice (cuts : List Nat) (pick : Nat → Nat) (test : Nat → Bool) (i m : Nat) : Bool :=
  if i ≠ 0 then test i else if m = 0 then cuts.any test else test (sepCode pick m)
theorem fastChoice_sound {cuts pick test i m} (h : fastChoice cuts pick test i m = true) :
    ∃ j, (j = i ∨ j ∈ cuts ∨ j < 20000) ∧ test j = true := by
  by_cases hi : i = 0
  · by_cases hm : m = 0
    · have hc : cuts.any test = true := by simpa [fastChoice, hi, hm] using h
      obtain ⟨j,hj,hv⟩ := List.any_eq_true.mp hc
      exact ⟨j,Or.inr (Or.inl hj),hv⟩
    · have hs : sepCode pick m < 20000 := by unfold sepCode; split <;> omega
      exact ⟨_,Or.inr (Or.inr hs), by simpa [fastChoice,hi,hm] using h⟩
  · exact ⟨i,Or.inl rfl, by simpa [fastChoice, hi] using h⟩
def fastKid (cuts : List Nat) (pick : Nat → Nat) (u : Bool) (k : Nat) (ix : HintIndex)
    (xs : List Nat) (a b z word op all am bm : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add xs.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
    (let i := packedDigit word (4 * op + packedSlot kk)
     let m := if kk.1 then all &&& am else all
     let m := if kk.2 then m &&& bm else m
     fastChoice cuts pick (indexedHint u k ix xs a b z kk.1 kk.2) i m)
def fastPair (cuts : List Nat) (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool) (k : Nat) (ix : HintIndex) (s : List Nat)
    (p : Nat × Nat × List Nat) (word : Nat) : Bool :=
  let a := masks p.1
  let b := masks p.2.1
  let common := p.2.2.foldl (fun v e => v &&& agreement bank (masks e)) bank
  (opsOf u).all fun op =>
    let z := nb op p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      (let zm := agreement bank (nb op a.1 b.1, nb op a.2 b.2)
       keeps.all (fastKid cuts pick u k ix p.2.2 p.1 p.2.1 z word op (common &&& zm) (agreement bank a) (agreement bank b)))
def fastBank (cuts : List Nat) (word : Nat) : List Nat :=
  (cuts.map projectedHint ++ (List.range 20000).map projectedHint) ++ (List.range 16).map (fun j => projectedHint (packedDigit word j))
theorem fastPair_sound {cuts masks pick bank u k n t s p word}
    (h : fastPair cuts masks pick bank u k (hintIndex n t) s p word = true) :
    pairOK u k n t s p (fastBank cuts word) = true := by
  apply List.all_eq_true.mpr
  intro op hop
  have hh := List.all_eq_true.mp h op hop
  dsimp only at hh ⊢
  simp only [Bool.or_eq_true] at hh ⊢
  rcases hh with h | h
  · exact Or.inl h
  right
  apply List.all_eq_true.mpr
  intro kk hkk
  have hk := List.all_eq_true.mp h kk hkk
  simp only [fastKid, Bool.or_eq_true] at hk
  simp only [kidOK, Bool.or_eq_true]
  rcases hk with hc|hk
  · exact Or.inl hc
  right
  apply List.any_eq_true.mpr
  obtain ⟨j, hj, hv⟩ := fastChoice_sound hk
  rcases hj with rfl | hj | hj
  · have ho : op < 4 := by cases u <;> simp [opsOf] at hop <;> omega
    have hs : packedSlot kk < 4 := by obtain ⟨a,b⟩ := kk; cases a <;> cases b <;> decide
    have hm : 4 * op + packedSlot kk ∈ List.range 16 := List.mem_range.mpr (by omega)
    exact ⟨_,List.mem_append_right _ (List.mem_map_of_mem hm), indexedHint_sound hv⟩
  · exact ⟨_,List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hj)), indexedHint_sound hv⟩
  · exact ⟨_,List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hj))), indexedHint_sound hv⟩
def fastState (cuts : List Nat) (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool) (T k : Nat) (ix : HintIndex)
    (st : PackedState) : Bool :=
  asc st.1 && !(mem1 T st.1) && packedZip (fastPair cuts masks pick bank u k ix st.1) (pairs st.1) st.2
theorem fastState_sound {cuts masks pick bank u T k n t st}
    (h : fastState cuts masks pick bank u T k (hintIndex n t) st = true) :
    stOK u T t k n (st.1, st.2.map (fastBank cuts)) = true := by
  obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨hb,packedZip_sound (fun _ _ h => fastPair_sound h) hc⟩
theorem fastLevelAll {cuts masks pick bank u R T E t k prev states}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (fastState cuts masks pick bank u T k (hintIndex (prev.map Prod.fst) t)) = true) :
    PackedLevel u T (k+1) states := by
  intro st hs
  apply stStep hb ht _ (fastState_sound (List.all_eq_true.mp hc st hs))
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
theorem fastLevelBy {cuts : PackedState → List Nat} {masks pick bank u R T E t k prev states}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (fun st => fastState (cuts st) masks pick bank u T k
      (hintIndex (prev.map Prod.fst) t) st) = true) : PackedLevel u T (k+1) states := by
  intro st hs
  apply stStep hb ht _ (fastState_sound (List.all_eq_true.mp hc st hs))
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
def localOK (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool)
    (T k : Nat) (ix : HintIndex) (st : PackedState) : Bool :=
  fastState st.2 masks pick bank u T k ix (st.1, List.replicate (pairs st.1).length 0)
theorem localLevelAll {masks pick bank u R T E t k prev states}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (localOK masks pick bank u T k (hintIndex (prev.map Prod.fst) t)) = true) :
    PackedLevel u T (k+1) states := by
  intro st hs
  have hh := fastState_sound (List.all_eq_true.mp hc st hs)
  apply stStep hb ht _ hh
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def sixBank : Nat := 0x111111e177e76e8011717fe111e7ee8010f17fe077e7ee8001101fe015e1ee80007011e077e5ee802030226033e3ee8011717f617761668
def sixSepIndex (j : Nat) : Nat := (0xb500000098000000200000009e0000001f00000019b00607000000004d005e710900af902c574c2a00007d5f17001536004b3461003500000000000000000000a3000000990094a7230000003d004fa0695441514355455d00000000a90000000d000000149f0b0a000068771a64164e00523f50005300000000000000000000c500000000aeadab33000000a800889324565c6340483b380000000000009d8110002b9a32473158000067661e6e1b260029283700460000000000000000000000000000a200000070000000000000008fc3b38a183c2e5a00000000000000008c00c400131d2d3e0000000022213a3000600001000800000000000000000000000000000000acb2bf0000000000000084000000877f114a000000000000b19574009b925b800f270000aa0085b41c2f007e04250002000000000000000000c200000000000000a1be00000000000091000000890000820e000000000000009c8e00006d598b830c0000009786968d12007b7a05000300000000000000000000ba000000bd00bcbb6f000000b700b9b86ab673723900444200000000a500c1c06b00a6a4750076490000000078007c6200006c650079000000 >>> (8 * j)) % 256
def sixMasks (v : Nat) : SepMask :=
  ((v &&& 0xffffffffffffffff) * 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001,
    (if v.testBit 0 then 0xffffffffffffffff else 0) |||
    (if v.testBit 1 then 0xffffffffffffffff0000000000000000 else 0) |||
    (if v.testBit 2 then 0xffffffffffffffff00000000000000000000000000000000 else 0) |||
    (if v.testBit 4 then 0xffffffffffffffff000000000000000000000000000000000000000000000000 else 0) |||
    (if v.testBit 8 then 0xffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 else 0) |||
    (if v.testBit 16 then 0xffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) |||
    (if v.testBit 32 then 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0))
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
structure DelayIndex where
  cut : Nat → Option CutV
  sep : Nat → Option (Nat × Nat)
  kw : Nat → Option KwD
  perm : Nat → Option (List Nat)
  next : Nat → Option (List Nat)
def indexedDelay (u : Bool) (k : Nat) (ix : DelayIndex)
    (xs : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  if i < 10000 then
    match ix.cut i with
    | some c => cutEval u k xs a b z ka kb c
    | none => false
  else if i < 20000 then
    match ix.sep (i - 10000) with
    | some q => sepEval u xs a b z ka kb q
    | none => false
  else if i < 30000 then
    match ix.kw (i - 20000) with
    | some q => !u && Nat.beq (kidN xs a b z ka kb).length (k+1) && kwList (kidN xs a b z ka kb) q
    | none => false
  else
    match ix.perm ((i - 30000) % 1024), ix.next ((i - 30000) / 1024) with
    | some perm, some st => beqL (sortN ((kidN xs a b z ka kb).map (permN perm))) st
    | _, _ => false
def rawLookup (v : List Nat) {α : Type} (f : Nat → α) : Nat → Option α :=
  let a := v.toArray
  fun j => a[j]?.map f
def delayOf (ix : HintIndex) : DelayIndex where
  cut := fun i => ix.cuts[i]?
  sep := fun i => ix.seps[i]?
  kw := fun i => ix.kws[i]?
  perm := fun i => ix.perms[i]?
  next := fun i => ix.next[i]?
def delayCert (codes : List Nat) : DelayIndex where
  cut := rawLookup certCutCodes (fun v => mkCut true certSlices (certCut v))
  sep := rawLookup certSepCodes (fun v => (v%128,v/128))
  kw := fun _ => none
  perm := rawLookup certPermCodes (certSwaps 15)
  next := rawLookup codes (fun v => (localState v).1)
def delayKid (cuts : List Nat) (pick : Nat → Nat) (u : Bool) (k : Nat) (ix : DelayIndex)
    (xs : List Nat) (a b z word op all am bm : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add xs.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
    (let i := packedDigit word (4 * op + packedSlot kk)
     let m := if kk.1 then all &&& am else all
     let m := if kk.2 then m &&& bm else m
     fastChoice cuts pick (indexedDelay u k ix xs a b z kk.1 kk.2) i m)
def delayPair (cuts : List Nat) (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool) (k : Nat) (ix : DelayIndex) (s : List Nat)
    (p : Nat × Nat × List Nat) (word : Nat) : Bool :=
  let a := masks p.1
  let b := masks p.2.1
  let common := p.2.2.foldl (fun v e => v &&& agreement bank (masks e)) bank
  (opsOf u).all fun op =>
    let z := nb op p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      (let zm := agreement bank (nb op a.1 b.1, nb op a.2 b.2)
       keeps.all (delayKid cuts pick u k ix p.2.2 p.1 p.2.1 z word op (common &&& zm) (agreement bank a) (agreement bank b)))
def delayState (cuts : List Nat) (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool) (T k : Nat) (ix : DelayIndex)
    (st : PackedState) : Bool :=
  asc st.1 && !(mem1 T st.1) && packedZip (delayPair cuts masks pick bank u k ix st.1) (pairs st.1) st.2
def delayLocal (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool)
    (T k : Nat) (ix : DelayIndex) (st : PackedState) : Bool :=
  delayState st.2 masks pick bank u T k ix (st.1, List.replicate (pairs st.1).length 0)
set_option maxRecDepth 100000 in
theorem asDelay (u k d xs a b z ka kb i) :
    indexedDelay u k (delayOf d) xs a b z ka kb i = indexedHint u k d xs a b z ka kb i := by
  by_cases h₁ : i < 10000
  · cases hg : d.cuts[i]? <;> simp only [indexedDelay,indexedHint,delayOf,h₁,ite_true,hg]
  by_cases h₂ : i < 20000
  · cases hg : d.seps[i-10000]? <;> simp only [indexedDelay,indexedHint,delayOf,h₁,h₂,ite_true,ite_false,hg]
  by_cases h₃ : i < 30000
  · cases hg : d.kws[i-20000]? <;> simp only [indexedDelay,indexedHint,delayOf,h₁,h₂,h₃,ite_true,ite_false,hg]
  · cases hg : d.perms[(i-30000)%1024]? <;> cases ht : d.next[(i-30000)/1024]? <;>
      simp only [indexedDelay,indexedHint,delayOf,h₁,h₂,h₃,ite_false,hg,ht]
theorem dRawEq (f : Nat → α) (xs : List Nat) : rawLookup xs f = fun i => (xs.map f).toArray[i]? := by
  funext i
  simp [rawLookup,List.getElem?_map]
theorem dRawEq2 (f : Nat → α) (g : α → β) (xs : List Nat) :
    rawLookup xs (fun v => g (f v)) = fun i => ((xs.map f).map g).toArray[i]? := by
  funext i
  simp [rawLookup,List.getElem?_map,Function.comp_def]
set_option maxRecDepth 100000 in
theorem rawDecodedIdx (raw : List Nat) :
    delayCert raw = delayOf (hintIndex ((raw.map localState).map Prod.fst) certTabs) := by
  exact congrArg₂ (fun c p => DelayIndex.mk c (rawLookup certSepCodes (fun v => (v%128,v/128)))
      (fun _ => none) (rawLookup certPermCodes (certSwaps 15)) p)
    (dRawEq2 certCut (mkCut true certSlices) certCutCodes)
    (dRawEq2 localState Prod.fst raw) |>.trans (by
      simp only [delayOf,hintIndex,certTabs,certCuts,certSeps,certPerms,Tabs.cuts,Tabs.seps,Tabs.kws,Tabs.perms]
      rw [dRawEq (fun v => (v%128,v/128)) certSepCodes, dRawEq (certSwaps 15) certPermCodes]
      rfl)
theorem delayVerified (u k raw xs a b z ka kb i) :
    indexedDelay u k (delayCert raw) xs a b z ka kb i =
      indexedHint u k (hintIndex ((raw.map localState).map Prod.fst) certTabs) xs a b z ka kb i := by
  rw [rawDecodedIdx, asDelay]
theorem delayAll (masks pick bank u T k raw st) :
    delayLocal masks pick bank u T k (delayCert raw) st =
    localOK masks pick bank u T k (hintIndex ((raw.map localState).map Prod.fst) certTabs) st := by
  let d := delayCert raw
  let h := hintIndex ((raw.map localState).map Prod.fst) certTabs
  have ie (xs a b z ka kb) : indexedDelay u k d xs a b z ka kb = indexedHint u k h xs a b z ka kb :=
    funext (delayVerified u k raw xs a b z ka kb)
  have ke (cuts xs a b z w op m am bm) : delayKid cuts pick u k d xs a b z w op m am bm =
      fastKid cuts pick u k h xs a b z w op m am bm := by
    funext kk
    simp only [delayKid,fastKid,ie]
  have pe (cuts signals) : delayPair cuts masks pick bank u k d signals =
      fastPair cuts masks pick bank u k h signals := by
    funext p word
    simp only [delayPair,fastPair,ke]
  change delayState st.2 masks pick bank u T k d _ = fastState st.2 masks pick bank u T k h _
  simp only [delayState,fastState,pe]
def queryCode {α : Type} (n : Nat) (entry : Nat → Nat) (f : Nat → α) (i : Nat) : Option α :=
    if i<n then some (f (entry i)) else none
def lookupCut {α : Type} (f : Nat → α) : Nat → Option α := queryCode 2056 limbCut f
def lookupSep {α : Type} (f : Nat → α) : Nat → Option α := queryCode 198 limbSep f
def lookupPerm {α : Type} (f : Nat → α) : Nat → Option α := queryCode 720 limbPerm f
def limbRaw : Nat → Array (List Nat)
  | 4 => #[local4g0]
  | 5 => #[local5g0,local5g1,local5g2,local5g3,local5g4,local5g5,local5g6,local5g7,local5g8,local5g9,local5g10,local5g11,local5g12,local5g13,local5g14,local5g15]
  | 6 => #[local6g0,local6g1,local6g2,local6g3,local6g4,local6g5,local6g6,local6g7,local6g8,local6g9,local6g10,local6g11,local6g12,local6g13,local6g14,local6g15,local6g16,local6g17,local6g18,local6g19,local6g20,local6g21,local6g22,local6g23,local6g24,local6g25,local6g26,local6g27,local6g28,local6g29,local6g30,local6g31,local6g32,local6g33,local6g34,local6g35,local6g36,local6g37,local6g38]
  | 7 => #[local7g0,local7g1,local7g2,local7g3,local7g4,local7g5,local7g6,local7g7,local7g8,local7g9,local7g10,local7g11,local7g12,local7g13,local7g14,local7g15,local7g16,local7g17,local7g18,local7g19,local7g20,local7g21,local7g22,local7g23,local7g24]
  | 8 => #[local8g0,local8g1,local8g2,local8g3,local8g4,local8g5]
  | 9 => #[local9g0]
  | 10 => #[local10g0]
  | 11 => #[local11g0]
  | 12 => #[local12g0]
  | _ => #[]
def limbNext (lev i : Nat) := (limbRaw lev)[i/24]?.bind (fun xs => xs[i%24]?)
theorem queryModel {α : Type} (n : Nat) (g : Nat → Nat) (f : Nat → α) :
    queryCode n g f = rawLookup ((List.range n).map g) f := by
  funext i
  by_cases hi : i < n
  · simp [queryCode,rawLookup,List.getElem?_map,List.getElem?_eq_getElem,hi]
  · have eq : (List.range n)[i]? = none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)
    simp [queryCode,rawLookup,List.getElem?_map,hi,eq]
def limbRawList (n lev : Nat) := (List.range n).map (fun i => (limbNext lev i).getD 0)
def limbIdxAt (n k : Nat) : DelayIndex where
  cut := lookupCut (fun v => mkCut true certSlices (certCut v))
  sep := lookupSep (fun v => (v%128,v/128))
  kw := fun _ => none
  perm := lookupPerm (certSwaps 15)
  next := queryCode n (fun i => (limbNext k i).getD 0) (fun v => (localState v).1)
theorem limbModel (n lev : Nat)
    (hc : certCutCodes = (List.range 2056).map limbCut)
    (hs : certSepCodes = (List.range 198).map limbSep)
    (hp : certPermCodes = (List.range 720).map limbPerm) :
    limbIdxAt n lev = delayCert (limbRawList n lev) := by
  unfold limbIdxAt delayCert limbRawList lookupCut lookupSep lookupPerm
  rw [hc,hs,hp]
  simp only [queryModel]
def limbCount : Nat → Nat
  | 4 => 16
  | 5 => 379
  | 6 => 913
  | 7 => 580
  | 8 => 132
  | 9 => 22
  | 10 => 5
  | 11 => 1
  | 12 => 1
  | _ => 0
def limbRows (k : Nat) : List PackedState := (limbRawList (limbCount k) k).map localState
def limbCheck (T k : Nat) : PackedState → Bool :=
  delayLocal sixMasks sixSepIndex sixBank true T k (limbIdxAt (limbCount k) k)
theorem limbCheckCorrect (T k : Nat) (s : PackedState) :
    limbCheck T k s = localOK sixMasks sixSepIndex sixBank true T k (hintIndex ((limbRows k).map Prod.fst) certTabs) s := by
  unfold limbCheck limbRows
  rw [limbModel _ _ rfl rfl rfl,delayAll]
theorem limbStep {k : Nat} {D : List PackedState} (hn : PackedLevel true stopT k (limbRows k))
    (h : D.all (limbCheck stopT k) = true) : PackedLevel true stopT (k+1) D := by
  apply localLevelAll (k:=k) (prev:=limbRows k) (masks:=sixMasks) (pick:=sixSepIndex) (bank:=sixBank) stopB certTabsValid hn
  apply List.all_eq_true.mpr
  intro st hs
  rw [← limbCheckCorrect]
  exact List.all_eq_true.mp h st hs
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def limbChunk (k i : Nat) : Bool :=
  (((limbRows k).drop (i*64)).take 64).all (limbCheck stopT (k-1))
theorem limbBefore : PackedLevel true stopT 3 (limbRows 3) := by intro s hs; cases hs
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local4part0 : limbChunk 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part0 : limbChunk 5 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part1 : limbChunk 5 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part2 : limbChunk 5 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part3 : limbChunk 5 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part4 : limbChunk 5 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part5 : limbChunk 5 5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part0 : limbChunk 6 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part1 : limbChunk 6 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part2 : limbChunk 6 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part3 : limbChunk 6 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part4 : limbChunk 6 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part5 : limbChunk 6 5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part6 : limbChunk 6 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part7 : limbChunk 6 7 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part8 : limbChunk 6 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part9 : limbChunk 6 9 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part10 : limbChunk 6 10 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part11 : limbChunk 6 11 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part12 : limbChunk 6 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part13 : limbChunk 6 13 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part14 : limbChunk 6 14 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part0 : limbChunk 7 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part1 : limbChunk 7 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part2 : limbChunk 7 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part3 : limbChunk 7 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part4 : limbChunk 7 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part5 : limbChunk 7 5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part6 : limbChunk 7 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part7 : limbChunk 7 7 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part8 : limbChunk 7 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part9 : limbChunk 7 9 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local8part0 : limbChunk 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local8part1 : limbChunk 8 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local8part2 : limbChunk 8 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local9part0 : limbChunk 9 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local10part0 : limbChunk 10 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local11part0 : limbChunk 11 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local12part0 : limbChunk 12 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated4 : PackedLevel true stopT 4 (limbRows 4) := by
  apply limbStep limbBefore
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local4part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated5 : PackedLevel true stopT 5 (limbRows 5) := by
  apply limbStep localValidated4
  apply packedAllChunks 64 6 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local5part0
  · exact local5part1
  · exact local5part2
  · exact local5part3
  · exact local5part4
  · exact local5part5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated6 : PackedLevel true stopT 6 (limbRows 6) := by
  apply limbStep localValidated5
  apply packedAllChunks 64 15 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local6part0
  · exact local6part1
  · exact local6part2
  · exact local6part3
  · exact local6part4
  · exact local6part5
  · exact local6part6
  · exact local6part7
  · exact local6part8
  · exact local6part9
  · exact local6part10
  · exact local6part11
  · exact local6part12
  · exact local6part13
  · exact local6part14
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated7 : PackedLevel true stopT 7 (limbRows 7) := by
  apply limbStep localValidated6
  apply packedAllChunks 64 10 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local7part0
  · exact local7part1
  · exact local7part2
  · exact local7part3
  · exact local7part4
  · exact local7part5
  · exact local7part6
  · exact local7part7
  · exact local7part8
  · exact local7part9
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated8 : PackedLevel true stopT 8 (limbRows 8) := by
  apply limbStep localValidated7
  apply packedAllChunks 64 3 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local8part0
  · exact local8part1
  · exact local8part2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated9 : PackedLevel true stopT 9 (limbRows 9) := by
  apply limbStep localValidated8
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local9part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated10 : PackedLevel true stopT 10 (limbRows 10) := by
  apply limbStep localValidated9
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local10part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated11 : PackedLevel true stopT 11 (limbRows 11) := by
  apply limbStep localValidated10
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local11part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated12 : PackedLevel true stopT 12 (limbRows 12) := by
  apply limbStep localValidated11
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local12part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem signedThirteen : LowN true stopR stopT 13 :=
  packedLowSearch stopB localValidated12 (by decide +kernel)
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux.SevenRoot
open PEqualNP.CircuitLowerBounds
def sevenT : Nat := 0xfffffffffffffffefffffffefffefee8
def sevenR : List Nat := [0,1,2,3,4,5,6]
def sevenE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17),(5,1,33),(6,1,65)]
theorem sevenB : baseOK sevenT sevenR sevenE = true := by decide +kernel
def sevenSlices : List SliceD := [(0x55555555555555555555555555555555,13,[1,2,3,4,5,6]),(0x33333333333333333333333333333333,13,[0,2,3,4,5,6]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,13,[0,1,3,4,5,6]),(0xff00ff00ff00ff00ff00ff00ff00ff,13,[0,1,2,4,5,6]),(0xffff0000ffff0000ffff0000ffff,13,[0,1,2,3,5,6]),(0xffffffff00000000ffffffff,13,[0,1,2,3,4,6]),(0xffffffffffffffff,13,[0,1,2,3,4,5])]
theorem sevenSlice0 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0x55555555555555555555555555555555,13,[1,2,3,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice1 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0x33333333333333333333333333333333,13,[0,2,3,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice2 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,13,[0,1,3,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice3 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xff00ff00ff00ff00ff00ff00ff00ff,13,[0,1,2,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice4 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xffff0000ffff0000ffff0000ffff,13,[0,1,2,3,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice5 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xffffffff00000000ffffffff,13,[0,1,2,3,4,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice6 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xffffffffffffffff,13,[0,1,2,3,4,5]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenValid (hl : LowN true stopR stopT 13) : ∀ s ∈ sevenSlices, SliceN true sevenR sevenT s := by
  unfold sevenSlices
  simp only [List.forall_mem_cons]
  exact ⟨sevenSlice0 hl,sevenSlice1 hl,sevenSlice2 hl,sevenSlice3 hl,sevenSlice4 hl,sevenSlice5 hl,sevenSlice6 hl,by simp⟩
def sevenCuts : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])]
def sevenTab : Tabs := (sevenCuts.map (mkCut true sevenSlices),[(5,4),(3,1),(3,0),(3,2),(5,1),(5,0),(9,1),(9,0),(17,1),(17,0),(33,1),(33,0),(65,1),(65,0),(6,2),(10,2),(18,2),(34,2),(66,2),(12,4),(20,4),(36,4),(68,4),(24,8),(40,8),(72,8),(48,16),(80,16),(96,32)],[],[])
theorem sevenTabOK (hl : LowN true stopR stopT 13) : TabsP true sevenR sevenT sevenTab :=
  ⟨cutsGood (sevenValid hl) (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def rootState : StD := (sevenR.map xN, [[0,1,10000,10001,10002],[0,2,10003,10004,10005],[0,3,10003,10006,10007],[0,4,10003,10008,10009],[0,5,10003,10010,10011],[0,6,10003,10012,10013],[1,2,10001,10014,10004],[1,3,10001,10015,10006],[1,4,10001,10016,10008],[1,5,10001,10017,10010],[1,6,10001,10018,10012],[2,3,10004,10019,10006],[2,4,10004,10020,10008],[2,5,10004,10021,10010],[2,6,10004,10022,10012],[3,4,10006,10023,10008],[3,5,10006,10024,10010],[3,6,10006,10025,10012],[4,5,10008,10026,10010],[4,6,10008,10027,10012],[5,6,10010,10028,10012]])
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem rootCheck : stOK true sevenT sevenTab 13 [] rootState = true := by decide +kernel
theorem signedFifteen (hl : LowN true stopR stopT 13) : LowN true sevenR sevenT 15 := by
  apply lowOf sevenB
  have h := stStep sevenB (sevenTabOK hl) (by simp) rootCheck
  simpa only [rootState,sevenR,rootsW,List.map_map,Function.comp_def] using h
def target : (Fin 7 → Bool) → Bool := (fun x : Fin 7 → Bool => decide (2 ≤ ((List.ofFn x).count true)))
def theInputs : List Sig := rootsW [0,1,2,3,4,5,6]
def graph : Sig := W sevenT
theorem graph_proper : proper graph := (baseOK_ok sevenB).prop
def sample (r : Row) (i : Fin 7) : Bool := bit r (theInputs.getD i.val zero)
theorem theList : List.ofFn (fun i : Fin 7 => theInputs.getD i.val zero) = theInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = theInputs.map (bit r) := by
  rw [←theList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem theTable : ∀ r : Row, bit r graph = target (sample r) := by unfold target; decide +kernel
theorem theEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates theInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physical (u : Bool) (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : u=false → ∀ g ∈ C.gates, isNot g=false)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live u graph k theInputs.toFinset := by
  have b := baseOK_ok sevenB
  have goalEq : (execute C.gates theInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (theEval C legal C.output r).trans ((computes (sample r)).trans (theTable r).symm)
  have out := get_rep (u:=u) (execute C.gates theInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W sevenT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=u) C.gates theInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : theInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = theInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run theInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes {u : Bool} {L : Nat} (low : LowN u [0,1,2,3,4,5,6] sevenT L) : ∀ k, k < L → ¬Live u graph k theInputs.toFinset := by
  intro k small run
  have steps := list_run run theInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (theInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := low q bank built hit
  omega
theorem paidFifteen (hl : LowN true stopR stopT 13) (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = target x) : 15 ≤ C.gates.countP (fun g => !isNot g) := by
  obtain ⟨k,hk,run⟩ := physical true C fan (by simp) computes
  by_contra h
  exact excludes (signedFifteen hl) k (by omega) run
theorem noCircuit (lowSix : LowN true stopR stopT 13)
    (mono : ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C →
       (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = target x) → 16 ≤ C.size) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 7 target 15 := by
  rintro ⟨C,fan,small,correct⟩
  classical
  by_cases only : ∀ g ∈ C.gates, isNot g = false
  · have hm : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      obtain ⟨ops,inputs⟩ := fan g hg
      refine ⟨?_,inputs⟩
      rcases ops with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have hn := only g hg
        change g.op = .not at h
        simp [isNot,h] at hn
    have h := mono C hm correct
    omega
  · push Not at only
    obtain ⟨g,hg,hop⟩ := only
    have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
      rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h|h
      · exact h
      · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
        cases hn : isNot g <;> simp_all
    have bound := paidFifteen lowSix C fan correct
    change C.gates.length ≤ 15 at small
    omega
end PEqualNP.Outside.L_meta_10393_aux.SevenRoot

namespace PEqualNP.Outside.L_meta_10393_aux

namespace ThresholdSixBound.Leaf5459
def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b
theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide
abbrev Formula (n : Nat) := BinaryTree (Sum (Fin n) Bool)
def formEval {n : Nat} : Formula n → (Fin n → Bool) → Bool
  | .nil, _ => false
  | .node (.inl i) _ _, x => x i
  | .node (.inr false) l r, x => formEval l x || formEval r x
  | .node (.inr true) l r, x => formEval l x && formEval r x
def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)
def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)
def formOcc {n : Nat} : Formula n → Fin n → Nat
  | .nil, _ => 0
  | .node (.inl j) _ _, i => if j = i then 1 else 0
  | .node (.inr _) l r, i => formOcc l i + formOcc r i
open scoped BigOperators
def cCube {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) : Finset (α → Bool) :=
  Fintype.piFinset fun a => if a ∈ s then {b a} else Finset.univ
theorem cCubeMember {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b f : α → Bool) :
    f ∈ cCube s b ↔ ∀ a ∈ s, f a = b a := by
  simp only [cCube, Fintype.mem_piFinset]
  constructor
  · intro h a ha
    simpa only [ite_eq_left ha, Finset.mem_singleton] using h a
  · intro h a
    by_cases ha : a ∈ s
    · simpa only [ite_eq_left ha, Finset.mem_singleton] using h a ha
    · simp only [ite_eq_right ha, Finset.mem_univ]
theorem cCubeCard {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card = ∏ a : α, if a ∈ s then 1 else 2 := by
  rw [cCube, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro a ha
  by_cases hs : a ∈ s <;> simp [hs]
theorem cCubeVolume {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card * 2 ^ s.card = 2 ^ Fintype.card α := by
  rw [cCubeCard]
  have hs : (∏ a : α, if a ∈ s then 2 else 1) = 2 ^ s.card := by simp
  rw [← hs, ← Finset.prod_mul_distrib]
  have he : (∏ a : α, (if a ∈ s then 1 else 2) * (if a ∈ s then 2 else 1)) =
      ∏ _a : α, 2 := by
    apply Finset.prod_congr rfl
    intro a ha
    by_cases h : a ∈ s <;> simp [h]
  rw [he]
  simp
section Generic
variable {α : Type} {β : Type}
def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f
theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩
theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih
theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩
theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)
def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws
section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}
theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d
theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)
theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)
theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2
theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩
theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega
theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)
end Run
def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z
theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h
theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih
theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩
end Generic
def MonoA : Fin 4 → Prop := fun k => k.val < 2
theorem mono_cases (k : Fin 4) (hk : MonoA k) : k=0 ∨ k=1 := by fin_cases k <;> simp_all [MonoA]
end ThresholdSixBound.Leaf5459
namespace ThresholdSixBound.Six
open Leaf5459 PEqualNP.Outside.L_meta_10393_aux
abbrev BF := (Fin 6 → Bool) → Bool
def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)
def var (i : Fin 6) : BF := fun x => x i
def ThrL (V : Fin 6 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧ ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true
def target (x : Fin 6 → Bool) : Bool := decide (2 ≤ (List.ofFn x).count true)
def MonoF (w : BF) : Prop := ∀ x y, (∀ i, x i = true → y i = true) → w x = true → w y = true
theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl
theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl
def sample (r : Row) (i : Fin 6) : Bool := bit r (W (xN i.val))
def sem (f : BF) : Wire Row := fun r => f (sample r)
theorem initialCov (w : BF) (hw : ∃ i, w = var i) :
    Available true ((rootsW stopR).map observe) (sem w) := by
  obtain ⟨i,rfl⟩ := hw
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨W (xN i.val),?_,rfl⟩
  apply List.mem_map.mpr
  exact ⟨i.val,(by fin_cases i <;> decide),rfl⟩
theorem simulate (m : Nat) (S : BF → Prop) (f : BF) (hu : UC gF MonoA m S f)
    (p : Nat) (bank : List (Wire Row)) (rb : Reach true ((rootsW stopR).map observe) p bank)
    (supply : ∀ w, S w → Available true bank (sem w)) :
    ∃ p' bank', Reach true ((rootsW stopR).map observe) p' bank' ∧
      Available true bank' (sem f) ∧ p' ≤ p+m := by
  induction m generalizing S f p bank with
  | zero => exact ⟨p,bank,rb,supply f hu,by omega⟩
  | succ m ih =>
    rcases hu with old | ⟨k,a,b,hk,ha,hb,run⟩
    · obtain ⟨j,ws,hr,ht,le⟩ := ih S f old p bank rb supply
      exact ⟨j,ws,hr,ht,by omega⟩
    · let op := decide (k=1)
      have eq : sem (gF k a b) = combine op (sem a) (sem b) := by
        rcases mono_cases k hk with rfl | rfl <;> rfl
      have next := Reach.two op rb (supply _ ha) (supply _ hb)
      have supp : ∀ w, (w = gF k a b ∨ S w) → Available true (combine op (sem a) (sem b)::bank) (sem w) := by
        rintro w (rfl | orig)
        · exact Or.inl (by simp [eq])
        · exact available_cons _ (supply _ orig)
      obtain ⟨j,ws,hr,ht,le⟩ := ih _ f run (p+1) _ next supp
      exact ⟨j,ws,hr,ht,by omega⟩
def SixLow := LowN true stopR stopT 13
theorem ucLower (lb : SixLow) (hu : UC gF MonoA 12 (fun w => ∃ i, w = var i) target) : False := by
  obtain ⟨k,ws,rb,ht,le⟩ := simulate 12 _ _ hu 0 _ Reach.start initialCov
  have eq : ∀ r : Row, sem target r = bit r (W stopT) := by decide +kernel
  have ee : sem target = observe (W stopT) := funext eq
  rw [ee] at ht
  have bot := lb k ws rb ht
  omega
theorem uc_mono : ∀ m (S : BF → Prop) f, (∀ w, S w → MonoF w) →
    UC gF MonoA m S f → MonoF f
  | 0,_,f,hs,h => hs f h
  | m+1,S,f,hs,h => by
    rcases h with ho | ⟨k,a,b,hk,ha,hb,ho⟩
    · exact uc_mono m S f hs ho
    · refine uc_mono m _ f ?_ ho
      rintro w (rfl | hw)
      · intro x y hxy hx
        rcases mono_cases k hk with rfl | rfl
        · rw [gF_and] at hx ⊢
          exact Bool.and_eq_true_iff.mpr
            ⟨hs _ ha x y hxy (Bool.and_eq_true_iff.mp hx).1,hs _ hb x y hxy (Bool.and_eq_true_iff.mp hx).2⟩
        · rw [gF_or] at hx ⊢
          simp only [Bool.or_eq_true] at hx ⊢
          exact hx.imp (hs _ ha x y hxy) (hs _ hb x y hxy)
      · exact hs _ hw
theorem M6 (lb : SixLow) {f : BF} (h : ThrL (fun _ => True) f)
    (hu : UC gF MonoA 12 (fun w => ∃ i, w = var i) f) : False := by
  have mono := uc_mono 12 _ f (by rintro w ⟨i,rfl⟩; exact fun _ _ hxy => hxy i) hu
  have small : ∀ x : Fin 6 → Bool, target x = false →
      ∃ i : Fin 6, ∀ j, x j = true → singleInput i j = true := by decide +kernel
  have large : ∀ x : Fin 6 → Bool, target x = true →
      ∃ i j : Fin 6, i ≠ j ∧ ∀ k, pairInput i j k = true → x k = true := by decide +kernel
  have ef : f = target := by
    funext x
    cases e : target x with
    | true =>
      obtain ⟨i,j,hn,p⟩ := large x e
      exact mono _ _ p (h.2 i j trivial trivial hn)
    | false =>
      obtain ⟨i,p⟩ := small x e
      cases v : f x with
      | false => rfl
      | true => exact Bool.noConfusion ((h.1 i trivial).symm.trans (mono _ _ p v))
  rw [ef] at hu
  exact ucLower lb hu
end ThresholdSixBound.Six

namespace ThresholdSixBound.Seven
open Leaf5459
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
abbrev BF := (Fin 7 → Bool) → Bool
def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)
def var (i : Fin 7) : BF := fun x => x i
def zF : BF := fun _ => false
def rst (p : Fin 7) (a : BF) : BF := fun x => a (Function.update x p false)
def ThrL (V : Fin 7 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true
theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]
theorem upd_single {i p : Fin 7} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]
theorem upd_pair {i j p : Fin 7} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]
theorem rst_var_self (p : Fin 7) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]
theorem rst_var_ne {i p : Fin 7} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]
theorem var_inj {i j : Fin 7} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm
theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 7 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])
def dcount (p : Fin 7) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)
theorem dcount_cons (p : Fin 7) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]
theorem dcount_rep (p : Fin 7) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all
theorem pot_dead {A : Fin 4 → Prop} (p : Fin 7) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2
theorem ex_third : ∀ p q : Fin 7, ∃ r, r ≠ p ∧ r ≠ q := by decide
theorem thr_rst {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 7) :
    (∀ j, rst p F (singleInput (p.succAbove j)) = false) ∧
    (∀ j j', j ≠ j' → rst p F (pairInput (p.succAbove j) (p.succAbove j')) = true) := by
  refine ⟨fun j => ?_, fun j j' hj => ?_⟩
  · show F (Function.update (singleInput (p.succAbove j)) p false) = false
    rw [upd_single (Fin.succAbove_ne p j)]
    exact hF.1 _ trivial
  · show F (Function.update (pairInput (p.succAbove j) (p.succAbove j')) p false) = true
    rw [upd_pair (Fin.succAbove_ne p j) (Fin.succAbove_ne p j')]
    exact hF.2 _ _ trivial trivial fun h => hj (Fin.succAbove_right_injective h)
theorem thr_rst_ne {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 7) : rst p F ≠ zF := by
  intro h
  have := (thr_rst hF p).2 0 1 (by decide)
  rw [h] at this
  exact Bool.noConfusion this
theorem thr_ne_zero {F : BF} (hF : ThrL (fun _ => True) F) : F ≠ zF := by
  intro h
  have := hF.2 0 1 trivial trivial (by decide)
  rw [h] at this
  exact Bool.noConfusion this
theorem to_run {A : Fin 4 → Prop} {F : BF} (hF : ThrL (fun _ => True) F) {t : ℕ}
    (hu : UC gF A t (fun w => ∃ i, w = var i) F) :
    ∃ t', t' ≤ t ∧ ∃ ws : List BF, (∀ w ∈ ws, ∃ i, w = var i) ∧
      TR gF (fun k _ _ => A k) [F] t' ws := by
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gF zF A (fun _ => True) (fun _ _ _ _ _ => trivial)
    gF_zero_left gF_zero_right gF_self t _ F (fun _ _ => trivial) (thr_ne_zero hF) hu
  exact ⟨t', ht, ws, fun w hw => (hws w hw).1, TR.monoC (fun _ _ _ h => h.1) hr⟩
theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl
theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)
def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])
theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 7 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl
theorem wires_eq (x : Fin 7 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]
theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)
def target (x : Fin 7 → Bool) : Bool := decide (2 ≤ (List.ofFn x).count true)
theorem targetThr : ThrL (fun _ => True) target := by
  constructor <;> decide +kernel
def proj (p : Fin 7) (w : BF) : Six.BF := fun y => w (p.insertNth false y)
theorem projVar (p : Fin 7) (j : Fin 6) : proj p (var (p.succAbove j)) = Six.var j := by
  funext y
  simp [proj, var, Six.var]
theorem projectThr : ∀ p : Fin 7, Six.ThrL (fun _ => True) (proj p (rst p target)) := by
  unfold Six.ThrL
  decide +kernel
theorem transfer {A : Fin 4 → Prop} (low : ℕ)
    (lb : ∀ (f : Six.BF), Six.ThrL (fun _ => True) f →
      ∀ k : ℕ, UC Six.gF A k (fun w => ∃ i, w = Six.var i) f → low ≤ k)
    {s : ℕ} {ws : List BF}
    (h : TR gF (fun k _ _ => A k) [target] s ws)
    (hw : ∀ w ∈ ws, ∃ i, w = var i) : low+2 ≤ s := by
  have hF := targetThr
  rcases s with _ | s
  · have hp := (TR.inv h).1 rfl
    obtain ⟨i, hi⟩ := hw target (hp.mem_iff.2 (by simp))
    have := hF.1 i trivial
    rw [hi] at this
    simp [var, singleInput] at this
  · obtain ⟨k, u, a, b, r, -, hp, hr⟩ := (TR.inv h).2 s rfl
    obtain ⟨p, rfl⟩ := hw a (hp.mem_iff.2 (by simp))
    obtain ⟨q, rfl⟩ := hw b (hp.mem_iff.2 (by simp))
    have hcnt : dcount p ws = dcount p (var p :: var q :: r) := hp.countP_eq _
    have key : 2 ≤ dcount p ws := by
      rw [hcnt, dcount_cons, dcount_cons]
      by_cases hpq : p = q
      · subst hpq; simp [rst_var_self]
      by_cases hmem : var p ∈ r
      · have : 1 ≤ dcount p r := by
          unfold dcount
          exact List.countP_pos_iff.2 ⟨var p, hmem, by simp [rst_var_self]⟩
        simp only [rst_var_self, ite_true]
        omega
      exfalso
      have hrv : ∀ w ∈ r, ∃ i, i ≠ p ∧ w = var i := by
        intro w hw'
        obtain ⟨i, hi⟩ := hw w (hp.mem_iff.2 (by simp [hw']))
        refine ⟨i, ?_, hi⟩
        rintro rfl
        exact hmem (hi ▸ hw')
      obtain ⟨β, c, hβ⟩ := (zeroGate_canalizes k).1
      cases β
      · obtain ⟨r₀, hr1, hr2⟩ := ex_third p q
        have hd := TRF_det hr (pairInput p r₀) (singleInput r₀) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p r₀) = false := by
              simp [var, pairInput, Ne.symm hpq, Ne.symm hr2]
            have e2 : var q (singleInput r₀) = false := by simp [var, singleInput, Ne.symm hr2]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) target (by simp)
        rw [hF.1 r₀ trivial, hF.2 p r₀ trivial trivial (Ne.symm hr1)] at hd
        exact Bool.noConfusion hd
      · have hd := TRF_det hr (pairInput p q) (singleInput q) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p q) = true := by simp [var, pairInput]
            have e2 : var q (singleInput q) = true := by simp [var, singleInput]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) target (by simp)
        rw [hF.1 q trivial, hF.2 p q trivial trivial hpq] at hd
        exact Bool.noConfusion hd
    obtain ⟨h1, h2⟩ := pot_dead p (thr_rst_ne hF p) h
    have h3 := h2 (fun w => ∃ j, w = var (p.succAbove j)) (by
      intro w hw' hwz
      obtain ⟨i, rfl⟩ := hw w hw'
      by_cases hi : i = p
      · subst hi; exact absurd (rst_var_self i) hwz
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
        exact ⟨j, by rw [rst_var_ne hi, hj]⟩)
    have mapped := UC_map (G' := Six.gF) (proj p) (fun _ _ _ => rfl)
      _ _ (fun w => ∃ i, w = Six.var i) _
      (by rintro w ⟨i, rfl⟩; exact ⟨i, projVar p i⟩) h3
    have hh := lb _ (projectThr p) _ mapped
    omega
end ThresholdSixBound.Seven
namespace ThresholdSixBound.OneShare
open Leaf5459
open scoped BigOperators
def wOcc {n : Nat} (x : Fin n → Bool) : Formula n → Nat
  | .nil => 0
  | .node (.inl i) _ _ => (x i).toNat
  | .node (.inr _) l r => wOcc x l + wOcc x r
def gCut {n d : Nat} (X : Fin d → Fin n → Bool) (l r : Formula n) (i : Fin d) : Option Bool :=
  match formEval l (X i), formEval r (X i) with
  | true,false => some false
  | false,true => some true
  | _,_ => none
def gCuts {n d : Nat} (X : Fin d → Fin n → Bool) : Formula n → List (Fin d → Option Bool)
  | .nil => []
  | .node (.inl _) _ _ => []
  | .node (.inr false) l r => gCuts X l ++ gCuts X r
  | .node (.inr true) l r => gCut X l r :: (gCuts X l ++ gCuts X r)
def width {d : Nat} (L : List (Fin d → Option Bool)) (i : Fin d) := L.countP (fun c => (c i).isSome)
theorem weight_bound {n d : Nat} (X : Fin d → Fin n → Bool) (t : Formula n) (i : Fin d) :
    width (gCuts X t) i + (formEval t (X i)).toNat ≤ wOcc (X i) t := by
  induction t with
  | nil => simp [width,gCuts,formEval,wOcc]
  | node a l r hl hr =>
    cases a with
    | inl j => simp [width,gCuts,formEval,wOcc]
    | inr op =>
      cases op <;> cases el : formEval l (X i) <;> cases er : formEval r (X i) <;>
        simp [width,gCuts,formEval,gCut,wOcc,el,er,List.countP_append] at * <;> omega
def FormulaSeparates {d : Nat} (L : List (Fin d → Option Bool)) (i j : Fin d) :=
  ∃ c ∈ L, (c i = some false ∧ c j = some true) ∨ (c i = some true ∧ c j = some false)
theorem generalized_separator {n d : Nat} (X : Fin d → Fin n → Bool) (t : Formula n) (i j : Fin d)
    (hp : formEval t (fun k => X i k || X j k) = true)
    (hi : formEval t (X i) = false) (hj : formEval t (X j) = false) :
    FormulaSeparates (gCuts X t) i j := by
  induction t with
  | nil => simp [formEval] at hp
  | node a l r hl hr =>
    cases a with
    | inl k =>
      change X i k = false at hi
      change X j k = false at hj
      change X i k || X j k = true at hp
      simp [hi,hj] at hp
    | inr op =>
      cases op with
      | false =>
        simp only [formEval, Bool.or_eq_true] at hp
        simp only [formEval, Bool.or_eq_false_iff] at hi hj
        rcases hp with hp | hp
        · obtain ⟨c, hc, hs⟩ := hl hp hi.1 hj.1
          exact ⟨c, by simp [gCuts, hc], hs⟩
        · obtain ⟨c, hc, hs⟩ := hr hp hi.2 hj.2
          exact ⟨c, by simp [gCuts, hc], hs⟩
      | true =>
        simp only [formEval, Bool.and_eq_true] at hp
        have liftL (hli : formEval l (X i) = false)
            (hlj : formEval l (X j) = false) :
            ∃ c ∈ gCuts X (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hl hp.1 hli hlj
          exact ⟨c, by simp [gCuts, hc], hs⟩
        have liftR (hri : formEval r (X i) = false)
            (hrj : formEval r (X j) = false) :
            ∃ c ∈ gCuts X (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hr hp.2 hri hrj
          exact ⟨c, by simp [gCuts, hc], hs⟩
        cases eli : formEval l (X i) with
        | false =>
          cases elj : formEval l (X j) with
          | false => exact liftL eli elj
          | true =>
            have erj : formEval r (X j) = false := by
              simpa [formEval, elj] using hj
            cases eri : formEval r (X i) with
            | false => exact liftR eri erj
            | true =>
              refine ⟨gCut X l r, by simp [gCuts], Or.inr ?_⟩
              simp [gCut, eli, elj, eri, erj]
        | true =>
          have eri : formEval r (X i) = false := by
            simpa [formEval, eli] using hi
          cases erj : formEval r (X j) with
          | false => exact liftR eri erj
          | true =>
            have elj : formEval l (X j) = false := by
              simpa [formEval, erj] using hj
            refine ⟨gCut X l r, by simp [gCuts], Or.inl ?_⟩
            simp [gCut, eli, elj, eri, erj]
theorem pack {d : Nat} (I : Finset (Fin d)) (L : List (Fin d → Option Bool))
    (denom : Nat) (weights : Fin d → Nat)
    (bound : ∀ i ∈ I, 2 ^ width L i * weights i ≤ denom)
    (sep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → FormulaSeparates L i j) : I.sum weights ≤ denom := by
  classical
  let s (i : Fin d) : Finset (Fin L.length) := Finset.univ.filter fun k => ((L.get k) i).isSome
  let b (i : Fin d) (k : Fin L.length) := ((L.get k) i).getD false
  have hcard (i) : (s i).card = width L i := by
    simpa [s,width,List.ofFn_get] using (List.countP_ofFn (List.get L) (fun c => (c i).isSome)).symm
  have disj : (I : Set (Fin d)).PairwiseDisjoint (fun i => cCube (s i) (b i)) := by
    intro i hi j hj hn
    apply Finset.disjoint_left.mpr
    intro f hfi hfj
    obtain ⟨c,hc,hs⟩ := sep i hi j hj hn
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hc
    have ei := cCubeMember (s i) (b i) f |>.mp hfi k
    have ej := cCubeMember (s j) (b j) f |>.mp hfj k
    rcases hs with ⟨hi,hj⟩ | ⟨hi,hj⟩ <;> simp [s,b,hk,hi,hj] at ei ej <;> simp_all
  let vol := 2 ^ Fintype.card (Fin L.length)
  have tot : I.sum (fun i => (cCube (s i) (b i)).card) ≤ vol := by
    rw [← Finset.card_biUnion disj]
    simpa [vol] using Finset.card_le_univ (I.biUnion (fun i => cCube (s i) (b i)))
  have each (i) (hi : i ∈ I) : vol * weights i ≤ (cCube (s i) (b i)).card * denom := by
    change 2 ^ Fintype.card (Fin L.length) * weights i ≤ _
    rw [← cCubeVolume (s i) (b i), Nat.mul_assoc,hcard]
    exact Nat.mul_le_mul_left _ (bound i hi)
  have ht := Finset.sum_le_sum each
  rw [← Finset.mul_sum, ← Finset.sum_mul] at ht
  have hh := ht.trans (Nat.mul_le_mul_right denom tot)
  have hv : 0 < vol := Nat.pow_pos (by decide)
  exact Nat.le_of_mul_le_mul_left hh hv
theorem monotone_eval {n} (t : Formula n) {x y : Fin n → Bool}
    (hle : ∀ i, x i = true → y i = true) (hx : formEval t x = true) :
    formEval t y = true := by
  induction t with
  | nil => cases hx
  | node a l r hl hr =>
    cases a with
    | inl i => exact hle _ hx
    | inr op =>
      cases op
      · simp only [formEval, Bool.or_eq_true] at hx ⊢
        exact hx.elim (fun h => Or.inl (hl h)) (fun h => Or.inr (hr h))
      · simp only [formEval, Bool.and_eq_true] at hx ⊢
        exact ⟨hl hx.1, hr hx.2⟩
end ThresholdSixBound.OneShare

namespace ThresholdSixBound.Leaf5459
theorem map_perm_cons {β γ : Type} (f : β → γ) {l : List β} {a : γ} {r : List γ}
    (h : (l.map f).Perm (a :: r)) :
    ∃ x l', l.Perm (x :: l') ∧ f x = a ∧ (l'.map f).Perm r := by
  have ha : a ∈ l.map f := h.mem_iff.2 (by simp)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  refine ⟨x, l₁ ++ l₂, List.perm_middle, rfl, ?_⟩
  have h1 := (List.perm_middle (a := x) (l₁ := l₁) (l₂ := l₂)).map f
  exact (h1.symm.trans h).cons_inv
end ThresholdSixBound.Leaf5459
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
def delta (b x : Bool) : Bool := if b then false else x
def joinO {n} (op : Bool) : Option (Formula n) → Option (Formula n) → Option (Formula n)
  | some a,some b => some (.node (.inr op) a b)
  | some a,none => if op then some a else none
  | none,some b => if op then some b else none
  | none,none => none
def erase {n} (b : Fin n → Bool) : Formula n → Option (Formula n)
  | .nil => some .nil
  | .node (.inl i) _ _ => if b i then none else some (.node (.inl i) .nil .nil)
  | .node (.inr op) l r => joinO op (erase b l) (erase b r)
def oval {n} (t : Option (Formula n)) (x : Fin n → Bool) := t.elim true (fun f => formEval f x)
def charged {n} (x : Fin n → Bool) (t : Option (Formula n)) := t.elim 0 (wOcc x)
def bot {n : ℕ} : Fin n → Bool := fun _ => false
def supB {n} (x y : Fin n → Bool) := fun k => x k || y k
def Below {n} (x y : Fin n → Bool) := ∀ i, x i = true → y i = true
theorem erase_eval {n} (b x : Fin n → Bool) (h : Below b x) (t : Formula n) :
    oval (erase b t) x = formEval t x := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl i =>
      cases e : b i <;> simp_all [erase,oval,formEval,Below]
    | inr op =>
      cases op <;> cases a : erase b l <;> cases c : erase b r <;>
        simp_all [erase,joinO,oval,formEval]
theorem erase_charge {n} (b x : Fin n → Bool) (t : Formula n) :
    charged x (erase b t) ≤ wOcc (fun i => delta (b i) (x i)) t := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl i => cases e : b i <;> simp [erase,charged,wOcc,e,delta]
    | inr op =>
      cases op <;> cases a : erase b l <;> cases c : erase b r <;>
        simp_all [erase,joinO,charged,wOcc] <;> omega
def rcuts {n d} (b : Fin n → Bool) (X : Fin d → Fin n → Bool) (t : Formula n) :=
  (erase b t).elim [] (gCuts X)
theorem rcharge {n d} (b : Fin n → Bool) (X : Fin d → Fin n → Bool) (t : Formula n)
    (i : Fin d) (h : Below b (X i)) :
    width (rcuts b X t) i + (delta (formEval t b) (formEval t (X i))).toNat ≤
      wOcc (fun j => delta (b j) (X i j)) t := by
  have b0 : Below b b := fun _ h => h
  have A := erase_eval b b b0 t
  have B := erase_eval b (X i) h t
  have K := erase_charge b (X i) t
  cases e : erase b t with
  | none => simp [e,oval] at A; simp [rcuts,e,delta,← A,width]
  | some q =>
    simp only [e,oval,Option.elim_some] at A B
    simp only [e,charged,Option.elim_some] at K
    have W := weight_bound X q i
    simp only [rcuts,e,Option.elim_some]
    have D : (delta (formEval t b) (formEval t (X i))).toNat ≤ (formEval t (X i)).toNat := by
      cases formEval t b <;> cases formEval t (X i) <;> decide
    rw [B] at W
    omega
theorem rsep {n d} (b : Fin n → Bool) (X : Fin d → Fin n → Bool) (t : Formula n)
    (i j : Fin d) (bi : Below b (X i)) (bj : Below b (X j))
    (hp : formEval t (supB (X i) (X j)) = true)
    (hi : formEval t (X i) = false) (hj : formEval t (X j) = false) :
    FormulaSeparates (rcuts b X t) i j := by
  have b2 : Below b (supB (X i) (X j)) := fun k h => by simp [supB,bi k h]
  have p := (erase_eval _ _ b2 t).trans hp
  have h := (erase_eval _ _ bi t).trans hi
  have k := (erase_eval _ _ bj t).trans hj
  cases e : erase b t with
  | none => simp [e,oval] at h
  | some q =>
    simp only [e,oval,Option.elim_some] at p h k
    exact (show FormulaSeparates (rcuts b X t) i j from by
      simpa [rcuts,e] using (generalized_separator X q i j p h k))
theorem wVar {n} (t : Formula n) (i : Fin n) :
    wOcc (singleInput i) t = formOcc t i := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl j => by_cases h : j=i <;> simp [singleInput,wOcc,formOcc,h]
    | inr op => simp [wOcc,formOcc,hl,hr]
theorem wLast {n} (t : Formula (n+1)) (x : Fin n → Bool) (v : Bool) :
    wOcc (Fin.snoc x v) t =
      wOcc (Fin.snoc x false) t + v.toNat * formOcc t (Fin.last n) := by
  induction t with
  | nil => simp [wOcc,formOcc]
  | node a l r hl hr =>
    cases a with
    | inl j => induction j using Fin.lastCases <;> simp [wOcc,formOcc,Fin.snoc,Fin.lastCases_last,Fin.lastCases_castSucc]
    | inr op => simp only [wOcc,formOcc,hl,hr,Nat.mul_add]; omega
theorem ws1 (t : Formula 8) (i : Fin 7) (b : Bool) :
    wOcc (Fin.snoc (singleInput i) b) t =
      formOcc t i.castSucc + b.toNat * formOcc t (Fin.last 7) := by
  rw [wLast]
  congr 1
  rw [← wVar]
  have h : ∀ i : Fin 7, (Fin.snoc (singleInput i) false : Fin 8 → Bool) = singleInput i.castSucc := by decide
  rw [h]
theorem ws2 (t : Formula 9) (i : Fin 7) (b c : Bool) :
    wOcc (Fin.snoc (Fin.snoc (singleInput i) b) c) t =
      formOcc t i.castSucc.castSucc + b.toNat * formOcc t (Fin.last 7).castSucc +
      c.toNat * formOcc t (Fin.last 8) := by
  induction t with
  | nil => simp [wOcc,formOcc]
  | node a l r hl hr =>
    cases a with
    | inr op => simp only [wOcc,formOcc,hl,hr,Nat.mul_add]; omega
    | inl j =>
      generalize_proofs
      exact (show ∀ (i : Fin 7) (j : Fin 9) (b c : Bool),
        ((Fin.snoc (Fin.snoc (singleInput i) b) c : Fin 9 → Bool) j).toNat =
        (if j=i.castSucc.castSucc then 1 else 0) +
        b.toNat*(if j=(Fin.last 7).castSucc then 1 else 0) +
        c.toNat*(if j=Fin.last 8 then 1 else 0) by decide +kernel) i j b c
end ThresholdSeven
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
abbrev V := Fin 7
abbrev X := V → Bool
def inG (H : Formula 7) (x : X) : Fin 8 → Bool := Fin.snoc x (formEval H x)
def inQ (H : Formula 7) (G : Formula 8) (x : X) : Fin 9 → Bool :=
  Fin.snoc (inG H x) (formEval G (inG H x))
def B (H : Formula 7) (i : V) := formEval H (singleInput i)
def C (H : Formula 7) (G : Formula 8) (i : V) := formEval G (inG H (singleInput i))
def baseG (a : Bool) : Fin 8 → Bool := Fin.snoc bot a
def baseC (a b : Bool) (G : Formula 8) := b || formEval G (baseG a)
def baseQ (a b : Bool) (G : Formula 8) : Fin 9 → Bool := Fin.snoc (baseG a) (baseC a b G)
def active (a b : Bool) (H : Formula 7) (G : Formula 8) (i : V) : Prop :=
  (a = true → B H i = true) ∧ (b = true → C H G i = true)
theorem belowBot {n} (x : Fin n → Bool) : Below bot x := by simp [Below,bot]
theorem belowLast {n} {x y : Fin n → Bool} {p q : Bool}
    (h : Below x y) (k : p = true → q = true) : Below (Fin.snoc x p) (Fin.snoc y q) := by
  intro i
  induction i using Fin.lastCases <;> simp_all [Fin.snoc_last, Fin.snoc_castSucc,Below]
theorem belowX {n} (i j : Fin n) : Below (singleInput i) (pairInput i j) := by
  intro k hk
  simp [singleInput] at hk
  simp [pairInput,hk]
theorem belowY {n} (i j : Fin n) : Below (singleInput j) (pairInput i j) := by
  intro k hk
  simp [singleInput] at hk
  simp [pairInput,hk]
theorem sup_in {n} (i j : Fin n) : supB (singleInput i) (singleInput j) = pairInput i j := by
  funext k
  by_cases h : k=i <;> simp [supB,singleInput,pairInput,h]
theorem sup_snoc {n} (x y : Fin n → Bool) (u v : Bool) :
    supB (Fin.snoc x u) (Fin.snoc y v) = Fin.snoc (supB x y) (u || v) := by
  funext i
  induction i using Fin.lastCases <;> simp [supB]
theorem delta_snoc {n} (x y : Fin n → Bool) (u v : Bool) :
    (fun i => delta ((Fin.snoc x u : Fin (n+1) → Bool) i) ((Fin.snoc y v : Fin (n+1) → Bool) i)) =
    Fin.snoc (fun i => delta (x i) (y i)) (delta u v) := by
  funext i
  induction i using Fin.lastCases <;> simp
theorem val0 {n} (t : Formula n) : formEval t bot = false := by
  induction t with
  | nil => rfl
  | node a l r hl hr => cases a with
    | inl i => rfl
    | inr op => cases op <;> simp [formEval,hl,hr]
theorem bg_ok {a b H G i} (hi : active a b H G i) : Below (baseG a) (inG H (singleInput i)) :=
  belowLast (belowBot _) hi.1
theorem bc_ok {a b H G i} (hi : active a b H G i) : baseC a b G = true → C H G i = true := by
  intro h
  have dis : b = true ∨ formEval G (baseG a) = true := by simpa [baseC] using h
  rcases dis with h | h
  · exact hi.2 h
  · exact monotone_eval G (bg_ok hi) h
theorem bq_ok {a b H G i} (hi : active a b H G i) : Below (baseQ a b G) (inQ H G (singleInput i)) :=
  belowLast (bg_ok hi) (bc_ok hi)
def ch (a : Bool) (H : Formula 7) : List (V → Option Bool) :=
  if a then [] else rcuts bot singleInput H
def cg (a b : Bool) (H : Formula 7) (G : Formula 8) : List (V → Option Bool) :=
  if b then [] else rcuts (baseG a) (fun i => inG H (singleInput i)) G
def cq (a b : Bool) (H : Formula 7) (G : Formula 8) (Q : Formula 9) : List (V → Option Bool) :=
  rcuts (baseQ a b G) (fun i => inQ H G (singleInput i)) Q
def layers (a b : Bool) (H : Formula 7) (G : Formula 8) (Q : Formula 9) :=
  ch a H ++ cg a b H G ++ cq a b H G Q
theorem gap : ∀ p q r : Bool, (p = true → r = true) → (q = true → r = true) →
    r ≠ (p || q) → p = false ∧ q = false ∧ r = true := by decide
theorem rootSep (a b : Bool) (H : Formula 7) (G : Formula 8) (Q : Formula 9) (i j : V)
    (iy : active a b H G i) (jy : active a b H G j)
    (loi : formEval Q (inQ H G (singleInput i)) = false)
    (loj : formEval Q (inQ H G (singleInput j)) = false)
    (hi : formEval Q (inQ H G (pairInput i j)) = true) :
    FormulaSeparates (layers a b H G Q) i j := by
  have h1 := monotone_eval H (belowX i j)
  have h2 := monotone_eval H (belowY i j)
  by_cases eH : formEval H (pairInput i j) = (B H i || B H j)
  · have se : supB (inG H (singleInput i)) (inG H (singleInput j)) = inG H (pairInput i j) := by
      rw [inG,inG,inG,sup_snoc,sup_in,eH]; rfl
    have g1 := monotone_eval G (belowLast (belowX i j) h1)
    have g2 := monotone_eval G (belowLast (belowY i j) h2)
    by_cases eG : formEval G (inG H (pairInput i j)) = (C H G i || C H G j)
    · have se' : supB (inQ H G (singleInput i)) (inQ H G (singleInput j)) = inQ H G (pairInput i j) := by
        rw [inQ,inQ,inQ,sup_snoc,se,eG]; rfl
      obtain ⟨c,hc,ep⟩ := rsep (baseQ a b G) (fun k => inQ H G (singleInput k)) Q i j
        (bq_ok iy) (bq_ok jy) (se' ▸ hi) loi loj
      exact ⟨c,List.mem_append_right _ hc,ep⟩
    · change (C H G i = true → formEval G (inG H (pairInput i j)) = true) at g1
      change (C H G j = true → formEval G (inG H (pairInput i j)) = true) at g2
      have vals : C H G i = false ∧ C H G j = false ∧ formEval G (inG H (pairInput i j)) = true := by
        exact gap _ _ _ g1 g2 eG
      have bb : b=false := by cases b <;> simp_all [active]
      obtain ⟨c,hc,ep⟩ := rsep (baseG a) (fun k => inG H (singleInput k)) G i j
        (bg_ok iy) (bg_ok jy) (se ▸ vals.2.2) vals.1 vals.2.1
      have mem : c ∈ cg a b H G := by simpa [cg,bb] using hc
      exact ⟨c,List.mem_append_left _ (List.mem_append_right _ mem),ep⟩
  · change (B H i = true → formEval H (pairInput i j) = true) at h1
    change (B H j = true → formEval H (pairInput i j) = true) at h2
    have vals : B H i = false ∧ B H j = false ∧ formEval H (pairInput i j) = true := by
      exact gap _ _ _ h1 h2 eH
    have aa : a=false := by cases a <;> simp_all [active]
    obtain ⟨c,hc,ep⟩ := rsep bot singleInput H i j (belowBot _) (belowBot _)
      (sup_in i j ▸ vals.2.2) vals.1 vals.2.1
    have mem : c ∈ ch a H := by simpa [ch,aa] using hc
    exact ⟨c,List.mem_append_left _ (List.mem_append_left _ mem),ep⟩
end ThresholdSeven
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
abbrev hraw (H : Formula 7) (i : V) := formOcc H i
abbrev graw (G : Formula 8) (i : V) := formOcc G i.castSucc
abbrev qraw (Q : Formula 9) (i : V) := formOcc Q i.castSucc.castSucc
abbrev gh (G : Formula 8) := formOcc G (Fin.last 7)
abbrev qh (Q : Formula 9) := formOcc Q (Fin.last 7).castSucc
abbrev qg (Q : Formula 9) := formOcc Q (Fin.last 8)
theorem chargeH (H : Formula 7) (i : V) :
    width (ch false H) i + (B H i).toNat ≤ hraw H i := by
  have h := rcharge bot singleInput H i (belowBot _)
  rw [val0] at h
  change width (rcuts bot singleInput H) i + (formEval H (singleInput i)).toNat ≤
    wOcc (singleInput i) H at h
  simpa [ch,B,wVar] using h
theorem chargeG {a b : Bool} {H : Formula 7} {G : Formula 8} {i : V} (iy : active a b H G i) :
    width (cg a false H G) i + (delta (formEval G (baseG a)) (C H G i)).toNat ≤
      graw G i + (delta a (B H i)).toNat * gh G := by
  have h := rcharge (baseG a) (fun k => inG H (singleInput k)) G i (bg_ok iy)
  have e : (fun j => delta (baseG a j) (inG H (singleInput i) j)) =
      Fin.snoc (singleInput i) (delta a (B H i)) := by
    exact delta_snoc bot (singleInput i) a (B H i)
  rw [e,ws1] at h
  exact h
theorem chargeQ {a b : Bool} {H : Formula 7} {G : Formula 8} (Q : Formula 9) {i : V}
    (iy : active a b H G i) :
    width (cq a b H G Q) i ≤ qraw Q i + (delta a (B H i)).toNat * qh Q +
      (delta (baseC a b G) (C H G i)).toNat * qg Q := by
  have h := rcharge (baseQ a b G) (fun k => inQ H G (singleInput k)) Q i (bq_ok iy)
  have e : (fun j => delta (baseQ a b G j) (inQ H G (singleInput i) j)) =
      Fin.snoc (Fin.snoc (singleInput i) (delta a (B H i))) (delta (baseC a b G) (C H G i)) := by
    unfold baseQ inQ
    rw [delta_snoc]
    have eg : (fun j => delta (baseG a j) (inG H (singleInput i) j)) =
        Fin.snoc (singleInput i) (delta a (B H i)) := delta_snoc bot (singleInput i) a (B H i)
    rw [eg];rfl
  rw [e,ws2] at h
  exact (Nat.le_add_right ..).trans h
theorem gzero (G : Formula 8) : formEval G (baseG false) = false := by
  have e : baseG false = bot := by decide
  rw [e,val0]
theorem ch_true (H : Formula 7) (i : V) : width (ch true H) i = 0 := rfl
theorem cg_true (a : Bool) (H : Formula 7) (G : Formula 8) (i : V) : width (cg a true H G) i = 0 := rfl
theorem widthLimits (H : Formula 7) (G : Formula 8) (Q : Formula 9)
    (cost : ∀ i, hraw H i + graw G i + qraw Q i ≤ 2)
    (costH : gh G + qh Q ≤ 2) (costG : qg Q ≤ 2) :
    ∀ a b i, active a b H G i → width (layers a b H G Q) i ≤
      (if a || b then 1 else 2) + (if !a then (B H i).toNat else 0) +
        (if !b then (C H G i).toNat else 0) := by
  intro a b i iy
  have raw := cost i
  have h := chargeH H i
  have g := chargeG iy
  have q := chargeQ Q iy
  have yn : active false false H G i := by simp [active]
  have g0 := chargeG yn
  rw [gzero] at g0
  have s1 := iy.1
  have s2 := iy.2
  change _ + _ ≤ _ at h
  simp only [layers,width,List.countP_append]
  change width (ch a H) i + width (cg a b H G) i + width (cq a b H G Q) i ≤ _
  cases a <;> cases b <;> cases eH : B H i <;> cases eG : C H G i <;>
    cases gbase : formEval G (baseG true) <;>
    simp only [eH,eG,baseC,gzero,gbase,ch_true,cg_true,Bool.false_or,Bool.or_true,Bool.true_or,delta,ite_true,ite_false,
      Bool.toNat_false,Bool.toNat_true,Nat.zero_mul,Nat.one_mul,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,Nat.add_zero,Nat.zero_add] at h g q g0 s1 s2 ⊢
  all_goals first | exact False.elim (s1 trivial) | exact False.elim (s2 trivial) | omega
end ThresholdSeven
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
def mass (a b p q : Bool) : Nat :=
  match a,b with
  | false,false => (if p then 1 else 2) * (if q then 1 else 2)
  | true,false => if p then (if q then 1 else 2) else 0
  | false,true => if q then (if p then 1 else 2) else 0
  | true,true => if p && q then 1 else 0
def room (a b : Bool) : Nat := match a,b with
  | false,false => 16
  | true,true => 2
  | _,_ => 4
theorem fitted : ∀ a b p q : Bool, (a = true → p = true) → (b = true → q = true) →
    2^((if a || b then 1 else 2) + (if !a then p.toNat else 0) +
      (if !b then q.toNat else 0)) * mass a b p q ≤ room a b := by decide
theorem total_mass : ∀ p q : Bool,
    mass false false p q + mass false true p q + mass true false p q + mass true true p q = 4 := by decide
theorem inactive : ∀ a b p q : Bool, ¬ ((a=true → p=true) ∧ (b=true → q=true)) →
    mass a b p q = 0 := by decide
theorem twoShare (H : Formula 7) (G : Formula 8) (Q : Formula 9)
    (cost : ∀ i, hraw H i + graw G i + qraw Q i ≤ 2)
    (costH : gh G + qh Q ≤ 2) (costG : qg Q ≤ 2)
    (lo : ∀ i : V, formEval Q (inQ H G (singleInput i)) = false)
    (hi : ∀ i j : V, i≠j → formEval Q (inQ H G (pairInput i j)) = true) : False := by
  classical
  let f (a b : Bool) (i : V) := mass a b (B H i) (C H G i)
  have hb (a b : Bool) : (Finset.univ.sum (f a b)) ≤ room a b := by
    let I := Finset.univ.filter (active a b H G)
    have S : Finset.univ.sum (f a b) = I.sum (f a b) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro x _ hx
      have ex : ¬ active a b H G x := by simpa [I] using hx
      exact inactive a b (B H x) (C H G x) ex
    rw [S]
    apply pack I (layers a b H G Q) (room a b)
    · intro i h
      have h' := (Finset.mem_filter.mp h).2
      have w := widthLimits H G Q cost costH costG a b i h'
      exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0<2) w)).trans
        (fitted a b _ _ h'.1 h'.2)
    · intro i h j h' hn
      exact rootSep a b H G Q i j (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp h').2
        (lo i) (lo j) (hi i j hn)
  have add : Finset.univ.sum (f false false) + Finset.univ.sum (f false true) +
      Finset.univ.sum (f true false) + Finset.univ.sum (f true true) = 28 := by
    simp only [← Finset.sum_add_distrib]
    calc
      _ = Finset.univ.sum (fun _ : V => (4:Nat)) := Finset.sum_congr rfl (fun i _ => total_mass _ _)
      _ = 28 := by decide
  have h00 := hb false false
  have h01 := hb false true
  have h10 := hb true false
  have h11 := hb true true
  simp only [room] at h00 h01 h10 h11
  omega
end ThresholdSeven
namespace ThresholdSixBound.SevenExtract
open Leaf5459
abbrev Fn := Seven.BF
abbrev GateRun (ys : List Fn) (s : ℕ) (ws : List Fn) :=
  TR Seven.gF (fun k _ _ => MonoA k) ys s ws
def ev {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (t : Formula n) : Fn :=
  fun x => formEval t (q x)
def occ {n : ℕ} (ts : List (Formula n)) (i : Fin n) : ℕ := (ts.map (fun t => formOcc t i)).sum
def disjoinForest {n : ℕ} : List (Formula n) → Formula n
  | [] => .nil
  | t :: ts => .node (.inr false) t (disjoinForest ts)
def leaf {n : ℕ} (i : Fin n) : Formula n := .node (.inl i) .nil .nil
def graft {n : ℕ} (k : Fin 4) (a b : Formula n) : Formula n :=
  .node (.inr (decide (k = 0))) a b
theorem graft_ev {n} (q : (Fin 7 → Bool) → Fin n → Bool) (k : Fin 4) (hk : MonoA k)
    (a b : Formula n) : ev q (graft k a b) = Seven.gF k (ev q a) (ev q b) := by
  rcases mono_cases k hk with rfl | rfl <;> rfl
theorem occ_graft {n} (k : Fin 4) (a b : Formula n) (i : Fin n) :
    formOcc (graft k a b) i = formOcc a i + formOcc b i := rfl
theorem permOcc {n} {a b : List (Formula n)} (h : a.Perm b) (i : Fin n) :
    occ a i = occ b i := (h.map _).sum_eq
theorem consOcc {n} (a : Formula n) (b : List (Formula n)) (i : Fin n) :
    occ (a::b) i = formOcc a i + occ b i := rfl
theorem combineOcc {n} {ts zs us : List (Formula n)} {a b : Formula n}
    (h1 : ts.Perm (a::zs)) (h2 : zs.Perm (b::us)) (k : Fin 4) (i : Fin n) :
    occ ts i = occ (graft k a b :: us) i := by
  rw [permOcc h1,consOcc,permOcc h2,consOcc,consOcc,occ_graft]
  omega
theorem overEval {n} (ts : List (Formula n)) (q : (Fin 7 → Bool) → Fin n → Bool)
    (x : Fin 7 → Bool) : formEval (disjoinForest ts) (q x) = (ts.map (ev q)).any (fun f => f x) := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp [disjoinForest,formEval,List.any_cons,ev,ih]
theorem overOcc {n} (ts : List (Formula n)) (i : Fin n) : formOcc (disjoinForest ts) i = occ ts i := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp [disjoinForest,formOcc,consOcc,ih]
theorem permAny {xs ys : List Fn} (h : xs.Perm ys) (x : Fin 7 → Bool) :
    xs.any (fun f => f x) = ys.any (fun f => f x) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  exact ⟨fun ⟨a,ha,hv⟩ => ⟨a,h.mem_iff.mp ha,hv⟩,
         fun ⟨a,ha,hv⟩ => ⟨a,h.mem_iff.mpr ha,hv⟩⟩
theorem plain {n} (q : (Fin 7 → Bool) → Fin n → Bool) {ys ws : List Fn} {s : ℕ}
    (h : GateRun ys s ws) :
    ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws → ws.length = s + ys.length →
      ∃ t : Formula n, (∀ x, ev q t x = ys.any (fun f => f x)) ∧ ∀ i, formOcc t i = occ ts i := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws →
    ws.length = s + ys.length → ∃ t : Formula n,
    (∀ x, ev q t x = ys.any (fun f => f x)) ∧ ∀ i, formOcc t i = occ ts i) h ?_ ?_ ?_
  · intro ts hp _
    exact ⟨disjoinForest ts,fun x => (overEval ts q x).trans (permAny hp x),overOcc ts⟩
  · intro s xs zs hp _ ih ts hm hl
    exact ih ts (hm.trans hp.symm) (by rw [hp.length_eq]; exact hl)
  · intro s a b r k u hk hr ih ts hm hl
    have hn := TR.len hr
    simp only [List.length_append,List.length_replicate,List.length_cons] at hn hl
    obtain rfl : u = 0 := by omega
    obtain ⟨ta,t₁,hp1,rfl,h1⟩ := map_perm_cons (ev q) hm
    obtain ⟨tb,t₂,hp2,rfl,h2⟩ := map_perm_cons (ev q) h1
    obtain ⟨t,ht,ho⟩ := ih (graft k ta tb :: t₂)
      (by rw [List.map_cons,graft_ev q k hk]; exact h2.cons _)
      (by simp only [List.length_append,List.length_replicate]; omega)
    exact ⟨t,ht,fun i => (ho i).trans (combineOcc hp1 hp2 k i).symm⟩
def lift {n : ℕ} :  Formula n → Formula (n+1)
  | .nil => .nil
  | .node (.inl i) _ _ => leaf i.castSucc
  | .node (.inr b) l r => .node (.inr b) (lift l) (lift r)
theorem liftEval {n : ℕ} (t : Formula n) (x : Fin n → Bool) (v : Bool) :
    formEval (lift t) (Fin.snoc x v) = formEval t x := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl i =>
      change (Fin.snoc x v : Fin (n+1) → Bool) i.castSucc = x i
      rw [Fin.snoc_castSucc]
    | inr b => cases b <;> simp [lift,formEval,hl,hr]
theorem liftOcc {n : ℕ} (t : Formula n) (i : Fin n) :
    formOcc (lift t) i.castSucc = formOcc t i := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl k => simp [lift,leaf,formOcc]
    | inr b => simp [lift,formOcc,hl,hr]
theorem liftLast {n : ℕ} (t : Formula n) : formOcc (lift t) (Fin.last n) = 0 := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl k => simp only [lift,leaf,formOcc,if_neg (Fin.castSucc_ne_last k)]
    | inr b => simp only [lift,formOcc,hl,hr,Nat.zero_add]
theorem occLift {n : ℕ} (ts : List (Formula n)) (i : Fin n) : occ (ts.map lift) i.castSucc = occ ts i := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [List.map_cons,consOcc,liftOcc,ih]
theorem occLiftLast {n : ℕ} (ts : List (Formula n)) : occ (ts.map lift) (Fin.last n) = 0 := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [List.map_cons,consOcc,liftLast,ih,Nat.zero_add]
def extended {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (h : Formula n)
    (x : Fin 7 → Bool) : Fin (n+1) → Bool := Fin.snoc (q x) (ev q h x)
theorem mapLift {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (ts : List (Formula n)) (h : Formula n) :
    (ts.map lift).map (ev (extended q h)) = ts.map (ev q) := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [List.map_cons,ih]; rw [show ev (extended q h) (lift a) = ev q a from funext (fun x => liftEval a (q x) _)]
def Shared {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (ys : List Fn) (ts : List (Formula n)) : Prop :=
  ∃ H : Formula n, ∃ P : Formula (n+1), (∀ x, formEval P (extended q H x) = ys.any (fun f => f x)) ∧
    (∀ i : Fin n, formOcc P i.castSucc + formOcc H i = occ ts i) ∧ formOcc P (Fin.last n) ≤ 2
theorem oneShare {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) {ys ws : List Fn} {s : ℕ} (h : GateRun ys s ws) :
    ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws → s + ys.length ≤ ws.length + 1 → Shared q ys ts := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws →
    s + ys.length ≤ ws.length + 1 → Shared q ys ts) h ?_ ?_ ?_
  · intro ts hp _
    refine ⟨.nil,lift (disjoinForest ts),?_,?_,by rw [liftLast]; decide⟩
    · intro x
      exact (liftEval (disjoinForest ts) (q x) _).trans ((overEval ts q x).trans (permAny hp x))
    · intro i
      simp [liftOcc,formOcc,overOcc]
  · intro s xs zs hp _ ih ts hm hl
    exact ih ts (hm.trans hp.symm) (by rw [hp.length_eq]; exact hl)
  · intro s a b r k u hk hr ih ts hm hl
    have hn := TR.len hr
    simp only [List.length_append,List.length_replicate,List.length_cons] at hn hl
    obtain ⟨ta,t₁,hp1,rfl,h1⟩ := map_perm_cons (ev q) hm
    obtain ⟨tb,t₂,hp2,rfl,h2⟩ := map_perm_cons (ev q) h1
    let H := graft k ta tb
    have hH : ev q H = Seven.gF k (ev q ta) (ev q tb) := graft_ev q k hk ta tb
    have hu : u = 0 ∨ u = 1 := by omega
    rcases hu with rfl | rfl
    · obtain ⟨K,P,he,ho,hf⟩ := ih (H :: t₂)
        (by rw [List.map_cons,hH]; exact h2.cons _)
        (by simp only [List.length_append,List.length_replicate]; omega)
      exact ⟨K,P,he,fun i => (ho i).trans (combineOcc hp1 hp2 k i).symm,hf⟩
    · let leafZ := leaf (Fin.last n)
      let ts' := leafZ :: leafZ :: t₂.map lift
      have hez : ev (extended q H) leafZ = ev q H := by
        funext x
        change (Fin.snoc (q x) (ev q H x) : Fin (n+1) → Bool) (Fin.last n) = _
        rw [Fin.snoc_last]
      have hmap : (ts'.map (ev (extended q H))).Perm
          (List.replicate (1+1) (Seven.gF k (ev q ta) (ev q tb)) ++ r) := by
        change (ev (extended q H) leafZ :: ev (extended q H) leafZ :: (t₂.map lift).map (ev (extended q H))).Perm _
        rw [hez,hH,mapLift]
        exact (h2.cons _).cons _
      obtain ⟨P,he,ho⟩ := plain (extended q H) hr ts' hmap (by
        simp only [List.length_append,List.length_replicate]; omega)
      refine ⟨H,P,he,?_,?_⟩
      · intro i
        rw [ho,combineOcc hp1 hp2 k i]
        simp only [ts',leafZ,leaf,consOcc,formOcc,H,if_neg (Ne.symm (Fin.castSucc_ne_last i)),Nat.zero_add]
        rw [occLift t₂ i]
        omega
      · rw [ho]; simp only [ts',leafZ,leaf,consOcc,formOcc,ite_true]; rw [occLiftLast t₂]
end ThresholdSixBound.SevenExtract
namespace ThresholdSixBound.SevenExtract
open Leaf5459
open ThresholdSeven
def Shared2 (ys : List Fn) (ts : List (Formula 7)) := ∃ (H : Formula 7) (G : Formula 8) (Q : Formula 9),
  (∀ x, formEval Q (inQ H G x) = ys.any (fun f => f x)) ∧
  (∀ i : Fin 7, hraw H i + graw G i + qraw Q i = occ ts i) ∧ gh G + qh Q ≤ 2 ∧ ThresholdSeven.qg Q ≤ 2
theorem extractForest {ys ws : List Fn} {s : ℕ} (h : GateRun ys s ws) :
    ∀ ts : List (Formula 7), (ts.map formEval).Perm ws → s + ys.length ≤ ws.length + 2 → Shared2 ys ts := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula 7), (ts.map formEval).Perm ws →
    s + ys.length ≤ ws.length + 2 → Shared2 ys ts) h ?_ ?_ ?_
  · intro ts hp _
    refine ⟨.nil,.nil,lift (lift (disjoinForest ts)),?_,?_,?_,?_⟩
    · intro x
      exact (liftEval _ (inG .nil x) _).trans ((liftEval _ x _).trans ((overEval ts id x).trans (permAny hp x)))
    · intro i
      simp [hraw,graw,qraw,liftOcc,formOcc,overOcc]
    · simp only [gh,qh,formOcc,liftOcc,liftLast]; decide
    · simp only [ThresholdSeven.qg,liftLast]; decide
  · intro s xs zs hp _ ih ts hm hl
    exact ih ts (hm.trans hp.symm) (by rw [hp.length_eq]; exact hl)
  · intro s a b r k u hk hr ih ts hm hl
    have hn := TR.len hr
    simp only [List.length_append,List.length_replicate,List.length_cons] at hn hl
    obtain ⟨ta,t₁,hp1,rfl,h1⟩ := map_perm_cons formEval hm
    obtain ⟨tb,t₂,hp2,rfl,h2⟩ := map_perm_cons formEval h1
    let H := graft k ta tb
    have hH : formEval H = Seven.gF k (formEval ta) (formEval tb) := graft_ev id k hk ta tb
    have hu : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hu with rfl | rfl | rfl
    · obtain ⟨H',G,Q,he,ho,hb,hc⟩ := ih (H :: t₂)
        (by rw [List.map_cons,hH]; exact h2.cons _)
        (by simp only [List.length_append,List.length_replicate]; omega)
      exact ⟨H',G,Q,he,fun i => (ho i).trans (combineOcc hp1 hp2 k i).symm,hb,hc⟩
    · let z := leaf (Fin.last 7)
      let ts' := z :: z :: t₂.map lift
      have ez : ev (extended id H) z = formEval H := by
        funext x
        change (Fin.snoc x (formEval H x) : Fin 8 → Bool) (Fin.last 7) = _
        rw [Fin.snoc_last]
      have hm' : (ts'.map (ev (extended id H))).Perm
          (List.replicate (1+1) (Seven.gF k (formEval ta) (formEval tb)) ++ r) := by
        change (ev (extended id H) z :: ev (extended id H) z :: (t₂.map lift).map (ev (extended id H))).Perm _
        rw [ez,hH,mapLift]
        exact (h2.cons _).cons _
      obtain ⟨G,Q,he,ho,hg⟩ := oneShare (extended id H) hr ts' hm' (by
        simp only [List.length_append,List.length_replicate]; omega)
      refine ⟨H,G,Q,he,?_,?_,hg⟩
      · intro i
        have u := ho i.castSucc
        rw [combineOcc hp1 hp2 k i,consOcc]
        simp only [ts',z,leaf,consOcc,formOcc,if_neg (Ne.symm (Fin.castSucc_ne_last i)),Nat.zero_add,occLift] at u
        change formOcc H i + formOcc G i.castSucc + formOcc Q i.castSucc.castSucc = formOcc H i + occ t₂ i
        omega
      · have u := ho (Fin.last 7)
        simp only [ts',z,leaf,consOcc,formOcc,ite_true,occLiftLast] at u
        change formOcc G (Fin.last 7) + formOcc Q (Fin.last 7).castSucc ≤ 2
        omega
    · let G : Formula 8 := leaf (Fin.last 7)
      let zH : Formula 9 := leaf (Fin.last 7).castSucc
      let zG : Formula 9 := leaf (Fin.last 8)
      let ts' := zG :: zG :: zH :: (t₂.map lift).map lift
      let enc := extended (extended id H) G
      have gval (x : Fin 7 → Bool) : formEval G (extended id H x) = formEval H x := by
        change (Fin.snoc x (formEval H x) : Fin 8 → Bool) (Fin.last 7) = _
        rw [Fin.snoc_last]
      have ezh : ev enc zH = formEval H := by
        funext x
        change (Fin.snoc (extended id H x) (ev (extended id H) G x) : Fin 9 → Bool) (Fin.last 7).castSucc = _
        rw [Fin.snoc_castSucc]
        exact gval x
      have ezg : ev enc zG = formEval H := by
        funext x
        change (Fin.snoc (extended id H x) (ev (extended id H) G x) : Fin 9 → Bool) (Fin.last 8) = _
        rw [Fin.snoc_last]
        exact gval x
      have hm' : (ts'.map (ev enc)).Perm
          (List.replicate (2+1) (Seven.gF k (formEval ta) (formEval tb)) ++ r) := by
        change (ev enc zG :: ev enc zG :: ev enc zH :: ((t₂.map lift).map lift).map (ev enc)).Perm _
        rw [ezh,ezg,hH]
        unfold enc
        rw [mapLift,mapLift]
        exact ((h2.cons _).cons _).cons _
      obtain ⟨Q,he,ho⟩ := plain enc hr ts' hm' (by
        simp only [List.length_append,List.length_replicate]; omega)
      refine ⟨H,G,Q,he,?_,?_,?_⟩
      · intro i
        rw [combineOcc hp1 hp2 k i,consOcc]
        have no1 : (Fin.last 7 : Fin 8) ≠ i.castSucc := Ne.symm (Fin.castSucc_ne_last i)
        have no2 : (Fin.last 8 : Fin 9) ≠ i.castSucc.castSucc := Ne.symm (Fin.castSucc_ne_last i.castSucc)
        have no3 : (Fin.last 7).castSucc ≠ i.castSucc.castSucc := fun h => no1 (Fin.castSucc_inj.mp h)
        simp only [hraw,graw,qraw,ho,ts',zH,zG,G,leaf,consOcc,formOcc,occLift,
          if_neg no1,if_neg no2,if_neg no3,Nat.zero_add,Nat.add_zero,H]
      · have non : (Fin.last 8 : Fin 9) ≠ (Fin.last 7).castSucc := Ne.symm (Fin.castSucc_ne_last _)
        simp only [gh,qh,G,zH,zG,leaf,ts',consOcc,formOcc,ho,occLift,occLiftLast,
          ite_true,if_neg non,Nat.add_zero,Nat.zero_add]; decide
      · have non : (Fin.last 7).castSucc ≠ (Fin.last 8 : Fin 9) := Fin.castSucc_ne_last _
        simp only [ThresholdSeven.qg,zH,zG,leaf,ts',consOcc,formOcc,ho,occLiftLast,
          ite_true,if_neg non,Nat.add_zero,Nat.zero_add]; decide
theorem inputOcc (idx : List (Fin 7)) (i : Fin 7) : occ (idx.map leaf) i = idx.count i := by
  induction idx with
  | nil => rfl
  | cons j js ih => simp [consOcc,leaf,formOcc,List.count_cons,ih]; split_ifs <;> omega
theorem extract {ys : List Fn} {s} {idx : List (Fin 7)} (h : GateRun ys s (idx.map Seven.var))
    (hc : s + ys.length ≤ idx.length + 2) (hi : ∀ i, idx.count i ≤ 2) :
    ∃ (H : Formula 7) (G : Formula 8) (Q : Formula 9),
      (∀ x, formEval Q (inQ H G x) = ys.any (fun f => f x)) ∧
      (∀ i, hraw H i + graw G i + qraw Q i ≤ 2) ∧ gh G + qh Q ≤ 2 ∧ ThresholdSeven.qg Q ≤ 2 := by
  have hm : ((idx.map leaf).map formEval).Perm (idx.map Seven.var) := by
    rw [List.map_map]; exact List.Perm.refl _
  obtain ⟨H,G,Q,he,ho,hg,hq⟩ := extractForest h (idx.map leaf) hm (by simpa using hc)
  exact ⟨H,G,Q,he,fun i => (ho i).le.trans ((inputOcc idx i) ▸ hi i),hg,hq⟩
end ThresholdSixBound.SevenExtract

namespace ThresholdSixBound.Seven
open Leaf5459
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws
def outF (ys : List BF) : BF := fun x => ys.any fun y => y x
def otop (x : Fin 7) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)
theorem top_elim (O : BF) :
    ∀ (m : ℕ) (S : BF → Prop) (F : BF), (∀ w, S w → ∀ p, w p = true → O p = true) → F ≠ O →
      UC gF MonoA m (fun w => w = O ∨ S w) F → UC gF MonoA m S F
  | 0, S, F, _, hF, hu => by
    rcases hu with h | h
    · exact absurd h hF
    · exact h
  | m + 1, S, F, hS, hF, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (top_elim O m S F hS hF hu)
    · have hle : ∀ w, (w = O ∨ S w) → ∀ p, w p = true → O p = true := by
        rintro w (rfl | hw) p hp
        · exact hp
        · exact hS w hw p hp
      have free : (gF k a b = O ∨ S (gF k a b)) → UC gF MonoA (m + 1) S F := by
        intro hg
        refine Or.inl (top_elim O m S F hS hF (UC_monoS gF MonoA m _ _ F ?_ hu))
        rintro w (rfl | hw)
        · exact hg
        · exact hw
      by_cases hao : a = O
      · subst hao
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = b := by
            rw [gF_and]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact hb
        · have : gF 1 a b = a := by
            rw [gF_or]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact Or.inl rfl
      by_cases hbo : b = O
      · subst hbo
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = a := by
            rw [gF_and]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact ha
        · have : gF 1 a b = b := by
            rw [gF_or]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact Or.inl rfl
      have ha' : S a := ha.resolve_left hao
      have hb' : S b := hb.resolve_left hbo
      refine UC_gate k a b hk ha' hb' (top_elim O m _ F ?_ hF (UC_monoS gF MonoA m _ _ F ?_ hu))
      · rintro w (rfl | hw) p hp
        · rcases mono_cases k hk with rfl | rfl
          · rw [gF_and] at hp
            simp only [Bool.and_eq_true] at hp
            exact hS a ha' p hp.1
          · rw [gF_or] at hp
            simp only [Bool.or_eq_true] at hp
            rcases hp with hp | hp
            · exact hS a ha' p hp
            · exact hS b hb' p hp
        · exact hS w hw p hp
      · rintro w (rfl | rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hw)
theorem outF_true (ys : List BF) (p : Fin 7 → Bool) :
    outF ys p = true ↔ ∃ y ∈ ys, y p = true := by
  simp [outF]
theorem outF_congr (ys : List BF) (p p' : Fin 7 → Bool) (h : ∀ y ∈ ys, y p = y p') :
    outF ys p = outF ys p' := by
  rw [Bool.eq_iff_iff, outF_true, outF_true]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [← h y hy]; exact hp⟩
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [h y hy]; exact hp⟩
theorem or_chain : ∀ (ys : List BF) (y : BF), MR [outF (y :: ys)] ys.length (y :: ys)
  | [], y => by
    have : outF [y] = y := funext fun x => by simp [outF]
    rw [this]
    exact TR.done
  | y2 :: rest, y => by
    have h := or_chain rest (gF 1 y y2)
    have e : outF (gF 1 y y2 :: rest) = outF (y :: y2 :: rest) :=
      funext fun x => by simp [outF, gF_or, Bool.or_assoc]
    rw [e] at h
    exact TR.step (r := rest) 1 0 (by simp [MonoA]) h
theorem complete_run (y0 : BF) (yt : List BF) {s : ℕ} {ws : List BF} (h : MR (y0 :: yt) s ws) :
    MR [outF (y0 :: yt)] (s + yt.length) ws := by
  refine TR.ind (P := fun s ws => MR [outF (y0 :: yt)] (s + yt.length) ws) h ?_ ?_ ?_
  · rw [Nat.zero_add]; exact or_chain yt y0
  · intro s xs zs hp _ ih; exact TR.perm hp ih
  · intro s a b r k u hc _ ih
    have e : s + 1 + yt.length = s + yt.length + 1 := by omega
    rw [e]
    exact TR.step k u hc ih
theorem frame (h0 : BF) {ys : List BF} {s : ℕ} {ws : List BF} (h : MR ys s ws) :
    MR (h0 :: ys) s (h0 :: ws) := by
  refine TR.ind (P := fun s ws => MR (h0 :: ys) s (h0 :: ws)) h TR.done ?_ ?_
  · intro s xs zs hp _ ih; exact TR.perm (hp.cons h0) ih
  · intro s a b r k u hc _ ih
    have p1 : (a :: b :: h0 :: r).Perm (h0 :: a :: b :: r) :=
      List.perm_middle (l₁ := [a, b])
    have p2 : (h0 :: (List.replicate (u + 1) (gF k a b) ++ r)).Perm
        (List.replicate (u + 1) (gF k a b) ++ h0 :: r) := List.perm_middle.symm
    exact TR.perm p1 (TR.step k u hc (TR.perm p2 ih))
def XI (x : Fin 7) (w : BF) : Prop := ∀ p b, w (Function.update p x b) = w p
def MonoF (w : BF) : Prop :=
  ∀ p q : Fin 7 → Bool, (∀ i, p i = true → q i = true) → w p = true → w q = true
def InvX (x : Fin 7) (w : BF) : Prop := XI x w ∧ MonoF w ∧ w (fun _ => false) = false
theorem InvX_gate {x : Fin 7} {k : Fin 4} (hk : MonoA k) {a b : BF} (ha : InvX x a)
    (hb : InvX x b) : InvX x (gF k a b) := by
  rcases mono_cases k hk with rfl | rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ && b _) = (a _ && b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_and] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ha.2.1 p q hpq h.1, hb.2.1 p q hpq h.2⟩
    · show (a _ && b _) = false
      rw [ha.2.2]; rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ || b _) = (a _ || b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_or] at h ⊢
      simp only [Bool.or_eq_true] at h ⊢
      exact h.imp (ha.2.1 p q hpq) (hb.2.1 p q hpq)
    · show (a _ || b _) = false
      rw [ha.2.2, hb.2.2]; rfl
theorem InvX_var {x m : Fin 7} (h : m ≠ x) : InvX x (var m) :=
  ⟨fun p v => by simp [var, Function.update_of_ne h], fun p q hpq hp => hpq m hp, rfl⟩
theorem mono_comm {k : Fin 4} (hk : MonoA k) (a b : BF) : gF k a b = gF k b a := by
  rcases mono_cases k hk with rfl | rfl
  · rw [gF_and, gF_and]; funext p; exact Bool.and_comm _ _
  · rw [gF_or, gF_or]; funext p; exact Bool.or_comm _ _
theorem upd_single_true (i x : Fin 7) :
    Function.update (singleInput i) x true = pairInput i x := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [pairInput]
  · simp [singleInput, pairInput, hm]
theorem single_eq_upd (x : Fin 7) :
    singleInput x = Function.update (fun _ => false) x true := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [singleInput]
  · simp [singleInput, hm]
theorem outF_rel (b' : BF) (p : Fin 7 → Bool) (hb : b' p = false) :
    ∀ (ys ys' : List BF), List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q) ys ys' →
      outF ys p = outF ys' p
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h t => by
    have ih := outF_rel b' p hb _ _ t
    simp only [outF, List.any_cons] at ih ⊢
    rw [h p hb, ih]
def SUc (x : Fin 7) (y0 : BF) (yt : List BF) (s : ℕ) (r : List BF) : Prop :=
  ((if otop x ∈ r then 2 else 3) ≤ s + yt.length ∧
    ∀ S : BF → Prop, (∀ w ∈ r, S w) → S (otop x) →
      UC gF MonoA (s + yt.length - (if otop x ∈ r then 2 else 3)) S
        (rst x (outF (y0 :: yt)))) ∨
  ∃ (c : ℕ) (h0 : BF) (ys' : List BF) (s' : ℕ), s = s' + 1 ∧ ys'.length = yt.length + 1 ∧
    ThrL (fun _ => True) (outF (h0 :: ys')) ∧
    MR (h0 :: ys') s' (List.replicate (c + 1) (var x) ++ r)
theorem SU (x : Fin 7) (y0 : BF) (yt : List BF)
    (hF : ThrL (fun _ => True) (outF (y0 :: yt))) :
    ∀ (s : ℕ) (r : List BF), MR (y0 :: yt) s (var x :: r) → (∀ w ∈ r, InvX x w) →
      SUc x y0 yt s r := by
  intro s
  induction s with
  | zero =>
    intro r h _
    exfalso
    have hp := (TR.inv h).1 rfl
    have hm : var x ∈ y0 :: yt := hp.mem_iff.1 (by simp)
    have h1 : outF (y0 :: yt) (singleInput x) = true :=
      (outF_true _ _).2 ⟨var x, hm, by simp [var, singleInput]⟩
    rw [hF.1 x trivial] at h1
    exact Bool.noConfusion h1
  | succ s ih =>
    intro r h hinv
    obtain ⟨k, u, a, b, r₁, hk, hp, hr⟩ := (TR.inv h).2 s rfl
    have consume : ∀ b' : BF, r.Perm (b' :: r₁) → gF k a b = gF k (var x) b' →
        SUc x y0 yt (s + 1) r := by
      intro b' hrp hg
      unfold SUc
      rw [hg] at hr
      have hb' : InvX x b' := hinv b' (hrp.mem_iff.2 (by simp))
      have hr1 : ∀ w ∈ r₁, InvX x w := fun w hw => hinv w (hrp.mem_iff.2 (by simp [hw]))
      have sens : ∀ i, i ≠ x → gF k (var x) b' (pairInput i x) =
          gF k (var x) b' (singleInput i) → False := by
        intro i hi hgg
        have hd := TRF_det hr (pairInput i x) (singleInput i) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · rw [List.eq_of_mem_replicate hw]; exact hgg
          · rw [← upd_single_true]
            exact (hr1 w hw).1 _ _)
        have h2 := outF_congr _ _ _ hd
        rw [hF.1 i trivial, hF.2 i x trivial trivial hi] at h2
        exact Bool.noConfusion h2
      have hbx : ∀ i, i ≠ x → b' (pairInput i x) = b' (singleInput i) := fun i _ => by
        rw [← upd_single_true]; exact hb'.1 _ _
      have hv1 : ∀ i, var x (pairInput i x) = true := fun i => by simp [var, pairInput]
      have hv2 : ∀ i, i ≠ x → var x (singleInput i) = false := fun i hi => by
        simp [var, singleInput, Ne.symm hi]
      rcases mono_cases k hk with rfl | rfl
      · left
        have hone : ∀ i, i ≠ x → b' (singleInput i) = true := by
          intro i hi
          by_contra hc
          have hc' : b' (singleInput i) = false := by simpa using hc
          apply sens i hi
          rw [gF_and]
          show (var x _ && b' _) = (var x _ && b' _)
          rw [hbx i hi, hc', hv2 i hi]; simp
        have hbo : b' = otop x := by
          funext p
          rw [← hb'.1 p false]
          by_cases hex : ∃ i, i ≠ x ∧ p i = true
          · obtain ⟨i, hi, hpi⟩ := hex
            have : otop x p = true := by simp only [otop, decide_eq_true_eq]; exact ⟨i, hi, hpi⟩
            rw [this]
            refine hb'.2.1 (singleInput i) _ ?_ (hone i hi)
            intro m hm
            have : m = i := by simpa [singleInput] using hm
            subst this
            rw [Function.update_of_ne hi]; exact hpi
          · have : otop x p = false := by simp only [otop, decide_eq_false_iff_not]; exact hex
            rw [this]
            have hz : Function.update p x false = fun _ => false := by
              funext m
              by_cases hm : m = x
              · subst hm; simp
              · rw [Function.update_of_ne hm]
                by_contra hc
                exact hex ⟨m, hm, by simpa using hc⟩
            rw [hz]; exact hb'.2.2
        have hmem : otop x ∈ r := hrp.mem_iff.2 (by simp [hbo])
        have hdead : rst x (gF 0 (var x) b') = zF := by
          funext p
          show (var x _ && b' _) = false
          simp [var]
        have hc := complete_run y0 yt hr
        obtain ⟨hd1, hd2⟩ := pot_dead x (thr_rst_ne hF x) hc
        rw [dcount_rep] at hd1 hd2
        simp only [hdead, ite_true] at hd1 hd2
        simp only [hmem, ite_true]
        refine ⟨by omega, fun S hS _ => UC_le (by omega) (hd2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hdead) hwz
        · have : rst x w = w := funext fun p => (hr1 w hw).1 p false
          rw [this]
          exact hS w (hrp.mem_iff.2 (by simp [hw]))
      · right
        have hzero : ∀ i, b' (singleInput i) = false := by
          intro i
          by_cases hi : i = x
          · subst hi
            rw [single_eq_upd, hb'.1]; exact hb'.2.2
          · by_contra hc
            have hc' : b' (singleInput i) = true := by simpa using hc
            apply sens i hi
            rw [gF_or]
            show (var x _ || b' _) = (var x _ || b' _)
            rw [hbx i hi, hc', hv1 i]; simp
        have hrel : List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q)
            (List.replicate (u + 1) (gF 1 (var x) b') ++ r₁)
            (List.replicate (u + 1) (var x) ++ r₁) := by
          refine List.rel_append ?_ (List.forall₂_same.2 fun _ _ _ _ => rfl)
          generalize u + 1 = n
          induction n with
          | zero => exact List.Forall₂.nil
          | succ n ihn =>
            refine List.Forall₂.cons (fun q hq => ?_) ihn
            show (var x q || b' q) = var x q
            rw [hq]; simp
        obtain ⟨ys', hy, hrun⟩ := TR.rel (A := MonoA)
          (fun w w' => ∀ q, b' q = false → w q = w' q)
          (fun k a a' b b' ha hb q hq => by
            show zeroGate k (a q) (b q) = zeroGate k (a' q) (b' q)
            rw [ha q hq, hb q hq]) hr _ hrel
        refine ⟨u, b', ys', s, rfl, ?_, ⟨fun i _ => ?_, fun i j _ _ hij => ?_⟩, ?_⟩
        · have := hy.length_eq
          simpa using this.symm
        · have e := outF_rel b' (singleInput i) (hzero i) _ _ hy
          have h3 : outF (b' :: ys') (singleInput i) =
              (b' (singleInput i) || outF ys' (singleInput i)) := by simp [outF]
          rw [h3, hzero i, ← e, hF.1 i trivial]; rfl
        · have h3 : outF (b' :: ys') (pairInput i j) =
              (b' (pairInput i j) || outF ys' (pairInput i j)) := by simp [outF]
          rw [h3]
          cases hbp : b' (pairInput i j)
          · have e := outF_rel b' (pairInput i j) hbp _ _ hy
            rw [← e, hF.2 i j trivial trivial hij]; rfl
          · rfl
        · have p1 : (b' :: (List.replicate (u + 1) (var x) ++ r₁)).Perm
              (List.replicate (u + 1) (var x) ++ r) :=
            List.perm_middle.symm.trans (List.Perm.append_left _ hrp.symm)
          exact TR.perm p1 (frame b' hrun)
    by_cases hax : a = var x
    · subst hax
      exact consume b hp.cons_inv rfl
    by_cases hbx : b = var x
    · subst hbx
      have hp' : (var x :: r).Perm (var x :: a :: r₁) := hp.trans (List.Perm.swap _ _ _)
      exact consume a hp'.cons_inv (mono_comm hk a (var x))
    have hx1 : var x ∈ r₁ := by
      have : var x ∈ a :: b :: r₁ := hp.mem_iff.1 (by simp)
      simp only [List.mem_cons] at this
      rcases this with h1 | h1 | h1
      · exact absurd h1.symm hax
      · exact absurd h1.symm hbx
      · exact h1
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx1
    have hr2 : r.Perm (a :: b :: (l₁ ++ l₂)) := by
      have p1 : (a :: b :: (l₁ ++ var x :: l₂)).Perm (var x :: a :: b :: (l₁ ++ l₂)) :=
        List.perm_middle (l₁ := a :: b :: l₁)
      exact (hp.trans p1).cons_inv
    have ha : InvX x a := hinv a (hr2.mem_iff.2 (by simp))
    have hb : InvX x b := hinv b (hr2.mem_iff.2 (by simp))
    have hsub : ∀ w ∈ l₁ ++ l₂, w ∈ r := fun w hw => hr2.mem_iff.2 (by simp [List.mem_append.1 hw])
    have p2 : (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ var x :: l₂)).Perm
        (var x :: (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_middle
    have hinv2 : ∀ w ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂), InvX x w := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw]; exact InvX_gate hk ha hb
      · exact hinv w (hsub w hw)
    have hih := ih _ (TR.perm p2 hr) hinv2
    unfold SUc at hih ⊢
    rcases hih with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
    · left
      by_cases hgo : gF k a b = otop x
      · have hm : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) := by
          rw [hgo]; simp
        simp only [hm, ite_true] at hA1 hA2
        refine ⟨by split_ifs <;> omega, fun S hS hSo => ?_⟩
        refine UC_le (by split_ifs <;> omega) (hA2 S ?_ hSo)
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgo]; exact hSo
        · exact hS w (hsub w hw)
      · have hiff : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) → otop x ∈ r := by
          intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact absurd (List.eq_of_mem_replicate hm).symm hgo
          · exact hsub _ hm
        have hcc : (if otop x ∈ r then 2 else 3) ≤
            (if otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) then 2 else 3) := by
          by_cases h1 : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂)
          · simp [h1, hiff h1]
          · simp only [h1, ite_false]; split_ifs <;> omega
        refine ⟨by omega, fun S hS hSo => ?_⟩
        have h1 := hA2 (fun w => w = gF k a b ∨ S w) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (List.eq_of_mem_replicate hw)
          · exact Or.inr (hS w (hsub w hw))) (Or.inr hSo)
        have h2 := UC_gate k a b hk (hS a (hr2.mem_iff.2 (by simp)))
          (hS b (hr2.mem_iff.2 (by simp))) h1
        exact UC_le (by omega) h2
    · right
      refine ⟨c, h0, ys', s' + 1, by omega, hl, hthr, ?_⟩
      have p3 : (List.replicate (c + 1) (var x) ++ r).Perm
          (a :: b :: (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) := by
        refine (List.Perm.append_left _ hr2).trans ?_
        exact List.perm_middle.trans (List.Perm.cons a List.perm_middle)
      have p4 : (List.replicate (c + 1) (var x) ++
          (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))).Perm
          (List.replicate (u + 1) (gF k a b) ++
            (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) :=
        List.perm_append_comm_assoc _ _ _
      subst hs'
      exact TR.perm p3.symm (TR.step k u hk (TR.perm p4 hrun))
theorem vars_list : ∀ (ws : List BF), (∀ w ∈ ws, ∃ i, w = var i) →
    ∃ idx : List (Fin 7), ws = idx.map var
  | [], _ => ⟨[], rfl⟩
  | w :: ws, h => by
    obtain ⟨i, rfl⟩ := h w (by simp)
    obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => h w (by simp [hw])
    exact ⟨i :: idx, rfl⟩
theorem len_counts : ∀ (idx : List (Fin 7)),
    idx.length = idx.count 0 + idx.count 1 + idx.count 2 + idx.count 3 + idx.count 4 + idx.count 5 + idx.count 6
  | [] => rfl
  | j :: idx => by
    have ih := len_counts idx
    fin_cases j <;> simp <;> omega
theorem outF_perm {ys ys' : List BF} (h : ys.Perm ys') (p : Fin 7 → Bool) :
    outF ys p = outF ys' p := h.any_eq
theorem restrict_thr (p : Fin 7) (F : BF) (ht : ThrL (fun _ => True) F) :
    Six.ThrL (fun _ => True) (proj p (rst p F)) := by
  have single : ∀ (p : Fin 7) (j : Fin 6),
      Function.update (p.insertNth false (singleInput j)) p false = singleInput (p.succAbove j) := by
    decide +kernel
  have pair : ∀ (p : Fin 7) (j k : Fin 6),
      Function.update (p.insertNth false (pairInput j k)) p false = pairInput (p.succAbove j) (p.succAbove k) := by
    decide +kernel
  refine ⟨fun j _ => ?_, fun j k _ _ hjk => ?_⟩
  · simpa only [proj,rst,single] using ht.1 (p.succAbove j) trivial
  · simpa only [proj,rst,pair] using ht.2 (p.succAbove j) (p.succAbove k)
      trivial trivial (fun eq => hjk (Fin.succAbove_right_injective eq))
theorem fiveLower (lb : Six.SixLow) (p : Fin 7) (F : BF) (ht : ThrL (fun _ => True) F) {k : Nat}
    (h : UC gF MonoA k (fun w => ∃ j, w = var (p.succAbove j)) (rst p F)) : 13 ≤ k := by
  have mapped := UC_map (G' := Six.gF) (proj p) (fun _ _ _ => rfl)
    _ _ (fun w => ∃ i, w = Six.var i) _
    (by rintro w ⟨i, rfl⟩; exact ⟨i, projVar p i⟩) h
  by_contra he
  exact Six.M6 lb (restrict_thr p F ht) (UC_le (by omega) mapped)
theorem count_le_dead (p : Fin 7) : ∀ idx : List (Fin 7), idx.count p ≤ dcount p (idx.map var)
  | [] => by simp [dcount]
  | j::js => by
    have ih := count_le_dead p js
    by_cases e : j=p
    · subst j
      simp [List.count_cons,dcount_cons,rst_var_self,ih]
    · simp [List.count_cons,e, dcount_cons]
      split <;> omega
theorem atMostTwo (lb : Six.SixLow) (y : BF) (ys : List BF) (idx : List (Fin 7)) (s : Nat)
    (h : MR (y::ys) s (idx.map var)) (hsize : s+ys.length=15)
    (thr : ThrL (fun _ => True) (outF (y::ys))) (p : Fin 7) :
    idx.count p ≤ 2 := by
  have closed := complete_run y ys h
  obtain ⟨h1,h2⟩ := pot_dead p (thr_rst_ne thr p) closed
  have hh := h2 (fun w => ∃ j, w = var (p.succAbove j)) (by
    intro w hw hz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    by_cases hi : i=p
    · subst i; exact False.elim (hz (rst_var_self p))
    · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi
      exact ⟨j,by rw [rst_var_ne hi,hj]⟩)
  have bound := fiveLower lb p _ thr hh
  have := count_le_dead p idx
  omega
def ImpossibleShared : Prop := ∀ (y : BF) (ys : List BF) (s : Nat) (idx : List (Fin 7)),
  MR (y::ys) s (idx.map var) → s+(y::ys).length ≤ idx.length+2 → (∀ i, idx.count i ≤ 2) →
  ThrL (fun _ => True) (outF (y::ys)) → False
theorem GS6 (lb : Six.SixLow) (one : ImpossibleShared) : ∀ (s : ℕ) (y0 : BF) (yt : List BF) (ws : List BF), MR (y0 :: yt) s ws →
    (∀ w ∈ ws, ∃ i, w = var i) → s + yt.length = 15 →
    ThrL (fun _ => True) (outF (y0 :: yt)) → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro y0 yt ws h hw hs hF
    have hlen := TR.len h
    obtain ⟨idx, rfl⟩ := vars_list ws hw
    have hpres : ∀ i, i ∈ idx := by
      intro i
      by_contra hi
      obtain ⟨j, hj, -⟩ := ex_third i i
      have hd := TRF_det h (pairInput i j) (singleInput j) (by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        have : m ≠ i := fun e => hi (e ▸ hm)
        simp [var, pairInput, singleInput, this])
      have h2 := outF_congr _ _ _ hd
      rw [hF.1 j trivial, hF.2 i j trivial trivial (Ne.symm hj)] at h2
      exact Bool.noConfusion h2
    simp only [List.length_map, List.length_cons] at hlen
    by_cases hall : ∀ i, 2 ≤ idx.count i
    · have hc := len_counts idx
      have h0 := hall 0
      have h1 := hall 1
      have h2 := hall 2
      have h3 := hall 3
      have h4 := hall 4
      have h5 := hall 5
      have h6 := hall 6
      apply one y0 yt s idx h _ (atMostTwo lb y0 yt idx s h hs hF) hF
      simp only [List.length_cons]
      omega
    · obtain ⟨x, hx⟩ := not_forall.1 hall
      have hx1 : idx.count x = 1 := by
        have := List.count_pos_iff.2 (hpres x)
        omega
      have hp : (idx.map var).Perm (var x :: (idx.erase x).map var) :=
        (List.perm_cons_erase (hpres x)).map var
      have hnx : x ∉ idx.erase x := by
        intro hm
        have := List.count_pos_iff.2 hm
        rw [List.count_erase_self] at this
        omega
      have hinv : ∀ w ∈ (idx.erase x).map var, InvX x w := by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        exact InvX_var fun e => hnx (e ▸ hm)
      have hsu := SU x y0 yt hF s _ (TR.perm hp h) hinv
      unfold SUc at hsu
      rcases hsu with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
      · have hno : otop x ∉ (idx.erase x).map var := by
          intro hm
          obtain ⟨m, -, he⟩ := List.mem_map.1 hm
          obtain ⟨j, hj1, hj2⟩ := ex_third m x
          have h5 := congrFun he (singleInput j)
          have h6 : var m (singleInput j) = false := by simp [var, singleInput, Ne.symm hj1]
          have h7 : otop x (singleInput j) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨j, hj2, by simp [singleInput]⟩
          rw [h6, h7] at h5
          exact Bool.noConfusion h5
        simp only [hno, ite_false] at hA1 hA2
        have h6 := hA2 (fun w => w = otop x ∨ ∃ j, w = var (x.succAbove j)) (by
          intro w hw'
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
          have hmx : m ≠ x := fun e => hnx (e ▸ hm)
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hmx
          exact Or.inr ⟨j, by rw [hj]⟩) (Or.inl rfl)
        have h7 := top_elim (otop x) _ (fun w => ∃ j, w = var (x.succAbove j)) _ (by
          rintro w ⟨j, rfl⟩ p hp'
          simp only [otop, decide_eq_true_eq]
          exact ⟨x.succAbove j, Fin.succAbove_ne x j, hp'⟩) (by
          intro he
          have h8 := (thr_rst hF x).1 0
          rw [he] at h8
          have h9 : otop x (singleInput (x.succAbove 0)) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨x.succAbove 0, Fin.succAbove_ne x 0, by simp [singleInput]⟩
          rw [h9] at h8
          exact Bool.noConfusion h8) h6
        have hb := fiveLower lb x _ hF h7
        omega
      · refine ih s' (by omega) h0 ys' _ hrun ?_ (by omega) hthr
        intro w hw'
        rcases List.mem_append.1 hw' with hw' | hw'
        · exact ⟨x, List.eq_of_mem_replicate hw'⟩
        · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hw'
          exact ⟨m, rfl⟩
theorem mono_sixteen (lb : Six.SixLow) (one : ImpossibleShared) (s : Nat)
    (h : UC gF MonoA s (fun w => ∃ i, w = var i) target) : 16 ≤ s := by
  obtain ⟨u,hu,ws,hw,hr⟩ := to_run targetThr h
  have h12 := transfer 13 (A := MonoA) (fun f hf k hk => by
    by_contra he
    exact Six.M6 lb hf (UC_le (by omega) hk)) hr hw
  by_contra he
  have eq : u=15 := by omega
  have ee : outF [target] = target := by funext x; simp [outF]
  exact GS6 lb one u target [] ws hr hw (by simp [eq]) (by rw [ee]; exact targetThr)
end ThresholdSixBound.Seven
namespace ThresholdSixBound.Seven
open Leaf5459
theorem sharedImpossible : ImpossibleShared := by
  intro y ys s idx run small count thr
  obtain ⟨H,G,Q,he,cost,hH,hG⟩ := SevenExtract.extract run small count
  apply ThresholdSeven.twoShare H G Q cost hH hG
  · intro i
    rw [he]
    exact thr.1 i trivial
  · intro i j hn
    rw [he]
    exact thr.2 i j trivial trivial hn
theorem monotoneLowerBound (lb : Six.SixLow) {s : ℕ} (h : UC gF MonoA s (fun w => ∃ i, w = var i) target) : 16 ≤ s :=
  mono_sixteen lb sharedImpossible s h
end ThresholdSixBound.Seven
namespace ThresholdSixBound.Seven
open Leaf5459 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def trueF : BF := fun _ => true
def memC (S : BF → Prop) (w : BF) := w = zF ∨ w = trueF ∨ S w
theorem monoGateForm (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = trueF ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a=zF) ∧ (b ∈ W ∨ b=zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op,ins⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases ins with _|⟨i,_|⟨j,_|rest⟩⟩
  · rcases hop with rfl|rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · rcases hop with rfl|rfl <;> refine Or.inr (Or.inr (Or.inl ⟨_,getD_mem W i,?_⟩)) <;>
      funext x <;> simp [gv,GateOp.eval]
  · rcases hop with rfl|rfl
    · exact Or.inr (Or.inr (Or.inr ⟨0,_,_,by simp [MonoA],getD_mem W i,getD_mem W j,
        funext (fun x => by simp [gv,gF,zeroGate,GateOp.eval])⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨1,_,_,by simp [MonoA],getD_mem W i,getD_mem W j,
        funext (fun x => by simp [gv,gF,zeroGate,GateOp.eval])⟩))
  · simp at hl
theorem monoNext {g W S} (hop : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, memC S w) :
    memC S (gv g W) ∨ ∃ k a b, MonoA k ∧ S a ∧ S b ∧ gv g W = gF k a b := by
  have read (a) (ha : a ∈ W ∨ a = zF) : memC S a := ha.elim (hW _) (fun ha => Or.inl ha)
  rcases monoGateForm g W hop hl with q|q|⟨a,ha,q⟩|⟨k,a,b,hk,ha,hb,q⟩
  · exact Or.inl (Or.inl q)
  · exact Or.inl (Or.inr (Or.inl q))
  · rw [q]; exact Or.inl (read a ha)
  · rcases read a ha with e|e|sa
    · rw [q,e]
      rcases gF_zero_left k b with z|same
      · exact Or.inl (Or.inl z)
      · rw [same]; exact Or.inl (read b hb)
    · rw [q,e]
      rcases mono_cases k hk with rfl|rfl
      · have red : gF 0 trueF b = b := by funext x; simp [gF_and,trueF]
        rw [red]; exact Or.inl (read b hb)
      · have red : gF 1 trueF b = trueF := by funext x; simp [gF_or,trueF]
        exact Or.inl (Or.inr (Or.inl red))
    · rcases read b hb with e|e|sb
      · rw [q,e]
        rcases gF_zero_right k a with z|same
        · exact Or.inl (Or.inl z)
        · rw [same]; exact Or.inl (Or.inr (Or.inr sa))
      · rw [q,e]
        rcases mono_cases k hk with rfl|rfl
        · have red : gF 0 a trueF = a := by funext x; simp [gF_and,trueF]
          rw [red]; exact Or.inl (Or.inr (Or.inr sa))
        · have red : gF 1 a trueF = trueF := by funext x; simp [gF_or,trueF]
          exact Or.inl (Or.inr (Or.inl red))
      · exact Or.inr ⟨k,a,b,hk,sa,sb,q⟩
theorem monoTrans : ∀ (gs : List Gate) (W : List BF) (S : BF→Prop),
    (∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ w∈W, memC S w) → ∀ o : ℕ,
    memC (UC gF MonoA gs.length S) ((wiresF gs W).getD o zF)
  | [], W, S, _, hW, o => by
    rcases getD_mem W o with q|q
    · exact hW _ q
    · exact Or.inl q
  | g::gs,W,S,legal,hW,o => by
    have hg:=legal g (by simp)
    have hr: ∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun v hv => legal v (List.mem_cons_of_mem _ hv)
    rcases monoNext hg.1 hg.2 hW with free | ⟨k,a,b,hk,ha,hb,eq⟩
    · have th:=monoTrans gs (W++[gv g W]) S hr (by
        intro w hw; rcases List.mem_append.mp hw with old|new
        · exact hW _ old
        · rwa [List.mem_singleton.mp new]) o
      rcases th with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_le (Nat.le_succ _) h))
    · have th:=monoTrans gs (W++[gv g W]) (fun w=>w=gF k a b ∨ S w) hr (by
        intro w hw; rcases List.mem_append.mp hw with old|new
        · exact (hW _ old).imp id (fun z => z.imp id Or.inr)
        · rw [List.mem_singleton.mp new]; exact Or.inr (Or.inr (Or.inl eq))) o
      rcases th with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_gate k a b hk ha hb h))
theorem circuitSevenLower (lb : Six.SixLow) (C : Circuit) (ok : Monotone2 C)
    (spec : ∀ x : Fin 7→Bool, C.eval (List.ofFn x) = target x) : 16 ≤ C.size := by
  have eq : (wiresF C.gates (List.ofFn var)).getD C.output zF = target := by
    funext x
    rw [← spec x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval,Circuit.wires,List.map_ofFn]
    rfl
  have h := monoTrans C.gates (List.ofFn var) (fun w=>∃ i, w=var i) ok (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact Or.inr (Or.inr ⟨i,rfl⟩)) C.output
  rw [eq] at h
  rcases h with z|t|h
  · exact False.elim (thr_ne_zero targetThr z)
  · have bad := congrFun t (fun _ => false)
    exact Bool.noConfusion bad
  · exact monotoneLowerBound lb h
end ThresholdSixBound.Seven

end PEqualNP.Outside.L_meta_10393_aux

theorem PEqualNP.Outside.L_meta_10393 : (¬ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => decide (2 ≤ ((List.ofFn x).count true))) 15)) := by
  exact PEqualNP.Outside.L_meta_10393_aux.SevenRoot.noCircuit PEqualNP.Outside.L_meta_10393_aux.signedThirteen (PEqualNP.Outside.L_meta_10393_aux.ThresholdSixBound.Seven.circuitSevenLower PEqualNP.Outside.L_meta_10393_aux.signedThirteen)
