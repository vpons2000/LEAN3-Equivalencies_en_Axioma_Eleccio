import TFG_VPL_Axiom_of_Choice TFG_VPL_set_theory_extra--TFG_VPL_Axiom_of_Choice 
open  Set empty functions AC_nodisj

universe u

variables {x y z t X Y Z T f g P 𝕏: Set.{u}}
variables a b c A B   Q: Set.{u}
namespace previs

--------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------
--def Ω (P:Set.{u}):set Set:={x:Set.{u}| x ∈ P}
def Φ (P:Set.{u}):set Set:={x:Set.{u}| x ⊆ P}

def π {P:Set.{u}}(x : Set.{u}) (h1 : x ∈ P) : P.to_set := subtype.mk x h1

def phi {P:Set.{u}}(X : Set.{u}) (h1 : X ⊆ P) : Φ P := subtype.mk X h1
--notation ⟨x,h⟩:= phi x h 
notation ⟨x,h⟩:= π x h 

namespace PO_lemmas
lemma phieq_val{P:Set.{u}}{X : Set.{u}} (h1 : X ⊆ P): (phi X h1).val = X:= congr_arg subtype.val rfl
lemma pieq_val {P:Set.{u}}{X : Set.{u}} (h1 : X ∈ P): ⟨X,h1⟩.val = X:= congr_arg subtype.val rfl

lemma pieq {P:Set.{u}}{X : P.to_set}{hp:X.1∈ P}: ⟨X.1,hp⟩ = X:= subtype.eq (pieq_val X.2)

variables {l k s:P.to_set}[partial_order P.to_set]

lemma le_vals {h1: l.1∈ P}{h2:k.1∈ P}: ⟨l.1,h1⟩  ≤ ⟨k.1,h2 ⟩ → l ≤ k:=
begin
  intro h,
  have hl:⟨l.1,h1⟩ =l, from pieq,have hk:⟨k.1,h2⟩ =k, from pieq,
  have l_le_h1: l  ≤ ⟨k.1,h2 ⟩,exact (eq.symm hl).trans_le h,
  exact eq.trans_ge hk l_le_h1,
end

lemma vals_of_pieq_of_le {h1: k.1∈ P}: l ≤ ⟨k.1,h1 ⟩ → l ≤ k:= λh , eq.trans_ge pieq h
lemma vals_of_le_of_pieq {h1: k.1∈ P}: ⟨k.1,h1 ⟩ ≤ l → k ≤ l:= λ h, (eq.symm pieq).trans_le h

lemma vals_of_pieq_of_lt {h1: k.1∈ P}: l < ⟨k.1,h1 ⟩ → l < k:= λh , eq.trans_gt pieq h
lemma vals_of_lt_of_pieq {h1: k.1∈ P}: ⟨k.1,h1 ⟩ < l → k < l:= λ h, (eq.symm pieq).trans_lt h

lemma vals_of_pieq_of_lt_iff {h1: k.1∈ P}: l < ⟨k.1,h1 ⟩ ↔ l < k:= 
begin 
  split, exact λh , eq.trans_gt pieq h,
  exact λ h, (eq.symm pieq).trans_gt h,
end


lemma lt_vals {h1: l.1∈ P}{h2:k.1∈ P}: ⟨l.1,h1⟩  < ⟨k.1,h2 ⟩ ↔ l < k:=
begin 
  have hl:⟨l.1,h1⟩ =l, from pieq,have hk:⟨k.1,h2⟩ =k, from pieq,
  split, intro h,
  have l_lt_h1: l  < ⟨k.1,h2 ⟩,exact (eq.symm hl).trans_lt h,
  exact eq.trans_gt hk l_lt_h1,
  --
  intro h,
  have l_lt_h1: ⟨l.1,h1 ⟩ < k ,exact eq.trans_lt hl h,
  exact (eq.symm hk).trans_gt l_lt_h1,
end

end PO_lemmas
#check P.to_set
#check P.to_set
#check set.mem_set_of.mpr

namespace Order

--class defined_partial_order (α:Type u)(hle:α → α → Prop) extends partial_order α:=
--(le_def: ∀ (a b:α), a ≤ b ↔ hle a b)

structure PartialOrderInstance :=
  (α : Type u)
  (le : α → α → Prop)
  (partial_order_proof : partial_order α)


-----------------------------------------------------------------------------------------

--lemma le_def (α:Type)(hle:α → α → Prop)[defined_partial_order α hle]: ∀ {a b:α}, a ≤ b ↔ hle a b:= (λ a b, defined_partial_order.le_def a b)

variable [partial_order (P.to_set)]
variable [partial_order (Q.to_set)]

--definim la condició de ser cadena
def is_chain (C:Φ P):Prop:= ∀ (x y : Set.{u}) (h1:x∈C.1) (h2:y∈C.1), ⟨x,C.2 h1⟩  ≤ ⟨y,C.2 h2⟩ ∨ ⟨y,C.2 h2⟩ ≤ ⟨x,C.2 h1⟩
--definim el conjunt de cadenes

def chains :Set.{u}:= {C ∈ powerset Q |∃(h1:C⊆Q), is_chain (phi C h1)}

--definim suprem o cota superior
def suprem (s :P.to_set)(X:Φ P):Prop:=∀(x:Set.{u})(h1:x ∈ X.1), ⟨x, (X.2 h1)⟩  ≤ s
notation s `suprem_de` X:= suprem s X

--Element maximal
def element_maximal (M:P.to_set) :Prop:=  ∀x:P.to_set , M ≤ x → M = x 
lemma not_maximal_to_lt {s:P.to_set}: ¬ (element_maximal s) → ∃x:P.to_set,s < x:=
begin
  intro notMax,by_contra,
  have s_max:element_maximal s, intros x hx, by_contra s_neq_x,
    have s_lt_x:s<x, from ne.lt_of_le s_neq_x hx,
    exact h (exists.intro x s_lt_x),
  exact notMax s_max,
end

--Mínim d'un conjunt
def minim_of_set (A:Φ P)(m:P.to_set)(hm:m.1 ∈ A.1):=∀(x:Set.{u})(hx:x ∈ A.1), m ≤ ⟨x, A.2 hx⟩ 

--Conjunt inferior a un element
def Cv (C: Φ P){x:Set.{u}}(hx:x∈ C.1):Set.{u}:={y ∈ C.1 | ∃(hy:y∈C.1),⟨y,C.2 hy⟩  < ⟨x,C.2 hx⟩}
notation C`↓`hx:=Cv C hx 

--conjunt de suprems d'un conjunt
def Upp (C: Φ P) : Set.{u}:={x∈ P| ∃(hx:x∈P),∀(y:Set.{u})(hy:y∈C.1), ⟨y, C.2 hy⟩  < ⟨x,hx⟩}
---------------------------------------------------------------------------------------------------
lemma Cv_ss_C {C: Φ P}{x:Set.{u}}{hx:x∈ C.1}: (C↓hx)⊆ C.1:=λ y hy, (mem_sep.mp hy).left
lemma Cv_ss_P {C: Φ P}{x:Set.{u}}{hx:x∈ C.1}: (C↓hx)⊆ P:= previs.subset_trans (Cv_ss_C) C.2

lemma mem_cv {C: Φ P}{x:Set.{u}}{hx:x∈ C.1}{w:Set.{u}}: w ∈ (C↓hx) ↔ (∃(h1:w∈C.1),⟨w, C.2 h1⟩ < ⟨x,C.2 hx⟩):=
begin
  split, intro h,exact (mem_sep.mp h).right,
  intro h,apply mem_sep.mpr,rcases h with ⟨w_in_C,w_lt_x⟩, split, exact (w_in_C), exact exists.intro w_in_C w_lt_x, 
end

open previs.PO_lemmas

lemma cv_is_cad_of_cad {C: Φ P}{x:Set.{u}}(cadC:is_chain C){hx:x∈ C.1}:is_chain (phi (C↓hx) Cv_ss_P):=
begin
  intros a b ha hb,
  have heq: (phi (C↓hx) Cv_ss_P).val = (C↓hx), from phieq_val Cv_ss_P,
  have a_in_C:a∈ C.1, from (mem_sep.mp (mem_of_eq_of_set heq ha)).left,
  have b_in_C:b∈C.1, from (mem_sep.mp (mem_of_eq_of_set heq hb)).left,
  exact cadC a b a_in_C b_in_C,
end



lemma diffsubtype (A B:Φ P):(A.1\B.1)⊆P:=λ w hw, A.2 (mem_diff.mp hw).left 

end Order
end previs
------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------
open previs previs.Order 
--PreLema de Zorn-
def preZorn (P:Set.{u})(hpo:partial_order (P.to_set)):Prop:=
(Set_nonempty P) ∧ 
(∀ (C:Φ P),(C.1 ∈ chains P) → (Set_nonempty C.1)  → (∃ s :P.to_set , suprem s C))
→ ∃ (M : P.to_set), element_maximal M
--Lema de Zorn--
def Zorn:Prop:=∀(P:Set.{u})(hpo:partial_order (P.to_set)),preZorn.{u} P hpo

------------------------------------------------------------------------------------------------------
-------------------------------------------Zorn → AC--------------------------------------------------
------------------------------------------------------------------------------------------------------
namespace preAC
  --definim la condició de ser cadena
  def is_chain2 (P:Set.{u})(h:partial_order (P.to_set)) (C:Φ P):Prop:= ∀ {x y : Set.{u}} (h1:x∈C.1) (h2:y∈C.1), ⟨x,C.2 h1⟩  ≤ ⟨y,C.2 h2⟩ ∨ ⟨y,C.2 h2⟩ ≤ ⟨x,C.2 h1⟩
  def chains2 (P:Set.{u})(h:partial_order (P.to_set)) :Set.{u}:= {C ∈ powerset P |∃(h1:C⊆P), is_chain2 P h (phi C h1)}

  --definim suprem o cota superior
  def suprem2 (P:Set.{u})(hpo:partial_order (P.to_set))(s :P.to_set)(X:Φ P):Prop:=∀(x:Set.{u})(h1:x ∈ X.1), ⟨x, (X.2 h1)⟩  ≤ s

  --Element maximal
  def element_maximal2 (P:Set.{u})(hpo:partial_order (P.to_set))(M:P.to_set) :Prop:=  ∀x:P.to_set , M ≤ x → M = x 


  lemma L1 (hpo:partial_order (P.to_set)){M Q:P.to_set}(h2:element_maximal2 P hpo M) (h3:M≤ Q) :M.1=Q.1:=
  begin
    have h5, from (h2 Q h3), exact congr_arg subtype.val (h2 Q h3),
  end

  def P_ (𝕏:Set.{u}) :Set.{u}:= {Z∈ (powerset 𝕏).prod (powerset (𝕏.prod 𝕏.sUnion))| ∃ 𝕐 G:Set.{u}, G∈(𝕐.funs 𝕐.sUnion) ∧ (∀{x y:Set.{u}}, x.pair y ∈ G → y∈ x) ∧  Z=𝕐.pair G}

  def hle_ (P:Set.{u}):(P.to_set) →(P.to_set) → Prop:=λ a b, ∃(X Y G H:Set.{u}),
    (X ⊆ Y) 
    ∧ (G ⊆ H)
    ∧ (X.pair G = a.1 ∧  Y.pair H = b.1)

  ---------------------------------


  lemma hle_antisymm :∀ (a b : ((P_ 𝕏).to_set)), hle_ (P_ 𝕏) a b → hle_ (P_ 𝕏) b a → a = b:=
  begin intros a b hab hba,
    have a_eq_b:a.1=b.1,
    rcases hab with ⟨ X1, Y1, G1, H1, hab1,hab2,hab3⟩,
      rcases hba with ⟨ Y2, X2, H2, G2, hba1,hba2,hba3⟩,
      --aleshores, com, tenim que X1=a.1=X2 i Y1 = b.1 =Y2  i Y1 = Y2 ∧ H1 = H2
      have ha1:X1 = X2 ∧ G1 = G2, from pair_inj.mp (eq.trans hab3.left hba3.right.symm),
      have ha2:Y1 = Y2 ∧ H1 = H2,from pair_inj.mp (eq.trans hab3.right hba3.left.symm),
      --aleshores com X1⊆Y1 i Y2⊆ X2
      have X_eq_Y:X1=Y1,
        have Y_ss_X:Y1⊆ X1,from (calc
        Y1  = Y2 : ha2.left
        ... ⊆ X2 : hba1
        ... = X1 : ha1.left.symm
        ),
        exact eq_of_subsets hab1 Y_ss_X,
      --ara demostrem que G=H
      have G_eq_H:G1=H1,
        have H_ss_G:H1⊆ G1,from (calc
        H1  = H2 : ha2.right
        ... ⊆ G2 : hba2
        ... = G1 : ha1.right.symm
        ),
        exact eq_of_subsets hab2 H_ss_G,
      --aleshores com tenim que X1=Y1 i G1=H1, tenim que a.1=X.pair G=Y.pair H=b.1
      exact (calc
        a.1 = X1.pair G1 : hab3.left.symm
        ... = Y1.pair H1 : pair_inj.mpr (and.intro X_eq_Y G_eq_H)
        ... = b.1        : hab3.right
      ),
    --aleshores tenim que compleix la propietat antisimètrica
    exact subtype.eq a_eq_b,  
  end

  lemma hle_refl:∀ (a : ((P_ 𝕏).to_set)),hle_ (P_ 𝕏) a a:=
  begin
    intro a, cases a with a a_in_P,
    --com a ∈ P, aleshores [ a∈ (powerset 𝕏).prod (𝕏.prod 𝕏.sUnion) ] ∧ [ ∃ 𝕐 G:Set.{u}, G∈(𝕐.funs 𝕐.sUnion) ∧ a=𝕐.pair G ] 
    have ha,from (mem_sep.mp a_in_P).left, rcases mem_prod.mp ha with ⟨a1,ha1,a2,ha2,ha3⟩, 
    --aleshores tenim que es compleix
    have a_ss:a⊆a, from previs.subset_of_eq rfl,
    exact exists.intro a1 (exists.intro a1 ( exists.intro a2 (exists.intro a2 ( and.intro (previs.subset_of_eq rfl) ( and.intro (previs.subset_of_eq rfl) (and.intro ha3.symm ha3.symm)))))), 
  end

  lemma hle_trans:∀ (a b c: ((P_ 𝕏).to_set)),hle_ (P_ 𝕏) a b → hle_ (P_ 𝕏) b c →hle_ (P_ 𝕏) a c:=
  begin
    intros a b c hab hbc, 
    rcases hab with ⟨X, Y1, G, H1,hab1,hab2,hab3⟩,
    rcases hbc with ⟨Y2, Z, H2, F,hbc1,hbc2,hbc3⟩,
    have ha:Y1 = Y2 ∧ H1 = H2,from pair_inj.mp (eq.trans hab3.right hbc3.left.symm),
    --tenim en primer lloc que Y1 = Y2 ∧ H1=H2
    have YH_eq: Y1 = Y2 ∧ H1=H2, from pair_inj.mp (eq.trans hab3.right hbc3.left.symm),
    --estem en condicions de demostrar que ≤ és transitiva
    have htrans:(X ⊆ Z) ∧ (G ⊆ F) ∧ (X.pair G = a.1 ∧  Z.pair F = c.1),
    -- ⊢ X ⊆ Z
      split,exact previs.subset_trans hab1 (previs.subset_trans (previs.subset_of_eq ha.left ) hbc1),split,
    -- ⊢ G  ⊆ F
      exact previs.subset_trans hab2 (previs.subset_trans (previs.subset_of_eq ha.right ) hbc2),
      exact and.intro hab3.left hbc3.right,
    exact exists.intro X (exists.intro Z (exists.intro G (exists.intro F (htrans)))),  
  end 
  ---------------------------------

  def myPartialOrderInstance (𝕏:Set.{u}) : PartialOrderInstance :=
  {
    α := ((P_ 𝕏).to_set),
    le:= hle_ (P_ 𝕏),
    partial_order_proof:= {
      le:= hle_ (P_ 𝕏),
      le_antisymm:= hle_antisymm,
      le_refl:=hle_refl,
      le_trans:=hle_trans
    }
  }
  #print myPartialOrderInstance
    
  lemma Pne (h𝕏E:𝕏≠ (∅:Set.{u}))(𝕏_props: ∅ ∉ 𝕏) : (P_ 𝕏).nonempty:=
  begin
    --com 𝕏 no és buit tenim que existeix algun element X de 𝕏
      have 𝕏ne:Set_nonempty 𝕏, from nonempty_iff_notEmpty.mpr h𝕏E, cases 𝕏ne with X hX,
      --ara com X∈ 𝕏 → ∃x ∈ X
      have Xne:Set_nonempty X, from xne_of_XhasNoE_of_xinX 𝕏_props hX, cases Xne with x hx,
      --aleshores definim l'aplicació J:{X}→ {X}.sUnion; J(X) = x
      set J:Set.{u}:={X.pair x},set X_:Set.{u}:={X},
      --demostrem que està ben definida
      
      have hJ:J∈ funs X_ X_.sUnion, apply mem_sep.mpr , 
        --primer demostrem que hXX : X∈ {X}
          have hXX:X∈ X_,exact mem_singleton.mpr rfl,
        --demostrem hxX: x∈ {X}.sUnion
          have hxX:x∈ X_.sUnion, exact mem_sUnion.mpr (exists.intro X (exists.intro (mem_singleton.mpr rfl) hx)),
        --J⊆ {X}.prod {X}.sUnion
        have hJ:J⊆ X_.prod X_.sUnion,
          intros w hw,-- tenim que w∈J={X.pair x} → w = X.pair x
          --demostrem que X.pair x ∈ {X}.prod {X}.sUnion
          have hXx_in_XUX:X.pair x ∈ X_.prod X_.sUnion, exact pair_mem_prod.mpr (and.intro hXX hxX),
          --aleshores tenim w= X.pair x ∈ {X}.prod {X}.sUnion
          exact mem_of_eq_of_mem (mem_singleton.mp hw).symm hXx_in_XUX,
        split,
          exact mem_powerset.mpr hJ,split, exact hJ,
          --⊢ ∀x:Set, x∈ {X}→ ∃! w:Set, z.pair w∈ J
          intros z hz, split,split, exact mem_of_eq_of_mem_left (mem_singleton.mp hz).symm (mem_singleton.mpr rfl),
            --⊢∀w:Set, z.pair w∈ J → w=x
            intros w hw, exact (pair_inj_right (mem_singleton.mp hw)),
      --ja hem demostrat que està ben definida, vegem que ({X},J) ∈ P
      have XY_in_P1:X_.pair J ∈ (powerset 𝕏).prod (powerset (𝕏.prod 𝕏.sUnion)), apply pair_mem_prod.mpr,split,
      --⊢ {X}∈ (powerset 𝕏)
        have h2: {X}⊆ 𝕏, intros w hw, exact mem_of_eq_of_mem (mem_singleton.mp hw).symm hX,
        exact mem_powerset.mpr h2,
      --⊢{X.x} = J ⊆ (𝕏.prod 𝕏.sUnion)
        --tenim que w ∈ {X.x}→ w = X.x ∈ 𝕏.prod 𝕏.sUnion
        have Xx_in_XUX:X.pair x ∈ 𝕏.prod 𝕏.sUnion, from pair_mem_prod.mpr (and.intro hX (mem_sUnion.mpr (exists.intro X (exists.intro hX hx)))),
        exact mem_powerset.mpr (λ w hw, (mem_of_eq_of_mem (mem_singleton.mp hw).symm Xx_in_XUX)),
      --⊢ ∀ (x y : Set), x.pair y ∈ J → y ∈ x
        have hcf:∀ (x y : Set), x.pair y ∈ J → y ∈ x, intros w y hwy, 
        --aleshores com (w,y)=(X,x), i tenim que y=x ∈ X=w,
        have h1:w = X ∧ y = x,from pair_inj.mp (mem_singleton.mp hwy),
        exact mem_of_eq_of_mem h1.right.symm (mem_of_eq_of_set h1.left.symm hx), 
      --Aleshores tenim que {X}.pair J ∈ P
      have XJ_in_P: (X_.pair J)∈ P_ 𝕏, exact mem_sep.mpr (and.intro XY_in_P1 (exists.intro X_ (exists.intro J (and.intro hJ (and.intro hcf rfl))))),
      exact exists.intro (X_.pair J) XJ_in_P,
    -- Hem demostrat que P no és buit 
  end

  def hpo (𝕏:Set.{u}):=(myPartialOrderInstance 𝕏).partial_order_proof

  lemma PWO {𝕏:Set.{u}} : ∀ (C:Φ (P_ 𝕏)),(C.1 ∈ (chains2 (P_ 𝕏) (hpo 𝕏)) → (Set_nonempty C.1)  → (∃ s : (P_ 𝕏).to_set , suprem2 (P_ 𝕏) (hpo 𝕏) s C)):=
  begin
    --siga C una cadena no buida de P
    intros C C_chain C_ne,
    --definim Z com a la unió de totes les primeres components de C
    set 𝒵:Set.{u}:= {Y∈𝕏 | ∃𝕐 G:Set.{u}, (𝕐.pair G ∈ C.1) ∧ (Y ∈ 𝕐)},
    set 𝒢:Set.{u}:= {Z∈ 𝕏.prod 𝕏.sUnion | ∃ X Y G 𝕐 :Set.{u}, (X∈ 𝕐) ∧ (X.pair Y ∈ G) ∧ (𝕐.pair G ∈ C.1)  ∧ Z=X.pair Y},
    --demostrem que 𝒢 ∈ funs 𝒵 𝒵.sUnion
    have G_fun_Z: 𝒢 ∈ 𝒵.funs 𝒵.sUnion, apply mem_sep.mpr, 
      --𝒢∈ (𝒵.prod 𝒵.sUnion).powerset
      have hG:𝒢 ⊆ 𝒵.prod 𝒵.sUnion,
        intros w hw, 
        --tenim que existeixen X Y G 𝕐 tal que (X∈ 𝕐) ∧ (X.pair y ∈ G) ∧ (𝕐.pair G ∈ C.1)  ∧ (w = X.pair y)
        have hG:∃ X Y G 𝕐 :Set.{u}, (X∈ 𝕐) ∧ (X.pair Y ∈ G) ∧ (𝕐.pair G ∈ C.1)  ∧ w=X.pair Y, from (mem_sep.mp hw).right, rcases hG with ⟨X,y,G,𝕐,hG1,hG2,hG3,hG4⟩,
        --vegem que (𝕐,G)∈ C ⊆ P → 
        --  𝕐.pair G ∈ (powerset 𝕏).prod (powerset (𝕏.prod 𝕏.sUnion)) ∧ 
        --  ( ∃ 𝕐2 G2, (G2 ∈ (𝕐2.funs 𝕐2.sUnion)) ∧ (𝕐.pair G = 𝕐2.pair G2) )
        have YG_in_P: 𝕐.pair G ∈ (P_ 𝕏), exact C.2 hG3, rcases (mem_sep.mp YG_in_P) with ⟨ h𝕐G,𝕐2,G2, hP1, hP2,hP3 ⟩,
        --vegem que X.pair y ∈ 𝒵.prod 𝒵.sUnion
        have hXY: X.pair y ∈ 𝒵.prod 𝒵.sUnion, apply pair_mem_prod.mpr,
        --⊢ X∈ 𝒵
          --en primer lloc sabem que 𝕐 = 𝕐2
          have Y2Y:𝕐=𝕐2, from pair_inj_left hP3,
          --Ara, també tenim qeu 𝕐 ⊆ 𝕏
          have Y_ss_X:𝕐⊆ 𝕏, from mem_powerset.mp (pair_mem_prod_left h𝕐G),
          --com X∈ 𝕐 tenim que X∈𝕏, ja que (𝕐,G)∈ C ⊆ P ∧ X ∈ 𝕐 ⊆ 𝕏 ← 𝕐2 ∈ 𝒫(𝕏) 
          have X_in_𝕏:X∈ 𝕏, exact  Y_ss_X hG1,split,
          --aleshores ja tenim que X∈ 𝒵
          exact mem_sep.mpr (and.intro X_in_𝕏 (exists.intro 𝕐 (exists.intro G (and.intro hG3 hG1)))),
        --⊢ y∈ 𝒵.sUnion
          --com G=G2 ∈ (𝕐2.funs 𝕐2.sUnion) ⊆ ( 𝕐2.prod 𝕐2.sUnion ).powerset → 
          have G_ss_YY:G ⊆  𝕐2.prod 𝕐2.sUnion, from (mem_sep.mp (mem_of_eq_of_mem (pair_inj_right hP3).symm hP1)).right.left,
          --aleshores X.pair y∈ G ⊆ 𝕐2.prod 𝕐2.sUnion → y ∈ 𝕐2.sUnion = 𝕐.sUnion
          have Y_in_UX:y ∈ 𝕐.sUnion, exact mem_of_eq_of_set (eq_sUnion (pair_inj_left hP3).symm) (pair_mem_prod_right (G_ss_YY hG2)), rcases (mem_sUnion.mp Y_in_UX) with ⟨Y,hY,hy⟩,   
          --per tant tenim que ∃(Y ∈ 𝕐), y ∈ Y, aleshores demostrem que Y∈ 𝒵
          have Y_in_Z:Y ∈ 𝒵, from mem_sep.mpr (and.intro (Y_ss_X hY) (exists.intro 𝕐 (exists.intro G (and.intro hG3 hY)))),
          --aleshores tenim que y∈ 𝒵.sUnion
          exact mem_sUnion.mpr (exists.intro Y (exists.intro Y_in_Z hy)),
        exact mem_of_eq_of_mem hG4.symm hXY,
      split, exact mem_powerset.mpr hG,split, exact hG,
      --demostrem que està ben definida G: ∀z∈ 𝒵, ∃!w, z.pair w ∈ 𝒢
      intros z hz, 
      --Ara com z∈𝒵,tenim que ( z∈ 𝕏 ) ∧  ∃ 𝕐 G, (𝕐.pair G ∈ C.1) ∧ (z ∈ 𝕐)
      rcases ( mem_sep.mp hz ) with ⟨ hz0 , 𝕐 , G , hz1 , hz2 ⟩,
      --Aleshores com z∈ 𝕐 i (𝕐,G)∈ C.1 ⊆ P, aleshores tenim que existeixen  𝕐2 G2, G2∈ 𝕐2.funs 𝕐2.sUnion ∧ (𝕐,G)=(𝕐2,G2)
      have hYG, from (mem_sep.mp (C.2 hz1)), rcases hYG with ⟨C0, 𝕐2, G2, hG2,CFG2,hYG⟩,
      --com G2 ∈ 𝕐2.funs 𝕐2.sUnion i x∈𝕐=𝕐2  aleshores existeix un únic y∈ 𝕐2.sUnion, (x,y)∈G2=G
      have hy, from ((mem_sep.mp hG2).right.right z (mem_of_eq_of_set (pair_inj_left hYG) hz2)), rcases  hy with ⟨y,hy,yuniq⟩,
      --aleshores z.pair y∈ G2=G
      have hzy1: z.pair y∈G, from (mem_of_eq_of_set (pair_inj_right hYG).symm hy),
      --ara, provem que z.pair y∈ 𝕏.prod 𝕏.sUnion, ja que z.pair y∈ 
      have hy2:z.pair y∈𝕏.prod 𝕏.sUnion,
        --en primer lloc tenim que G⊆ 
        --primer com que z.pair y∈ G2 ∈ funs 𝕐2 𝕐2.sUnion, tenim que y∈ 𝕐2.sUnion
        have hy2:y∈ 𝕐2.sUnion, from (pair_mem_prod_right ((mem_sep.mp hG2).right.left hy)),
        --aleshores, com 𝕐2=𝕐⊆ 𝕏, tenim que y∈ U𝕐2 = U𝕐 ⊆ U𝕏
        have hy3: y∈ 𝕏.sUnion, from (subset_sUnion (mem_powerset.mp (pair_mem_prod_left C0))) (mem_of_eq_of_set (eq_sUnion (pair_inj_left hYG).symm) hy2),
        --aleshores ja estem en condicions per demostrar que z.pair y∈𝕏.prod 𝕏.sUnion
        exact pair_mem_prod.mpr (and.intro hz0 hy3),
      --aleshores ja estem en condicions de provar que z.pair y∈ 𝒢
      have hzy2:(z.pair y)∈𝒢, from (mem_sep.mpr (and.intro hy2 (exists.intro z (exists.intro y (exists.intro G (exists.intro 𝕐 (and.intro hz2 (and.intro (mem_of_eq_of_set (pair_inj_right hYG).symm hy) (and.intro hz1 rfl))))))))),
      --aleshores existeix un w tal que z.pair w ∈ 𝒢
      split,split, exact hzy2,
      --només cal demostrar que és únic. Suposem que hi ha un w tal que z.pair w∈ 𝒢, volem demostrar que w=y, aleshores ∃ z0 w0 G0 𝕐0 tal que z0 ∈ 𝕐0 ∧ z0.pair w0 ∈ G0 ∧ 𝕐0.pair G0 ∈ C.val ∧ z.pair w = z0.pair w0
        intros w hw, rcases (mem_sep.mp hw) with ⟨zw_in_XX,z0,w0,G0,𝕐0,hz0, zw0_in_G0,YG0_in_C, h0 ⟩,
        --Ara com (𝕐0,G0)∈ C.1, i C és cadena, tenim que, o bé  (𝕐0,G0)≤ (𝕐,G) o (𝕐,G) ≤ (𝕐0,G0)
        rcases (mem_sep.mp C_chain) with ⟨C_in_P,C_in_Q, hcchain⟩,
        specialize hcchain YG0_in_C hz1,
        cases hcchain,
        --si hcchain:(𝕐0,G0)≤ (𝕐,G) aleshores 
          --have hYG0_le_YG, from hpo_le_def.mp hcchain, 
          rcases hcchain with ⟨A0,A,B0,B,A0_le_A, B0_le_B, AB_eq_YG⟩,
          --ara com tenim que A0.pair B0 = (𝕐0,G0) i A.pair B = (𝕐,G) obtenim
          have le_eq:(A0=𝕐0 ∧ B0=G0) ∧ (A=𝕐 ∧ B = G ), from and.intro (pair_inj.mp AB_eq_YG.left) (pair_inj.mp AB_eq_YG.right),
          --aleshores com estem suposant que z,w = z,w0∈ G0 = B0 ⊆ B = G = G2,
          have G0_ss_G2:G0⊆ G2, intros a ha, exact mem_of_eq_of_set (eq.trans le_eq.right.right (pair_inj_right hYG))  (B0_le_B (mem_of_eq_of_set le_eq.left.right.symm ha)),
          have w_in_G2: z.pair w ∈ G2,exact mem_of_eq_of_mem h0.symm (G0_ss_G2 zw0_in_G0),
          --aleshores tenim que w = y
          exact yuniq w w_in_G2,
        --si hcchain:(𝕐,G) ≤ (𝕐0,G0) aleshores
          rcases hcchain with ⟨A,A0,B,B0,A_le_A0, B_le_B0, AB_eq_YG⟩,
          --ara com tenim que A0.pair B0 = (𝕐0,G0) i A.pair B = (𝕐,G) obtenim
          have le_eq:(A0=𝕐0 ∧ B0=G0) ∧ (A=𝕐 ∧ B = G ), from and.intro (pair_inj.mp AB_eq_YG.right) (pair_inj.mp AB_eq_YG.left),
          --Aleshores z.pair y ∈ G=B ⊆ B0 = G0
          have zy_in_G0:z.pair y ∈ G0, from mem_of_eq_of_set le_eq.left.right (B_le_B0 (mem_of_eq_of_set le_eq.right.right.symm hzy1)),
          --aleshores com 𝕐0.pair G0 ∈C ⊆   P → ∃𝕐1 G1, G1∈(𝕐1.funs 𝕐1.sUnion) ∧ (∀x y:Set.{u}, x.pair y ∈ G1 → y∈ x) ∧  𝕐0.pair G0 = 𝕐1.pair G1
          have 𝕐G0_in_P:𝕐0.pair G0 ∈ (P_ 𝕏), from C.2 YG0_in_C,rcases (mem_sep.mp 𝕐G0_in_P).right with ⟨ 𝕐1, G1, G1func, CFG, h1eq⟩,
          --aleshores com 𝕐0.pair G0 = 𝕐1.pair G1
          have h1eq:𝕐0=𝕐1 ∧ G0 = G1, from pair_inj.mp h1eq,
          --aleshores, com z.pair y∈ G0 = G1 ∈ 𝕐1.funs 𝕐1 
          have zy_in_G1:z.pair y ∈ G1, from mem_of_eq_of_set h1eq.right zy_in_G0,
          --com z.pair y ∈ G1⊆ 𝕐1.funs 𝕐1 ⊆ 𝕐1.prod 𝕐1.sUnion → z∈ 𝕐1
          have z_in_Y1:z∈𝕐1, from pair_mem_prod_left ((mem_sep.mp G1func).right.left zy_in_G1),
          --aleshores, com z∈ 𝕐1, ∃!w1, z.pair w1∈ G1
          have hz1uniq, from ((mem_sep.mp G1func).right.right z z_in_Y1), rcases hz1uniq with ⟨w1, hw1, w1uniq ⟩,
          --aleshores, com z.pair y ∈ G1, y= w1
          have y_eq_w1: y=w1, from w1uniq y zy_in_G1,
          --també tenim que z.pair w = z.pair w0 ∈ G0 = G1
          have zw_in_G1:z.pair w ∈ G1, exact mem_of_eq_of_set h1eq.right (mem_of_eq_of_mem h0.symm zw0_in_G0),
          --aleshores tenim que w=w1
          have w_eq_w1: w=w1, from w1uniq w zw_in_G1,
          --aleshores tenim que w = w1 = y
          exact eq.trans w_eq_w1 y_eq_w1.symm,
    --ja hem demostrat que 𝒢 és una funció, 
    
    --demostrem que és funció d'elecció
    have CFG:(∀x y:Set.{u}, x.pair y ∈ 𝒢 → y∈ x), intros X x hXx_in_G,
      --aleshores, com (X,x)∈ 𝒢, ∃ Y y G 𝕐 :Set.{u}, (Y∈ 𝕐) ∧ (Y.pair y ∈ G) ∧ (𝕐.pair G ∈ C.1)  ∧ X.pair x = Y.pair y
      rcases (mem_sep.mp hXx_in_G).right with ⟨Y, y, G, 𝕐, Y_in_𝕐, Yy_in_G, YG_in_C, heq ⟩,
      --aleshores, com  𝕐.pair G ∈ C.1 ⊆ P → ∃ 𝕐P GP:Set.{u}, GP∈(𝕐P.funs 𝕐P.sUnion) ∧ (∀x y:Set.{u}, x.pair y ∈ GP → y∈ x) ∧  𝕐.pair G=𝕐P.pair GP
      rcases (mem_sep.mp (C.2 YG_in_C)).right with ⟨ 𝕐P,GP, GPfuns, CFGP, heqP ⟩,
      --aleshores com  X.pair x= Y.pair y ∈ G = GP
      have Xx_in_GP:X.pair x ∈ GP, from mem_of_eq_of_set (pair_inj_right heqP) (mem_of_eq_of_mem heq.symm Yy_in_G),
      --per tant, x∈ X
      exact CFGP Xx_in_GP,
    --queda provat que és una funció d'elecció

    --Ara, provem que 𝒵.pair 𝒢 ∈ (powerset 𝕏).prod (powerset (𝕏.prod 𝕏.sUnion))
    have ZG_in_PXPXUX:𝒵.pair 𝒢 ∈ (powerset 𝕏).prod (powerset (𝕏.prod 𝕏.sUnion)), 
      have Z_in_PX: 𝒵 ⊆ 𝕏, intros z hz, exact (mem_sep.mp hz).left,
      have G_in_PXUX:𝒢 ⊆ 𝕏.prod 𝕏.sUnion, intros w hw, exact (mem_sep.mp hw).left,
      exact pair_mem_prod.mpr (and.intro (mem_powerset.mpr Z_in_PX) (mem_powerset.mpr G_in_PXUX)),
    --aleshores obtenim que (𝒵,𝒢)∈ P

    have ZG_in_P: 𝒵.pair 𝒢 ∈ (P_ 𝕏), from mem_sep.mpr (and.intro ZG_in_PXPXUX (exists.intro 𝒵 (exists.intro 𝒢 (and.intro G_fun_Z (and.intro CFG rfl))))),
    --aleshores, com ZG∈ P tenim que ZG és suprem de C
    have ZGsup: suprem2 (P_ 𝕏) (hpo 𝕏) ⟨𝒵.pair 𝒢 ,ZG_in_P⟩  C, intros x hx,
      --volem demostrar que ⟨x, (C.2 hx)⟩  ≤ ⟨𝒵.pair 𝒢 ,ZG_in_P⟩
      --com x ∈ P, aleshores x∈𝕏.powerset.prod (𝕏.prod 𝕏.sUnion).powerset ∧ ∃𝕐 G:Set.{u}, G∈(𝕐.funs 𝕐.sUnion) ∧ (∀{x y:Set.{u}}, x.pair y ∈ G → y∈ x) ∧  x=𝕐.pair G
      rcases (mem_sep.mp (C.2 hx)) with ⟨hx0, 𝕐,G,Gfunc,CFG, heq ⟩,
      -- 𝕐.prod G ⊆ 𝕏.prod (𝕏.prod 𝕏.sUnion), ja que 𝕐.prod G = x ∈ 𝕏.powerset.prod (𝕏.prod 𝕏.sUnion).powerset
        have YG_ss_XXUX:𝕐.pair G ∈ 𝕏.powerset.prod (𝕏.prod 𝕏.sUnion).powerset, from mem_of_eq_of_mem heq hx0,
        have YssX_GssUX: 𝕐 ∈  𝕏.powerset ∧ G∈ (𝕏.prod 𝕏.sUnion).powerset , from (pair_mem_prod.mp YG_ss_XXUX),
      -- 𝕐 ⊆ 𝒵 --
      have Y_ss_Z:𝕐 ⊆ 𝒵, intros w hw,
          --tenim que 𝕐.pair G = x∈ C.1
          have YG_in_C: 𝕐.pair G∈C.1, from mem_of_eq_of_mem heq hx,
          --aleshores 𝕐.prod G ⊆ 𝕏.powerset.prod (𝕏.prod 𝕏.sUnion).powerset → 𝕐 ⊆ 𝕏
          have Y_ss_X:𝕐 ⊆ 𝕏, from mem_powerset.mp YssX_GssUX.left,
          --aleshores ja hem obtés que w∈ 𝒵
          exact mem_sep.mpr (and.intro (Y_ss_X hw) (exists.intro 𝕐 (exists.intro G (and.intro YG_in_C hw)))),
      -- G ⊆ 𝒢 --
      have G_ss_Z: G ⊆ 𝒢,intros w hw,
          --primer tenim que G ⊆  𝕏.prod 𝕏.sUnion
          have G_in_XUX:G ⊆ 𝕏.prod 𝕏.sUnion, from mem_powerset.mp YssX_GssUX.right,
          --ara, com G∈𝕐.prod 𝕐.funs, tenim que w ∈ G ⊆ 𝕐.prod 𝕐.sUnion
          have w_in_YUY:w∈ 𝕐.prod 𝕐.sUnion, from (mem_sep.mp Gfunc).right.left hw,
          --aleshores tenim que ∃a,b / a.pair b = a
          rcases (mem_prod.mp w_in_YUY) with ⟨a, ha, b, hb, ab_eq_w ⟩,
          --aleshores tenim que w∈ 𝒢
          exact mem_sep.mpr (and.intro (G_in_XUX hw) (exists.intro a (exists.intro b (exists.intro G (exists.intro 𝕐 (and.intro ha (and.intro (mem_of_eq_of_mem ab_eq_w hw) (and.intro (mem_of_eq_of_mem heq hx) ab_eq_w )))))))),
      -- Aleshores ja tenim que es compleix:
      exact (exists.intro 𝕐 (exists.intro 𝒵 (exists.intro G (exists.intro 𝒢 (and.intro Y_ss_Z (and.intro G_ss_Z (and.intro heq.symm rfl))))))), 
    --aleshores ja podem aplicar el lema e Zorn
    split, exact ZGsup,
    
  end
      --Aleshores podem aplicar el lema de Zorn a P

  lemma WDGA (fFunc:f∈ Y.funs Y.sUnion)(hx:x∈X)(X_notin_Y:X∉Y): f∪{X.pair x}∈ (Y∪{X}).funs (Y∪{X}).sUnion:=
  begin
    apply mem_funs.mpr,
    --primer vegem que f⊆(Y∪{X}).prod (Y∪{X}).sUnion
    have fss:f⊆(Y∪{X}).prod (Y∪{X}).sUnion,intros w hw2,
      have w_in_YUY: w∈ Y.prod Y.sUnion, from (mem_funs.mp fFunc).left hw2,
      have Y_ss:Y⊆ Y∪{X}, from subset_union_left,
      have YU_ss:Y.sUnion⊆ (Y∪{X}).sUnion, from subset_sUnion (Y_ss),
      exact (subset_trans (subset_prod_right YU_ss) (subset_prod_left Y_ss )) w_in_YUY,
    --ara vegem que {X.pair x}⊆ (Y∪{X}).prod (Y∪{X}).sUnion
    have Xxss:{X.pair x}⊆(Y∪{X}).prod (Y∪{X}).sUnion, intros w hw2,
        have Xx_in_YUY:X.pair x ∈ (Y∪{X}).prod (Y∪{X}).sUnion,apply pair_mem_prod.mpr,
        have X_in_YX:X∈ (Y∪{X}), from mem_union.mpr (or.inr (mem_singleton.mpr rfl)),split,
        exact X_in_YX, exact mem_sUnion.mpr (exists.intro X (exists.intro X_in_YX hx)),
      --aleshores w∈ {X.pair x} ⊆ (Y∪{X}).prod (Y∪{X}).sUnion
      exact (subset_of_singleton_of_mem Xx_in_YUY) hw2,
    --aleshores tenim que f∪{X.pair x}⊆(Y∪{X}).prod (Y∪{X}).sUnion
    split, intros w hw,have hw2, from mem_union.mp hw, cases hw2,
    ----volem demostrar que w∈ (Y∪{X}).prod (Y∪{X}).sUnion
    --w∈f--
      -- com w∈ f⊆ (Y∪{X}).prod (Y∪{X}).sUnion
      exact fss hw2,
    --w∈{X.pair x}--
      exact Xxss hw2,
    --(∃! (w : Set), z.pair w ∈ f ∪ {X.pair x})
    intros z hz, have hz2, from mem_union.mp hz, cases hz2,
    --z∈ Y--
      --aleshores com z∈ Y,∃!w, z.pair w∈ f
      rcases (mem_funs.mp fFunc).right z hz2 with ⟨w, hw, wuniq⟩,
      --i com w∈ f⊆f∪ {X.pair x}
      have w_in_f2:z.pair w∈ f∪{X.pair x}, from subset_union_left hw,
      split,split, exact w_in_f2,
      --⊢∀ (y : Set), (λ (w : Set), z.pair w ∈ f ∪ {X.pair x}) y → y = w
      intros y hy, have hy2, from mem_union.mp hy, cases hy2,
      --z.pair y∈ f--
        exact wuniq y hy2,
      --z.pair y∈ {X.pair x}
        --ara, com z.pair w∈ f⊆ Y.pair Y.sUnion, tenim que z∈ Y
        have z_in_Y:z∈ Y, from pair_mem_prod_left ((mem_funs.mp fFunc).left hw),
        have X_in_Y:X∈ Y, from mem_of_eq_of_mem (pair_inj_left (mem_singleton.mp hy2)) z_in_Y,
        exact false.elim (X_notin_Y X_in_Y),
    --z=X--
      --aleshores la imatge serà x
      split,split, exact mem_of_eq_of_mem_left (mem_singleton.mp hz2).symm (mem_union.mpr (or.inr (mem_singleton.mpr rfl))),
      --⊢ ∀ (y : Set), (λ (w : Set), z.pair w ∈ f ∪ {X.pair x}) y → y = x
      intros y hy,have hy2, from mem_union.mp hy, cases hy2,
      --z.pair y∈ f-- aleshores X=z∈ f⊆ Y.pair Y.Union
        have X_in_Y:X∈ Y, from pair_mem_prod_left ((mem_funs.mp fFunc).left (mem_of_eq_of_mem_left (mem_singleton.mp hz2) hy2)),
        exact false.elim (X_notin_Y X_in_Y),
      --z.pair y ∈ {X.pair x}
        exact pair_inj_right (mem_singleton.mp hy2), 
  end


  lemma zorn_to_AC (hzorn:Zorn.{u})(𝕏_props: ∅ ∉ 𝕏):∃(f:Set.{u})(h:f∈ 𝕏.funs (𝕏.sUnion)), ChoiceFunction f:=
  begin
  --suposem que 𝕏 és el buit
    by_cases h𝕏E:𝕏=(∅:Set.{u}),
      --definim f com l'aplicació buida
      set f:={x∈ (∅:Set.{u}).prod (∅:Set.{u}).sUnion| false},
      --demostrem que l'aplicació buida està ben definida
      have h1:f ∈ 𝕏.funs 𝕏.sUnion, apply mem_sep.mpr,
        --vegem que f⊆ 𝕏.prod 𝕏.sUnion i  que està ben definida
        have fss:f⊆ 𝕏.prod 𝕏.sUnion, intros w hw,exact false.elim (mem_sep.mp hw).right,
        split, exact mem_powerset.mpr fss,split, exact fss, intros z hz, exact false.elim (not_mem_empty z (mem_of_eq_of_set h𝕏E hz)),
      --només queda demostrar que és funció d'elecció
      have h2:ChoiceFunction f, intros z w hzw,
        exact false.elim (mem_sep.mp hzw).right,
      exact exists.intro f (exists.intro h1 h2),
    
  --suposem que 𝕏 no és buit  h𝕏E:¬ 𝕏 = ∅
    specialize hzorn (P_ 𝕏) (hpo 𝕏) (and.intro (Pne h𝕏E 𝕏_props) PWO),
    cases hzorn with M M_max, cases M with M M_in_P,
    --com que M∈ P, aleshores podem desglosar M en N⊆𝕏 i G:N→ UN
    rcases (mem_sep.mp M_in_P) with ⟨hMX,N,G,Gfunc,CFG,Meq ⟩,
    --aleshores en primer lloc tenim que M⊆ 𝕏
    have N_ss_X: N⊆𝕏, from mem_powerset.mp (pair_mem_prod_left (mem_of_eq_of_mem Meq hMX)),
    --demostrem que N=X i aleshores obtenim que G és funció d'elecció ben definida
    have N_eq_X:N=𝕏, --si ho tenim, arribem a que G = f
    --aleshores només queda demostrar que N = 𝕏
      by_contra N_neq_X, 
      have XlNne: Set_nonempty (𝕏\N), from diff_nonempty_of_subsetneq N_ss_X N_neq_X,
      --aleshores tenim que existeix un X∈ (𝕏\N)
      cases XlNne with X hX, have hX, from mem_diff.mp hX, cases hX with hX X_notin_N,
      --Ara, com  ∅ ∉ 𝕏, tenim que X.nonempty → ∃ x∈ X
      have Xne:Set_nonempty X, from xne_of_XhasNoE_of_xinX 𝕏_props hX, cases Xne with x hx,
      --volem demostrar que G∪{X.pair x}∈ P
        --primer provem que G∪{X.pair x}∈ (Y∪{X}).funs (Y∪{X}).sUnion 
        have WDGUX:G∪{X.pair x}∈ (N∪{X}).funs (N∪{X}).sUnion, from WDGA Gfunc hx X_notin_N,
        --ara provem que és funció d'elecció:
        have CFGUX: ∀(a b:Set.{u}), a.pair b ∈ G∪{X.pair x} → b∈ a, intros a b hab, have hab2, from (mem_union.mp hab),cases hab2,
          --si ab∈ G
            exact CFG hab2,
          --si ab∈{X.pair x}
            have h1:a=X ∧  b=x ,from pair_inj.mp (mem_singleton.mp hab2),
            --b=x ∈ X = a 
            exact mem_of_eq_of_mem h1.right.symm (mem_of_eq_of_set h1.left.symm hx),
        --només queda demostrar que estan dins de N∪{X}.pair G∪{X.pair x}∈(𝕏).powerset.prod (𝕏.prod 𝕏.sUnion).powerset
        have hfinale:(N∪{X}).pair (G∪{X.pair x})∈𝕏.powerset.prod (𝕏.prod 𝕏.sUnion).powerset,
          --primer vegem que N∪{X}⊆ 𝕏
          have NuX_ss:N∪{X}⊆ 𝕏, from subset_of_union_of_subsets N_ss_X (subset_of_singleton_of_mem hX),
          have GuXx_ss_XUX:G∪{X.pair x} ⊆ 𝕏.prod 𝕏.sUnion, from previs.subset_trans (mem_funs.mp WDGUX).left (subset_prod_inj_mpr NuX_ss (subset_sUnion NuX_ss)),
          exact pair_mem_prod.mpr (and.intro (mem_powerset.mpr NuX_ss) (mem_powerset.mpr GuXx_ss_XUX)),
        --Aleshores ja tenim que G∪{X.pair x}∈ P
      have GuXx_in_P:(N∪{X}).pair (G∪{X.pair x})∈ P_ 𝕏, from mem_sep.mpr (and.intro hfinale (exists.intro (N∪{X}) (exists.intro (G∪{X.pair x}) (and.intro WDGUX (and.intro CFGUX rfl))))),
      --tenim que N.pair G∈ P
      have NG_in_P:N.pair G∈ P_ 𝕏, from mem_of_eq_of_mem Meq M_in_P, 
      --només queda demostrar que N.pair G ≤ (N∪{X}).pair (G∪{X.pair x})
      have leDEF: (hle_ (P_ 𝕏)) ⟨M,M_in_P⟩ ⟨(N∪{X}).pair (G∪{X.pair x}), GuXx_in_P ⟩,
        --(X ⊆ Y) ∧ (G ⊆ H)
        have N_ss:N⊆ (N∪{X}), from subset_union_left,
        have G_ss:G⊆ (G∪{X.pair x}),from subset_union_left,
        split,split,split,split,split, exact N_ss, split, exact G_ss,exact and.intro Meq.symm rfl,
      --Aleshores, com M era maximal i M ≤ (N∪{X}).pair (G∪{X.pair x}) tenim que M=(N∪{X}).pair (G∪{X.pair x})
      specialize M_max ⟨(N∪{X}).pair (G∪{X.pair x}), GuXx_in_P ⟩ leDEF,
      --aleshores N.pair G=M=N∪{X}.pair G∪{X.pair x}
      have M_eq_NGuXx: M = ((N∪{X}).pair (G∪{X.pair x})), from congr_arg subtype.val M_max,
      --aleshores tenim que N=N∪{X}
      have N_eq_NuX:N=N∪{X}, from pair_inj_left (eq.trans Meq.symm M_eq_NGuXx),
      --aleshores tenim que N∪{X}⊆ N → {X}⊆ N
      have X_ss_N:{X}⊆ N, from subset_of_subset_of_union_left (previs.subset_of_eq N_eq_NuX.symm),
      --aleshores tenim que X ∈ N
      have X_in_N:X∈N, from mem_of_subsingleton_subset.mp X_ss_N,
      exact X_notin_N X_in_N,
    --aleshores ja tenim que és funció d'elecció G perque N=𝕏
    have h1:G ∈ 𝕏.funs (⋃₀ 𝕏), from N_eq_X ▸ Gfunc,
    have h2:ChoiceFunction G, intros a b hab, exact CFG hab,
    exact exists.intro G (exists.intro h1 h2),
  end
end preAC

------------------------------------------------------------------------------------------------------
-------------------------------------------AC → Zorn--------------------------------------------------
------------------------------------------------------------------------------------------------------
namespace preZorn
variables [partial_order P.to_set][partial_order Q.to_set]
-------------------------------------------
--                 LEMA A                --
-------------------------------------------
lemma LA (Pne:Set_nonempty P) (PWO:∀ (C : (Φ P)), C.val ∈ chains P → Set_nonempty C.val → (∃ (s : (P.to_set)), s suprem_de C))
(hnon_max:¬∃ (M : P.to_set), element_maximal M):
∀(C:Φ P)(Cchain:is_chain C), (Set_nonempty (Upp C)):=  
begin
  intros C Cchain, by_cases hCne:C.1=(∅:Set.{u}),
  --si C.1=∅ 
    --aleshores existeix un x∈ P, demostrem que x∈ Upp ∅
    cases Pne with x hx,
    have x_in_UppC:x∈ Upp(C),apply mem_sep.mpr,split, exact hx,split, intros y hy, exact false.elim (not_mem_empty y (mem_of_eq_of_set hCne hy)), exact hx,
    split, exact x_in_UppC,
  --si C.1≠ ∅
    have Cne:Set_nonempty C.1, from nonempty_iff_notEmpty.mpr hCne,
    --aleshores, com no és buit, per la condició del lema de Zorn obtenim que C té suprem
    have C1chain:C.1∈ chains P, apply mem_sep.mpr,split, exact mem_powerset.mpr C.2, split, exact Cchain, exact C.2,
    --nomenem s al suprem de C
    have supC, from PWO C C1chain Cne, cases  supC with s sSupC,
    --sabem que s no pot ser maximal
    by_cases hmax:element_maximal s, exact false.elim (hnon_max (exists.intro s hmax)),
    --si s no és element maximal, aleshores existeix un element x superior a s
    have xmax:∃x:P.to_set, s < x, from not_maximal_to_lt hmax, cases xmax with x xmax,
    have x_eq_x:x=⟨x.1,x.2⟩, from subtype.eq rfl,
    have s_lt_x:s<⟨x.1,x.2⟩, exact eq.trans_gt x_eq_x xmax,
    --vegem que x està en Upp C
    have x_in_UppC:x.1∈ Upp(C),apply mem_sep.mpr,split, exact x.2, split, intros y hy, exact lt_of_le_of_lt (sSupC y hy) (s_lt_x),
    exact exists.intro x.1 x_in_UppC,
end

def ℂ :Set.{u}:={Z∈ powerset Q| ∃C:(Φ Q), is_chain C ∧ Z=Upp C}

lemma C_hasnt_E (Pne:Set_nonempty P) (PWO:∀ (C : (Φ P)), C.val ∈ chains P → Set_nonempty C.val → (∃ (s : (P.to_set)), s suprem_de C))
(hnon_max:¬∃ (M : P.to_set),element_maximal M) : (∅:Set.{u}) ∉ (ℂ P) :=
begin
  intro E_in_C,
  --aleshores ∃C, cadena , ∅ = Upp C
  rcases (mem_sep.mp E_in_C).right with ⟨C,Cchain,Ceq⟩, 
  --aleshores tenim que (Upp C) no és buit
  have UppCne:Set_nonempty (Upp C), from (LA Pne PWO hnon_max) C Cchain, cases UppCne with x hx,
  exact not_mem_empty x (mem_of_eq_of_set Ceq.symm hx),
end

--Definim la funció d'elecció F tal que x.pair y ∈ F → y ∈ x

class conforme (f:Set.{u}) (A:Φ P):Prop:=
(C0:Set_nonempty A.1)
(C1:∀(X:Set.{u})(hss:X⊆A.1), Set_nonempty X → (∃(x:P.to_set)(hx:x.1∈X),minim_of_set (phi X (previs.subset_trans hss A.2)) x hx))
(C2:∀(x:Set.{u})(hx: x∈ A.1), (Upp (phi (A↓hx) (Cv_ss_P))).pair x ∈ f)

lemma CC1 {A:Φ P} (hconf:conforme f A): ∀{X:Set.{u}}(hss:X⊆A.1), Set_nonempty X → (∃(x:P.to_set)(hx:x.1∈X),minim_of_set (phi X (previs.subset_trans hss A.2)) x hx):= hconf.C1
lemma CC2 {A:Φ P} (hconf:conforme f A): ∀{x:Set.{u}}{hx: x∈ A.1}, (Upp (phi (A↓hx) (Cv_ss_P))).pair x ∈ f:=hconf.C2


lemma confCadC1 (f:Set.{u}) (A:Φ P) (hCC1:∀(X:Set.{u})(hss:X⊆A.1), Set_nonempty X → (∃(x:P.to_set)(hx:x.1∈X),minim_of_set (phi X (previs.subset_trans hss A.2)) x hx)):is_chain A:=
begin
  intros a b ha hb,
  have ab_ss_A:{a,b}⊆ A.1, intros w hw, have hw2, from mem_pair.mp hw, cases hw2,
    exact mem_of_eq_of_mem hw2.symm ha,--si w=a
    exact mem_of_eq_of_mem hw2.symm hb,--si w=b
  have abne: Set_nonempty {a,b}, from exists.intro a (mem_pair.mpr (or.inl rfl)),
  --aleshores existeix un mínim de {a,b}
  have hmin,from hCC1 {a,b} ab_ss_A abne,rcases hmin with ⟨x,hx,xmin⟩, have hx2,from mem_pair.mp hx, cases hx2,
  --si x.val=a
    have x_le_b:x ≤ ⟨b, A.2 hb⟩ , from xmin b (mem_pair.mpr (or.inr rfl)), 
    have x_eq_a:⟨x.1, x.2⟩ = ⟨a,A.2 ha⟩, from subtype.eq hx2,
    have x_eq_x:⟨x.1,x.2⟩ = x, from subtype.eq rfl,
    exact or.inl ((eq.trans x_eq_a.symm x_eq_x).trans_le x_le_b),
  --si x.val = b
    have x_le_a:x ≤ ⟨a, A.2 ha⟩ , from xmin a (mem_pair.mpr (or.inl rfl)),
    have x_eq_a:⟨x.1, x.2⟩ = ⟨b,A.2 hb⟩, from subtype.eq hx2,
    have x_eq_x:⟨x.1,x.2⟩ = x, from subtype.eq rfl,
    exact or.inr ((eq.trans x_eq_a.symm x_eq_x).trans_le x_le_a),
end
lemma confCad {f:Set.{u}} {A:Φ P}:conforme f A → is_chain A:=λ h, confCadC1 f A h.C1


-------------------------------------------
--                 LEMA B                --
-------------------------------------------
open previs.PO_lemmas


lemma LB {f:Set.{u}} {A B:Φ P} (fFunc:f∈ (ℂ P).funs (⋃₀ ℂ P) ) (hA:conforme f A)(hB:conforme f B):Set_nonempty (A.1\B.1)→ (∃(x:Set.{u})(h1:x∈ (A.1\B.1)), B.1 = (A↓(mem_diff.mp h1).left) ∧ minim_of_set (phi (A.1\B.1) (diffsubtype A B)) ⟨x,A.2 (mem_diff.mp h1).left ⟩ h1 ):=
begin
  intros AlBne,
  --com que A\B⊆ A
  have AlB_ss_A: A.1\B.1⊆ A.1, exact dif_subset,
  --Aleshores tenim que té mínim
  have AlBmin,from CC1 hA AlB_ss_A AlBne, 
  rcases AlBmin with ⟨ x, hx,xmin⟩, 
  have hprob:(phi (A.val \ B.val) (previs.subset_trans dif_subset A.2 )).val = (A.val \ B.val), from phieq_val (previs.subset_trans dif_subset A.2), 
  have hx2:x.val∈ (phi (A.val \ B.val) (previs.subset_trans dif_subset A.2 )).val,from mem_of_eq_of_set hprob.symm hx ,
  --només tenim que demostrar que 
  have LemaB: B.val = (A↓(mem_diff.mp hx).left),swap, split,split,split,exact LemaB, 
    --demostrem que si es dona el lema B aleshores ja estaria:
    intros y hy, have hy2, from mem_of_eq_of_set hprob hy,
    have x_le_y:x ≤ ⟨y, A.2 (mem_diff.mp hy2).left⟩, from xmin y hy2,
    exact le_trans (le_of_eq pieq) x_le_y,
--LEMA B--
  set Ax:Set.{u} := (A↓(mem_diff.mp hx).left),
  ext w,split,swap,
--A↓x ⊆ B
  intro w_in_Ax, by_contra w_notin_B,
  --aleshores w∈ (A.val\B.val)
  have w_in_Alb:w∈ (A.val\B.val), from mem_diff.mpr (and.intro (Cv_ss_C w_in_Ax) (w_notin_B)),
  --per tant x ≤ w
  have x_le_w:x ≤ ⟨w , Cv_ss_P w_in_Ax⟩ , from xmin w w_in_Alb,
  --i per hipòtesi, w< x
  have w_lt_x:⟨w , Cv_ss_P w_in_Ax⟩ < x, cases (mem_cv.mp w_in_Ax) with h1 h2, exact vals_of_pieq_of_lt h2,
  --aleshores x≤ w < x
  have x_irrefl:x<x, from lt_of_le_of_lt x_le_w w_lt_x, exact lt_irrefl x x_irrefl,
--B ⊆ A↓x
  intros hw, by_contra w_notin_Ax,
  --aleshores B\w_notin_Ax no és buit, i és subconjunt de B 
  have BlAxne:Set_nonempty (B.val\(A↓(mem_diff.mp hx).left)),split, exact mem_diff.mpr (and.intro hw w_notin_Ax),
  have BlAxss:(B.val\(A↓(mem_diff.mp hx).left))⊆ B.1, from dif_subset,
  --per tant té mínim y
  have BlAx_min, from CC1 hB BlAxss BlAxne, rcases BlAx_min with ⟨y,hy,ymin⟩,
  set By:Set.{u}:=(B↓(mem_diff.mp hy).left),
  --LEMA B1--
  have LB1: ∀{v u:P.to_set}(h1 :v.1 ∈ A.val)(h2:u.1∈ By), v < u → v.1∈ By,
    intros v u hv hu v_lt_u,
    --en primer lloc tenim que v < y 
    have v_lt_y:v < y, cases (mem_cv.mp hu) with hu u_lt_y, exact lt_trans v_lt_u ( lt_vals.mp u_lt_y),
    --només cal demostrat que v∈ B
    have v_in_B:v.1 ∈ B.1, by_contra v_notin_B,
      --aleshores v∈ A\B
      have v_in_AlB:v.1∈A.val\B.val, from mem_diff.mpr (and.intro hv v_notin_B), 
      -- Ara, com x ≤ v i v < u → u ∉ A↓x
      have x_le_v:x≤ v, from vals_of_pieq_of_le (xmin v.1 v_in_AlB),
      have x_lt_u:x < u, from lt_of_le_of_lt x_le_v v_lt_u,
      have u_notin_Ax:u.1∉Ax, intro u_in_Ax, cases (mem_cv.mp u_in_Ax) with u_in_A u_lt_x,
        --ja que si u∈A↓x → x < u < x
        have x_irrefl:x<x, from lt_trans x_lt_u (lt_vals.mp u_lt_x),exact lt_irrefl x x_irrefl,
      --Aleshores, tenim que u∈ B\A↓x,
      have u_in_BlAx:u.1∈ B.1\Ax, from mem_diff.mpr (and.intro (mem_sep.mp hu).left u_notin_Ax),
      --per tant, per definició de y≤u i per def de u < y
      have y_le_u:y ≤ u, from vals_of_pieq_of_le (ymin u.1 u_in_BlAx), 
      have u_lt_y:u<y, cases (mem_cv.mp hu) with u_in_B u_lt_y, exact lt_vals.mp u_lt_y,
      --aleshores tenim que y < y
      have y_irrefl:y<y, from lt_of_le_of_lt y_le_u u_lt_y, 
      exact lt_irrefl y y_irrefl,
    exact mem_cv.mpr (exists.intro v_in_B (lt_vals.mpr v_lt_y)),
  --Així queda demostrat el lema B1

  --Ara, com A\B no és buit, aleshores A\B↓y tampoc
  have x_notin_By:x.val∉By,intro x_in_By, have x_in_B:By ⊆ B, from Cv_ss_C, exact (mem_diff.mp hx).right (x_in_B x_in_By), 

  have AlBy_ne:Set_nonempty (A.val\By), 
    split, exact mem_diff.mpr (and.intro (mem_diff.mp hx).left x_notin_By),
  have AlBy_ss_A:(A.val\By)⊆ A, from dif_subset,
  --Aleshores podem aplicar la 1a propietat de conforme 
  have hzmin, from CC1 hA AlBy_ss_A AlBy_ne, rcases hzmin with ⟨z,hz,zmin⟩, 
  set Az:Set.{u}:=(A↓(mem_diff.mp hz).left),
  --aleshores demostrem que Az=By
  have LB2:Az=By,ext w,split,
  --w∈ Az→ w∈ By
    intro hw,by_contra w_notin_By,
    --aleshores w∈ A\By
    have w_in_AlBy: w∈ (A.val\By),from mem_diff.mpr (and.intro (mem_sep.mp hw).left w_notin_By),
    --per tant, com z és mínim de  A\By, tenim que  z≤ w
    have z_le_w: z ≤ ⟨w,A.2 (mem_diff.mp w_in_AlBy).left⟩, from (zmin w w_in_AlBy),
    --però, com w∈ Az, w< z
    cases (mem_cv.mp hw) with hw w_lt_z,
    --aleshores z < w < z
    have z_irrefl:z<z, from vals_of_pieq_of_lt (lt_of_le_of_lt z_le_w w_lt_z),
    exact lt_irrefl z z_irrefl,
  --w∈ By → w∈ Az
    intro hw,--suposem que w∉A
    have w_in_A:w∈ A.val,by_contra w_notin_A,
      --aleshores w∉A↓x
      have w_notin_Ax:w∉Ax, exact λ w_in_Ax, w_notin_A (mem_sep.mp w_in_Ax).left,
      --per tant w∈ B\A↓x
      have w_in_BlAx: w∈ (B.val\Ax), from mem_diff.mpr (and.intro (mem_sep.mp hw).left w_notin_Ax),
      --aleshores, per definició de y ≤ w
      have y_le_w:y≤⟨w, (B.2 (mem_sep.mp hw).left)⟩, from (ymin w w_in_BlAx),
      --però per hipòtesi w < y
      have w_lt_y:⟨w, (B.2 (mem_sep.mp hw).left)⟩ < y, cases (mem_cv.mp hw) with hw2 w_lt_y, exact vals_of_pieq_of_lt w_lt_y,
      --aleshores tenim que y < y
      have y_irrefl:y<y, from lt_of_le_of_lt y_le_w w_lt_y,
      exact lt_irrefl y y_irrefl,
    --Aleshores, si w∈ A només queda provar que w < z
    have w_lt_z:⟨w, (B.2 (mem_sep.mp hw).left)⟩<z, by_contra w_nlt_z,
      --Tenim que A és cadena, per ser conforme
      have hw_le, from confCad hA w z.1 w_in_A (mem_diff.mp hz).left,
      --primer vegem que w≠z
      have w_neq_z:w≠z.1, intro w_eq_z, 
        --aleshores z∈ By, 
        have z_in_By:z.1∈By, from mem_of_eq_of_mem w_eq_z hw,
        --però per hipòtesi z∉By
        exact (mem_diff.mp hz).right z_in_By,
      --ara suposem dos casos per ser A cadena : w ≤ z ∨ z ≤ w
      cases hw_le,
      -- w ≤ z --
        --aleshores w < z ∨ w=z però això no es pot donar
        have w_lt_z,from lt_or_eq_of_le hw_le, cases w_lt_z,
          exact w_nlt_z (vals_of_pieq_of_lt w_lt_z), exact w_neq_z (congr_arg subtype.val w_lt_z),
      -- z ≤ w
        --aleshores z < w ∨ z=w
        have z_lt_w,from lt_or_eq_of_le hw_le, cases z_lt_w,
        --si z < w, pel lema B1, obtenim que z∈ By
        have w_in_By:⟨w, (B.2 (mem_sep.mp hw).left)⟩.val ∈ By, from hw,
        have z_in_By:z.1∈ By, from LB1 (mem_diff.mp hz).left w_in_By (vals_of_lt_of_pieq z_lt_w),
        --però per definició z∉ By
        exact (mem_diff.mp hz).right z_in_By,
        --si z = w → w = z
        exact w_neq_z (congr_arg subtype.val z_lt_w.symm),
    --Aleshores ja tenim tot el que necessitàvem
    exact mem_cv.mpr (exists.intro w_in_A (vals_of_pieq_of_lt_iff.mpr w_lt_z)),
  --Només queda demostrar que z=y
  have z_eq_y1:z=y,
    --com Az=By tenim que (phi (Az) (Cv_ss_P)) = (phi (Az) (Cv_ss_P))
    have Az_eq_By1:(phi (Az) (Cv_ss_P)) = (phi (By) (Cv_ss_P)), 
      have Az2:(phi (Az) (Cv_ss_P)).val = Az , from phieq_val Cv_ss_P,
      have By2:(phi (By) (Cv_ss_P)).val = By , from phieq_val Cv_ss_P,
      have Az_eq_By1_val:(phi (Az) (Cv_ss_P)).val=(phi (By) (Cv_ss_P)).val, from ( calc
      (phi (Az) (Cv_ss_P)).val  = Az :Az2
      ...                       = By :LB2
      ...                       = (phi (By) (Cv_ss_P)).val : By2.symm
      ),
      exact subtype.eq Az_eq_By1_val,
    have UppAz_eq_UppBy:Upp (phi (Az) (Cv_ss_P)) = Upp (phi (By) (Cv_ss_P)), exact congr_arg Upp Az_eq_By1,
    --Ara, demostrem que Upp (phi (Az) (Cv_ss_P))∈ ℂ P
    have Az_chain: is_chain (phi (Az) (Cv_ss_P)), 
      --com que A és conforme, aleshores és cadena 
      have hCadA:is_chain A, from confCad hA,
      --per tant, A↓x és cadena
      exact cv_is_cad_of_cad hCadA,
    --Aleshores, com Az és cadena, Upp (Az)∈ ℂ P,
    have UppAz_in_C:Upp (phi (Az) (Cv_ss_P)) ∈ ℂ P, apply mem_sep.mpr,
      --Upp (phi (Az) (Cv_ss_P)) ⊆ P
      have hUpp_ss: Upp (phi (Az) (Cv_ss_P))⊆ P, from λ w hw, (mem_sep.mp hw).left,
      split, exact mem_powerset.mpr hUpp_ss,
      --∃ (C : ↥(Φ P)), is_chain C ∧ Upp (phi Az Cv_ss_P) = Upp C
      split, exact and.intro Az_chain rfl,
    --aleshores, com Az=By, tenim que Upp(By)∈ ℂ P
    have UppBy_in_C:Upp (phi (By) (Cv_ss_P))∈ ℂ P, from mem_of_eq_of_mem UppAz_eq_UppBy UppAz_in_C,
    --Com f està ben definida tenim que la imatge de Upp (Az) és única
    have funiq, from (mem_funs.mp fFunc).right (Upp (phi (Az) (Cv_ss_P))) UppAz_in_C, rcases funiq with ⟨w,hw, wuniq⟩,
    --Ara com, A és Conforme,  Upp (Az).pair z ∈ f
    have hz_in_f: (Upp (phi (Az) (Cv_ss_P))).pair z.1 ∈ f, from CC2 hA,
    --De manera anàlega tenim que Upp (By).pair y ∈ f
    have hBy_in_f: (Upp (phi (By) (Cv_ss_P))).pair y.1 ∈ f, from CC2 hB,
    --aleshores, com (Upp (phi (By) (Cv_ss_P))) = (Upp (phi (Az) (Cv_ss_P))) → (Upp (phi (Az) (Cv_ss_P))).pair y.1∈ f
    have hy_in_f: (Upp (phi (Az) (Cv_ss_P))).pair y.1 ∈ f, from mem_of_eq_of_mem_left UppAz_eq_UppBy.symm hBy_in_f,
    --aleshores w=z ∧ w=y
    have w_eq_z1: z.1 = w, from wuniq z.1 hz_in_f,
    have w_eq_y1:y.1 = w, from wuniq y.1 hy_in_f,
    have z_eq_w:z.1=y.1, from eq.trans w_eq_z1 w_eq_y1.symm,
    exact subtype.eq z_eq_w,
  --com x∈ A\B→ x∈ A\By
  have x_in_AlBy:x.1∈(A.1\By), from mem_diff.mpr (and.intro (mem_diff.mp hx).left x_notin_By),
  --aleshores, z ≤ x
  have z_le_x: z ≤ x, from vals_of_pieq_of_le (zmin x.1 x_in_AlBy),
  --aleshores y ≤ x, 
  have y_le_x: y ≤ x, exact (eq.symm z_eq_y1).trans_le z_le_x, 
  --per tant: y < x ∨ y = x 
  have y_lt_x, from lt_or_eq_of_le y_le_x, cases y_lt_x,
  --y < x--
    --tenim que y∈Ax
    have y_in_Ax:y.1 ∈ Ax, apply mem_cv.mpr,split,  exact lt_vals.mpr y_lt_x, exact mem_of_eq_of_mem (congr_arg subtype.val z_eq_y1) (mem_diff.mp hz).left,
    --el qual entra en contradicció per definició de y
    exact (mem_diff.mp hy).right y_in_Ax,
  --y = x--
    have x_in_B:x.1∈ B.1, from mem_of_eq_of_mem (congr_arg subtype.val y_lt_x) (mem_diff.mp hy).left,
    have hx2:x.1∉B.1, from (mem_diff.mp hx).right,
    exact hx2 x_in_B,
end

-------------------------------------------
--                 LEMA C                --
-------------------------------------------
lemma sUnion_A_in_P {P 𝔸:Set.{u}} (A_ss_PP:𝔸 ⊆ powerset P ):sUnion 𝔸 ⊆ P:=
begin
  intros y hy, rcases (mem_sUnion.mp hy) with ⟨z, hz, y_in_z⟩,
  have z_in_PP:z∈ P.powerset, from A_ss_PP hz,
  exact (mem_powerset.mp z_in_PP) y_in_z,
end

lemma LC {𝔸 f:Set.{u}}(fFunc:f∈ (ℂ P).funs (⋃₀ ℂ P))(A_ss_PP:𝔸 ⊆ powerset P )(h𝔸: ∀{A:Set.{u}}(hA:A∈𝔸), conforme f (phi A (mem_powerset.mp (A_ss_PP hA)))) (hne:Set_nonempty 𝔸 ):conforme f (phi (sUnion 𝔸) (sUnion_A_in_P A_ss_PP)):=
begin split,
--⊢ ⋃₀ 𝔸 nonempty
  --com 𝔸 no és buit, aleshores existeix un A∈ 𝔸, i com que, A és conforme per ser element de 𝔸, aleshores ∃a∈ A
  cases hne with A hA, cases (h𝔸 hA).C0 with a ha,
  --aleshores a∈ ⋃₀𝔸 
  split,exact mem_sUnion.mpr (exists.intro A (exists.intro hA ha)),
--⊢ ∀ (X : Set) (hss : X ⊆ (phi (⋃₀ 𝔸) _).val), Set_nonempty X → (∃ (x : ↥(P.to_set)) (hx : x.val ∈ X), minim_of_set (phi X _) x hx)
  intros X hss Xne, 
  --com X no és buit, ∃a∈ X
  cases Xne with a ha,
  --aleshores, com a∈ sUnion 𝔸, existeix A∈ 𝔸, a∈ A i A és conforme
  rcases (mem_sUnion.mp (hss ha)) with ⟨ A, hA, a_in_A⟩,
  have hAconf,from h𝔸 hA,
  --aleshores tenim que X∩A ⊆ A i no és buit
  have XcapA_ss_A: X∩A ⊆ A, from subset_of_inter_right,
  have XcapAne:Set_nonempty (X∩A),split, exact mem_inter.mpr (and.intro ha a_in_A),
  --aleshores per la propietat C1 de conforme i ser A conforme tenim que té buit
  rcases (CC1 hAconf XcapA_ss_A XcapAne) with ⟨z,hz,zmin ⟩, split,split,
  --demostrem que z és el mínim de X
  intros b hb,
  --suposem que b∈ A
  by_cases b_in_A:b∈ A, exact zmin b (mem_inter.mpr (and.intro hb b_in_A)),
  --suposem ara que b∉A, aleshores, existeix un B∈𝔸 ,B conforme i B\A no és buit
  rcases (mem_sUnion.mp (hss hb)) with ⟨B,hB,b_in_B⟩,
  have hBconf, from h𝔸 hB,
  have b_in_BlA,from mem_diff.mpr (and.intro b_in_B b_in_A),
  have BlAne:Set_nonempty (B\A), split, exact b_in_BlA,
  --aleshores, pel lema B, obtenim que existeix un x minim de B\A
  rcases (LB fFunc hBconf hAconf BlAne) with ⟨x,hx,A_eq_Bx,xmin⟩,
  --aleshores, com z∈ A=Bx → z < x ≤ b
  have x_le_b, from xmin b b_in_BlA,
  have z_in_Bx, from mem_of_eq_of_set A_eq_Bx (mem_inter.mp hz).right,
  cases (mem_cv.mp z_in_Bx) with z_in_B z_lt_x,
  have z_le_x, from vals_of_le_of_pieq (le_of_lt z_lt_x),
  exact le_trans z_le_x x_le_b,
  exact (mem_inter.mp hz).left,
--⊢ ∀ (x : Set) (hx : x ∈ (phi (⋃₀ 𝔸) _).val), (Upp (phi (phi (⋃₀ 𝔸) _↓hx) Cv_ss_P)).pair x ∈ f
  intros a ha, rcases (mem_sUnion.mp ha) with ⟨A,hA, a_in_A ⟩, 
  have A_ss_P:A⊆P, from mem_powerset.mp (A_ss_PP hA),
  have hAconf, from h𝔸 hA,
  have UA_ss_P:⋃₀𝔸⊆P, intros x hx,rcases (mem_sUnion.mp hx) with ⟨ Y,hY,x_in_Y ⟩, exact mem_powerset.mp (A_ss_PP hY) x_in_Y,
  --aleshores demostrem que A↓a = ⋃₀𝔸↓a
  have Aa_eq_U𝔸a:((phi A A_ss_P)↓a_in_A)=((phi (⋃₀𝔸) UA_ss_P)↓ha), ext x,split,
  --⊢ x ∈ (A↓a) → x ∈ ((⋃₀ 𝔸)↓a)
    intro hx, cases (mem_cv.mp hx) with x_in_A x_lt_a,
    --aleshores x_in_U₀𝔸 
    have x_in_UA:x∈ (⋃₀𝔸), from mem_sUnion.mpr (exists.intro A (exists.intro hA x_in_A)),  
    --per tant x_in_UA↓a
    exact mem_cv.mpr (exists.intro x_in_UA x_lt_a),
  --⊢ x ∈ ((⋃₀ 𝔸)↓a) → x ∈ (A↓a)
    intro hx, apply mem_cv.mpr,
    --com x ∈ ((⋃₀ 𝔸)↓a) → x∈ (⋃₀ 𝔸) ∧ x < a
    cases (mem_cv.mp hx) with x_in_UA x_lt_a, split, exact x_lt_a,
    --suposem que x∉A
    by_contra x_notin_A,
    --aleshores existeix un x∈ B∈𝔸, B conforme i B\A.nonempty
    rcases (mem_sUnion.mp x_in_UA) with ⟨ B, hB, x_in_B ⟩,
    have hBconf,from h𝔸 hB, 
    have x_in_BlA:x∈B\A, from mem_diff.mpr (and.intro x_in_B x_notin_A),
    have BlAne:Set_nonempty (B\A), split, exact x_in_BlA,
    --aleshores, pel lema B obtenim que existeix un z minim de B\A, tal que A=B↓z
    rcases (LB fFunc hBconf hAconf BlAne) with ⟨z, hz,A_eq_Bz ,zmin⟩,
    --aleshores com a∈ A, a < z
    have a_in_Bz, from mem_of_eq_of_set A_eq_Bz a_in_A,
    cases (mem_cv.mp a_in_Bz) with a_in_B a_lt_z,
    --també tenim que z ≤ x, per ser mínim
    have z_le_x, from zmin x x_in_BlA,
    --i per definició tenim que x< a pel que obtenim que a < a
    have a_irrefl, from lt_trans (lt_of_lt_of_le a_lt_z z_le_x) x_lt_a,
    exact lt_irrefl ⟨a, UA_ss_P ha⟩ a_irrefl,
  --Aleshores 
  have hAa_eq_UAa_phi:( phi ((phi A A_ss_P)↓a_in_A) Cv_ss_P) = ( phi ((phi (⋃₀𝔸) UA_ss_P)↓ha) Cv_ss_P), from subtype.eq Aa_eq_U𝔸a,
  have UppAa_eq_UppUAa:Upp ( phi ((phi A A_ss_P)↓a_in_A) Cv_ss_P) = Upp ( phi ((phi (⋃₀𝔸) UA_ss_P)↓ha) Cv_ss_P), from congr_arg Upp hAa_eq_UAa_phi,
  --Ara, com que A conforme aleshores A↓a és cadena
  have Acad:is_chain ( phi ((phi A A_ss_P)↓a_in_A) Cv_ss_P), from cv_is_cad_of_cad (confCad hAconf),
  --aleshores, com A és conforme, Upp Aa .pair a ∈ f
  have UppAa_in_f: (Upp ( phi ((phi A A_ss_P)↓a_in_A) Cv_ss_P)).pair a ∈ f, from CC2 hAconf,
  --també tenim que Upp UAa .pair a ∈ f, per la igualtat que hem demostrat abans
  exact mem_of_eq_of_mem_left UppAa_eq_UppUAa UppAa_in_f,
end

def 𝕂 (f:Set.{u}):Set.{u}:={A∈ powerset Q| ∃(h1:A⊆ Q), conforme f (phi A h1) }

lemma K_ss_P (f:Set.{u}):𝕂 Q f ⊆ powerset Q:= λ y hy, (mem_sep.mp hy).left

lemma Echain: is_chain (phi (∅:Set.{u}) (empty_subset P)):= λ a b ha, false.elim (not_mem_empty a ha)


lemma U𝕂conf (fFunc:f∈ (ℂ P).funs (⋃₀ ℂ P)): conforme f (phi (⋃₀(𝕂 P f)) (sUnion_A_in_P (K_ss_P P f))):=
begin
  --vegem que tot element de 𝕂 és conforme
  have h𝔸: ∀(A:Set.{u})(hA:A∈(𝕂 P f)), conforme f (phi A (mem_powerset.mp ((K_ss_P P f) hA))), 
    intros A hA,cases (mem_sep.mp hA).right with hA1 hA2, exact hA2,
  --vegem que 𝕂 no és buit 
  --com f és funció i Upp ∅ ∈ ℂ P, 
  have Kne:Set_nonempty (𝕂 P f),
    have UppE_in_C: Upp (phi (∅:Set.{u}) (empty_subset P)) ∈ ℂ P, 
      have UppE_ss_PP:Upp (phi (∅:Set.{u}) (empty_subset P))⊆ P, exact λ y hy, (mem_sep.mp hy).left,
      exact mem_sep.mpr (and.intro (mem_powerset.mpr UppE_ss_PP) (exists.intro (phi (∅:Set.{u}) (empty_subset P)) (and.intro Echain rfl))),
    --aleshores existeix la imatge de f upp ∅ = w 
    
    rcases ((mem_funs.mp fFunc).right (Upp (phi (∅:Set.{u}) (empty_subset P))) UppE_in_C) with ⟨w, hw, wuniq⟩, 
    --aleshores vegem que {w} és conforme, primer debem veure que w ∈ P
    have w_in_P:w∈ P, 
      --com (Upp (phi ∅ _)).pair w ∈ f ⊆ (ℂ P).prod (⋃₀ ℂ P) → w∈ (⋃₀ ℂ P) → ∃X∈ ℂ P, w∈ X⊆ P
      have w_in_UC:w∈ (⋃₀ ℂ P), from pair_mem_prod_right ((mem_funs.mp fFunc).left hw),
      rcases (mem_sUnion.mp w_in_UC) with ⟨X,hX,w_in_X ⟩,
      have X_ss_P:X ⊆ P, from mem_powerset.mp (mem_sep.mp hX).left,
      exact  X_ss_P w_in_X,
    --aleshores tenim que {w} és conforme
    have w_ss_P:{w}⊆ P, from mem_of_subsingleton_subset.mpr w_in_P,
    have wconf:conforme f (phi ({w}) w_ss_P),split,
    --⊢ Set_nonempty (phi {w} _).val
      split, exact mem_singleton.mpr rfl,
    --⊢ ∀ (X : Set) (hss : X ⊆ (phi {w} _).val), Set_nonempty X → (∃ (x : ↥(P.to_set)) (hx : x.val ∈ X), minim_of_set (phi X _) x hx)
      intros X hss Xne,
      cases Xne with x hx,
      have x_eq_w, from mem_singleton.mp (hss hx ),
      have x_in_P, from mem_of_eq_of_mem x_eq_w.symm w_in_P,
      have X_ss_P:X⊆ P, from λ y hy, w_ss_P (hss hy),
      have xmin:minim_of_set (phi X (X_ss_P)) ⟨x,x_in_P⟩ hx,
        intros z hz,
        --tenim que z∈ {w}
        have z_in_w:z=w, from mem_singleton.mp (hss hz),
        have z_in_P, from mem_of_eq_of_mem z_in_w.symm w_in_P,
        have x_in_w:x=w, from mem_singleton.mp (hss hx),
        have x_eq_z1:x=z, from eq.trans x_in_w z_in_w.symm,
        have x_eq_z:⟨x, x_in_P⟩ = ⟨z,z_in_P⟩, from subtype.eq x_eq_z1,
        exact le_of_eq x_eq_z,
      split,split, exact xmin,
    --⊢ ∀ (x : Set) (hx : x ∈ (phi {w} w_ss_P).val), (Upp (phi (phi {w} w_ss_P↓hx) Cv_ss_P)).pair x ∈ f
      intros x hx,
      have x_eq_w:x=w, from mem_singleton.mp hx,
      have ww_eq_E:  ((phi {w} w_ss_P)↓hx) = (∅:Set.{u}),
        ext z, split, 
        intro hz,
        --com z∈ {w}↓x tenim que z∈ w ∧ z < x
        cases  (mem_cv.mp hz) with z_in_w z_lt_x, 
        --aleshores z < x=w=z
        have x_in_P:x∈ P, from mem_of_eq_of_mem x_eq_w.symm w_in_P,
        have z_in_P:z∈ P, from mem_of_eq_of_mem (mem_singleton.mp z_in_w).symm w_in_P,
        have x_eq_z1:x=z, from eq.trans x_eq_w (mem_singleton.mp z_in_w).symm,
        have x_eq_z:⟨x,x_in_P⟩ = ⟨z,z_in_P⟩ ,from subtype.eq x_eq_z1,
        have x_irrefl:⟨x,x_in_P⟩ < ⟨x,x_in_P⟩ ,from lt_of_le_of_lt (le_of_eq x_eq_z) z_lt_x,
        exact false.elim (lt_irrefl ⟨x,x_in_P⟩ x_irrefl),
        exact λ h, false.elim (not_mem_empty z h),
      --aleshores com hem definit w=Upp (phi (∅:Set.{u}) (empty_subset P)) volem veure que açò és igual a (Upp (phi (phi {w} w_ss_P↓hx) Cv_ss_P))
      have E_eq_ww_v:(phi (∅:Set.{u}) (empty_subset P))=(phi (phi {w} w_ss_P↓hx) Cv_ss_P), from subtype.eq ww_eq_E.symm,
      have UppE_eq_Uppww:Upp (phi (∅:Set.{u}) (empty_subset P))=Upp (phi (phi {w} w_ss_P↓hx) Cv_ss_P), exact congr_arg Upp E_eq_ww_v,
      --ara com x=w i Upp ∅.pair w ∈ f, obtenim que Upp ∅.pair x ∈ f
      exact mem_of_eq_of_mem_right x_eq_w.symm (mem_of_eq_of_mem_left UppE_eq_Uppww hw),
    --aleshores tenim que {w} és conforme, pel que 𝕂 no és buit,
    split, exact mem_sep.mpr (and.intro (mem_powerset.mpr w_ss_P) (exists.intro w_ss_P wconf)),
  --aleshores, com 𝕂 no és buit estem en condicions de aplicar el lmea C i demostrar que ⋃₀𝕂 és conforme
  exact LC fFunc (K_ss_P P f) h𝔸 Kne,   
end

lemma Upp_ss_P (C: Φ P): Upp C ⊆ P:= λ y hy, (mem_sep.mp hy).left

lemma UK_ss_P: (sUnion (𝕂 P f))⊆ P:= λ y hy,sUnion_A_in_P (K_ss_P P f) hy

lemma kuUK_ss_P {k:Set.{u}}(k_in_P:k∈ P): ({k}∪(sUnion (𝕂 P f)))⊆ P:=
begin
  intros y hy,cases (mem_union.mp hy),
  exact mem_of_eq_of_mem (mem_singleton.mp h).symm k_in_P,
  exact UK_ss_P h,
end 

lemma eq_to_upp {A B:Set.{u}}(h1:A⊆P)(h2:B⊆ P)(hAB:A=B):Upp (phi A h1) = Upp (phi B h2):=
begin
  have hABP:(phi A h1)=(phi B h2), from subtype.eq hAB,
  exact congr_arg Upp hABP,
end


lemma kuUKconf (fFunc:f∈ (ℂ P).funs (⋃₀ ℂ P)) {k:Set.{u}}(k_in_P:k∈ P) (hk:∀ (y : Set) (hy : y ∈ (sUnion (𝕂 P f))), ⟨ y,(sUnion_A_in_P (K_ss_P P f)) hy ⟩ < ⟨k,k_in_P⟩) (hkf:(Upp (phi (⋃₀ 𝕂 P f) (sUnion_A_in_P (K_ss_P P f)))).pair k ∈ f): 
conforme f (phi ({k}∪(sUnion (𝕂 P f))) (kuUK_ss_P k_in_P)):=
begin split,
  --⊢ Set_nonempty ({k} ∪ ⋃₀ 𝕂 P f)
    --en primer lloc, com k∈ {k} tenim que no és buit
    split, exact mem_union.mpr (or.inl (mem_singleton.mpr rfl)),
  --⊢ ∀ (X : Set) (hss : X ⊆ (phi ({k} ∪ ⋃₀ 𝕂 P f) _).val), Set_nonempty X → (∃ (x : ↥(P.to_set)) (hx : x.val ∈ X), minim_of_set (phi X _) x hx)
    intros X hX Xne,
    --separem en dos cassos, X={k}, X ≠ {k}
    by_cases X_cap_UK_E:X∩(sUnion (𝕂 P f))=(∅:Set.{u}),
    --si X∩(sUnion (𝕂 P f))=(∅:Set.{u})--
      --aleshores tot element w de X, w∈ sUnion (𝕂 P f) → false
      have not_mem_X_UK:∀{y:Set.{u}}(hy:y∈X)(h:y∈sUnion (𝕂 P f)), false,
        intros y hy h, exact not_mem_empty y (mem_of_eq_of_set X_cap_UK_E (mem_inter.mpr (and.intro hy h))),
      split,split,intros w hw,
      --siga w∈ X, tenim que w∈{k} ∨ w∈ ⋃𝕂
      cases (mem_union.mp (hX hw)),
      --si w∈{k}
      have k_eq_w:k=w, from (mem_singleton.mp h).symm,
      have k_eq_wP:⟨k,k_in_P⟩=⟨w,(kuUK_ss_P k_in_P) (hX hw)⟩, from subtype.eq k_eq_w,
      exact le_of_eq k_eq_wP, swap,
      --com X no és buit, aleshores conté a k
      cases Xne with y hy, cases (mem_union.mp (hX hy)),
      exact mem_of_eq_of_mem (mem_singleton.mp h) hy,
      exact false.elim (not_mem_X_UK hy h),
      exact false.elim (not_mem_X_UK hw h),
    --si X∩(sUnion (𝕂 P f))≠(∅:Set.{u})--
      --aleshores, com (sUnion (𝕂 P f)) és conforme, tenim que existeix un mínim de X∩(sUnion (𝕂 P f)) 
      rcases (CC1 (U𝕂conf fFunc) (subset_of_inter_right) (nonempty_iff_notEmpty.mpr X_cap_UK_E)) with ⟨ z,hz,zmin ⟩,
      --vegem que aquest z és el mínim
      split,split,intros w hw, cases mem_union.mp (hX hw),
      --si w=k, aleshores z ≤ k per definició de k
      have z_lt_k, from hk z.val (mem_inter.mp hz).right,
      have w_in_P:w∈ P, from mem_of_eq_of_mem (mem_singleton.mp h).symm k_in_P,
      have k_eq_w:⟨k,k_in_P⟩ = ⟨w,w_in_P⟩, from subtype.eq (mem_singleton.mp h).symm,
      exact le_trans (le_of_lt z_lt_k) (le_of_eq k_eq_w),
      --si w∈ UK aleshores per def de z tenim que és minim
      have z_le_w,from (zmin w (mem_inter.mpr (and.intro hw h))),
      exact le_trans (le_of_eq pieq) z_le_w,
      --i vegem que z∈X
      exact (mem_inter.mp hz).left,

  --⊢ ∀ (x : Set) (hx : x ∈ (phi ({k} ∪ ⋃₀ 𝕂 P f) _).val), (Upp (phi (phi ({k} ∪ ⋃₀ 𝕂 P f) _↓hx) Cv_ss_P)).pair x ∈ f
  set UK:=⋃₀ 𝕂 P f,
  intros x hx,
  cases (mem_union.mp hx),
  --si x=k--
    --tenim que x∈ P
    have x_in_P:x∈P, from (kuUK_ss_P k_in_P) hx,
    --tenim que ({k} ∪ ⋃₀ 𝕂 P f) _↓hx) = ⋃₀ 𝕂 P f
    have kuUK_eq_UK:((phi ({k} ∪ UK) (kuUK_ss_P k_in_P))↓hx) = UK, ext w,split,
    --w ∈ (phi ({k} ∪ UK) _↓hx) → w ∈ UK
      intro hw, cases (mem_cv.mp hw) with w_in_kuUK w_lt_x,
      --com w∈ ({k} ∪ UK) o bé w=k o w∈ Uk
      cases mem_union.mp w_in_kuUK with w_in_k w_in_UK,
      --si w∈{k} aleshores, com k=x obtenim que x=w
      have x_eq_w:x=w, from eq.trans (mem_singleton.mp h) (mem_singleton.mp w_in_k).symm,
      have x_eq_wP:⟨x,x_in_P⟩ =  ⟨w,(kuUK_ss_P k_in_P) w_in_kuUK ⟩,from subtype.eq x_eq_w,
      --aleshores x < x
      have x_irrefl:⟨x,x_in_P⟩ < ⟨x,x_in_P⟩, from lt_of_le_of_lt (le_of_eq x_eq_wP) w_lt_x,
      exact false.elim (lt_irrefl ⟨x,x_in_P⟩ x_irrefl),
      --si w∈ UK ja ho tenim
      exact  w_in_UK,
    --w ∈ UK → w ∈ (phi ({k} ∪ UK) _↓hx)
      intro hw,
      --com w∈ UK, aleshores w< k = x 
      have k_eq_xP:⟨k,k_in_P⟩ = ⟨ x,x_in_P⟩, from subtype.eq (mem_singleton.mp h).symm,
      have w_lt_x:⟨w,UK_ss_P hw⟩ < ⟨x,x_in_P⟩ , from lt_of_lt_of_le (hk w hw) (le_of_eq k_eq_xP),
      exact mem_cv.mpr (exists.intro (subset_union_right hw) w_lt_x),
    --Aleshores com {k}∪(UK)x= UK → Upp ({k}∪(UK)x)= Upp (UK), tenim que Upp {k}∪(UK) .pair k ∈ f per hkf
    have kuUK_eq_UKP: Upp (phi ((phi ({k} ∪ UK) (kuUK_ss_P k_in_P))↓hx) Cv_ss_P) = Upp (phi UK UK_ss_P), from eq_to_upp Cv_ss_P UK_ss_P kuUK_eq_UK,
    have UppkuUk_k_in_f, from mem_of_eq_of_mem_left kuUK_eq_UKP.symm hkf,
    --i com x = k obtenim el que voliem
    exact mem_of_eq_of_mem_right (mem_singleton.mp h).symm UppkuUk_k_in_f,
  --si x ∈ UK--
    --en este cas provem que {k}∪⋃K↓x= ⋃K↓x
    have kuUKx_eq_UKx:((phi ({k} ∪ UK) (kuUK_ss_P k_in_P))↓hx) = ((phi UK UK_ss_P)↓h),ext w,split,
    --w ∈ (phi ({k} ∪ UK) _↓hx) → w ∈ (phi UK UK_ss_P↓h)
      intro hw,cases (mem_cv.mp hw) with w_in_kuUK w_lt_x, cases (mem_union.mp w_in_kuUK),
      --w=k--
        --tenim que w < x < k = w
        have x_lt_k,from hk x h,
        have w_in_P:w∈ P, from mem_of_eq_of_mem (mem_singleton.mp h_1).symm k_in_P,
        have w_eq_kP:⟨w,w_in_P⟩ = ⟨k,k_in_P ⟩, from subtype.eq  (mem_singleton.mp h_1),
        have w_irrefl:⟨w,w_in_P⟩ < ⟨w,w_in_P⟩, from lt_trans w_lt_x (lt_of_lt_of_le x_lt_k (le_of_eq w_eq_kP.symm)),
        exact false.elim (lt_irrefl ⟨w,w_in_P⟩ w_irrefl),
      --w∈⋃K↓x--
        apply mem_cv.mpr, split, exact w_lt_x, exact h_1,
    --w ∈ (phi UK UK_ss_P↓h) → w ∈ (phi ({k} ∪ UK) _↓hx)
      intro hw,cases (mem_cv.mp hw) with w_in_UK w_lt_x, exact mem_cv.mpr (exists.intro (mem_union.mpr (or.inr w_in_UK)) w_lt_x),
    --Aleshores, com UK és conforme tenim que Upp (UK↓x) .pair x ∈ f
    have UppkUKx_eq_UppUKx: Upp(phi ((phi ({k} ∪ UK) (kuUK_ss_P k_in_P))↓hx) Cv_ss_P) = Upp (phi ((phi UK UK_ss_P)↓h) Cv_ss_P), from eq_to_upp Cv_ss_P Cv_ss_P kuUKx_eq_UKx,
    have UppUKx_x_in_f:(Upp (phi ((phi UK UK_ss_P)↓h) Cv_ss_P)).pair x∈ f, from CC2 (U𝕂conf fFunc),
    exact mem_of_eq_of_mem_left  UppkUKx_eq_UppUKx.symm UppUKx_x_in_f,
end


  theorem AC_to_Zorn (AC_nd:AxiomOfChoice_noDisj.{u})(𝕏: Set.{u})(hpo: partial_order (𝕏.to_set)): preZorn 𝕏 hpo:=
  begin
    --Set_nonempty P ∧ ∀ (C : Set), C ∈ chains P → Set_nonempty C → (∃ (s : Set) (H : s ∈ P), ssuprem_deC)
    intro hprops,
    by_contra hnon_max, 
    --have AC_nd:AxiomOfChoice_noDisj, from AC_equiv_nodisj.mp AC,
    specialize AC_nd (ℂ 𝕏) (C_hasnt_E hprops.left hprops.right hnon_max),rcases AC_nd with ⟨F, Ffunc, CFF ⟩,
    --aleshores, pel lema U𝕂conf obtenim que ⋃𝕂 és conforme 
    have UK_ss_P, from (sUnion_A_in_P (K_ss_P 𝕏 F)),
    have UKconf:conforme F (phi (⋃₀(𝕂 𝕏 F)) UK_ss_P), from U𝕂conf Ffunc,
    --definim un acurtament per a Upp ⋃𝕂
    set UK:=(⋃₀ 𝕂 𝕏 F),
    set UppUK:=(Upp (phi UK UK_ss_P)),--(Upp (phi (⋃₀ 𝕂 𝕏 F) (sUnion_A_in_P (K_ss_P 𝕏 F))))
    --per tant Upp U𝕂 ∈ ℂ 𝕏, ja que al ser conforme, és cadena 

    have UK_in_C:UppUK∈ ℂ 𝕏, 
      apply mem_sep.mpr, split, exact mem_powerset.mpr (Upp_ss_P (phi (⋃₀(𝕂 𝕏 F)) (sUnion_A_in_P (K_ss_P 𝕏 F)))),split,split, 
      exact confCad UKconf, exact rfl,
    --aleshores, com F és funció, existeix un k tal que Upp (phi (⋃₀(𝕂 𝕏 F)) UK_ss_P).pair k ∈ F
    rcases (mem_funs.mp Ffunc).right (UppUK) UK_in_C with ⟨k, hk,kuniq ⟩ ,
    --aleshores com que F és funció d'elecció, tenim que k∈ Upp(⋃₀(𝕂))
    have k_in_UppUK:k ∈ UppUK, from CFF UppUK k hk,
    --per tant kUppUK := ∀x∈ U𝕂, x < k
    cases (mem_sep.mp k_in_UppUK).right with k_in_𝕏 kUppUK,
    --per tant k∉U𝕂
    have k_notin_UK:k∉UK, 
      intro k_in_UK,
      --aleshores, k < k
      have k_irrefl: ⟨k,k_in_𝕏⟩ < ⟨k,k_in_𝕏⟩, from kUppUK k k_in_UK,
      exact lt_irrefl ⟨k,k_in_𝕏⟩ k_irrefl,
    -- Ara obtenim que {k}∪UK és conforme i per tant {k}∪UK∈ ℂ 𝕏
    have kuUK_in_K: ({k}∪ UK)∈ 𝕂 𝕏 F, apply mem_sep.mpr, split, exact mem_powerset.mpr (kuUK_ss_P k_in_𝕏),split, exact kuUKconf Ffunc k_in_𝕏 kUppUK hk,
    --aleshores, com k∈ ({k}∪ UK
    have k_in_kuUK:k∈ ({k}∪ UK), from mem_union.mpr (or.inl (mem_singleton.mpr rfl)),
    --tenim que k∈ U𝕂
    have k_in_UK:k∈ UK, from mem_sUnion.mpr (exists.intro ({k}∪ UK) (exists.intro kuUK_in_K k_in_kuUK)),
    --aleshores, comabans hem demostrat que k∉ UK arribem a una contradficció
    exact k_notin_UK k_in_UK,
  end
end preZorn






open preAC preZorn

theorem AC_eq_Zorn: AxiomOfChoice.{u} ↔ Zorn.{u}:=
begin split,
--AC_to_Zorn
  intros AC P hpo,
  exact AC_to_Zorn (AC_equiv_nodisj.mp AC) P hpo,
--Zorn_to_AC
  intros hzorn 𝕏 𝕏_props,
  exact zorn_to_AC hzorn 𝕏_props.left,
end

--podem observar que no es requereix la condició de que el conjunt de l'axioma d'elecció siga disjunt

theorem AC_nodisj_eq_Zorn: AxiomOfChoice_noDisj.{u} ↔ Zorn.{u}:=
begin split,
--AC_to_Zorn
  intros AC P hpo,
  exact AC_to_Zorn AC P hpo,
--Zorn_to_AC
  intros hzorn 𝕏 𝕏_props,
  exact zorn_to_AC hzorn 𝕏_props,
end