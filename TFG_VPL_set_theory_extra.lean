import  set_theory.zfc.basic data.set.basic --TFG_VPL_Axiom_of_Choice 
open  Set --AC_nodisj

universe u

variables {x y z t X Y Z T f g P: Set.{u}}
variables a b c A B  𝕏 Q: Set.{u}

lemma mem_of_eq_of_mem : x = y → x ∈ X → y ∈ X  := λ XeY,λ PX, XeY ▸ PX
lemma mem_of_eq_of_set : X = Y → x ∈ X → x ∈ Y := λ XeY,λ PX, XeY ▸ PX


namespace empty
  def Set_nonempty (X:Set.{u}):Prop:= ∃x:Set.{u}, x∈ X

  --X no és no buit sii X és buit
  lemma not_nonempty_iff_empty :¬ (Set_nonempty X) ↔ X = ∅ :=
  begin split,
    --¬ (Set_nonempty X) →  X = ∅ 
      intro Xnot_nonempty, apply ext, intro z, split,
        intro z_in_X, exact false.elim (Xnot_nonempty (exists.intro z z_in_X)), intro hz, exact false.elim (not_mem_empty z hz),
    --X = ∅ → ¬Set_nonempty X
    intros h1 h2,
    --donat un conjunt x, x∈ X → false
    have h3:∀x:Set.{u},x∈ X→false,
      intros x hx,
      --com X=∅ → x∈ ∅ 
      have h4:x∈ (∅:Set.{u}),from eq.subst h1 hx, 
      --hem arribat a una contradicció
      exact false.elim (not_mem_empty x h4),
    exact exists.elim h2 h3,
  end
  lemma nonempty_iff_notEmpty :Set_nonempty X ↔ X≠ (∅:Set.{u}):=
  begin split,
    intros Xne XE,cases Xne with x hx,exact not_mem_empty x (mem_of_eq_of_set XE hx),
    intros X_not_E, by_contra notXne, exact X_not_E (not_nonempty_iff_empty.mp notXne),
  end

  --Si ∅∉𝕏 i X∈𝕏 aleshores X.nonempty 
  lemma xne_of_XhasNoE_of_xinX {𝕏 X:Set.{u}}: (∅:Set.{u}) ∉ 𝕏 → X∈𝕏 → Set_nonempty X:=
  begin
    intros E_notin_𝕏 X_in_𝕏,
    by_contra h3,
    have X_eq_E:X=(∅:Set.{u}),from (not_nonempty_iff_empty).mp h3,
    --tenim que ∅∈𝕏
    have E_in_𝕏:(∅:Set.{u})∈ 𝕏,from mem_of_eq_of_mem X_eq_E X_in_𝕏,
    exact E_notin_𝕏 E_in_𝕏,
  end

end empty

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

namespace previs
  open empty

  lemma subset_prod_left (h1:X ⊆ Y) : X.prod Z ⊆ Y.prod Z:= 
  begin
    intros w hw, 
    have hw2, from mem_pair_sep.mp hw, 
    rcases hw2 with ⟨a,ha, hw2⟩,
    exact mem_pair_sep.mpr (exists.intro a (exists.intro (h1 ha) hw2)),
  end
  lemma subset_prod_right (h1:X ⊆ Y) : Z.prod X ⊆ Z.prod Y:= 
  begin
    intros w hw, 
    have hw2, from mem_pair_sep.mp hw, 
    rcases hw2 with ⟨a,ha,b,hb, hw2⟩,
    exact mem_pair_sep.mpr (exists.intro a (exists.intro ha (exists.intro b (exists.intro (h1 hb) hw2)))),
  end

  lemma subset_sUnion (h1:X ⊆ Y) : X.sUnion ⊆ Y.sUnion :=
  begin
    intros z hz,have hz, from mem_sUnion.mp hz, rcases hz with ⟨ Z,hZ ,hz⟩,
    exact  mem_sUnion.mpr (exists.intro Z (exists.intro (h1 hZ) hz)),
  end
  lemma eq_sUnion (h1:X = Y) : X.sUnion = Y.sUnion := h1 ▸ rfl 



  lemma subset_of_eq (h:X=Y):X ⊆ Y:= λ x hx,mem_of_eq_of_set h hx

  lemma subset_iff_eq : X = Y ↔ X ⊆ Y ∧ Y ⊆ X:=
  begin split,
    intro h, exact and.intro (subset_of_eq h) (subset_of_eq h.symm),
    intro h,apply ext, intro w,split, intro hw, exact h.left hw,intro hw, exact h.right hw,
  end


  lemma subset_trans (h1:X⊆Y)(h2:Y ⊆ Z):X⊆Z:= λ x hx, h2 (h1 hx)

  lemma eq_prod_subset_cross {X Y Z T:Set.{u}}(h1:X ⊆ Y)(h2:Z ⊆ T) :x∈ X.prod T → x∈ Y.prod Z → x∈ X.prod Z:=
  begin
    intros h3 h4,
    have h3, from mem_prod.mp h3,rcases h3 with ⟨a1, ha1,b1,hb1,h1 ⟩,
    have h4, from mem_prod.mp h4,rcases h4 with ⟨a2, ha2,b2,hb2,h2⟩,
    have h5, from pair_inj.mp (eq.trans h1.symm h2),
    have h6:x=a1.pair b2,from h5.right ▸ h1,
    exact mem_prod.mpr (exists.intro a1 (exists.intro ha1 (exists.intro b2 (exists.intro hb2 h6)))),
  end

  lemma subset_of_eq_of_subset {X Y Z :Set.{u}}(h1:X = Y)(h2:Y ⊆ Z):X ⊆ Z:= h1.symm ▸ h2

  lemma subset_of_subset_of_eq {X Y Z :Set.{u}}(h2:Z ⊆ X)(h1:X = Y):Z ⊆ Y:= h1 ▸ h2

  lemma subset_union_left :X⊆(X∪Z) :=(λ w hw , mem_union.mpr (or.inl hw))
  lemma subset_union_right :Z⊆(X∪Z) :=(λ w hw , mem_union.mpr (or.inr hw))

  lemma subset_of_union_of_subsets(h1:X⊆Y ) (h2:Z⊆Y ): X∪ Z⊆ Y:=
  begin
    intros w hw, have hw2,from (mem_union.mp hw), cases hw2,
    exact h1 hw2,exact h2 hw2,
  end

  lemma eq_of_subsets (h1:x⊆y)(h2:y⊆x):x=y:=
  begin
    ext z,split,
      intro hz,exact h1 hz,
      intro hz,exact h2 hz,
  end

  -------------------------------------------------------------------------------
  lemma mem_of_eq_of_mem_left (h1:x = z)(h2:x.pair y∈ X):z.pair y ∈ X:= h1 ▸ h2
  lemma mem_of_eq_of_mem_right (h1:y = z)(h2:x.pair y∈ X):x.pair z ∈ X:= h1 ▸ h2

  lemma pair_inj_right (h1:x.pair y = z.pair t):y = t:= (pair_inj.mp h1).right
  lemma pair_inj_left (h1:x.pair y = z.pair t):x = z:= (pair_inj.mp h1).left

  lemma pair_mem_prod_left (h1:x.pair y ∈  z.prod t): x∈ z:= (pair_mem_prod.mp h1).left
  lemma pair_mem_prod_right (h1:x.pair y ∈  z.prod t): y∈ t:= (pair_mem_prod.mp h1).right

  lemma diff_nonempty_of_subsetneq (h1:X⊆Y) (h2:X≠Y):(Y\X).nonempty:=
  begin
    by_contra h3,
    have h4:(Y\X)=(∅:Set.{u}), from not_nonempty_iff_empty.mp h3,
    have h5:Y⊆X, intros y hy,by_contra y_notin_X,
      --aleshores y ∈ ∅
      have h6:y∈Y\X, from mem_diff.mpr (and.intro hy y_notin_X),
      exact not_mem_empty y (mem_of_eq_of_set h4 h6),
    have h7:X=Y, from eq_of_subsets h1 h5,
    exact h2 h7,
  end

  lemma subset_of_singleton_of_mem (h1:x ∈ y):{x}⊆ y:=λ w hw, mem_of_eq_of_mem (mem_singleton.mp hw).symm h1

  lemma subset_prod_inj_mpr: X⊆Z → Y⊆ T → X.prod Y ⊆ Z.prod T :=
  begin 
    intros h1 h2, intros x hx, 
    rcases (mem_prod.mp hx) with ⟨a,ha,b,hb,hx2⟩,
    exact mem_prod.mpr (exists.intro a (exists.intro (h1 ha) (exists.intro b (exists.intro (h2 hb) hx2)))),
  end

  lemma subset_of_subset_of_union_left:(Y∪X ⊆ Y)→ X⊆ Y:=λ h1 x hx, h1 (mem_union.mpr (or.inr hx))

  lemma mem_of_subsingleton_subset: {x}⊆ y ↔ x ∈ y:=
  begin
    split,intro h,exact h (mem_singleton.mpr rfl), exact λ h,subset_of_singleton_of_mem h,
  end

  lemma dif_subset: (X\Y)⊆ X:=
  begin
    intros w hw,exact (mem_diff.mp hw).left,
  end

  lemma subset_of_inter_left: X∩Y ⊆ X := λ w hw, (mem_inter.mp hw).left
  lemma subset_of_inter_right: X∩Y ⊆ Y := λ w hw, (mem_inter.mp hw).right

end previs

------------------------------------------------------------------------------------------------------------------

namespace functions
-- `composició` de funcions i algunes propietats --
  section composition
    def comp (hf:f ∈ (Y.funs Z))(hg:g ∈ (X.funs Y)):Set.{u}:= {w∈ X.prod Z|∃x y z : Set.{u}, (x.pair y) ∈g ∧ (y.pair z)∈f ∧ w = x.pair z}
    notation x`∘∘`y := comp x y


    -- pair_sep (λ a c, ∃b:Set, (a,pair b)∈ g ∧ (b.pair c)∈ f)

    lemma comp_is_func (hf:f ∈ (Y.funs Z))(hg:g ∈ (X.funs Y)): (hf ∘∘ hg)∈X.funs Z:= 
    begin
      apply mem_sep.mpr,
      --primer demostrem que fs∘g està en (X × Z),
        have h1:(hf ∘∘ hg) ⊆ (X.prod Z),
          intros z hz, have h1,from mem_sep.mp hz, exact h1.left,
        split,
        exact mem_powerset.mpr h1,split,exact h1,
      --X.is_func Z (hf∘hg)
        --siga x∈ X
        intros x hx,
      --volem demostrar:∃! (w : Set), z.pair w ∈ hf∘hg 
        have hf0,from ((mem_sep.mp hf).right).left,
        have hg0,from ((mem_sep.mp hg).right).left,
        have hf1:∀ (z : Set), z ∈ Y → (∃! (w : Set), z.pair w ∈ f),from ((mem_sep.mp hf).right).right,
        have hg1:∀ (z : Set), z ∈ X → (∃! (w : Set), z.pair w ∈ g),from ((mem_sep.mp hg).right).right,
        --aleshores com x∈ X i g:X → Y aleshores existeix un unic y de Y tal que g x = y
        specialize hg1 x hx,cases hg1 with y hy, cases hy with x_y_in_g hy_uniq,
        --idem, com (x,y)∈f⊆ X × Y, tenim que y∈ Y
        have y_in_Y:y∈ Y,from (pair_mem_prod.mp (hg0 x_y_in_g)).right,
        --aleshores com y∈ Y i f:Y → Z aleshores existeix un unic z de Z tal que f y = z
        specialize hf1 y y_in_Y, cases hf1 with z hz, cases hz with y_z_in_f hz_uniq,
        --aleshores volem provar: x.pair z ∈ hf∘hg ∧ ∀ (y : Set), x.pair y ∈ hf∘hg → y = z
        split,swap, exact z,simp at *,split,
        --x.pair z ∈ hf∘hg
          apply mem_sep.mpr,split,
          --x.pair z ∈ X.prod Z, que és equivalent a x ∈ X i z ∈ Z
            apply pair_mem_prod.mpr,split, exact hx,
            --demostrem que z ∈ Z per (y,z)∈g⊆ Y × Z, tenim que z∈ Z
            exact (pair_mem_prod.mp (hf0 y_z_in_f)).right,
          --definició de f∘g
            exact exists.intro x (exists.intro y (exists.intro z (and.intro x_y_in_g (and.intro y_z_in_f rfl)))),
        --demostrem que està ben definida
          intros w x_w_in_fg,
          --demostrem que si (x,w)∈ f ∘ g aleshores w=z
          have hfg1,from (mem_sep.mp x_w_in_fg).right,
          --desglosem f∘ g tal que existeix un y0∈ Y tal que g(x)=y0 i f(y0)=w
          cases hfg1 with x0 hfg1, cases hfg1 with y0 hfg1, cases hfg1 with z0 hfg1,cases hfg1 with x0_y0_in_g hfg1, cases hfg1 with y0_z0_in_f hfg1,
          have x_eq_x0:x=x0,from (pair_inj.mp hfg1).left,
          --aleshores x.pair_y0 ∈ g, pel que y0 = y
          have x_y0_in_g:x.pair y0 ∈ g, from eq.subst x_eq_x0.symm x0_y0_in_g,
          have y0_eq_y: y0=y ,from hy_uniq y0 x_y0_in_g,
          --per tant y.pair w ∈ f, pel que w=z
          have z0_eq_w:z0=w,from (pair_inj.mp hfg1).right.symm,
          have y_z0_in_f:y.pair z0 ∈ f, from eq.subst y0_eq_y y0_z0_in_f,
          have z0_eq_z:z0=z, from hz_uniq z0 y_z0_in_f,
          exact eq.trans z0_eq_w.symm z0_eq_z,
    end
  end composition

-- `restricció` de funcions i algunes propietats --
  section restriction 
    open previs

    def restrict (hf:f∈ X.funs Y) (Z:Set.{u}):Set.{u}:={w∈ f|w∈ Z.prod Y}

    lemma restrict_subset (hf:f∈ X.funs Y) (Z:Set.{u}): restrict hf Z ⊆ f:= λ w hw, (mem_sep.mp hw).left

    lemma restrict_subset_of_subset (hf:f∈ X.funs Y) {Z T:Set.{u}} (h1:Z ⊆ T): restrict hf Z ⊆ restrict hf T:=
    begin
      intros z hz, have hz, from mem_sep.mp hz,
      exact mem_sep.mpr (and.intro hz.left (subset_prod_left h1 hz.right)),
    end

    lemma eq_restrict (hf:f∈ X.funs Y) {Z T:Set.{u}} (h1:Z = T): restrict hf Z = restrict hf T:= h1 ▸ rfl

    lemma restrict_equiv_subset1 (hg:g∈ Z.funs Z.sUnion) (hf:f∈ X.funs X.sUnion)(h1:X ⊆ Z):f = restrict hg X ↔ f ⊆ g:=
    begin split,
      intros restr w w_in_f,exact (mem_sep.mp (mem_of_eq_of_set restr w_in_f)).left,
      --f ⊆ g → f = restrict hg Z
      intro f_ss_g, apply ext, intro w,split, --w∈ f → w∈ restrict hg Z
        intro w_in_f, have w_in_g:w∈ g, from f_ss_g w_in_f,
        --aleshores demostrem que w∈ X.prod Z.sUnion donat que w∈ f⊆ X.prod X.sUnion
        have w_in_XUZ: w∈ X.prod Z.sUnion, from (subset_prod_right (subset_sUnion h1)) ((mem_sep.mp hf).right.left w_in_f),
        exact mem_sep.mpr (and.intro w_in_g w_in_XUZ),
        -- w∈ restrict hg Z → w∈ f
        intro w_in_gZ,
        --aleshores tenim que w∈ X.prod Z
        have w_in_XZ:w∈ X.prod Z.sUnion, from (mem_sep.mp w_in_gZ).right,
        --aleshores tenim que existeix un w1 i w2 tals que w1.pair w2∈ X.prod Z.sUnion
        have wcases, from mem_prod.mp w_in_XZ, rcases wcases with ⟨w1, hw1, w2, hw2,hw⟩, 
        --aleshores com w1∈ X, per def de f funció, tenim que ∀w1∈ X, ∃!x, (w1,x)∈ f
        have hx:∃!x, w1.pair x∈ f, from (mem_sep.mp hf).right.right w1 hw1,rcases hx with ⟨x,hx,xuniq⟩,
        --ara bé, com X⊆Z, tenim que w1 ∈ Z
        have w1_in_Z:w1∈Z, from h1 hw1,
        --aleshores per g ser funció, existeix un únic y tal que w1.pair y ∈ g
        have hy:∃!y, w1.pair y∈ g, from (mem_sep.mp hg).right.right w1 w1_in_Z,rcases hy with ⟨y,hy,yuniq⟩,
        --ara bé, com (w1,w2)∈ g, tenim que w = y
        have w_eq_y:w2=y, from yuniq w2 (mem_of_eq_of_mem hw (mem_sep.mp w_in_gZ).left),
        --de la mateixa manera tenim que x=y
        have x_eq_y:x=y, from yuniq x (f_ss_g hx),
        --aleshores obtenim que w1.pair w2 = w1.pair x ∈ f
        exact mem_of_eq_of_mem hw.symm (mem_of_eq_of_mem  (pair_inj.mpr (and.intro rfl (eq.trans x_eq_y w_eq_y.symm))) hx),
    end

  end restriction

-- funció `identitat` d'un conjunt
  section identitat
    def Id: Set.{u}:={x∈ A.prod A| ∃y:Set.{u}, y.pair y = x}

    --tenim que la identitat està ben definida
    lemma id_well_defined:(Id A) ∈ A.funs A:=
    begin
    have h1:Id A ∈ (A.prod A).powerset ∧ A.is_func A (Id A),
      have id_SS: (Id A)⊆ A.prod A, intros x hx,exact (mem_sep.mp hx).left,
      split,
      exact mem_powerset.mpr id_SS,
      --A.is_func A (id A)
      split, exact id_SS,
      --∀ (z : Set), z ∈ A → (∃! (w : Set), z.pair w ∈ id A)
      intros z hz,
      have zz_in_A:z.pair z∈ Id A,
        have zz_in_AA:z.pair z ∈A.prod A, from pair_mem_prod.mpr (and.intro hz hz),
        exact mem_sep.mpr (and.intro zz_in_AA (exists.intro z rfl)),
      split,split, exact zz_in_A,
      -- ∀ (y : Set), (λ (w : Set), z.pair w ∈ id A) y → y = z
        intros y hy,
        have hzy,from (mem_sep.mp hy).right, cases hzy with y1 hzy,
        --ara tenim que y = y1 = z
        have y_eq_y1_eq_z,from pair_inj.mp hzy,
        exact eq.trans y_eq_y1_eq_z.right.symm y_eq_y1_eq_z.left,
      exact mem_sep.mpr h1,
    end 
    lemma mem_Id: x∈X →  x.pair x∈ (Id X):=
    begin
      intro x_in_X,
      have h:x.pair x∈ X.prod X ∧ ∃y:Set.{u}, y.pair y = x.pair x,  split, exact pair_mem_prod.mpr (and.intro x_in_X x_in_X),
        exact exists.intro x rfl,
      exact mem_sep.mpr h,
    end
  end identitat
-- propietats de `funcions` varies --

  lemma func_subset_image {X Y Z f:Set.{u}}(hf: f ∈ X.funs Y)(hY:Y⊆ Z): f ∈ X.funs Z:=
  begin
    apply mem_sep.mpr,have hf1,from mem_sep.mp hf, cases hf1 with hf1 hf2,
    have fSS:f⊆ X.prod Z, intros z hz, 
      have z_in_XZ:z∈  X.prod Y, from mem_powerset.mp hf1 hz,
      have hz1,from mem_prod.mp z_in_XZ, cases hz1 with a hz1, cases hz1 with ha hz1, cases hz1 with b hz1, cases hz1 with hb hz1,
      have hz2:a.pair b ∈ X.prod Z, from pair_mem_prod.mpr (and.intro ha (hY hb)),
      exact mem_of_eq_of_mem hz1.symm hz2,  
    split, exact mem_powerset.mpr fSS, split, exact fSS,
    exact (mem_sep.mp hf).right.right,
  end

end functions

--  exact congr_arg subtype.val h1

namespace order
open set
variables {Ω:Type}(j:Ω)
variables {R:set Ω}{l k s:R}[partial_order R]
--lemma lt_of_le_of_lt
/-
lemma l1: j.1=k.1→ j=k:= λ h,subtype.eq h

lemma l2(h1:l ≤ k) (h2:j=l): j ≤ k:= h2.trans_le h1

lemma l3 (h1:j = k): j.1=k.1:= congr_arg subtype.val h1
-/
lemma le_of_eq_of_le_down: l=s →  l ≤ k → s ≤ k:= λ h1 h2, h1 ▸ h2
lemma le_of_eq_of_le_up: k=s →  l ≤ k → l ≤ s:= λ h1 h2, h1 ▸ h2

#check partial_order



end order