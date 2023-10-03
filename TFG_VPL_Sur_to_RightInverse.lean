import TFG_VPL_Axiom_of_Choice TFG_VPL_set_theory_extra
open AC_nodisj Set empty previs functions

universe u
variables {x y z t X Y Z f g:Set.{u}}
variables a b c A B C : Set.{u}

#check AC_equiv_nodisj



-----------------------------------------------------------------------------------------
-- tota funció sobrejectiva té inversa per la dreta és equivalent a l'axioma d'elecció --
-----------------------------------------------------------------------------------------

---------------- Definicions prèvies ----------------------------------------------------
--Funció sobrejectiva
def is_surjective (hf: f∈ X.funs Y): Prop := ∀y∈Y, ∃x:Set.{u}, x.pair y ∈ f

--definim imatge d'una funció
def image (hf: f∈ X.funs Y) :Set.{u} →  Set.{u} :=λ x, {z∈Y| x.pair z ∈ f }.sUnion

--definim antiimatge d'una funció
def antiimage (hf: f∈ X.funs Y) (Z:Set.{u}):Set.{u} :={x∈ X| ∃y:Set.{u},y∈ Z ∧ x.pair y ∈ f}
notation hf⁻¹ Z:= antiimage hf Z

--definim la funció identitat



namespace Sur_to_RightInverse
--definim inversa per la dreta
def is_right_inverse (hf: f∈ X.funs Y) (hg: g∈ Y.funs X):Prop:=(hf ∘∘ hg) = Id Y

--definim si té inversa per la dreta
def has_right_inverse (hf: f∈ X.funs Y):Prop:= ∃(g:Set.{u})[hg: g∈ Y.funs X], is_right_inverse hf hg

----------------------------------------TEOREMA------------------------------------------
-- tota funció sobrejectiva té inversa per la dreta és equivalent a l'axioma d'elecció --
-----------------------------------------------------------------------------------------
theorem AC_equiv_sur_to_RInv: AxiomOfChoice.{u}↔ ∀{X Y f:Set.{u}}(hf:f∈ X.funs Y), is_surjective hf → has_right_inverse hf:=
begin split,
--AxiomOfChoice → ∀ (X Y f : Set) (hf : f ∈ X.funs Y), is_surjective hf → has_right_inverse hf
  intros AC X Y f hf fSurj,
  set 𝕏:Set.{u}:={Z∈powerset X | ∃ y:Set.{u}, y∈Y ∧  Z =  hf⁻¹ {y} },
  --provem que ∅∉𝕏
  have E_notin_𝕏:(∅:Set.{u})∉ 𝕏, assume E_in_𝕏,
    --com ∅∈ 𝕏, tenim que ∃ (y : Set), y ∈ Y ∧ ∅ = hf⁻¹{y}
    have hE𝕏,from (mem_sep.mp E_in_𝕏).right, cases hE𝕏 with y hy, 
    --com f és sobrejectiva tenim que f té preimatge no buida
    specialize fSurj y hy.left, cases fSurj with x hx, 
    --provem que x ∈ f⁻¹{y} 
    have finv_ne:x∈ hf⁻¹{y}, apply mem_sep.mpr,
      --ara com f:X→Y, x∈ X
      have hx2:x.pair y∈ X.prod Y,from mem_powerset.mp (mem_sep.mp hf).left hx,
      have hx3:x∈X, from (pair_mem_prod.mp hx2).left,split, exact hx3,
      exact exists.intro y (and.intro (mem_singleton.mpr rfl) hx),
    --ara com x∈ f⁻¹{y}=∅, és una contradicció
    exact not_mem_empty x (mem_of_eq_of_set hy.right.symm finv_ne),
  --podem aplicar l'axioma d'elecció sobre el conjunt 𝕏 -- 
  have AC_nodisj, from AC_equiv_nodisj.mp AC 𝕏 E_notin_𝕏, rcases AC_nodisj with ⟨F, hF, CFF⟩,
  --definim l'aplicació G:Y→ 𝕏; G(y) = f⁻¹{y}
  set G:Set.{u}:={Z∈ Y.prod 𝕏 |∃y:Set.{u}, Z = (y.pair hf⁻¹{y})},
  --vegem que està ben definida G
  have hG:G∈ Y.funs 𝕏, apply mem_sep.mpr,
    have G_SS:G ⊆ Y.prod 𝕏, intros w hw, exact (mem_sep.mp hw).left,
    split, exact mem_powerset.mpr G_SS, split, exact G_SS,
    intros y hy,
    have finv: (hf⁻¹{y})∈ 𝕏, apply mem_sep.mpr, 
    have finvSS: (hf⁻¹{y})⊆ X, intros w hw, exact (mem_sep.mp hw).left, 
    split, exact mem_powerset.mpr finvSS,
    exact exists.intro y (and.intro hy rfl),
    have yfinvy_in_G:y.pair (hf⁻¹{y}) ∈ G,
      apply mem_sep.mpr,split, exact pair_mem_prod.mpr (and.intro hy finv),
      exact exists.intro y rfl,
    split, split, exact yfinvy_in_G,
    --∀ (y_1 : Set), (λ (w : Set), y.pair w ∈ G) y_1 → (y_1 = hf⁻¹{y})
      intros z hz,
      have hz1,from (mem_sep.mp hz).right,
      cases hz1 with y1 hy1,
      --tenim que y=y1 ∧ z=f⁻¹{y1}
      have hy2:y=y1 ∧ z=hf⁻¹{y1},from pair_inj.mp hy1,
      exact hy2.left.symm ▸ hy2.right,
  --primer tenim que demostrar que la imatge de F està en X
  have hF2:F∈ 𝕏.funs X,
    have hXU_ss_X: 𝕏.sUnion ⊆ X, intros z hz, have hz1,from mem_sUnion.mp hz, cases hz1 with w hw, cases hw with hw hw2,
      have hw3,from mem_powerset.mp (mem_sep.mp hw).left, exact hw3 hw2,
    exact func_subset_image hF hXU_ss_X,
  --definim g=F∘G
  set g:= (hF2 ∘∘ hG),
  have hg: g∈ Y.funs X, from comp_is_func hF2 hG,
  --demostrem que g és la inversa per la dreta de f
  have RIfg:is_right_inverse hf hg, apply ext, intro z, split,
  --z ∈ hf∘hg → z ∈ id Y
    intro hz, apply mem_sep.mpr,split, 
    --z ∈ Y.prod Y
      exact (mem_sep.mp hz).left,
    --∃ (y : Set), y.pair y = z
      --aleshores, com z∈ f∘g, tenim que existeixen a b c / (a,b)∈g ∧ (b,c)∈ f ∧ (a,c) = z
      have hz1,from (mem_sep.mp hz).right, cases hz1 with a hz1, cases hz1 with b hz1, cases hz1 with c hz1,
      --(a,b)∈g → ∃ a0 ab b0 / (a0,ab)∈ G ∧ (ab,b0)∈ F ∧ (a,b)=(a0,b0)
      have hz2,from (mem_sep.mp hz1.left).right, cases hz2 with a0 hz2, cases hz2 with ab hz2, cases hz2 with b0 hz2,
      --(a0,ab)∈G→ ∃ a1 / (a0,ab)=(a1,f⁻¹{a1})
      have hz3,from (mem_sep.mp hz2.left).right, cases hz3 with a1 hz3,
      --ara com (ab,b0)∈ F, t F és funció d'elecció, tenim que b0∈ ab
      have hz4:b0 ∈ ab, from CFF ab b0 hz2.right.left,
      --aleshores b0 ∈ ab = f⁻¹{a1}
      have hz5:b0 ∈ hf⁻¹ {a1}, from mem_of_eq_of_set (pair_inj.mp hz3).right hz4,
      --ara, com tenim que b0 ∈ f⁻¹{a1} tenim que ∃ c1, c1∈ {a1} ∧ (b0,c1) ∈ f
      have hz6,from (mem_sep.mp hz5).right, cases hz6 with c1 hz6,
      --ara com que b0 = b i (b,c)∈ f,  (b0, c)∈ f
      have hz7:b0.pair c ∈ f, from eq.subst (pair_inj.mp hz2.right.right).right hz1.right.left,
      --ara com (b0,c1) ∈ f → b0∈ X, tenim que ∃! c0, (b0,c0)∈ f, es a dir ∀w, (b0,w)∈ f → w = c0 
      have hz8, from (mem_sep.mp hf).right.right b0 (pair_mem_prod.mp ((mem_sep.mp hf).right.left hz7)).left, cases hz8 with c0 hz8,
      --com (b0,c1) ∈ f i (b0,c)∈ f tenim que c1 = c0 = c
      have hz9:c1=c,from eq.trans (hz8.right c1 hz6.right) (hz8.right c hz7).symm,
      --aleshores com c1∈ {a1}, tenim que c = c1 = a1 = a0 = a
      have c_eq_a:c = a, exact (calc
        c   = c1 : hz9.symm
        ... = a1 : mem_singleton.mp hz6.left
        ... = a0 : (pair_inj.mp hz3).left.symm
        ... = a  : (pair_inj.mp hz2.right.right).left.symm
      ),
      have ac_eq_aa:a.pair c = a.pair a, from eq.subst c_eq_a rfl,
      have z_eq_aa:z = a.pair a, from eq.trans hz1.right.right ac_eq_aa,
      exact exists.intro a z_eq_aa.symm,
  --z ∈ id Y → z ∈ hf∘hg
    intro hz, --apply mem_sep.mpr,
    have hz0:z ∈ Y.prod Y ∧ ∃ (x y z_1 : Set), x.pair y ∈ g ∧ y.pair z_1 ∈ f ∧ z = x.pair z_1,split,
      exact (mem_sep.mp hz).left,
      --aleshores tenim que z∈Y.prod Y ∧  ∃y, y.pair y = z
      have hz1, from mem_sep.mp hz, cases hz1.right with y hy,
      --primer que tot, com (y, y)∈ Y.prod Y, tenim que y∈ Y, 
      --aleshores ∃ b, (y, b) ∈ g ∧ ∀b0∈ Y, (y,b0)∈ g → b0=b 
      have hz2, from (mem_sep.mp hg).right.right y (pair_mem_prod.mp (mem_of_eq_of_mem hy.symm (mem_sep.mp hz).left)).left, cases hz2 with b hz2,
      --aleshores tenim que (b,y)∈ f i (y,y)=z, 
      split,split,split,split, exact hz2.left,split, swap, exact hy.symm,
      --només queda demostrar que (y,b)∈ g--
        --ara, com y.pair b∈ g = F ∘ G, tenim que ∃ a0 ab0 b0, (a0,ab0)∈ G ∧ (ab0,b0)∈ F ∧ a0.pair b0 = y.pair b 
        have hz3, from (mem_sep.mp hz2.left).right, cases hz3 with a0 hz3, cases hz3 with ab0 hz3, cases hz3 with b0 hz3,
        --on tenim que ab0=f⁻¹{a0}, per ser f⁻¹{a0}=G(a0)=ab0
        have hz4:ab0 = (hf⁻¹{a0}), 
          --com (a0,ab0) ∈ G, alehsores ∃ a1, (a0,ab0)=(a1, hf⁻¹{a1})
          have hG2, from (mem_sep.mp hz3.left).right, cases hG2 with a1 hG2, 
          exact eq.subst (pair_inj.mp hG2).left.symm (pair_inj.mp hG2).right,
        --per tant, com (ab0,b0)∈ F i F d'elecció b0 ∈ ab0 = hf⁻¹{a0}
        have hz5: b0∈ hf⁻¹{a0}, from mem_of_eq_of_set hz4 (CFF ab0 b0 hz3.right.left),
        --aleshores (b0,a0)∈ f,
        have hz6: b0.pair a0 ∈ f,
          --ja que  b0 ∈ hf⁻¹{a0} → ∃(a2:Set.{u}),a2∈ {a0} ∧  b0.pair a2 ∈ f
          have hf2, from (mem_sep.mp hz5).right, cases hf2 with a2 hf2, 
          exact eq.subst (mem_singleton.mp hf2.left) hf2.right,
        --ara, com a0=y b0=b, obtenim que (b,y)=(b0,a0)∈ f
        exact mem_of_eq_of_mem (pair_inj.mpr (and.symm (pair_inj.mp hz3.right.right))).symm hz6,
    --aleshores ja hem obtés que g és invers aper la dreta de f
    exact mem_sep.mpr hz0,
  --i per tant f té inversa per la dreta
  exact exists.intro g (exists.intro hg RIfg),
--(∀ {X Y f : Set} (hf : f ∈ X.funs Y), is_surjective hf → has_right_inverse hf) → AxiomOfChoice
  intros h_sur_to_Rinv 𝕏 𝕏.props,
  --tenim que demostrar que existeix una funció d'elecció en 𝕏
  --definim la funció G:⋃𝕏→𝕏, tal que, a cada x∈ ⋃𝕏, li fa correspondre l'únic X∈ 𝕏, x∈ X
  set G: Set.{u} := {z∈ 𝕏.sUnion.prod 𝕏| ∃ x X:Set, x ∈ X ∧ z=x.pair X},
  --vegem que està ben definida
  have hG:G∈ 𝕏.sUnion.funs 𝕏, apply mem_sep.mpr,
    have Gss:G⊆(𝕏.sUnion.prod 𝕏), intros w hw, exact (mem_sep.mp hw).left, split, exact mem_powerset.mpr Gss, split, exact Gss,
    --⊢ ∀x, x∈ 𝕏.sUnion → ∃! X, (x,X)∈G
    intros x hx,
    --com x∈ 𝕏.sUnion aleshores ∃X, X∈ 𝕏 ∧ x∈ X
    have hX, from mem_sUnion.mp hx, cases hX with X hX, cases hX with hX x_in_X,
    --aleshores (x,X)∈ G
    have xX_in_G:x.pair X ∈ G, apply mem_sep.mpr,split,
      --⊢ x.pair X ∈  ⋃𝕏 × 𝕏
      exact pair_mem_prod.mpr (and.intro hx hX),
      --⊢ ∃ x1 X1:Set, x1 ∈ X1 ∧ x.pair X=x1.pair X1
      exact exists.intro x (exists.intro X (and.intro x_in_X rfl)),
    split,split, exact xX_in_G,
    --⊢ ∀Y, (x,Y)∈G → Y=X 
    intros Y hYG,
    --tenim que Y∈ 𝕏 ja que és imatge de G
    have hY:Y∈ 𝕏, from (pair_mem_prod.mp (mem_sep.mp hYG).left).right,
    --com X Y ∈ 𝕏 i Disj (𝕏), aleshores X=Y ∨ X∩Y = ∅ 
    have hXY,from 𝕏.props.right X hX Y hY,
    --suposem que X∩Y és buida
    cases hXY,
      --tenim que x∈ X∩Y, ja que Y=G(x) i x ∈ X
      have hxXY:x∈ X∩Y,
        --demostrem que x∈ Y
        have x_in_Y: x∈ Y, cases (mem_sep.mp hYG).right with x1 hY1, cases hY1 with X1 hY1,
          --com (x,Y)∈ G, ∃ x1 X1, x1∈ X1 ∧ (x,Y)=(x1,X1)→ x=x1∈ X1=Y
          exact mem_of_eq_of_mem (pair_inj.mp hY1.right).left.symm (mem_of_eq_of_set (pair_inj.mp hY1.right).right.symm hY1.left), 
        --aleshores tenim que x∈ X ∩ Y
        exact mem_inter.mpr (and.intro x_in_X x_in_Y),
      --aleshores x ∈ X∩Y = ∅
      exact false.elim (not_mem_empty x (mem_of_eq_of_set hXY hxXY)),
      --aleshores necessàriament X=Y
      exact hXY.symm,
  --Aleshores ja tenim ben definida G
  --Ara demostrem que G és sobrejectiva
  have hGsur:is_surjective hG,
    --⊢ siga X∈ 𝕏, demotrar que ∃x∈ X, (x,X)∈G 
    intros X hX, 
    --com X∉ 𝕏 i X∈ 𝕏, tenim que ∃x,x∈ X
    have hXne:Set_nonempty X, from xne_of_XhasNoE_of_xinX 𝕏.props.left hX, cases  hXne with x hx,
    --aleshores tenim que (x,X)∈ G, perque x∈ X
    have xX_in_G:x.pair X ∈ G,apply mem_sep.mpr, split, exact pair_mem_prod.mpr (and.intro (mem_sUnion.mpr (exists.intro X (exists.intro hX hx))) hX),
      --⊢ ∃ x X:Set, x ∈ X ∧ z=x.pair X
      exact exists.intro x (exists.intro X (and.intro hx rfl)),
    exact exists.intro x xX_in_G,
  --hem demostrat que és sobrejectiva, per tant, per hipòtesi, té una inversa per la dreta que nomenem F 
  have GRinv, from h_sur_to_Rinv hG hGsur, rcases GRinv with ⟨F, hF, hFRinv⟩,
  --demostrem que F és una funció d'elecció, siga X∈ 𝕏 i x∈ ⋃𝕏, (X,x)∈ F
  have CFF:ChoiceFunction F, intros X x Xx_in_F,
    --però, com que F és inversa per la dreta, aleshores X.pair X∈ id 𝕏= G ∘ F 
    have XX_in_GF:X.pair X ∈ (hG∘∘hF), from mem_of_eq_of_set hFRinv.symm (mem_Id (pair_mem_prod.mp ((mem_sep.mp hF).right.left Xx_in_F)).left),
    --∃X0 y X1, X0.pair y∈ F ∧ y.pair X1 ∈ G ∧ X0.pair X1 = X.pair X
    have hXX_in_GF, from (mem_sep.mp XX_in_GF).right, cases hXX_in_GF with X0 hXX_in_GF, cases hXX_in_GF with y hXX_in_GF, cases hXX_in_GF with X1 hXX_in_GF,
    --ara, com y∈ ⋃𝕏, ∃!Y, (y,Y)∈ G:= ∀(y,X)∈G, Y=X
    have hy, from (mem_sep.mp hG).right.right y (pair_mem_prod.mp ((mem_sep.mp hF).right.left hXX_in_GF.left)).right, cases hy with Y hy, cases hy with hy Yuniq,
    --a més, per definició de G, tenim que x∈Y
    have y_in_Y:y∈Y, 
      --∃ z Z, z∈ Z ∧ y.pair Y = z.pair Z 
      have hz,from (mem_sep.mp hy).right, cases hz with z hz, cases hz with Z hz,
      --aleshores y=z∈Z=Y
      exact mem_of_eq_of_mem (pair_inj.mp hz.right).left.symm (mem_of_eq_of_set (pair_inj.mp hz.right).right.symm hz.left),
    --Ara com y.pair X∈ G, tenim per estar ben definida G que Y=X
    have Y_eq_X: X=Y , from eq.trans (pair_inj.mp hXX_in_GF.right.right).right (Yuniq X1 hXX_in_GF.right.left),
    --Ara bé, provem que x=y per a aconseguir x = y ∈ Y = X
    --com F està ben definida obteinim que ∃!x0, (X,x0)∈ F
    have hx0F, from (mem_sep.mp hF).right.right X (pair_mem_prod.mp ((mem_sep.mp hF).right.left Xx_in_F)).left, cases hx0F with x0 hx0F,cases hx0F with hx0F x0uniq,
    --aleshores, com (X,x)∈ F, tenim que x=x0=y
    have x_eq_y:x=y,
      have x_eq_x0:x=x0, from (x0uniq x Xx_in_F),
      have y_eq_x0:y=x0, from x0uniq y (mem_of_eq_of_mem_left (pair_inj_left hXX_in_GF.right.right).symm hXX_in_GF.left),
      exact eq.trans x_eq_x0 y_eq_x0.symm,
    --obtenim que x = y ∈ Y = X
    exact mem_of_eq_of_mem x_eq_y.symm (mem_of_eq_of_set Y_eq_X.symm y_in_Y),
  --per tant ja hem demostrat que la funció és d'elecció
  exact exists.intro F (exists.intro hF CFF),
end

end Sur_to_RightInverse