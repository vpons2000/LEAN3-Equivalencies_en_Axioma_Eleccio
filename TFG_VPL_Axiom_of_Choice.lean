import set_theory.zfc.basic TFG_VPL_set_theory_extra
open Set previs functions empty

universe u
--variable Ω: Type
variables a b A B:Set.{u}
variables {x y X Y Z f g: Set.{u}}
variables {P:Set.{u} → Prop}(Q:Set.{u} → Prop)

#check x ∪ y 

#check ⋃₀ x
#check x ∩ y 
--def inter := {a∈x|a∈ y}


#print funs 
#print is_func

#check sInter

--en teoria de conjunts una funció `f` és un conjunt amb dos components tal que, si a∈ x, aleshores existeix un únic b∈ y tal que (x,y)∈ f

#check mem_sUnion
#check Set_nonempty

----------------------------- Definicions Axioma d'elecció -------------------------------------

def disjunts:= Set.inter a b = (∅:Set.{u})
def Disj: Prop:= ∀a b∈A, disjunts a b  ∨ a=b

--diguem que una funció `f` és d'elecció ti totes les imatges de f estàn en la seua antiimatge 
def ChoiceFunction (f:Set.{u}):Prop:= ∀(z w:Set.{u}), pair z w ∈ f → w ∈ z

--Axiom d'elecció
def AxiomOfChoice :Prop:=∀(𝕏:Set.{u}),((∅:Set) ∉ 𝕏 ) ∧ Disj 𝕏  → ∃f∈ 𝕏.funs 𝕏.sUnion, ChoiceFunction f

def AxiomOfChoice_noDisj :Prop:=∀(𝕏:Set.{u}),((∅:Set) ∉ 𝕏 ) → ∃f∈ 𝕏.funs 𝕏.sUnion, ChoiceFunction f

namespace AC_nodisj
------------------------------------------------------------------------------------------------
-----------------L'axioma d'elecció no depén de la condició de disjunt--------------------------
------------------------------------------------------------------------------------------------
theorem AC_equiv_nodisj:AxiomOfChoice.{u} ↔ AxiomOfChoice_noDisj.{u}:=
begin split,swap, assume AC 𝕏 hprops, exact AC 𝕏 hprops.left, 
  intros AC 𝕏 E_notin_𝕏,
  --definim el conjunt 𝕏𝕏 com a tots els conjunts en etiqueta
  set 𝕏𝕏:Set.{u}:= {XX∈ powerset(prod (𝕏.sUnion) 𝕏)|∃X∈ 𝕏, XX = prod X {X}},

  --definim la aplicació que a cada X li fa correspondre X× {X}
  set T:Set.{u}→ Set.{u}:= λ X, prod X {X},

  --demostrem les propietats necessàries per a aplicar l'AC
  have hpropAC:(∅:Set.{u})∉𝕏𝕏 ∧ Disj 𝕏𝕏, split,
  --∅ ∉ 𝕏𝕏
    intro hE,
    --si el buit està en 𝕏𝕏, aleshores existeix un X∈𝕏 tal que ∅=X×{X}
    have E_in_XX,from mem_sep.mp hE,cases E_in_XX.right with X hX,cases hX with hX E_eq_XX,
    --com X està en 𝕏, aleshores no és buit
    have Xne:Set_nonempty X, from xne_of_XhasNoE_of_xinX E_notin_𝕏 hX,
    cases Xne with x hx,
    --com x∈X,  x,X∈ XX
    have xX_in_XX:pair x X ∈ prod X ({X}:Set.{u}), 
      --tenim que x∈X i que X∈ {X}
      have X_in_singleton:X∈ ({X}:Set.{u}), exact mem_singleton.mpr rfl,
      exact mem_prod.mpr (exists.intro x (exists.intro hx (exists.intro X (exists.intro X_in_singleton rfl)))),
    --aleshores que (x,X)∈ ∅
    have xX_in_E: pair x X ∈ (∅:Set.{u}), from mem_of_eq_of_set E_eq_XX.symm xX_in_XX,
    --el qual és una contradicció perque el buit no té elements
    exact false.elim (not_mem_empty (pair x X) xX_in_E),
  --Disj 𝕏𝕏
    --siguen XX i YY conjunts de 𝕏𝕏,
    intros XX hXX0 YY hYY0, have hXX,from (mem_sep.mp hXX0).right,have hYY,from (mem_sep.mp hYY0).right,
    cases hXX with X hX, cases hX with hX hX2,
    cases hYY with Y hY, cases hY with hY hY2,
    --suposem que no són disjunts
    by_cases hdisj:disjunts XX YY, exact or.inl hdisj,
    --ara com XX ∩ YY són distints del buit per no ser disjunts hi ha un element z en comú
    have XXYY_ne:Set_nonempty (Set.inter XX YY), from  nonempty_iff_notEmpty.mpr hdisj, cases XXYY_ne with z hz0, have hz, from mem_sep.mp hz0,
    --ara, com z∈ XX, aleshores Z∈ Xprod {X}
    have z_in_XX:z ∈  X.prod {X}, from mem_of_eq_of_set hX2 hz.left,
    --per tant tenim que z=(a,b) tq a∈ X i b∈ {X}
    have h,from mem_prod.mp z_in_XX, cases h with a ha, cases ha with haX b, cases b with b hb,cases hb with hbX z_eq_ab,

    --ara de manera anàlega obtenim que (a,b)∈ Y × {Y}
    have ab_in_YY:a.pair b∈ Y.prod {Y},from mem_of_eq_of_mem z_eq_ab (mem_of_eq_of_set hY2 hz.right),
    --i per tant b∈ {Y}
    have h,from pair_mem_prod.mp ab_in_YY,cases h with haY hbY,
    --aleshores com b∈ {X} tenim qeu b=X i com b∈ {Y}, b=Y
    have b_eq_X:b=X,from mem_singleton.mp hbX,have b_eq_Y:b=Y, from mem_singleton.mp hbY,
    --per tant X=b=Y
    have X_eq_Y:X=Y,from eq.trans b_eq_X.symm b_eq_Y,
    --per tant X × {X} = Y × {Y}
    have XX_eq_YY:T X = T Y, from eq.subst X_eq_Y rfl,
    --provem que XX=YY
    exact or.inr (calc
      XX = X.prod {X}: hX2
      ... = Y.prod {Y}: XX_eq_YY
      ... = YY :hY2.symm
      ),
  --ja queden demostrades les propietats necessàries per a aplicar l'AC a 𝕏𝕏
  specialize AC 𝕏𝕏 hpropAC,
  --aleshores obtenim la funció d'elecció F:𝕏𝕏 → ⋃ 𝕏𝕏
  cases AC with F hF, cases hF with hF0 cfF,
  have hF, from mem_sep.mp hF0,cases hF with hF0b hF,
  --aleshores tenim que
  cases hF with hF1 hF2,
  --Definim l'aplicació que a cada X de 𝕏, li fa correspondre X × {X}
  set f:Set.{u}:={Z ∈ 𝕏.prod 𝕏𝕏.sUnion| ∃X Y:Set.{u}, (X.prod {X}).pair Y∈ F ∧ X.pair Y = Z},
  --demostrem que està ben definida
  have hf:f∈ 𝕏.funs 𝕏𝕏.sUnion,apply mem_sep.mpr,
  --tenim que f⊆ 𝕏.prod 𝕏𝕏
    have hf: f⊆ 𝕏.prod 𝕏𝕏.sUnion, intros w w_in_f, exact (mem_sep.mp w_in_f).left,split,exact mem_powerset.mpr hf,split, exact hf,
  --només cal demostrar quie està ben definida
    intros X hX,
    --com que F és una funció aleshores tenim que ∃!Y∈ ⋃𝕏𝕏 tq f X = Y
    have hXX:X.prod {X}∈𝕏𝕏, apply mem_sep.mpr,split,
    --X.prod {X} ∈ (𝕏.sUnion.prod 𝕏).powerset
      have hXX_in_𝕏𝕏:X.prod {X}⊆ 𝕏.sUnion.prod 𝕏,
        intros Z hZ,--Z ∈ 𝕏.sUnion.prod 𝕏
        apply mem_prod.mpr, have hZ2,from mem_prod.mp hZ,
        cases hZ2 with a hZ2, cases hZ2 with ha hZ2, cases hZ2 with b hZ2, cases hZ2 with hb hZ2,
        --aleshores tenim que a∈ ⋃𝕏
        have a_in_U𝕏:a∈ 𝕏.sUnion, exact mem_sUnion.mpr (exists.intro X (exists.intro hX ha)),
        -- també tenim que b=X
        have hbX:b=X,from mem_singleton.mp hb,
        --aleshores tenim que a,b∈ U𝕏 × 𝕏
        exact exists.intro a (exists.intro a_in_U𝕏 (exists.intro b (exists.intro (mem_of_eq_of_mem hbX.symm hX) hZ2))),
      exact mem_powerset.mpr hXX_in_𝕏𝕏,
      exact exists.intro X (exists.intro hX rfl),
    --demostrem que està ben definida
      --per a fer-ho, com hem demostrat que X.prod {X}∈𝕏𝕏, aleshores hi ha un Y tal que (X.prod {X}).pair Y∈ F
      have hY, from hF2 (X.prod {X}) hXX, cases hY with Y hY, cases hY with hY Yuniq,
      --tenim que (X,Y) ∈  f
      have XY_in_f:X.pair Y ∈ f, apply mem_sep.mpr,split, apply pair_mem_prod.mpr,
      --X ∈ 𝕏 ∧ Y ∈ 𝕏𝕏.sUnion
        split, exact hX, exact (pair_mem_prod.mp (hF1 hY)).right,
      --(X_1.prod {X_1}).pair Y_1 ∈ F ∧ X_1.pair Y_1 = X.pair Y
        exact exists.intro X (exists.intro Y (and.intro hY rfl)),
      split,split, exact XY_in_f, 
    --∀ (y : Set),  X.pair y ∈ f → y = Y
      intros Y0 hY0,--X.pair Y0 ∈ f
      have hY01,from (mem_sep.mp hY0).right, cases hY01 with X1 hY01, cases hY01 with Y1 hY01,
      --(X1.prod {X1}).pair Y1 ∈ F ∧ X1.pair Y1 = X.pair Y0 aleshores X1 = X i Y1 = Y
      have XY1_eq_XY0, from pair_inj.mp hY01.right,
      --(X.prod {X}).pair Y1 ∈ F
      have XXY_in_F:(λw:Set.{u},(w.prod {w}).pair Y1 ∈ F) X,from eq.subst (XY1_eq_XY0.left) hY01.left,
      --com (X.prod {X}).pair Y1 ∈ F → Y0 = Y1 = Y
      specialize Yuniq Y1 XXY_in_F, exact eq.trans XY1_eq_XY0.right.symm Yuniq,
  --ara definim e1 com l'aplicació que a cada element de 𝕏𝕏.sUnion → 𝕏.sUnion que agafa la primera component
  set e1:Set.{u}:={Z∈ 𝕏𝕏.sUnion.prod 𝕏.sUnion| ∃ X Y: Set.{u}, (X.pair Y).pair X = Z },
  --demostrem  que e1 està ben definida
  have he1:e1∈ 𝕏𝕏.sUnion.funs 𝕏.sUnion, apply mem_sep.mpr,
  --tenim que e1 ⊆  (𝕏𝕏.sUnion.prod 𝕏.sUnion)
    have e1_ssE:e1⊆ (𝕏𝕏.sUnion.prod 𝕏.sUnion), intros x hx, exact (mem_sep.mp hx).left, split, exact mem_powerset.mpr e1_ssE, split, exact e1_ssE,
  --∀ (z : Set), z ∈ 𝕏𝕏.sUnion → (∃! (w : Set), z.pair w ∈ e1)
    intros xx hxx,--siga xx∈ U𝕏𝕏, existeix un XX tq xx ∈ XX 
    have hxx0,from mem_sUnion.mp hxx,cases hxx0 with XX hxx0, cases hxx0 with hXX hxx0,
    --aleshores com XX∈ 𝕏𝕏, ∃X, XX = X.prod {X}
    have hXX2,from mem_sep.mp hXX,cases hXX2 with hXX2 hXX3, cases hXX3 with X hXX3, cases hXX3 with hX hXX3,
    --tenim que XX=X.prod {X} i per tant xx∈ X.prod {X} → ∃x∈ U𝕏, xx = (x,X),
    have xx_in_XX:xx∈ X.prod {X} ,from mem_of_eq_of_set hXX3 hxx0, 
    have hxx1,from mem_prod.mp xx_in_XX, cases hxx1 with x hxx1, cases hxx1 with hx hxx1, cases hxx1 with X_ hxx1, cases hxx1 with hX_ hxx1,
    --aleshores x.pair X ∈ 𝕏𝕏.sUnion i x∈ 𝕏.sUnion
    have xX_in_U𝕏𝕏: x.pair X_ ∈ 𝕏𝕏.sUnion,from eq.subst hxx1 hxx,
    have x_in_U𝕏:x∈ 𝕏.sUnion, from mem_sUnion.mpr (exists.intro X (exists.intro hX hx)),
    --vegem que xx.pair x ∈ e1 
    have xxx_in_e1: xx.pair x ∈ e1,
      have hxxx_in_e1: xx.pair x∈ 𝕏𝕏.sUnion.prod 𝕏.sUnion ∧ ∃ X Y: Set.{u}, (X.pair Y).pair X = (xx.pair x),split,
        --xx.pair x∈ 𝕏𝕏.sUnion.prod 𝕏.sUnion
        exact mem_prod.mpr (exists.intro xx (exists.intro hxx (exists.intro x (exists.intro x_in_U𝕏 rfl)))),
        --∃ X Y: Set.{u}, (X.pair Y).pair X = (xx.pair x)
        have xXx_eq_xxx:(x.pair X_).pair x = (xx.pair x),from eq.subst hxx1.symm rfl,
        exact exists.intro x (exists.intro X_ xXx_eq_xxx),
      exact mem_sep.mpr hxxx_in_e1,
    split,split, exact xxx_in_e1,
    --vegem que està ben definida: xx.pair w ∈ e1 → w = x
    intros w hw0, have hw,from (mem_sep.mp hw0).right,
    --com  xx.pair w ∈ e1, tenim que  ∃ A B: Set.{u}, (A.pair B).pair A = xx.pair w
    cases hw with A hw, cases hw with B hw,
    --aleshores A.pair B = xx ∧ A = w
    have AB_eq_xx_n_A_eq_w:A.pair B = xx ∧ A = w, from pair_inj.mp hw,
    --per tant A.pair B = x.pair X_ → w = A = x
    have A_eq_x:A=x, from (pair_inj.mp (eq.trans AB_eq_xx_n_A_eq_w.left hxx1)).left, exact eq.trans AB_eq_xx_n_A_eq_w.right.symm A_eq_x,
  --Ja tenim que e1 està ben definida
  --aleshores definim g = e1∘f
  set g: Set.{u} := (he1 ∘∘ hf),
  have hg: g∈ 𝕏.funs 𝕏.sUnion, from comp_is_func he1 hf,
  --provem que g és funció d'elecció
  have hgCF: ChoiceFunction g, --siga X de 𝕏 i x∈ ⋃𝕏, demostrem que, si (X,x)∈ g → x∈X
    intros X x hXx_in_g,
    --com (X,x)∈ g, aleshores ∃ a b c, (a,b)∈ f, (b,c)∈ e1 ∧ (X,x) = (a,c)
    cases (mem_sep.mp hXx_in_g).right with a hg0,cases hg0 with b hg0, cases hg0 with c hg0,
    --com (a,b)∈ f, aleshores tenim que ∃a0 b0:Set.{u}, (a0.prod {a0}).pair b0∈ F ∧ a0.pair b0 = a.pair b
    cases (mem_sep.mp hg0.left).right with a0 hf0, cases hf0 with b0 hf0,
    --per tant, com F és funció d'elecció, aleshores b0 ∈ (a0.prod {a0})
    have b0_in_a0a0:b0∈ a0.prod {a0}, from cfF (a0.prod {a0}) b0 hf0.left,
    --ara, com (b,c)∈ e1, tenim que  ∃ c0 C: Set.{u}, (c0.pair C).pair c0 = (b,c)
    cases (mem_sep.mp hg0.right.left).right with c0 he0, cases he0 with C he0,
    --aleshores tenim que (c0.pair C = b ∧ c0 = c ) i (a0 = a ∧ b0 = b) i (X=a ∧ x=c)
    have he0inj:c0.pair C = b ∧ c0 = c, from pair_inj.mp he0, 
    have hf0inj:a0 = a ∧ b0 = b, from pair_inj.mp hf0.right,
    have hg0inj:X=a ∧ x=c, from pair_inj.mp hg0.right.right,

    --per tant tenim que c0.pair C = b = b0 ∈ (a0.prod {a0})
    have c0C_in_a0a0:c0.pair C ∈ (a0.prod {a0}), from mem_of_eq_of_mem (eq.trans he0inj.left hf0inj.right.symm ).symm b0_in_a0a0,
    --aleshores obtenim que c = c0∈ a0 = a 
    have c_in_a:c∈a,from mem_of_eq_of_set hf0inj.left (mem_of_eq_of_mem he0inj.right (pair_mem_prod.mp c0C_in_a0a0).left),
    --per tant x = c ∈ a = X
    exact mem_of_eq_of_set hg0inj.left.symm (mem_of_eq_of_mem hg0inj.right.symm c_in_a),
  --per tant g és una funció d'elecció entre 𝕏 → ⋃𝕏
  exact exists.intro g ((exists.intro hg) hgCF),
end
end AC_nodisj
