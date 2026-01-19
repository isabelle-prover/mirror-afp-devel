section \<open>\<open>CO_Invariants\<close> – Preservation of invariants under compressed oracle queries\<close>

theory CO_Invariants imports
  Invariant_Preservation
  CO_Operations
begin

lemma function_oracle_ket_invariant: \<open>function_oracle h *\<^sub>S ket_invariant I = ket_invariant ((\<lambda>(x,y). (x,y + h x)) ` I)\<close>
  by (auto intro!: arg_cong[where f=\<open>\<lambda>x. ccspan (x ` I)\<close>] simp add: ket_invariant_def cblinfun_image_ccspan image_image function_oracle_apply)

lemma function_oracle_Snd_ket_invariant: \<open>Snd (function_oracle h) *\<^sub>S ket_invariant I = ket_invariant ((\<lambda>(w,x,y). (w,x,y+h x)) ` I)\<close>
  by (auto intro!: ext arg_cong[where f=\<open>\<lambda>x. ccspan (x ` I)\<close>]
      simp add: Snd_def ket_invariant_def cblinfun_image_ccspan image_image function_oracle_apply tensor_op_ket tensor_ell2_ket)

context compressed_oracle begin

text \<open>This lemma allows to simplify the preservation of invariants under invocations of the compressed oracle.

Given an invariant \<^term>\<open>I\<close>, it can be split into many invariants \<^term>\<open>I1 z\<close> for which preservation is shown 
then with respect to a fixed oracle input \<^term>\<open>x z\<close>, using the simpler oracle \<^const>\<open>query1\<close> instead.

This allows to reduce complex cases to more elementary ones that talk about a single output of the oracle.

Lemmas \<open>inv_split_reg_query\<close> and \<open>inv_split_reg_query'\<close> are the specific instantiations of this for the
two compressed oracle variants \<^const>\<open>query\<close> and \<^const>\<open>query'\<close>.\<close>

lemma inv_split_reg_query_generic:
  fixes query query1
  assumes query_local: \<open>query = controlled_op (\<lambda>x. (Fst; Snd o function_at x) query1)\<close>
  fixes X :: \<open>'x update \<Rightarrow> 'm update\<close>
    and Y :: \<open>'y update \<Rightarrow> 'm update\<close>
    and H :: \<open>('x\<rightharpoonup>'y) update \<Rightarrow> 'm update\<close>
    and K :: \<open>'z \<Rightarrow> 'm ell2 ccsubspace\<close>
    and x :: \<open>'z \<Rightarrow> 'x\<close>
    and M :: \<open>'z set\<close>
  assumes XK: \<open>\<And>z. z\<in>M \<Longrightarrow> K z \<le> lift_invariant X (ket_invariant {x z})\<close>
  assumes pres_I1: \<open>\<And>z. z\<in>M \<Longrightarrow> preserves query1 (I1 z) (J1 z) \<epsilon>\<close>
  assumes I_leq: \<open>I \<le> (SUP z\<in>M. K z \<sqinter> lift_invariant (Y;H o function_at (x z)) (I1 z))\<close>
  assumes J_geq: \<open>\<And>z. z\<in>M \<Longrightarrow> J \<ge> K z \<sqinter> lift_invariant (Y;H o function_at (x z)) (J1 z)\<close>
  assumes YK: \<open>\<And>z. z\<in>M \<Longrightarrow> compatible_register_invariant Y (K z)\<close>
  assumes HK: \<open>\<And>z. z\<in>M \<Longrightarrow> compatible_register_invariant (H o function_at (x z)) (K z)\<close>
  assumes [simp]: \<open>compatible X Y\<close> \<open>compatible X H\<close> \<open>compatible Y H\<close>
  assumes U: \<open>U = ((X;(Y;H)) query)\<close>
  assumes orthoK: \<open>\<And>z z'. z\<in>M \<Longrightarrow> z'\<in>M \<Longrightarrow> z \<noteq> z' \<Longrightarrow> orthogonal_spaces (K z) (K z')\<close>
  assumes \<open>\<epsilon> \<ge> 0\<close>
  assumes \<open>finite M\<close>
  shows \<open>preserves U I J \<epsilon>\<close>
proof (rule inv_split_reg[where ?U1.0=\<open>\<lambda>_. query1\<close> and ?I1.0=I1 and ?J1.0=J1
      and Y=\<open>\<lambda>z. (Y;H o function_at (x z))\<close> and K=K])
  show \<open>(Y;H \<circ> function_at (x z)) query1 *\<^sub>V \<psi> = U *\<^sub>V \<psi>\<close> 
    if \<open>z\<in>M\<close> and \<open>\<psi> \<in> space_as_set (K z)\<close> for \<psi> z
  proof -
    from that(2) XK[OF \<open>z\<in>M\<close>] have \<open>\<psi> \<in> space_as_set (lift_invariant X (ket_invariant {x z}))\<close>
      using less_eq_ccsubspace.rep_eq by blast
    then have \<psi>x: \<open>\<psi> = X (Proj (ket_invariant {x z})) *\<^sub>V \<psi>\<close>
      by (metis Proj_lift_invariant Proj_fixes_image \<open>compatible X Y\<close> compatible_register1)
    have \<open>U *\<^sub>V \<psi> = (X;(Y;H)) query *\<^sub>V \<psi>\<close>
      by (simp add: U)
    also have \<open>\<dots> = (X;(Y;H)) (controlled_op (\<lambda>x. (Fst;Snd \<circ> function_at x) query1)) *\<^sub>V \<psi>\<close>
      by (simp add: query_local)
    also have \<open>\<dots> =  (X;(Y;H)) (controlled_op (\<lambda>x. (Fst;Snd \<circ> function_at x) query1) o\<^sub>C\<^sub>L Fst (selfbutter (ket (x z)))) *\<^sub>V \<psi>\<close>
      by (simp add: register_pair_apply Fst_def flip: register_mult Proj_ket_invariant_butterfly \<psi>x)
    also have \<open>\<dots> = (X;(Y;H)) (Snd ((Fst;Snd \<circ> function_at (x z)) query1) o\<^sub>C\<^sub>L Fst (selfbutter (ket (x z)))) *\<^sub>V \<psi>\<close>
      by (simp add: controlled_op_comp_butter)
    also have \<open>\<dots> = (X;(Y;H)) (Snd ((Fst;Snd \<circ> function_at (x z)) query1)) *\<^sub>V \<psi>\<close>
      by (simp add: register_pair_apply Fst_def flip: register_mult Proj_ket_invariant_butterfly \<psi>x)
    also have \<open>\<dots> = (((X;(Y;H)) o Snd o (Fst;Snd \<circ> function_at (x z))) query1) *\<^sub>V \<psi>\<close>
      by auto
    also have \<open>\<dots> = (Y;H \<circ> function_at (x z)) query1 *\<^sub>V \<psi>\<close>
      by (simp add: register_pair_Snd register_pair_Fst flip: register_comp_pair comp_assoc)
    finally show ?thesis
      by simp
  qed
  from pres_I1 show \<open>preserves query1 (I1 z) (J1 z) \<epsilon>\<close> if \<open>z\<in>M\<close> for z
    using that by -
  from I_leq
  show \<open>I \<le> (SUP z\<in>M. K z \<sqinter> lift_invariant (Y;H o function_at (x z)) (I1 z))\<close>
    by -
  from J_geq
  show \<open>J \<ge> K z \<sqinter> lift_invariant (Y;H o function_at (x z)) (J1 z)\<close> if \<open>z\<in>M\<close> for z
    using that by -
  show \<open>compatible_register_invariant (Y;H \<circ> function_at (x z)) (K z)\<close> if \<open>z\<in>M\<close> for z
    using YK[OF that] HK[OF that] by (rule compatible_register_invariant_pair)
  from orthoK
  show \<open>orthogonal_spaces (K z) (K z')\<close> if \<open>z\<in>M\<close> \<open>z'\<in>M\<close> \<open>z \<noteq> z'\<close> for z z'
    using that by -
  show \<open>register (Y;H \<circ> function_at (x z))\<close> for z
    by simp
  from assms show \<open>\<epsilon> \<ge> 0\<close>
    by -
  from assms show \<open>finite M\<close>
    by metis
qed

lemmas inv_split_reg_query = inv_split_reg_query_generic[OF query_local]
lemmas inv_split_reg_query' = inv_split_reg_query_generic[OF query'_local]

definition \<open>num_queries q = {(x::'x, y::'y, D::'x\<rightharpoonup>'y). card (dom D) \<le> q}\<close>
definition \<open>num_queries' q = {D::'x\<rightharpoonup>'y. card (dom D) \<le> q}\<close>

lemma num_queries_num_queries': \<open>num_queries q = UNIV \<times> UNIV \<times> (num_queries' q)\<close>
  by (auto intro!: simp: num_queries_def num_queries'_def)

lemma ket_invariant_num_queries_num_queries': \<open>ket_invariant (num_queries q) = \<top> \<otimes>\<^sub>S \<top> \<otimes>\<^sub>S ket_invariant (num_queries' q)\<close>
  by (auto simp: ket_invariant_tensor num_queries_num_queries' simp flip: ket_invariant_UNIV)



text \<open>This lemma shows that the number of recorded queries (defined outputs in the oracle register)
  increases at most by 1 upon each query of the compressed oracle.

  The two instantiations for the two compressed oracle variants are given afterwards.\<close>

lemma preserves_num_generic:
  fixes query query1
  assumes query_local: \<open>query = controlled_op (\<lambda>x. (Fst; Snd o function_at x) query1)\<close>
  shows \<open>preserves_ket query (num_queries q) (num_queries (q+1)) 0\<close>
proof -
  define K where \<open>K x = ket_invariant {(x::'x,y::'y,D::'x\<rightharpoonup>'y) | y D. card (dom D - {x}) \<le> q}\<close> for x
  define Kd where \<open>Kd x D0 = ket_invariant {(x::'x,y::'y,D::'x\<rightharpoonup>'y) | y D. (\<forall>x'\<noteq>x. D x' = D0 x')}\<close> for x D0
  have K: \<open>K x = (SUP D0\<in>{D0. D0 x = None \<and> card (dom D0 - {x}) \<le> q}. Kd x D0)\<close> for x
  proof -
    have aux1: \<open>card (dom D - {x}) \<le> q \<Longrightarrow>
         \<exists>D'. D' x = None \<and> card (dom D' - {x}) \<le> q \<and> (\<forall>x'. x' \<noteq> x \<longrightarrow> D x' = D' x')\<close> for D
      apply (rule exI[of _ \<open>D(x:=None)\<close>])
      by auto
    have aux2: \<open>D' x = None \<Longrightarrow>
       card (dom D' - {x}) \<le> q \<Longrightarrow> \<forall>x'. x' \<noteq> x \<longrightarrow> D x' = D' x' \<Longrightarrow> card (dom D - {x}) \<le> q\<close> for D' D
      by (smt (verit) DiffE Diff_empty card_mono domIff dom_minus dual_order.trans finite_class.finite_code singleton_iff subsetI)
    show ?thesis
      by (auto intro!: aux1 aux2 simp add: K_def Kd_def simp flip: ket_invariant_SUP)
  qed
  define Kdx where \<open>Kdx x D0 x' = ket_invariant {(x::'x,y::'y,D::'x\<rightharpoonup>'y) | y D. D x' = D0 x'}\<close> for D0 x' x
  have Kd: \<open>Kd x D0 = (INF x'\<in>-{x}. Kdx x D0 x')\<close> for x D0
    unfolding Kd_def Kdx_def
    apply (subst ket_invariant_INF[symmetric])
    apply (rule arg_cong[where f=ket_invariant])
    by auto
  have Kdx: \<open>Kdx x D0 x' = lift_invariant reg_1_3 (ket_invariant {x}) \<sqinter> lift_invariant (reg_3_3 o function_at x') (ket_invariant {D0 x'})\<close> for D0 x' x
    unfolding Kdx_def reg_3_3_def reg_1_3_def
    apply (simp add: lift_invariant_comp)
    apply (subst lift_invariant_function_at_ket_inv)
    apply (subst lift_Snd_ket_inv)
    apply (subst lift_Snd_ket_inv)
    apply (subst lift_Fst_ket_inv)
    apply (subst ket_invariant_inter)
    apply (rule arg_cong[where f=ket_invariant])
    by auto

  show ?thesis
  proof (rule inv_split_reg_query_generic[where X=\<open>reg_1_3\<close> and Y=\<open>reg_2_3\<close> and H=\<open>reg_3_3\<close> and K=K 
        and x=\<open>\<lambda>x. x\<close> and ?I1.0=\<open>\<lambda>_. \<top>\<close> and ?J1.0=\<open>\<lambda>_. \<top>\<close>, OF query_local])
    show \<open>query = (reg_1_3;(reg_2_3;reg_3_3)) query\<close>
      by (auto simp add: pair_Fst_Snd reg_1_3_def reg_2_3_def reg_3_3_def)
    show \<open>compatible reg_1_3 reg_2_3\<close> \<open>compatible reg_1_3 reg_3_3\<close> \<open>compatible reg_2_3 reg_3_3\<close>
      by simp_all
    show \<open>compatible_register_invariant reg_2_3 (K x)\<close> for x
      unfolding K Kd Kdx
      apply (rule compatible_register_invariant_SUP, simp)
      apply (rule compatible_register_invariant_INF, simp)
      apply (rule compatible_register_invariant_inter, simp)
       apply (rule compatible_register_invariant_compatible_register)
       apply simp
      apply (rule compatible_register_invariant_compatible_register)
      by simp
    show \<open>compatible_register_invariant (reg_3_3 o function_at x) (K x)\<close> for x
      unfolding K Kd Kdx
      apply (rule compatible_register_invariant_SUP, simp)
      apply (rule compatible_register_invariant_INF, simp)
      apply (rule compatible_register_invariant_inter, simp)
       apply (rule compatible_register_invariant_compatible_register)
       apply simp
      apply (rule compatible_register_invariant_compatible_register)
      by simp
    show \<open>ket_invariant (num_queries q)
      \<le> (SUP x. K x \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) \<top>)\<close>
      by (auto intro!: card_Diff1_le[THEN order_trans]
          simp: K_def lift_Fst_ket_inv reg_1_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          num_queries_def)
    have *: \<open>card (dom D) \<le> card (dom D - {x}) + 1\<close> for D x
      by (metis One_nat_def card.empty card.insert diff_card_le_card_Diff empty_not_insert finite.intros(1)
          finite_insert insert_absorb le_diff_conv)
    show \<open>K x \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) \<top>
      \<le> ket_invariant (num_queries (q + 1))\<close> for x
      by (auto intro!: *[THEN order_trans]
          simp add: num_queries_def K_def lift_Fst_ket_inv reg_1_3_def ket_invariant_inter ket_invariant_SUP[symmetric])
    show \<open>preserves query1 \<top> \<top> 0\<close>
      by simp
    show \<open>orthogonal_spaces (K x) (K x')\<close> if \<open>x \<noteq> x'\<close> for x x'
      unfolding K_def orthogonal_spaces_ket using that by auto
    show \<open>K x \<le> lift_invariant reg_1_3 (ket_invariant {x})\<close> for x
      by (auto simp add: K Kd_def reg_1_3_def lift_inv_prod' lift_Fst_ket_inv
          simp flip: ket_invariant_SUP)
    show \<open>0 \<le> (0::real)\<close>
      by auto
    show \<open>finite (UNIV::'x set)\<close>
      by simp
  qed
qed

lemmas preserves_num = preserves_num_generic[OF query_local]
lemmas preserves_num' = preserves_num_generic[OF query'_local]


text \<open>We now present various lemmas that give concrete bounds for the preservation of invariants
under various conditions, for \<^const>\<open>query1\<close> (and \<^const>\<open>query1'\<close>).

The invariants are formulated specifically for an application of \<^const>\<open>query1\<close> to a two-partite
system with query output register and oracle register only.

These can be applied to derive invariant preservation for full compressed oracle queries on arbitrary systems by 
first splitting the invariant using @{thm [source] inv_split_reg_query}.\<close>



text \<open>The first bound is applicable for ket-invariants that do not put any conditions on the output register
and that not not require that the output register is defined (not \<^term>\<open>None\<close>) after the query.

Lemmas \<open>preserve_query1_bound\<close> and \<open>preserve_query1'_bound\<close>; with slightly simplified bounds in
\<open>preserve_query1_simplified\<close>, \<open>preserve_query1'_simplified\<close>.\<close>

definition \<open>preserve_query1_bound NoneI b\<^sub>i b\<^sub>j\<^sub>0 = 4 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N  +  2 * of_bool NoneI * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
lemma preserve_query1: 
  assumes IJ: \<open>I \<subseteq> J\<close>
  assumes [simp]: \<open>None \<in> J\<close>
  assumes b\<^sub>i: \<open>card (Some -` I) \<le> b\<^sub>i\<close>
  assumes b\<^sub>j\<^sub>0: \<open>card (- Some -` J) \<le> b\<^sub>j\<^sub>0\<close>
  assumes \<epsilon>: \<open>\<epsilon> \<ge> preserve_query1_bound (None\<in>I) b\<^sub>i b\<^sub>j\<^sub>0\<close>
  shows \<open>preserves_ket query1 (UNIV \<times> I) (UNIV \<times> J) \<epsilon>\<close>
proof (rule preservesI')
  show \<open>\<epsilon> \<ge> 0\<close>
    using _ \<epsilon> apply (rule order.trans)
    by (simp add: preserve_query1_bound_def)
  fix \<psi> :: \<open>('y \<times> 'y option) ell2\<close>
  assume \<psi>': \<open>\<psi> \<in> space_as_set (ket_invariant (UNIV \<times> I))\<close>
  assume \<open>norm \<psi> = 1\<close>

  define I' J' where \<open>I' = Some -` I\<close> and \<open>J' = Some -` J\<close>
  from \<psi>' have \<psi>: \<open>\<psi> \<in> space_as_set (ket_invariant (UNIV \<times> ((Some ` I' \<union> {None}))))\<close>
    using I'_def less_eq_ccsubspace.rep_eq by fastforce
  have [simp]: \<open>I' \<subseteq> J'\<close>
    using I'_def J'_def IJ by blast

  define \<beta> where \<open>\<beta> = Rep_ell2 \<psi>\<close>
  then have \<beta>: \<open>\<psi> = (\<Sum>yd\<in>UNIV\<times>(Some ` I' \<union> {None}). \<beta> yd *\<^sub>C ket yd)\<close>
    using ell2_sum_ket_ket_invariant[OF \<psi>] by auto
  have \<beta>bound: \<open>(\<Sum>yd\<in>UNIV\<times>(Some ` I' \<union> {None}). (cmod (\<beta> yd))\<^sup>2) \<le> 1\<close> (is \<open>?lhs \<le> 1\<close>)
    apply (subgoal_tac \<open>(norm \<psi>)\<^sup>2 = ?lhs\<close>)
     apply (simp add: \<open>norm \<psi> = 1\<close>)
    by (simp add: \<beta> pythagorean_theorem_sum)
  have \<beta>None0: \<open>\<beta> (y,None) = 0\<close> if \<open>None \<notin> I\<close> for y
    using \<psi>' that by (simp add: \<beta>_def ket_invariant_Rep_ell2)

  have [simp]: \<open>Some -` insert None X = Some -` X\<close> for X :: \<open>'z option set\<close>
    by auto
  have [simp]: \<open>Some -` Some ` X = X\<close> for X :: \<open>'z set\<close>
    by auto
  have [simp]: \<open>Some x \<in> J \<longleftrightarrow> x \<in> J'\<close> for x
    by (simp add: J'_def)
  have [simp]: \<open>x \<in> I' \<Longrightarrow> x \<in> J'\<close> for x
    using \<open>I' \<subseteq> J'\<close> by blast
  have [simp]: \<open>(\<Sum>x\<in>X. if x \<notin> Y then f x else 0) = (\<Sum>x\<in>X-Y. f x)\<close> if \<open>finite X\<close> for f :: \<open>'y \<Rightarrow> 'z::ab_group_add\<close> and X Y
    apply (rule sum.mono_neutral_cong_right)
    using that by auto
  have [simp]: \<open>(\<Sum>x\<in>X. \<Sum>y\<in>Y. if x \<notin> X' then f x y else 0) = (\<Sum>x\<in>X-X'. \<Sum>y\<in>Y. f x y)\<close> if \<open>finite X\<close> 
    for f :: \<open>'x \<Rightarrow> 'y \<Rightarrow> 'z::ab_group_add\<close> and X X' Y
    apply (rule sum.mono_neutral_cong_right)
    using that by auto
  have [simp]: \<open>\<beta> yd *\<^sub>C a *\<^sub>C b = a *\<^sub>C \<beta> yd *\<^sub>C b\<close> for yd a and b :: \<open>'z::complex_vector\<close>
    by auto
  have [simp]: \<open>cmod \<alpha> = inverse (sqrt N)\<close> \<open>cmod (\<alpha>\<^sup>2) = inverse N\<close> \<open>cmod (\<alpha>^3) = inverse (N * sqrt N)\<close> \<open>cmod (\<alpha>^4) = inverse (N\<^sup>2)\<close>
    by (auto simp: power4_eq_xxxx power2_eq_square norm_mult numeral_3_eq_3 \<alpha>_def inverse_eq_divide norm_divide norm_power power_one_over)
  have [simp]: \<open>card (Some ` I') \<le> b\<^sub>i\<close>
    by (metis I'_def b\<^sub>i card_image inj_Some)
  have bound_J'[simp]: \<open>card (Some ` (- J')) \<le> b\<^sub>j\<^sub>0\<close>
    using b\<^sub>j\<^sub>0 unfolding J'_def by (simp add: card_image)

  define \<phi> and PJ :: \<open>('y \<times> 'y option) update\<close> where 
    \<open>\<phi> = query1 *\<^sub>V \<psi>\<close> and \<open>PJ = Proj (ket_invariant (UNIV \<times> -J))\<close>
  have [simp]: \<open>PJ *\<^sub>V ket (x,y) = (if y\<in>-J then ket (x,y) else 0)\<close> for x y
    by (simp add: Proj_ket_invariant_ket PJ_def)
  have P0\<phi>: \<open>PJ *\<^sub>V \<phi> = 
        \<alpha>^4 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (y, Some d) *\<^sub>C ket (y', Some d')) -
        \<alpha>\<^sup>2 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (y, Some d) *\<^sub>C ket (y + d, Some d')) -
        \<alpha>\<^sup>2 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (y, Some d) *\<^sub>C ket (y + d', Some d')) +
        \<alpha>\<^sup>2 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (y, Some d) *\<^sub>C ket (y, Some d')) +
        \<alpha> *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (y, None) *\<^sub>C ket (y + d', Some d')) -
        \<alpha>^3 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (y, None) *\<^sub>C ket (y', Some d'))\<close>
    (is \<open>_ = ?t1 - ?t2 - ?t3 + ?t4 + ?t5 - ?t6\<close>)
    by (simp add: \<phi>_def \<beta> query1 option_sum_split vimage_Compl
        cblinfun.add_right cblinfun.diff_right if_distrib Compl_eq_Diff_UNIV
        vimage_singleton_inj sum_sum_if_eq sum.distrib scaleC_diff_right scaleC_sum_right
        sum_subtractf case_prod_beta sum.cartesian_product' scaleC_add_right add_diff_eq
        cblinfun.scaleC_right cblinfun.sum_right
        flip: sum.Sigma add.assoc scaleC_scaleC
        cong del: option.case_cong if_cong)

  have norm_t1: \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket y'd') \<le> sqrt (N * b\<^sub>i)\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by (auto simp: N_def)

    have \<open>norm ?t1 = inverse (N\<^sup>2) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket y'd')\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      apply (subst sum.swap) apply (subst (2) sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (N * sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def real_sqrt_mult algebra_simps  real_sqrt_mult algebra_simps
          sqrt_sqrt[THEN extend_mult_rule])
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (N * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (metis bound_J' linordered_field_class.inverse_nonnegative_iff_nonnegative mult.commute mult_right_mono of_nat_0_le_iff of_nat_mono real_sqrt_ge_zero real_sqrt_le_iff)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (smt (verit) ab_semigroup_mult_class.mult_ac(1) divide_inverse_commute of_nat_power power2_eq_square real_divide_square_eq)
    finally show \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t2: \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>card {y. \<delta> = fst y + the (snd y) \<and> y \<in> UNIV \<times> Some ` I'} \<le> card I'\<close> for \<delta>
      apply (rule card_inj_on_le[where f=\<open>\<lambda>y. the (snd y)\<close>])
      by (auto intro!: inj_onI)
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket (fst yd + the (snd yd), d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * I'_def b\<^sub>i order.trans by auto

    have \<open>norm ?t2 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket (fst yd + the (snd yd), d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t3: \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>card {y. a = fst y \<and> y \<in> UNIV \<times> (I \<inter> range Some)} \<le> card I'\<close> for a :: 'y
      apply (rule card_inj_on_le[where f=\<open>\<lambda>y. the (snd y)\<close>])
      by (auto intro!: inj_onI simp: I'_def)
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket (fst yd + the d', d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * I'_def b\<^sub>i order.trans by auto

    have \<open>norm ?t3 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> Some ` I'. 
                          \<beta> yd *\<^sub>C ket (fst yd + the d', d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t4: \<open>norm ?t4 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>card {y. a = fst y \<and> y \<in> UNIV \<times> (I \<inter> range Some)} \<le> card I'\<close> for a :: 'y
      apply (rule card_inj_on_le[where f=\<open>\<lambda>y. the (snd y)\<close>])
      by (auto intro!: inj_onI simp: I'_def)
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket (fst yd, d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * I'_def b\<^sub>i order.trans by auto

    have \<open>norm ?t4 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> Some ` I'. 
                          \<beta> yd *\<^sub>C ket (fst yd, d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t4 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t5: \<open>norm ?t5 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True
    have *: \<open>card {y. a = fst y \<and> y \<in> UNIV \<times> {None :: 'y option}} \<le> card {()}\<close> for a :: 'y
      apply (rule card_inj_on_le[where f=\<open>\<lambda>_. undefined\<close>])
      by (auto intro!: inj_onI)
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> {None}. \<beta> yd *\<^sub>C ket (fst yd + the d', d')) \<le> sqrt (1::nat)\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * by auto

    have \<open>norm ?t5 = inverse (sqrt N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> {None}. 
                          \<beta> yd *\<^sub>C ket (fst yd + the d', d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) 
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (sqrt N) * (sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse (sqrt N) * sqrt b\<^sub>j\<^sub>0\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      by (simp add: True divide_inverse_commute)
    finally show ?thesis
      by -
  next
    case False
    then show ?thesis
      using \<beta>None0 by auto
  qed

  have norm_t6: \<open>norm ?t6 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> {None}. \<beta> yd *\<^sub>C ket y'd') \<le> sqrt N\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by (auto simp: N_def)

    have \<open>norm ?t6 = inverse (N * sqrt N) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> {None}. \<beta> yd *\<^sub>C ket y'd')\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (N * sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def mult.commute real_sqrt_mult vector_space_over_itself.scale_scale)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (N * sqrt b\<^sub>j\<^sub>0)\<close>
      by (simp add: N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      using True by (simp add: divide_inverse_commute less_eq_real_def N_def)
    finally show ?thesis
      by -
  next
    case False
    then show ?thesis
      using \<beta>None0 by auto
  qed

  have \<open>norm (PJ *\<^sub>V \<phi>) \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N   +   sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N             +   sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N
                       + sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N   + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
    unfolding P0\<phi>
    apply (rule norm_triangle_le_diff norm_triangle_le, rule add_mono)+
         apply (rule norm_t1)
        apply (rule norm_t2)
       apply (rule norm_t3)
      apply (rule norm_t4)
     apply (rule norm_t5)
    by (rule norm_t6)

  also have \<open>\<dots> \<le> 4 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N  +  2 * of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
    by (simp add: mult.commute vector_space_over_itself.scale_left_commute)
  also have \<open>\<dots> \<le> \<epsilon>\<close>
    using \<epsilon> by (auto intro!: simp add: preserve_query1_bound_def)
  finally show \<open>norm (Proj (- ket_invariant (UNIV \<times> J)) *\<^sub>V \<phi>) \<le> \<epsilon>\<close>
    unfolding PJ_def
    apply (subst ket_invariant_compl[symmetric])
    by simp
qed

definition \<open>preserve_query1'_bound NoneI b\<^sub>i b\<^sub>j\<^sub>0 = 3 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N  +  2 * of_bool NoneI * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
lemma preserve_query1':
  assumes IJ: \<open>I \<subseteq> J\<close>
  assumes [simp]: \<open>None \<in> J\<close>
  assumes b\<^sub>i: \<open>card (Some -` I) \<le> b\<^sub>i\<close>
  assumes b\<^sub>j\<^sub>0: \<open>card (- Some -` J) \<le> b\<^sub>j\<^sub>0\<close>
  assumes \<epsilon>: \<open>\<epsilon> \<ge> preserve_query1'_bound (None\<in>I) b\<^sub>i b\<^sub>j\<^sub>0\<close>
  shows \<open>preserves_ket query1' (UNIV \<times> I) (UNIV \<times> J) \<epsilon>\<close>
proof (rule preservesI')
  show \<open>\<epsilon> \<ge> 0\<close>
    using _ \<epsilon> apply (rule order.trans)
    by (simp add: preserve_query1'_bound_def)
  fix \<psi> :: \<open>('y \<times> 'y option) ell2\<close>
  assume \<psi>': \<open>\<psi> \<in> space_as_set (ket_invariant (UNIV \<times> I))\<close>
  assume \<open>norm \<psi> = 1\<close>

  define I' J' where \<open>I' = Some -` I\<close> and \<open>J' = Some -` J\<close>
  from \<psi>' have \<psi>: \<open>\<psi> \<in> space_as_set (ket_invariant (UNIV \<times> ((Some ` I' \<union> {None}))))\<close>
    using I'_def less_eq_ccsubspace.rep_eq by fastforce
  have [simp]: \<open>I' \<subseteq> J'\<close>
    using I'_def J'_def IJ by blast

  define \<beta> where \<open>\<beta> = Rep_ell2 \<psi>\<close>
  then have \<beta>: \<open>\<psi> = (\<Sum>yd\<in>UNIV\<times>(Some ` I' \<union> {None}). \<beta> yd *\<^sub>C ket yd)\<close>
    using ell2_sum_ket_ket_invariant[OF \<psi>] by auto
  have \<beta>bound: \<open>(\<Sum>yd\<in>UNIV\<times>(Some ` I' \<union> {None}). (cmod (\<beta> yd))\<^sup>2) \<le> 1\<close> (is \<open>?lhs \<le> 1\<close>)
    apply (subgoal_tac \<open>(norm \<psi>)\<^sup>2 = ?lhs\<close>)
     apply (simp add: \<open>norm \<psi> = 1\<close>)
    by (simp add: \<beta> pythagorean_theorem_sum)
  have \<beta>None0: \<open>\<beta> (y,None) = 0\<close> if \<open>None \<notin> I\<close> for y
    using \<psi>' that by (simp add: \<beta>_def ket_invariant_Rep_ell2)

  have [simp]: \<open>Some -` insert None X = Some -` X\<close> for X :: \<open>'z option set\<close>
    by auto
  have [simp]: \<open>Some -` Some ` X = X\<close> for X :: \<open>'z set\<close>
    by auto
  have [simp]: \<open>Some x \<in> J \<longleftrightarrow> x \<in> J'\<close> for x
    by (simp add: J'_def)
  have [simp]: \<open>x \<in> I' \<Longrightarrow> x \<in> J'\<close> for x
    using \<open>I' \<subseteq> J'\<close> by blast
  have [simp]: \<open>(\<Sum>x\<in>X. if x \<notin> Y then f x else 0) = (\<Sum>x\<in>X-Y. f x)\<close> if \<open>finite X\<close> for f :: \<open>'y \<Rightarrow> 'z::ab_group_add\<close> and X Y
    apply (rule sum.mono_neutral_cong_right)
    using that by auto
  have [simp]: \<open>(\<Sum>x\<in>X. \<Sum>y\<in>Y. if x \<notin> X' then f x y else 0) = (\<Sum>x\<in>X-X'. \<Sum>y\<in>Y. f x y)\<close> if \<open>finite X\<close> 
    for f :: \<open>'x \<Rightarrow> 'y \<Rightarrow> 'z::ab_group_add\<close> and X X' Y
    apply (rule sum.mono_neutral_cong_right)
    using that by auto
  have [simp]: \<open>\<beta> yd *\<^sub>C a *\<^sub>C b = a *\<^sub>C \<beta> yd *\<^sub>C b\<close> for yd a and b :: \<open>'z::complex_vector\<close>
    by auto
  have [simp]: \<open>cmod \<alpha> = inverse (sqrt N)\<close> \<open>cmod (\<alpha>\<^sup>2) = inverse N\<close> \<open>cmod (\<alpha>^3) = inverse (N * sqrt N)\<close> \<open>cmod (\<alpha>^4) = inverse (N\<^sup>2)\<close>
    by (auto simp: norm_mult numeral_3_eq_3 \<alpha>_def inverse_eq_divide norm_divide norm_power power_one_over power4_eq_xxxx power2_eq_square)
  have [simp]: \<open>card (Some ` I') \<le> b\<^sub>i\<close>
    by (metis I'_def b\<^sub>i card_image inj_Some)
  have bound_J'[simp]: \<open>card (Some ` (- J')) \<le> b\<^sub>j\<^sub>0\<close>
      using b\<^sub>j\<^sub>0 unfolding J'_def by (simp add: card_image)

  define \<phi> and PJ :: \<open>('y * 'y option) update\<close> where 
    \<open>\<phi> = query1' *\<^sub>V \<psi>\<close> and \<open>PJ = Proj (ket_invariant (UNIV \<times> -J))\<close>
  have [simp]: \<open>PJ *\<^sub>V ket (x,y) = (if y\<in>-J then ket (x,y) else 0)\<close> for x y
    by (simp add: Proj_ket_invariant_ket PJ_def)
  have P0\<phi>: \<open>PJ *\<^sub>V \<phi> = 
        \<alpha>^4 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (y, Some d) *\<^sub>C ket (y', Some d')) -
        \<alpha>\<^sup>2 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (y, Some d) *\<^sub>C ket (y + d, Some d')) -
        \<alpha>\<^sup>2 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (y, Some d) *\<^sub>C ket (y + d', Some d')) +
        \<alpha> *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (y, None) *\<^sub>C ket (y + d', Some d')) -
        \<alpha>^3 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (y, None) *\<^sub>C ket (y', Some d'))\<close>
    (is \<open>_ = ?t1 - ?t2 - ?t3 + ?t5 - ?t6\<close>)
    by (simp add: \<phi>_def \<beta> query1' option_sum_split vimage_Compl cblinfun.scaleC_right
        cblinfun.add_right cblinfun.diff_right if_distrib Compl_eq_Diff_UNIV
        vimage_singleton_inj sum_sum_if_eq sum.distrib scaleC_diff_right scaleC_sum_right
        sum_subtractf case_prod_beta sum.cartesian_product' scaleC_add_right add_diff_eq
        cblinfun.sum_right
        flip: sum.Sigma add.assoc scaleC_scaleC
        cong del: option.case_cong if_cong)

  have norm_t1: \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket y'd') \<le> sqrt (N * b\<^sub>i)\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by (auto simp: N_def)

    have \<open>norm ?t1 = inverse (N\<^sup>2) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket y'd')\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      apply (subst sum.swap) apply (subst (2) sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (N * sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def real_sqrt_mult algebra_simps
          sqrt_sqrt[THEN extend_mult_rule])
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (N * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (metis bound_J' linordered_field_class.inverse_nonnegative_iff_nonnegative mult.commute mult_right_mono of_nat_0_le_iff of_nat_mono real_sqrt_ge_zero real_sqrt_le_iff)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (smt (verit) ab_semigroup_mult_class.mult_ac(1) divide_inverse_commute of_nat_power power2_eq_square real_divide_square_eq)
    finally show \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t2: \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>card {y. \<delta> = fst y + the (snd y) \<and> y \<in> UNIV \<times> Some ` I'} \<le> card I'\<close> for \<delta>
      apply (rule card_inj_on_le[where f=\<open>\<lambda>y. the (snd y)\<close>])
      by (auto intro!: inj_onI)
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket (fst yd + the (snd yd), d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * I'_def b\<^sub>i order.trans by auto

    have \<open>norm ?t2 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket (fst yd + the (snd yd), d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t3: \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>card {y. a = fst y \<and> y \<in> UNIV \<times> (I \<inter> range Some)} \<le> card I'\<close> for a :: 'y
      apply (rule card_inj_on_le[where f=\<open>\<lambda>y. the (snd y)\<close>])
      by (auto intro!: inj_onI simp: I'_def)
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> Some ` I'. \<beta> yd *\<^sub>C ket (fst yd + the d', d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * I'_def b\<^sub>i order.trans by auto

    have \<open>norm ?t3 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> Some ` I'. 
                          \<beta> yd *\<^sub>C ket (fst yd + the d', d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t5: \<open>norm ?t5 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True
    have *: \<open>card {y. a = fst y \<and> y \<in> UNIV \<times> {None :: 'y option}} \<le> card {()}\<close> for a :: 'y
      apply (rule card_inj_on_le[where f=\<open>\<lambda>_. undefined\<close>])
      by (auto intro!: inj_onI)
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> {None}. \<beta> yd *\<^sub>C ket (fst yd + the d', d')) \<le> sqrt (1::nat)\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * by auto

    have \<open>norm ?t5 = inverse (sqrt N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> {None}. 
                          \<beta> yd *\<^sub>C ket (fst yd + the d', d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) 
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (sqrt N) * (sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse (sqrt N) * sqrt b\<^sub>j\<^sub>0\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      using True by (simp add: divide_inverse_commute)
    finally show ?thesis
      by -
  next
    case False
    then show ?thesis
      using \<beta>None0 by auto
  qed

  have norm_t6: \<open>norm ?t6 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True 
    have *: \<open>norm (\<Sum>yd\<in>UNIV \<times> {None}. \<beta> yd *\<^sub>C ket y'd') \<le> sqrt N\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by (auto simp: N_def)

    have \<open>norm ?t6 = inverse (N * sqrt N) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<Sum>yd\<in>UNIV \<times> {None}. \<beta> yd *\<^sub>C ket y'd')\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (N * sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def real_sqrt_mult algebra_simps
          sqrt_sqrt[THEN extend_mult_rule])
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (N * sqrt b\<^sub>j\<^sub>0)\<close>
      by (simp add: N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      using True by (simp add: divide_inverse_commute less_eq_real_def N_def)
    finally show ?thesis
      by -
  next
    case False
    then show ?thesis
      using \<beta>None0 by auto
  qed

  have \<open>norm (PJ *\<^sub>V \<phi>) \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N   +   sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N              +   sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N
                                                  + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
    unfolding P0\<phi>
    apply (rule norm_triangle_le_diff norm_triangle_le, rule add_mono)+
         apply (rule norm_t1)
        apply (rule norm_t2)
       apply (rule norm_t3)
     apply (rule norm_t5)
    by (rule norm_t6)
  also have \<open>\<dots> \<le> 3 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N  +  2 * of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
    by (simp add: mult.commute vector_space_over_itself.scale_left_commute)
  also have \<open>\<dots> \<le> \<epsilon>\<close>
    using \<epsilon> by (auto intro!: simp add: preserve_query1'_bound_def)
  finally show \<open>norm (Proj (- ket_invariant (UNIV \<times> J)) *\<^sub>V \<phi>) \<le> \<epsilon>\<close>
    unfolding PJ_def
    apply (subst ket_invariant_compl[symmetric])
    by simp
qed


(* Invariant preservation of query1 for invariants that say nothing about the Y-register. Slightly simpler bound. *)

lemma preserve_query1_simplified:
  assumes \<open>I \<subseteq> J\<close>
  assumes \<open>None \<in> J\<close>
  assumes b\<^sub>j\<^sub>0: \<open>card (- Some -` J) \<le> b\<^sub>j\<^sub>0\<close>
  shows \<open>preserves_ket query1 (UNIV \<times> I) (UNIV \<times> J) (6 * sqrt b\<^sub>j\<^sub>0 / sqrt N)\<close>
  apply (rule preserve_query1[where b\<^sub>j\<^sub>0=b\<^sub>j\<^sub>0 and b\<^sub>i=N])
  using assms by (auto intro!: divide_right_mono simp: preserve_query1_bound_def card_mono N_def)

lemma preserve_query1'_simplified:
  assumes \<open>I \<subseteq> J\<close>
  assumes \<open>None \<in> J\<close>
  assumes b\<^sub>j\<^sub>0: \<open>card (- Some -` J) \<le> b\<^sub>j\<^sub>0\<close>
  shows \<open>preserves_ket query1' (UNIV \<times> I) (UNIV \<times> J) (5 * sqrt b\<^sub>j\<^sub>0 / sqrt N)\<close>
  apply (rule preserve_query1'[where b\<^sub>j\<^sub>0=b\<^sub>j\<^sub>0 and b\<^sub>i=N])
  using assms by (auto intro!: divide_right_mono simp: preserve_query1'_bound_def card_mono N_def)


text \<open>The next bound is applicable for ket-invariants assume the output register to have a specific value
\<^term>\<open>ket y\<^sub>0\<close> (typically \<^term>\<open>ket 0\<close>) before the query and do not put any conditions on the output register after the query.

Lemmas \<open>preserve_query1_fixY\<close> and \<open>preserve_query1'_fixY\<close>.\<close>

definition \<open>preserve_query1_fixY_bound NoneI NoneJ b\<^sub>i b\<^sub>j\<^sub>0 = sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N) 
  + 3 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N  +  of_bool NoneI * sqrt b\<^sub>j\<^sub>0 / sqrt N + of_bool NoneI * sqrt b\<^sub>j\<^sub>0 / N
   + of_bool NoneJ / sqrt N + of_bool NoneJ * sqrt b\<^sub>i / N + of_bool (NoneI \<and> NoneJ) / sqrt N\<close>
lemma preserve_query1_fixY: 
  assumes IJ: \<open>I \<subseteq> J\<close>
  assumes b\<^sub>i: \<open>card (Some -` I) \<le> b\<^sub>i\<close>
  assumes b\<^sub>j\<^sub>0: \<open>card (- Some -` J) \<le> b\<^sub>j\<^sub>0\<close>
  assumes \<epsilon>: \<open>\<epsilon> \<ge> preserve_query1_fixY_bound (None\<in>I) (None\<notin>J) b\<^sub>i b\<^sub>j\<^sub>0\<close>
  shows \<open>preserves_ket query1 ({y\<^sub>0} \<times> I) (UNIV \<times> J) \<epsilon>\<close>
proof (rule preservesI')
  show \<open>\<epsilon> \<ge> 0\<close>
    using _ \<epsilon> apply (rule order.trans)
    by (simp add: preserve_query1_fixY_bound_def)
  fix \<psi> :: \<open>('y \<times> 'y option) ell2\<close>
  assume \<psi>: \<open>\<psi> \<in> space_as_set (ket_invariant ({y\<^sub>0} \<times> I))\<close>
  assume \<open>norm \<psi> = 1\<close>

  define I' J' where \<open>I' = Some -` I\<close> and \<open>J' = Some -` J\<close>
  then have \<open>{y\<^sub>0} \<times> I \<subseteq> {y\<^sub>0} \<times> (Some ` I' \<union> {None})\<close>
    apply (rule_tac Sigma_mono)
    by auto
  with \<psi> have \<psi>': \<open>\<psi> \<in> space_as_set (ket_invariant ({y\<^sub>0} \<times> ((Some ` I' \<union> {None}))))\<close>
    using less_eq_ccsubspace.rep_eq ket_invariant_le by fastforce
  have [simp]: \<open>I' \<subseteq> J'\<close>
    using I'_def J'_def IJ by blast

  define \<beta> where \<open>\<beta> d = Rep_ell2 \<psi> (y\<^sub>0,d)\<close> for d
  then have \<beta>: \<open>\<psi> = (\<Sum>d\<in>Some ` I' \<union> {None}. \<beta> d *\<^sub>C ket (y\<^sub>0,d))\<close>
    using ell2_sum_ket_ket_invariant[OF \<psi>']
    by (auto simp: sum.cartesian_product')
  have \<beta>bound: \<open>(\<Sum>d\<in>(Some ` I' \<union> {None}). (cmod (\<beta> d))\<^sup>2) \<le> 1\<close> (is \<open>?lhs \<le> 1\<close>)
    apply (subgoal_tac \<open>(norm \<psi>)\<^sup>2 = ?lhs\<close>)
     apply (simp add: \<open>norm \<psi> = 1\<close>)
    by (simp add: \<beta> pythagorean_theorem_sum del: sum.insert)
  have \<beta>None: \<open>cmod (\<beta> None) \<le> 1\<close>
  proof -
    have \<open>(cmod (\<beta> None))\<^sup>2 = (\<Sum>d\<in>{None}. (cmod (\<beta> d))\<^sup>2)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Sum>d\<in>(Some ` I' \<union> {None}). (cmod (\<beta> d))\<^sup>2)\<close>
      apply (rule sum_mono2) by auto
    also have \<open>\<dots> \<le> 1\<close>
      by (rule \<beta>bound)
    finally show ?thesis
      by (simp add: power_le_one_iff)
  qed
  have \<beta>None0: \<open>\<beta> None = 0\<close> if \<open>None \<notin> I\<close>
    using \<psi> that by (simp add: \<beta>_def ket_invariant_Rep_ell2)

  have [simp]: \<open>Some -` insert None X = Some -` X\<close> for X :: \<open>'z option set\<close>
    by auto
  have [simp]: \<open>Some -` Some ` X = X\<close> for X :: \<open>'z set\<close>
    by auto
  have [simp]: \<open>Some x \<in> J \<longleftrightarrow> x \<in> J'\<close> for x
    by (simp add: J'_def)
  have [simp]: \<open>x \<in> I' \<Longrightarrow> x \<in> J'\<close> for x
    using \<open>I' \<subseteq> J'\<close> by blast
  have [simp]: \<open>(\<Sum>x\<in>X. if x \<notin> Y then f x else 0) = (\<Sum>x\<in>X-Y. f x)\<close> if \<open>finite X\<close> for f :: \<open>'y \<Rightarrow> 'z::ab_group_add\<close> and X Y
    apply (rule sum.mono_neutral_cong_right)
    using that by auto
  have [simp]: \<open>\<beta> yd *\<^sub>C a *\<^sub>C b = a *\<^sub>C \<beta> yd *\<^sub>C b\<close> for yd a and b :: \<open>'z::complex_vector\<close>
    by auto
  have [simp]: \<open>cmod \<alpha> = inverse (sqrt N)\<close> \<open>cmod (\<alpha>\<^sup>2) = inverse N\<close> \<open>cmod (\<alpha>^3) = inverse (N * sqrt N)\<close> \<open>cmod (\<alpha>^4) = inverse (N\<^sup>2)\<close>
    by (auto simp: norm_mult numeral_3_eq_3 \<alpha>_def inverse_eq_divide norm_divide norm_power power_one_over power4_eq_xxxx power2_eq_square)
  have [simp]: \<open>card (Some ` I') \<le> b\<^sub>i\<close>
    by (metis I'_def b\<^sub>i card_image inj_Some)
  have bound_J'[simp]: \<open>card (Some ` (- J')) \<le> b\<^sub>j\<^sub>0\<close>
      using b\<^sub>j\<^sub>0 unfolding J'_def by (simp add: card_image)

  define \<phi> and PJ :: \<open>('y * 'y option) update\<close> where 
    \<open>\<phi> = query1 *\<^sub>V \<psi>\<close> and \<open>PJ = Proj (ket_invariant (UNIV \<times> -J))\<close>
  have [simp]: \<open>PJ *\<^sub>V ket (x,y) = (if y\<in>-J then ket (x,y) else 0)\<close> for x y
    by (simp add: Proj_ket_invariant_ket PJ_def)
  have P0\<phi>: \<open>PJ *\<^sub>V \<phi> = 
        \<alpha>^4 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (Some d) *\<^sub>C ket (y', Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d', Some d'))
        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0, Some d'))
        + \<alpha> *\<^sub>C (\<Sum>d'\<in>- J'. \<beta> (None) *\<^sub>C ket (y\<^sub>0 + d', Some d'))
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (None) *\<^sub>C ket (y', Some d'))
        + (of_bool (None \<notin> J) * \<alpha>) *\<^sub>C (\<Sum>d\<in>I'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, None))
        - (of_bool (None \<notin> J) * \<alpha>^3) *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y'\<in>UNIV. \<beta> (Some d) *\<^sub>C ket (y', None))
        + (of_bool (None \<notin> J) * \<alpha>\<^sup>2) *\<^sub>C (\<Sum>y'\<in>UNIV. \<beta> None *\<^sub>C ket (y', None))
        \<close>
    (is \<open>_ = ?t1 - ?t2 - ?t3 + ?t4 + ?t5 - ?t6 + ?t7 - ?t8 + ?t9\<close>)
    by (simp add: \<phi>_def \<beta> query1 option_sum_split vimage_Compl
        cblinfun.add_right cblinfun.diff_right if_distrib Compl_eq_Diff_UNIV
        vimage_singleton_inj sum_sum_if_eq sum.distrib scaleC_diff_right scaleC_sum_right
        sum_subtractf case_prod_beta sum.cartesian_product' scaleC_add_right add_diff_eq
        cblinfun.scaleC_right cblinfun.sum_right
        flip: sum.Sigma add.assoc scaleC_scaleC
        cong del: option.case_cong if_cong)

  have norm_t1: \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N)\<close>
  proof - 
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket y'd') \<le> sqrt b\<^sub>i\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto

    have \<open>norm ?t1 = inverse (N\<^sup>2) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket y'd')\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (sqrt N * sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def real_sqrt_mult)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (sqrt N * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (metis bound_J' linordered_field_class.inverse_nonnegative_iff_nonnegative mult.commute mult_right_mono of_nat_0_le_iff of_nat_mono real_sqrt_ge_zero real_sqrt_le_iff)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N)\<close>
      by (smt (verit, del_insts) divide_divide_eq_left divide_inverse mult.commute of_nat_0_le_iff of_nat_power power2_eq_square real_divide_square_eq real_sqrt_pow2 times_divide_eq_left)
    finally show \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N)\<close>
      by -
  qed

  have norm_t2: \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>card {d. \<delta> = the d \<and> d \<in> Some ` I'} \<le> card I'\<close> for \<delta>
      apply (rule card_inj_on_le[where f=the])
      by (auto intro!: inj_onI)
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * I'_def b\<^sub>i order.trans by auto

    have \<open>norm ?t2 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t3: \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have aux: \<open>I' = Some -` I \<Longrightarrow> card (Some -` I) \<le> b\<^sub>i \<Longrightarrow> Some x \<in> I \<Longrightarrow> card {y \<in> I. y \<in> range Some} \<le> b\<^sub>i\<close> for x
      by (smt (verit, ccfv_SIG) Collect_cong Int_iff card_image image_vimage_eq inf_set_def inj_Some mem_Collect_eq)
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d', d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using I'_def b\<^sub>i aux by auto
    have \<open>norm ?t3 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>d\<in>Some ` I'. 
                          \<beta> d *\<^sub>C ket (y\<^sub>0 + the d', d'))\<close>
      apply (simp add: sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t4: \<open>norm ?t4 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have aux: \<open>I' = Some -` I \<Longrightarrow>
         card (Some -` I) \<le> b\<^sub>i \<Longrightarrow> Some x \<in> I \<Longrightarrow> card {y \<in> I. y \<in> range Some} \<le> b\<^sub>i\<close> for x
      by (smt (verit) Collect_cong Int_iff card_image image_vimage_eq inf_set_def inj_Some mem_Collect_eq)
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0, d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using I'_def b\<^sub>i aux by auto

    have \<open>norm ?t4 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>d\<in>Some ` I'. 
                          \<beta> d *\<^sub>C ket (y\<^sub>0, d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t4 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t5: \<open>norm ?t5 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True
    have *: \<open>norm (\<beta> None *\<^sub>C ket (y\<^sub>0 + the d', d')) \<le> sqrt (1::nat)\<close> for d' :: \<open>'y option\<close>
      using \<beta>None by simp

    have \<open>norm ?t5 = inverse (sqrt N) * norm (\<Sum>d' \<in> Some ` (-J').  
                          \<beta> None *\<^sub>C ket (y\<^sub>0 + the d', d'))\<close>
      by (simp add: sum.cartesian_product' sum.reindex)
    also have \<open>\<dots> \<le> inverse (sqrt N) * (sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse (sqrt N) * sqrt b\<^sub>j\<^sub>0\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      by (simp add: divide_inverse_commute True)
    finally show \<open>norm ?t5 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      by -
  next
    case False
    then show ?thesis by (simp add: \<beta>None0)
  qed

  have norm_t6: \<open>norm ?t6 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True
    have *: \<open>norm (\<beta> None *\<^sub>C ket y'd') \<le> 1\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using \<beta>None by simp

    have \<open>norm ?t6 = inverse (N * sqrt N) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<beta> None *\<^sub>C ket y'd')\<close>
      by (simp add: sum.cartesian_product' sum.reindex)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt N * sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def real_sqrt_mult)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt N * sqrt b\<^sub>j\<^sub>0)\<close>
      by (simp add: N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N\<close>
      by (simp add: divide_inverse_commute less_eq_real_def True N_def)
    finally show \<open>norm ?t6 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N\<close>
      by -
  next
    case False
    then show ?thesis by (simp add: \<beta>None0)
  qed

  have norm_t7: \<open>norm ?t7 \<le> of_bool (None\<notin>J) / sqrt N\<close>
  proof (cases \<open>None\<in>J\<close>)
    assume \<open>None \<notin> J\<close>

    have \<open>norm ?t7 = inverse (sqrt N) * norm (\<Sum>d\<in>I'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, None :: 'y option))\<close>
      using \<open>None \<notin> J\<close> by simp
    also have \<open>\<dots> = inverse (sqrt N) * norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, None :: 'y option))\<close>
      apply (subst sum.reindex)
      by auto
    also have \<open>\<dots> \<le> inverse (sqrt N) * (sqrt (real 1))\<close>
    proof -
      have aux: \<open>x \<in> I' \<Longrightarrow> card {y. x = the y \<and> y \<in> Some ` I'} \<le> Suc 0\<close> for x
        by (smt (verit, del_insts) card_eq_Suc_0_ex1 dual_order.refl imageE imageI mem_Collect_eq option.sel)
      show ?thesis
        apply (rule mult_left_mono)
        using _ _ \<beta>bound apply (rule bound_coeff_sum2)
        using aux by auto
    qed
    also have \<open>\<dots> = of_bool (None\<notin>J) / sqrt N\<close>
      using \<open>None \<notin> J\<close> inverse_eq_divide by auto
    finally show ?thesis
      by -
  qed simp

  have norm_t8: \<open>norm ?t8 \<le> of_bool (None\<notin>J) * sqrt b\<^sub>i / N\<close>
  proof (cases \<open>None\<in>J\<close>)
    assume \<open>None \<notin> J\<close>
    have aux: \<open>I' = Some -` I \<Longrightarrow>
         card (Some -` I) \<le> b\<^sub>i \<Longrightarrow> Some x \<in> I \<Longrightarrow> card {y \<in> I. y \<in> range Some} \<le> b\<^sub>i\<close> for x
      by (smt (verit, ccfv_SIG) Collect_cong Int_iff card_image image_vimage_eq inf_set_def inj_Some mem_Collect_eq)
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y', None :: 'y option)) \<le> sqrt (real b\<^sub>i)\<close> for y' :: 'y
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using I'_def b\<^sub>i aux by auto

    have \<open>norm ?t8 = inverse (N * sqrt N) * norm (\<Sum>y'::'y\<in>UNIV. \<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y', None :: 'y option))\<close>
      apply (simp add: sum.reindex \<open>None \<notin> J\<close> N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt N * sqrt (real b\<^sub>i))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def)
    also have \<open>\<dots> = of_bool (None\<notin>J) * sqrt b\<^sub>i / N\<close>
      using \<open>None \<notin> J\<close> inverse_eq_divide
      by (simp add: divide_inverse_commute N_def)
    finally show ?thesis
      by -
  qed simp


  have norm_t9: \<open>norm ?t9 \<le> of_bool (None\<in>I \<and> None\<notin>J) / sqrt N\<close>
  proof (cases \<open>None\<in>I \<and> None\<notin>J\<close>)
    case True

    have \<open>norm ?t9 = inverse N * norm (\<Sum>y'::'y\<in>UNIV. \<beta> None *\<^sub>C ket (y', None :: 'y option))\<close>
      by (simp add: sum.reindex True)
    also have \<open>\<dots> \<le> inverse N * (sqrt N * sqrt 1)\<close>
      apply (rule mult_left_mono)
       apply (rule norm_ortho_sum_bound[where b'=1])
      using \<beta>None by (auto simp: N_def)
    also have \<open>\<dots> = of_bool (None\<in>I \<and> None\<notin>J) / sqrt N\<close>
      using True apply simp
      by (metis divide_inverse_commute inverse_eq_divide of_nat_0_le_iff sqrt_divide_self_eq)
    finally show ?thesis
      by -
  next
    case False with \<beta>None0 
    show ?thesis by auto
  qed

  have \<open>norm (PJ *\<^sub>V \<phi>) \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N) + sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N               +   sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N
                       + sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N            + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N
                       + of_bool (None\<notin>J) / sqrt N        + of_bool (None\<notin>J) * sqrt b\<^sub>i / N       + of_bool (None\<in>I \<and> None\<notin>J) / sqrt N\<close>
    unfolding P0\<phi>
    apply (rule norm_triangle_le_diff norm_triangle_le, rule add_mono)+
            apply (rule norm_t1)
           apply (rule norm_t2)
          apply (rule norm_t3)
         apply (rule norm_t4)
        apply (rule norm_t5)
       apply (rule norm_t6)
      apply (rule norm_t7)
     apply (rule norm_t8)
    apply (rule norm_t9)
    by -
  also have \<open>\<dots> \<le> preserve_query1_fixY_bound (None\<in>I) (None\<notin>J) b\<^sub>i b\<^sub>j\<^sub>0\<close>
    by (auto simp: preserve_query1_fixY_bound_def mult.commute mult.left_commute)
  also have \<open>\<dots> \<le> \<epsilon>\<close>
    by (simp add: \<epsilon>)
  finally show \<open>norm (Proj (- ket_invariant (UNIV \<times> J)) *\<^sub>V \<phi>) \<le> \<epsilon>\<close>
    unfolding PJ_def
    apply (subst ket_invariant_compl[symmetric])
    by simp
qed


definition \<open>preserve_query1'_fixY_bound NoneI NoneJ b\<^sub>i b\<^sub>j\<^sub>0 = sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N) 
  + 2 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N  +  of_bool NoneI * sqrt b\<^sub>j\<^sub>0 / sqrt N + of_bool NoneI * sqrt b\<^sub>j\<^sub>0 / N
   + of_bool NoneJ / sqrt N + of_bool NoneJ * sqrt b\<^sub>i / N + of_bool (NoneI \<and> NoneJ) / sqrt N\<close>
lemma preserve_query1'_fixY: 
  assumes IJ: \<open>I \<subseteq> J\<close>
  assumes b\<^sub>i: \<open>card (Some -` I) \<le> b\<^sub>i\<close>
  assumes b\<^sub>j\<^sub>0: \<open>card (- Some -` J) \<le> b\<^sub>j\<^sub>0\<close>
  assumes \<epsilon>: \<open>\<epsilon> \<ge> preserve_query1'_fixY_bound (None\<in>I) (None\<notin>J) b\<^sub>i b\<^sub>j\<^sub>0\<close>
  (* assumes \<epsilon>nn: \<open>\<epsilon> \<ge> 0\<close> *)
  shows \<open>preserves_ket query1' ({y\<^sub>0} \<times> I) (UNIV \<times> J) \<epsilon>\<close>
proof (rule preservesI')
  show \<open>\<epsilon> \<ge> 0\<close>
    using _ \<epsilon> apply (rule order.trans)
    by (simp add: preserve_query1'_fixY_bound_def)
  fix \<psi> :: \<open>('y \<times> 'y option) ell2\<close>
  assume \<psi>: \<open>\<psi> \<in> space_as_set (ket_invariant ({y\<^sub>0} \<times> I))\<close>
  assume \<open>norm \<psi> = 1\<close>

  define I' J' where \<open>I' = Some -` I\<close> and \<open>J' = Some -` J\<close>
  then have \<open>{y\<^sub>0} \<times> I \<subseteq> {y\<^sub>0} \<times> (Some ` I' \<union> {None})\<close>
    apply (rule_tac Sigma_mono)
    by auto
  with \<psi> have \<psi>': \<open>\<psi> \<in> space_as_set (ket_invariant ({y\<^sub>0} \<times> ((Some ` I' \<union> {None}))))\<close>
    using less_eq_ccsubspace.rep_eq ket_invariant_le by fastforce
  have [simp]: \<open>I' \<subseteq> J'\<close>
    using I'_def J'_def IJ by blast

  define \<beta> where \<open>\<beta> d = Rep_ell2 \<psi> (y\<^sub>0,d)\<close> for d
  then have \<beta>: \<open>\<psi> = (\<Sum>d\<in>Some ` I' \<union> {None}. \<beta> d *\<^sub>C ket (y\<^sub>0,d))\<close>
    using ell2_sum_ket_ket_invariant[OF \<psi>']
    by (auto simp: sum.cartesian_product')
  have \<beta>bound: \<open>(\<Sum>d\<in>(Some ` I' \<union> {None}). (cmod (\<beta> d))\<^sup>2) \<le> 1\<close> (is \<open>?lhs \<le> 1\<close>)
    apply (subgoal_tac \<open>(norm \<psi>)\<^sup>2 = ?lhs\<close>)
     apply (simp add: \<open>norm \<psi> = 1\<close>)
    by (simp add: \<beta> pythagorean_theorem_sum del: sum.insert)
  have \<beta>None: \<open>cmod (\<beta> None) \<le> 1\<close>
  proof -
    have \<open>(cmod (\<beta> None))\<^sup>2 = (\<Sum>d\<in>{None}. (cmod (\<beta> d))\<^sup>2)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Sum>d\<in>(Some ` I' \<union> {None}). (cmod (\<beta> d))\<^sup>2)\<close>
      apply (rule sum_mono2) by auto
    also have \<open>\<dots> \<le> 1\<close>
      by (rule \<beta>bound)
    finally show ?thesis
      by (simp add: power_le_one_iff)
  qed
  have \<beta>None0: \<open>\<beta> None = 0\<close> if \<open>None \<notin> I\<close>
    using \<psi> that by (simp add: \<beta>_def ket_invariant_Rep_ell2)

  have [simp]: \<open>Some -` insert None X = Some -` X\<close> for X :: \<open>'z option set\<close>
    by auto
  have [simp]: \<open>Some -` Some ` X = X\<close> for X :: \<open>'z set\<close>
    by auto
  have [simp]: \<open>Some x \<in> J \<longleftrightarrow> x \<in> J'\<close> for x
    by (simp add: J'_def)
  have [simp]: \<open>x \<in> I' \<Longrightarrow> x \<in> J'\<close> for x
    using \<open>I' \<subseteq> J'\<close> by blast
  have [simp]: \<open>(\<Sum>x\<in>X. if x \<notin> Y then f x else 0) = (\<Sum>x\<in>X-Y. f x)\<close> if \<open>finite X\<close> for f :: \<open>'y \<Rightarrow> 'z::ab_group_add\<close> and X Y
    apply (rule sum.mono_neutral_cong_right)
    using that by auto
  have [simp]: \<open>\<beta> yd *\<^sub>C a *\<^sub>C b = a *\<^sub>C \<beta> yd *\<^sub>C b\<close> for yd a and b :: \<open>'z::complex_vector\<close>
    by auto
  have [simp]: \<open>cmod \<alpha> = inverse (sqrt N)\<close> \<open>cmod (\<alpha>\<^sup>2) = inverse N\<close> \<open>cmod (\<alpha>^3) = inverse (N * sqrt N)\<close> \<open>cmod (\<alpha>^4) = inverse (N\<^sup>2)\<close>
    by (auto simp: norm_mult numeral_3_eq_3 \<alpha>_def inverse_eq_divide norm_divide norm_power power_one_over power2_eq_square power4_eq_xxxx)
  have [simp]: \<open>card (Some ` I') \<le> b\<^sub>i\<close>
    by (metis I'_def b\<^sub>i card_image inj_Some)
  have bound_J'[simp]: \<open>card (Some ` (- J')) \<le> b\<^sub>j\<^sub>0\<close>
      using b\<^sub>j\<^sub>0 unfolding J'_def by (simp add: card_image)

  define \<phi> and PJ :: \<open>('y * 'y option) update\<close> where 
    \<open>\<phi> = query1' *\<^sub>V \<psi>\<close> and \<open>PJ = Proj (ket_invariant (UNIV \<times> -J))\<close>
  have [simp]: \<open>PJ *\<^sub>V ket (x,y) = (if y\<in>-J then ket (x,y) else 0)\<close> for x y
    by (simp add: Proj_ket_invariant_ket PJ_def)
  have P0\<phi>: \<open>PJ *\<^sub>V \<phi> = 
        \<alpha>^4 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (Some d) *\<^sub>C ket (y', Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>- J'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d', Some d'))
        + \<alpha> *\<^sub>C (\<Sum>d'\<in>- J'. \<beta> (None) *\<^sub>C ket (y\<^sub>0 + d', Some d'))
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d'\<in>- J'. \<beta> (None) *\<^sub>C ket (y', Some d'))
        + (of_bool (None \<notin> J) * \<alpha>) *\<^sub>C (\<Sum>d\<in>I'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, None))
        - (of_bool (None \<notin> J) * \<alpha>^3) *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y'\<in>UNIV. \<beta> (Some d) *\<^sub>C ket (y', None))
        + (of_bool (None \<notin> J) * \<alpha>\<^sup>2) *\<^sub>C (\<Sum>y'\<in>UNIV. \<beta> None *\<^sub>C ket (y', None))
        \<close>
    (is \<open>_ = ?t1 - ?t2 - ?t3 + ?t5 - ?t6 + ?t7 - ?t8 + ?t9\<close>)
    by (simp add: \<phi>_def \<beta> query1' option_sum_split vimage_Compl
        cblinfun.add_right cblinfun.diff_right if_distrib Compl_eq_Diff_UNIV
        vimage_singleton_inj sum_sum_if_eq sum.distrib scaleC_diff_right scaleC_sum_right
        sum_subtractf case_prod_beta sum.cartesian_product' scaleC_add_right add_diff_eq
        cblinfun.scaleC_right cblinfun.sum_right
        flip: sum.Sigma add.assoc scaleC_scaleC
        cong del: option.case_cong if_cong)

  have norm_t1: \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N)\<close>
  proof - 
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket y'd') \<le> sqrt b\<^sub>i\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto

    have \<open>norm ?t1 = inverse (N\<^sup>2) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket y'd')\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst (2) sum.swap) apply (subst (3) sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (sqrt N * sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def real_sqrt_mult)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (sqrt N * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (metis bound_J' linordered_field_class.inverse_nonnegative_iff_nonnegative mult.commute mult_right_mono of_nat_0_le_iff of_nat_mono real_sqrt_ge_zero real_sqrt_le_iff)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N)\<close>
      by (smt (verit, del_insts) divide_divide_eq_left divide_inverse mult.commute of_nat_0_le_iff of_nat_power power2_eq_square real_divide_square_eq real_sqrt_pow2 times_divide_eq_left)
    finally show \<open>norm ?t1 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N)\<close>
      by -
  qed

  have norm_t2: \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have *: \<open>card {d. \<delta> = the d \<and> d \<in> Some ` I'} \<le> card I'\<close> for \<delta>
      apply (rule card_inj_on_le[where f=the])
      by (auto intro!: inj_onI)
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using * I'_def b\<^sub>i order.trans by auto

    have \<open>norm ?t2 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t2 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t3: \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
  proof - 
    have aux: \<open>I' = Some -` I \<Longrightarrow> card (Some -` I) \<le> b\<^sub>i \<Longrightarrow> card {y \<in> I. y \<in> range Some} \<le> b\<^sub>i\<close>
      by (smt (verit, ccfv_SIG) Collect_cong Int_iff card_image image_vimage_eq inf_set_def inj_Some mem_Collect_eq)
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d', d')) \<le> sqrt b\<^sub>i\<close> for d' :: \<open>'y option\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using I'_def b\<^sub>i aux by auto

    have \<open>norm ?t3 = inverse (real N) * norm (\<Sum>d' \<in> Some ` (-J'). \<Sum>d\<in>Some ` I'. 
                          \<beta> d *\<^sub>C ket (y\<^sub>0 + the d', d'))\<close>
      apply (simp add: sum.reindex N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (real N) * (sqrt (card (Some ` (- J'))) * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute)
    finally show \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N\<close>
      by -
  qed

  have norm_t5: \<open>norm ?t5 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True
    have *: \<open>norm (\<beta> None *\<^sub>C ket (y\<^sub>0 + the d', d')) \<le> sqrt (1::nat)\<close> for d' :: \<open>'y option\<close>
      using \<beta>None by simp

    have \<open>norm ?t5 = inverse (sqrt N) * norm (\<Sum>d' \<in> Some ` (-J').  
                          \<beta> None *\<^sub>C ket (y\<^sub>0 + the d', d'))\<close>
      by (simp add: sum.cartesian_product' sum.reindex)
    also have \<open>\<dots> \<le> inverse (sqrt N) * (sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> \<le> inverse (sqrt N) * sqrt b\<^sub>j\<^sub>0\<close>
      by (simp add: mult_right_mono N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      by (simp add: divide_inverse_commute True)
    finally show \<open>norm ?t5 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N\<close>
      by -
  next
    case False
    then show ?thesis by (simp add: \<beta>None0)
  qed

  have norm_t6: \<open>norm ?t6 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N\<close>
  proof (cases \<open>None\<in>I\<close>)
    case True
    have *: \<open>norm (\<beta> None *\<^sub>C ket y'd') \<le> 1\<close> for y'd' :: \<open>'y \<times> 'y option\<close>
      using \<beta>None by simp

    have \<open>norm ?t6 = inverse (N * sqrt N) * norm (\<Sum>y'd' \<in> (UNIV::'y set) \<times> Some ` (-J'). \<beta> None *\<^sub>C ket y'd')\<close>
      by (simp add: sum.cartesian_product' sum.reindex)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt N * sqrt (card (Some ` (- J'))))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left real_sqrt_mult N_def)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt N * sqrt b\<^sub>j\<^sub>0)\<close>
      by (simp add: N_def)
    also have \<open>\<dots> \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N\<close>
      by (simp add: divide_inverse_commute less_eq_real_def True N_def)
    finally show \<open>norm ?t6 \<le> of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N\<close>
      by -
  next
    case False
    then show ?thesis by (simp add: \<beta>None0)
  qed

  have norm_t7: \<open>norm ?t7 \<le> of_bool (None\<notin>J) / sqrt N\<close>
  proof (cases \<open>None\<in>J\<close>)
    assume \<open>None \<notin> J\<close>

    have \<open>norm ?t7 = inverse (sqrt N) * norm (\<Sum>d\<in>I'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, None :: 'y option))\<close>
      using \<open>None \<notin> J\<close> by simp
    also have \<open>\<dots> = inverse (sqrt N) * norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, None :: 'y option))\<close>
      apply (subst sum.reindex)
      by auto
    also have \<open>\<dots> \<le> inverse (sqrt N) * (sqrt (real 1))\<close>
    proof -
      have aux: \<open>x \<in> I' \<Longrightarrow> card {y. x = the y \<and> y \<in> Some ` I'} \<le> Suc 0\<close> for x
        by (smt (verit, del_insts) card_eq_Suc_0_ex1 dual_order.refl imageE imageI mem_Collect_eq option.sel)
      show ?thesis
        apply (rule mult_left_mono)
        using _ _ \<beta>bound apply (rule bound_coeff_sum2)
        using aux by auto
    qed
    also have \<open>\<dots> = of_bool (None\<notin>J) / sqrt N\<close>
      using \<open>None \<notin> J\<close> inverse_eq_divide by auto
    finally show ?thesis
      by -
  qed simp

  have norm_t8: \<open>norm ?t8 \<le> of_bool (None\<notin>J) * sqrt b\<^sub>i / N\<close>
  proof (cases \<open>None\<in>J\<close>)
    assume \<open>None \<notin> J\<close>

    have aux: \<open>card (Some -` I) \<le> b\<^sub>i \<Longrightarrow> card {y \<in> I. y \<in> range Some} \<le> b\<^sub>i\<close>
      by (smt (verit, ccfv_SIG) Collect_cong Int_iff card_image image_vimage_eq inf_set_def inj_Some mem_Collect_eq)
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y', None :: 'y option)) \<le> sqrt (real b\<^sub>i)\<close> for y' :: 'y
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using I'_def b\<^sub>i aux by auto

    have \<open>norm ?t8 = inverse (N * sqrt N) * norm (\<Sum>y'::'y\<in>UNIV. \<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y', None :: 'y option))\<close>
      apply (simp add: sum.reindex \<open>None \<notin> J\<close> N_def)
      apply (subst sum.swap) apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt N * sqrt (real b\<^sub>i))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def)
    also have \<open>\<dots> = of_bool (None\<notin>J) * sqrt b\<^sub>i / N\<close>
      using \<open>None \<notin> J\<close> inverse_eq_divide
      by (simp add: divide_inverse_commute N_def)
    finally show ?thesis
      by -
  qed simp

  have norm_t9: \<open>norm ?t9 \<le> of_bool (None\<in>I \<and> None\<notin>J) / sqrt N\<close>
  proof (cases \<open>None\<in>I \<and> None\<notin>J\<close>)
    case True

    have \<open>norm ?t9 = inverse N * norm (\<Sum>y'::'y\<in>UNIV. \<beta> None *\<^sub>C ket (y', None :: 'y option))\<close>
      by (simp add: sum.reindex True)
    also have \<open>\<dots> \<le> inverse N * (sqrt N * sqrt 1)\<close>
      apply (rule mult_left_mono)
       apply (rule norm_ortho_sum_bound[where b'=1])
      using \<beta>None by (auto simp: N_def)
    also have \<open>\<dots> = of_bool (None\<in>I \<and> None\<notin>J) / sqrt N\<close>
      using True apply simp
      by (metis divide_inverse_commute inverse_eq_divide of_nat_0_le_iff sqrt_divide_self_eq)
    finally show ?thesis
      by -
  next
    case False with \<beta>None0 
    show ?thesis by auto
  qed

  have \<open>norm (PJ *\<^sub>V \<phi>) \<le> sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N) + sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N               +   sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N
                                                          + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / sqrt N + of_bool (None\<in>I) * sqrt b\<^sub>j\<^sub>0 / N
                       + of_bool (None\<notin>J) / sqrt N        + of_bool (None\<notin>J) * sqrt b\<^sub>i / N       + of_bool (None\<in>I \<and> None\<notin>J) / sqrt N\<close>
    unfolding P0\<phi>
    apply (rule norm_triangle_le_diff norm_triangle_le, rule add_mono)+
           apply (rule norm_t1)
          apply (rule norm_t2)
         apply (rule norm_t3)
        apply (rule norm_t5)
       apply (rule norm_t6)
      apply (rule norm_t7)
     apply (rule norm_t8)
    apply (rule norm_t9)
    by -
  also have \<open>\<dots> \<le> preserve_query1'_fixY_bound (None\<in>I) (None\<notin>J) b\<^sub>i b\<^sub>j\<^sub>0\<close>
    by (auto simp: preserve_query1'_fixY_bound_def mult.commute mult.left_commute)
  also have \<open>\<dots> \<le> \<epsilon>\<close>
    by (simp add: \<epsilon>)
  finally show \<open>norm (Proj (- ket_invariant (UNIV \<times> J)) *\<^sub>V \<phi>) \<le> \<epsilon>\<close>
    unfolding PJ_def
    apply (subst ket_invariant_compl[symmetric])
    by simp
qed

(* Query1' with Y=fixed (typically Y=0) returns its result. *)
(* Does not exist for query instead of query' because query has a high probability of putting something random and unconnected to Y in D *)


text \<open>The next bound is applicable for ket-invariants assume the output register to have a specific value
\<^term>\<open>ket y\<^sub>0\<close> (typically \<^term>\<open>ket 0\<close>) before the query and require that after the query,
the oracle register is not \<^const>\<open>None\<close> and the output register has the correct value given that
oracle register content.

Notice that this invariant is only available for \<^const>\<open>query1'\<close>, not for \<^const>\<open>query1\<close>!\<close>


definition \<open>preserve_query1'_fixY_bound_output b\<^sub>i = 4 / sqrt N + 2 * sqrt b\<^sub>i / N\<close>
lemma preserve_query1'_fixY_output: 
  assumes b\<^sub>i: \<open>card (Some -` I) \<le> b\<^sub>i\<close>
  assumes \<epsilon>: \<open>\<epsilon> \<ge> preserve_query1'_fixY_bound_output b\<^sub>i\<close>
  shows \<open>preserves_ket query1' ({y\<^sub>0} \<times> I) {(y\<^sub>0+d, Some d)| d. True} \<epsilon>\<close>
proof (rule preservesI')
  show \<open>\<epsilon> \<ge> 0\<close>
    using _ \<epsilon> apply (rule order.trans)
    by (simp add: preserve_query1'_fixY_bound_output_def)
  fix \<psi> :: \<open>('y \<times> 'y option) ell2\<close>
  assume \<psi>: \<open>\<psi> \<in> space_as_set (ket_invariant ({y\<^sub>0} \<times> I))\<close>
  assume \<open>norm \<psi> = 1\<close>

  define I' where \<open>I' = Some -` I\<close>
  then have \<open>{y\<^sub>0} \<times> I \<subseteq> {y\<^sub>0} \<times> (Some ` I' \<union> {None})\<close>
    apply (rule_tac Sigma_mono)
    by auto
  with \<psi> have \<psi>': \<open>\<psi> \<in> space_as_set (ket_invariant ({y\<^sub>0} \<times> ((Some ` I' \<union> {None}))))\<close>
    using less_eq_ccsubspace.rep_eq ket_invariant_le by fastforce

  define \<beta> where \<open>\<beta> d = Rep_ell2 \<psi> (y\<^sub>0,d)\<close> for d
  then have \<beta>: \<open>\<psi> = (\<Sum>d\<in>Some ` I' \<union> {None}. \<beta> d *\<^sub>C ket (y\<^sub>0,d))\<close>
    using ell2_sum_ket_ket_invariant[OF \<psi>']
    by (auto simp: sum.cartesian_product')
  have \<beta>bound: \<open>(\<Sum>d\<in>(Some ` I' \<union> {None}). (cmod (\<beta> d))\<^sup>2) \<le> 1\<close> (is \<open>?lhs \<le> 1\<close>)
    apply (subgoal_tac \<open>(norm \<psi>)\<^sup>2 = ?lhs\<close>)
     apply (simp add: \<open>norm \<psi> = 1\<close>)
    by (simp add: \<beta> pythagorean_theorem_sum del: sum.insert)
  have \<beta>bound1[simp]: \<open>cmod (\<beta> x) \<le> 1\<close> for x
    using norm_point_bound_ell2[of \<psi>] \<open>norm \<psi> = 1\<close> unfolding \<beta>_def by auto

  have [simp]: \<open>Some -` insert None X = Some -` X\<close> for X :: \<open>'z option set\<close>
    by auto
  have [simp]: \<open>Some -` Some ` X = X\<close> for X :: \<open>'z set\<close>
    by auto
  have [simp]: \<open>\<beta> yd *\<^sub>C a *\<^sub>C b = a *\<^sub>C \<beta> yd *\<^sub>C b\<close> for yd a and b :: \<open>'z::complex_vector\<close>
    by auto
  have [simp]: \<open>cmod \<alpha> = inverse (sqrt N)\<close> \<open>cmod (\<alpha>\<^sup>2) = inverse N\<close> \<open>cmod (\<alpha>^3) = inverse (N * sqrt N)\<close> \<open>cmod (\<alpha>^4) = inverse (N\<^sup>2)\<close>
    by (auto simp: norm_mult numeral_3_eq_3 \<alpha>_def inverse_eq_divide norm_divide norm_power power_one_over power4_eq_xxxx power2_eq_square)
  have [simp]: \<open>card (Some ` I') \<le> b\<^sub>i\<close>
    by (metis I'_def b\<^sub>i card_image inj_Some)

  define \<phi> and PJ :: \<open>('y * 'y option) update\<close> where 
    \<open>\<phi> = query1' *\<^sub>V \<psi>\<close> and \<open>PJ = Proj (ket_invariant (- {(y\<^sub>0+d, Some d)| d. True}))\<close>
  have aux: \<open>\<forall>d. y \<noteq> y\<^sub>0 + d \<Longrightarrow> d \<noteq> Some (y\<^sub>0 + y)\<close> for d y
    by (metis add.right_neutral y_cancel ordered_field_class.sign_simps(1))
  then have [simp]: \<open>PJ *\<^sub>V ket (y,d) = (if Some (y\<^sub>0 + y) = d then 0 else ket (y,d))\<close> for y d
    by (auto simp add: Proj_ket_invariant_ket PJ_def)
  have P0\<phi>: \<open>PJ *\<^sub>V \<phi> = 
      \<alpha> *\<^sub>C (\<Sum>d\<in>I'. \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, None))
    - \<alpha>^3 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y\<in>UNIV. \<beta> (Some d) *\<^sub>C ket (y, None))
    - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>UNIV. if d=d' then 0 else \<beta> (Some d) *\<^sub>C ket (y\<^sub>0 + d, Some d'))
    + \<alpha>^4 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y\<in>UNIV. \<Sum>d'\<in>UNIV. if y\<^sub>0+y=d' then 0 else \<beta> (Some d) *\<^sub>C ket (y, Some d'))
    - \<alpha>^3 *\<^sub>C (\<Sum>y\<in>UNIV. \<Sum>d'\<in>UNIV. if y\<^sub>0+y=d' then 0 else \<beta> None *\<^sub>C ket (y, Some d'))
    + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>y\<in>UNIV. \<beta> None *\<^sub>C ket (y, None))\<close>
    (is \<open>_ = ?t1 - ?t2 - ?t3 + ?t4 - ?t5 + ?t6\<close>)

    by (simp add: \<phi>_def \<beta> query1' option_sum_split vimage_Compl of_bool_def cblinfun.sum_right
        cblinfun.add_right cblinfun.diff_right if_distrib Compl_eq_Diff_UNIV cblinfun.scaleC_right
        vimage_singleton_inj sum_sum_if_eq sum.distrib scaleC_diff_right scaleC_sum_right
        sum_subtractf case_prod_beta sum.cartesian_product' scaleC_add_right add_diff_eq
        flip: sum.Sigma add.assoc scaleC_scaleC
        cong del: option.case_cong if_cong)

  have norm_t1: \<open>norm ?t1 \<le> 1 / sqrt N\<close>
  proof - 
    have \<open>norm ?t1 = inverse (sqrt N) * norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, None :: 'y option))\<close>
      by (simp add: sum.reindex)
    also have \<open>\<dots> \<le> inverse (sqrt N) * sqrt (1::nat)\<close>
    proof -
      have aux: \<open>x \<in> I' \<Longrightarrow> card {y. x = the y \<and> y \<in> Some ` I'} \<le> Suc 0\<close> for x
        by (smt (verit, del_insts) card_eq_Suc_0_ex1 imageE imageI le_refl mem_Collect_eq option.sel)
      show ?thesis
        apply (rule mult_left_mono)
        using _ _ \<beta>bound apply (rule bound_coeff_sum2)
        using aux by auto
    qed
    also have \<open>\<dots> = 1 / sqrt N\<close>
      apply simp
      using inverse_eq_divide by blast
    finally show \<open>norm ?t1 \<le> 1 / sqrt N\<close>
      by -
  qed

  have norm_t2: \<open>norm ?t2 \<le> sqrt b\<^sub>i / N\<close>
  proof -
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y, None :: 'y option)) \<le> sqrt b\<^sub>i\<close> for y :: 'y
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto
      
    have \<open>norm ?t2 = inverse (N * sqrt N) * norm (\<Sum>y\<in>UNIV. \<Sum>d\<in>Some ` I'. \<beta> d *\<^sub>C ket (y :: 'y, None :: 'y option))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt (real N) * sqrt (real b\<^sub>i))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def)
    also have \<open>\<dots> = sqrt b\<^sub>i / N\<close>
      by (simp add: divide_inverse_commute N_def)
    finally show ?thesis
      by auto
  qed

  have norm_t3: \<open>norm ?t3 \<le> 1 / sqrt N\<close>
  proof -
    have aux: \<open>card {y. x = the y \<and> y \<in> Some ` (I' - {d'})} \<le> Suc 0\<close> for x d'
      by (smt (verit, best) Collect_empty_eq bot_nat_0.not_eq_extremum card.empty card_eq_Suc_0_ex1 imageE le_simps(3) mem_Collect_eq nat_le_linear option.sel)
    have *: \<open>norm (\<Sum>d\<in>Some ` (I' - {d'}). \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, Some d')) \<le> sqrt (1::nat)\<close> for d'
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      using aux[of _ d'] by auto

    have \<open>norm ?t3 = inverse N * norm (\<Sum>d'\<in>UNIV. \<Sum>d\<in>Some ` (I'-{d'}). \<beta> d *\<^sub>C ket (y\<^sub>0 + the d, Some d'))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex)
      apply (subst sum.swap)
      apply (simp add: sum_if_eq_else)
      by -
    also have \<open>\<dots> \<le> inverse N * sqrt N\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def)
    also have \<open>\<dots> = 1 / sqrt N\<close>
      by (simp add: inverse_eq_divide sqrt_divide_self_eq)
    finally show ?thesis
      by -
  qed

  have norm_t4: \<open>norm ?t4 \<le> sqrt (real b\<^sub>i) / N\<close>
  proof -
    have *: \<open>norm (\<Sum>d\<in>Some ` I'. if y\<^sub>0 + fst yd' = snd yd' then 0 else \<beta> d *\<^sub>C ket (fst yd', Some (snd yd'))) \<le> sqrt b\<^sub>i\<close> for yd'
      apply (cases \<open>y\<^sub>0 + fst yd' = snd yd'\<close>)
       apply simp
      apply simp
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto

    note if_cong[cong del]

    have \<open>norm ?t4 = inverse (N\<^sup>2) * norm (\<Sum>yd'\<in>UNIV. \<Sum>d\<in>Some ` I'. if y\<^sub>0 + fst yd' = snd yd' then 0 else \<beta> d *\<^sub>C ket (fst yd', Some (snd yd')))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def flip: UNIV_Times_UNIV)
      apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (real N * sqrt (real b\<^sub>i))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left cinner_ket N_def
          if_distrib[where f=\<open>\<lambda>x. cinner _ x\<close>] if_distrib[where f=\<open>\<lambda>x. cinner x _\<close>])
    also have \<open>\<dots> \<le> sqrt (real b\<^sub>i) / N\<close>
      by (metis divide_inverse_commute dual_order.refl of_nat_mult power2_eq_square real_divide_square_eq)
    finally show ?thesis
      by -
  qed

  have norm_t5: \<open>norm ?t5 \<le> 1 / sqrt N\<close>
  proof -
    have \<open>norm ?t5 = inverse (N * sqrt N) * norm (\<Sum>yd\<in>UNIV. if y\<^sub>0 + fst yd = snd yd then 0 else \<beta> None *\<^sub>C ket (fst yd, Some (snd yd)))\<close>
      by (simp add: sum.cartesian_product' sum.reindex flip: UNIV_Times_UNIV cong del: if_cong)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * N\<close>
      apply (rule mult_left_mono)
       apply (rule norm_ortho_sum_bound[where b'=1])
      by (auto simp: N_def)
    also have \<open>\<dots> = 1 / sqrt N\<close>
      by (simp add: divide_inverse_commute N_def)
    finally show ?thesis
      by -
  qed

  have norm_t6: \<open>norm ?t6 \<le> 1 / sqrt N\<close>
  proof -
    have \<open>norm ?t6 = inverse N * norm (\<Sum>y\<in>UNIV. \<beta> None *\<^sub>C ket (y :: 'y, None :: 'y option))\<close>
      by simp
    also have \<open>\<dots> \<le> inverse N * sqrt N\<close>
      apply (rule mult_left_mono)
       apply (rule norm_ortho_sum_bound[where b'=1])
      by (auto simp: N_def)
    also have \<open>\<dots> = 1 / sqrt N\<close>
      by (simp add: inverse_eq_divide sqrt_divide_self_eq)
    finally show ?thesis
      by -
  qed

  have \<open>norm (PJ *\<^sub>V \<phi>) \<le> 1 / sqrt N          +   sqrt b\<^sub>i / N   +   1 / sqrt N
                       + sqrt (real b\<^sub>i) / N   +   1 / sqrt N   +   1 / sqrt N\<close>
    unfolding P0\<phi>
    apply (rule norm_triangle_le_diff norm_triangle_le, rule add_mono)+
         apply (rule norm_t1)
        apply (rule norm_t2)
       apply (rule norm_t3)
      apply (rule norm_t4)
     apply (rule norm_t5)
    apply (rule norm_t6)
    by -
  also have \<open>\<dots> \<le> preserve_query1'_fixY_bound_output b\<^sub>i\<close>
    by (auto simp: preserve_query1'_fixY_bound_output_def mult.commute mult.left_commute)
  also have \<open>\<dots> \<le> \<epsilon>\<close>
    by (simp add: \<epsilon>)
  finally show \<open>norm (Proj (- ket_invariant {(y\<^sub>0 + d, Some d) |d. True}) *\<^sub>V \<phi>) \<le> \<epsilon>\<close>
    unfolding PJ_def
    apply (subst ket_invariant_compl[symmetric])
    by simp
qed


text \<open>A simpler to understand (and sometimes simpler to use) special case of
  @{thm [source] preserve_query1'_fixY_output} in terms of \<^const>\<open>query'\<close> and ket-invariants.\<close>
lemma (in compressed_oracle) preserves_ket_query'_output_simple:
  \<open>preserves_ket query' {(x, y, D). y = 0} {(x, y, D). D x = Some y} (6 / sqrt N)\<close>
proof -
  define K :: \<open>'x \<Rightarrow> ('x \<times> 'y \<times> ('x \<Rightarrow> 'y option)) ell2 ccsubspace\<close> where \<open>K x = lift_invariant reg_1_3 (ket_invariant {x})\<close> for x
  
  show ?thesis
  proof (rule inv_split_reg_query'[where X=\<open>reg_1_3\<close> and Y=\<open>reg_2_3\<close> and H=\<open>reg_3_3\<close> and K=K
        and ?I1.0=\<open>\<lambda>_. ket_invariant ({0} \<times> UNIV)\<close> and ?J1.0=\<open>\<lambda>_. ket_invariant {(0+d, Some d)| d. True}\<close>])
    show \<open>query' = (reg_1_3;(reg_2_3;reg_3_3)) query'\<close>
      by (auto simp add: pair_Fst_Snd reg_1_3_def reg_2_3_def reg_3_3_def) 
    show \<open>compatible reg_1_3 reg_2_3\<close> \<open>compatible reg_1_3 reg_3_3\<close> \<open>compatible reg_2_3 reg_3_3\<close>
      by simp_all
    show \<open>compatible_register_invariant reg_2_3 (K x)\<close> for x
      by (auto intro!: compatible_register_invariant_compatible_register simp add: K_def)
    show \<open>compatible_register_invariant (reg_3_3 o function_at x) (K x)\<close> for x
      by (auto intro!: compatible_register_invariant_compatible_register simp add: K_def)
    show \<open>ket_invariant {(x, y, D). y = 0}
          \<le> (SUP x. K x \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) (ket_invariant ({0} \<times> UNIV)))\<close>
      apply (simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          lift_inv_prod' lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv case_prod_unfold)
      by force
    show \<open>K x \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) (ket_invariant {(0+d, Some d)| d. True})
          \<le> ket_invariant {(x, y, D). D x = Some y}\<close> for x
      apply (simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          lift_inv_prod' lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv
          case_prod_unfold)
      by fastforce
    show \<open>orthogonal_spaces (K x) (K x')\<close> if \<open>x \<noteq> x'\<close> for x x'
      using that by (auto simp add: K_def orthogonal_spaces_lift_invariant)
    show \<open>preserves_ket query1' ({0} \<times> UNIV) {(0+d, Some d)| d. True} (6 / sqrt N)\<close>
      apply (rule preserve_query1'_fixY_output[where b\<^sub>i=N])
      by (auto intro!: simp: preserve_query1'_fixY_bound_output_def simp flip: N_def)
    show \<open>K x \<le> lift_invariant reg_1_3 (ket_invariant {x})\<close> for x
      by (simp add: K_def)
    show \<open>6 / sqrt N \<ge> 0\<close>
      by simp
  qed simp
qed

text \<open>A strengthened form of @{thm [source] preserves_ket_query'_output_simple} that additionally maintains
  a property \<^term>\<open>P\<close> on the already existing oracle register (that can depend also on some auxiliary register
  and on the query input register).

  This comes with the condition on \<^term>\<open>P\<close> that when \<^term>\<open>P\<close> accepts some oracle function that is undefined
  at the query input \<^term>\<open>x\<close>, then it needs to accept the updated oracle function with any output at \<^term>\<open>x\<close>.
  And if \<^term>\<open>P\<close> doesn't accept the oracle function to be undefined at \<^term>\<open>x\<close>, then it must accept 
  either only a small amount of outputs or all but a small amount of outputs for \<^term>\<open>x\<close>.\<close>

lemma (in compressed_oracle) preserves_ket_query'_output:
  fixes F :: \<open>('x\<times>'y\<times>('x\<rightharpoonup>'y)) update \<Rightarrow> 'mem update\<close>
    and P :: \<open>'w::finite \<Rightarrow> 'x \<Rightarrow> ('x\<rightharpoonup>'y) \<Rightarrow> bool\<close>
    and b :: nat
  assumes [register]: \<open>register G\<close>
  assumes \<open>F = G o Snd\<close>
  assumes PNone: \<open>\<And>w x D. P w x (D(x:=None)) \<Longrightarrow> P w x D\<close>
  assumes PSome: \<open>\<And>w x D. D x = None \<Longrightarrow> \<not> P w x D \<Longrightarrow> let c = card {y. P w x (D(x:=Some y))} in c*(N-c) \<le> b\<close>
  shows \<open>preserves (F query') (lift_invariant G (ket_invariant {(w, x, y, D). y = 0 \<and> P w x D}))
                              (lift_invariant G (ket_invariant {(w, x, y, D). D x = Some y \<and> P w x D}))
                              (9 / sqrt N + 2 * sqrt b / N)\<close>
proof -
  define K :: \<open>'w\<times>'x\<times>('x\<rightharpoonup>'y) \<Rightarrow> 'mem ell2 ccsubspace\<close> where
    \<open>K = (\<lambda>(w,x,D). lift_invariant G (ket_invariant {(w, x, y, D') | y D'. D'(x:=None) = D}))\<close>
  define M :: \<open>('w\<times>'x\<times>('x\<rightharpoonup>'y)) set\<close> where
    \<open>M = {(w,x,D). D x = None}\<close>
  define I1 :: \<open>'w\<times>'x\<times>('x\<rightharpoonup>'y) \<Rightarrow> ('y \<times> 'y option) ell2 ccsubspace\<close> where
    \<open>I1 = (\<lambda>(w,x,D). ket_invariant {(0, y) | y. P w x (D(x:=y))})\<close>
  define J1 :: \<open>'w\<times>'x\<times>('x\<rightharpoonup>'y) \<Rightarrow> ('y \<times> 'y option) ell2 ccsubspace\<close> where
    \<open>J1 = (\<lambda>(w,x,D). ket_invariant {(y, Some y) | y. P w x (D(x:=Some y))})\<close>

  show ?thesis
  proof (rule inv_split_reg_query'[where X=\<open>G o Snd o reg_1_3\<close> and Y=\<open>G o Snd o reg_2_3\<close> and H=\<open>G o Snd o reg_3_3\<close>
        and K=K and ?I1.0=I1 and ?J1.0=J1 and M=M])
    show \<open>F query' = (G \<circ> Snd \<circ> reg_1_3;(G \<circ> Snd \<circ> reg_2_3;G \<circ> Snd \<circ> reg_3_3)) query'\<close>
      unfolding reg_1_3_def reg_2_3_def reg_3_3_def assms
      by (simp flip: comp_assoc)
    show \<open>compatible (G \<circ> Snd \<circ> reg_1_3) (G \<circ> Snd \<circ> reg_2_3)\<close> \<open>compatible (G \<circ> Snd \<circ> reg_1_3) (G \<circ> Snd \<circ> reg_3_3)\<close> \<open>compatible (G \<circ> Snd \<circ> reg_2_3) (G \<circ> Snd \<circ> reg_3_3)\<close>
      by simp_all
    show \<open>compatible_register_invariant (G \<circ> Snd \<circ> reg_2_3) (K wxD)\<close> if \<open>wxD \<in> M\<close> for wxD
       by (auto intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_Fst 
           simp add: K_def assms compatible_register_invariant_chain reg_2_3_def
          comp_assoc M_def split!: prod.split)
    show \<open>compatible_register_invariant ((G \<circ> Snd o reg_3_3) o function_at (let (w,x,D) = wxD in x)) (K wxD)\<close> if \<open>wxD \<in> M\<close> for wxD
      by (auto intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_function_at
          simp add: K_def compatible_register_invariant_chain comp_assoc reg_3_3_def
          split!: prod.split)
    show \<open>lift_invariant G (ket_invariant {(w, x, y, D). y = 0 \<and> P w x D})
          \<le> (\<Squnion>wxD\<in>M. K wxD \<sqinter> lift_invariant (G \<circ> Snd \<circ> reg_2_3;G \<circ> Snd \<circ> reg_3_3 \<circ> function_at (let (w, x, D) = wxD in x)) (I1 wxD))\<close>
      by (auto intro!: lift_invariant_mono
          simp add: K_def M_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric] register_comp_pair
          comp_assoc I1_def 
          lift_inv_prod' lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv case_prod_unfold
          simp flip: lift_invariant_inf lift_invariant_SUP
          split!: prod.split)
    have aux: \<open>D'(fst (snd wxD) := None) = snd (snd wxD) \<Longrightarrow>
       D' (fst (snd wxD)) = Some ya \<Longrightarrow>
       P (fst wxD) (fst (snd wxD)) ((snd (snd wxD))(fst (snd wxD) \<mapsto> ya)) \<Longrightarrow>
       P (fst wxD) (fst (snd wxD)) D'\<close> for wxD D' ya
      by (metis fun_upd_triv fun_upd_upd)
    show \<open>K wxD \<sqinter> lift_invariant (G \<circ> Snd \<circ> reg_2_3;G \<circ> Snd \<circ> reg_3_3 \<circ> function_at (let (w, x, D) = wxD in x)) (J1 wxD)
         \<le> lift_invariant G (ket_invariant {(w, x, y, D). D x = Some y \<and> P w x D})\<close> if \<open>wxD \<in> M\<close> for wxD
      using that
      by (auto intro!: aux lift_invariant_mono
          simp add: K_def J1_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          lift_inv_prod' Times_Int_Times lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv
          lift_invariant_comp register_comp_pair lift_Snd_inv
          comp_assoc case_prod_unfold ket_invariant_tensor
          simp flip: lift_invariant_inf ket_invariant_SUP ket_invariant_UNIV 
          split!: prod.split)
    show \<open>orthogonal_spaces (K wxD) (K wxD')\<close> if \<open>wxD \<in> M\<close> and \<open>wxD' \<in> M\<close> and \<open>wxD \<noteq> wxD'\<close> for wxD wxD'
      using that
      by (auto simp add: K_def orthogonal_spaces_lift_invariant M_def split!: prod.split)
    show \<open>preserves query1' (I1 wxD) (J1 wxD) (9 / sqrt N + 2 * sqrt b / N)\<close> if \<open>wxD \<in> M\<close> for wxD
    proof -
      obtain w x D where wxD[simp]: \<open>wxD = (w,x,D)\<close>
        by (simp add: prod_eq_iff)
      from that
      have Dx: \<open>D x = None\<close>
        by (simp add: M_def)
      have I1: \<open>I1 (w,x,D) = ket_invariant ({0} \<times> {y. P w x (D(x := y))})\<close>
        by (auto simp add: I1_def)
      have presY: \<open>preserves query1' (I1 wxD) (ket_invariant {(0+d, Some d)| d. True}) (6 / sqrt (real N))\<close> 
        apply (simp only: wxD I1)
        apply (rule preserve_query1'_fixY_output[where b\<^sub>i=N])
         apply (simp add: N_def card_mono)
        using sqrt_divide_self_eq 
        by (simp add: preserve_query1'_fixY_bound_output_def divide_inverse flip: N_def)
      have presP1: \<open>preserves query1' (I1 wxD) (ket_invariant (UNIV \<times> {y. P w x (D(x := y))})) (3 / sqrt N + 2 * sqrt b / N)\<close> 
        if \<open>\<not> P w x D\<close>
      proof -
        from that Dx PNone have NoneI: \<open>(None \<in> {y. P w x (D(x := y))}) = False\<close>
          by auto
        from that Dx PNone have NoneJ: \<open>(None \<notin> {y. P w x (D(x := y))}) = True\<close>
          by auto
        define b\<^sub>i where \<open>b\<^sub>i = card (Some -` {y. P w x (D(x := y))})\<close>
        define b\<^sub>j\<^sub>0 where \<open>b\<^sub>j\<^sub>0 = card (- Some -` {y. P w x (D(x := y))})\<close>
        have \<open>sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N) + 2 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N + 1 / sqrt N + sqrt b\<^sub>i / N
                      \<le> 3 / sqrt N + 2 * sqrt b / N\<close>
        proof -
          have \<open>b\<^sub>j\<^sub>0 = N - b\<^sub>i\<close>
            by (simp add: N_def b\<^sub>i_def b\<^sub>j\<^sub>0_def card_complement)
          then have \<open>b\<^sub>i * b\<^sub>j\<^sub>0 \<le> b\<close>
            using PSome[of D x w] that
            by (auto intro!: simp: b\<^sub>i_def Let_def Dx)
          have \<open>b\<^sub>i \<le> N\<close>
            apply (simp add: b\<^sub>i_def)
            by (metis N_def card_complement diff_le_self double_complement)
          have bbN: \<open>sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i \<le> N\<close>
            using \<open>b\<^sub>i \<le> N\<close> \<open>b\<^sub>j\<^sub>0 = N - b\<^sub>i\<close> 
            by (smt (verit, best) Extra_Ordered_Fields.sign_simps(5) of_nat_0_le_iff of_nat_diff
                ordered_comm_semiring_class.comm_mult_left_mono real_sqrt_ge_0_iff sqrt_sqrt)
          have bbb: \<open>sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i \<le> sqrt b\<close>
            using  \<open>b\<^sub>i * b\<^sub>j\<^sub>0 \<le> b\<close>
            by (smt (verit) Num.of_nat_simps(5) cross3_simps(11) of_nat_mono real_sqrt_le_iff real_sqrt_mult)
          have sqrtNN: \<open>sqrt N / N = 1 / sqrt N\<close>
            by (metis div_by_1 inverse_divide of_nat_0_le_iff real_div_sqrt)
          have \<open>sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / (N * sqrt N) + 2 * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i / N + 1 / sqrt N + sqrt b\<^sub>i / N
             \<le> N / (N * sqrt N) + 2 * sqrt b / N + 1 / sqrt N + sqrt N / N\<close>
            apply (intro add_mono divide_right_mono)
            by (auto intro!: \<open>b\<^sub>i \<le> N\<close> bbN bbb)
          also have \<open>\<dots> = 3 / sqrt N + 2 * sqrt b / N\<close>
            by (simp add: nonzero_divide_mult_cancel_left sqrtNN)
          finally show ?thesis
            by -
        qed
        then show ?thesis
          apply (simp only: wxD I1)
          apply (rule preserve_query1'_fixY[where b\<^sub>i=b\<^sub>i and b\<^sub>j\<^sub>0=b\<^sub>j\<^sub>0])
          unfolding NoneI
          by (simp_all add: b\<^sub>i_def b\<^sub>j\<^sub>0_def preserve_query1'_fixY_bound_def)
      qed
      have presP2: \<open>preserves query1' (I1 wxD) (ket_invariant (UNIV \<times> {y. P w x (D(x := y))})) (3 / sqrt N + 2 * sqrt b / N)\<close> 
        if \<open>P w x D\<close>
        apply (rewrite at \<open>{y. P w x (D(x := y))}\<close> to UNIV DEADID.rel_mono_strong)
        using that PNone Dx apply (metis UNIV_eq_I array_rules(5) fun_upd_triv mem_Collect_eq)
        by auto
      from presP1 presP2
      have presP: \<open>preserves query1' (I1 wxD) (ket_invariant (UNIV \<times> {y. P w x (D(x := y))})) (3 / sqrt N + 2 * sqrt b / N)\<close>
        by auto
      from preserves_intersect[OF _ presY presP]
      have \<open>preserves query1' (I1 wxD) (ket_invariant {(0 + d, Some d) |d. True} \<sqinter> ket_invariant (UNIV \<times> {y. P w x (D(x := y))}))
            ((6 / sqrt N) + (3 / sqrt N + 2 * sqrt b / N))\<close>
        by auto
      then show ?thesis
        apply (rule arg_cong4[where f=preserves, THEN iffD1, rotated -1])
        by (auto intro!: simp: ket_invariant_inter J1_def)
    qed
    show \<open>K wxD \<le> lift_invariant (G \<circ> Snd \<circ> reg_1_3) (ket_invariant {let (w, x, D) = wxD in x})\<close> for wxD
      by (auto intro!: lift_invariant_mono 
          simp add: K_def lift_invariant_comp reg_1_3_def lift_Fst_ket_inv lift_Snd_ket_inv
          split!: prod.split)
    show \<open>9 / sqrt N + 2 * sqrt b / N \<ge> 0\<close>
      by simp
    show \<open>finite M\<close>
      by simp
  qed
qed

text \<open>This is an example of how @{thm [source] preserves_ket_query'_output} is used to deal with more complex query sequences.
It is also useful in its own right (we use it in \<open>Collision.thy\<close>).

It shows that if we make two queries, then the oracle function contains the outputs of both queries.
(In contrast, @{thm [source] preserves_ket_query'_output_simple} shows this only for a single query.)\<close>

lemma dist_inv_double_query':
  fixes X1 X2 Y1 Y2 H and state1 :: \<open>'mem ell2\<close>
  defines \<open>state2 \<equiv> (X1;(Y1;H)) query' *\<^sub>V state1\<close>
  defines \<open>state3 \<equiv> (X2;(Y2;H)) query' *\<^sub>V state2\<close>
  assumes [register]: \<open>mutually compatible (X1,X2,Y1,Y2,H)\<close>
  assumes [iff]: \<open>norm state1 \<le> 1\<close>
  assumes dist1: \<open>dist_inv ((X1;X2);((Y1;Y2);H)) (ket_invariant {((x1,x2),(y1,y2),D). y1 = 0 \<and> y2 = 0}) state1 \<le> \<epsilon>\<close>
  shows \<open>dist_inv ((X1;X2);((Y1;Y2);H)) (ket_invariant {((x1,x2),(y1,y2),D). D x1 = Some y1 \<and> D x2 = Some y2}) state3 \<le> \<epsilon> + 20 / sqrt N\<close>
proof -
  have [iff]: \<open>norm state2 \<le> 1\<close>
    by (auto intro!: norm_cblinfun_apply_leq1I simp add: state2_def register_norm)
  have bound: \<open>let c = card {y2. (x' = x2 \<longrightarrow> y2 = y') \<and> x' = x2} in c * (N - c) \<le> N\<close> for x' x2 y'
    by (cases \<open>x' = x2\<close>, auto)
  from dist1 have \<open>dist_inv ((X2; Y2); (X1;(Y1;H)))
                   (ket_invariant {(x2y2,(x1,y1,D)). y1 = 0 \<and> snd x2y2 = 0}) state1 \<le> \<epsilon>\<close>
    apply (rule le_back_subst)
    apply (rule dist_inv_register_rewrite, simp, simp)
    apply (rewrite at \<open>((X2;Y2);(X1;(Y1;H)))\<close> to \<open>((X1;X2);((Y1;Y2);H)) o ((reg_1_3 o Snd; reg_2_3 o Snd); (reg_1_3 o Fst; (reg_2_3 o Fst; reg_3_3)))\<close> DEADID.rel_mono_strong)
     apply (simp add: register_pair_Snd register_pair_Fst flip: register_comp_pair comp_assoc)
    apply (subst lift_invariant_comp, simp)
    apply simp
    by (auto intro!: simp: lift_inv_prod' reg_1_3_def reg_3_3_def reg_2_3_def lift_invariant_comp lift_Snd_ket_inv lift_Fst_ket_inv
        ket_invariant_inter  case_prod_unfold 
        simp flip: ket_invariant_SUP)
  then have \<open>dist_inv ((X2; Y2); (X1;(Y1;H)))
                   (ket_invariant {(x2y2,(x1,y1,D)). D x1 = Some y1 \<and> snd x2y2 = 0}) state2 \<le> \<epsilon> + 9 / sqrt (real N)\<close>
    unfolding state2_def
    apply (rule dist_inv_preservesI)
         apply (rule preserves_ket_query'_output[where b=0])
    by (auto intro!: simp: register_pair_Snd register_norm simp del: o_apply)
  then have \<open>dist_inv ((X1; Y1); (X2;(Y2;H)))
                   (ket_invariant {(x1y1,(x2,y2,D)). y2 = 0 \<and> D (fst x1y1) = Some (snd x1y1)}) state2 \<le> \<epsilon> + 9 / sqrt (real N)\<close>
    apply (rule le_back_subst)
    apply (rule dist_inv_register_rewrite, simp, simp)
    apply (rewrite at \<open>((X1; Y1); (X2;(Y2;H)))\<close> to \<open>((X2; Y2); (X1;(Y1;H))) o ((Snd o reg_1_3; Snd o reg_2_3); (Fst o Fst; (Fst o Snd; Snd o reg_3_3)))\<close> DEADID.rel_mono_strong)
     apply (simp add: register_pair_Snd register_pair_Fst flip: register_comp_pair comp_assoc)
    apply (subst lift_invariant_comp, simp)
    apply simp
    by (auto intro!: simp: lift_inv_prod' reg_1_3_def reg_3_3_def reg_2_3_def lift_invariant_comp lift_Snd_ket_inv lift_Fst_ket_inv
        ket_invariant_inter  case_prod_unfold 
        simp flip: ket_invariant_SUP)
  then have \<open>dist_inv ((X1; Y1); (X2;(Y2;H)))
                   (ket_invariant {(x1y1,(x2,y2,D)). D x2 = Some y2 \<and> D (fst x1y1) = Some (snd x1y1)}) state3 \<le> \<epsilon> + 20 / sqrt N\<close>
    unfolding state3_def
    apply (rule dist_inv_preservesI)
         apply (rule preserves_ket_query'_output[where b=N])
    by (auto intro!: bound simp: register_pair_Snd register_norm simp del: o_apply split!: if_split_asm)
  then show \<open>dist_inv ((X1;X2);((Y1;Y2);H)) (ket_invariant {((x1,x2),(y1,y2),D). D x1 = Some y1 \<and> D x2 = Some y2}) state3 \<le> \<epsilon> + 20 / sqrt N\<close>
    apply (rule le_back_subst)
    apply (rule dist_inv_register_rewrite, simp, simp)
    apply (rewrite at \<open>((X1; Y1); (X2;(Y2;H)))\<close> to \<open>((X1;X2);((Y1;Y2);H)) o ((reg_1_3 o Fst; reg_2_3 o Fst); (reg_1_3 o Snd; (reg_2_3 o Snd; reg_3_3)))\<close> DEADID.rel_mono_strong)
     apply (simp add: register_pair_Snd register_pair_Fst flip: register_comp_pair comp_assoc)
    apply (subst lift_invariant_comp, simp)
    apply simp
    by (auto intro!: simp: lift_inv_prod' reg_1_3_def reg_3_3_def reg_2_3_def lift_invariant_comp lift_Snd_ket_inv lift_Fst_ket_inv
        ket_invariant_inter  case_prod_unfold 
        simp flip: ket_invariant_SUP)
qed


text \<open>The next bound is applicable for ket-invariants assume the output register to have a value
\<^term>\<open>ket d\<close> that matches what is in the output register before the query and require that after the query,
the oracle register is not \<^const>\<open>None\<close> and the output register has the correct value given that
oracle register content. (I.e., before an uncomputation step.)

Notice that this invariant is only available for \<^const>\<open>query1'\<close>, not for \<^const>\<open>query1\<close>!\<close>

definition \<open>preserve_query1'_uncompute_bound NoneJ b\<^sub>i b\<^sub>j\<^sub>0 = 
          of_bool NoneJ * sqrt b\<^sub>i / sqrt N   +   of_bool NoneJ * sqrt b\<^sub>i / N
      +   sqrt b\<^sub>j\<^sub>0 / N   +   sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / N   +   sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / (N * sqrt N)\<close>
lemma preserve_query1'_uncompute:
  assumes IJ: \<open>I \<subseteq> J\<close>
  assumes b\<^sub>i: \<open>card (Some -` I) \<le> b\<^sub>i\<close>
  assumes b\<^sub>j\<^sub>0: \<open>card (- Some -` J) \<le> b\<^sub>j\<^sub>0\<close>
  assumes \<epsilon>: \<open>\<epsilon> \<ge> preserve_query1'_uncompute_bound (None\<notin>J) b\<^sub>i b\<^sub>j\<^sub>0\<close>
  shows \<open>preserves_ket query1' ((UNIV \<times> I) \<inter> {(d, Some d)| d. True}) (UNIV \<times> J) \<epsilon>\<close>
proof (rule preservesI')
  show \<open>\<epsilon> \<ge> 0\<close>
    using _ \<epsilon> apply (rule order.trans)
    by (simp add: preserve_query1'_uncompute_bound_def)
  fix \<psi> :: \<open>('y \<times> 'y option) ell2\<close>
  assume \<psi>: \<open>\<psi> \<in> space_as_set (ket_invariant ((UNIV \<times> I) \<inter> {(d, Some d)| d. True}))\<close>
  assume \<open>norm \<psi> = 1\<close>

  define I' J' where \<open>I' = Some -` I\<close> and \<open>J' = Some -` J\<close>
  then have \<open>((UNIV \<times> I) \<inter> {(d, Some d)| d. True}) = (\<lambda>d. (d, Some d)) ` I'\<close>
    by auto
  with \<psi> have \<psi>': \<open>\<psi> \<in> space_as_set (ket_invariant ((\<lambda>d. (d, Some d)) ` I'))\<close>
    by fastforce
  have [simp]: \<open>I' \<subseteq> J'\<close>
    using I'_def J'_def IJ by blast
  have card_minus_J': \<open>card (- J') \<le> b\<^sub>j\<^sub>0\<close>
    using J'_def b\<^sub>j\<^sub>0 by force

  define \<beta> where \<open>\<beta> d = Rep_ell2 \<psi> (d, Some d)\<close> for d
  have \<beta>: \<open>\<psi> = (\<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (d, Some d))\<close>
    using ell2_sum_ket_ket_invariant[OF \<psi>']
    apply (subst (asm) infsum_reindex)
     apply (simp add: inj_on_convol_ident)
    by (auto simp: \<beta>_def)
  have \<beta>bound: \<open>(\<Sum>d\<in>I'. (cmod (\<beta> d))\<^sup>2) \<le> 1\<close> (is \<open>?lhs \<le> 1\<close>)
    apply (subgoal_tac \<open>(norm \<psi>)\<^sup>2 = ?lhs\<close>)
     apply (simp add: \<open>norm \<psi> = 1\<close>)
    by (simp add: \<beta> pythagorean_theorem_sum del: sum.insert)

  have [simp]: \<open>Some x \<in> J \<longleftrightarrow> x \<in> J'\<close> for x
    by (simp add: J'_def)
  have [simp]: \<open>x \<in> I' \<Longrightarrow> x \<in> J'\<close> for x
    using \<open>I' \<subseteq> J'\<close> by blast
  have [simp]: \<open>(\<Sum>x\<in>X. if x \<notin> Y then f x else 0) = (\<Sum>x\<in>X-Y. f x)\<close> if \<open>finite X\<close> for f :: \<open>'y \<Rightarrow> 'z::ab_group_add\<close> and X Y
    apply (rule sum.mono_neutral_cong_right)
    using that by auto
  have [simp]: \<open>\<beta> yd *\<^sub>C a *\<^sub>C b = a *\<^sub>C \<beta> yd *\<^sub>C b\<close> for yd a and b :: \<open>'z::complex_vector\<close>
    by auto
  have [simp]: \<open>cmod \<alpha> = inverse (sqrt N)\<close> \<open>cmod (\<alpha>\<^sup>2) = inverse N\<close> \<open>cmod (\<alpha>^3) = inverse (N * sqrt N)\<close> \<open>cmod (\<alpha>^4) = inverse (N\<^sup>2)\<close>
    by (auto simp: norm_mult numeral_3_eq_3 \<alpha>_def inverse_eq_divide norm_divide norm_power power_one_over power2_eq_square power4_eq_xxxx)
  have [simp]: \<open>card I' \<le> b\<^sub>i\<close>
    by (metis I'_def b\<^sub>i)

  define \<phi> and PJ :: \<open>('y * 'y option) update\<close> where 
    \<open>\<phi> = query1' *\<^sub>V \<psi>\<close> and \<open>PJ = Proj (ket_invariant (UNIV \<times> -J))\<close>
  have [simp]: \<open>PJ *\<^sub>V ket (x,y) = (if y\<in>-J then ket (x,y) else 0)\<close> for x y
    by (simp add: Proj_ket_invariant_ket PJ_def)
  have P0\<phi>: \<open>PJ *\<^sub>V \<phi> = 
          (of_bool (None\<notin>J) * \<alpha>) *\<^sub>C (\<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (0, None))
        - (of_bool (None\<notin>J) * \<alpha>^3) *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y\<in>UNIV. \<beta> d *\<^sub>C ket (y, None))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>-J'. \<beta> d *\<^sub>C ket (d + d', Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>d'\<in>-J'. \<beta> d *\<^sub>C ket (0, Some d'))
        + \<alpha>^4 *\<^sub>C (\<Sum>d\<in>I'. \<Sum>y\<in>UNIV. \<Sum>d''\<in>-J'. \<beta> d *\<^sub>C ket (y, Some d''))
        \<close>
    (is \<open>_ = ?t1 - ?t2 - ?t3 - ?t4 + ?t5\<close>)
    by (simp add: \<phi>_def \<beta> query1' option_sum_split vimage_Compl
        cblinfun.add_right cblinfun.diff_right if_distrib Compl_eq_Diff_UNIV
        vimage_singleton_inj sum_sum_if_eq sum.distrib scaleC_diff_right scaleC_sum_right
        sum_subtractf case_prod_beta sum.cartesian_product' scaleC_add_right add_diff_eq
        cblinfun.scaleC_right cblinfun.sum_right
        flip: sum.Sigma add.assoc scaleC_scaleC
        cong del: option.case_cong if_cong)

  have norm_t1: \<open>norm ?t1 \<le> of_bool (None\<notin>J) * sqrt b\<^sub>i / sqrt N\<close>
  proof (cases \<open>None \<in> J\<close>)
    case True
    then show ?thesis
      by simp
  next
    case False
    then have \<open>norm ?t1 = inverse (sqrt N) * norm (\<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (0 :: 'y, None :: 'y option))\<close>
      by simp
    also have \<open>\<dots> \<le> inverse (sqrt N) * sqrt b\<^sub>i\<close>
      apply (rule mult_left_mono)
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto
    also have \<open>\<dots> = of_bool (None\<notin>J) * sqrt b\<^sub>i / sqrt N\<close>
      using False by (simp add: divide_inverse_commute)
    finally show ?thesis
      by -
  qed

  have norm_t2: \<open>norm ?t2 \<le> of_bool (None\<notin>J) * sqrt b\<^sub>i / N\<close>
  proof (cases \<open>None \<in> J\<close>)
    case True
    then show ?thesis
      by simp
  next
    case False
    have *: \<open>norm (\<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (y, None :: 'y option)) \<le> sqrt b\<^sub>i\<close> for y :: 'y
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto

    have \<open>norm ?t2 = inverse (N * sqrt N) * norm (\<Sum>y\<in>UNIV. \<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (y :: 'y, None :: 'y option))\<close>
      apply (subst sum.swap) by (simp add: False)
    also have \<open>\<dots> \<le> inverse (N * sqrt N) * (sqrt (real N) * sqrt (real b\<^sub>i))\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto simp add: cinner_sum_right cinner_sum_left N_def)
    also have \<open>\<dots> = of_bool (None\<notin>J) * sqrt b\<^sub>i / N\<close>
      using False by (simp add: divide_inverse_commute N_def)
    finally show ?thesis
      by -
  qed

  have norm_t3: \<open>norm ?t3 \<le> sqrt b\<^sub>j\<^sub>0 / N\<close>
  proof -
    have *: \<open>norm (\<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (d + d', Some d')) \<le> sqrt (1::nat)\<close> for d' :: 'y
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by (auto simp add: card_le_Suc0_iff_eq)

    have \<open>norm ?t3 = inverse N * norm (\<Sum>d'\<in>- J'. \<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (d + d', Some d'))\<close>
      apply (subst sum.swap) by simp
    also have \<open>\<dots> \<le> inverse N * sqrt b\<^sub>j\<^sub>0\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      using card_minus_J' by (auto simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> = sqrt b\<^sub>j\<^sub>0 / N\<close>
      by (simp add: divide_inverse_commute)
    finally show ?thesis
      by -
  qed

  have norm_t4: \<open>norm ?t4 \<le> sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / N\<close>
  proof -
    have *: \<open>norm (\<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (0, Some d')) \<le> sqrt b\<^sub>i\<close> for d' :: 'y
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto

    have \<open>norm ?t4 = inverse N * norm (\<Sum>d'\<in>- J'. \<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (0 :: 'y, Some d' :: 'y option))\<close>
      apply (subst sum.swap) by simp
    also have \<open>\<dots> \<le> inverse N * (sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      by (auto intro!: card_minus_J' mult_right_mono simp add: cinner_sum_right cinner_sum_left)
    also have \<open>\<dots> = sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / N\<close>
      by (simp add: divide_inverse_commute)
    finally show ?thesis
      by -
  qed

  have norm_t5: \<open>norm ?t5 \<le> sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / (N * sqrt N)\<close>
  proof -
    have *: \<open>norm (\<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (fst yd'', Some (snd yd''))) \<le> sqrt b\<^sub>i\<close> for yd'' :: \<open>'y \<times> 'y\<close>
      using _ _ \<beta>bound apply (rule bound_coeff_sum2)
      by auto

    have \<open>norm ?t5 = inverse (N\<^sup>2) * norm (\<Sum>yd''\<in>UNIV\<times>-J'. \<Sum>d\<in>I'. \<beta> d *\<^sub>C ket (fst yd'' :: 'y, Some (snd yd'')))\<close>
      apply (simp add: sum.cartesian_product' sum.reindex N_def)
      apply (subst (2) sum.swap) apply (subst sum.swap)
      by (rule refl)
    also have \<open>\<dots> \<le> inverse (N\<^sup>2) * (sqrt N * sqrt b\<^sub>j\<^sub>0 * sqrt b\<^sub>i)\<close>
      apply (rule mult_left_mono)
      using * apply (rule norm_ortho_sum_bound)
      using card_minus_J' by (auto intro!: mult_right_mono simp add: cinner_sum_right cinner_sum_left cinner_ket real_sqrt_mult N_def)
    also have \<open>\<dots> = sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / (N * sqrt N)\<close>
      by (smt (verit, ccfv_threshold) field_class.field_divide_inverse mult.commute of_nat_0_le_iff of_nat_power power2_eq_square real_divide_square_eq real_sqrt_mult_self times_divide_times_eq)
    finally show ?thesis
      by -
  qed

  have \<open>norm (PJ *\<^sub>V \<phi>) \<le> of_bool (None\<notin>J) * sqrt b\<^sub>i / sqrt N   +   of_bool (None\<notin>J) * sqrt b\<^sub>i / N
                        +   sqrt b\<^sub>j\<^sub>0 / N   +   sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / N   +   sqrt b\<^sub>i * sqrt b\<^sub>j\<^sub>0 / (N * sqrt N)\<close>
    unfolding P0\<phi>
    apply (rule norm_triangle_le_diff norm_triangle_le, rule add_mono)+
        apply (rule norm_t1)
       apply (rule norm_t2)
      apply (rule norm_t3)
     apply (rule norm_t4)
    by (rule norm_t5)
  also have \<open>\<dots> = preserve_query1'_uncompute_bound (None\<notin>J) b\<^sub>i b\<^sub>j\<^sub>0\<close>
    by (auto simp: preserve_query1'_uncompute_bound_def mult.commute mult.left_commute)
  also have \<open>\<dots> \<le> \<epsilon>\<close>
    by (simp add: \<epsilon>)
  finally show \<open>norm (Proj (- ket_invariant (UNIV \<times> J)) *\<^sub>V \<phi>) \<le> \<epsilon>\<close>
    unfolding PJ_def
    apply (subst ket_invariant_compl[symmetric])
    by simp
qed

end (* context compressed_oracle *)

end
