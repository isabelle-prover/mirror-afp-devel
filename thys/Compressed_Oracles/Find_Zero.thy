section \<open>\<open>Find_Zero\<close> – Invariant preservation for zero-finding\<close>

theory Find_Zero
  imports CO_Invariants Oracle_Programs
begin

context compressed_oracle begin

definition \<open>no_zero = {(x::'x,y::'y,D::'x\<rightharpoonup>'y). 0 \<notin> ran D}\<close>
definition \<open>no_zero' = {D::'x\<rightharpoonup>'y. 0 \<notin> ran D}\<close>

lemma no_zero_no_zero': \<open>no_zero = UNIV \<times> UNIV \<times> no_zero'\<close>
  by (auto intro!: simp: no_zero_def no_zero'_def)

lemma ket_invariant_no_zero_no_zero': \<open>ket_invariant no_zero = \<top> \<otimes>\<^sub>S \<top> \<otimes>\<^sub>S ket_invariant no_zero'\<close>
  by (auto simp: ket_invariant_tensor no_zero_no_zero' simp flip: ket_invariant_UNIV)

text \<open>We show the preservation of the \<^const>\<open>no_zero\<close> invariant.
We show it first with respect to the oracle \<^const>\<open>query\<close>.\<close>

lemma preserves_no_zero: \<open>preserves_ket query no_zero no_zero (6 / sqrt N)\<close>
proof -
  define K where \<open>K x = ket_invariant {(x,y::'y,D::'x\<rightharpoonup>'y) | y D. Some 0 \<notin> D ` (-{x})}\<close> for x
  define Kd where \<open>Kd x D0 = ket_invariant {(x,y::'y,D::'x\<rightharpoonup>'y) | y D. (\<forall>x'\<noteq>x. D x' = D0 x')}\<close> for x D0
  have aux: \<open>Some 0 \<notin> D ` (- {x}) \<Longrightarrow>
         \<exists>xa. xa x = None \<and> Some 0 \<notin> range xa \<and> (\<forall>x'. x' \<noteq> x \<longrightarrow> D x' = xa x')\<close> for D::\<open>'x\<rightharpoonup>'y\<close> and x
    apply (rule exI[of _ \<open>D(x:=None)\<close>])
    by force
  have K: \<open>K x = (SUP D0\<in>{D0. D0 x = None \<and> Some 0 \<notin> range D0}. Kd x D0)\<close> for x
    using aux[of _ x] by (auto intro!: simp: K_def Kd_def simp flip: ket_invariant_SUP)
  define Kdx where \<open>Kdx x D0 x' = ket_invariant {(x::'x,y::'y,D::'x\<rightharpoonup>'y) | y D. D x' = D0 x'}\<close> for x D0 x'
  have Kd: \<open>Kd x D0 = (INF x'\<in>-{x}. Kdx x D0 x')\<close> for x D0
    unfolding Kd_def Kdx_def
    apply (subst ket_invariant_INF[symmetric])
    apply (rule arg_cong[where f=ket_invariant])
    by auto
  have Kdx: \<open>Kdx x D0 x' = lift_invariant reg_1_3 (ket_invariant {x}) \<sqinter> lift_invariant (reg_3_3 o function_at x') (ket_invariant {D0 x'})\<close> for x D0 x'
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
  proof (rule inv_split_reg_query[where X=\<open>reg_1_3\<close> and Y=\<open>reg_2_3\<close> and H=\<open>reg_3_3\<close> and K=K 
        and ?I1.0=\<open>\<lambda>_. ket_invariant (UNIV \<times> -{Some 0})\<close> and ?J1.0=\<open>\<lambda>_. ket_invariant (UNIV \<times> -{Some 0})\<close>])
    show \<open>query = (reg_1_3;(reg_2_3;reg_3_3)) query\<close>
      by (simp add: pair_Fst_Snd reg_1_3_def reg_2_3_def reg_3_3_def)
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
    show \<open>ket_invariant no_zero
          \<le> (SUP x. K x \<sqinter>
               lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) (ket_invariant (UNIV \<times> - {Some 0})))\<close>
      apply (simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv)
      unfolding no_zero_def
      by (auto simp add: ranI)
    have aux: \<open>\<And>D::'x\<rightharpoonup>'y. Some 0 \<notin> D ` (- {x}) \<Longrightarrow> D x \<noteq> Some 0 \<Longrightarrow> 0 \<in> ran D \<Longrightarrow> False\<close> for x
      by (smt (verit, del_insts) ComplI image_iff mem_Collect_eq ran_def singletonD)
    show \<open>K x \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) (ket_invariant (UNIV \<times> - {Some 0}))
          \<le> ket_invariant no_zero\<close> for x
      by (auto intro: aux simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv
          no_zero_def)
    show \<open>orthogonal_spaces (K x) (K x')\<close> if \<open>x \<noteq> x'\<close> for x x'
      using that by (auto simp add: K_def)
    show \<open>preserves_ket query1 (UNIV \<times> - {Some 0}) (UNIV \<times> - {Some 0}) (6 / sqrt N)\<close>
      apply (subst asm_rl[of \<open>6 / sqrt N = 6 * sqrt (1::nat) / sqrt N\<close>], simp)
      apply (rule preserve_query1_simplified)
      by (auto simp add: card_le_Suc0_iff_eq)
      (* Direct proof is tighter, gives factor 4 instead of 6. Reason: in this specific case, terms t3,t4 cancel out in lemma preserve_query1.
      See commit 44e3f12f *)
    show \<open>K x \<le> lift_invariant reg_1_3 (ket_invariant {x})\<close> for x
      by (auto simp add: K_def reg_1_3_def lift_Fst_ket_inv)
    show \<open>6 / sqrt N \<ge> 0\<close>
      by simp
  qed simp
qed

text \<open>Like @{thm [source] preserves_no_zero} but with respect to the oracle \<^const>\<open>query\<close>.\<close>

lemma preserves_no_zero': \<open>preserves_ket query' no_zero no_zero (5 / sqrt N)\<close>
proof -
  define K where \<open>K x = ket_invariant {(x,y::'y,D::'x\<rightharpoonup>'y) | y D. Some 0 \<notin> D ` (-{x})}\<close> for x
  define Kd where \<open>Kd x D0 = ket_invariant {(x,y::'y,D::'x\<rightharpoonup>'y) | y D. (\<forall>x'\<noteq>x. D x' = D0 x')}\<close> for x D0
  have aux: \<open>Some 0 \<notin> D ` (- {x}) \<Longrightarrow>
         \<exists>xa. xa x = None \<and> Some 0 \<notin> range xa \<and> (\<forall>x'. x' \<noteq> x \<longrightarrow> D x' = xa x')\<close> for D::\<open>'x\<rightharpoonup>'y\<close> and x
    apply (rule exI[of _ \<open>D(x:=None)\<close>])
    by force
  have K: \<open>K x = (SUP D0\<in>{D0. D0 x = None \<and> Some 0 \<notin> range D0}. Kd x D0)\<close> for x
    using aux[of _ x] by (auto intro!: simp: K_def Kd_def simp flip: ket_invariant_SUP)
  define Kdx where \<open>Kdx x D0 x' = ket_invariant {(x::'x,y::'y,D::'x\<rightharpoonup>'y) | y D. D x' = D0 x'}\<close> for x D0 x'
  have Kd: \<open>Kd x D0 = (INF x'\<in>-{x}. Kdx x D0 x')\<close> for x D0
    unfolding Kd_def Kdx_def
    apply (subst ket_invariant_INF[symmetric])
    apply (rule arg_cong[where f=ket_invariant])
    by auto
  have Kdx: \<open>Kdx x D0 x' = lift_invariant reg_1_3 (ket_invariant {x}) \<sqinter> lift_invariant (reg_3_3 o function_at x') (ket_invariant {D0 x'})\<close> for x D0 x'
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
  proof (rule inv_split_reg_query'[where X=\<open>reg_1_3\<close> and Y=\<open>reg_2_3\<close> and H=\<open>reg_3_3\<close> and K=K 
        and ?I1.0=\<open>\<lambda>_. ket_invariant (UNIV \<times> -{Some 0})\<close> and ?J1.0=\<open>\<lambda>_. ket_invariant (UNIV \<times> -{Some 0})\<close>])
    show \<open>query' = (reg_1_3;(reg_2_3;reg_3_3)) query'\<close>
      by (simp add: pair_Fst_Snd reg_1_3_def reg_2_3_def reg_3_3_def) 
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
    show \<open>ket_invariant no_zero
          \<le> (SUP x. K x \<sqinter>
               lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) (ket_invariant (UNIV \<times> - {Some 0})))\<close>
      apply (simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv)
      unfolding no_zero_def
      by (auto simp add: ranI)
    have aux: \<open>Some 0 \<notin> D ` (- {x}) \<Longrightarrow> D x \<noteq> Some 0 \<Longrightarrow> 0 \<notin> ran D\<close> for D x
      by (smt (verit, del_insts) ComplI image_iff mem_Collect_eq ran_def singletonD)
    show \<open>K x \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at x) (ket_invariant (UNIV \<times> - {Some 0}))
          \<le> ket_invariant no_zero\<close> for x
      using aux[of _ x]
      by (auto simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric]
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv
          no_zero_def)
    show \<open>orthogonal_spaces (K x) (K x')\<close> if \<open>x \<noteq> x'\<close> for x x'
      using that by (auto simp add: K_def)
    show \<open>preserves_ket query1' (UNIV \<times> - {Some 0}) (UNIV \<times> - {Some 0}) (5 / sqrt N)\<close>
      apply (subst asm_rl[of \<open>5 / sqrt N = 5 * sqrt (1::nat) / sqrt N\<close>], simp)
      apply (rule preserve_query1'_simplified)
      by (auto simp add: card_le_Suc0_iff_eq)
    show \<open>K x \<le> lift_invariant reg_1_3 (ket_invariant {x})\<close> for x
      by (auto simp add: K_def reg_1_3_def lift_Fst_ket_inv)
    show \<open>5 / sqrt N \<ge> 0\<close>
      by simp
  qed simp
qed



lemma preserves_no_zero_num: \<open>preserves_ket query (no_zero \<inter> num_queries q) (no_zero \<inter> num_queries (q+1)) (6 / sqrt N)\<close>
  apply (subst add_0_right[of \<open>6/sqrt N\<close>, symmetric])
  apply (rule preserves_intersect_ket)
   apply (simp add: preserves_mono[OF preserves_no_zero])
  apply (rule preserves_mono[OF preserves_num])
  by auto  

lemma preserves_no_zero_num': \<open>preserves_ket query' (no_zero \<inter> num_queries q) (no_zero \<inter> num_queries (q+1)) (5 / sqrt N)\<close>
  apply (subst add_0_right[of \<open>5/sqrt N\<close>, symmetric])
  apply (rule preserves_intersect_ket)
   apply (simp add: preserves_mono[OF preserves_no_zero'])
  apply (rule preserves_mono[OF preserves_num'])
  by auto  

subsection \<open>Zero-finding is hard for q-query adversaries\<close>

lemma zero_finding_is_hard:
  fixes program :: \<open>('mem, 'x, 'y) program\<close>
    and adv_output :: \<open>'x update \<Rightarrow> 'mem update\<close>
    and initial_state
  assumes [iff]: \<open>valid_program program\<close>
  assumes \<open>norm initial_state = 1\<close>
  assumes [register]: \<open>register adv_output\<close>
  shows \<open>(\<Sum>h\<in>UNIV. \<Sum>x|h x = 0. measurement_probability adv_output (exec_program h program initial_state) x) / CARD('x \<Rightarrow> 'y)
                 \<le> (5 * real (query_count program) + 11)\<^sup>2 / N\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]

  text \<open>In this game based proof, we consider three different quantum memory models:

\<^item> The one from the statement of the lemma, where the overall quantum state lives in \<^typ>\<open>'mem\<close>,
  and the adversary output register is described by \<^term>\<open>adv_output\<close>, and the initial state
  in \<^term>\<open>initial_state\<close>. The program \<^term>\<open>program\<close> assumes this memory model.
\<^item> The "extra output" (short XO) memory model, where there is an extra auxiliary register \<open>aux\<close> of type \<^typ>\<open>'y\<close>.
  The type of the memory is then \<^typ>\<open>'mem \<times> 'y\<close>. (I.e., the extra register is in addition to the content of \<^typ>\<open>'mem\<close>.)
\<^item> The "compressed oracle" (short CO) memory model, where additionally to XO, we have an oracle register
  that can holds the content of the compressed oracle (or the standard oracle).\<close>


  text \<open>Since the register \<^term>\<open>adv_output :: _ \<Rightarrow> ('mem ell2 \<Rightarrow>\<^sub>C\<^sub>L 'mem ell2)\<close> is defined w.r.t. a specific memory,
    we define convenience definitions for the same register as it would be accessed in the other memories:\<close>

  define adv_output_in_xo :: \<open>'x update \<Rightarrow> ('mem\<times>'y) update\<close> where \<open>adv_output_in_xo = Fst o adv_output\<close>
  define adv_output_in_co :: \<open>'x update \<Rightarrow> (('mem\<times>'y) \<times> ('x\<rightharpoonup>'y)) update\<close> where \<open>adv_output_in_co = Fst o adv_output_in_xo\<close>

  text \<open>Analogously, we defined the \<open>aux\<close>-register and the oracle register in the applicable memories:\<close>

  define aux_in_xo :: \<open>'y update \<Rightarrow> ('mem\<times>'y) update\<close> where \<open>aux_in_xo = Snd\<close>
  define aux_in_co :: \<open>'y update \<Rightarrow> (('mem\<times>'y) \<times> ('x\<rightharpoonup>'y)) update\<close> where \<open>aux_in_co = Fst o aux_in_xo\<close>
  define oracle_in_co :: \<open>('x\<rightharpoonup>'y) update \<Rightarrow> (('mem\<times>'y) \<times> ('x\<rightharpoonup>'y)) update\<close> where \<open>oracle_in_co = Snd\<close>
  define aao_in_co where \<open>aao_in_co = (adv_output_in_co; (aux_in_co; oracle_in_co))\<close>
    \<comment> \<open>Abbreviation since we use this combination often.\<close>

  have [register]: \<open>compatible aux_in_co oracle_in_co\<close>
    by (simp add: adv_output_in_co_def aux_in_co_def oracle_in_co_def adv_output_in_xo_def aux_in_xo_def)
  have [register]: \<open>compatible adv_output_in_xo aux_in_xo\<close>
    by (simp add: adv_output_in_xo_def aux_in_xo_def)
  have [register]: \<open>compatible adv_output_in_co aux_in_co\<close>
    by (simp add: adv_output_in_co_def aux_in_co_def)
  have [register]: \<open>compatible adv_output_in_co oracle_in_co\<close>
    by (simp add: adv_output_in_co_def oracle_in_co_def)
  have [register]: \<open>compatible aux_in_xo Fst\<close>
    by (simp add: aux_in_xo_def)
  have [register]: \<open>compatible aux_in_co (Fst o Fst)\<close>
    by (simp add: aux_in_co_def)
  have [register]: \<open>compatible aux_in_co Snd\<close>
    by (simp add: aux_in_co_def)
  have [register]: \<open>register aao_in_co\<close>
    by (simp add: aao_in_co_def)

  text \<open>The initial states in XO/CO are like the original initial state, but with
   \<^term>\<open>ket 0\<close> in \<open>aux\<close> and \<^term>\<open>ket Map.empty\<close> (the fully undefined function) in the oracle register.\<close>

  define initial_state_in_xo where \<open>initial_state_in_xo = initial_state \<otimes>\<^sub>s ket (0 :: 'y)\<close>
  define initial_state_in_co :: \<open>(('mem\<times>'y) \<times> ('x\<rightharpoonup>'y)) ell2\<close> where \<open>initial_state_in_co = initial_state_in_xo \<otimes>\<^sub>s ket Map.empty\<close>

  text \<open>We define an extended program \<open>ext_program\<close> that executes \<^term>\<open>program\<close>, followed by one additional query to the oracle.
    Input register is the adversary output register. Output register is the additional register \<open>aux\<close>.
    Hence \<open>ext_program\<close> is only meaningful in the models XO and CO. (Our definition is for XO.)\<close>

  define ext_program where \<open>ext_program = lift_program Fst program @ [QueryStep adv_output_in_xo aux_in_xo]\<close>
  have [iff]: \<open>valid_program ext_program\<close>
    by (auto intro!: valid_program_lift simp add: valid_program_append adv_output_in_xo_def aux_in_xo_def ext_program_def)

  text \<open>We define the final states of the programs \<^term>\<open>program\<close> and \<^term>\<open>ext_program\<close>, in the original model, and in XO, and CO.\<close>
  define final :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> 'mem ell2\<close> where \<open>final h = exec_program h program initial_state\<close> for h
  define xo_ext_final :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('mem\<times>'y) ell2\<close> where \<open>xo_ext_final h = exec_program h ext_program initial_state_in_xo\<close> for h
  define xo_final :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('mem\<times>'y) ell2\<close> where \<open>xo_final h = exec_program h (lift_program Fst program) initial_state_in_xo\<close> for h
  define co_ext_final :: \<open>(('mem\<times>'y) \<times> ('x\<rightharpoonup>'y)) ell2\<close> where \<open>co_ext_final = exec_program_with query' ext_program initial_state_in_co\<close>
  define co_final :: \<open>(('mem\<times>'y) \<times> ('x\<rightharpoonup>'y)) ell2\<close> where \<open>co_final = exec_program_with query' (lift_program Fst program) initial_state_in_co\<close>

  have [simp]: \<open>norm initial_state_in_xo = 1\<close>
    by (simp add: initial_state_in_xo_def norm_tensor_ell2 assms)
  have norm_initial_state_in_co[simp]: \<open>norm initial_state_in_co = 1\<close>
    by (simp add: initial_state_in_co_def norm_tensor_ell2)

  have norm_co_final[simp]: \<open>norm co_final \<le> 1\<close>
    unfolding co_final_def
    using norm_exec_program_with valid_program_lift \<open>valid_program program\<close>
      norm_query' register_Fst norm_initial_state_in_co
    by smt

  text \<open>We derive the relationships between the various final states:\<close>

  have co_ext_final_prefinal: \<open>co_ext_final = aao_in_co query' *\<^sub>V co_final\<close>
    by (simp add: co_ext_final_def ext_program_def exec_program_with_append aao_in_co_def
        flip: initial_state_in_co_def co_final_def adv_output_in_co_def aux_in_co_def oracle_in_co_def)

  have xo_final_final: \<open>xo_final h = final h \<otimes>\<^sub>s ket 0\<close> for h
    by (simp add: xo_final_def final_def initial_state_in_xo_def exec_lift_program_Fst)

  have xo_ext_final_xo_final: \<open>xo_ext_final h = (adv_output_in_xo;aux_in_xo) (function_oracle h) *\<^sub>V xo_final h\<close> for h
    by (simp add: xo_ext_final_def xo_final_def ext_program_def exec_program_def)

  text \<open>After executing \<^term>\<open>program\<close> (in XO), the \<open>aux\<close>-register is in state \<^term>\<open>ket 0\<close>:\<close>
  have xo_final_has_y0: \<open>dist_inv_avg (adv_output_in_xo;aux_in_xo) (\<lambda>_. ket_invariant {(x,y). y = 0}) xo_final = 0\<close>
  proof -
    have \<open>dist_inv_avg aux_in_xo (\<lambda>_::'x\<Rightarrow>'y. ket_invariant {0}) xo_final
        \<le> dist_inv_avg aux_in_xo (\<lambda>_::'x\<Rightarrow>'y. ket_invariant {0}) (\<lambda>h. initial_state_in_xo)\<close>
      unfolding xo_final_def
      apply (subst dist_inv_avg_exec_compatible)
      using dist_inv_avg_exec_compatible
      by auto
    also have \<open>\<dots> = 0\<close>
      by (auto intro!: tensor_ell2_in_tensor_ccsubspace ket_in_ket_invariantI
          simp add: initial_state_in_xo_def dist_inv_0_iff distance_from_inv_avg0I aux_in_xo_def lift_Snd_inv)
    finally have \<open>dist_inv_avg aux_in_xo (\<lambda>_. ket_invariant {0}) xo_final = 0\<close>
      by (smt (verit, ccfv_SIG) dist_inv_avg_pos)
    then show ?thesis
      apply (rewrite at \<open>{(x, y). y = 0}\<close> to \<open>UNIV \<times> {0}\<close> DEADID.rel_mono_strong, blast)
      apply (subst dist_inv_avg_register_rewrite)
      by (simp_all add: lift_inv_prod)
  qed

  text \<open>Same as @{thm [source] xo_final_has_y0}, but in CO:\<close>
  have co_final_has_y0: \<open>dist_inv aao_in_co (ket_invariant {(x,y,D). y = 0}) co_final = 0\<close>
  proof -
    have \<open>dist_inv aux_in_co (ket_invariant {0}) co_final
       \<le> dist_inv aux_in_co (ket_invariant {0}) initial_state_in_co\<close>
      unfolding co_final_def
      apply (rule dist_inv_exec'_compatible)
      by simp_all
    also have \<open>\<dots> = 0\<close>
      by (auto intro!: tensor_ell2_in_tensor_ccsubspace ket_in_ket_invariantI
          simp add: initial_state_in_co_def initial_state_in_xo_def dist_inv_0_iff
          aux_in_co_def aux_in_xo_def lift_Fst_inv lift_Snd_inv lift_invariant_comp)
    finally have \<open>dist_inv aux_in_co (ket_invariant {0}) co_final = 0\<close>
      by (smt (verit, best) dist_inv_pos)
    then show ?thesis
      apply (rewrite at \<open>{(x, y, D). y = 0}\<close> to \<open>UNIV \<times> {0} \<times> UNIV\<close> DEADID.rel_mono_strong, blast)
      apply (subst dist_inv_register_rewrite)
      by (simp_all add: lift_inv_prod aao_in_co_def)
  qed

  define q where \<open>q = query_count program\<close>
  text \<open>The following term occurs a lot (it's how much the \<^term>\<open>no_zero\<close> invariant is preserved after running \<^term>\<open>ext_program\<close>).
    So we abbreviate it as \<open>d\<close>.\<close>
  define d :: real where \<open>d = (5 * q + 11) / sqrt N\<close>

  have [iff]: \<open>d \<ge> 0\<close>
    by (simp add: d_def)

  have \<open>dist_inv oracle_in_co (ket_invariant no_zero') co_ext_final \<le> 5 * (q+1) / sqrt N\<close>
      \<comment> \<open>In CO-execution, before the adversary's final query, the oracle register has no 0 in its range\<close>
  proof (unfold co_ext_final_def, rule dist_inv_induct[where g=\<open>\<lambda>_. 5 / sqrt N\<close> and J=\<open>\<lambda>_. ket_invariant no_zero'\<close>])
    show \<open>compatible oracle_in_co Fst\<close>
      using oracle_in_co_def by simp
    show \<open>initial_state_in_co \<in> space_as_set (lift_invariant oracle_in_co (ket_invariant no_zero'))\<close>
      by (auto intro!: tensor_ell2_in_tensor_ccsubspace
          simp add: initial_state_in_co_def oracle_in_co_def lift_Snd_ket_inv
          initial_state_in_xo_def tensor_ell2_ket ket_in_ket_invariantI no_zero'_def
         simp flip: ket_invariant_tensor)
    show \<open>ket_invariant no_zero' \<le> ket_invariant no_zero'\<close>
      by simp
    show \<open>valid_program ext_program\<close>
      by (simp add: valid_program_lift)
    show \<open>preserves ((Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) query') (lift_invariant oracle_in_co (ket_invariant no_zero'))
        (lift_invariant oracle_in_co (ket_invariant no_zero')) (5 / sqrt N)\<close> if [register]: \<open>compatible X_in_xo Y_in_xo\<close> for X_in_xo Y_in_xo
    proof -
      from preserves_no_zero'
      have \<open>preserves ((Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) query')
            (lift_invariant (Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) (ket_invariant no_zero))
            (lift_invariant (Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) (ket_invariant no_zero))
            (5 / sqrt (real N))\<close>
        unfolding N_def
        apply (rule preserves_lift_invariant[THEN iffD2, rotated])
        by simp
      moreover have \<open>lift_invariant (Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) (ket_invariant no_zero)
                   = lift_invariant oracle_in_co (ket_invariant no_zero')\<close>
        by (simp add: oracle_in_co_def no_zero_no_zero' lift_inv_prod)
      finally show ?thesis
        by -
    qed
    show \<open>norm query' \<le> 1\<close>
      by simp
    show \<open>norm initial_state_in_co \<le> 1\<close>
      by simp
    show \<open>(\<Sum>i<query_count ext_program. 5 / sqrt N) \<le> real (5 * (q+1)) / sqrt N\<close>
      apply (simp add: query_count_lift_program ext_program_def flip: q_def)
      by argo
  qed

  then have dist_zero: \<open>dist_inv aao_in_co (ket_invariant no_zero) co_ext_final \<le> 5 * (q+1) / sqrt N\<close>
      \<comment> \<open>Same thing, but expressed w.r.t. different register\<close>
    apply (rule le_back_subst)
    apply (rule dist_inv_register_rewrite)
    by (auto intro!: simp: aao_in_co_def no_zero_no_zero' lift_inv_prod)

  have dist_Dxy: \<open>dist_inv aao_in_co (ket_invariant {(x,y,D). D x = Some y}) co_ext_final \<le> 6 / sqrt N\<close> (is \<open>?lhs \<le> _\<close>)
    unfolding co_ext_final_prefinal
    apply (rule dist_inv_leq_if_preserves[THEN order_trans])
       apply (subst preserves_lift_invariant)
        apply (auto intro!: preserves_ket_query'_output_simple simp: register_norm)[4]
    using norm_co_final
    by (simp add: N_def co_final_has_y0 field_class.field_divide_inverse)

  have \<open>dist_inv aao_in_co
          (ket_invariant {(x, y, D::'x \<rightharpoonup> 'y). 0 \<notin> ran D \<and> D x = Some y}) co_ext_final \<le> d\<close> (is \<open>?lhs \<le> d\<close>)
    \<comment> \<open>In CO-execution, after the adversary's final query, the oracle register has no 0 in its range,
        and the aux register contains the output of the oracle function evaluated on the adversary output register.\<close>
  proof -
    have \<open>?lhs = dist_inv aao_in_co (ket_invariant no_zero \<sqinter> ket_invariant {(x, y, D). D x = Some y}) co_ext_final\<close>
      apply (rule arg_cong3[where f=dist_inv])
      by (auto intro!: simp: no_zero_def ket_invariant_inter)
    also have \<open>\<dots> \<le> sqrt ((dist_inv aao_in_co (ket_invariant no_zero) co_ext_final)\<^sup>2
                        + (dist_inv aao_in_co (ket_invariant {(x, y, D). D x = Some y}) co_ext_final)\<^sup>2)\<close>
      apply (rule dist_inv_intersect)
      by auto
    also have \<open>\<dots> \<le> sqrt ((5 * (q+1) / sqrt N)\<^sup>2 + (6 / sqrt N)\<^sup>2)\<close>
      apply (rule real_sqrt_le_mono)
      apply (rule add_mono)
      using dist_zero dist_Dxy
      by auto
    also have \<open>\<dots> \<le> (5 * q + 11) / sqrt N\<close>
      apply (rule sqrt_sum_squares_le_sum[THEN order_trans])
      by (auto, argo)
    finally show ?thesis
      by (simp add: d_def)
  qed
  then have \<open>dist_inv aao_in_co (ket_invariant {(x, y, D::'x \<rightharpoonup> 'y). y \<noteq> 0}) co_ext_final \<le> d\<close>
    \<comment> \<open>In CO-execution, after the adversary's final query, the adversary output register is not 0.\<close>
    apply (rule le_back_subst_le)
    apply (rule dist_inv_mono)
    by (auto intro!: ranI)
  then have \<open>dist_inv (adv_output_in_co; aux_in_co) (ket_invariant {(x, y). y \<noteq> 0}) co_ext_final \<le> d\<close>
    \<comment> \<open>As before, but with respect to a different register (without the oracle register that doesn't exist in XO).\<close>
    apply (rule le_back_subst)
    apply (rule dist_inv_register_rewrite)
      apply (simp, simp)
    apply (rewrite at \<open>{(x, y, D). y \<noteq> 0}\<close> 
        to \<open>(\<lambda>((a,b),c). (a,b,c)) ` ({(x, y) | x y. y \<noteq> 0} \<times> UNIV)\<close> DEADID.rel_mono_strong)
     apply force
    by (simp add: ket_invariant_image_assoc pair_o_assoc pair_o_assoc[unfolded o_def] lift_inv_prod aao_in_co_def
        flip: lift_invariant_comp[unfolded o_def, THEN fun_cong])
  then have \<open>dist_inv_avg (adv_output_in_xo; aux_in_xo) (\<lambda>h. ket_invariant {(x, y). y \<noteq> 0}) xo_ext_final \<le> d\<close>
    \<comment> \<open>In XO-execution, after the adversary's final query, the auxiliary register is not 0.\<close>
    apply (rule le_back_subst)
    unfolding co_ext_final_def xo_ext_final_def
    apply (rewrite at \<open>(adv_output_in_co;aux_in_co)\<close> to \<open>Fst o (adv_output_in_xo;aux_in_xo)\<close> DEADID.rel_mono_strong)
     apply (simp add: adv_output_in_co_def aux_in_co_def register_comp_pair) 
    by (simp add: initial_state_in_co_def dist_inv_exec_query'_exec_fixed)
  then have \<open>dist_inv_avg (adv_output_in_xo; aux_in_xo)
          (\<lambda>h. ket_invariant {(x, y). h x \<noteq> 0 \<or> y \<noteq> 0}) xo_final \<le> d\<close>
    \<comment> \<open>In XO-execution, before the adversary's final query, \<^term>\<open>h x \<noteq> 0\<close> or \<^term>\<open>y \<noteq> 0\<close>.\<close>
    apply (rule le_back_subst_le)
    unfolding xo_ext_final_xo_final[abs_def]
    apply (subst dist_inv_avg_apply_iff)
    by (auto intro!: ext dist_inv_avg_mono simp: function_oracle_ket_invariant)
  then have *: \<open>dist_inv_avg (adv_output_in_xo; aux_in_xo)
          (\<lambda>h. ket_invariant {(x, y). h x \<noteq> 0}) xo_final \<le> d\<close>
    \<comment> \<open>In XO-execution, before the adversary's final query, \<^term>\<open>h x \<noteq> 0\<close>.\<close>
    apply (rule le_back_subst_le)
    apply (rule ord_le_eq_trans)
     apply (rule dist_inv_avg_mono[where I=\<open>\<lambda>h. ket_invariant {(x, y). h x \<noteq> 0 \<or> y \<noteq> 0} \<sqinter> ket_invariant {(x,y). y=0}\<close>])
      apply (auto simp: ket_invariant_inter)[2]
    apply (rule dist_inv_avg_intersect)
       apply simp_all[2]
    by (fact xo_final_has_y0)
  then have \<open>dist_inv_avg adv_output_in_xo
          (\<lambda>h. ket_invariant {x. h x \<noteq> 0}) xo_final \<le> d\<close>
    apply (subst dist_inv_avg_register_rewrite[where R=\<open>(adv_output_in_xo; aux_in_xo)\<close> and J=\<open>\<lambda>h. ket_invariant {(x, y). h x \<noteq> 0}\<close>])
      apply (simp, simp)
    apply (rewrite at \<open>{(x, y). h x \<noteq> 0}\<close> in for (h) to \<open>{x. h x \<noteq> 0} \<times> UNIV\<close> DEADID.rel_mono_strong)
     apply fastforce
    by (simp add: lift_inv_prod)
  then have \<open>dist_inv_avg adv_output (\<lambda>h. ket_invariant {x. h x \<noteq> 0}) final \<le> d\<close>
    by (simp add: xo_final_final[abs_def] adv_output_in_xo_def dist_inv_avg_Fst_tensor)
  then have \<open>(\<Sum>h\<in>UNIV. \<Sum>x|h x = 0. measurement_probability adv_output (final h) x) / CARD('x \<Rightarrow> 'y) \<le> d\<^sup>2\<close>
    apply (subst dist_inv_avg_measurement_probability)
     apply simp
    apply (rewrite at \<open>- {x. h x = 0}\<close> in \<open>\<lambda>h. \<hole>\<close> to \<open>{x. h x \<noteq> 0}\<close> DEADID.rel_mono_strong)
     apply blast
    by auto
  also have \<open>d\<^sup>2 = (5 * q + 11)\<^sup>2 / N\<close>
    by (simp add: d_def power2_eq_square)
  finally show ?thesis
    by (simp add: final_def q_def)
qed


end (* context compressed_oracle *)

end
