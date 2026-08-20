section \<open>\<open>Collision\<close> – Invariant preservation for collision resistance\<close>

theory Collision imports
  CO_Invariants
  Oracle_Programs
  Aux_Sturm_Calculation
begin

context compressed_oracle begin

definition \<open>no_collision = {(x,y,D::'x\<rightharpoonup>'y). inj_map D}\<close>
definition \<open>no_collision' = {D::'x\<rightharpoonup>'y. inj_map D}\<close>

lemma no_collision_no_collision': \<open>no_collision = UNIV \<times> UNIV \<times> no_collision'\<close>
  by (auto intro!: simp: no_collision_def no_collision'_def)

lemma ket_invariant_no_collision_no_collision': \<open>ket_invariant no_collision = \<top> \<otimes>\<^sub>S \<top> \<otimes>\<^sub>S ket_invariant no_collision'\<close>
  by (auto simp: ket_invariant_tensor no_collision_no_collision' simp flip: ket_invariant_UNIV)

text \<open>We show the preservation of the \<^const>\<open>no_collision\<close> invariant.
We show it with respect to the oracle \<^const>\<open>query\<close> first.\<close>

lemma preserves_no_collision: \<open>preserves_ket query (no_collision \<inter> num_queries q) no_collision (6 * sqrt q / sqrt N)\<close>
proof -
  define K where \<open>K = (\<lambda>(x::'x,D0::'x\<rightharpoonup>'y). ket_invariant {(x, y, D0(x:=d)) | (y::'y) d. 
                            D0 x = None \<and> card (dom D0) \<le> q \<and> inj_map D0})\<close>

  define I1 J1 :: \<open>('x\<rightharpoonup>'y) \<Rightarrow> ('y \<times> 'y option) set\<close> 
    where \<open>I1 D0 = UNIV \<times> (if card (dom D0) \<le> q then - Some ` ran D0 else {})\<close>
      and \<open>J1 D0 = (UNIV \<times> - Some ` ran D0)\<close>
    for D0 :: \<open>'x \<rightharpoonup> 'y\<close>

  show ?thesis
  proof (rule inv_split_reg_query[where X=\<open>reg_1_3\<close> and Y=\<open>reg_2_3\<close> and H=\<open>reg_3_3\<close> and K=K
        and ?I1.0=\<open>\<lambda>(x,D0). ket_invariant (I1 D0)\<close> and ?J1.0=\<open>\<lambda>(x,D0). ket_invariant (J1 D0)\<close>])
    show \<open>query = (reg_1_3;(reg_2_3;reg_3_3)) query\<close>
      by (auto simp: reg_1_3_def reg_2_3_def reg_3_3_def pair_Fst_Snd)
    show \<open>compatible reg_1_3 reg_2_3\<close> \<open>compatible reg_1_3 reg_3_3\<close> \<open>compatible reg_2_3 reg_3_3\<close>
      by simp_all
    show \<open>compatible_register_invariant reg_2_3 (K xD0)\<close> for xD0
      apply (cases xD0)
      by (auto simp add: K_def reg_2_3_def
          intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_Fst)
    show \<open>compatible_register_invariant (reg_3_3 o function_at (fst xD0)) (K xD0)\<close> for xD0
      apply (cases xD0)
      by (auto simp add: K_def reg_3_3_def comp_assoc
          intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_Fst
          compatible_register_invariant_function_at)

    have aux: \<open>inj_map b \<Longrightarrow>
           card (dom b) \<le> q \<Longrightarrow>
           \<exists>ba. (card (dom ba) \<le> q \<longrightarrow>
                 (\<exists>d. b = ba(a := d)) \<and> ba a = None \<and> inj_map ba \<and> b a \<notin> Some ` ran ba) \<and>
                card (dom ba) \<le> q\<close> for b a
      apply (intro exI[of _ \<open>b(a:=None)\<close>] exI[of _ \<open>b a\<close>] impI conjI)
          apply fastforce
         apply force
        apply (smt (verit, ccfv_SIG) array_rules(2) inj_map_def)
       apply (auto simp: ran_def inj_map_def)[1]
      by (simp add: dom_fun_upd card_Diff1_le[THEN order_trans])
    show \<open>ket_invariant (no_collision \<inter> num_queries q)
        \<le> (SUP xD0\<in>UNIV. K xD0 \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at (fst xD0)) (case xD0 of (x, D0) \<Rightarrow> ket_invariant (I1 D0)))\<close>
      by (auto intro!: aux simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric] I1_def
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv case_prod_beta
          no_collision_def num_queries_def)
    have aux: \<open>d \<notin> Some ` ran (snd xD0) \<Longrightarrow> inj_map (snd xD0) \<Longrightarrow> inj_map ((snd xD0)(fst xD0 := d))\<close> for d xD0
      by (smt (verit, del_insts) fun_upd_other fun_upd_same image_iff inj_map_def not_Some_eq ranI)
    show \<open>K xD0 \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at (fst xD0)) (case xD0 of (x, D0) \<Rightarrow> ket_invariant (J1 D0))
              \<le> ket_invariant no_collision\<close> for xD0
      apply (simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter
          ket_invariant_SUP[symmetric] J1_def lift_inv_prod lift_invariant_comp
          lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv case_prod_beta)
      unfolding no_collision_def
      using aux[of _ xD0] by auto
    have aux: \<open>b aa = None \<Longrightarrow>
       ba aa = None \<Longrightarrow>
       b \<noteq> ba \<Longrightarrow>
       card (dom b) \<le> q \<Longrightarrow>
       inj_map b \<Longrightarrow> card (dom ba) \<le> q \<Longrightarrow> inj_map ba \<Longrightarrow> b(aa := d) \<noteq> ba(aa := da)\<close>
      for aa b ba d da
      by (metis fun_upd_triv fun_upd_upd)
    have aux: \<open>\<And>b aa ba d da.
       b(aa := d) = ba(aa := da) \<Longrightarrow> 
       b aa = None \<Longrightarrow>
       ba aa = None \<Longrightarrow>
       b \<noteq> ba \<Longrightarrow>
       card (dom b) \<le> q \<Longrightarrow>
       inj_map b \<Longrightarrow> card (dom ba) \<le> q \<Longrightarrow> inj_map ba \<Longrightarrow> False\<close>
      by (metis fun_upd_triv fun_upd_upd)
    show \<open>orthogonal_spaces (K xD0) (K xD0')\<close> if \<open>xD0 \<noteq> xD0'\<close> for xD0 xD0'
      apply (cases xD0; cases xD0')
      unfolding K_def using that by (auto elim!: aux)
    have \<open>preserves_ket query1 (I1 D0) (J1 D0) (6 * sqrt q / sqrt N)\<close> for D0 :: \<open>'x\<rightharpoonup>'y\<close>
    proof (cases \<open>card (dom D0) \<le> q\<close>)
      case True
      have [simp]: \<open>card (ran D0) \<le> q\<close>
        using True ran_smaller_dom[of D0] by simp
      show ?thesis
        apply (simp add: I1_def J1_def True)
        apply (rule preserve_query1_simplified)
        by (auto simp add: inj_vimage_image_eq vimage_Compl)
    next
      case False
      then show ?thesis
        unfolding I1_def by simp
    qed
    then show \<open>preserves query1 (case xD0 of (x, D0) \<Rightarrow> ket_invariant (I1 D0)) (case xD0 of (x::'x, D0) \<Rightarrow> ket_invariant (J1 D0)) (6 * sqrt q / sqrt N)\<close> for xD0
      apply (cases xD0) by auto
    show \<open>6 * sqrt q / sqrt N \<ge> 0\<close>
      by auto
    show \<open>K xD0 \<le> lift_invariant reg_1_3 (ket_invariant {fst xD0})\<close> for xD0
      apply (cases xD0)
      by (auto simp add: K_def reg_1_3_def lift_Fst_ket_inv)
  qed simp
qed

text \<open>Like @{thm [source] preserves_no_collision} but with respect to the oracle \<^const>\<open>query\<close>.\<close>

lemma preserves_no_collision': \<open>preserves_ket query' (no_collision \<inter> num_queries q) no_collision (5 * sqrt q / sqrt N)\<close>
proof -
  define K where \<open>K = (\<lambda>(x::'x,D0::'x\<rightharpoonup>'y). ket_invariant {(x, y, D0(x:=d)) | (y::'y) d. 
                            D0 x = None \<and> card (dom D0) \<le> q \<and> inj_map D0})\<close>

  define I1 J1 :: \<open>('x\<rightharpoonup>'y) \<Rightarrow> ('y \<times> 'y option) set\<close> 
    where \<open>I1 D0 = UNIV \<times> (if card (dom D0) \<le> q then - Some ` ran D0 else {})\<close>
      and \<open>J1 D0 = (UNIV \<times> - Some ` ran D0)\<close>
    for D0 :: \<open>'x \<rightharpoonup> 'y\<close>

  show ?thesis
  proof (rule inv_split_reg_query'[where X=\<open>reg_1_3\<close> and Y=\<open>reg_2_3\<close> and H=\<open>reg_3_3\<close> and K=K
        and ?I1.0=\<open>\<lambda>(x,D0). ket_invariant (I1 D0)\<close> and ?J1.0=\<open>\<lambda>(x,D0). ket_invariant (J1 D0)\<close>])
    show \<open>query' = (reg_1_3;(reg_2_3;reg_3_3)) query'\<close>
      by (simp add: reg_1_3_def reg_2_3_def reg_3_3_def pair_Fst_Snd) 
    show \<open>compatible reg_1_3 reg_2_3\<close> \<open>compatible reg_1_3 reg_3_3\<close> \<open>compatible reg_2_3 reg_3_3\<close>
      by simp_all
    show \<open>compatible_register_invariant reg_2_3 (K xD0)\<close> for xD0
      apply (cases xD0)
      by (auto simp add: K_def reg_2_3_def
          intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_Fst)
    show \<open>compatible_register_invariant (reg_3_3 o function_at (fst xD0)) (K xD0)\<close> for xD0
      apply (cases xD0)
      by (auto simp add: K_def reg_3_3_def comp_assoc
          intro!: compatible_register_invariant_Snd_comp compatible_register_invariant_Fst
          compatible_register_invariant_function_at)
    have aux: \<open>inj_map b \<Longrightarrow>
           card (dom b) \<le> q \<Longrightarrow>
           \<exists>ba. (card (dom ba) \<le> q \<longrightarrow>
                 (\<exists>d. b = ba(a := d)) \<and> ba a = None \<and> inj_map ba \<and> b a \<notin> Some ` ran ba) \<and>
                card (dom ba) \<le> q\<close> for a b
      apply (intro exI[of _ \<open>b(a:=None)\<close>] exI[of _ \<open>b a\<close>] impI conjI)
          apply fastforce
         apply force
        apply (smt (verit, ccfv_SIG) array_rules(2) inj_map_def)
       apply (auto simp: ran_def inj_map_def)[1]
      by (simp add: dom_fun_upd card_Diff1_le[THEN order_trans])
    show \<open>ket_invariant (no_collision \<inter> num_queries q)
        \<le> (SUP xD0\<in>UNIV. K xD0 \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at (fst xD0)) (case xD0 of (x, D0) \<Rightarrow> ket_invariant (I1 D0)))\<close>
      by (auto intro!: aux simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter ket_invariant_SUP[symmetric] I1_def
          lift_inv_prod lift_invariant_comp lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv case_prod_beta
          no_collision_def num_queries_def)
    show \<open>K xD0 \<sqinter> lift_invariant (reg_2_3;reg_3_3 \<circ> function_at (fst xD0)) (case xD0 of (x, D0) \<Rightarrow> ket_invariant (J1 D0))
              \<le> ket_invariant no_collision\<close> for xD0
    proof -
      have aux: \<open>d \<notin> Some ` ran (snd xD0) \<Longrightarrow>
         snd xD0 (fst xD0) = None \<Longrightarrow>
         card (dom (snd xD0)) \<le> q \<Longrightarrow> inj_map (snd xD0) \<Longrightarrow> inj_map ((snd xD0)(fst xD0 := d))\<close> for d
        by (smt (verit, del_insts) fun_upd_other fun_upd_same image_iff inj_map_def not_Some_eq ranI)
      show ?thesis
        apply (simp add: K_def lift_Fst_ket_inv reg_1_3_def reg_2_3_def ket_invariant_inter
          ket_invariant_SUP[symmetric] J1_def lift_inv_prod lift_invariant_comp
          lift_invariant_function_at_ket_inv reg_3_3_def lift_Snd_ket_inv case_prod_beta no_collision_def)
        using aux by auto
    qed
    have aux: \<open>b aa = None \<Longrightarrow> ba aa = None \<Longrightarrow> b \<noteq> ba \<Longrightarrow> b(aa := d) = ba(aa := da) \<Longrightarrow> False\<close> for aa b ba d da
      by (metis fun_upd_triv fun_upd_upd)
    show \<open>orthogonal_spaces (K xD0) (K xD0')\<close> if \<open>xD0 \<noteq> xD0'\<close> for xD0 xD0'
      apply (cases xD0; cases xD0')
      unfolding K_def using that aux by auto
    have \<open>preserves_ket query1' (I1 D0) (J1 D0) (5 * sqrt q / sqrt N)\<close> for D0 :: \<open>'x\<rightharpoonup>'y\<close>
    proof (cases \<open>card (dom D0) \<le> q\<close>)
      case True
      have [simp]: \<open>card (ran D0) \<le> q\<close>
        using True ran_smaller_dom[of D0] by simp
      show ?thesis
        apply (simp add: I1_def J1_def True)
        apply (rule preserve_query1'_simplified)
        by (auto simp add: inj_vimage_image_eq vimage_Compl)
    next
      case False
      then show ?thesis
        unfolding I1_def by simp
    qed
    then show \<open>preserves query1' (case xD0 of (x, D0) \<Rightarrow> ket_invariant (I1 D0)) (case xD0 of (x::'x, D0) \<Rightarrow> ket_invariant (J1 D0)) (5 * sqrt q / sqrt N)\<close> for xD0
      apply (cases xD0) by auto
    show \<open>5 * sqrt q / sqrt N \<ge> 0\<close>
      by auto
    show \<open>K xD0 \<le> lift_invariant reg_1_3 (ket_invariant {fst xD0})\<close> for xD0
      apply (cases xD0)
      by (auto simp add: K_def reg_1_3_def lift_Fst_ket_inv)
  qed simp
qed

lemma preserves_no_collision_num: \<open>preserves_ket query (no_collision \<inter> num_queries q) (no_collision \<inter> num_queries (q+1)) (6 * sqrt q / sqrt N)\<close>
  apply (subst add_0_right[of \<open>6 * sqrt q / sqrt N\<close>, symmetric])
  apply (rule preserves_intersect_ket)
   apply (rule preserves_no_collision)
  apply (rule preserves_mono[OF preserves_num])
  by auto

lemma preserves_no_collision'_num: \<open>preserves_ket query' (no_collision \<inter> num_queries q) (no_collision \<inter> num_queries (q+1)) (5 * sqrt q / sqrt N)\<close>
  apply (subst add_0_right[of \<open>5 * sqrt q / sqrt N\<close>, symmetric])
  apply (rule preserves_intersect_ket)
   apply (rule preserves_no_collision')
  apply (rule preserves_mono[OF preserves_num'])
  by auto


subsection \<open>Collision-finding is hard for q-query adversaries\<close>

lemma collision_finding_is_hard:
  fixes program :: \<open>('mem, 'x, 'y) program\<close>
    and adv_output :: \<open>('x \<times> 'x) update \<Rightarrow> 'mem update\<close>
    and initial_state
  assumes [iff]: \<open>valid_program program\<close>
  assumes \<open>norm initial_state = 1\<close>
  assumes [register]: \<open>register adv_output\<close>
  shows \<open>(\<Sum>h\<in>UNIV. \<Sum>(x1,x2)|x1 \<noteq> x2 \<and> h x1 = h x2. measurement_probability adv_output (exec_program h program initial_state) (x1,x2)) / CARD('x \<Rightarrow> 'y)
                 \<le> 12 * (query_count program + 154)^3 / N\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]

  text \<open>In this game based proof, we consider three different quantum memory models:

\<^item> The one from the statement of the lemma, where the overall quantum state lives in \<^typ>\<open>'mem\<close>,
  and the adversary output register is described by \<^term>\<open>adv_output\<close>, and the initial state
  in \<^term>\<open>initial_state\<close>. The program \<^term>\<open>program\<close> assumes this memory model.
\<^item> The "extra output" (short XO) memory model, where there is an extra auxiliary register \<open>aux\<close> of type \<^typ>\<open>'y\<times>'y\<close>.
  The type of the memory is then \<^typ>\<open>'mem \<times> ('y \<times> 'y)\<close>. (I.e., the extra register is in addition to the content of \<^typ>\<open>'mem\<close>.)
\<^item> The "compressed oracle" (short CO) memory model, where additionally to XO, we have an oracle register
  that can holds the content of the compressed oracle (or the standard oracle).\<close>

  text \<open>Since the register \<^term>\<open>adv_output :: _ \<Rightarrow> ('mem ell2 \<Rightarrow>\<^sub>C\<^sub>L 'mem ell2)\<close> is defined w.r.t. a specific memory,
    we define convenience definitions for the same register as it would be accessed in the other memories:\<close>

  define adv_output_in_xo :: \<open>('x\<times>'x) update \<Rightarrow> ('mem\<times>'y\<times>'y) update\<close> where \<open>adv_output_in_xo = Fst o adv_output\<close>
  define adv_output_in_co :: \<open>('x\<times>'x) update \<Rightarrow> (('mem\<times>'y\<times>'y) \<times> ('x\<rightharpoonup>'y)) update\<close> where \<open>adv_output_in_co = Fst o adv_output_in_xo\<close>

  text \<open>Analogously, we defined the \<open>aux\<close>-register and the oracle register in the applicable memories:\<close>

  define aux_in_xo :: \<open>('y\<times>'y) update \<Rightarrow> ('mem\<times>'y\<times>'y) update\<close> where \<open>aux_in_xo = Snd\<close>
  define aux_in_co :: \<open>('y\<times>'y) update \<Rightarrow> (('mem\<times>'y\<times>'y) \<times> ('x\<rightharpoonup>'y)) update\<close> where \<open>aux_in_co = Fst o aux_in_xo\<close>
  define oracle_in_co :: \<open>('x\<rightharpoonup>'y) update \<Rightarrow> (('mem\<times>'y\<times>'y) \<times> ('x\<rightharpoonup>'y)) update\<close> where \<open>oracle_in_co = Snd\<close>
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
   \<^term>\<open>ket (0,0)\<close> in \<open>aux\<close> and \<^term>\<open>ket Map.empty\<close> (the fully undefined function) in the oracle register.\<close>

  define initial_state_in_xo where \<open>initial_state_in_xo = initial_state \<otimes>\<^sub>s ket ((0,0) :: 'y\<times>'y)\<close>
  define initial_state_in_co :: \<open>(('mem\<times>'y\<times>'y) \<times> ('x\<rightharpoonup>'y)) ell2\<close> where \<open>initial_state_in_co = initial_state_in_xo \<otimes>\<^sub>s ket Map.empty\<close>

  text \<open>We define an extended program \<open>ext_program\<close> that executes \<^term>\<open>program\<close>, followed by two additional queries to the oracle.
    Input register is the adversary output register. Output register is the additional register \<open>aux\<close>.
    Hence \<open>ext_program\<close> is only meaningful in the models XO and CO. (Our definition is for XO.)\<close>

  define ext_program where \<open>ext_program = lift_program Fst program
       @ [QueryStep (adv_output_in_xo o Fst) (aux_in_xo o Fst), QueryStep (adv_output_in_xo o Snd) (aux_in_xo o Snd)]\<close>
  have [iff]: \<open>valid_program ext_program\<close>
    by (auto intro!: valid_program_lift simp add: valid_program_append adv_output_in_xo_def aux_in_xo_def ext_program_def)

  text \<open>We define the final states of the programs \<^term>\<open>program\<close> and \<^term>\<open>ext_program\<close>, in the original model, and in XO, and CO.\<close>
  define final :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> 'mem ell2\<close> where \<open>final h = exec_program h program initial_state\<close> for h
  define xo_ext_final :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('mem\<times>'y\<times>'y) ell2\<close> where \<open>xo_ext_final h = exec_program h ext_program initial_state_in_xo\<close> for h
  define xo_final :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('mem\<times>'y\<times>'y) ell2\<close> where \<open>xo_final h = exec_program h (lift_program Fst program) initial_state_in_xo\<close> for h
  define co_ext_final :: \<open>(('mem\<times>'y\<times>'y) \<times> ('x\<rightharpoonup>'y)) ell2\<close> where \<open>co_ext_final = exec_program_with query' ext_program initial_state_in_co\<close>
  define co_final :: \<open>(('mem\<times>'y\<times>'y) \<times> ('x\<rightharpoonup>'y)) ell2\<close> where \<open>co_final = exec_program_with query' (lift_program Fst program) initial_state_in_co\<close>

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

  have co_ext_final_prefinal: 
       \<open>co_ext_final = (adv_output_in_co o Snd; (aux_in_co o Snd; oracle_in_co)) query' *\<^sub>V 
                       (adv_output_in_co o Fst; (aux_in_co o Fst; oracle_in_co)) query' *\<^sub>V co_final\<close>
    by (simp add: co_ext_final_def ext_program_def exec_program_with_append adv_output_in_co_def aux_in_co_def oracle_in_co_def comp_assoc
        flip: initial_state_in_co_def co_final_def)

  have xo_final_final: \<open>xo_final h = final h \<otimes>\<^sub>s ket (0,0)\<close> for h
    by (simp add: xo_final_def final_def initial_state_in_xo_def exec_lift_program_Fst)

  have xo_ext_final_xo_final: \<open>xo_ext_final h = (adv_output_in_xo o Snd; aux_in_xo o Snd) (function_oracle h) *\<^sub>V 
           (adv_output_in_xo o Fst; aux_in_xo o Fst) (function_oracle h) *\<^sub>V xo_final h\<close> for h
    by (simp add: xo_ext_final_def xo_final_def ext_program_def exec_program_def)

  text \<open>After executing \<^term>\<open>program\<close> (in XO), the \<open>aux\<close>-register is in state \<^term>\<open>ket (0,0)\<close>:\<close>
  have xo_final_has_y0: \<open>dist_inv_avg (adv_output_in_xo;aux_in_xo) (\<lambda>_. ket_invariant {(xx,yy). yy = (0,0)}) xo_final = 0\<close>
  proof -
    have \<open>dist_inv_avg aux_in_xo (\<lambda>_::'x\<Rightarrow>'y. ket_invariant {(0,0)}) xo_final
        \<le> dist_inv_avg aux_in_xo (\<lambda>_::'x\<Rightarrow>'y. ket_invariant {(0,0)}) (\<lambda>h. initial_state_in_xo)\<close>
      unfolding xo_final_def
      apply (subst dist_inv_avg_exec_compatible)
      using dist_inv_avg_exec_compatible
      by auto
    also have \<open>\<dots> = 0\<close>
      by (auto intro!: tensor_ell2_in_tensor_ccsubspace ket_in_ket_invariantI
          simp add: initial_state_in_xo_def dist_inv_0_iff distance_from_inv_avg0I aux_in_xo_def lift_Snd_inv)
    finally have \<open>dist_inv_avg aux_in_xo (\<lambda>_. ket_invariant {(0,0)}) xo_final = 0\<close>
      by (smt (verit, ccfv_SIG) dist_inv_avg_pos)
    then show ?thesis
      apply (rewrite at \<open>{(xx, yy). yy = (0,0)}\<close> to \<open>UNIV \<times> {(0,0)}\<close> DEADID.rel_mono_strong, blast)
      apply (subst dist_inv_avg_register_rewrite)
      by (simp_all add: lift_inv_prod)
  qed

  text \<open>Same as @{thm [source] xo_final_has_y0}, but in CO:\<close>
  have co_final_has_y0: \<open>dist_inv aao_in_co (ket_invariant {(x,y,D). y = (0,0)}) co_final = 0\<close>
  proof -
    have \<open>dist_inv aux_in_co (ket_invariant {(0,0)}) co_final
       \<le> dist_inv aux_in_co (ket_invariant {(0,0)}) initial_state_in_co\<close>
      unfolding co_final_def
      apply (rule dist_inv_exec'_compatible)
      by simp_all
    also have \<open>\<dots> = 0\<close>
      by (auto intro!: tensor_ell2_in_tensor_ccsubspace ket_in_ket_invariantI
          simp add: initial_state_in_co_def initial_state_in_xo_def dist_inv_0_iff
          aux_in_co_def aux_in_xo_def lift_Fst_inv lift_Snd_inv lift_invariant_comp)
    finally have \<open>dist_inv aux_in_co (ket_invariant {(0,0)}) co_final = 0\<close>
      by (smt (verit, best) dist_inv_pos)
    then show ?thesis
      apply (rewrite at \<open>{(xx, yy, D). yy = (0,0)}\<close> to \<open>UNIV \<times> {(0,0)} \<times> UNIV\<close> DEADID.rel_mono_strong, blast)
      apply (subst dist_inv_register_rewrite)
      by (simp_all add: lift_inv_prod aao_in_co_def)
  qed

  define q where \<open>q = query_count program\<close>
  text \<open>The following term occurs a lot (it's how much the \<^term>\<open>no_collision\<close> invariant is preserved after running \<^term>\<open>ext_program\<close>).
    So we abbreviate it as \<open>d\<close>.\<close>
  define d :: real where \<open>d = (10/3 * sqrt (q+2)^3 + 20) / sqrt N\<close>

  have [iff]: \<open>d \<ge> 0\<close>
    by (simp add: d_def)

  have \<open>dist_inv oracle_in_co (ket_invariant (no_collision' \<inter> num_queries' (q+2))) co_ext_final \<le> 10/3 * sqrt (q+2)^3 / sqrt N\<close>
      \<comment> \<open>In CO-execution, before the adversary's final query, the oracle register has no collision in its range (and we also track the number of queries to make the induction go through)\<close>
    unfolding co_ext_final_def
  proof (rule dist_inv_induct[where g=\<open>\<lambda>i::nat. 5 * sqrt i / sqrt N\<close>
          and J=\<open>\<lambda>i. ket_invariant (no_collision' \<inter> num_queries' i)\<close>])
    show \<open>compatible oracle_in_co Fst\<close>
      using oracle_in_co_def by simp
    show \<open>initial_state_in_co \<in> space_as_set (lift_invariant oracle_in_co (ket_invariant (no_collision' \<inter> num_queries' 0)))\<close>
      by (auto intro!: tensor_ell2_in_tensor_ccsubspace ket_in_ket_invariantI
          simp add: initial_state_in_co_def oracle_in_co_def lift_Snd_ket_inv inj_map_def num_queries'_def
          initial_state_in_xo_def tensor_ell2_ket ket_in_ket_invariantI no_collision'_def
         simp flip: ket_invariant_tensor)
    show \<open>ket_invariant (no_collision' \<inter> num_queries' (query_count ext_program)) \<le> ket_invariant (no_collision' \<inter> num_queries' (q+2))\<close>
      by (simp add: q_def ext_program_def)
    show \<open>valid_program ext_program\<close>
      by simp
    show \<open>preserves ((Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) query') (lift_invariant oracle_in_co (ket_invariant (no_collision' \<inter> num_queries' i)))
        (lift_invariant oracle_in_co (ket_invariant (no_collision' \<inter> num_queries' (Suc i)))) (5 * sqrt i / sqrt N)\<close>
            if [register]: \<open>compatible X_in_xo Y_in_xo\<close> for X_in_xo Y_in_xo i
    proof -
      from preserves_no_collision'_num
      have \<open>preserves ((Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) query')
            (lift_invariant (Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) (ket_invariant (no_collision \<inter> num_queries i)))
            (lift_invariant (Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) (ket_invariant (no_collision \<inter> num_queries (i+1))))
            (5 * sqrt (real i) / sqrt N)\<close>
        apply (rule preserves_lift_invariant[THEN iffD2, rotated])
        by simp
      moreover have \<open>lift_invariant (Fst \<circ> X_in_xo;(Fst \<circ> Y_in_xo;Snd)) (ket_invariant (no_collision \<inter> num_queries i))
                   = lift_invariant oracle_in_co (ket_invariant (no_collision' \<inter> num_queries' i))\<close> for i
        by (simp add: oracle_in_co_def no_collision_no_collision' num_queries_num_queries' lift_inv_prod Times_Int_Times)
      ultimately show ?thesis
        by simp
    qed
    show \<open>norm query' \<le> 1\<close>
      by simp
    show \<open>norm initial_state_in_co \<le> 1\<close>
      by simp
    show \<open>(\<Sum>i<query_count ext_program. 5 * sqrt i / sqrt N) \<le> 10/3 * sqrt (q+2)^3 / sqrt N\<close>
    proof -
      have \<open>(\<Sum>i<q+2. sqrt i) \<le> 2/3 * sqrt (q+2) ^ 3\<close>
        by (rule sum_sqrt)
      then have \<open>(\<Sum>i<q+2. 5 * sqrt i / sqrt N) \<le> 5 * (2/3 * sqrt (q+2) ^ 3) / sqrt N\<close>
        by (auto intro!: divide_right_mono real_sqrt_ge_zero simp only: simp flip: sum_distrib_left sum_divide_distrib)
      also have \<open>\<dots> = 10/3 * sqrt (q+2)^3 / sqrt N\<close>
        by simp
      finally
      show \<open>(\<Sum>i<query_count ext_program. 5 * sqrt i / sqrt N) \<le> 10/3 * sqrt (q+2)^3 / sqrt N\<close>
        by (simp add: q_def ext_program_def)
    qed
  qed

  then have \<open>dist_inv oracle_in_co (ket_invariant no_collision') co_ext_final \<le> 10/3 * sqrt (q+2)^3 / sqrt N\<close>
      \<comment> \<open>Like the previous but without the number of queries)\<close>
    apply (rule le_back_subst_le)
    apply (rule dist_inv_mono)
    by auto

  then have dist_collision: \<open>dist_inv aao_in_co (ket_invariant no_collision) co_ext_final \<le> 10/3 * sqrt (q+2)^3 / sqrt N\<close>
      \<comment> \<open>Same thing, but expressed w.r.t. different register\<close>
    apply (rule le_back_subst)
    apply (rule dist_inv_register_rewrite)
    by (auto intro!: simp: aao_in_co_def no_collision_no_collision' lift_inv_prod)

  have dist_Dxy: \<open>dist_inv aao_in_co (ket_invariant {((x1,x2),(y1,y2),D). D x1 = Some y1 \<and> D x2 = Some y2}) co_ext_final \<le> 20 / sqrt N\<close>
  proof -
    have aao_in_co_decomp: \<open>aao_in_co = ((adv_output_in_co o Fst; adv_output_in_co o Snd); ((aux_in_co o Fst; aux_in_co o Snd); oracle_in_co))\<close>
      by (simp add: register_pair_Snd register_pair_Fst aao_in_co_def flip: register_comp_pair comp_assoc)
    have \<open>dist_inv ((adv_output_in_co \<circ> Fst;adv_output_in_co \<circ> Snd);((aux_in_co \<circ> Fst;aux_in_co \<circ> Snd);oracle_in_co))
     (ket_invariant {((x1, x2), (y1, y2), D). y1 = 0 \<and> y2 = 0}) co_final = 0\<close>
      using co_final_has_y0
      by (simp add: aao_in_co_decomp case_prod_unfold prod_eq_iff)
    then show ?thesis
      apply (rewrite at \<open>20 / sqrt N\<close> to \<open>0 + 20 / sqrt N\<close> DEADID.rel_mono_strong, simp)
      unfolding co_ext_final_prefinal aao_in_co_decomp
      apply (rule dist_inv_double_query')
      by (simp_all add: aao_in_co_decomp)
  qed

  have \<open>dist_inv aao_in_co
          (ket_invariant {((x1,x2),(y1,y2),D). inj_map D \<and> D x1 = Some y1 \<and> D x2 = Some y2}) co_ext_final \<le> d\<close> (is \<open>?lhs \<le> d\<close>)
    \<comment> \<open>In CO-execution, after the adversary's final query, the oracle register has no collision,
        and the aux register contains the outputs of the oracle function evaluated on the adversary output registers.\<close>
  proof -
    have \<open>?lhs = dist_inv aao_in_co (ket_invariant no_collision \<sqinter> ket_invariant {((x1,x2),(y1,y2),D). D x1 = Some y1 \<and> D x2 = Some y2}) co_ext_final\<close>
      apply (rule arg_cong3[where f=dist_inv])
      by (auto intro!: simp: no_collision_def ket_invariant_inter)
    also have \<open>\<dots> \<le> sqrt ((dist_inv aao_in_co (ket_invariant no_collision) co_ext_final)\<^sup>2
                        + (dist_inv aao_in_co (ket_invariant {((x1,x2),(y1,y2),D). D x1 = Some y1 \<and> D x2 = Some y2}) co_ext_final)\<^sup>2)\<close>
      apply (rule dist_inv_intersect)
      by auto
    also have \<open>\<dots> \<le> sqrt ((10/3 * sqrt (q+2)^3 / sqrt N)\<^sup>2 + (20 / sqrt N)\<^sup>2)\<close>
      apply (rule real_sqrt_le_mono)
      apply (rule add_mono)
      using dist_collision dist_Dxy
      by auto
    also have \<open>\<dots> \<le> (10/3 * sqrt (q+2)^3 + 20) / sqrt N\<close>
      apply (rule sqrt_sum_squares_le_sum[THEN order_trans])
      by (auto, argo)
    finally show ?thesis
      by (simp add: d_def)
  qed
  then have \<open>dist_inv aao_in_co (ket_invariant {((x1,x2),(y1,y2),D). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2}) co_ext_final \<le> d\<close>
    \<comment> \<open>In CO-execution, after the adversary's final query, the auxiliary registers are non-equal (if the adversary registers are).\<close>
    apply (rule le_back_subst_le)
    apply (rule dist_inv_mono)
    by (auto simp: inj_map_def)
  then have \<open>dist_inv (adv_output_in_co; aux_in_co) (ket_invariant {((x1,x2), (y1,y2)). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2}) co_ext_final \<le> d\<close>
    \<comment> \<open>As before, but with respect to a different register (without the oracle register that doesn't exist in XO).\<close>
    apply (rule le_back_subst)
    apply (rule dist_inv_register_rewrite)
      apply (simp, simp)
    apply (rewrite at \<open>(adv_output_in_co;aux_in_co)\<close> to \<open>aao_in_co o (reg_1_3; reg_2_3)\<close> DEADID.rel_mono_strong)
     apply (simp add: aao_in_co_def flip: register_comp_pair)
    apply (subst lift_invariant_comp, simp)
    by (auto intro!: simp: lift_inv_prod' reg_1_3_def reg_3_3_def reg_2_3_def lift_invariant_comp lift_Snd_ket_inv lift_Fst_ket_inv
        ket_invariant_inter  case_prod_unfold 
        simp flip: ket_invariant_SUP)
  then have *: \<open>dist_inv_avg (adv_output_in_xo; aux_in_xo) (\<lambda>h. ket_invariant {((x1,x2), (y1,y2)). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2}) xo_ext_final \<le> d\<close>
    \<comment> \<open>In XO-execution, after the adversary's final query, the adversary output register is not 0.\<close>
    apply (rule le_back_subst)
    unfolding co_ext_final_def xo_ext_final_def
    apply (rewrite at \<open>(adv_output_in_co;aux_in_co)\<close> to \<open>Fst o (adv_output_in_xo;aux_in_xo)\<close> DEADID.rel_mono_strong)
     apply (simp add: adv_output_in_co_def aux_in_co_def register_comp_pair) 
    by (simp add: initial_state_in_co_def dist_inv_exec_query'_exec_fixed)
  have \<open>dist_inv_avg (adv_output_in_xo; aux_in_xo)
          (\<lambda>h. ket_invariant {((x1,x2), yy). (x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2) \<or> yy \<noteq> (0,0)}) xo_final \<le> d\<close>
    \<comment> \<open>In XO-execution, before the adversary's final query, x1,x2 are a collision, or the aux register is nonzero.\<close>
  proof -
    define state2 where \<open>state2 h = (adv_output_in_xo o Fst; aux_in_xo o Fst) (function_oracle h) *\<^sub>V xo_final h\<close> for h
    have xo_ext_final_state2: \<open>xo_ext_final h = (adv_output_in_xo \<circ> Snd;aux_in_xo \<circ> Snd) (function_oracle h) *\<^sub>V state2 h\<close> for h
      using state2_def xo_ext_final_xo_final by presburger
    have fo_apply2: \<open>(Snd \<otimes>\<^sub>r Snd) (function_oracle h)* *\<^sub>S ket_invariant {((x1, x2), y1, y2). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2}
         \<le> ket_invariant {((x1,x2), (y1,y2)). (x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> h x2) \<or> y2 \<noteq> 0}\<close> for h :: \<open>'x \<Rightarrow> 'y\<close>
    proof -
      have \<open>(Snd \<otimes>\<^sub>r Snd) (function_oracle h)* *\<^sub>S ket_invariant {((x1, x2), y1, y2). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2}
          = (Snd \<otimes>\<^sub>r Snd) (function_oracle h) *\<^sub>S ket_invariant {((x1, x2), y1, y2). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2}\<close>
        by (simp add: uminus_y flip: register_adj)
      also have \<open>\<dots> = lift_invariant (Fst \<otimes>\<^sub>r Fst;Snd \<otimes>\<^sub>r Snd) (Snd (function_oracle h) *\<^sub>S ket_invariant {((x1, y1), x2, y2). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2})\<close>
        apply (rewrite at \<open>(Snd \<otimes>\<^sub>r Snd)\<close> to \<open>(Fst \<otimes>\<^sub>r Fst; Snd \<otimes>\<^sub>r Snd) o Snd\<close> DEADID.rel_mono_strong)
         apply (simp add: register_pair_Snd compatible_register_tensor)
        apply (rewrite at \<open>ket_invariant {((x1, x2), y1, y2). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2}\<close>
            to \<open>lift_invariant (Fst \<otimes>\<^sub>r Fst; Snd \<otimes>\<^sub>r Snd) (ket_invariant {((x1, y1), x2, y2). x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2})\<close> DEADID.rel_mono_strong)
         apply (auto intro!: simp: lift_inv_prod' compatible_register_tensor lift_inv_tensor' lift_Fst_ket_inv lift_Snd_ket_inv
            ket_invariant_tensor case_prod_unfold ket_invariant_inter
            simp flip: ket_invariant_SUP)[1]
        by (simp add: o_apply register_image_lift_invariant compatible_register_tensor register_isometry)
      also have \<open>\<dots> = lift_invariant (Fst \<otimes>\<^sub>r Fst; Snd \<otimes>\<^sub>r Snd)  (ket_invariant {((x1, y1), (x2, y2 + h x2)) | x1 y1 x2 y2. x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> y2})\<close>
        apply (simp add: function_oracle_Snd_ket_invariant)
        apply (rule arg_cong[where f=\<open>\<lambda>x. lift_invariant _ (ket_invariant x)\<close>])
        by (auto simp add: image_iff)
      also have \<open>\<dots> \<le> lift_invariant (Fst \<otimes>\<^sub>r Fst; Snd \<otimes>\<^sub>r Snd)  (ket_invariant {((x1, y1), (x2, y2)). (x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> h x2) \<or> y2 \<noteq> 0})\<close>
      proof -
        have aux: \<open>x1 \<noteq> x2 \<Longrightarrow> h x2 \<noteq> y2 \<Longrightarrow> y2 + h x2 \<noteq> 0\<close> for x1 x2 y2
          by (metis add_right_cancel y_cancel)
        show ?thesis
          apply (rule lift_invariant_mono, simp add: compatible_register_tensor)
          apply (rule ket_invariant_mono)
          using aux by auto
      qed
      also have \<open>\<dots> = ket_invariant {((x1, x2), (y1, y2)). (x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> h x2) \<or> y2 \<noteq> 0}\<close>
        by (auto intro!: simp: lift_inv_prod' compatible_register_tensor lift_inv_tensor' lift_Fst_ket_inv lift_Snd_ket_inv
            ket_invariant_tensor case_prod_unfold ket_invariant_inter
            simp flip: ket_invariant_SUP)[1]
      finally show ?thesis
        by -
    qed
    have fo_apply1: \<open>(Fst \<otimes>\<^sub>r Fst) (function_oracle h)* *\<^sub>S ket_invariant {((x1, x2), (y1, y2)). x1 \<noteq> x2 \<longrightarrow> y1 = h x2 \<longrightarrow> y2 \<noteq> 0}
         \<le> ket_invariant {((x1,x2), yy). (x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2) \<or> yy \<noteq> (0,0)}\<close> for h :: \<open>'x \<Rightarrow> 'y\<close>
    proof -
      have \<open>(Fst \<otimes>\<^sub>r Fst) (function_oracle h)* *\<^sub>S ket_invariant {((x1, x2), (y1, y2)). x1 \<noteq> x2 \<longrightarrow> y1 = h x2 \<longrightarrow> y2 \<noteq> 0}
          = (Fst \<otimes>\<^sub>r Fst) (function_oracle h) *\<^sub>S ket_invariant {((x1, x2), (y1, y2)). x1 \<noteq> x2 \<longrightarrow> y1 = h x2 \<longrightarrow> y2 \<noteq> 0}\<close>
        by (simp add: uminus_y flip: register_adj)
      also have \<open>\<dots> = lift_invariant (Snd \<otimes>\<^sub>r Snd;Fst \<otimes>\<^sub>r Fst) (Snd (function_oracle h) *\<^sub>S ket_invariant {((x2, y2), (x1, y1)). x1 \<noteq> x2 \<longrightarrow> y1 = h x2 \<longrightarrow> y2 \<noteq> 0})\<close>
        apply (rewrite at \<open>(Fst \<otimes>\<^sub>r Fst)\<close> to \<open>(Snd \<otimes>\<^sub>r Snd; Fst \<otimes>\<^sub>r Fst) o Snd\<close> DEADID.rel_mono_strong)
         apply (simp add: register_pair_Snd compatible_register_tensor)
        apply (rewrite at \<open>ket_invariant {((x1, x2), (y1, y2)). x1 \<noteq> x2 \<longrightarrow> y1 = h x2 \<longrightarrow> y2 \<noteq> 0}\<close>
            to \<open>lift_invariant (Snd \<otimes>\<^sub>r Snd; Fst \<otimes>\<^sub>r Fst) (ket_invariant {((x2, y2), (x1, y1)). x1 \<noteq> x2 \<longrightarrow> y1 = h x2 \<longrightarrow> y2 \<noteq> 0})\<close> DEADID.rel_mono_strong)
         apply (auto intro!: simp: lift_inv_prod' compatible_register_tensor lift_inv_tensor' lift_Snd_ket_inv lift_Fst_ket_inv
            ket_invariant_tensor case_prod_unfold ket_invariant_inter
            simp flip: ket_invariant_SUP)[1]
        by (simp_all add: o_apply register_image_lift_invariant compatible_register_tensor register_isometry)
      also have \<open>\<dots> = lift_invariant (Snd \<otimes>\<^sub>r Snd; Fst \<otimes>\<^sub>r Fst)  (ket_invariant {((x2, y2), (x1, y1 + h x1)) | x1 y1 x2 y2. x1 \<noteq> x2 \<longrightarrow> y1 = h x2 \<longrightarrow> y2 \<noteq> 0})\<close>
        apply (simp add: function_oracle_Snd_ket_invariant)
        apply (rule arg_cong[where f=\<open>\<lambda>x. lift_invariant _ (ket_invariant x)\<close>])
        by (auto simp add: image_iff)
      also have \<open>\<dots> \<le> lift_invariant (Snd \<otimes>\<^sub>r Snd; Fst \<otimes>\<^sub>r Fst)  (ket_invariant {((x2, y2), (x1, y1)). (x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2) \<or> (y1,y2) \<noteq> (0,0)})\<close>
      proof -
        have aux: \<open>y1 + h x2 = 0 \<Longrightarrow> x1 \<noteq> x2 \<Longrightarrow> h x1 = h x2 \<Longrightarrow> y1 = h x2\<close> for y1 x2 x1
          by (metis add_right_cancel y_cancel)
        show ?thesis
        apply (rule lift_invariant_mono, simp add: compatible_register_tensor)
        apply (rule ket_invariant_mono)
          using aux by auto
      qed
      also have \<open>\<dots> = ket_invariant {((x1,x2), yy). (x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2) \<or> yy \<noteq> (0,0)}\<close>
        by (auto intro!: simp: lift_inv_prod' compatible_register_tensor lift_inv_tensor' lift_Snd_ket_inv lift_Fst_ket_inv
            ket_invariant_tensor case_prod_unfold ket_invariant_inter
            simp flip: ket_invariant_SUP)[1]
      finally show ?thesis
        by -
    qed
    from * have \<open>dist_inv_avg (adv_output_in_xo; aux_in_xo)
          (\<lambda>h. ket_invariant {((x1,x2), (y1,y2)). (x1 \<noteq> x2 \<longrightarrow> y1 \<noteq> h x2) \<or> y2 \<noteq> 0}) state2 \<le> d\<close>
      apply (rule le_back_subst_le)
      unfolding xo_ext_final_state2[abs_def]
      apply (subst dist_inv_avg_apply[where U=\<open>\<lambda>h. function_oracle h\<close> and S=\<open>Snd \<otimes>\<^sub>r Snd\<close>])
      using fo_apply2 by (auto intro!: dist_inv_avg_mono simp: function_oracle_ket_invariant pair_o_tensor simp del: o_apply)
    then show ?thesis
      apply (rule le_back_subst_le)
      unfolding state2_def[abs_def]
      apply (subst dist_inv_avg_apply[where U=\<open>\<lambda>h. function_oracle h\<close> and S=\<open>Fst \<otimes>\<^sub>r Fst\<close>])
      using fo_apply1 by (auto intro!: dist_inv_avg_mono simp: function_oracle_ket_invariant pair_o_tensor simp del: o_apply)
  qed
  then have *: \<open>dist_inv_avg (adv_output_in_xo; aux_in_xo)
          (\<lambda>h. ket_invariant {((x1,x2), yy). x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2}) xo_final \<le> d\<close>
    \<comment> \<open>In XO-execution, before the adversary's final query, x1,x2 are a collision.\<close>
    apply (rule le_back_subst_le)
    apply (rule ord_le_eq_trans)
     apply (rule dist_inv_avg_mono[where I=\<open>\<lambda>h. ket_invariant {((x1,x2), yy). (x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2) \<or> yy \<noteq> (0,0)} \<sqinter> ket_invariant {(xx,yy). yy=(0,0)}\<close>])
      apply (auto simp: ket_invariant_inter)[2]
    apply (rule dist_inv_avg_intersect)
       apply simp_all[2]
    by (fact xo_final_has_y0)
  then have \<open>dist_inv_avg adv_output_in_xo
          (\<lambda>h. ket_invariant {(x1,x2). x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2}) xo_final \<le> d\<close>
    \<comment> \<open>As before, but with respect to only the adversary output register.\<close>
    apply (subst dist_inv_avg_register_rewrite[where R=\<open>(adv_output_in_xo; aux_in_xo)\<close> and J=\<open>\<lambda>h. ket_invariant {((x1,x2),yy). x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2}\<close>])
       apply (simp, simp)
     apply (rewrite at \<open>{((x1,x2),yy). x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2}\<close> in for (h) to \<open>{(x1,x2). x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2} \<times> UNIV\<close> DEADID.rel_mono_strong)
      apply fastforce
    by (simp add: lift_inv_prod)
  then have \<open>dist_inv_avg adv_output (\<lambda>h. ket_invariant {(x1,x2). x1 \<noteq> x2 \<longrightarrow> h x1 \<noteq> h x2}) final \<le> d\<close>
    \<comment> \<open>As before, but in the original execution.\<close>
    by (simp add: xo_final_final[abs_def] adv_output_in_xo_def dist_inv_avg_Fst_tensor)
  then have \<open>(\<Sum>h\<in>UNIV. \<Sum>(x1,x2)|x1 \<noteq> x2 \<and> h x1 = h x2. measurement_probability adv_output (final h) (x1,x2)) / CARD('x \<Rightarrow> 'y) \<le> d\<^sup>2\<close>
    unfolding case_prod_unfold prod.collapse
    apply (subst dist_inv_avg_measurement_probability)
     apply simp
    apply (rewrite at \<open>- {p. fst p \<noteq> snd p \<and> h (fst p) = h (snd p)}\<close> in \<open>\<lambda>h. \<hole>\<close> to \<open>{p. fst p \<noteq> snd p \<longrightarrow> h (fst p) \<noteq> h (snd p)}\<close> DEADID.rel_mono_strong)
     apply blast
    by auto
  also have \<open>d\<^sup>2 \<le> 12 * (q+154)^3 / N\<close>
  proof -
    define r where \<open>r = sqrt q\<close>
    have [iff]: \<open>r \<ge> 0\<close>
      using r_def by force
    have 1: \<open>sqrt (r\<^sup>2 + 2) \<le> r + 2\<close>
      apply (rule real_le_lsqrt)
      by (simp_all add: power2_sum)
    have \<open>N * d\<^sup>2 = (10/3 * sqrt (r\<^sup>2+2)^3 + 20)\<^sup>2\<close>
      apply (simp add: d_def power_divide of_nat_add r_def) by argo
    also have \<open>\<dots> \<le> (10/3 * (r+2)^3 + 20)\<^sup>2\<close>
      using 1 by (auto intro!: power_mono add_right_mono mult_left_mono)
    also have \<open>\<dots> \<le> 12 * (r\<^sup>2+154)^3\<close>
    proof -
      define f where \<open>f r = 12 * (r\<^sup>2+154)^3 - (10/3 * (r+2)^3 + 20)\<^sup>2\<close> for r :: real
      have fr: \<open>f r \<noteq> 0\<close> if \<open>r \<ge> 0\<close> for r :: real
        unfolding f_def using that by (rule sturm_calculation) (* Outsourced because the method fails if called here. *)
      have f0: \<open>f 0 \<ge> 0\<close>
        by (simp add: f_def power2_eq_square)
      have \<open>isCont f r\<close> for r
        unfolding f_def
        by (intro continuous_intros)
      have \<open>f r \<ge> 0\<close> if \<open>r \<ge> 0\<close> for r :: real
      proof (rule ccontr)
        assume \<open>\<not> 0 \<le> f r\<close>
        then have \<open>\<exists>x\<ge>0. x \<le> r \<and> f x = 0\<close>
          apply (rule_tac IVT2[where f=f and a=0 and b=r and y=0])
          by (auto intro!: \<open>isCont f _\<close> simp: f0 that)
        then show False
          using fr by blast
      qed
      then show ?thesis
        by (simp add: f_def)
    qed
    finally show ?thesis
      apply (rule_tac mult_left_le_imp_le[where c=\<open>real N\<close>])
      using Nneq0 r_def by force+
  qed
  finally show ?thesis
    by (simp add: final_def q_def)
qed

end (* context compressed_oracle *)

end
