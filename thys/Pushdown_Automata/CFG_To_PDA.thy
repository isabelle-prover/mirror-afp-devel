section \<open>Equivalence of CFG and PDA\<close>

subsection \<open>CFG to PDA\<close>

text \<open>Starting from a CFG, we construct an equivalent single-state PDA.
The formalization is based on the Lean formalization by Leichtfried\cite{lean}.\<close>

theory CFG_To_PDA
imports
  Pushdown_Automata
  Context_Free_Grammar.Context_Free_Grammar
begin

datatype sing_st = Q_loop

instance sing_st :: finite
proof
  have *: "UNIV = {Q_loop}"
    by (auto intro: sing_st.exhaust)
  show "finite (UNIV :: sing_st set)"
    by (simp add: *)
qed

instance sym :: (finite, finite) finite
proof
  have *: "UNIV = {t. \<exists>s. t = Nt s} \<union> {t. \<exists>s. t = Tm s}"
    by (auto intro: sym.exhaust)
  show "finite (UNIV :: ('a, 'b) sym set)"
    by (simp add: * full_SetCompr_eq)
qed

locale cfg_to_pda =
  fixes G :: "('n :: finite, 't :: finite) Cfg"
  assumes finite_G: "finite (Prods G)"
begin

fun pda_of_cfg :: "sing_st \<Rightarrow> 't \<Rightarrow> ('n,'t) sym \<Rightarrow> (sing_st \<times> ('n,'t) syms) set" where
  "pda_of_cfg Q_loop a (Tm b) = (if a = b then {(Q_loop, [])} else {})"
| "pda_of_cfg _ _ _ = {}"

fun pda_eps_of_cfg :: "sing_st \<Rightarrow> ('n,'t) sym \<Rightarrow> (sing_st \<times> ('n,'t) syms) set" where
  "pda_eps_of_cfg Q_loop (Nt A) = {(Q_loop, \<alpha>)| \<alpha>. (A, \<alpha>) \<in> Prods G}"
| "pda_eps_of_cfg _ _ = {}"

definition cfg_to_pda_pda :: "(sing_st, 't, ('n,'t) sym) pda" where
  "cfg_to_pda_pda \<equiv> \<lparr> init_state = Q_loop, init_symbol = Nt (Start G), final_states = {}, 
                    delta = pda_of_cfg, delta_eps = pda_eps_of_cfg \<rparr>"

lemma pda_cfg_to_pda: "pda cfg_to_pda_pda"
proof (standard, goal_cases)
  case (1 p x z)
  have "finite (pda_of_cfg p x z)"
    by (induction p x z rule: pda_of_cfg.induct) auto
  then show ?case
    by (simp add: cfg_to_pda_pda_def)
next
  case (2 p z)
  let ?h = "\<lambda>(A,\<alpha>). (Q_loop, \<alpha>)"
  have *: "\<And>A. {(Q_loop, \<alpha>) |\<alpha>. (A, \<alpha>) \<in> Prods G} \<subseteq> (?h ` Prods G)" by auto
  have **: "finite (?h ` Prods G)"
    by (simp add: finite_G)
  have "\<And>A. finite {(Q_loop, \<alpha>) |\<alpha>. (A, \<alpha>) \<in> Prods G}"
    using finite_subset[OF * **] by simp
  hence "finite (pda_eps_of_cfg p z)"
    by (induction p z rule: pda_eps_of_cfg.induct) auto
  then show ?case
    by (simp add: cfg_to_pda_pda_def)
qed

lemma cfg_to_pda_cons_tm:
  "pda.step\<^sub>1 cfg_to_pda_pda (Q_loop, a#w, Tm a#\<gamma>) (Q_loop, w, \<gamma>)"
using pda.step\<^sub>1_rule[OF pda_cfg_to_pda] by (simp add: cfg_to_pda_pda_def)

lemma cfg_to_pda_cons_nt:
  assumes "(A, \<alpha>) \<in> Prods G"
  shows "pda.step\<^sub>1 cfg_to_pda_pda (Q_loop, w, Nt A#\<gamma>) (Q_loop, w, \<alpha>@\<gamma>)"
using assms pda.step\<^sub>1_rule[OF pda_cfg_to_pda] by (simp add: cfg_to_pda_pda_def)

lemma cfg_to_pda_cons_tms:
  "pda.steps cfg_to_pda_pda (Q_loop, w@w', map Tm w @ \<gamma>) (Q_loop, w', \<gamma>)"
proof (induction w)
  case (Cons a w)
  have "pda.step\<^sub>1 cfg_to_pda_pda (Q_loop, (a # w) @ w', map Tm (a # w) @ \<gamma>) (Q_loop, w @ w', map Tm w @ \<gamma>)"
    using cfg_to_pda_cons_tm by simp
  with Cons.IH show ?case
    using pda.step\<^sub>1_steps[OF pda_cfg_to_pda] pda.steps_trans[OF pda_cfg_to_pda] by blast
qed (simp add: pda.steps_refl[OF pda_cfg_to_pda])

lemma cfg_to_pda_nt_cons:
  assumes "pda.step\<^sub>1 cfg_to_pda_pda (Q_loop, w, Nt A#\<gamma>) (Q_loop, w', \<beta>)"
  shows "\<exists>\<alpha>. (A, \<alpha>) \<in> Prods G \<and> \<beta> = \<alpha> @ \<gamma> \<and> w' = w"
proof -
  from assms have "(\<exists>\<beta>\<^sub>0. w' = w \<and> \<beta> = \<beta>\<^sub>0@\<gamma> \<and> (Q_loop, \<beta>\<^sub>0) \<in> pda_eps_of_cfg Q_loop (Nt A)) 
                     \<or> (\<exists>a \<beta>\<^sub>0. w = a # w' \<and> \<beta> = \<beta>\<^sub>0@\<gamma> \<and> (Q_loop,\<beta>\<^sub>0) \<in> pda_of_cfg Q_loop a (Nt A))"
    using pda.step\<^sub>1_rule[OF pda_cfg_to_pda] by (simp add: cfg_to_pda_pda_def)
  thus ?thesis
    by (induction Q_loop "Nt A :: ('n, 't) sym" rule: pda_eps_of_cfg.induct) auto
qed

lemma cfg_to_pda_tm_stack_cons:
  assumes "pda.step\<^sub>1 cfg_to_pda_pda (Q_loop, w, Tm a # \<beta>) (Q_loop, w', \<beta>')"
  shows "w = a # w' \<and> \<beta> = \<beta>'"
proof -
  from assms have "(\<exists>\<beta>\<^sub>0. w' = w \<and> \<beta>' = \<beta>\<^sub>0@\<beta> \<and> (Q_loop, \<beta>\<^sub>0) \<in> pda_eps_of_cfg Q_loop (Tm a)) 
                   \<or> (\<exists>a\<^sub>0 \<beta>\<^sub>0. w = a\<^sub>0#w' \<and> \<beta>' = \<beta>\<^sub>0@\<beta> \<and> (Q_loop, \<beta>\<^sub>0) \<in> pda_of_cfg Q_loop a\<^sub>0 (Tm a))"
    using pda.step\<^sub>1_rule[OF pda_cfg_to_pda] by (simp add: cfg_to_pda_pda_def)
  thus ?thesis
    by (induction Q_loop "Tm a :: ('n, 't) sym" rule: pda_eps_of_cfg.induct, auto) (metis emptyE, metis empty_iff prod.inject singletonD)
qed

lemma cfg_to_pda_tm_stack_path:
  assumes "pda.steps cfg_to_pda_pda (Q_loop, w, Tm a # \<alpha>) (Q_loop, [], [])"
  shows "\<exists>w'. w = a#w' \<and> pda.steps cfg_to_pda_pda (Q_loop, w', \<alpha>) (Q_loop, [], [])"
proof -
  from assms obtain q' w' \<alpha>' where step1: "pda.step\<^sub>1 cfg_to_pda_pda (Q_loop, w, Tm a # \<alpha>) (q', w', \<alpha>')" and 
                                   steps: "pda.steps cfg_to_pda_pda (q', w', \<alpha>') (Q_loop, [], [])"
    using pda.steps_not_refl_split_first[OF pda_cfg_to_pda] by blast
  have q'_def: "q' = Q_loop"
    using sing_st.exhaust by blast
  from step1[unfolded q'_def] have "(\<exists>\<beta>\<^sub>0. w' = w \<and> \<alpha>' = \<beta>\<^sub>0@\<alpha> \<and> (Q_loop, \<beta>\<^sub>0) \<in> pda_eps_of_cfg Q_loop (Tm a)) 
                    \<or> (\<exists>a\<^sub>0 \<beta>\<^sub>0. w = a\<^sub>0#w' \<and> \<alpha>' = \<beta>\<^sub>0@\<alpha> \<and> (Q_loop, \<beta>\<^sub>0) \<in> pda_of_cfg Q_loop a\<^sub>0 (Tm a))"
    using pda.step\<^sub>1_rule[OF pda_cfg_to_pda] by (simp add: cfg_to_pda_pda_def)
  hence "w = a # w' \<and> \<alpha>' = \<alpha>"
    by (induction Q_loop "Tm a :: ('n, 't) sym" rule: pda_eps_of_cfg.induct, auto) (metis empty_iff, metis empty_iff prod.inject singletonD)
  with steps q'_def show ?thesis by simp
qed

lemma cfg_to_pda_tms_stack_path:
  assumes "pda.steps cfg_to_pda_pda (Q_loop, w, map Tm v @ \<alpha>) (Q_loop, [], [])"
  shows "\<exists>w'. w = v @ w' \<and> pda.steps cfg_to_pda_pda (Q_loop, w', \<alpha>) (Q_loop, [], [])"
using assms cfg_to_pda_tm_stack_path by (induction v arbitrary: w) fastforce+

lemma cfg_to_pda_accepts_if_G_derives:
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>l* map Tm w"
  shows "pda.steps cfg_to_pda_pda (Q_loop, w, \<alpha>) (Q_loop, [], [])"
using assms proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case
    using cfg_to_pda_cons_tms[where ?w' = "[]" and ?\<gamma> = "[]"] by simp 
next
  case (step y z)
  from step(1) obtain A \<alpha> u1 u2 where prod: "(A,\<alpha>) \<in> Prods G" and y_def: "y = map Tm u1 @ Nt A # u2" and z_def: "z = map Tm u1 @ \<alpha> @ u2"
    using derivel_iff[of "Prods G" y z] by blast
  from step(3) z_def obtain w' where w_def: "w = u1 @ w'" and 
                                     *: "pda.steps cfg_to_pda_pda (Q_loop, w', \<alpha> @ u2) (Q_loop, [], [])"
    using cfg_to_pda_tms_stack_path by blast

  from w_def y_def have "pda.steps cfg_to_pda_pda (Q_loop, w, y) (Q_loop, w', Nt A # u2)"
    using cfg_to_pda_cons_tms by simp

  moreover from prod have "pda.steps cfg_to_pda_pda (Q_loop, w', Nt A # u2) (Q_loop, w', \<alpha> @ u2)"
    using cfg_to_pda_cons_nt pda.step\<^sub>1_steps[OF pda_cfg_to_pda] by simp

  ultimately show ?case
    using * pda.steps_trans[OF pda_cfg_to_pda] by blast
qed

lemma G_derives_if_cfg_to_pda_accepts:
  assumes "pda.steps cfg_to_pda_pda (Q_loop, w, \<alpha>) (Q_loop, [], [])"
  shows "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
using assms proof (induction "(Q_loop, w, \<alpha>)" "(Q_loop, [] :: 't list, [] :: ('n, 't) syms)" 
                      arbitrary: w \<alpha> rule: pda.steps_induct2[OF pda_cfg_to_pda])
  case (3 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2)
  then show ?case proof (cases \<alpha>\<^sub>1)
    case (Cons Z' \<alpha>')
    have p\<^sub>2_def: "p\<^sub>2 = Q_loop"
      using sing_st.exhaust by blast
    with 3(2,3) have IH: "Prods G \<turnstile> \<alpha>\<^sub>2 \<Rightarrow>* map Tm w\<^sub>2" by simp
    show ?thesis proof (cases Z')
      case (Nt A)
      with Cons p\<^sub>2_def 3(1) obtain \<alpha> where prod: "(A, \<alpha>) \<in> Prods G" and \<alpha>\<^sub>2_def: "\<alpha>\<^sub>2 = \<alpha> @ \<alpha>'" and w\<^sub>2_def: "w\<^sub>2 = w\<^sub>1"
        using cfg_to_pda_nt_cons by blast
      from Cons Nt prod \<alpha>\<^sub>2_def have "Prods G \<turnstile> \<alpha>\<^sub>1 \<Rightarrow> \<alpha>\<^sub>2"
        using derive_iff by fast
      with IH w\<^sub>2_def show ?thesis by simp
    next
      case (Tm a)
      with Cons p\<^sub>2_def 3(1) have w_\<alpha>_def: "w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>' = \<alpha>\<^sub>2"
        using cfg_to_pda_tm_stack_cons by simp
      from IH have "Prods G \<turnstile> Tm a # \<alpha>\<^sub>2 \<Rightarrow>* Tm a # map Tm w\<^sub>2"
        using derives_Cons by auto
      with Cons Tm w_\<alpha>_def show ?thesis by simp
    qed
  qed (simp add: 3(1) pda.step\<^sub>1_empty_stack[OF pda_cfg_to_pda])
qed (simp_all add: assms)

lemma cfg_to_pda: "LangS G = pda.accept_stack cfg_to_pda_pda" (is "?L = ?P")
proof
  show "?L \<subseteq> ?P"
  proof
    fix x
    assume "x \<in> ?L"
    hence "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* map Tm x"
      by (simp add: Lang_def)
    hence "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>l* map Tm x"
      using derivels_iff_derives by auto
    hence "pda.steps cfg_to_pda_pda (Q_loop, x, [Nt (Start G)]) (Q_loop, [], [])"
      using cfg_to_pda_accepts_if_G_derives by simp
    thus "x \<in> ?P"
      unfolding pda.accept_stack_def[OF pda_cfg_to_pda] by (auto simp: cfg_to_pda_pda_def)
  qed
next
  show "?P \<subseteq> ?L"
  proof
    fix x
    assume "x \<in> ?P"
    then obtain q where steps: "pda.steps cfg_to_pda_pda (Q_loop, x, [Nt (Start G)]) (q, [], [])"
      unfolding pda.accept_stack_def[OF pda_cfg_to_pda] by (auto simp: cfg_to_pda_pda_def)
    have "q = Q_loop"
      using sing_st.exhaust by blast
    with steps have "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* map Tm x"
      using G_derives_if_cfg_to_pda_accepts by simp
    thus "x \<in> ?L"
      by (simp add: Lang_def)
  qed
qed

end
end