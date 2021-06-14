theory Std_to_Inca_simulation
  imports Global List_util Std Inca
    "VeriComp.Simulation"
begin

section \<open>Generic definitions\<close>

locale std_inca_simulation =
  Sstd: std
    Fstd_empty Fstd_get Fstd_add Fstd_to_list
    heap_empty heap_get heap_add heap_to_list
    uninitialized is_true is_false
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> +
  Sinca: inca
    Finca_empty Finca_get Finca_add Finca_to_list
    heap_empty heap_get heap_add heap_to_list
    uninitialized is_true is_false
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll>
  for
    \<comment> \<open>Functions environments\<close>
    Fstd_empty and
    Fstd_get :: "'fenv_std \<Rightarrow> 'fun \<Rightarrow> ('label, ('dyn, 'var, 'fun, 'label, 'op) Std.instr) fundef option" and
    Fstd_add and Fstd_to_list and

    Finca_empty and
    Finca_get :: "'fenv_inca \<Rightarrow> 'fun \<Rightarrow> ('label, ('dyn, 'var, 'fun, 'label, 'op, 'opinl) Inca.instr) fundef option" and
    Finca_add and Finca_to_list and
    
    \<comment> \<open>Memory heap\<close>
    heap_empty and
    heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and
    heap_add and heap_to_list and

    \<comment> \<open>Dynamic values\<close>
    uninitialized :: 'dyn and is_true and is_false and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn" and \<AA>\<rr>\<ii>\<tt>\<yy> and
    \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'op"
begin

fun norm_instr where
  "norm_instr (Inca.IPush d) = Std.IPush d" |
  "norm_instr Inca.IPop = Std.IPop" |
  "norm_instr (Inca.IGet n) = Std.IGet n" |
  "norm_instr (Inca.ISet n) = Std.ISet n" |
  "norm_instr (Inca.ILoad x) = Std.ILoad x" |
  "norm_instr (Inca.IStore x) = Std.IStore x" |
  "norm_instr (Inca.IOp op) = Std.IOp op" |
  "norm_instr (Inca.IOpInl opinl) = Std.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl)" |
  "norm_instr (Inca.ICJump l\<^sub>t l\<^sub>f) = Std.ICJump l\<^sub>t l\<^sub>f" |
  "norm_instr (Inca.ICall x) = Std.ICall x" |
  "norm_instr Inca.IReturn = Std.IReturn"

abbreviation norm_eq where
  "norm_eq x y \<equiv> norm_instr y = x"

definition rel_fundefs where
  "rel_fundefs f g = (\<forall>x. rel_option (rel_fundef (=) norm_eq) (f x) (g x))"

lemma rel_fundefsI:
  assumes "\<And>x. rel_option (rel_fundef (=) norm_eq) (F1 x) (F2 x)"
  shows "rel_fundefs F1 F2"
  using assms
  by (simp add: rel_fundefs_def)

lemma rel_fundefsD:
  assumes "rel_fundefs F1 F2"
  shows "rel_option (rel_fundef (=) norm_eq) (F1 x) (F2 x)"
  using assms
  by (simp add: rel_fundefs_def)

lemma rel_fundefs_next_instr:
  assumes rel_F1_F2: "rel_fundefs F1 F2"
  shows "rel_option norm_eq (next_instr F1 f l pc) (next_instr F2 f l pc)"
proof -
  have "rel_option (rel_fundef (=) norm_eq) (F1 f) (F2 f)"
    using rel_F1_F2[unfolded rel_fundefs_def] by simp
  thus ?thesis
  proof (cases rule: option.rel_cases)
    case None
    then show ?thesis by (simp add: next_instr_def)
  next
    case (Some fd1 fd2)
    hence "rel_option (list_all2 norm_eq) (map_of (body fd1) l) (map_of (body fd2) l)"
      by (auto elim!: fundef.rel_cases intro: rel_option_map_of)
    then show ?thesis
      by (cases rule: option.rel_cases;
          simp add: next_instr_def instr_at_def Some list_all2_conv_all_nth)
  qed
qed

lemma rel_fundefs_next_instr1:
  assumes rel_F1_F2: "rel_fundefs F1 F2" and next_instr1: "next_instr F1 f l pc = Some instr1"
  shows "\<exists>instr2. next_instr F2 f l pc = Some instr2 \<and> norm_eq instr1 instr2"
  using rel_fundefs_next_instr[OF rel_F1_F2, of f l pc]
  unfolding next_instr1
  unfolding option_rel_Some1
  by assumption

lemma rel_fundefs_next_instr2:
  assumes rel_F1_F2: "rel_fundefs F1 F2" and next_instr2: "next_instr F2 f l pc = Some instr2"
  shows "\<exists>instr1. next_instr F1 f l pc = Some instr1 \<and> norm_eq instr1 instr2"
  using rel_fundefs_next_instr[OF rel_F1_F2, of f l pc]
  unfolding next_instr2
  unfolding option_rel_Some2
  by assumption

lemma rel_fundefs_empty: "rel_fundefs (\<lambda>_. None) (\<lambda>_. None)"
  by (simp add: rel_fundefs_def)

lemma rel_fundefs_None1:
  assumes "rel_fundefs f g" and "f x = None"
  shows "g x = None"
  by (metis assms rel_fundefs_def rel_option_None1)

lemma rel_fundefs_None2:
  assumes "rel_fundefs f g" and "g x = None"
  shows "f x = None"
  by (metis assms rel_fundefs_def rel_option_None2)

lemma rel_fundefs_Some1:
  assumes "rel_fundefs f g" and "f x = Some y"
  shows "\<exists>z. g x = Some z \<and> rel_fundef (=) norm_eq y z"
proof -
  from assms(1) have "rel_option (rel_fundef (=) norm_eq) (f x) (g x)"
    unfolding rel_fundefs_def by simp
  with assms(2) show ?thesis
    by (simp add: option_rel_Some1)
qed

lemma rel_fundefs_Some2:
  assumes "rel_fundefs f g" and "g x = Some y"
  shows "\<exists>z. f x = Some z \<and> rel_fundef (=) norm_eq z y"
proof -
  from assms(1) have "rel_option (rel_fundef (=) norm_eq) (f x) (g x)"
    unfolding rel_fundefs_def by simp
  with assms(2) show ?thesis
    by (simp add: option_rel_Some2)
qed

lemma rel_fundefs_rel_option:
  assumes "rel_fundefs f g" and "\<And>x y. rel_fundef (=) norm_eq x y \<Longrightarrow> h x y"
  shows "rel_option h (f z) (g z)"
proof -
  have "rel_option (rel_fundef (=) norm_eq) (f z) (g z)"
    using assms(1)[unfolded rel_fundefs_def] by simp
  then show ?thesis
    unfolding rel_option_unfold
    by (auto simp add: assms(2))
qed

lemma rel_fundefs_rewriteI2:
  assumes
    rel_F1_F2: "rel_fundefs (Fstd_get F1) (Finca_get F2)" and
    next_instr1: "next_instr (Fstd_get F1) f l pc = Some instr1"
    "norm_eq instr1 instr2'"
  shows "rel_fundefs (Fstd_get F1)
    (Finca_get (Sinca.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc instr2')))"
  (is "rel_fundefs (Fstd_get ?F1') (Finca_get ?F2')")
proof (rule rel_fundefsI)
  fix x
  show "rel_option (rel_fundef (=) norm_eq) (Fstd_get ?F1' x) (Finca_get ?F2' x)"
  proof (cases "f = x")
    case True
    show ?thesis
      using rel_F1_F2[THEN rel_fundefsD, of x] True next_instr1 assms(3)
      by (cases rule: option.rel_cases)
        (auto intro!: rel_fundef_rewrite_body2' dest!: next_instrD)
  next
    case False
    then show ?thesis
      using rel_F1_F2[THEN rel_fundefsD, of x] by simp
  qed
qed

section \<open>Simulation relation\<close>

inductive match (infix "\<sim>" 55) where
  "wf_fundefs (Fstd_get F1) \<Longrightarrow>
  rel_fundefs (Fstd_get F1) (Finca_get F2) \<Longrightarrow>
  (State F1 H st) \<sim> (State F2 H st)"


section \<open>Backward simulation\<close>

lemma backward_lockstep_simulation:
  assumes "Sinca.step s2 s2'" and "match s1 s2"
  shows "\<exists>s1'. Sstd.step s1 s1' \<and> match s1' s2'"
proof -
  from assms(2) obtain F1 F2 H st where
    s1_def: "s1 = State F1 H st" and
    s2_def: "s2 = State F2 H st" and
    ok_F1: "wf_fundefs (Fstd_get F1)" and
    rel_F1_F2: "rel_fundefs (Fstd_get F1) (Finca_get F2)"
    by (auto elim: match.cases)

  note rel_F1_F2_next_instr = rel_fundefs_next_instr[OF rel_F1_F2]

  from assms(1) show "?thesis"
    unfolding s1_def s2_def
  proof (induction "State F2 H st" s2' rule: Sinca.step.induct)
    case (step_push f l pc d R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l (Suc pc) R (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_push rel_F1_F2_next_instr[of f l pc]
        by (auto intro!: Sstd.step_push simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_pop f l pc R d \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l (Suc pc) R \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_pop rel_F1_F2_next_instr[of f l pc]
        by (auto intro!: Sstd.step_pop simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_get f l pc n R d \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l (Suc pc) R (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_get  rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sstd.step_get simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_set f l pc n R R' d \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l (Suc pc) R' \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_set  rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sstd.step_set simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_load f l pc x y d R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l (Suc pc) R (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_load  rel_F1_F2_next_instr[of f l pc]
        by (auto intro!: Sstd.step_load simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_store f l pc x y d H' R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H' (Frame f l (Suc pc) R \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_store rel_F1_F2_next_instr[of f l pc]
        by (auto intro!: Sstd.step_store simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op f l pc op ar \<Sigma> x R st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op rel_F1_F2_next_instr[of f l pc]
        by (auto intro!: Sstd.step_op simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op_inl f l pc op ar \<Sigma> opinl x F2' R st')
    then obtain instr1 where
      next_instr1: "next_instr (Fstd_get F1) f l pc = Some instr1" and
      norm_eq_instr1_instr2: "norm_eq instr1 (Inca.IOp op)"
      using rel_F1_F2_next_instr[of f l pc] by (simp add: option_rel_Some2)
    then show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof (cases instr1)
      case (IOp op')
      hence "op' = op" using norm_eq_instr1_instr2 by simp
      let ?s1' = "State F1 H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op_inl next_instr1 IOp \<open>op' = op\<close>
        using Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct Sinca.\<II>\<nn>\<ll>_invertible
        by (auto intro: Sstd.step_op)
      moreover have "?MATCH ?s1'"
        using ok_F1 step_op_inl next_instr1 IOp \<open>op' = op\<close>
        using  Sinca.\<II>\<nn>\<ll>_invertible
        by (auto intro!: match.intros intro: rel_fundefs_rewriteI2[OF rel_F1_F2])
      ultimately show "?thesis" by blast
    qed simp_all
  next
    case (step_op_inl_hit f l pc opinl ar \<Sigma> x R st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op_inl_hit rel_F1_F2_next_instr[of f l pc]
        using Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
        by (auto intro: Sstd.step_op simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op_inl_miss f l pc opinl ar \<Sigma> x F' R st')
    then obtain instr1 where
      next_instr1: "next_instr (Fstd_get F1) f l pc = Some instr1" and
      norm_eq_instr1_instr2: "norm_eq instr1 (Inca.IOpInl opinl)"
      using rel_F1_F2_next_instr[of f l pc] by (simp add: option_rel_Some2)
    then show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof (cases instr1)
      case (IOp op)
      hence "op = \<DD>\<ee>\<II>\<nn>\<ll> opinl" using norm_eq_instr1_instr2 by simp
      let ?s1' = "State F1 H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op_inl_miss next_instr1 IOp \<open>op = \<DD>\<ee>\<II>\<nn>\<ll> opinl\<close>
        using Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
        by (auto intro: Sstd.step_op)
      moreover have "?MATCH ?s1'"
        using ok_F1 step_op_inl_miss next_instr1 IOp \<open>op = \<DD>\<ee>\<II>\<nn>\<ll> opinl\<close>
        using  Sinca.\<II>\<nn>\<ll>_invertible
        by (auto intro!: match.intros intro: rel_fundefs_rewriteI2[OF rel_F1_F2])
      ultimately show "?thesis" by blast
    qed simp_all
  next
    case (step_cjump f l pc l\<^sub>t l\<^sub>f d l' R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f l' 0 R \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_cjump rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sstd.step_cjump simp: option_rel_Some2)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_call f l\<^sub>f pc\<^sub>f g gd2 \<Sigma>\<^sub>f frame\<^sub>g R\<^sub>f st')
    then obtain gd1 where
      F1_g: "Fstd_get F1 g = Some gd1" and
      rel_gd1_gd2: "rel_fundef (=) norm_eq gd1 gd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast

    have same_fst_label_gd1_gd2: "fst (hd (body gd1)) = fst (hd (body gd2))"
      using wf_fundefs_imp_wf_fundef[OF ok_F1 F1_g, unfolded wf_fundef_def] rel_gd1_gd2
      by (auto elim!: fundef.rel_cases dest: list_all2_rel_prod_fst_hd)

    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?\<Sigma>g = "take (arity gd1) \<Sigma>\<^sub>f"
      let ?lg = "(fst (hd (body gd1)))"
      let ?s1' = "State F1 H (frame\<^sub>g # Frame f l\<^sub>f pc\<^sub>f R\<^sub>f \<Sigma>\<^sub>f # st')"
      have "?STEP ?s1'"
        using step_call rel_F1_F2_next_instr[of f l\<^sub>f pc\<^sub>f]
        using F1_g same_fst_label_gd1_gd2 rel_gd1_gd2
        by (auto intro!: Sstd.step_call
            simp: option_rel_Some2 allocate_frame_def rel_fundef_arities rel_fundef_locals)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2
        by (auto intro: match.intros)
      ultimately show ?thesis by auto
    qed
  next
    case (step_return g l\<^sub>g pc\<^sub>g gd2 \<Sigma>\<^sub>f \<Sigma>\<^sub>g frame\<^sub>f' f l\<^sub>f pc\<^sub>f R\<^sub>f R\<^sub>g st')
    then obtain gd1 where
      F1_g: "Fstd_get F1 g = Some gd1" and
      rel_gd1_gd2: "rel_fundef (=) norm_eq gd1 gd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    obtain instr1 where
      next_instr1: "next_instr (Fstd_get F1) g l\<^sub>g pc\<^sub>g = Some instr1" and
      norm_eq_instr1_instr2: "norm_eq instr1 Inca.IReturn"
      using step_return rel_F1_F2_next_instr[of g l\<^sub>g pc\<^sub>g] by (simp add: option_rel_Some2)
    then show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof (cases instr1)
      case IReturn
      let ?s1' = "State F1 H (frame\<^sub>f' # st')"
      have "?STEP ?s1'"
        using step_return next_instr1 IReturn
        using F1_g rel_gd1_gd2
        by (auto intro!: Sstd.step_return simp: rel_fundef_arities rel_fundef_return)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show ?thesis by auto
    qed simp_all
  qed
qed

lemma match_final_backward:
  assumes "match s1 s2" and final_s2: "final Finca_get Inca.IReturn s2"
  shows "final Fstd_get Std.IReturn s1"
  using \<open>match s1 s2\<close>
proof (cases s1 s2 rule: match.cases)
  case (1 F1 F2 H st)
  show ?thesis
    using final_s2[unfolded 1]
  proof (cases _ _ "State F2 H st" rule: final.cases)
    case (finalI f l pc R \<Sigma>)
    then show ?thesis
      using 1
      by (auto intro!: final.intros dest: rel_fundefs_next_instr2)
  qed
qed

sublocale std_inca_simulation:
  backward_simulation where
    step1 = Sstd.step and final1 = "final Fstd_get Std.IReturn" and
    step2 = Sinca.step and final2 = "final Finca_get Inca.IReturn" and
    order = "\<lambda>_ _. False" and match = "\<lambda>_. match"
  using match_final_backward backward_lockstep_simulation
    lockstep_to_plus_backward_simulation[of match Sinca.step Sstd.step]
  by unfold_locales auto


section \<open>Forward simulation\<close>

lemma forward_lockstep_simulation:
  assumes "Sstd.step s1 s1'" and "match s1 s2"
  shows "\<exists>s2'. Sinca.step s2 s2' \<and> s1' \<sim> s2'"
proof -
  from assms(2) obtain F1 F2 H st where
    s1_def: "s1 = State F1 H st" and
    s2_def: "s2 = State F2 H st" and
    ok_F1: "wf_fundefs (Fstd_get F1)" and
    rel_F1_F2: "rel_fundefs (Fstd_get F1) (Finca_get F2)"
    by (auto elim: match.cases)

  note rel_F1_F2_next_instr = rel_fundefs_next_instr[OF rel_F1_F2]

  from assms(1) show "?thesis"
    unfolding s1_def s2_def
  proof(induction "State F1 H st" s1' rule: Sstd.step.induct)
    case (step_push f l pc d R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f l (Suc pc) R (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_push rel_F1_F2_next_instr[of f l pc]
        by (auto intro!: Sinca.step_push elim: norm_instr.elims simp: option_rel_Some1)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_pop f l pc R d \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f l (Suc pc) R \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_pop rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sinca.step_pop elim: norm_instr.elims simp: option_rel_Some1)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_get f l pc n R d \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f l (Suc pc) R (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_get rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sinca.step_get elim: norm_instr.elims simp: option_rel_Some1)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_set f l pc n R R' d \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f l (Suc pc) R' \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_set rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sinca.step_set elim: norm_instr.elims simp: option_rel_Some1)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_load f l pc x y d R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f l (Suc pc) R (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_load rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sinca.step_load elim: norm_instr.elims simp: option_rel_Some1)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_store f l pc x y d H' R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H' (Frame f l (Suc pc) R \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_store rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sinca.step_store elim: norm_instr.elims simp: option_rel_Some1)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op f l pc op ar \<Sigma> x R st')
    then obtain instr2 where
      next_instr2: "next_instr (Finca_get F2) f l pc = Some instr2" and
      norm_eq_instr2: "norm_eq (Std.IOp op) instr2"
      using rel_F1_F2_next_instr[of f l pc] by (auto simp: option_rel_Some1)
    thus ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof (cases instr2)
      case (IOp op')
      then have "op' = op" using norm_eq_instr2 by simp
      show ?thesis
      proof (cases "\<II>\<nn>\<ll> op' (take ar \<Sigma>)")
        case None
        let ?s2' = "State F2 H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using None IOp step_op \<open>op' = op\<close> next_instr2
          by (auto intro: Sinca.step_op)
        moreover have "?MATCH ?s2'"
          using ok_F1 rel_F1_F2 by (auto intro: match.intros)
        ultimately show ?thesis by auto
      next
        case (Some opinl)
        let ?F2' = "Sinca.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc (IOpInl opinl))"
        let ?s2' = "State ?F2' H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using Some IOp step_op \<open>op' = op\<close>
          using Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct Sinca.\<II>\<nn>\<ll>_invertible next_instr2
          by (auto intro: Sinca.step_op_inl)
        moreover have "?MATCH ?s2'"
          using ok_F1 step_op IOp \<open>op' = op\<close> Some
          by (auto intro!: match.intros intro: rel_fundefs_rewriteI2[OF rel_F1_F2]
                simp: Sinca.\<II>\<nn>\<ll>_invertible)
        ultimately show ?thesis by auto
      qed
    next
      case (IOpInl opinl)
      hence "op = \<DD>\<ee>\<II>\<nn>\<ll> opinl" using norm_eq_instr2 by simp
      show ?thesis
      proof (cases "\<II>\<ss>\<II>\<nn>\<ll> opinl (take ar \<Sigma>)")
        case True
        let ?s2' = "State F2 H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using step_op IOpInl \<open>op = \<DD>\<ee>\<II>\<nn>\<ll> opinl\<close> True
          using next_instr2 Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
          by (auto intro: Sinca.step_op_inl_hit)
        moreover have "?MATCH ?s2'"
          using ok_F1 rel_F1_F2 by (auto intro: match.intros)
        ultimately show ?thesis by auto
      next
        case False
        let ?F2' = "Sinca.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc (IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl)))"
        let ?s2' = "State ?F2' H (Frame f l (Suc pc) R (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using step_op IOpInl \<open>op = \<DD>\<ee>\<II>\<nn>\<ll> opinl\<close> False
          using next_instr2 Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
          by (auto intro: Sinca.step_op_inl_miss)
        moreover have "?MATCH ?s2'"
          using ok_F1 step_op \<open>op = \<DD>\<ee>\<II>\<nn>\<ll> opinl\<close>
          by (auto intro!: match.intros intro: rel_fundefs_rewriteI2[OF rel_F1_F2])
        ultimately show ?thesis by auto
      qed
    qed simp_all
  next
    case (step_cjump f l pc l\<^sub>t l\<^sub>f d l' R \<Sigma> st')
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f l' 0 R \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_cjump rel_F1_F2_next_instr[of f l pc]
        by (auto intro: Sinca.step_cjump elim: norm_instr.elims simp: option_rel_Some1)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_call f l\<^sub>f pc\<^sub>f g gd1 \<Sigma>\<^sub>f frame\<^sub>g R\<^sub>f st')
    then obtain gd2 where
      F2_g: "Finca_get F2 g = Some gd2" and
      rel_gd1_gd2: "rel_fundef (=) norm_eq gd1 gd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast

    have same_fst_label_gd1_gd2: "fst (hd (body gd1)) = fst (hd (body gd2))"
      using rel_gd1_gd2
      using wf_fundefs_imp_wf_fundef[OF ok_F1 \<open>Fstd_get F1 g = Some gd1\<close>, unfolded wf_fundef_def]
      by (auto elim: fundef.rel_cases dest!: list_all2_rel_prod_fst_hd)

    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?\<Sigma>g = "take (arity gd2) \<Sigma>\<^sub>f"
      let ?s2' = "State F2 H (frame\<^sub>g # Frame f l\<^sub>f pc\<^sub>f R\<^sub>f \<Sigma>\<^sub>f # st')"
      have "?STEP ?s2'"
        using step_call F2_g rel_gd1_gd2 rel_F1_F2_next_instr[of f l\<^sub>f pc\<^sub>f]
        using same_fst_label_gd1_gd2
        by (auto intro!: Sinca.step_call elim: norm_instr.elims
            simp: option_rel_Some1 rel_fundef_arities rel_fundef_locals allocate_frame_def)
      moreover have "?MATCH ?s2'"
        using ok_F1 rel_F1_F2
        by (auto intro: match.intros)
      ultimately show ?thesis by auto
    qed
  next
    case (step_return g l\<^sub>g pc\<^sub>g gd1 \<Sigma>\<^sub>f \<Sigma>\<^sub>g frame\<^sub>f' f l\<^sub>f pc\<^sub>f R\<^sub>f R\<^sub>g st')
    then obtain gd2 where
      F2_g: "Finca_get F2 g = Some gd2" and
      rel_gd1_gd2: "rel_fundef (=) norm_eq gd1 gd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    obtain instr2 where
      next_instr2: "next_instr (Finca_get F2) g l\<^sub>g pc\<^sub>g = Some instr2" and
      norm_eq_instr1_instr2: "norm_eq Std.IReturn instr2"
      using step_return rel_F1_F2_next_instr[of g l\<^sub>g pc\<^sub>g] by (auto simp: option_rel_Some1)
    thus ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof (cases instr2)
      case IReturn
      let ?s1' = "State F2 H (frame\<^sub>f' # st')"
      have "?STEP ?s1'"
        using step_return next_instr2 IReturn
        using F2_g rel_gd1_gd2
        by (auto intro!: Sinca.step_return simp: rel_fundef_arities rel_fundef_return)
      moreover have "?MATCH ?s1'"
        using ok_F1 rel_F1_F2 by (auto intro: match.intros)
      ultimately show ?thesis by auto
    qed simp_all
  qed
qed

lemma match_final_forward:
  assumes "match s1 s2" and final_s1: "final Fstd_get Std.IReturn s1"
  shows "final Finca_get Inca.IReturn s2"
  using \<open>match s1 s2\<close>
proof (cases s1 s2 rule: match.cases)
  case (1 F1 F2 H st)
  show ?thesis
    using final_s1[unfolded 1]
  proof (cases _ _ "State F1 H st" rule: final.cases)
    case (finalI f l pc R \<Sigma>)
    then show ?thesis
      using 1
      by (auto intro: final.intros elim: norm_instr.elims dest: rel_fundefs_next_instr1)
  qed
qed

sublocale std_inca_forward_simulation:
  forward_simulation where
    step1 = Sstd.step and final1 = "final Fstd_get Std.IReturn" and
    step2 = Sinca.step and final2 = "final Finca_get Inca.IReturn" and
    order = "\<lambda>_ _. False" and match = "\<lambda>_. match"
  using match_final_forward forward_lockstep_simulation
    lockstep_to_plus_forward_simulation[of match Sstd.step _ Sinca.step]
  by unfold_locales auto


section \<open>Bisimulation\<close>

sublocale std_inca_bisimulation:
  bisimulation where
    step1 = Sstd.step and final1 = "final Fstd_get Std.IReturn" and
    step2 = Sinca.step and final2 = "final Finca_get Inca.IReturn" and
    order = "\<lambda>_ _. False" and match = "\<lambda>_. match"
  by unfold_locales

end

end