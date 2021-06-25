theory Std_to_Inca_compiler
  imports Std_to_Inca_simulation
    "VeriComp.Compiler"
begin


subsection \<open>Compilation of function definitions\<close>

fun compile_instr where
  "compile_instr (Std.IPush d) = Inca.IPush d" |
  "compile_instr Std.IPop = Inca.IPop" |
  "compile_instr (Std.IGet n) = Inca.IGet n" |
  "compile_instr (Std.ISet n) = Inca.ISet n" |
  "compile_instr (Std.ILoad x) = Inca.ILoad x" |
  "compile_instr (Std.IStore x) = Inca.IStore x" |
  "compile_instr (Std.IOp op) = Inca.IOp op" |
  "compile_instr (Std.ICJump l\<^sub>t l\<^sub>f) = Inca.ICJump l\<^sub>t l\<^sub>f" |
  "compile_instr (Std.ICall f) = Inca.ICall f" |
  "compile_instr Std.IReturn = Inca.IReturn"

fun compile_fundef where
  "compile_fundef (Fundef [] _ _ _) = None" |
  "compile_fundef (Fundef bblocks ar ret locals) =
    Some (Fundef (map_ran (\<lambda>_. map compile_instr) bblocks) ar ret locals)"

context std_inca_simulation begin

lemma lambda_eq_eq[simp]: "(\<lambda>x y. y = x) = (=)"
  apply (intro ext)
  by blast

lemma norm_compile_instr:
  "norm_instr (compile_instr instr) = instr"
by (cases instr) auto

lemma rel_compile_fundef:
  assumes "compile_fundef fd1 = Some fd2"
  shows "rel_fundef (=) norm_eq fd1 fd2"
  using assms
proof (cases rule: compile_fundef.elims)
  case (2 x xs ar)
  then show ?thesis
    by (auto intro: list.rel_refl
        simp: const_eq_if_conv list.rel_map norm_compile_instr map_ran_def case_prod_beta
          rel_prod_sel)
qed simp_all

lemma rel_fundef_imp_fundef_ok_iff:
  assumes "rel_fundef (=) norm_eq fd1 fd2"
  shows "wf_fundef fd1 \<longleftrightarrow> wf_fundef fd2"
  unfolding wf_fundef_def
  using assms
  by (auto simp: list_all2_rel_prod_conv list.rel_eq elim: fundef.rel_cases)

lemma rel_fundefs_imp_wf_fundefs_iff:
  assumes rel_f_g: "rel_fundefs f g"
  shows "wf_fundefs f \<longleftrightarrow> wf_fundefs g"
proof (rule iffI)
  assume "wf_fundefs f" show "wf_fundefs g"
  proof (rule wf_fundefsI)
    fix x fd
    assume "g x = Some fd" thus "wf_fundef fd"
      using \<open>wf_fundefs f\<close>
      by (meson rel_f_g rel_fundef_imp_fundef_ok_iff rel_fundefs_Some2 wf_fundefs_imp_wf_fundef)
  qed
next
  show "wf_fundefs g \<Longrightarrow> wf_fundefs f"
    using rel_f_g
    by (meson rel_fundef_imp_fundef_ok_iff rel_fundefs_Some1 wf_fundefs_imp_wf_fundef wf_fundefsI)
qed

lemma compile_fundef_wf:
  assumes "compile_fundef fd = Some fd'"
  shows "wf_fundef fd'"
  using assms
proof (cases rule: compile_fundef.elims)
  case (2 x xs ar)
  then show ?thesis
    by (simp add: const_eq_if_conv wf_fundef_def map_ran_Cons_sel)
qed simp_all


subsection \<open>Compilation of function environments\<close>

definition compile_env where
  "compile_env e \<equiv>
    Some Sinca.Fenv.from_list \<diamondop> ap_map_list (ap_map_prod Some compile_fundef) (Fstd_to_list e)"

lemma compile_env_imp_rel_option:
  assumes "compile_env F1 = Some F2"
  shows "rel_option (\<lambda>fd1 fd2. compile_fundef fd1 = Some fd2) (Fstd_get F1 f) (Finca_get F2 f)"
proof -
  from assms(1) obtain xs where
    ap_map_list_F1: "ap_map_list (ap_map_prod Some compile_fundef) (Fstd_to_list F1) = Some xs" and
    F2_def: "F2 = Sinca.Fenv.from_list xs"
    by (auto simp add: compile_env_def ap_option_eq_Some_conv)

  show ?thesis
    unfolding F2_def Sinca.Fenv.from_list_correct[symmetric]
    unfolding Sinca.Fenv.from_list_correct
    unfolding Sstd.Fenv.to_list_correct[symmetric]
    using ap_map_list_F1
    by (simp add: ap_map_list_ap_map_prod_imp_rel_option_map_of)
qed

lemma Finca_get_compile:
  assumes compile_F1: "compile_env F1 = Some F2"
  shows "Finca_get F2 f = Fstd_get F1 f \<bind> compile_fundef"
  using compile_env_imp_rel_option[OF assms(1), of f]
  by (auto elim!: option.rel_cases)

lemma compile_env_rel_fundefs:
  assumes "compile_env F1 = Some F2"
  shows "rel_fundefs (Fstd_get F1) (Finca_get F2)"
  unfolding rel_fundefs_def
proof (rule allI)
  fix f
  show "rel_option (rel_fundef (=) norm_eq) (Fstd_get F1 f) (Finca_get F2 f)"
    using compile_env_imp_rel_option[OF assms(1), of f]
    by (auto elim!: option.rel_cases intro: rel_compile_fundef)
qed

lemma compile_env_imp_wf_fundefs2:
  assumes "compile_env F1 = Some F2"
  shows "wf_fundefs (Finca_get F2)"
  unfolding Finca_get_compile[OF assms(1)]
  by (auto simp: bind_eq_Some_conv intro!: wf_fundefsI intro: compile_fundef_wf)


subsection \<open>Compilation of programs\<close>

fun compile where
  "compile (Prog F1 H f) = Some Prog \<diamondop> compile_env F1 \<diamondop> Some H \<diamondop> Some f"

theorem compile_load:
  assumes
    compile_p1: "compile p1 = Some p2" and
    load: "Sinca.load p2 s2"
  shows "\<exists>s1. Sstd.load p1 s1 \<and> match s1 s2"
proof (cases p1)
  case (Prog F1 H main)
  with assms(1) obtain F2 where
    compile_F1: "compile_env F1 = Some F2" and
    p2_def: "p2 = Prog F2 H main"
    by (auto simp: ap_option_eq_Some_conv)

  show ?thesis
    using assms(2) unfolding p2_def Sinca.load_def
  proof (cases _ _ _ s2 rule: load.cases)
    case (1 fd2)
    from 1 obtain fd1 where
      F1_main: "Fstd_get F1 main = Some fd1" and compile_fd1: "compile_fundef fd1 = Some fd2"
      using Finca_get_compile[OF compile_F1] by (auto simp: bind_eq_Some_conv)

    note rel_fd1_fd2 = rel_compile_fundef[OF compile_fd1]
    hence first_label_fd1_fd2: "fst (hd (body fd1)) = fst (hd (body fd2))"
      using 1
      by (auto elim!: fundef.rel_cases dest: list_all2_rel_prod_fst_hd)

    have bodies_fd1_fd2: "body fd1 = [] \<longleftrightarrow> body fd2 = []"
      using rel_fundef_body_length[OF rel_fd1_fd2]
      by auto

    let ?s1 = "State F1 H [allocate_frame main fd1 [] uninitialized]"

    show ?thesis
    proof (intro exI conjI)
      show "Sstd.load p1 ?s1"
        unfolding Prog
        using 1 F1_main rel_fd1_fd2 bodies_fd1_fd2
        by (auto simp: rel_fundef_arities Sstd.load_def intro!: load.intros)
    next
      note rel_F1_F2 = compile_env_rel_fundefs[OF compile_F1]
      moreover have "wf_fundefs (Fstd_get F1)"
      proof (rule wf_fundefsI)
        fix f fd1
        assume "Fstd_get F1 f = Some fd1"
        then show "wf_fundef fd1"
          by (metis (mono_tags, lifting) Finca_get_compile bind.bind_lunit compile_F1
              rel_F1_F2 compile_fundef_wf rel_fundef_imp_fundef_ok_iff
              rel_fundefs_Some1)
      qed
      ultimately show "match ?s1 s2"
        unfolding 1
        using rel_fd1_fd2
        by (auto simp: allocate_frame_def first_label_fd1_fd2 rel_fundef_locals
            intro: match.intros)
    qed
  qed
qed

sublocale std_to_inca_compiler:
  compiler where
    step1 = Sstd.step and final1 = "final Fstd_get Std.IReturn" and load1 = "Sstd.load" and
    step2 = Sinca.step and final2 = "final Finca_get Inca.IReturn" and load2 = "Sinca.load" and
    order = "\<lambda>_ _. False" and match = "\<lambda>_. match" and compile = compile
  using compile_load
  by unfold_locales  auto


subsection \<open>Completeness of compilation\<close>

lemma compile_fundef_complete:
  assumes "wf_fundef fd1"
  shows "\<exists>fd2. compile_fundef fd1 = Some fd2"
proof (cases fd1)
  case (Fundef bbs ar)
  then obtain bb bbs' where bbs_def: "bbs = bb # bbs'"
    using assms(1) by (cases bbs; auto)
  show ?thesis
    using assms
    unfolding Fundef bbs_def
    by simp
qed

lemma compile_env_complete:
  assumes wf_F1: "wf_fundefs (Fstd_get F1)"
  shows "\<exists>F2. compile_env F1 = Some F2"
proof -
  show ?thesis
    using wf_F1
    by (auto simp: compile_env_def ap_option_eq_Some_conv ap_map_prod_eq_Some_conv
        intro!: ex_ap_map_list_eq_SomeI Sstd.Fenv.to_list_list_allI compile_fundef_complete
        intro: wf_fundefs_imp_wf_fundef)
qed

theorem compile_complete:
  assumes wf_p1: "wf_prog Fstd_get p1"
  shows "\<exists>p2. compile p1 = Some p2"
proof (cases p1)
  case (Prog x1 x2 x3)
  then show ?thesis
    using wf_p1 unfolding wf_prog_def
    by (auto dest: compile_env_complete)
qed

theorem compile_load_forward:
  assumes
    wf_p1: "wf_prog Fstd_get p1" and load_p1: "Sstd.load p1 s1"
  shows "\<exists>p2 s2. compile p1 = Some p2 \<and> Sinca.load p2 s2 \<and> match s1 s2"
proof -
  from load_p1 obtain F1 H main fd1 where
    p1_def: "p1 = Prog F1 H main" and
    s1_def: "s1 = Global.state.State F1 H [allocate_frame main fd1 [] uninitialized]" and
    F1_main: "Fstd_get F1 main = Some fd1" and
    arity_fd1: "arity fd1 = 0"
    by (auto simp: Sstd.load_def elim: load.cases)

  obtain F2 where compile_F1: "compile_env F1 = Some F2"
    using wf_p1[unfolded p1_def wf_prog_def, simplified]
    using compile_env_complete[of F1]
    by auto

  obtain fd2 where
    F2_main: "Finca_get F2 main = Some fd2" and compile_fd1: "compile_fundef fd1 = Some fd2"
    using compile_env_imp_rel_option[OF compile_F1, of main]
    unfolding F1_main option_rel_Some1
    by auto

  hence rel_fd1_fd2: "rel_fundef (=) norm_eq fd1 fd2"
    using rel_compile_fundef by auto

  note wf_fd2 = compile_fundef_wf[OF compile_fd1]

  let ?s2 = "State F2 H [allocate_frame main fd2 [] uninitialized]"

  show ?thesis
  proof (intro exI conjI)
    show "compile p1 = Some (Prog F2 H main)"
      by (simp add: p1_def compile_F1)
  next
    show "Sinca.load (Prog F2 H main) ?s2"
      using F2_main arity_fd1
      using rel_fundef_arities[OF rel_fd1_fd2]
      using compile_fundef_wf[OF compile_fd1]
      by (auto simp: wf_fundef_def Sinca.load_def intro: load.intros)
  next
    have "fst (hd (body fd1)) = fst (hd (body fd2))"
      using rel_fd1_fd2 wf_fd2
      by (auto simp add: fundef.rel_sel wf_fundef_def list_all2_rel_prod_fst_hd)
    moreover have "wf_fundefs (Fstd_get F1)"
      using compile_env_imp_wf_fundefs2[OF compile_F1]
      using compile_env_rel_fundefs[OF compile_F1, THEN rel_fundefs_imp_wf_fundefs_iff]
      by simp
    ultimately show "match s1 ?s2"
      unfolding s1_def
      using rel_fd1_fd2 compile_env_rel_fundefs[OF compile_F1]
      by (auto simp: allocate_frame_def rel_fundef_locals intro!: match.intros)
  qed
qed

end

end