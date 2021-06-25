theory Global
  imports "HOL-Library.Library" Result Env List_util Option_Extra Map_Extra AList_Extra
begin

sledgehammer_params [timeout = 30]
sledgehammer_params [provers = "cvc4 e spass vampire z3 zipperposition"]

declare K_record_comp[simp]

lemma if_then_Some_else_None_eq[simp]:
  "(if a then Some b else None) = Some c \<longleftrightarrow> a \<and> b = c"
  "(if a then Some b else None) = None \<longleftrightarrow> \<not> a"
  by (cases a) simp_all

lemma if_then_else_distributive: "(if a then f b else f c) = f (if a then b else c)"
  by simp


section \<open>Rest\<close>

lemma map_ofD:
  fixes xs k opt
  assumes "map_of xs k = opt"
  shows "opt = None \<or> (\<exists>n < length xs. opt = Some (snd (xs ! n)))"
  using assms
  by (metis in_set_conv_nth map_of_SomeD not_Some_eq snd_conv)

lemma list_all2_assoc_map_rel_get:
  assumes "list_all2 (=) (map fst xs) (map fst ys)" and "list_all2 R (map snd xs) (map snd ys)"
  shows "rel_option R (map_of xs k) (map_of ys k)"
  using assms[unfolded list.rel_map]
proof (induction xs ys rule: list.rel_induct)
  case Nil
  thus ?case by simp
next
  case (Cons x xs y ys)
  thus ?case by (cases "k = fst x") auto
qed

subsection \<open>Function definition\<close>

datatype ('label, 'instr) fundef =
  Fundef (body: "('label \<times> 'instr list) list") (arity: nat) (return: nat) (fundef_locals: nat)

lemma rel_fundef_arities: "rel_fundef r1 r2 gd1 gd2 \<Longrightarrow> arity gd1 = arity gd2"
  by (simp add: fundef.rel_sel)

lemma rel_fundef_return: "rel_fundef R1 R2 gd1 gd2 \<Longrightarrow> return gd1 = return gd2"
  by (simp add: fundef.rel_sel)

lemma rel_fundef_locals: "rel_fundef R1 R2 gd1 gd2 \<Longrightarrow> fundef_locals gd1 = fundef_locals gd2"
  by (simp add: fundef.rel_sel)

lemma rel_fundef_body_length[simp]:
  "rel_fundef r1 r2 fd1 fd2 \<Longrightarrow> length (body fd1) = length (body fd2)"
  by (auto intro: list_all2_lengthD simp add: fundef.rel_sel)

definition funtype where
  "funtype fd \<equiv> (arity fd, return fd)"

lemma rel_fundef_funtype[simp]: "rel_fundef R1 R2 fd1 fd2 \<Longrightarrow> funtype fd1 = funtype fd2"
  by (simp add: fundef.rel_sel funtype_def)

lemma rel_fundef_rel_fst_hd_bodies:
  assumes "rel_fundef R1 R2 fd1 fd2" and "body fd1 \<noteq> [] \<or> body fd2 \<noteq> []"
  shows "R1 (fst (hd (body fd1))) (fst (hd (body fd2)))"
  using assms
  unfolding fundef.rel_sel
  by (auto intro: list_all2_rel_prod_fst_hd[THEN conjunct1])

lemma map_option_comp_conv:
  assumes
    "\<And>x. rel_option R (f x) (g x)"
    "\<And>fd1 fd2. fd1 \<in> ran f \<Longrightarrow> fd2 \<in> ran g \<Longrightarrow> R fd1 fd2 \<Longrightarrow> h fd1 = i fd2"
  shows "map_option h \<circ> f = map_option i \<circ> g"
proof (intro ext)
  fix x
  show "(map_option h \<circ> f) x = (map_option i \<circ> g) x"
    using assms(1)[of x]
    by (cases rule: option.rel_cases) (auto intro: ranI assms(2))
qed

lemma map_option_arity_comp_conv:
  assumes "(\<And>x. rel_option (rel_fundef R S) (f x) (g x))"
  shows "map_option arity \<circ> f = map_option arity \<circ> g"
proof (rule map_option_comp_conv)
  fix x show "rel_option (rel_fundef R S) (f x) (g x)"
    by (rule assms(1))
next
  fix fd1 fd2
  show "rel_fundef R S fd1 fd2 \<Longrightarrow> arity fd1 = arity fd2 "
    by (rule rel_fundef_arities)
qed

definition wf_fundef where
  "wf_fundef fd \<longleftrightarrow> body fd \<noteq> []"

lemma wf_fundef_non_empty_bodyD[dest,intro]: "wf_fundef fd \<Longrightarrow> body fd \<noteq> []"
  by (simp add: wf_fundef_def)

definition wf_fundefs where
  "wf_fundefs F \<longleftrightarrow> (\<forall>f fd. F f = Some fd \<longrightarrow> wf_fundef fd)"

lemma wf_fundefsI:
  assumes "\<And>f fd. F f = Some fd \<Longrightarrow> wf_fundef fd"
  shows "wf_fundefs F"
  using assms by (simp add: wf_fundefs_def)

lemma wf_fundefsI':
  assumes "\<And>f. pred_option wf_fundef (F f)"
  shows "wf_fundefs F"
  using assms unfolding wf_fundefs_def
  by (metis option.pred_inject(2))

lemma wf_fundefs_imp_wf_fundef:
  assumes "wf_fundefs F" and "F f = Some fd"
  shows "wf_fundef fd"
  using assms by (simp add: wf_fundefs_def)

hide_fact wf_fundefs_def

subsection \<open>Program\<close>

datatype ('fenv, 'henv, 'fun) prog =
  Prog (prog_fundefs: 'fenv) (heap: 'henv) (main_fun: 'fun)

definition wf_prog where                
  "wf_prog Get p \<longleftrightarrow> wf_fundefs (Get (prog_fundefs p))"

subsection \<open>Stack frame\<close>

datatype ('fun, 'label, 'operand) frame =
  Frame 'fun 'label (prog_counter: nat) (regs: "'operand list") (operand_stack: "'operand list")

definition instr_at where
  "instr_at fd label pc =
    (case map_of (body fd) label of
      Some instrs \<Rightarrow>
        if pc < length instrs then
          Some (instrs ! pc)
        else
          None
    | None \<Rightarrow> None)"

lemma instr_atD:
  assumes "instr_at fd l pc = Some instr"
  shows "\<exists>instrs. map_of (body fd) l = Some instrs \<and> pc < length instrs \<and> instrs ! pc = instr"
  using assms
  by (cases "map_of (body fd) l") (auto simp: instr_at_def)

lemma rel_fundef_imp_rel_option_instr_at:
  assumes "rel_fundef (=) R fd1 fd2"
  shows "rel_option R (instr_at fd1 l pc) (instr_at fd2 l pc)"
  using assms
proof (cases rule: fundef.rel_cases)
  case (Fundef bblocks1 _ _ bblocks2 )
  then show ?thesis
    by (auto simp: instr_at_def list_all2_lengthD
        intro: list_all2_nthD2 elim!: option.rel_cases dest!: rel_option_map_of[of _ _ _ l])
qed

definition next_instr where
  "next_instr F f label pc \<equiv> do {
    fd \<leftarrow> F f;
    instr_at fd label pc
  }"

lemma next_instr_eq_Some_conv:
  "next_instr F f l pc = Some instr \<longleftrightarrow> (\<exists>fd. F f = Some fd \<and> instr_at fd l pc = Some instr)"
  by (simp add: next_instr_def bind_eq_Some_conv)

lemma next_instrD:
  assumes "next_instr F f l pc = Some instr"
  shows "\<exists>fd. F f = Some fd \<and> instr_at fd l pc = Some instr"
  using assms unfolding next_instr_def
  by (cases "F f"; simp)

lemma next_instr_pc_lt_length_instrsI:
  assumes
    "next_instr F f l pc = Some instr" and
    "F f = Some fd" and
    "map_of (body fd) l = Some instrs"
  shows "pc < length instrs"
  using assms
  by (auto dest!: next_instrD instr_atD)

lemma next_instr_get_map_ofD:
  assumes
    "next_instr F f l pc = Some instr" and
    "F f = Some fd" and
    "map_of (body fd) l = Some instrs"
  shows "pc < length instrs" and "instrs ! pc = instr"
  using assms
  by (auto dest!: next_instrD instr_atD)

lemma next_instr_length_instrs:
  assumes
    "F f = Some fd" and
    "map_of (body fd) label = Some instrs"
  shows "next_instr F f label (length instrs) = None"
  by (simp add: assms next_instr_def instr_at_def)

lemma next_instr_take_Suc_conv:
  assumes "next_instr F f l pc = Some instr" and
    "F f = Some fd" and
    "map_of (body fd) l = Some instrs"
  shows "take (Suc pc) instrs = take pc instrs @ [instr]"
  using assms
  by (auto simp: take_Suc_conv_app_nth dest!: next_instrD instr_atD)


subsection \<open>Dynamic state\<close>

datatype ('fenv, 'henv, 'frame) state =
  State (state_fundefs: 'fenv) (heap: 'henv) (callstack: "'frame list")

definition state_ok where
  "state_ok Get s \<longleftrightarrow> wf_fundefs (Get (state_fundefs s))"

inductive final for F_get Return where
  finalI: "next_instr (F_get F) f l pc = Some Return \<Longrightarrow>
    final F_get Return (State F H [Frame f l pc R \<Sigma>])"

definition allocate_frame where
  "allocate_frame f fd args uninitialized \<equiv>
    Frame f (fst (hd (body fd))) 0 (args @ replicate (fundef_locals fd) uninitialized) []"

inductive load for F_get Uninitialized where
  "F_get F main = Some fd \<Longrightarrow> arity fd = 0 \<Longrightarrow> body fd \<noteq> [] \<Longrightarrow>
  load F_get Uninitialized (Prog F H main) (State F H [allocate_frame main fd [] Uninitialized])"

lemma length_neq_imp_not_list_all2:
  assumes "length xs \<noteq> length ys"
  shows "\<not> list_all2 R xs ys"
proof (rule notI)
  assume "list_all2 R xs ys"
  hence "length xs = length ys"
    by (rule list_all2_lengthD)
  thus False
    using assms by contradiction
qed

lemma list_all2_rel_prod_conv:
  "list_all2 (rel_prod R S) xs ys \<longleftrightarrow>
    list_all2 R (map fst xs) (map fst ys) \<and> list_all2 S (map snd xs) (map snd ys)"
proof (cases "length xs = length ys")
  case True
  then show ?thesis
    by (induction xs ys rule: list_induct2) (auto simp: rel_prod_sel)
next
  case False
  hence neq_length_maps:
      "length (map fst xs) \<noteq> length (map fst ys)"
      "length (map snd xs) \<noteq> length (map snd ys)"
    by simp_all
  show ?thesis
    using length_neq_imp_not_list_all2[OF False]
    using neq_length_maps[THEN length_neq_imp_not_list_all2]
    by simp
qed

definition rewrite_fundef_body ::
  "('label, 'instr) fundef \<Rightarrow> 'label \<Rightarrow> nat \<Rightarrow> 'instr \<Rightarrow> ('label, 'instr) fundef" where
  "rewrite_fundef_body fd l n instr =
    (case fd of Fundef bblocks ar ret locals \<Rightarrow>
      Fundef (AList.map_entry l (\<lambda>instrs. instrs[n := instr]) bblocks) ar ret locals)"

lemma rewrite_fundef_body_cases[case_names invalid_label valid_label]:
  assumes
    "\<And>bs ar ret locals. fd = Fundef bs ar ret locals \<Longrightarrow> map_of bs l = None \<Longrightarrow> P"
    "\<And>bs ar ret locals instrs. fd = Fundef bs ar ret locals \<Longrightarrow> map_of bs l = Some instrs \<Longrightarrow> P"
  shows "P"
  using assms
  by (cases fd; cases "map_of (body fd) l") auto

lemma arity_rewrite_fundef_body[simp]: "arity (rewrite_fundef_body fd l pc instr) = arity fd"
  by (cases fd; simp add: rewrite_fundef_body_def option.case_eq_if)

lemma return_rewrite_fundef_body[simp]: "return (rewrite_fundef_body fd l pc instr) = return fd"
  by (cases fd) (simp add: rewrite_fundef_body_def option.case_eq_if)

lemma funtype_rewrite_fundef_body[simp]: "funtype (rewrite_fundef_body fd l pc instr') = funtype fd"
  by (simp add: funtype_def)

lemma length_body_rewrite_fundef_body[simp]:
  "length (body (rewrite_fundef_body fd l pc instr)) = length (body fd)"
  by (cases fd) (simp add: rewrite_fundef_body_def)

lemma prod_in_set_fst_image_conv: "(x, y) \<in> set xys \<Longrightarrow> x \<in> fst ` set xys"
  by (metis fstI image_eqI)

lemma map_of_body_rewrite_fundef_body_conv_neq[simp]:
  assumes "l \<noteq> l'"
  shows "map_of (body (rewrite_fundef_body fd l pc instr)) l' = map_of (body fd) l'"
  using assms
  by (cases fd) (simp add: rewrite_fundef_body_def map_of_map_entry)

lemma map_of_body_rewrite_fundef_body_conv_eq[simp]:
  "map_of (body (rewrite_fundef_body fd l pc instr)) l =
   map_option (\<lambda>xs. xs[pc := instr]) (map_of (body fd) l)"
  by (cases fd) (simp add: rewrite_fundef_body_def map_of_map_entry map_option_case)

lemma instr_at_rewrite_fundef_body_conv:
  "instr_at (rewrite_fundef_body fd l' pc' instr') l pc =
    map_option (\<lambda>instr. if l = l' \<and> pc = pc' then instr' else instr) (instr_at fd l pc)"
proof (cases fd)
  case (Fundef bblocks ar ret locals)
  then show ?thesis
  proof (cases "instr_at fd l pc")
    case None
    then show ?thesis
      by (cases "map_of bblocks l")
        (auto simp add: Fundef rewrite_fundef_body_def instr_at_def map_of_map_entry)
  next
    case (Some instrs)
    then show ?thesis
      by (cases "map_of bblocks l")
        (auto simp add: Fundef rewrite_fundef_body_def instr_at_def map_of_map_entry)
  qed
qed

lemma fundef_locals_rewrite_fundef_body[simp]:
  "fundef_locals (rewrite_fundef_body fd l pc instr) = fundef_locals fd"
  by (cases fd; simp add: rewrite_fundef_body_def option.case_eq_if)

lemma rel_fundef_rewrite_body1:
  assumes
    rel_fd1_fd2: "rel_fundef (=) R fd1 fd2" and
    instr_at_l_pc: "instr_at fd1 l pc = Some instr" and
    R_iff: "\<And>x. R instr x \<longleftrightarrow> R instr' x"
  shows "rel_fundef (=) R (rewrite_fundef_body fd1 l pc instr') fd2"
  using assms(1)
proof (cases rule: fundef.rel_cases)
  case (Fundef xs ar' ret' locals' ys ar ret locals)
  show ?thesis
    using Fundef(3,3,1,2,4-) instr_at_l_pc
  proof (induction xs ys arbitrary: fd1 fd2 rule: list.rel_induct)
    case Nil
    then show ?case by (simp add: rewrite_fundef_body_def)
  next
    case (Cons x xs y ys)
    then show ?case
      apply (simp add: rewrite_fundef_body_def)
      apply safe
      using assms(3)
       apply (smt (verit, ccfv_SIG) fun_upd_apply fundef.sel(1) instr_atD list_all2_lengthD
          list_all2_nthD2 list_all2_update1_cong map_of.simps(2) option.simps(1) prod.sel(1,2)
          rel_prod_sel)
      by (simp add: instr_at_def)
  qed
qed

lemma rel_fundef_rewrite_body:
  assumes rel_fd1_fd2: "rel_fundef (=) R fd1 fd2" and R_i1_i2: "R i1 i2"
  shows "rel_fundef (=) R (rewrite_fundef_body fd1 l pc i1) (rewrite_fundef_body fd2 l pc i2)"
  using assms(1)
proof (cases rule: fundef.rel_cases)
  case (Fundef bblocks1 ar1 ret1 locals1 bblocks2 ar2 ret2 locals2)
  then show ?thesis
    using R_i1_i2
    by (auto simp: rewrite_fundef_body_def
      intro!: list_all2_update_cong
      intro!: list_all2_rel_prod_map_entry
      dest: rel_option_map_of[of _ _ _ l])
qed

lemma rewrite_fundef_body_triv:
  "instr_at fd l pc = Some instr \<Longrightarrow> rewrite_fundef_body fd l pc instr = fd"
  by (cases fd)
    (auto simp add: rewrite_fundef_body_def map_entry_map_of_Some_conv update_triv dest: instr_atD)

lemma rel_fundef_rewrite_body2:
  assumes
    rel_fd1_fd2: "rel_fundef (=) R fd1 fd2" and
    instr_at_l_pc: "instr_at fd2 l pc = Some instr" and
    R_iff: "\<And>x. R x instr \<longleftrightarrow> R x instr'"
  shows "rel_fundef (=) R fd1 (rewrite_fundef_body fd2 l pc instr')"
  using assms(1)
proof (cases rule: fundef.rel_cases)
  case (Fundef xs ar' ret' locals' ys ar ret locals)
  moreover obtain instrs2 where
    "map_of (body fd2) l = Some instrs2" and "pc < length instrs2" and "instrs2 ! pc = instr"
    using instr_atD[OF instr_at_l_pc] by auto
  moreover then obtain instrs1 instr1 where
    "map_of (body fd1) l = Some instrs1" and "pc < length instrs1" and "instrs1 ! pc = instr1"
    using rel_fundef_imp_rel_option_instr_at[OF rel_fd1_fd2, of l pc]
    apply (auto simp add: instr_at_def option_rel_Some2)
    by (metis instr_atD instr_at_def)
  moreover have "list_all2 R instrs1 instrs2"
    using Fundef \<open>map_of (body fd2) l = Some instrs2\<close> \<open>map_of (body fd1) l = Some instrs1\<close>
    by (auto dest: rel_option_map_of[of _ _ _ l])
  moreover hence "R (instrs1 ! pc) (instrs2 ! pc)"
    using \<open>pc < length instrs1\<close>
    by (auto intro: list_all2_nthD)
  ultimately show ?thesis
    by (auto simp: rewrite_fundef_body_def R_iff
          intro!: list_all2_rel_prod_map_entry2
          intro: list_all2_update2_cong)
qed

lemma rel_fundef_rewrite_body2':
  assumes
    rel_fd1_fd2: "rel_fundef (=) R fd1 fd2" and
    instr_at1: "instr_at fd1 l pc = Some instr1" and
    R_instr1_instr2: "R instr1 instr2'"
  shows "rel_fundef (=) R fd1 (rewrite_fundef_body fd2 l pc instr2')"
  using assms(1)
proof (cases rule: fundef.rel_cases)
  case (Fundef bblocks1 ar1 ret1 locals1 bblocks2 ar2 ret2 locals2)
  moreover obtain instrs1 where
    "map_of bblocks1 l = Some instrs1" and "pc < length instrs1" and "instrs1 ! pc = instr1"
    using Fundef instr_at1[THEN instr_atD] by auto

  moreover then obtain instrs2 instr2 where
    "map_of (body fd2) l = Some instrs2" and "pc < length instrs2" and "instrs2 ! pc = instr2"
    using Fundef rel_fd1_fd2
    apply (auto simp: option_rel_Some1 dest!: rel_option_map_of[where l = l])
    by (metis list_all2_lengthD)
  ultimately show ?thesis
    using R_instr1_instr2
    by (auto simp: rewrite_fundef_body_def
          intro!: list_all2_update2_cong list_all2_rel_prod_map_entry2
          dest: rel_option_map_of[of _ _ _ l])
qed

thm rel_fundef_rewrite_body

lemma if_eq_const_conv: "(if x then y else z) = w \<longleftrightarrow> x \<and> y = w \<or> \<not> x \<and> z = w"
  by simp

lemma const_eq_if_conv: "w = (if x then y else z) \<longleftrightarrow> x \<and> w = y \<or> \<not> x \<and> w = z"
  by auto

end
