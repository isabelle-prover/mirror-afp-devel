theory Ubx_Verification
  imports "HOL-Library.Sublist" Ubx Map_Extra 
begin

lemma f_g_eq_f_imp_f_comp_g_eq_f[simp]: "(\<And>x. f (g x) = f x) \<Longrightarrow> (f \<circ> g) = f"
  by (simp add: comp_def)

context ubx begin

inductive sp_instr for F ret where
  Push:
    "sp_instr F ret (IPush d) \<Sigma> (None # \<Sigma>)" |
  PushUbx1:
    "sp_instr F ret (IPushUbx1 u) \<Sigma> (Some Ubx1 # \<Sigma>)" |
  PushUbx2:
    "sp_instr F ret (IPushUbx2 u) \<Sigma> (Some Ubx2 # \<Sigma>)" |
  Pop:
    "sp_instr F ret IPop (\<tau> # \<Sigma>) \<Sigma>" |
  Get:
    "sp_instr F ret (IGet n) \<Sigma> (None # \<Sigma>)" |
  GetUbx:
    "sp_instr F ret (IGetUbx \<tau> n) \<Sigma> (Some \<tau> # \<Sigma>)" |
  Set:
    "sp_instr F ret (ISet n) (None # \<Sigma>) \<Sigma>" |
  SetUbx:
    "sp_instr F ret (ISetUbx \<tau> n) (Some \<tau> # \<Sigma>) \<Sigma>" |
  Load:
    "sp_instr F ret (ILoad x) (None # \<Sigma>) (None # \<Sigma>)" |
  LoadUbx:
    "sp_instr F ret (ILoadUbx \<tau> x) (None # \<Sigma>) (Some \<tau> # \<Sigma>)" |
  Store:
    "sp_instr F ret (IStore x) (None # None # \<Sigma>) \<Sigma>" |
  StoreUbx:
    "sp_instr F ret (IStoreUbx \<tau> x) (None # Some \<tau> # \<Sigma>) \<Sigma>" |
  Op:
    "\<Sigma>i = (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> op) None @ \<Sigma>) \<Longrightarrow>
    sp_instr F ret (IOp op) \<Sigma>i (None # \<Sigma>)" |
  OpInl:
    "\<Sigma>i = (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) None @ \<Sigma>) \<Longrightarrow>
    sp_instr F ret (IOpInl opinl) \<Sigma>i (None # \<Sigma>)" |
  OpUbx:
    "\<Sigma>i = fst (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx) @ \<Sigma> \<Longrightarrow> result = snd (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx) \<Longrightarrow>
    sp_instr F ret (IOpUbx opubx) \<Sigma>i (result # \<Sigma>)" |
  CJump:
    "sp_instr F ret (ICJump l\<^sub>t l\<^sub>f) [None] []" |
  Call:
    "F f = Some (ar, r) \<Longrightarrow> \<Sigma>i = replicate ar None @ \<Sigma> \<Longrightarrow> \<Sigma>o = replicate r None @ \<Sigma> \<Longrightarrow>
    sp_instr F ret (ICall f) \<Sigma>i \<Sigma>o" |
  Return: "\<Sigma>i = replicate ret None \<Longrightarrow>
    sp_instr F ret IReturn \<Sigma>i []"

inductive sp_instrs for F ret where
  Nil:
    "sp_instrs F ret [] \<Sigma> \<Sigma>" |
  Cons:
    "sp_instr F ret instr \<Sigma>i \<Sigma> \<Longrightarrow> sp_instrs F ret instrs \<Sigma> \<Sigma>o \<Longrightarrow>
    sp_instrs F ret (instr # instrs) \<Sigma>i \<Sigma>o"

lemmas sp_instrs_ConsE = sp_instrs.cases[of _ _ "x # xs" for x xs, simplified]

lemma sp_instrs_ConsD:
  assumes "sp_instrs F ret (instr # instrs) \<Sigma>i \<Sigma>o"
  shows "\<exists>\<Sigma>. sp_instr F ret instr \<Sigma>i \<Sigma> \<and> sp_instrs F ret instrs \<Sigma> \<Sigma>o"
  using assms
  by (auto elim: sp_instrs_ConsE)

lemma sp_instr_deterministic:
  assumes
    "sp_instr F ret instr \<Sigma>i \<Sigma>o" and 
    "sp_instr F ret instr \<Sigma>i \<Sigma>o'"
  shows "\<Sigma>o = \<Sigma>o'"
  using assms by (auto elim!: sp_instr.cases)

lemma sp_instr_right_unique: "right_unique (\<lambda>(instr, \<Sigma>i) \<Sigma>o. sp_instr F ret instr \<Sigma>i \<Sigma>o)"
  by (auto intro!: right_uniqueI intro: sp_instr_deterministic)

lemma sp_instrs_deterministic:
  assumes
    "sp_instrs F ret instr \<Sigma>i \<Sigma>o" and 
    "sp_instrs F ret instr \<Sigma>i \<Sigma>o'"
  shows "\<Sigma>o = \<Sigma>o'"
  using assms
proof (induction instr \<Sigma>i \<Sigma>o arbitrary: \<Sigma>o' rule: sp_instrs.induct)
  case (Nil \<Sigma>)
  then show ?case
    by (auto elim: sp_instrs.cases)
next
  case (Cons instr \<Sigma>i \<Sigma> instrs \<Sigma>o)
  from Cons.prems obtain \<Sigma>' where "sp_instr F ret instr \<Sigma>i \<Sigma>'" and "sp_instrs F ret instrs \<Sigma>' \<Sigma>o'"
    by (auto elim: sp_instrs.cases)
  hence "\<Sigma>' = \<Sigma>" and "sp_instrs F ret instrs \<Sigma>' \<Sigma>o'"
    using Cons.hyps
    by (auto intro: sp_instr_deterministic)
  then show ?case
    by (auto intro: Cons.IH)
qed

fun fun_call_in_range where
  "fun_call_in_range F (ICall f) \<longleftrightarrow> f \<in> dom F" |
  "fun_call_in_range F instr \<longleftrightarrow> True"

lemma fun_call_in_range_generalize_instr[simp]:
  "fun_call_in_range F (generalize_instr instr) \<longleftrightarrow> fun_call_in_range F instr"
  by (induction instr; simp)

lemma sp_instr_complete:
  assumes "fun_call_in_range F instr"
  shows "\<exists>\<Sigma>i \<Sigma>o. sp_instr F ret instr \<Sigma>i \<Sigma>o"
  using assms
  by (cases instr; auto intro: sp_instr.intros)

lemma sp_instr_Op2I:
  assumes "\<AA>\<rr>\<ii>\<tt>\<yy> op = 2"
  shows "sp_instr F ret (IOp op) (None # None # \<Sigma>) (None # \<Sigma>)"
  using sp_instr.Op[of _ op]
  unfolding assms numeral_2_eq_2
  by auto

lemma
  assumes
    F_def: "F = Map.empty" and
    arity_op: "\<AA>\<rr>\<ii>\<tt>\<yy> op = 2"
  shows "sp_instrs F 1 [IPush x, IPush y, IOp op, IReturn] [] []"
  by (auto simp: arity_op numeral_2_eq_2
        intro!: sp_instrs.intros
        intro: sp_instr.intros sp_instr_Op2I)

lemma sp_intrs_NilD[dest]: "sp_instrs F ret [] \<Sigma>i \<Sigma>o \<Longrightarrow> \<Sigma>i = \<Sigma>o"
  by (auto elim: sp_instrs.cases)

lemma sp_instrs_list_update:
  assumes
    "sp_instrs F ret instrs \<Sigma>i \<Sigma>o" and
    "sp_instr F ret (instrs!n) = sp_instr F ret instr"
  shows "sp_instrs F ret (instrs[n := instr]) \<Sigma>i \<Sigma>o"
  using assms
proof (induction instrs \<Sigma>i \<Sigma>o arbitrary: n rule: sp_instrs.induct)
  case (Nil \<Sigma>)
  thus ?case by (auto intro: sp_instrs.Nil)
next
  case (Cons instr \<Sigma>i \<Sigma> instrs \<Sigma>o)
  show ?case
  proof (cases n)
    case 0
    thus ?thesis
      using Cons.hyps Cons.prems[unfolded 0, simplified]
      by (auto intro: sp_instrs.Cons)
  next
    case (Suc n')
    then show ?thesis
      using Cons.hyps Cons.prems[unfolded Suc, simplified, THEN Cons.IH]
      by (auto intro: sp_instrs.Cons)
  qed
qed

lemma sp_instrs_appendD:
  assumes "sp_instrs F ret (instrs1 @ instrs2) \<Sigma>i \<Sigma>o"
  shows "\<exists>\<Sigma>. sp_instrs F ret instrs1 \<Sigma>i \<Sigma> \<and> sp_instrs F ret instrs2 \<Sigma> \<Sigma>o"
  using assms
proof (induction instrs1 arbitrary: \<Sigma>i)
  case Nil
  thus ?case by (auto intro: sp_instrs.Nil)
next
  case (Cons instr instrs1)
  then obtain \<Sigma> where "sp_instr F ret instr \<Sigma>i \<Sigma>" and "sp_instrs F ret (instrs1 @ instrs2) \<Sigma> \<Sigma>o"
    by (auto elim: sp_instrs.cases)
  thus ?case
    by (auto intro: sp_instrs.Cons dest: Cons.IH)
qed

lemma sp_instrs_appendD':
  assumes "sp_instrs F ret (instrs1 @ instrs2) \<Sigma>i \<Sigma>o" and "sp_instrs F ret instrs1 \<Sigma>i \<Sigma>"
  shows "sp_instrs F ret instrs2 \<Sigma> \<Sigma>o"
proof -
  obtain \<Sigma>' where
    sp_instrs1: "sp_instrs F ret instrs1 \<Sigma>i \<Sigma>'" and
    sp_instrs2: "sp_instrs F ret instrs2 \<Sigma>' \<Sigma>o"
    using sp_instrs_appendD[OF assms(1)]
    by auto
  have "\<Sigma>' = \<Sigma>"
    using sp_instrs_deterministic[OF assms(2) sp_instrs1] by simp
  thus ?thesis
    using sp_instrs2 by simp
qed

lemma sp_instrs_appendI[intro]:
  assumes "sp_instrs F ret instrs1 \<Sigma>i \<Sigma>" and "sp_instrs F ret instrs2 \<Sigma> \<Sigma>o"
  shows "sp_instrs F ret (instrs1 @ instrs2) \<Sigma>i \<Sigma>o"
  using assms
  by (induction instrs1 \<Sigma>i \<Sigma> rule: sp_instrs.induct) (auto intro: sp_instrs.Cons)

lemma sp_instrs_singleton_conv[simp]:
  "sp_instrs F ret [instr] \<Sigma>i \<Sigma>o \<longleftrightarrow> sp_instr F ret instr \<Sigma>i \<Sigma>o"
  by (auto intro: sp_instrs.intros elim: sp_instrs.cases)

lemma sp_instrs_singletonI:
  assumes "sp_instr F ret instr \<Sigma>i \<Sigma>o"
  shows "sp_instrs F ret [instr] \<Sigma>i \<Sigma>o"
  using assms by (auto intro: sp_instrs.intros)

fun local_var_in_range where
  "local_var_in_range n (IGet k) \<longleftrightarrow> k < n" |
  "local_var_in_range n (IGetUbx \<tau> k) \<longleftrightarrow> k < n" |
  "local_var_in_range n (ISet k) \<longleftrightarrow> k < n" |
  "local_var_in_range n (ISetUbx \<tau> k) \<longleftrightarrow> k < n" |
  "local_var_in_range _ _ \<longleftrightarrow> True"

lemma local_var_in_range_generalize_instr[simp]:
  "local_var_in_range n (generalize_instr instr) \<longleftrightarrow> local_var_in_range n instr"
  by (cases instr; simp)

lemma local_var_in_range_comp_generalize_instr[simp]:
  "local_var_in_range n \<circ> generalize_instr = local_var_in_range n"
  using local_var_in_range_generalize_instr
  by auto

fun jump_in_range where
  "jump_in_range L (ICJump l\<^sub>t l\<^sub>f) \<longleftrightarrow> {l\<^sub>t, l\<^sub>f} \<subseteq> L" |
  "jump_in_range L _ \<longleftrightarrow> True"

inductive wf_basic_block for F L ret n where
  "instrs \<noteq> [] \<Longrightarrow>
    list_all (local_var_in_range n) instrs \<Longrightarrow>
    list_all (fun_call_in_range F) instrs \<Longrightarrow>
    list_all (jump_in_range L) instrs \<Longrightarrow>
    list_all (\<lambda>i. \<not> is_jump i \<and> \<not> is_return i) (butlast instrs) \<Longrightarrow>
    sp_instrs F ret instrs [] [] \<Longrightarrow>
    wf_basic_block F L ret n (label, instrs)"

lemmas wf_basic_blockI = wf_basic_block.simps[THEN iffD2]
lemmas wf_basic_blockD = wf_basic_block.simps[THEN iffD1]

definition wf_fundef where
  "wf_fundef F fd \<longleftrightarrow>
    body fd \<noteq> [] \<and>
    list_all
      (wf_basic_block F (fst ` set (body fd)) (return fd) (arity fd + fundef_locals fd))
      (body fd)"

lemmas wf_fundefI = wf_fundef_def[THEN iffD2, OF conjI]
lemmas wf_fundefD = wf_fundef_def[THEN iffD1]
lemmas wf_fundef_body_neq_NilD = wf_fundefD[THEN conjunct1]
lemmas wf_fundef_all_wf_basic_blockD = wf_fundefD[THEN conjunct2]

definition wf_fundefs where
  "wf_fundefs F \<longleftrightarrow> (\<forall>f. pred_option (wf_fundef (map_option funtype \<circ> F)) (F f))"

lemmas wf_fundefsI = wf_fundefs_def[THEN iffD2]
lemmas wf_fundefsD = wf_fundefs_def[THEN iffD1]

lemma wf_fundefs_getD:
  shows "wf_fundefs F \<Longrightarrow> F f = Some fd \<Longrightarrow> wf_fundef (map_option funtype \<circ> F) fd"
  by (auto dest!: wf_fundefsD[THEN spec, of _ f])

definition wf_prog where
  "wf_prog p \<longleftrightarrow> wf_fundefs (F_get (prog_fundefs p))"

definition wf_state where
  "wf_state s \<longleftrightarrow> wf_fundefs (F_get (state_fundefs s))"

lemmas wf_stateI = wf_state_def[THEN iffD2]
lemmas wf_stateD = wf_state_def[THEN iffD1]

lemma sp_instr_generalize0:
  assumes "sp_instr F ret instr \<Sigma>i \<Sigma>o" and
    "\<Sigma>i' = map (\<lambda>_. None) \<Sigma>i" and "\<Sigma>o' = map (\<lambda>_. None) \<Sigma>o"
  shows "sp_instr F ret (generalize_instr instr) \<Sigma>i' \<Sigma>o'"
  using assms
proof (induction instr \<Sigma>i \<Sigma>o rule: sp_instr.induct)
  case (OpUbx \<Sigma>i opubx \<Sigma> result)
  then show ?case
    apply simp
    unfolding map_replicate_const
    unfolding \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>[symmetric]
    by (auto intro: sp_instr.OpInl)
qed (auto simp: intro: sp_instr.intros)

lemma sp_instrs_generalize0:
  assumes "sp_instrs F ret instrs \<Sigma>i \<Sigma>o" and
    "\<Sigma>i' = map (\<lambda>_. None) \<Sigma>i" and "\<Sigma>o' = map (\<lambda>_. None) \<Sigma>o"
  shows "sp_instrs F ret (map generalize_instr instrs) \<Sigma>i' \<Sigma>o'"
  using assms
proof (induction instrs \<Sigma>i \<Sigma>o arbitrary: \<Sigma>i' \<Sigma>o' rule: sp_instrs.induct)
  case (Nil \<Sigma>)
  then show ?case
    by (auto intro: sp_instrs.Nil)
next
  case (Cons instr \<Sigma>i \<Sigma> instrs \<Sigma>o)
  then show ?case
    by (auto intro: sp_instrs.Cons sp_instr_generalize0)
qed

lemmas sp_instr_generalize = sp_instr_generalize0[OF _ refl refl]
lemmas sp_instr_generalize_Nil_Nil = sp_instr_generalize[of _ _ _ "[]" "[]", simplified]
lemmas sp_instrs_generalize = sp_instrs_generalize0[OF _ refl refl]
lemmas sp_instrs_generalize_Nil_Nil = sp_instrs_generalize[of _ _ _ "[]" "[]", simplified]

lemma jump_in_range_generalize_instr[simp]:
  "jump_in_range L (generalize_instr instr) \<longleftrightarrow> jump_in_range L instr"
  by (cases instr) simp_all

lemma wf_basic_block_map_generalize_instr:
  assumes "wf_basic_block F L ret n (label, instrs)"
  shows "wf_basic_block F L ret n (label, map generalize_instr instrs)"
  using assms
  by (auto simp add: wf_basic_block.simps list.pred_map map_butlast[symmetric]
      intro: sp_instrs_generalize_Nil_Nil)

lemma list_all_wf_basic_block_generalize_fundef:
  assumes "list_all (wf_basic_block F L ret n) (body fd)"
  shows "list_all (wf_basic_block F L ret n) (body (generalize_fundef fd))"
proof (cases fd)
  case (Fundef bblocks ar ret locals)
  then show ?thesis
    using assms
    by (auto simp: map_ran_def list.pred_map comp_def case_prod_beta
        intro: wf_basic_block_map_generalize_instr
        elim!: list.pred_mono_strong)
qed

lemma wf_fundefs_map_entry:
  assumes wf_F: "wf_fundefs (F_get F)" and
    same_funtype: "\<And>fd. fd \<in> ran (F_get F) \<Longrightarrow> funtype (f fd) = funtype fd" and
    same_arity: "\<And>fd. F_get F x = Some fd \<Longrightarrow> arity (f fd) = arity fd" and
    same_return: "\<And>fd. F_get F x = Some fd \<Longrightarrow> return (f fd) = return fd" and
    same_body_length: "\<And>fd. F_get F x = Some fd \<Longrightarrow> length (body (f fd)) = length (body fd)" and
    same_locals: "\<And>fd. F_get F x = Some fd \<Longrightarrow> fundef_locals (f fd) = fundef_locals fd" and
    same_labels: "\<And>fd. F_get F x = Some fd \<Longrightarrow> fst ` set (body (f fd)) = fst ` set (body fd)" and
    list_all_wf_basic_block_f: "\<And>fd.
      F_get F x = Some fd \<Longrightarrow>
      list_all (wf_basic_block (map_option funtype \<circ> F_get F) (fst ` set (body fd)) (return fd)
        (arity fd + fundef_locals fd)) (body fd) \<Longrightarrow>
      list_all (wf_basic_block (map_option funtype \<circ> F_get F) (fst ` set (body fd)) (return fd)
        (arity fd + fundef_locals fd)) (body (f fd))"
  shows "wf_fundefs (F_get (Fenv.map_entry F x f))"
proof (intro wf_fundefsI allI)
  fix y
  let ?F' = "F_get (Fenv.map_entry F x f)"
  show "pred_option (wf_fundef (map_option funtype \<circ> ?F')) (?F' y)"
  proof (cases "F_get F y")
    case None
    then show ?thesis
      by (simp add: Fenv.get_map_entry_conv)
  next
    case (Some gd)
    hence wf_gd: "wf_fundef (map_option funtype \<circ> F_get F) gd"
      using wf_F[THEN wf_fundefsD, THEN spec, of y] by simp
    then show ?thesis
    proof (cases "x = y")
      case True
      moreover have "wf_fundef (map_option funtype \<circ> F_get (Fenv.map_entry F y f)) (f gd)"
      proof (rule wf_fundefI)
        show "body (f gd) \<noteq> []"
          using same_body_length[unfolded True, OF Some]
          using wf_fundef_body_neq_NilD[OF wf_gd]
          by auto
      next
        show "list_all (wf_basic_block (map_option funtype \<circ> F_get (Fenv.map_entry F y f))
          (fst ` set (body (f gd))) (return (f gd)) (arity (f gd) + fundef_locals (f gd))) (body (f gd))"
        using Some True
        using wf_gd[THEN wf_fundefD] Some[unfolded True]
        by (auto simp: Fenv.map_option_comp_map_entry ranI assms(2-8) intro!: wf_fundefI)
      qed
      ultimately show ?thesis
        by (simp add: Some)
    next
      case False
      then show ?thesis
        unfolding Fenv.get_map_entry_neq[OF False]
        unfolding Some option.pred_inject
        using wf_gd[THEN wf_fundefD]
        using same_funtype
        by (auto simp: Fenv.map_option_comp_map_entry  intro!: wf_fundefI)
    qed
  qed
qed

lemma wf_fundefs_generalize:
  assumes wf_F: "wf_fundefs (F_get F)"
  shows "wf_fundefs (F_get (Fenv.map_entry F f generalize_fundef))"
  using wf_F
  apply (elim wf_fundefs_map_entry)
  by (auto elim: list_all_wf_basic_block_generalize_fundef)

lemma list_all_wf_basic_block_rewrite_fundef_body:
  assumes
    "list_all (wf_basic_block F L ret n) (body fd)" and
    "instr_at fd l pc = Some instr" and
    sp_instr_eq: "sp_instr F ret instr = sp_instr F ret instr'" and
    local_var_in_range_iff: "local_var_in_range n instr' \<longleftrightarrow> local_var_in_range n instr" and
    fun_call_in_range_iff: "fun_call_in_range F instr' \<longleftrightarrow> fun_call_in_range F instr" and
    jump_in_range_iff: "jump_in_range L instr' \<longleftrightarrow> jump_in_range L instr" and
    is_jump_iff: "is_jump instr' \<longleftrightarrow> is_jump instr" and
    is_return_iff: "is_return instr' \<longleftrightarrow> is_return instr"
  shows "list_all (wf_basic_block F L ret n) (body (rewrite_fundef_body fd l pc instr'))"
proof (cases fd)
  case (Fundef bblocks ar ret' locals)
  have wf_bblocks: "list_all (wf_basic_block F L ret n) bblocks"
    using assms(1) unfolding Fundef by simp

  moreover have "wf_basic_block F L ret n (l, instrs[pc := instr'])"
    if "map_of bblocks l = Some instrs" for instrs
  proof -
    have wf_basic_block_l_instrs: "wf_basic_block F L ret n (l, instrs)"
      by (rule list_all_map_of_SomeD[OF wf_bblocks that])

    have nth_instrs_pc: "pc < length instrs" "instrs ! pc = instr"
      using assms(2)[unfolded instr_at_def Fundef, simplified, unfolded that, simplified]
      by simp_all

    show ?thesis
    proof (rule wf_basic_blockI, simp, intro conjI)
      show "instrs \<noteq> []"
        using wf_basic_block_l_instrs
        by (auto elim: wf_basic_block.cases)
    next
      show "list_all (local_var_in_range n) (instrs[pc := instr'])"
        using wf_basic_block_l_instrs nth_instrs_pc
        by (auto simp: local_var_in_range_iff
            elim!: wf_basic_block.cases intro!: list_all_list_updateI)
    next
      show "list_all (\<lambda>i. \<not> is_jump i \<and> \<not> is_return i) (butlast (instrs[pc := instr']))"
        using wf_basic_block_l_instrs nth_instrs_pc
        apply (auto simp: butlast_list_update elim!: wf_basic_block.cases)
        apply (rule list_all_list_updateI)
         apply assumption
        by (simp add: is_jump_iff is_return_iff list_all_length nth_butlast)
    next
      show "sp_instrs F ret (instrs[pc := instr']) [] []"
        using wf_basic_block_l_instrs nth_instrs_pc sp_instr_eq
        by (auto elim!: wf_basic_block.cases elim!: sp_instrs_list_update)
    next
      show "list_all (fun_call_in_range F) (instrs[pc := instr'])"
        using wf_basic_block_l_instrs nth_instrs_pc
        by (auto simp: fun_call_in_range_iff
            elim!: wf_basic_block.cases intro!: list_all_list_updateI)
    next
      show "list_all (jump_in_range L) (instrs[pc := instr'])"
        using wf_basic_block_l_instrs nth_instrs_pc
        by (auto simp: jump_in_range_iff elim!: wf_basic_block.cases intro!: list_all_list_updateI)
    qed
  qed

  with Fundef show ?thesis
    using assms(1,2)
    by (auto simp add: rewrite_fundef_body_def map_entry_map_of_Some_conv
        intro: list_all_updateI dest!: instr_atD)
qed

lemma wf_fundefs_rewrite_body:
  assumes "wf_fundefs (F_get F)" and
    "next_instr (F_get F) f l pc = Some instr" and
    sp_instr_eq: "\<And>ret.
      sp_instr (map_option funtype \<circ> F_get F) ret instr' =
      sp_instr (map_option funtype \<circ> F_get F) ret instr" and
    local_var_in_range_iff: "\<And>n. local_var_in_range n instr' \<longleftrightarrow> local_var_in_range n instr" and
    fun_call_in_range_iff:
      "fun_call_in_range (map_option funtype \<circ> F_get F) instr' \<longleftrightarrow>
       fun_call_in_range (map_option funtype \<circ> F_get F) instr" and
    jump_in_range_iff: "\<And>L. jump_in_range L instr' \<longleftrightarrow> jump_in_range L instr" and
    is_jump_iff: "is_jump instr' \<longleftrightarrow> is_jump instr" and
    is_return_iff: "is_return instr' \<longleftrightarrow> is_return instr"
  shows "wf_fundefs (F_get (Fenv.map_entry F f (\<lambda>fd. rewrite_fundef_body fd l pc instr')))"
proof -
  obtain fd where F_f: "F_get F f = Some fd" and instr_at_pc: "instr_at fd l pc = Some instr"
    using assms(2)[THEN next_instrD]
    by auto

  show ?thesis
    using assms(1)
  proof (rule wf_fundefs_map_entry)
    fix fd
    show "fst ` set (body (rewrite_fundef_body fd l pc instr')) = fst ` set (body fd)"
      by (cases fd) (simp add: rewrite_fundef_body_def dom_map_entry)
  next
    fix gd
    assume "F_get F f = Some gd"
    hence "gd = fd"
      using F_f by simp
    then show
      "list_all (wf_basic_block (map_option funtype \<circ> F_get F) (fst ` set (body gd)) (return gd)
        (arity gd + fundef_locals gd)) (body gd) \<Longrightarrow>
       list_all (wf_basic_block (map_option funtype \<circ> F_get F) (fst ` set (body gd)) (return gd)
        (arity gd + fundef_locals gd)) (body (rewrite_fundef_body gd l pc instr'))"
    using assms(1,3-)
    using F_f instr_at_pc
    by (elim list_all_wf_basic_block_rewrite_fundef_body) simp_all
  qed simp_all
qed

lemma sp_instr_Op_OpInl_conv:
  assumes "op = \<DD>\<ee>\<II>\<nn>\<ll> opinl"
  shows "sp_instr F ret (IOp op) = sp_instr F ret (IOpInl opinl)"
  by (auto simp: assms elim: sp_instr.cases intro: sp_instr.OpInl sp_instr.Op)

lemma wf_state_step_preservation:
  assumes "wf_state s" and "step s s'"
  shows "wf_state s'"
  using assms(2,1)
proof (cases s s' rule: step.cases)
  case (step_op_inl F f l pc op ar \<Sigma> \<Sigma>' opinl x F' H R st)
  then show ?thesis
    using assms(1)
    by (auto intro!: wf_stateI intro: sp_instr_Op_OpInl_conv[symmetric]
          elim!: wf_fundefs_rewrite_body dest!: wf_stateD \<II>\<nn>\<ll>_invertible)
next
  case (step_op_inl_miss F f l pc opinl ar \<Sigma> \<Sigma>' x F' H R st)
  then show ?thesis
    using assms(1)
    by (auto intro!: wf_stateI intro: sp_instr_Op_OpInl_conv
          elim!: wf_fundefs_rewrite_body dest!: wf_stateD)
qed (auto simp: box_stack_def 
      intro!: wf_stateI wf_fundefs_generalize
      intro: sp_instr.intros
      dest!: wf_stateD)

(* lemma
  assumes "wf_state s"
  shows "\<exists>s'. step s s'"
proof (cases s)
  case (State F H frames)
  hence "frames \<noteq> []" and wf_fundefs_bblocks: "wf_fundefs (F_get F)"
    using assms(1)[THEN wf_stateD] by simp_all
  then obtain f l pc locals \<Sigma> frames' where "frames = Frame f l pc locals \<Sigma> # frames'"
    unfolding neq_Nil_conv by (metis frame.exhaust)
  
  show ?thesis
  proof (cases "next_instr (F_get F) f l pc")
    case None
    then show ?thesis sorry
  next
    case (Some a)
    then show ?thesis sorry
  qed
qed *)
  

end

end