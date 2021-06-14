theory Inca_to_Ubx_simulation
  imports List_util Result
    "VeriComp.Simulation"
    Inca Ubx Ubx_Verification Unboxed_lemmas
begin

lemma take_:"Suc n = length xs \<Longrightarrow> take n xs = butlast xs"
  using butlast_conv_take diff_Suc_1 append_butlast_last_id
  by (metis butlast_conv_take diff_Suc_1)

lemma append_take_singleton_conv:"Suc n = length xs \<Longrightarrow> xs = take n xs @ [xs ! n]"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using Cons
      by simp
  next
    case (Suc n')
    have "Suc n' = length xs"
      by (rule Cons.prems[unfolded Suc, simplified])
    from Suc show ?thesis
      by (auto intro: Cons.IH[OF \<open>Suc n' = length xs\<close>])
  qed
qed


section \<open>Locale imports\<close>

locale inca_to_ubx_simulation =
  Sinca: inca
    Finca_empty Finca_get Finca_add Finca_to_list
    heap_empty heap_get heap_add heap_to_list
    uninitialized is_true is_false
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll> +
  Subx: ubx
    Fubx_empty Fubx_get Fubx_add Fubx_to_list
    heap_empty heap_get heap_add heap_to_list
    uninitialized is_true is_false
    box_ubx1 unbox_ubx1 box_ubx2 unbox_ubx2
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll> \<UU>\<bb>\<xx>\<OO>\<pp> \<UU>\<bb>\<xx> \<BB>\<oo>\<xx> \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
  for
    \<comment> \<open>Functions environments\<close>
    Finca_empty and
    Finca_get :: "'fenv_inca \<Rightarrow> 'fun \<Rightarrow> ('label, ('dyn, 'var, 'fun, 'label, 'op, 'opinl) Inca.instr) fundef option" and
    Finca_add and Finca_to_list and

    Fubx_empty and
    Fubx_get :: "'fenv_ubx \<Rightarrow> 'fun \<Rightarrow> ('label, ('dyn, 'var, 'fun, 'label, 'op, 'opinl, 'opubx, 'ubx1, 'ubx2) Ubx.instr) fundef option" and
    Fubx_add and Fubx_to_list and

    \<comment> \<open>Memory heap\<close>
    heap_empty and heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and heap_add and heap_to_list and

    \<comment> \<open>Dynamic values\<close>
    uninitialized :: 'dyn and is_true and is_false and

    \<comment> \<open>Unboxed values\<close>
    box_ubx1 and unbox_ubx1 and
    box_ubx2 and unbox_ubx2 and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> and \<AA>\<rr>\<ii>\<tt>\<yy> and \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> and \<UU>\<bb>\<xx>\<OO>\<pp> and \<UU>\<bb>\<xx> and \<BB>\<oo>\<xx> and \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
begin


section \<open>Normalization\<close>

fun norm_instr where
  "norm_instr (Ubx.IPush d) = Inca.IPush d" |
  "norm_instr (Ubx.IPushUbx1 n) = Inca.IPush (box_ubx1 n)" |
  "norm_instr (Ubx.IPushUbx2 b) = Inca.IPush (box_ubx2 b)" |
  "norm_instr Ubx.IPop = Inca.IPop" |
  "norm_instr (Ubx.IGet n) = Inca.IGet n" |
  "norm_instr (Ubx.IGetUbx _ n) = Inca.IGet n" |
  "norm_instr (Ubx.ISet n) = Inca.ISet n" |
  "norm_instr (Ubx.ISetUbx _ n) = Inca.ISet n" |
  "norm_instr (Ubx.ILoad x) = Inca.ILoad x" |
  "norm_instr (Ubx.ILoadUbx _ x) = Inca.ILoad x" |
  "norm_instr (Ubx.IStore x) = Inca.IStore x" |
  "norm_instr (Ubx.IStoreUbx _ x) = Inca.IStore x" |
  "norm_instr (Ubx.IOp op) = Inca.IOp op" |
  "norm_instr (Ubx.IOpInl op) = Inca.IOpInl op" |
  "norm_instr (Ubx.IOpUbx op) = Inca.IOpInl (\<BB>\<oo>\<xx> op)" |
  "norm_instr (Ubx.ICJump l\<^sub>t l\<^sub>f) = Inca.ICJump l\<^sub>t l\<^sub>f" |
  "norm_instr (Ubx.ICall x) = Inca.ICall x" |
  "norm_instr Ubx.IReturn = Inca.IReturn"

lemma norm_generalize_instr[simp]: "norm_instr (Subx.generalize_instr instr) = norm_instr instr"
  by (cases instr) simp_all

abbreviation norm_eq where
  "norm_eq x y \<equiv> x = norm_instr y"

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
  using rel_F1_F2[THEN rel_fundefsD, of f]
proof (cases rule: option.rel_cases)
  case None
  thus ?thesis by (simp add: next_instr_def)
next
  case (Some fd1 fd2)
  then show ?thesis
    by (auto simp: next_instr_def intro: rel_fundef_imp_rel_option_instr_at)
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

lemma rel_fundef_generalizeI:
  assumes "rel_fundef (=) norm_eq fd1 fd2"
  shows "rel_fundef (=) norm_eq fd1 (Subx.generalize_fundef fd2)"
  using assms
  by (cases rule: fundef.rel_cases)
    (auto simp: map_ran_def list.rel_map elim: list.rel_mono_strong)

lemma rel_fundefs_generalizeI:
  assumes "rel_fundefs (Finca_get F1) (Fubx_get F2)"
  shows "rel_fundefs (Finca_get F1) (Fubx_get (Subx.Fenv.map_entry F2 f Subx.generalize_fundef))"
proof (rule rel_fundefsI)
  fix x
  show "rel_option (rel_fundef (=) norm_eq)
    (Finca_get F1 x) (Fubx_get (Subx.Fenv.map_entry F2 f Subx.generalize_fundef) x)"
    unfolding Subx.Fenv.get_map_entry_conv
    unfolding option.rel_map
    using assms(1)[THEN rel_fundefsD, of x]
    by (auto intro: rel_fundef_generalizeI elim: option.rel_mono_strong)
qed

lemma rel_fundefs_rewriteI:
  assumes
    rel_F1_F2: "rel_fundefs (Finca_get F1) (Fubx_get F2)" and
    "norm_eq instr1' instr2'"
  shows "rel_fundefs
    (Finca_get (Sinca.Fenv.map_entry F1 f (\<lambda>fd. rewrite_fundef_body fd l pc instr1')))
    (Fubx_get (Subx.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc instr2')))"
  (is "rel_fundefs (Finca_get ?F1') (Fubx_get ?F2')")
proof (rule rel_fundefsI)
  fix x
  show "rel_option (rel_fundef (=) norm_eq) (Finca_get ?F1' x) (Fubx_get ?F2' x)"
  proof (cases "f = x")
    case True
    show ?thesis
      using rel_F1_F2[THEN rel_fundefsD, of x] True assms(2)
      by (cases rule: option.rel_cases) (auto intro: rel_fundef_rewrite_body)
  next
    case False
    then show ?thesis
      using rel_F1_F2[THEN rel_fundefsD, of x] by simp
  qed
qed


section \<open>Equivalence of call stacks\<close>

definition norm_stack :: "('dyn, 'ubx1, 'ubx2) unboxed list \<Rightarrow> 'dyn list" where
  "norm_stack \<Sigma> \<equiv> List.map Subx.norm_unboxed \<Sigma>"

lemma norm_stack_Nil[simp]: "norm_stack [] = []"
  by (simp add: norm_stack_def)

lemma norm_stack_Cons[simp]: "norm_stack (d # \<Sigma>) = Subx.norm_unboxed d # norm_stack \<Sigma>"
  by (simp add: norm_stack_def)

lemma norm_stack_append: "norm_stack (xs @ ys) = norm_stack xs @ norm_stack ys"
  by (simp add: norm_stack_def)

lemmas drop_norm_stack = drop_map[where f = Subx.norm_unboxed, folded norm_stack_def]
lemmas take_norm_stack = take_map[where f = Subx.norm_unboxed, folded norm_stack_def]
lemmas norm_stack_map = map_map[where f = Subx.norm_unboxed, folded norm_stack_def]

lemma norm_box_stack[simp]: "norm_stack (map Subx.box_operand \<Sigma>) = norm_stack \<Sigma>"
  by (induction \<Sigma>) (auto simp: norm_stack_def)

lemma length_norm_stack[simp]: "length (norm_stack xs) = length xs"
  by (simp add: norm_stack_def)

definition is_valid_fun_call where
  "is_valid_fun_call F f l pc \<Sigma> g \<equiv> next_instr F f l pc = Some (ICall g) \<and>
      (\<exists>gd. F g = Some gd \<and> arity gd \<le> length \<Sigma> \<and> list_all is_dyn_operand (take (arity gd) \<Sigma>))"

lemma is_valid_funcall_map_entry_generalize_fundefI:
  assumes "is_valid_fun_call (Fubx_get F2) g l pc \<Sigma> z"
  shows "is_valid_fun_call (Fubx_get (Subx.Fenv.map_entry F2 f Subx.generalize_fundef)) g l pc \<Sigma> z"
proof (cases "f = z")
  case True
  then show ?thesis
    using assms
    by (cases "z = g")
      (auto simp: is_valid_fun_call_def next_instr_def Subx.instr_at_generalize_fundef_conv)
next
  case False
  then show ?thesis
    using assms
    by (cases "Fubx_get F2 g")
      (auto simp: is_valid_fun_call_def next_instr_def
          Subx.instr_at_generalize_fundef_conv Subx.Fenv.get_map_entry_conv)
qed

lemma is_valid_fun_call_map_box_operandI:
  assumes "is_valid_fun_call (Fubx_get F2) g l pc \<Sigma> z"
  shows "is_valid_fun_call (Fubx_get F2) g l pc (map Subx.box_operand \<Sigma>) z"
  using assms
  unfolding is_valid_fun_call_def
  by (auto simp: take_map list.pred_map list.pred_True)

lemma inst_at_rewrite_fundef_body_disj:
  "instr_at (rewrite_fundef_body fd l pc instr) l pc = Some instr \<or>
   instr_at (rewrite_fundef_body fd l pc instr) l pc = None"
proof (cases fd)
  case (Fundef bblocks ar locals)
  show ?thesis
  proof (cases "map_of bblocks l")
    case None
    thus ?thesis
      using Fundef
      by (simp add: rewrite_fundef_body_def instr_at_def map_entry_map_of_None_conv)
  next
    case (Some instr')
    moreover hence "l \<in> fst ` set bblocks"
      by (meson domI domIff map_of_eq_None_iff)
    ultimately show ?thesis
      using Fundef
      apply (auto simp add: rewrite_fundef_body_def instr_at_def map_entry_map_of_Some_conv)
      by (smt (verit, ccfv_threshold) length_list_update nth_list_update_eq option.case_eq_if option.distinct(1) option.sel update_Some_unfold)
  qed
qed

lemma is_valid_fun_call_map_entry_conv:
  assumes "next_instr (Fubx_get F2) f l pc = Some instr" "\<not> is_fun_call instr" "\<not> is_fun_call instr'"
  shows
    "is_valid_fun_call (Fubx_get (Subx.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc instr')))=
     is_valid_fun_call (Fubx_get F2)"
proof (intro ext)
  fix f' l' pc' \<Sigma> g
  show
    "is_valid_fun_call (Fubx_get (Subx.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc instr'))) f' l' pc' \<Sigma> g =
     is_valid_fun_call (Fubx_get F2) f' l' pc' \<Sigma> g"
  proof (cases "f = f'")
    case True
    then show ?thesis
      using assms
      apply (cases "f = g")
      by (auto simp: is_valid_fun_call_def next_instr_eq_Some_conv
          instr_at_rewrite_fundef_body_conv if_split_eq1)
  next
    case False
    then show ?thesis
      using assms
      apply (cases "f = g")
      by (auto simp: is_valid_fun_call_def next_instr_eq_Some_conv)
  qed
qed

lemma is_valid_fun_call_map_entry_neq_f_neq_l:
  assumes "f \<noteq> g" "l \<noteq> l'"
  shows
    "is_valid_fun_call (Fubx_get (Subx.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc instr'))) g l' =
     is_valid_fun_call (Fubx_get F2) g l'"
  apply (intro ext)
  unfolding is_valid_fun_call_def
  using assms
  apply (simp add: next_instr_eq_Some_conv)
  apply (rule iffI; simp)
  unfolding Subx.Fenv.get_map_entry_conv
  apply simp
   apply (metis arity_rewrite_fundef_body)
  apply safe
  by simp

inductive rel_stacktraces for F where
  rel_stacktraces_Nil:
    "rel_stacktraces F opt [] []" |

  rel_stacktraces_Cons:
    "rel_stacktraces F (Some f) st1 st2 \<Longrightarrow>
    \<Sigma>1 = map Subx.norm_unboxed \<Sigma>2 \<Longrightarrow>
    R1 = map Subx.norm_unboxed R2 \<Longrightarrow>
    list_all is_dyn_operand R2 \<Longrightarrow>
    F f = Some fd2 \<Longrightarrow> map_of (body fd2) l = Some instrs \<Longrightarrow>
    Subx.sp_instrs (map_option funtype \<circ> F) (return fd2) (take pc instrs) [] (map typeof \<Sigma>2) \<Longrightarrow>
    pred_option (is_valid_fun_call F f l pc \<Sigma>2) opt \<Longrightarrow>
    rel_stacktraces F opt (Frame f l pc R1 \<Sigma>1 # st1) (Frame f l pc R2 \<Sigma>2 # st2)"

lemma rel_stacktraces_map_entry_gneralize_fundefI[intro]:
  assumes "rel_stacktraces (Fubx_get F2) opt st1 st2"
  shows "rel_stacktraces (Fubx_get (Subx.Fenv.map_entry F2 f Subx.generalize_fundef))
    opt st1 (Subx.box_stack f st2)"
  using assms(1)
proof (induction opt st1 st2 rule: rel_stacktraces.induct)
  case (rel_stacktraces_Nil opt)
  thus ?case
    by (auto intro: rel_stacktraces.rel_stacktraces_Nil)
next
  case (rel_stacktraces_Cons g st1 st2 \<Sigma>1 \<Sigma>2 R1 R2 gd2 l instrs pc opt)
  show ?case
  proof (cases "f = g")
    case True
    then show ?thesis
      using rel_stacktraces_Cons
    apply auto
     apply (rule rel_stacktraces.rel_stacktraces_Cons)
             apply assumption
            apply simp
           apply (rule refl)
          apply assumption
        apply simp
      by (auto simp add: take_map Subx.map_of_generalize_fundef_conv
          intro!: Subx.sp_instrs_generalize0
          intro!: is_valid_funcall_map_entry_generalize_fundefI is_valid_fun_call_map_box_operandI
          elim!: option.pred_mono_strong)
  next
    case False
    then show ?thesis
      using rel_stacktraces_Cons
      by (auto intro: rel_stacktraces.intros is_valid_funcall_map_entry_generalize_fundefI
          elim!: option.pred_mono_strong)
  qed
qed

lemma rel_stacktraces_map_entry_rewrite_fundef_body:
  assumes
    "rel_stacktraces (Fubx_get F2) opt st1 st2" and
    "next_instr (Fubx_get F2) f l pc = Some instr" and
    "\<And>ret. Subx.sp_instr (map_option funtype \<circ> Fubx_get F2) ret instr =
      Subx.sp_instr (map_option funtype \<circ> Fubx_get F2) ret instr'" and
    "\<not> is_fun_call instr" "\<not> is_fun_call instr'"
  shows "rel_stacktraces
    (Fubx_get (Subx.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc instr'))) opt st1 st2"
  using assms(1)
proof (induction opt st1 st2 rule: rel_stacktraces.induct)
  case (rel_stacktraces_Nil opt)
  then show ?case 
    by (auto intro: rel_stacktraces.rel_stacktraces_Nil)
next
  case (rel_stacktraces_Cons g st1 st2 \<Sigma>1 \<Sigma>2 R1 R2 gd2 l' instrs pc' opt)
  show ?case (is "rel_stacktraces (Fubx_get ?F2') opt ?st1 ?st2")
  proof (cases "f = g")
    case True
    show ?thesis
    proof (cases "l' = l")
      case True
      show ?thesis
        apply (rule rel_stacktraces.rel_stacktraces_Cons)
        using rel_stacktraces_Cons.IH apply simp
        using rel_stacktraces_Cons.hyps apply simp
        using rel_stacktraces_Cons.hyps apply simp
        using rel_stacktraces_Cons.hyps apply simp
        using rel_stacktraces_Cons.hyps \<open>f = g\<close> apply simp
        using rel_stacktraces_Cons.hyps True apply simp
        using rel_stacktraces_Cons.hyps apply simp
        using rel_stacktraces_Cons.hyps assms \<open>f = g\<close> True
         apply (cases "pc' \<le> pc") []
         apply (auto simp add: take_update_swap intro!: Subx.sp_instrs_list_update
            dest!: next_instrD instr_atD) [2]
        using rel_stacktraces_Cons.hyps
        unfolding is_valid_fun_call_map_entry_conv[OF assms(2,4,5)]
        by simp
    next
      case False
      show ?thesis
      proof (rule rel_stacktraces.rel_stacktraces_Cons)
        show "Fubx_get ?F2' g = Some (rewrite_fundef_body gd2 l pc instr')"
          unfolding \<open>f = g\<close>
          using rel_stacktraces_Cons.hyps by simp
      next
        show "pred_option (is_valid_fun_call (Fubx_get ?F2') g l' pc' \<Sigma>2) opt"
          unfolding is_valid_fun_call_map_entry_conv[OF assms(2,4,5)]
          using rel_stacktraces_Cons.hyps by simp
      qed (insert rel_stacktraces_Cons False, simp_all)
    qed
  next
    case False
    then show ?thesis
      using rel_stacktraces_Cons
      by (auto simp: is_valid_fun_call_map_entry_conv[OF assms(2,4,5)]
          intro!: rel_stacktraces.rel_stacktraces_Cons)
  qed
qed


section \<open>Simulation relation\<close>

inductive match (infix "\<sim>" 55) where
  matchI: "Subx.wf_state (State F2 H st2) \<Longrightarrow>
    rel_fundefs (Finca_get F1) (Fubx_get F2) \<Longrightarrow>
    rel_stacktraces (Fubx_get F2) None st1 st2 \<Longrightarrow>
    match (State F1 H st1) (State F2 H st2)"

lemmas matchI[consumes 0, case_names wf_state rel_fundefs rel_stacktraces] = match.intros(1)


section \<open>Backward simulation\<close>

lemma map_eq_append_map_drop:
  "map f xs = ys @ map f (drop n xs) \<longleftrightarrow> map f (take n xs) = ys"
  by (metis append_same_eq append_take_drop_id map_append)

lemma ap_map_list_cast_Dyn_to_map_norm:
  assumes "ap_map_list cast_Dyn xs = Some ys"
  shows "ys = map Subx.norm_unboxed xs"
proof -
  from assms have "list_all2 (\<lambda>x y. cast_Dyn x = Some y) xs ys"
    by (simp add: ap_map_list_iff_list_all2)
  thus ?thesis
    by (induction xs ys rule: list.rel_induct) (auto dest: cast_inversions)
qed

lemma ap_map_list_cast_Dyn_to_all_Dyn:
  assumes "ap_map_list cast_Dyn xs = Some ys"
  shows "list_all (\<lambda>x. typeof x = None) xs"
proof -
  from assms have "list_all2 (\<lambda>x y. cast_Dyn x = Some y) xs ys"
    by (simp add: ap_map_list_iff_list_all2)
  hence "list_all2 (\<lambda>x y. typeof x = None) xs ys"
    by (auto intro: list.rel_mono_strong cast_Dyn_eq_Some_imp_typeof)
  thus ?thesis
    by (induction xs ys rule: list.rel_induct) auto
qed

lemma ap_map_list_cast_Dyn_map_typeof_replicate_conv:
  assumes "ap_map_list cast_Dyn xs = Some ys" and "n = length xs"
  shows "map typeof xs = replicate n None"
  using assms
  by (auto simp: list.pred_set intro!: replicate_eq_map[symmetric]
        dest!: ap_map_list_cast_Dyn_to_all_Dyn)

lemma cast_Dyn_eq_Some_conv_norm_unboxed[simp]: "cast_Dyn i = Some i' \<Longrightarrow> Subx.norm_unboxed i = i'"
  by (cases i) simp_all

lemma cast_Dyn_eq_Some_conv_typeof[simp]: "cast_Dyn i = Some i' \<Longrightarrow> typeof i = None"
  by (cases i) simp_all

lemma backward_lockstep_simulation:
  assumes "match s1 s2" and "Subx.step s2 s2'"
  shows "\<exists>s1'. Sinca.step s1 s1' \<and> match s1' s2'"
  using assms
proof (induction s1 s2 rule: match.induct)
  case (matchI F2 H st2 F1 st1)
  from matchI(3,1,2,4) show ?case
  proof (induction "None :: 'fun option" st1 st2 rule: rel_stacktraces.induct)
    case rel_stacktraces_Nil
    hence False by (auto elim: Subx.step.cases)
    thus ?case by simp
  next
    case (rel_stacktraces_Cons f st1 st2 \<Sigma>1 \<Sigma>2 R1 R2 fd2 l instrs pc)
    note hyps = rel_stacktraces_Cons.hyps
    note prems = rel_stacktraces_Cons.prems
    have wf_state2: "Subx.wf_state (State F2 H (Frame f l pc R2 \<Sigma>2 # st2))" using prems by simp
    have rel_F1_F2: "rel_fundefs (Finca_get F1) (Fubx_get F2)" using prems by simp
    have rel_st1_st2: "rel_stacktraces (Fubx_get F2) (Some f) st1 st2" using hyps by simp
    have \<Sigma>1_def: "\<Sigma>1 = map Subx.norm_unboxed \<Sigma>2" using hyps by simp
    have R1_def: "R1 = map Subx.norm_unboxed R2" using hyps by simp
    have all_dyn_R2: "list_all is_dyn_operand R2" using hyps by simp
    have F2_f: "Fubx_get F2 f = Some fd2" using hyps by simp
    have map_of_fd2_l: "map_of (body fd2) l = Some instrs" using hyps by simp
    have sp_instrs_prefix: "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2)
      (take pc instrs) [] (map typeof \<Sigma>2)"
      using hyps by simp

    note next_instr2 = rel_fundefs_next_instr2[OF rel_F1_F2]
    note sp_instrs_prefix' =
      Subx.sp_instrs_singletonI[THEN Subx.sp_instrs_appendI[OF sp_instrs_prefix]]

    obtain fd1 where
      F1_f: "Finca_get F1 f = Some fd1" and rel_fd1_fd2: "rel_fundef (=) norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto

    have wf_F2: "Subx.wf_fundefs (Fubx_get F2)"
      by (rule wf_state2[THEN Subx.wf_stateD, simplified])

    have wf_fd2: "Subx.wf_fundef (map_option funtype \<circ> Fubx_get F2) fd2"
      using F2_f wf_F2[THEN Subx.wf_fundefsD, THEN spec, of f]
      by simp

    have
      instrs_neq_Nil: "instrs \<noteq> []" and
      all_jumps_in_range: "list_all (Subx.jump_in_range (fst ` set (body fd2))) instrs" and
      sp_instrs_instrs: "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2) instrs [] []"
      using list_all_map_of_SomeD[OF wf_fd2[THEN Subx.wf_fundef_all_wf_basic_blockD] map_of_fd2_l]
      by (auto dest: Subx.wf_basic_blockD)

    have sp_instrs_instrs': "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2)
      (butlast instrs @ [instrs ! pc]) [] []" if pc_def: "pc = length instrs - 1"
      unfolding pc_def last_conv_nth[OF instrs_neq_Nil, symmetric]
      unfolding append_butlast_last_id[OF instrs_neq_Nil]
      by (rule sp_instrs_instrs)

    have sp_instr_last: "Subx.sp_instr (map_option funtype \<circ> Fubx_get F2) (return fd2)
      (instrs ! pc) (map typeof \<Sigma>2) []" if pc_def: "pc = length instrs - 1"
      using sp_instrs_instrs'[OF pc_def]
      using sp_instrs_prefix[unfolded pc_def butlast_conv_take[symmetric]]
      by (auto dest!: Subx.sp_instrs_appendD')

    from list_all_map_of_SomeD[OF wf_fd2[THEN Subx.wf_fundef_all_wf_basic_blockD] map_of_fd2_l]
    have is_jump_nthD: "\<And>n. is_jump (instrs ! n) \<Longrightarrow> n < length instrs \<Longrightarrow> n = length instrs - 1"
      by (auto dest!: Subx.wf_basic_blockD
            list_all_butlast_not_nthD[of "\<lambda>i. \<not> is_jump i \<and> \<not> Ubx.instr.is_return i", simplified, OF _ disjI1])

    note wf_s2' = Subx.wf_state_step_preservation[OF wf_state2 prems(3)]
    
    from prems(3) show ?case
      using wf_s2'
    proof (induction "State F2 H (Frame f l pc R2 \<Sigma>2 # st2)" s2' rule: Subx.step.induct)
      case (step_push d)
      let ?st1' = "Frame f l (Suc pc) R1 (d # \<Sigma>1) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          using step_push.hyps
          by (auto intro!: Sinca.step_push dest: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_push.hyps rel_stacktraces_Cons
          using Subx.sp_instr.Push[THEN sp_instrs_prefix']
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_push.prems rel_F1_F2
          by (auto intro: match.intros)
      qed
    next
      case (step_push_ubx1 n)
      let ?st1' = "Frame f l (Suc pc) R1 (box_ubx1 n # \<Sigma>1) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          using step_push_ubx1.hyps
          by (auto intro!: Sinca.step_push dest: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_push_ubx1.hyps rel_stacktraces_Cons
          using Subx.sp_instr.PushUbx1[THEN sp_instrs_prefix']
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_push_ubx1.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_push_ubx2 b)
      let ?st1' = "Frame f l (Suc pc) R1 (box_ubx2 b # \<Sigma>1) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          using step_push_ubx2.hyps
          by (auto intro!: Sinca.step_push dest: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_push_ubx2.hyps rel_stacktraces_Cons
          using Subx.sp_instr.PushUbx2[THEN sp_instrs_prefix']
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_push_ubx2.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_pop d \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) R1 (map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_pop.hyps
          by (auto intro!: Sinca.step_pop dest: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_pop.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Pop
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_pop.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_get n d)
      let ?st1' = "Frame f l (Suc pc) R1 (R1 ! n # map Subx.norm_unboxed \<Sigma>2) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def R1_def
          using step_get.hyps
          by (auto intro!: Sinca.step_get dest: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_get.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Get
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_get.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_get_ubx_hit \<tau> n d blob)
      let ?st1' = "Frame f l (Suc pc) R1 (R1 ! n # map Subx.norm_unboxed \<Sigma>2) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def R1_def
          using step_get_ubx_hit.hyps
          by (auto intro!: Sinca.step_get dest: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_get_ubx_hit.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.GetUbx
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_get_ubx_hit.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_get_ubx_miss \<tau> n d F2')
      hence "R1 ! n = d"
        by (simp add: R1_def)
      let ?st1' = "Frame f l (Suc pc) R1 (R1 ! n # map Subx.norm_unboxed \<Sigma>2) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2' H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def R1_def
          using step_get_ubx_miss.hyps
          by (auto intro!: Sinca.step_get dest: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2') None ?st1' ?st2'"
          apply simp
        proof (rule rel_stacktraces.intros)
          show "rel_stacktraces (Fubx_get F2') (Some f) st1 (Subx.box_stack f st2)"
            unfolding step_get_ubx_miss.hyps
            using rel_st1_st2
            by (rule rel_stacktraces_map_entry_gneralize_fundefI)
        next
          show "Fubx_get F2' f = Some (Subx.generalize_fundef fd2)"
            unfolding step_get_ubx_miss.hyps
            using F2_f
            by simp
        next
          show "map_of (body (Subx.generalize_fundef fd2)) l = Some (map Subx.generalize_instr instrs)"
            unfolding Subx.map_of_generalize_fundef_conv
            unfolding map_of_fd2_l
            by simp
        next
          show "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2')
            (return (Subx.generalize_fundef fd2))
            (take (Suc pc) (map Subx.generalize_instr instrs))
            [] (map typeof (OpDyn d # map Subx.box_operand \<Sigma>2))"
            using step_get_ubx_miss.hyps F2_f map_of_fd2_l
            by (auto simp: take_map take_Suc_conv_app_nth simp del: map_append
              intro!: sp_instrs_prefix'[THEN Subx.sp_instrs_generalize0] Subx.sp_instr.GetUbx
              dest!: next_instrD instr_atD)
        qed (insert R1_def all_dyn_R2 \<open>R1 ! n = d\<close>, simp_all)
        thus "?MATCH ?s1' (State F2' H ?st2')"
          using step_get_ubx_miss.prems rel_F1_F2
          unfolding step_get_ubx_miss.hyps
          by (auto intro!: match.intros rel_fundefs_generalizeI)
      qed
    next
      case (step_set n blob d R2' \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) (map Subx.norm_unboxed R2') (map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def R1_def
          using step_set.hyps
          by (auto simp: map_update intro!: Sinca.step_set dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_set.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Set
              intro: list_all_list_updateI
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_set.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_set_ubx \<tau> n blob d R2' \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) (map Subx.norm_unboxed R2') (map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def R1_def
          using step_set_ubx.hyps
          by (auto simp: map_update intro!: Sinca.step_set dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_set_ubx.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.SetUbx
              intro: list_all_list_updateI
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_set_ubx.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_load x i i' d \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) R1 (d # map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_load.hyps
          by (auto intro!: Sinca.step_load dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_load.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Load
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_load.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_load_ubx_hit \<tau> x i i' d blob \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) R1 (d # map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_load_ubx_hit.hyps
          by (auto intro!: Sinca.step_load dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_load_ubx_hit.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.LoadUbx
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_load_ubx_hit.prems rel_F1_F2
          by (auto intro!: match.intros)
      qed
    next
      case (step_load_ubx_miss \<tau> x i i' d F2' \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) R1 (d # map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2' H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_load_ubx_miss.hyps
          by (auto intro!: Sinca.step_load dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2') None ?st1' ?st2'"
          apply simp
        proof (rule rel_stacktraces.intros)
          show "rel_stacktraces (Fubx_get F2') (Some f) st1 (Subx.box_stack f st2)"
          unfolding step_load_ubx_miss
          using rel_st1_st2
          by (rule rel_stacktraces_map_entry_gneralize_fundefI)
        next
          show "Fubx_get F2' f = Some (Subx.generalize_fundef fd2)"
            unfolding step_load_ubx_miss.hyps
            using F2_f by (simp add: Subx.map_of_generalize_fundef_conv)
        next
          show "map_of (body (Subx.generalize_fundef fd2)) l =
            Some (map Subx.generalize_instr instrs)"
            unfolding Subx.map_of_generalize_fundef_conv
            using step_load_ubx_miss.hyps F2_f map_of_fd2_l
            by simp
        next
          show "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2') (return (Subx.generalize_fundef fd2))
            (take (Suc pc) (map Subx.generalize_instr instrs))
            [] (map typeof (OpDyn d # map Subx.box_operand \<Sigma>2'))"
            using step_load_ubx_miss.hyps F2_f map_of_fd2_l
            by (auto simp: take_map take_Suc_conv_app_nth simp del: map_append
              intro!: sp_instrs_prefix'[THEN Subx.sp_instrs_generalize0] Subx.sp_instr.LoadUbx
              dest!: next_instrD instr_atD)
        qed (insert all_dyn_R2, simp_all add: R1_def)
        thus "?MATCH ?s1' (State F2' H ?st2')"
          using step_load_ubx_miss.prems rel_F1_F2
          unfolding step_load_ubx_miss.hyps
          by (auto intro: match.intros rel_fundefs_generalizeI)
      qed
    next
      case (step_store x i i' y d H' \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) R1 (map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H' ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H' ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_store.hyps
          by (auto intro: Sinca.step_store dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_store.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Store
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H' ?st2')"
          using step_store.prems rel_F1_F2
          by (auto intro: match.intros)
      qed
    next
      case (step_store_ubx \<tau> x i i' blob d H' \<Sigma>2')
      let ?st1' = "Frame f l (Suc pc) R1 (map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H' ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H' ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_store_ubx.hyps
          by (auto intro: Sinca.step_store dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_store_ubx.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.StoreUbx
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H' ?st2')"
          using step_store_ubx.prems rel_F1_F2
          by (auto intro: match.intros)
      qed
    next
      case (step_op op ar \<Sigma>2' x)
      let ?st1' = "Frame f l (Suc pc) R1 (x # drop ar (map Subx.norm_unboxed \<Sigma>2)) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op.hyps
          by (auto simp: take_map ap_map_list_cast_Dyn_to_map_norm[symmetric]
              intro!: Sinca.step_op dest!: next_instr2)
      next
        have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
          using step_op.hyps rel_stacktraces_Cons
          by (auto simp: take_Suc_conv_app_nth drop_map map_eq_append_map_drop
              simp: ap_map_list_cast_Dyn_map_typeof_replicate_conv
              intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Op
              dest!: next_instrD instr_atD)
        thus "?MATCH ?s1' (State F2 H ?st2')"
          using step_op.prems rel_F1_F2
          by (auto intro: match.intros)
      qed
    next
      case (step_op_inl op ar \<Sigma>2' opinl x F2')
      let ?F1' = "Sinca.Fenv.map_entry F1 f (\<lambda>fd. rewrite_fundef_body fd l pc (Inca.IOpInl opinl))"
      let ?st1' = "Frame f l (Suc pc) R1 (x # drop ar (map Subx.norm_unboxed  \<Sigma>2)) # st1"
      let ?s1' = "State ?F1' H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2' H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op_inl.hyps
          by (auto simp: take_map ap_map_list_cast_Dyn_to_map_norm[symmetric]
              intro!: Sinca.step_op_inl dest!: next_instr2)
      next
        show "?MATCH ?s1' (State F2' H ?st2')"
          using step_op_inl.prems
        proof (rule match.intros)
          show "rel_fundefs (Finca_get ?F1') (Fubx_get F2')"
            unfolding step_op_inl.hyps
            using rel_F1_F2
            by (auto intro: rel_fundefs_rewriteI)
        next
          let ?fd2' = "rewrite_fundef_body fd2 l pc (Ubx.instr.IOpInl opinl)"
          let ?instrs' = "instrs[pc := Ubx.instr.IOpInl opinl]"
          show "rel_stacktraces (Fubx_get F2') None ?st1' ?st2'"
          proof (rule rel_stacktraces.intros)
            show "rel_stacktraces (Fubx_get F2') (Some f) st1 st2"
              using step_op_inl.hyps rel_st1_st2 Sinca.\<II>\<nn>\<ll>_invertible
              by (auto simp: Subx.sp_instr_Op_OpInl_conv
                  intro: rel_stacktraces_map_entry_rewrite_fundef_body)
          next
            show "Fubx_get F2' f = Some ?fd2'"
              unfolding step_op_inl.hyps
              using F2_f by simp
          next
            show "map_of (body ?fd2') l = Some ?instrs'"
              using map_of_fd2_l by simp
          next
            show "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2')
              (return (rewrite_fundef_body fd2 l pc (Ubx.instr.IOpInl opinl)))
              (take (Suc pc) ?instrs') [] (map typeof (OpDyn x # drop ar \<Sigma>2))"
            using rel_stacktraces_Cons step_op_inl.hyps
            by (auto simp add: take_Suc_conv_app_nth Subx.Fenv.map_option_comp_map_entry
                map_eq_append_map_drop ap_map_list_cast_Dyn_map_typeof_replicate_conv
                Sinca.\<II>\<nn>\<ll>_invertible
                intro!: sp_instrs_prefix' Subx.sp_instr.OpInl
                dest!: next_instrD instr_atD)
          qed (insert all_dyn_R2 R1_def, simp_all add: drop_map)
        qed
      qed
    next
      case (step_op_inl_hit opinl ar \<Sigma>2' x)
      let ?st1' = "Frame f l (Suc pc) R1 (x # drop ar (map Subx.norm_unboxed \<Sigma>2)) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op_inl_hit.hyps
          by (auto simp: take_map ap_map_list_cast_Dyn_to_map_norm[symmetric]
              intro!: Sinca.step_op_inl_hit dest!: next_instr2)
      next
        show "?MATCH ?s1' (State F2 H ?st2')"
          using step_op_inl_hit.prems rel_F1_F2
        proof (rule match.intros)
          show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
            using step_op_inl_hit.hyps rel_stacktraces_Cons
            by (auto simp: take_Suc_conv_app_nth drop_map map_eq_append_map_drop
                simp: ap_map_list_cast_Dyn_map_typeof_replicate_conv
                intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.OpInl
                dest!: next_instrD instr_atD)
        qed
      qed
    next
      case (step_op_inl_miss opinl ar \<Sigma>2' x F2')
      let ?F1' = "Sinca.Fenv.map_entry F1 f (\<lambda>fd. rewrite_fundef_body fd l pc (Inca.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl)))"
      let ?st1' = "Frame f l (Suc pc) R1 (x # drop ar (map Subx.norm_unboxed  \<Sigma>2)) # st1"
      let ?s1' = "State ?F1' H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2' H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op_inl_miss.hyps
          by (auto simp: take_map ap_map_list_cast_Dyn_to_map_norm[symmetric]
              intro!: Sinca.step_op_inl_miss dest!: next_instr2)
      next
        show "?MATCH ?s1' (State F2' H ?st2')"
          using step_op_inl_miss.prems
        proof (rule match.intros)
          show "rel_fundefs (Finca_get ?F1') (Fubx_get F2')"
            unfolding step_op_inl_miss.hyps
            using rel_F1_F2
            by (auto intro: rel_fundefs_rewriteI)
        next
          let ?fd2' = "rewrite_fundef_body fd2 l pc (Ubx.instr.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl))"
          let ?instrs' = "instrs[pc := Ubx.instr.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl)]"
          show "rel_stacktraces (Fubx_get F2') None ?st1' ?st2'"
          proof (rule rel_stacktraces.intros)
            show "rel_stacktraces (Fubx_get F2') (Some f) st1 st2"
              using step_op_inl_miss.hyps rel_st1_st2 Sinca.\<II>\<nn>\<ll>_invertible
              by (auto intro: rel_stacktraces_map_entry_rewrite_fundef_body
                  Subx.sp_instr_Op_OpInl_conv[OF refl, symmetric])
          next
            show "Fubx_get F2' f = Some ?fd2'"
              unfolding step_op_inl_miss.hyps
              using F2_f by simp
          next
            show "map_of (body ?fd2') l = Some ?instrs'"
              using map_of_fd2_l by simp
          next
            show "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2')
              (return (rewrite_fundef_body fd2 l pc (Ubx.instr.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl))))
              (take (Suc pc) ?instrs') [] (map typeof (OpDyn x # drop ar \<Sigma>2))"
            using rel_stacktraces_Cons step_op_inl_miss.hyps
            by (auto simp add: take_Suc_conv_app_nth Subx.Fenv.map_option_comp_map_entry
                map_eq_append_map_drop ap_map_list_cast_Dyn_map_typeof_replicate_conv
                Sinca.\<II>\<nn>\<ll>_invertible
                intro!: sp_instrs_prefix' Subx.sp_instr.Op
                dest!: next_instrD instr_atD)
          qed (insert all_dyn_R2 R1_def, simp_all add: drop_map)
        qed
      qed
    next
      case (step_op_ubx opubx op ar x)
      let ?st1' = "Frame f l (Suc pc) R1 (Subx.norm_unboxed x # drop ar (map Subx.norm_unboxed \<Sigma>2)) # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op_ubx.hyps
          by (auto simp: take_map
              intro!: Sinca.step_op_inl_hit
              intro: Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_to_\<II>\<nn>\<ll>[THEN Sinca.\<II>\<nn>\<ll>_\<II>\<ss>\<II>\<nn>\<ll>] Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_correct
              dest: next_instr2)
      next
        show "?MATCH ?s1' (State F2 H ?st2')"
          using step_op_ubx.prems rel_F1_F2
        proof (rule match.intros)
          show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
            using step_op_ubx.hyps rel_stacktraces_Cons
            by (auto simp: take_Suc_conv_app_nth drop_map map_eq_append_map_drop
                intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.OpUbx
                dest!: next_instrD instr_atD
                dest!: Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_complete)
        qed
      qed
    next
      case (step_cjump l\<^sub>t l\<^sub>f x d l' \<Sigma>2')
      hence "instr_at fd2 l pc = Some (Ubx.instr.ICJump l\<^sub>t l\<^sub>f)"
        using F2_f by (auto dest!: next_instrD)
      hence pc_in_dom: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = Ubx.instr.ICJump l\<^sub>t l\<^sub>f"
        using map_of_fd2_l by (auto dest!: instr_atD)
      hence "{l\<^sub>t, l\<^sub>f} \<subseteq> fst ` set (body fd2)"
        using all_jumps_in_range by (auto simp: list_all_length)
      moreover have "l' \<in> {l\<^sub>t, l\<^sub>f}"
        using step_cjump.hyps by auto
      ultimately have "l' \<in> fst ` set (body fd2)"
        by blast
      then obtain instrs' where map_of_l': "map_of (body fd2) l' = Some instrs'"
        by (auto dest: weak_map_of_SomeI)

      have pc_def: "pc = length instrs - 1"
        using is_jump_nthD[OF _ pc_in_dom] nth_instrs_pc by simp
      have \<Sigma>2'_eq_Nil: "\<Sigma>2' = []"
        using sp_instr_last[OF pc_def] step_cjump.hyps
        by (auto simp: nth_instrs_pc elim!: Subx.sp_instr.cases)

      let ?st1' = "Frame f l' 0 R1 (map Subx.norm_unboxed \<Sigma>2') # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_cjump.hyps
          by (auto intro!: Sinca.step_cjump dest: next_instr2)
      next
        show "?MATCH ?s1' (State F2 H ?st2')"
          using step_cjump.prems rel_F1_F2
        proof (rule match.intros)
          show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
            using map_of_l' rel_stacktraces_Cons(1,3-5)
            by (auto simp: \<Sigma>2'_eq_Nil intro!: rel_stacktraces.intros intro: Subx.sp_instrs.Nil)
        qed
      qed
    next
      case (step_call g gd2 frame\<^sub>g)
      then obtain gd1 where
        F1_g: "Finca_get F1 g = Some gd1" and rel_gd1_gd2: "rel_fundef (=) norm_eq gd1 gd2"
        using rel_fundefs_Some2[OF rel_F1_F2] by auto
                
      have wf_gd2: "Subx.wf_fundef (map_option funtype \<circ> Fubx_get F2) gd2"
        using Subx.wf_fundefs_getD[OF wf_F2] step_call.hyps by simp

      obtain intrs\<^sub>g where gd2_fst_bblock: "map_of (body gd2) (fst (hd (body gd2))) = Some intrs\<^sub>g"
        using Subx.wf_fundef_body_neq_NilD[OF wf_gd2]
        by (metis hd_in_set map_of_eq_None_iff not_Some_eq prod.collapse prod_in_set_fst_image_conv)

      let ?frame\<^sub>g = "allocate_frame g gd1 (take (arity gd1) \<Sigma>1) uninitialized"
      let ?st1' = "?frame\<^sub>g # Frame f l pc R1 \<Sigma>1 # st1"
      let ?s1' = "State F1 H ?st1'"
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
      proof (intro exI conjI)
        show "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_call.hyps F1_g rel_gd1_gd2
          by (auto simp: rel_fundef_arities intro!: Sinca.step_call dest: next_instr2)
      next
        show "?MATCH ?s1' (State F2 H ?st2')"
          using step_call.prems rel_F1_F2
        proof (rule match.intros)
          have FOO: "fst (hd (body gd1)) = fst (hd (body gd2))"
            apply (rule rel_fundef_rel_fst_hd_bodies[OF rel_gd1_gd2])
            using Subx.wf_fundefs_getD[OF wf_F2 \<open>Fubx_get F2 g = Some gd2\<close>]
            by (auto dest: Subx.wf_fundef_body_neq_NilD)
          show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
            unfolding step_call allocate_frame_def FOO
          proof (rule rel_stacktraces.intros(2))
            show "rel_stacktraces (Fubx_get F2) (Some g)
              (Frame f l pc R1 \<Sigma>1 # st1) (Frame f l pc R2 \<Sigma>2 # st2)"
              using step_call rel_stacktraces_Cons
              by (auto simp: is_valid_fun_call_def intro: rel_stacktraces.intros)
          next
            show "take (arity gd1) \<Sigma>1 @ replicate (fundef_locals gd1) uninitialized =
              map Subx.norm_unboxed (take (arity gd2) \<Sigma>2 @
              replicate (fundef_locals gd2) (OpDyn uninitialized))"
              using rel_gd1_gd2
              by (simp add: rel_fundef_arities rel_fundef_locals take_map \<Sigma>1_def)
          next
            show "list_all is_dyn_operand (take (arity gd2) \<Sigma>2 @
              replicate (fundef_locals gd2) (OpDyn uninitialized))"
              using step_call.hyps by auto
          qed (insert step_call gd2_fst_bblock, simp_all add: Subx.sp_instrs.Nil)
        qed
      qed
    next
      case (step_return fd2' \<Sigma>2\<^sub>g frame\<^sub>g' g l\<^sub>g pc\<^sub>g R2\<^sub>g st2')
      hence fd2_fd2'[simp]: "fd2' = fd2"
        using F2_f by simp
      then obtain fd1 where
        F1_f: "Finca_get F1 f = Some fd1" and rel_fd1_fd2: "rel_fundef (=) norm_eq fd1 fd2"
        using F2_f rel_fundefs_Some2[OF rel_F1_F2] by auto
      show ?case
        using rel_st1_st2 unfolding \<open>Frame g l\<^sub>g pc\<^sub>g R2\<^sub>g \<Sigma>2\<^sub>g # st2' = st2\<close>[symmetric]
      proof (cases rule: rel_stacktraces.cases)
        case (rel_stacktraces_Cons st1' \<Sigma>1\<^sub>g R1\<^sub>g gd2 instrs)
        hence is_valid_call_f: "is_valid_fun_call (Fubx_get F2) g l\<^sub>g pc\<^sub>g \<Sigma>2\<^sub>g f"
          by simp
        let ?s1' = "State F1 H (Frame g l\<^sub>g (Suc pc\<^sub>g) R1\<^sub>g (\<Sigma>1 @ drop (arity fd2) \<Sigma>1\<^sub>g) # st1')"
        show ?thesis (is "\<exists>x. ?STEP x \<and> ?MATCH x (State F2 H ?st2')")
        proof (intro exI conjI)
          show "?STEP ?s1'"
            unfolding rel_stacktraces_Cons
          proof (rule Sinca.step.step_return)
            show "next_instr (Finca_get F1) f l pc = Some Inca.instr.IReturn"
              using \<open>next_instr (Fubx_get F2) f l pc = Some Ubx.instr.IReturn\<close>
              using rel_fundefs_next_instr2[OF rel_F1_F2]
              by force
          next
            show "Finca_get F1 f = Some fd1"
              by (rule F1_f)
          qed (insert step_return.hyps rel_fd1_fd2,
              simp_all add: \<Sigma>1_def rel_fundef_arities rel_fundef_return)
        next
          show "?MATCH ?s1' (State F2 H ?st2')"
            unfolding step_return.hyps
          proof (rule match.intros)
            have "next_instr (Fubx_get F2) g l\<^sub>g pc\<^sub>g = Some (Ubx.instr.ICall f)" and
              "arity fd2 \<le> length \<Sigma>2\<^sub>g" and "list_all is_dyn_operand (take (arity fd2) \<Sigma>2\<^sub>g)"
              using is_valid_call_f[unfolded is_valid_fun_call_def] F2_f
              by simp_all
            hence
              pc\<^sub>g_in_range: "pc\<^sub>g < length instrs" and
              nth_instrs_pc\<^sub>g: "instrs ! pc\<^sub>g = Ubx.instr.ICall f"
              using rel_stacktraces_Cons
              by (auto dest!: next_instrD instr_atD)
            have replicate_None: "replicate (arity fd2) None = map typeof (take (arity fd2) \<Sigma>2\<^sub>g)"
              using \<open>arity fd2 \<le> length \<Sigma>2\<^sub>g\<close> \<open>list_all is_dyn_operand (take (arity fd2) \<Sigma>2\<^sub>g)\<close>
              by (auto simp: is_dyn_operand_eq_typeof list_all_iff intro!: replicate_eq_map)
            show "rel_stacktraces (Fubx_get F2) None
             (Frame g l\<^sub>g (Suc pc\<^sub>g) R1\<^sub>g (\<Sigma>1 @ drop (arity fd2) \<Sigma>1\<^sub>g) # st1')
             (Frame g l\<^sub>g (Suc pc\<^sub>g) R2\<^sub>g (\<Sigma>2 @ drop (arity fd2') \<Sigma>2\<^sub>g) # st2')"
              using rel_stacktraces_Cons
              apply (auto simp: \<Sigma>1_def drop_map take_Suc_conv_app_nth[OF pc\<^sub>g_in_range] nth_instrs_pc\<^sub>g
                  intro!: rel_stacktraces.intros elim!: Subx.sp_instrs_appendI)
              apply (rule Subx.sp_instr.Call[of _ _ _ _ _ "map typeof (drop (arity fd2) \<Sigma>2\<^sub>g)"])
                apply (simp add: F2_f funtype_def)
               apply (simp add: replicate_None map_append[symmetric])
              using \<open>length \<Sigma>2 = return fd2'\<close> \<open>list_all is_dyn_operand \<Sigma>2\<close>
              by (auto simp: list.pred_set intro: replicate_eq_map[symmetric])
          qed (insert step_return rel_F1_F2, simp_all)
        qed
      qed
    qed
  qed
qed

lemma match_final_backward:
  assumes "match s1 s2" and final_s2: "final Fubx_get Ubx.IReturn s2"
  shows "final Finca_get Inca.IReturn s1"
  using \<open>match s1 s2\<close>
proof (cases s1 s2 rule: match.cases)
  case (matchI F2 H st2 F1 st1)
  show ?thesis
    using final_s2[unfolded matchI]
  proof (cases _ _ "State F2 H st2" rule: final.cases)
    case (finalI f l pc R \<Sigma>)
    then show ?thesis
      using matchI
      by (auto intro!: final.intros elim!: rel_stacktraces.cases dest: rel_fundefs_next_instr2)
  qed
qed

sublocale inca_to_ubx_simulation:
  backward_simulation Sinca.step Subx.step
    "final Finca_get Inca.IReturn"
    "final Fubx_get Ubx.IReturn"
    "\<lambda>_ _. False" "\<lambda>_. match"
  using match_final_backward backward_lockstep_simulation
   lockstep_to_plus_backward_simulation[of match Subx.step Sinca.step]
  by unfold_locales auto


section \<open>Forward simulation\<close>

lemma ap_map_list_cast_Dyn_eq_norm_stack:
  assumes "list_all (\<lambda>x. x = None) (map typeof xs)"
  shows "ap_map_list cast_Dyn xs = Some (map Subx.norm_unboxed xs)"
  using assms
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons.prems have
    typeof_x: "typeof x = None" and
    typeof_xs: "list_all (\<lambda>x. x = None) (map typeof xs)"
    by simp_all
  obtain x' where "x = OpDyn x'"
    using typeof_unboxed_inversion(1)[OF typeof_x] by auto
  then show ?case
    using Cons.IH[OF typeof_xs]
    by simp
qed

lemma forward_lockstep_simulation:
  assumes "match s1 s2" and "Sinca.step s1 s1'"
  shows "\<exists>s2'. Subx.step s2 s2' \<and> match s1' s2'"
  using assms(1)
proof (cases s1 s2 rule: match.cases)
  case (matchI F2 H st2 F1 st1)
  have s2_def: "s2 = Global.state.State F2 H st2" using matchI by simp
  have rel_F1_F2: "rel_fundefs (Finca_get F1) (Fubx_get F2)" using matchI by simp
  have wf_s2: "Subx.wf_state s2" using matchI by simp
  hence wf_F2: "Subx.wf_fundefs (Fubx_get F2)" by (auto simp: s2_def dest: Subx.wf_stateD)

  note wf_s2'I = Subx.wf_state_step_preservation[OF wf_s2]

  from \<open>rel_stacktraces (Fubx_get F2) None st1 st2\<close> show ?thesis
  proof (cases "Fubx_get F2" "None :: 'fun option" st1 st2 rule: rel_stacktraces.cases)
    case rel_stacktraces_Nil
    with matchI assms(2) show ?thesis by (auto elim: Sinca.step.cases)
  next
    case (rel_stacktraces_Cons f st1' st2' \<Sigma>1 \<Sigma>2 R1 R2 fd2 l instrs pc)
    have rel_st1'_st2': "rel_stacktraces (Fubx_get F2) (Some f) st1' st2'"
      using rel_stacktraces_Cons by simp
    have st2_def: "st2 = Frame f l pc R2 \<Sigma>2 # st2'" using rel_stacktraces_Cons by simp
    have \<Sigma>1_def: "\<Sigma>1 = map Subx.norm_unboxed \<Sigma>2" using rel_stacktraces_Cons by simp
    have all_dyn_R2: "list_all is_dyn_operand R2" using rel_stacktraces_Cons by simp
    have F2_f: "Fubx_get F2 f = Some fd2" using rel_stacktraces_Cons by simp
    have map_of_fd2_l: "map_of (body fd2) l = Some instrs" using rel_stacktraces_Cons by simp
    have sp_instrs_prefix: "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2)
      (take pc instrs) [] (map typeof \<Sigma>2)"
      using rel_stacktraces_Cons by simp
    note sp_instrs_prefix' =
      Subx.sp_instrs_singletonI[THEN Subx.sp_instrs_appendI[OF sp_instrs_prefix]]

    have wf_fd2: "Subx.wf_fundef (map_option funtype \<circ> Fubx_get F2) fd2"
      using wf_F2 F2_f by (auto dest: Subx.wf_fundefs_getD)
    hence sp_instrs_instrs:
      "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2) instrs [] []"
      using wf_fd2[THEN Subx.wf_fundef_all_wf_basic_blockD] map_of_fd2_l
      by (auto dest: list_all_map_of_SomeD[OF _ map_of_fd2_l] dest: Subx.wf_basic_blockD)
    hence sp_instrs_sufix: "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2)
      (instrs ! pc # drop (Suc pc) instrs) (map typeof \<Sigma>2) []" if "pc < length instrs"
      using that Subx.sp_instrs_appendD'[OF _ sp_instrs_prefix]
      by (simp add: Cons_nth_drop_Suc)

    have
      instrs_neq_Nil: "instrs \<noteq> []" and
      all_jumps_in_range: "list_all (Subx.jump_in_range (fst ` set (body fd2))) instrs" and
      sp_instrs_instrs: "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2) instrs [] []"
      using list_all_map_of_SomeD[OF wf_fd2[THEN Subx.wf_fundef_all_wf_basic_blockD] map_of_fd2_l]
      by (auto dest: Subx.wf_basic_blockD)

    from assms(2)[unfolded matchI rel_stacktraces_Cons] show ?thesis
    proof (induction "State F1 H (Frame f l pc (map Subx.norm_unboxed R2) (map Subx.norm_unboxed \<Sigma>2) # st1')" s1' rule: Sinca.step.induct)
      case (step_push d)
      then obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.IPush d) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      then show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (IPush d2)
        let ?st2' = "Frame f l (Suc pc) R2 (OpDyn d # \<Sigma>2) # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using next_instr2 norm_eq_instr1_instr2
            unfolding IPush
            by (auto simp: s2_def st2_def intro: Subx.step_push)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding IPush
              by (auto simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' intro: Subx.sp_instr.Push)
          qed (simp_all add: rel_F1_F2)
        qed
      next
        case (IPushUbx1 u)
        let ?st2' = "Frame f l (Suc pc) R2 (OpUbx1 u # \<Sigma>2) # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using next_instr2 norm_eq_instr1_instr2
            unfolding IPushUbx1
            by (auto simp: s2_def st2_def intro: Subx.step_push_ubx1)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 norm_eq_instr1_instr2 rel_stacktraces_Cons
              unfolding IPushUbx1
              by (auto simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' intro: Subx.sp_instr.PushUbx1)
          qed (simp_all add: rel_F1_F2)
        qed
      next
        case (IPushUbx2 u)
        let ?st2' = "Frame f l (Suc pc) R2 (OpUbx2 u # \<Sigma>2) # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using next_instr2 norm_eq_instr1_instr2
            unfolding IPushUbx2
            by (auto simp: s2_def st2_def intro: Subx.step_push_ubx2)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 norm_eq_instr1_instr2 rel_stacktraces_Cons
              unfolding IPushUbx2
              by (auto simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' intro: Subx.sp_instr.PushUbx2)
          qed (simp_all add: rel_F1_F2)
        qed
      qed simp_all
    next
      case (step_pop d \<Sigma>1')
      then obtain u \<Sigma>2' where
        \<Sigma>2_def: "\<Sigma>2 = u # \<Sigma>2'" and "d = Subx.norm_unboxed u" and
        \<Sigma>1'_def: "\<Sigma>1' = map Subx.norm_unboxed \<Sigma>2'"
        by auto
      from step_pop obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq Inca.IPop instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      then show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case IPop
        let ?st2' = "Frame f l (Suc pc) R2 \<Sigma>2' # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using next_instr2 norm_eq_instr1_instr2
            unfolding IPop
            by (auto simp: s2_def st2_def \<Sigma>2_def intro: Subx.step_pop)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding IPop
              by (auto simp: \<Sigma>2_def \<Sigma>1'_def next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Pop)
          qed (simp_all add: rel_F1_F2)
        qed
      qed simp_all
    next
      case (step_get n d)
      hence nth_R2_n: "R2 ! n = OpDyn d"
        using all_dyn_R2
        by (metis Subx.norm_unboxed.simps(1) is_dyn_operand_def length_map list_all_length nth_map)
      from step_get obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.IGet n) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      then show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (IGet n')
        hence "n' = n" using norm_eq_instr1_instr2 by simp
        let ?st2' = "Frame f l (Suc pc) R2 (OpDyn d # \<Sigma>2) # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using step_get nth_R2_n
            using next_instr2 norm_eq_instr1_instr2
            unfolding IGet
            by (auto simp: s2_def st2_def intro: Subx.step_get)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding IGet
              by (auto simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' intro: Subx.sp_instr.Get)
          qed (simp_all add: rel_F1_F2)
        qed
      next
        case (IGetUbx \<tau> n')
        hence "n' = n" using norm_eq_instr1_instr2 by simp
        show ?thesis
        proof (cases "Subx.unbox \<tau> d")
          case None
          let ?F2' = "Subx.Fenv.map_entry F2 f Subx.generalize_fundef"
          let ?st2' = "Subx.box_stack f (Frame f l (Suc pc) R2 (OpDyn d # \<Sigma>2) # st2')"
          let ?s2' = "State ?F2' H ?st2'"
          show ?thesis
          proof (intro exI conjI)
            show "?STEP ?s2'"
              using step_get nth_R2_n None
              using next_instr2 norm_eq_instr1_instr2
              unfolding IGetUbx
              by (auto simp: s2_def st2_def intro: Subx.step_get_ubx_miss[simplified])
          next
            show "?MATCH (State F1 H ?st1') ?s2'"
            proof (rule match.intros)
              show "Subx.wf_state ?s2'"
                using wf_F2
                by (auto intro!: Subx.wf_stateI intro: Subx.wf_fundefs_generalize)
            next
              show "rel_fundefs (Finca_get F1) (Fubx_get ?F2')"
                using rel_F1_F2
                by (auto intro: rel_fundefs_generalizeI)
            next
              have sp_instrs_gen: "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2)
                (take (Suc pc) (map Subx.generalize_instr instrs)) [] (map Map.empty (OpDyn d # \<Sigma>2))"
                using rel_stacktraces_Cons step_get.hyps
                using IGetUbx \<open>n' = n\<close>
                using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
                by (auto simp: take_Suc_conv_app_nth take_map
                    intro!: Subx.sp_instrs_appendI
                    intro: Subx.sp_instrs_generalize0 Subx.sp_instr.Get)
              then show "rel_stacktraces (Fubx_get ?F2') None ?st1' ?st2'"
                apply simp
              proof (rule rel_stacktraces.intros)
                show "rel_stacktraces (Fubx_get ?F2') (Some f) st1' (Subx.box_stack f st2')"
                  using rel_st1'_st2' rel_stacktraces_map_entry_gneralize_fundefI by simp
              next
                show "Fubx_get ?F2' f = Some (Subx.generalize_fundef fd2)"
                  using F2_f by simp
              next
                show "map_of (body (Subx.generalize_fundef fd2)) l =
                  Some (map Subx.generalize_instr instrs)"
                  using map_of_fd2_l by (simp add: Subx.map_of_generalize_fundef_conv)
              qed (insert all_dyn_R2 map_of_fd2_l, simp_all add: Subx.map_of_generalize_fundef_conv)
            qed
          qed
        next
          case (Some u)
          let ?st2' = "Frame f l (Suc pc) R2 (u # \<Sigma>2) # st2'"
          let ?s2' = "State F2 H ?st2'"
          show ?thesis
          proof (intro exI conjI)
            show "?STEP ?s2'"
              using step_get nth_R2_n Some
              using next_instr2 norm_eq_instr1_instr2
              unfolding IGetUbx
              by (auto simp: s2_def st2_def intro: Subx.step_get_ubx_hit)
          next
            show "?MATCH (State F1 H ?st1') ?s2'"
            proof (rule match.intros)
              show "Subx.wf_state ?s2'"
                using wf_F2 by (auto intro: Subx.wf_stateI)
            next
              show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
                using next_instr2 rel_stacktraces_Cons
                using Some
                unfolding IGetUbx
                by (auto simp: next_instr_take_Suc_conv
                    intro!: rel_stacktraces.intros sp_instrs_prefix' intro: Subx.sp_instr.GetUbx)
            qed (simp_all add: rel_F1_F2)
          qed
        qed
      qed simp_all
    next
      case (step_set n R1' d \<Sigma>1')
      then obtain u \<Sigma>2' where
        \<Sigma>2_def: "\<Sigma>2 = u # \<Sigma>2'" and d_def: "d = Subx.norm_unboxed u" and
        \<Sigma>1'_def: "\<Sigma>1' = map Subx.norm_unboxed \<Sigma>2'"
        by auto
      from step_set obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.ISet n) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all
      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (ISet n')
        hence "n' = n" using norm_eq_instr1_instr2 by simp
        have typeof_u: "typeof u = None"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc ISet, simplified]
          by (auto simp: \<Sigma>2_def elim: Subx.sp_instrs.cases Subx.sp_instr.cases)
        hence cast_Dyn_u: "cast_Dyn u = Some d"
          by (auto simp add: d_def dest: Subx.typeof_and_norm_unboxed_imp_cast_Dyn)
        let ?R2' = "R2[n := OpDyn d]"
        let ?st2' = "Frame f l (Suc pc) ?R2' \<Sigma>2' # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using step_set.hyps cast_Dyn_u
            using next_instr2 norm_eq_instr1_instr2
            unfolding ISet
            by (auto simp: s2_def st2_def \<Sigma>2_def intro: Subx.step_set)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding ISet
              using step_set.hyps cast_Dyn_u
              by (auto simp: \<Sigma>1'_def \<Sigma>2_def map_update next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Set
                  intro: list_all_list_updateI)
          qed (simp_all add: rel_F1_F2)
        qed
      next
        case (ISetUbx \<tau> n')
        hence "n' = n" using norm_eq_instr1_instr2 by simp
        have typeof_u: "typeof u = Some \<tau>"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc ISetUbx, simplified]
          by (auto simp: \<Sigma>2_def elim: Subx.sp_instrs.cases Subx.sp_instr.cases)
        hence cast_and_box_u: "Subx.cast_and_box \<tau> u = Some d"
          by (auto simp add: d_def dest: Subx.typeof_and_norm_unboxed_imp_cast_and_box)
        let ?R2' = "R2[n := OpDyn d]"
        let ?st2' = "Frame f l (Suc pc) ?R2' \<Sigma>2' # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using step_set cast_and_box_u
            using next_instr2 norm_eq_instr1_instr2
            unfolding ISetUbx
            by (auto simp: s2_def st2_def \<Sigma>2_def intro: Subx.step_set_ubx)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding ISetUbx
              using step_set.hyps cast_and_box_u
              by (auto simp: \<Sigma>1'_def \<Sigma>2_def map_update next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.SetUbx
                  intro: list_all_list_updateI)
          qed (simp_all add: rel_F1_F2)
        qed
      qed simp_all
    next
      case (step_load x y d \<Sigma>1')
      then obtain u \<Sigma>2' where
        \<Sigma>2_def: "\<Sigma>2 = u # \<Sigma>2'" and d_def: "y = Subx.norm_unboxed u" and
        \<Sigma>1'_def: "\<Sigma>1' = map Subx.norm_unboxed \<Sigma>2'"
        by auto
      from step_load obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.ILoad x) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all
      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (ILoad x')
        hence "x' = x" using norm_eq_instr1_instr2 by simp
        have typeof_u: "typeof u = None"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc ILoad, simplified]
          by (auto simp: \<Sigma>2_def elim: Subx.sp_instrs.cases Subx.sp_instr.cases)
        hence cast_Dyn_u: "cast_Dyn u = Some y"
          by (auto simp add: d_def dest: Subx.typeof_and_norm_unboxed_imp_cast_Dyn)
        let ?st2' = "Frame f l (Suc pc) R2 (OpDyn d # \<Sigma>2') # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using step_load.hyps cast_Dyn_u next_instr2
            unfolding ILoad \<open>x' = x\<close>
            by (auto simp: s2_def st2_def \<Sigma>2_def intro: Subx.step_load)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding ILoad \<open>x' = x\<close>
              using step_load.hyps cast_Dyn_u
              by (auto simp: \<Sigma>1'_def \<Sigma>2_def map_update next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Load
                  intro: list_all_list_updateI)
          qed (simp_all add: rel_F1_F2)
        qed
      next
        case (ILoadUbx \<tau> x')
        hence "x' = x" using norm_eq_instr1_instr2 by simp
        have typeof_u: "typeof u = None"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc ILoadUbx, simplified]
          by (auto simp: \<Sigma>2_def elim: Subx.sp_instrs.cases Subx.sp_instr.cases)
        hence cast_Dyn_u: "cast_Dyn u = Some y"
          by (auto simp add: d_def dest: Subx.typeof_and_norm_unboxed_imp_cast_Dyn)
        show ?thesis
        proof (cases "Subx.unbox \<tau> d")
          case None
          let ?F2' = "Subx.Fenv.map_entry F2 f Subx.generalize_fundef"
          let ?st2' = "Subx.box_stack f (Frame f l (Suc pc) R2 (OpDyn d # \<Sigma>2') # st2')"
          let ?s2' = "State ?F2' H ?st2'"
          show ?thesis
          proof (intro exI conjI)
            show "?STEP ?s2'"
              using step_load.hyps next_instr2 cast_Dyn_u None 
              unfolding ILoadUbx \<open>x' = x\<close>
              by (auto simp add: s2_def st2_def \<Sigma>2_def intro: Subx.step_load_ubx_miss[simplified])
          next
            show "?MATCH (State F1 H ?st1') ?s2'"
            proof (rule match.intros)
              show "Subx.wf_state ?s2'"
                using wf_F2
                by (auto intro!: Subx.wf_stateI intro: Subx.wf_fundefs_generalize)
            next
              show "rel_fundefs (Finca_get F1) (Fubx_get ?F2')"
                using rel_F1_F2
                by (auto intro: rel_fundefs_generalizeI)
            next
              have "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2)
                (take (Suc pc) (map Subx.generalize_instr instrs)) [] (None # map Map.empty \<Sigma>2')"
                using rel_stacktraces_Cons step_load.hyps
                using pc_in_range nth_instrs_pc
                using ILoadUbx \<open>x' = x\<close>
                by (auto simp: \<Sigma>2_def take_Suc_conv_app_nth take_map
                    intro!: Subx.sp_instrs_appendI
                    intro: Subx.sp_instrs_generalize0 Subx.sp_instr.Load)
              thus "rel_stacktraces (Fubx_get ?F2') None ?st1' ?st2'"
                apply simp
              proof (rule rel_stacktraces.intros)
                show "Fubx_get ?F2' f = Some (Subx.generalize_fundef fd2)"
                  using F2_f by simp
              next
                show "map_of (body (Subx.generalize_fundef fd2)) l =
                  Some (map Subx.generalize_instr instrs)"
                  using map_of_fd2_l
                  by (simp add: Subx.map_of_generalize_fundef_conv)
              qed (insert rel_F1_F2 all_dyn_R2 F2_f map_of_fd2_l rel_st1'_st2', auto simp: \<Sigma>1'_def)
            qed
          qed
        next
          case (Some u2)
          let ?st2' = "Frame f l (Suc pc) R2 (u2 # \<Sigma>2') # st2'"
          let ?s2' = "State F2 H ?st2'"
          show ?thesis
          proof (intro exI conjI)
            show "?STEP ?s2'"
              using step_load.hyps next_instr2 cast_Dyn_u Some
              unfolding ILoadUbx \<open>x' = x\<close>
              by (auto simp add: s2_def st2_def \<Sigma>2_def intro: Subx.step_load_ubx_hit[simplified])
          next
            show "?MATCH (State F1 H ?st1') ?s2'"
            proof (rule match.intros)
              show "Subx.wf_state ?s2'"
                using wf_F2
                by (auto intro!: Subx.wf_stateI intro: Subx.wf_fundefs_generalize)
            next
              show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
                using next_instr2 rel_stacktraces_Cons
                using Some typeof_u
                unfolding ILoadUbx
                by (auto simp: \<Sigma>2_def \<Sigma>1'_def next_instr_take_Suc_conv
                    intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.LoadUbx)
            qed (insert rel_F1_F2, simp_all)
          qed
        qed
      qed simp_all
    next
      case (step_store x d1 d2 H' \<Sigma>1')
      then obtain u1 u2 \<Sigma>2' where
        \<Sigma>2_def: "\<Sigma>2 = u1 # u2 # \<Sigma>2'" and
        d1_def: "d1 = Subx.norm_unboxed u1" and
        d2_def: "d2 = Subx.norm_unboxed u2" and
        \<Sigma>1'_def: "\<Sigma>1' = map Subx.norm_unboxed \<Sigma>2'"
        by auto
      from step_store obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.instr.IStore x) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all
      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H' ?st1') x")
      proof (cases instr2)
        case (IStore x')
        hence "x' = x" using norm_eq_instr1_instr2 by simp
        have casts: "cast_Dyn u1 = Some d1" "cast_Dyn u2 = Some d2"
          unfolding atomize_conj
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IStore, simplified]
          by (auto simp: d1_def d2_def \<Sigma>2_def elim: Subx.sp_instrs.cases Subx.sp_instr.cases
              intro: Subx.typeof_and_norm_unboxed_imp_cast_Dyn)
        let ?st2' = "Frame f l (Suc pc) R2 \<Sigma>2' # st2'"
        let ?s2' = "State F2 H' ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using step_store.hyps casts next_instr2
            unfolding IStore \<open>x' = x\<close>
            by (auto simp: s2_def st2_def \<Sigma>2_def intro: Subx.step_store)
        next
          show "?MATCH (State F1 H' ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding IStore \<open>x' = x\<close>
              using step_store.hyps casts
              by (auto simp: \<Sigma>1'_def \<Sigma>2_def map_update next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Store
                  intro: list_all_list_updateI)
          qed (insert rel_F1_F2, simp_all)
        qed
      next
        case (IStoreUbx \<tau> x')
        hence "x' = x" using norm_eq_instr1_instr2 by simp
        have casts: "cast_Dyn u1 = Some d1" "Subx.cast_and_box \<tau> u2 = Some d2"
          unfolding atomize_conj
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IStoreUbx, simplified]
          by (auto simp: d1_def d2_def \<Sigma>2_def elim: Subx.sp_instrs.cases Subx.sp_instr.cases
              intro: Subx.typeof_and_norm_unboxed_imp_cast_Dyn
              intro: Subx.typeof_and_norm_unboxed_imp_cast_and_box)
        let ?st2' = "Frame f l (Suc pc) R2 \<Sigma>2' # st2'"
        let ?s2' = "State F2 H' ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using step_store.hyps casts next_instr2
            unfolding IStoreUbx \<open>x' = x\<close>
            by (auto simp: s2_def st2_def \<Sigma>2_def intro: Subx.step_store_ubx)
        next
          show "?MATCH (State F1 H' ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using next_instr2 rel_stacktraces_Cons
              unfolding IStoreUbx \<open>x' = x\<close>
              using step_store.hyps casts
              by (auto simp: \<Sigma>1'_def \<Sigma>2_def map_update next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.StoreUbx
                  intro: list_all_list_updateI)
          qed (insert rel_F1_F2, simp_all)
        qed
      qed simp_all
    next
      case (step_op op ar x)
      then obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.IOp op) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all
      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (IOp op')
        hence "op' = op" using norm_eq_instr1_instr2 by simp
        have casts:
          "ap_map_list cast_Dyn (take ar \<Sigma>2) = Some (take ar (map Subx.norm_unboxed \<Sigma>2))"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IOp, simplified]
          using step_op.hyps
          by (auto simp: \<open>op' = op\<close> take_map
              elim!: Subx.sp_instrs.cases[of _ _ "x # xs" for x xs, simplified] Subx.sp_instr.cases
              intro!: ap_map_list_cast_Dyn_eq_norm_stack[of "take (\<AA>\<rr>\<ii>\<tt>\<yy> op) \<Sigma>2"]
              dest!: map_eq_append_replicate_conv)
        let ?st2' = "Frame f l (Suc pc) R2 (OpDyn x # drop ar \<Sigma>2) # st2'"
        let ?s2' = "State F2 H ?st2'"
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'"
            using step_op.hyps casts next_instr2
            unfolding IOp \<open>op' = op\<close>
            by (auto simp: s2_def st2_def intro: Subx.step_op)
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              using wf_F2 by (auto intro: Subx.wf_stateI)
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using step_op.hyps casts next_instr2 rel_stacktraces_Cons
              unfolding IOp \<open>op' = op\<close>
              by (auto simp: min_absorb2 take_map[symmetric] drop_map[symmetric]
                  simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.Op
                  intro: list_all_list_updateI
                  dest!: ap_map_list_cast_Dyn_replicate[symmetric])
          qed (insert rel_F1_F2, simp_all)
        qed
      qed simp_all
    next
      case (step_op_inl op ar opinl x F1')
      then obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.IOp op) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all
      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1' H ?st1') x")
      proof (cases instr2)
        case (IOp op')
        hence "op' = op" using norm_eq_instr1_instr2 by simp
        have casts:
          "ap_map_list cast_Dyn (take ar \<Sigma>2) = Some (take ar (map Subx.norm_unboxed \<Sigma>2))"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IOp, simplified]
          using step_op_inl.hyps
          by (auto simp: \<open>op' = op\<close> take_map
              elim!: Subx.sp_instrs.cases[of _ _ "x # xs" for x xs, simplified] Subx.sp_instr.cases
              intro!: ap_map_list_cast_Dyn_eq_norm_stack[of "take (\<AA>\<rr>\<ii>\<tt>\<yy> op) \<Sigma>2"]
              dest!: map_eq_append_replicate_conv)
        let ?st2' = "Frame f l (Suc pc) R2 (OpDyn x # drop ar \<Sigma>2) # st2'"
        let ?F2' = "Subx.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc (Ubx.IOpInl opinl))"
        let ?s2' = "State ?F2' H ?st2'"
        have step_s2_s2': "?STEP ?s2'"
          using step_op_inl.hyps casts next_instr2
          unfolding IOp \<open>op' = op\<close>
          by (auto simp: s2_def st2_def intro: Subx.step_op_inl)
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'" by (rule step_s2_s2')
        next
          show "?MATCH (State F1' H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              by (rule Subx.wf_state_step_preservation[OF wf_s2 step_s2_s2'])
          next
            show "rel_fundefs (Finca_get F1') (Fubx_get ?F2')"
              using rel_F1_F2 step_op_inl
              by (auto intro: rel_fundefs_rewriteI)
          next
            have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using rel_st1'_st2'
              apply (rule rel_stacktraces.intros)
              using step_op_inl.hyps casts next_instr2 rel_stacktraces_Cons
              unfolding IOp \<open>op' = op\<close>
              by (auto simp: min_absorb2 take_map[symmetric] drop_map[symmetric]
                  simp: next_instr_take_Suc_conv
                  intro!: sp_instrs_prefix' Subx.sp_instr.Op
                  dest!: ap_map_list_cast_Dyn_replicate[symmetric])
            then show "rel_stacktraces (Fubx_get ?F2') None ?st1' ?st2'"
              apply (rule rel_stacktraces_map_entry_rewrite_fundef_body)
              apply (rule next_instr2)
              unfolding IOp \<open>op' = op\<close>
              using Sinca.\<II>\<nn>\<ll>_invertible Subx.sp_instr_Op_OpInl_conv step_op_inl.hyps(4) apply blast
               apply simp
              apply simp
              done
          qed
        qed
      qed simp_all
    next
      case (step_op_inl_hit opinl ar x)
      then obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.IOpInl opinl) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all
      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (IOpInl opinl')
        hence "opinl' = opinl" using norm_eq_instr1_instr2 by simp
        have casts:
          "ap_map_list cast_Dyn (take ar \<Sigma>2) = Some (take ar (map Subx.norm_unboxed \<Sigma>2))"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IOpInl, simplified]
          using step_op_inl_hit.hyps
          by (auto simp: \<open>opinl' = opinl\<close> take_map
              elim!: Subx.sp_instrs.cases[of _ _ "x # xs" for x xs, simplified] Subx.sp_instr.cases
              intro!: ap_map_list_cast_Dyn_eq_norm_stack[of "take (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) \<Sigma>2"]
              dest!: map_eq_append_replicate_conv)
        let ?st2' = "Frame f l (Suc pc) R2 (OpDyn x # drop ar \<Sigma>2) # st2'"
        let ?s2' = "State F2 H ?st2'"
        have step_s2_s2': "?STEP ?s2'"
          using step_op_inl_hit.hyps casts next_instr2
          unfolding IOpInl \<open>opinl' = opinl\<close>
          by (auto simp: s2_def st2_def intro: Subx.step_op_inl_hit)
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'" by (rule step_s2_s2')
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              by (rule Subx.wf_state_step_preservation[OF wf_s2 step_s2_s2'])
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using step_op_inl_hit.hyps casts next_instr2 rel_stacktraces_Cons
              unfolding IOpInl \<open>opinl' = opinl\<close>
              by (auto simp: min_absorb2 take_map[symmetric] drop_map[symmetric]
                  simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.OpInl
                  intro: list_all_list_updateI
                  dest!: ap_map_list_cast_Dyn_replicate[symmetric])
          qed (insert rel_F1_F2, simp_all)
        qed
      next
        case (IOpUbx opubx)
        hence "opinl = \<BB>\<oo>\<xx> opubx" using norm_eq_instr1_instr2 by simp
        let ?ar = "\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx))"

        obtain codom where typeof_opubx: "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx = (map typeof (take ?ar \<Sigma>2), codom)"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IOpUbx, simplified]
          by (cases "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx")
            (auto simp: eq_append_conv_conj Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy> take_map
              dest!: Subx.sp_instrs_ConsD elim!: Subx.sp_instr.cases)

        obtain u where
          eval_opubx: "\<UU>\<bb>\<xx>\<OO>\<pp> opubx (take ?ar \<Sigma>2) = Some u" and typeof_u: "typeof u = codom"
          using Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_correct[OF typeof_opubx] by auto
        hence x_def: "x = Subx.norm_unboxed u"
          using step_op_inl_hit.hyps
          using Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_correct[OF eval_opubx]
          unfolding \<open>opinl = \<BB>\<oo>\<xx> opubx\<close> take_map
          by simp

        let ?st2' = "Frame f l (Suc pc) R2 (u # drop ?ar \<Sigma>2) # st2'"
        let ?s2' = "State F2 H ?st2'"

        have step_s2_s2': "?STEP ?s2'"
          using step_op_inl_hit.hyps next_instr2
          unfolding IOpUbx \<open>opinl = \<BB>\<oo>\<xx> opubx\<close>
          using eval_opubx
          by (auto simp: s2_def st2_def intro!: Subx.step_op_ubx)
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'" by (rule step_s2_s2')
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              by (rule Subx.wf_state_step_preservation[OF wf_s2 step_s2_s2'])
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using step_op_inl_hit.hyps next_instr2 rel_stacktraces_Cons
              unfolding IOpUbx \<open>opinl = \<BB>\<oo>\<xx> opubx\<close> x_def
              by (auto simp: typeof_opubx typeof_u
                  simp: min_absorb2 take_map[symmetric] drop_map[symmetric]
                  simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.OpUbx
                  dest!: ap_map_list_cast_Dyn_replicate[symmetric])
          qed (insert rel_F1_F2, simp_all)
        qed
      qed simp_all
    next
      case (step_op_inl_miss opinl ar x F1')
      then obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.IOpInl opinl) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all
      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1' H ?st1') x")
      proof (cases instr2)
        case (IOpInl opinl')
        hence "opinl' = opinl" using norm_eq_instr1_instr2 by simp
        have casts:
          "ap_map_list cast_Dyn (take ar \<Sigma>2) = Some (take ar (map Subx.norm_unboxed \<Sigma>2))"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IOpInl, simplified]
          using step_op_inl_miss.hyps
          by (auto simp: \<open>opinl' = opinl\<close> take_map
              elim!: Subx.sp_instrs.cases[of _ _ "x # xs" for x xs, simplified] Subx.sp_instr.cases
              intro!: ap_map_list_cast_Dyn_eq_norm_stack[of "take (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) \<Sigma>2"]
              dest!: map_eq_append_replicate_conv)
        let ?st2' = "Frame f l (Suc pc) R2 (OpDyn x # drop ar \<Sigma>2) # st2'"
        let ?F2' = "Subx.Fenv.map_entry F2 f (\<lambda>fd. rewrite_fundef_body fd l pc (Ubx.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl)))"
        let ?s2' = "State ?F2' H ?st2'"
        have step_s2_s2': "?STEP ?s2'"
          using step_op_inl_miss.hyps casts next_instr2
          unfolding IOpInl \<open>opinl' = opinl\<close>
          by (auto simp: s2_def st2_def intro: Subx.step_op_inl_miss)
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'" by (rule step_s2_s2')
        next
          show "?MATCH (State F1' H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              by (rule Subx.wf_state_step_preservation[OF wf_s2 step_s2_s2'])
          next
            show "rel_fundefs (Finca_get F1') (Fubx_get ?F2')"
              using rel_F1_F2 step_op_inl_miss.hyps
              by (auto intro: rel_fundefs_rewriteI)
          next
            have "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using rel_st1'_st2'
              apply (rule rel_stacktraces.intros)
              using step_op_inl_miss.hyps casts next_instr2 rel_stacktraces_Cons
              unfolding IOpInl \<open>opinl' = opinl\<close>
              by (auto simp: min_absorb2 take_map[symmetric] drop_map[symmetric]
                  simp: next_instr_take_Suc_conv
                  intro!: sp_instrs_prefix' Subx.sp_instr.OpInl
                  dest!: ap_map_list_cast_Dyn_replicate[symmetric])
            then show "rel_stacktraces (Fubx_get ?F2') None ?st1' ?st2'"
              apply (rule rel_stacktraces_map_entry_rewrite_fundef_body)
              apply (rule next_instr2)
              unfolding IOpInl \<open>opinl' = opinl\<close>
              using Sinca.\<II>\<nn>\<ll>_invertible Subx.sp_instr_Op_OpInl_conv step_op_inl_miss.hyps apply metis
               apply simp
              apply simp
              done
          qed
        qed
      next
        case (IOpUbx opubx)
        hence "opinl = \<BB>\<oo>\<xx> opubx" using norm_eq_instr1_instr2 by simp
        let ?ar = "\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx))"

        obtain codom where typeof_opubx: "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx = (map typeof (take ?ar \<Sigma>2), codom)"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IOpUbx, simplified]
          by (cases "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx")
            (auto simp: eq_append_conv_conj Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy> take_map
              dest!: Subx.sp_instrs_ConsD elim!: Subx.sp_instr.cases)
        obtain u where "\<UU>\<bb>\<xx>\<OO>\<pp> opubx (take ?ar \<Sigma>2) = Some u"
          using Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_correct[OF typeof_opubx] by auto
        hence "\<II>\<ss>\<II>\<nn>\<ll> opinl (take ?ar \<Sigma>1)"
          unfolding \<Sigma>1_def
          by (auto simp: \<open>opinl = \<BB>\<oo>\<xx> opubx\<close> take_map dest: Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_to_\<II>\<nn>\<ll>[THEN Sinca.\<II>\<nn>\<ll>_\<II>\<ss>\<II>\<nn>\<ll>])
        hence False
          using step_op_inl_miss.hyps
          by (simp add: \<Sigma>1_def \<open>opinl = \<BB>\<oo>\<xx> opubx\<close>)
        thus ?thesis by simp
      qed simp_all
    next
      case (step_cjump l\<^sub>t l\<^sub>f d l' \<Sigma>1')
      then obtain u \<Sigma>2' where
        \<Sigma>2_def: "\<Sigma>2 = u # \<Sigma>2'" and
        d_def: "d = Subx.norm_unboxed u" and
        \<Sigma>1'_def: "\<Sigma>1' = map Subx.norm_unboxed \<Sigma>2'"
        by auto
      from step_cjump.hyps obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.ICJump l\<^sub>t l\<^sub>f) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all

      from next_instr2 norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (ICJump l\<^sub>t' l\<^sub>f')
        hence "l\<^sub>t' = l\<^sub>t" and "l\<^sub>f' = l\<^sub>f" using norm_eq_instr1_instr2 by simp_all
        hence "{l\<^sub>t, l\<^sub>f} \<subseteq> fst ` set (body fd2)"
          using all_jumps_in_range pc_in_range nth_instrs_pc ICJump by (auto simp: list_all_length)
        moreover have "l' \<in> {l\<^sub>t, l\<^sub>f}"
          using step_cjump.hyps by auto
        ultimately have "l' \<in> fst ` set (body fd2)"
          by blast
        then obtain instrs' where map_of_l': "map_of (body fd2) l' = Some instrs'"
          by (auto dest: weak_map_of_SomeI)

        have sp_instrs_instrs': "Subx.sp_instrs (map_option funtype \<circ> Fubx_get F2) (return fd2)
          (butlast instrs @ [instrs ! pc]) [] []" if pc_def: "pc = length instrs - 1"
          unfolding pc_def last_conv_nth[OF instrs_neq_Nil, symmetric]
          unfolding append_butlast_last_id[OF instrs_neq_Nil]
          by (rule sp_instrs_instrs)
  
        have sp_instr_last: "Subx.sp_instr (map_option funtype \<circ> Fubx_get F2) (return fd2)
          (instrs ! pc) (map typeof \<Sigma>2) []" if pc_def: "pc = length instrs - 1"
          using sp_instrs_instrs'[OF pc_def]
          using sp_instrs_prefix[unfolded pc_def butlast_conv_take[symmetric]]
          by (auto dest!: Subx.sp_instrs_appendD')

        have is_jump_nthD: "\<And>n. is_jump (instrs ! n) \<Longrightarrow> n < length instrs \<Longrightarrow> n = length instrs - 1"
          using list_all_map_of_SomeD[OF wf_fd2[THEN Subx.wf_fundef_all_wf_basic_blockD] map_of_fd2_l]
          by (auto dest!: Subx.wf_basic_blockD
                list_all_butlast_not_nthD[of "\<lambda>i. \<not> is_jump i \<and> \<not> Ubx.instr.is_return i", simplified, OF _ disjI1])

        have pc_def: "pc = length instrs - 1"
          using is_jump_nthD[OF _ pc_in_range] nth_instrs_pc ICJump by simp
        have \<Sigma>2'_eq_Nil: "\<Sigma>2' = []"
          using sp_instr_last[OF pc_def] step_cjump.hyps
          by (auto simp: \<Sigma>2_def d_def nth_instrs_pc ICJump elim!: Subx.sp_instr.cases)

        have cast: "cast_Dyn u = Some d"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc ICJump, simplified]
          by (auto simp: \<Sigma>2_def d_def dest!: Subx.sp_instrs_ConsD elim!: Subx.sp_instr.cases
              intro: Subx.typeof_and_norm_unboxed_imp_cast_Dyn)

        let ?st2' = "Frame f l' 0 R2 \<Sigma>2' # st2'"
        let ?s2' = "State F2 H ?st2'"

        have step_s2_s2': "?STEP ?s2'"
          using step_cjump.hyps cast next_instr2
          unfolding ICJump \<open>l\<^sub>t' = l\<^sub>t\<close> \<open>l\<^sub>f' = l\<^sub>f\<close>
          by (auto simp: s2_def st2_def \<Sigma>2_def intro!: Subx.step_cjump)
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'" by (rule step_s2_s2')
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              by (rule Subx.wf_state_step_preservation[OF wf_s2 step_s2_s2'])
          next
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              using step_cjump.hyps cast next_instr2 rel_stacktraces_Cons
              using map_of_l'
              unfolding ICJump \<open>l\<^sub>t' = l\<^sub>t\<close> \<open>l\<^sub>f' = l\<^sub>f\<close> \<Sigma>1'_def \<Sigma>2'_eq_Nil
              by (auto simp: min_absorb2 take_map[symmetric] drop_map[symmetric]
                  simp: next_instr_take_Suc_conv
                  intro!: rel_stacktraces.intros sp_instrs_prefix' Subx.sp_instr.CJump
                  intro: Subx.sp_instrs.Nil
                  dest!: ap_map_list_cast_Dyn_replicate[symmetric])
          qed (insert rel_F1_F2, simp_all)
        qed
      qed simp_all
    next
      case (step_call g gd1 frame\<^sub>g)
      then obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq (Inca.ICall g) instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all

      from step_call.hyps obtain gd2 where
        F2_g: "Fubx_get F2 g = Some gd2" and rel_gd1_gd2: "rel_fundef (=) norm_eq gd1 gd2"
        using rel_fundefs_Some1[OF rel_F1_F2] by auto
                
      have wf_gd2: "Subx.wf_fundef (map_option funtype \<circ> Fubx_get F2) gd2"
        by (rule Subx.wf_fundefs_getD[OF wf_F2 F2_g])

      obtain intrs\<^sub>g where gd2_fst_bblock: "map_of (body gd2) (fst (hd (body gd2))) = Some intrs\<^sub>g"
        using Subx.wf_fundef_body_neq_NilD[OF wf_gd2]
        by (metis hd_in_set map_of_eq_None_iff not_Some_eq prod.collapse prod_in_set_fst_image_conv)

      from norm_eq_instr1_instr2
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case (ICall g')
        hence "g' = g" using norm_eq_instr1_instr2 by simp
        hence all_dyn_args: "list_all is_dyn_operand (take (arity gd2) \<Sigma>2)"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc ICall, simplified]
          using F2_g
          by (auto simp: funtype_def eq_append_conv_conj take_map list.pred_set
              dest!: Subx.sp_instrs_ConsD replicate_eq_impl_Ball_eq elim!: Subx.sp_instr.cases)

        let ?frame\<^sub>g = "allocate_frame g gd2 (take (arity gd2) \<Sigma>2) (OpDyn uninitialized)"
        let ?st2' = "?frame\<^sub>g # Frame f l pc R2 \<Sigma>2 # st2'"
        let ?s2' = "State F2 H ?st2'"

        have step_s2_s2': "?STEP ?s2'"
          using step_call.hyps next_instr2 F2_g rel_gd1_gd2 all_dyn_args
          unfolding ICall \<open>g' = g\<close>
          by (auto simp: s2_def st2_def rel_fundef_arities intro!: Subx.step_call)
        show ?thesis
        proof (intro exI conjI)
          show "?STEP ?s2'" by (rule step_s2_s2')
        next
          show "?MATCH (State F1 H ?st1') ?s2'"
          proof (rule match.intros)
            show "Subx.wf_state ?s2'"
              by (rule Subx.wf_state_step_preservation[OF wf_s2 step_s2_s2'])
          next
            have FOO: "fst (hd (body gd1)) = fst (hd (body gd2))"
              apply (rule rel_fundef_rel_fst_hd_bodies[OF rel_gd1_gd2])
              using Subx.wf_fundefs_getD[OF wf_F2 \<open>Fubx_get F2 g = Some gd2\<close>]
              by (auto dest: Subx.wf_fundef_body_neq_NilD)
            show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
              unfolding step_call.hyps allocate_frame_def FOO
            proof (rule rel_stacktraces.intros)
              show "Fubx_get F2 g = Some gd2"
                by (rule F2_g)
            next
              show "rel_stacktraces (Fubx_get F2) (Some g)
                (Frame f l pc (map Subx.norm_unboxed R2) (map Subx.norm_unboxed \<Sigma>2) # st1')
                (Frame f l pc R2 \<Sigma>2 # st2')"
                using step_call.hyps rel_stacktraces_Cons next_instr2 F2_g rel_gd1_gd2 all_dyn_args
                unfolding ICall \<open>g' = g\<close>
                by (auto simp: is_valid_fun_call_def rel_fundef_arities intro!: rel_stacktraces.intros)
            qed (insert rel_gd1_gd2 all_dyn_args gd2_fst_bblock,
                simp_all add: take_map rel_fundef_arities rel_fundef_locals Subx.sp_instrs.Nil
                list_all_replicateI)
          qed (insert rel_F1_F2, simp_all)
        qed
      qed simp_all
    next
      case (step_return fd1 \<Sigma>1\<^sub>g frame\<^sub>g' g l\<^sub>g pc\<^sub>g R1\<^sub>g st1'')
      then obtain instr2 where
        next_instr2: "next_instr (Fubx_get F2) f l pc = Some instr2" and
        norm_eq_instr1_instr2: "norm_eq Inca.IReturn instr2"
        by (auto dest: rel_fundefs_next_instr1[OF rel_F1_F2])
      have pc_in_range: "pc < length instrs" and nth_instrs_pc: "instrs ! pc = instr2"
        using next_instr_get_map_ofD[OF next_instr2 F2_f map_of_fd2_l]
        by simp_all

      from step_return.hyps have rel_fd1_fd2: "rel_fundef (=) norm_eq fd1 fd2"
        using rel_fundefsD[OF rel_F1_F2, of f] F2_f  by simp

      from norm_eq_instr1_instr2
      show ?case  (is "\<exists>x. ?STEP x \<and> ?MATCH (State F1 H ?st1') x")
      proof (cases instr2)
        case IReturn
        have map_typeof_\<Sigma>2: "map typeof \<Sigma>2 = replicate (return fd2) None"
          using sp_instrs_sufix[OF pc_in_range, unfolded nth_instrs_pc IReturn, simplified]
          by (auto elim: Subx.sp_instr.cases dest: Subx.sp_instrs_ConsD)
        hence all_dyn_\<Sigma>2: "list_all is_dyn_operand \<Sigma>2"
          by (auto simp: list.pred_set dest: replicate_eq_impl_Ball_eq[OF sym])
        show ?thesis
          using rel_st1'_st2' unfolding \<open>Frame g l\<^sub>g pc\<^sub>g R1\<^sub>g \<Sigma>1\<^sub>g # st1'' = st1'\<close>[symmetric]
        proof (cases rule: rel_stacktraces.cases)
          case (rel_stacktraces_Cons st2'' \<Sigma>2\<^sub>g R2\<^sub>g gd2 instrs\<^sub>g)
          let ?st2' = "Frame g l\<^sub>g (Suc pc\<^sub>g) R2\<^sub>g (\<Sigma>2 @ drop (arity fd2) \<Sigma>2\<^sub>g) # st2''"
          let ?s2' = "State F2 H ?st2'"
          have step_s2_s2': "?STEP ?s2'"
            using step_return.hyps next_instr2 F2_f rel_fd1_fd2 rel_stacktraces_Cons all_dyn_\<Sigma>2
            unfolding IReturn
            by (auto simp: s2_def st2_def rel_fundef_arities rel_fundef_return
                intro: Subx.step_return)
          show ?thesis
          proof (intro exI conjI)
            show "?STEP ?s2'" by (rule step_s2_s2')
          next
            show "?MATCH (State F1 H ?st1') ?s2'"
            proof (rule match.intros)
              show "Subx.wf_state ?s2'"
                by (rule Subx.wf_state_step_preservation[OF wf_s2 step_s2_s2'])
            next
              have "Subx.sp_instr (map_option funtype \<circ> Fubx_get F2) (return gd2)
                (Ubx.instr.ICall f) (map typeof \<Sigma>2\<^sub>g)
                (replicate (return fd2) None @ map typeof (drop (arity fd2) \<Sigma>2\<^sub>g))"
                using rel_stacktraces_Cons F2_f
                using replicate_eq_map[of "arity fd2" "take (arity fd2) \<Sigma>2\<^sub>g" typeof None]
                by (auto simp: funtype_def is_valid_fun_call_def
                    simp: min_absorb2 list.pred_set take_map[symmetric] drop_map[symmetric]
                    intro!: Subx.sp_instr.Call[where \<Sigma> = "map typeof (drop (arity fd2) \<Sigma>2\<^sub>g)"])
              then show "rel_stacktraces (Fubx_get F2) None ?st1' ?st2'"
                unfolding step_return.hyps
                using rel_stacktraces_Cons rel_fd1_fd2 F2_f
                using map_typeof_\<Sigma>2
                by (auto simp: drop_map rel_fundef_arities is_valid_fun_call_def
                    simp: next_instr_take_Suc_conv funtype_def
                    intro!: rel_stacktraces.intros Subx.sp_instrs_appendI[where \<Sigma> = "map typeof \<Sigma>2\<^sub>g"])
            qed (insert rel_F1_F2, simp_all)
          qed
        qed
      qed simp_all
    qed
  qed
qed

lemma match_final_forward:
  assumes "match s1 s2" and final_s1: "final Finca_get Inca.IReturn s1"
  shows "final Fubx_get Ubx.IReturn s2"
  using \<open>match s1 s2\<close>
proof (cases s1 s2 rule: match.cases)
  case (matchI F2 H st2 F1 st1)
  show ?thesis
    using final_s1[unfolded matchI]
  proof (cases _ _ "State F1 H st1" rule: final.cases)
    case (finalI f l pc R \<Sigma>)
    then show ?thesis
      using matchI
      by (auto intro!: final.intros elim: rel_stacktraces.cases norm_instr.elims[OF sym]
          dest: rel_fundefs_next_instr1)
  qed
qed

sublocale inca_ubx_forward_simulation:
  forward_simulation Sinca.step Subx.step
    "final Finca_get Inca.IReturn"
    "final Fubx_get Ubx.IReturn"
    "\<lambda>_ _. False" "\<lambda>_. match"
  using match_final_forward forward_lockstep_simulation
  using lockstep_to_plus_forward_simulation[of match Sinca.step _ Subx.step]
  by unfold_locales auto


section \<open>Bisimulation\<close>

sublocale inca_ubx_bisimulation:
  bisimulation Sinca.step Subx.step "final Finca_get Inca.IReturn" "final Fubx_get Ubx.IReturn"
  "\<lambda>_ _. False" "\<lambda>_. match"
  by unfold_locales

end

end
