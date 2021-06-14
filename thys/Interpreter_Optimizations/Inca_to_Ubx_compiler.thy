theory Inca_to_Ubx_compiler
  imports Inca_to_Ubx_simulation Result
    "VeriComp.Compiler"
    "HOL-Library.Monad_Syntax"
begin

section \<open>Generic program rewriting\<close>

primrec monadic_fold_map where
  "monadic_fold_map f acc [] = Some (acc, [])" |
  "monadic_fold_map f acc (x # xs) = do {
    (acc', x') \<leftarrow> f acc x;
    (acc'', xs') \<leftarrow> monadic_fold_map f acc' xs;
    Some (acc'', x' # xs')
  }"

lemma monadic_fold_map_length:
  "monadic_fold_map f acc xs = Some (acc', xs') \<Longrightarrow> length xs = length xs'"
  by (induction xs arbitrary: acc xs') (auto simp: bind_eq_Some_conv)

lemma monadic_fold_map_ConsD[dest]:
  assumes "monadic_fold_map f a (x # xs) = Some (c, ys)"
  shows "\<exists>y ys' b. ys = y # ys' \<and> f a x = Some (b, y) \<and> monadic_fold_map f b xs = Some (c, ys')"
  using assms
  by (auto simp add: bind_eq_Some_conv)

lemma monadic_fold_map_list_all2:
  assumes "monadic_fold_map f acc xs = Some (acc', ys)" and
    "\<And>acc acc' x y. f acc x = Some (acc', y) \<Longrightarrow> P x y"
  shows "list_all2 P xs ys"
  using assms(1)
proof (induction xs arbitrary: acc ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    using Cons.prems
    by (auto simp: bind_eq_Some_conv intro: assms(2) Cons.IH)
qed

lemma monadic_fold_map_list_all:
  assumes "monadic_fold_map f acc xs = Some (acc', ys)" and
    "\<And>acc acc' x y. f acc x = Some (acc', y) \<Longrightarrow> P y"
  shows "list_all P ys"
proof -
  have "list_all2 (\<lambda>_. P) xs ys"
    using assms
    by (auto elim: monadic_fold_map_list_all2)
  thus ?thesis
    by (auto elim: list_rel_imp_pred2)
qed

fun gen_pop_push where
  "gen_pop_push instr (domain, codomain) \<Sigma> = (
    let ar = length domain in
    if ar \<le> length \<Sigma> \<and> take ar \<Sigma> = domain then
      Some (instr, codomain @ drop ar \<Sigma>)
    else
      None
  )"

context inca_to_ubx_simulation begin

section \<open>Lifting\<close>

fun lift_instr where
  "lift_instr F L ret N (Inca.IPush d) \<Sigma> = Some (IPush d, None # \<Sigma>)" |
  "lift_instr F L ret N Inca.IPop (_ # \<Sigma>) = Some (IPop, \<Sigma>)" |
  "lift_instr F L ret N (Inca.IGet n) \<Sigma> = (if n < N then Some (IGet n, None # \<Sigma>) else None)" |
  "lift_instr F L ret N (Inca.ISet n) (None # \<Sigma>) = (if n < N then Some (ISet n, \<Sigma>) else None)" |
  "lift_instr F L ret N (Inca.ILoad x) (None # \<Sigma>) = Some (ILoad x, None # \<Sigma>)" |
  "lift_instr F L ret N (Inca.IStore x) (None # None # \<Sigma>) = Some (IStore x, \<Sigma>)" |
  "lift_instr F L ret N (Inca.IOp op) \<Sigma> =
    gen_pop_push (IOp op) (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> op) None, [None]) \<Sigma>" |
  "lift_instr F L ret N (Inca.IOpInl opinl) \<Sigma> =
    gen_pop_push (IOpInl opinl) (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) None, [None]) \<Sigma>" |
  "lift_instr F L ret N (Inca.ICJump l\<^sub>t l\<^sub>f) [None] =
    (if List.member L l\<^sub>t \<and> List.member L l\<^sub>f then Some (ICJump l\<^sub>t l\<^sub>f, []) else None)" |
  "lift_instr F L ret N (Inca.ICall f) \<Sigma> = do {
    (ar, ret) \<leftarrow> F f;
    gen_pop_push (ICall f) (replicate ar None, replicate ret None) \<Sigma>
  }" |
  "lift_instr F L ret N Inca.IReturn \<Sigma> =
    (if \<Sigma> = replicate ret None then Some (IReturn, []) else None)" |
  "lift_instr _ _ _ _ _ _ = None"

definition lift_instrs where
  "lift_instrs F L ret N \<equiv>
    monadic_fold_map (\<lambda>\<Sigma> instr. map_option prod.swap (lift_instr F L ret N instr \<Sigma>))"

lemma lift_instrs_length:
  assumes "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "length xs = length ys"
  using assms unfolding lift_instrs_def
  by (auto intro: monadic_fold_map_length)

lemma lift_instrs_not_Nil: "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys) \<Longrightarrow> xs \<noteq> [] \<longleftrightarrow> ys \<noteq> []"
  using lift_instrs_length by fastforce

lemma lift_instrs_NilD[dest]:
  assumes "lift_instrs F L ret N \<Sigma>i [] = Some (\<Sigma>o, ys)"
  shows "\<Sigma>o = \<Sigma>i \<and> ys = []"
  using assms
  by (simp_all add: lift_instrs_def)

lemmas Some_eq_bind_conv =
  bind_eq_Some_conv[unfolded eq_commute[of "Option.bind f g" "Some x" for f g x]]

lemma lift_instr_is_jump:
  assumes "lift_instr F L ret N x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Inca.is_jump x \<longleftrightarrow> Ubx.is_jump y"
  using assms
  by (rule lift_instr.elims)
    (auto simp add: if_split_eq2 Let_def Some_eq_bind_conv)

lemma lift_instr_is_return:
  assumes "lift_instr F L ret N x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Inca.is_return x \<longleftrightarrow> Ubx.is_return y"
  using assms
  by (rule lift_instr.elims)
    (auto simp add: if_split_eq2 Let_def Some_eq_bind_conv)

lemma lift_instrs_all_not_jump_not_return:
  assumes "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows
    "list_all (\<lambda>i. \<not> Inca.is_jump i \<and> \<not> Inca.is_return i) xs \<longleftrightarrow>
     list_all (\<lambda>i. \<not> Ubx.is_jump i \<and> \<not> Ubx.is_return i) ys"
  using assms
proof (induction xs arbitrary: \<Sigma>i \<Sigma>o ys)
  case Nil
  then show ?case by (simp add: lift_instrs_def)
next
  case (Cons x xs)
  from Cons.prems show ?case
    apply (simp add: lift_instrs_def bind_eq_Some_conv)
    apply (fold lift_instrs_def)
    by (auto simp add: Cons.IH lift_instr_is_jump lift_instr_is_return)
qed

lemma lift_instrs_all_butlast_not_jump_not_return:
  assumes "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows
    "list_all (\<lambda>i. \<not> Inca.is_jump i \<and> \<not> Inca.is_return i) (butlast xs) \<longleftrightarrow>
     list_all (\<lambda>i. \<not> Ubx.is_jump i \<and> \<not> Ubx.is_return i) (butlast ys)"
  using lift_instrs_length[OF assms(1)] assms unfolding lift_instrs_def
proof (induction xs ys arbitrary: \<Sigma>i \<Sigma>o rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  thus ?case
    by (auto simp add: bind_eq_Some_conv lift_instr_is_jump lift_instr_is_return)
qed

lemma lift_instr_sp:
  assumes "lift_instr F L ret N x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.sp_instr F ret y \<Sigma>i \<Sigma>o"
  using assms
  apply (induction F L ret N x \<Sigma>i rule: lift_instr.induct;
      auto simp: Let_def intro: Subx.sp_instr.intros)
    apply (rule Subx.sp_instr.Op, metis append_take_drop_id)
   apply (rule Subx.sp_instr.OpInl, metis append_take_drop_id)
  apply (auto simp add: bind_eq_Some_conv intro!: Subx.sp_instr.Call, metis append_take_drop_id)
  done

lemma lift_instrs_sp:
  assumes "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "Subx.sp_instrs F ret ys \<Sigma>i \<Sigma>o"
  using assms unfolding lift_instrs_def
proof (induction xs arbitrary: \<Sigma>i \<Sigma>o ys)
  case Nil
  thus ?case by (auto intro: Subx.sp_instrs.Nil)
next
  case (Cons x xs)
  from Cons.prems show ?case
    by (auto simp add: bind_eq_Some_conv intro: Subx.sp_instrs.Cons lift_instr_sp Cons.IH)
qed

lemma lift_instr_fun_call_in_range:
  assumes "lift_instr F L ret N x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.fun_call_in_range F y"
  using assms
  by (induction F L ret N x \<Sigma>i rule: lift_instr.induct) (auto simp: Let_def bind_eq_Some_conv)

lemma lift_instrs_all_fun_call_in_range:
  assumes "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "list_all (Subx.fun_call_in_range F) ys"
  using assms unfolding lift_instrs_def
  by (auto intro!: monadic_fold_map_list_all intro: lift_instr_fun_call_in_range)

lemma lift_instr_local_var_in_range:
  assumes "lift_instr F L ret N x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.local_var_in_range N y"
  using assms
  by (induction F L ret N x \<Sigma>i rule: lift_instr.induct) (auto simp: Let_def bind_eq_Some_conv)

lemma lift_instrs_all_local_var_in_range:
  assumes "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "list_all (Subx.local_var_in_range N) ys"
  using assms unfolding lift_instrs_def
  by (auto intro!: monadic_fold_map_list_all intro: lift_instr_local_var_in_range)

lemma lift_instr_jump_in_range:
  assumes "lift_instr F L ret N x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.jump_in_range (set L) y"
  using assms
  by (induction F L ret N x \<Sigma>i rule: lift_instr.induct)
    (auto simp: Let_def bind_eq_Some_conv in_set_member)

lemma lift_instrs_all_jump_in_range:
  assumes "lift_instrs F L ret N \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "list_all (Subx.jump_in_range (set L)) ys"
  using assms unfolding lift_instrs_def
  by (auto intro!: monadic_fold_map_list_all intro: lift_instr_jump_in_range)

lemma lift_instr_norm:
  "lift_instr F L ret N instr1 \<Sigma>1 = Some (instr2, \<Sigma>2) \<Longrightarrow> norm_eq instr1 instr2"
  by (induction instr1 \<Sigma>1 rule: lift_instr.induct) (auto simp: Let_def bind_eq_Some_conv)

lemma lift_instrs_all_norm:
  assumes "lift_instrs F L ret N \<Sigma>1 instrs1 = Some (\<Sigma>2, instrs2)"
  shows "list_all2 norm_eq instrs1 instrs2"
  using assms unfolding lift_instrs_def
  by (auto simp: lift_instr_norm elim!: monadic_fold_map_list_all2)


section \<open>Optimization\<close>

context
  fixes load_oracle :: "nat \<Rightarrow> type option"
begin

definition orelse :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"  (infixr "orelse" 55) where
  "x orelse y = (case x of Some x' \<Rightarrow> Some x' | None \<Rightarrow> y)"

lemma orelse_eq_Some_conv:
  "x orelse y = Some z \<longleftrightarrow> (x = Some z \<or> x = None \<and> y = Some z)"
  by (cases x) (simp_all add: orelse_def)

lemma orelse_eq_SomeE:
  assumes
    "x orelse y = Some z" and
    "x = Some z \<Longrightarrow> P" and
    "x = None \<Longrightarrow> y = Some z \<Longrightarrow> P"
  shows "P"
  using assms(1)
  unfolding orelse_def
  by (cases x; auto intro: assms(2,3))

fun drop_prefix where
  "drop_prefix [] ys = Some ys" |
  "drop_prefix (x # xs) (y # ys) = (if x = y then drop_prefix xs ys else None)" |
  "drop_prefix _ _ = None "

lemma drop_prefix_eq_Some_conv: "drop_prefix xs ys = Some zs \<longleftrightarrow> ys = xs @ zs"
  by (induction xs ys arbitrary: zs rule: drop_prefix.induct)
    (auto simp: if_split_eq1)

fun optim_instr where
  "optim_instr _ _ _ (IPush d) \<Sigma> =
    Some Pair \<diamondop> (Some IPushUbx1 \<diamondop> (unbox_ubx1 d)) \<diamondop> Some (Some Ubx1 # \<Sigma>) orelse
    Some Pair \<diamondop> (Some IPushUbx2 \<diamondop> (unbox_ubx2 d)) \<diamondop> Some (Some Ubx2 # \<Sigma>) orelse
    Some (IPush d, None # \<Sigma>)
  " |
  "optim_instr _ _ _ (IPushUbx1 n) \<Sigma> = Some (IPushUbx1 n, Some Ubx1 # \<Sigma>)" |
  "optim_instr _ _ _ (IPushUbx2 b) \<Sigma> = Some (IPushUbx2 b, Some Ubx2 # \<Sigma>)" |
  "optim_instr _ _ _ IPop (_ # \<Sigma>) = Some (IPop, \<Sigma>)" |
  "optim_instr _ _ pc (IGet n) \<Sigma> =
    map_option (\<lambda>\<tau>. (IGetUbx \<tau> n, Some \<tau> # \<Sigma>)) (load_oracle pc) orelse
    Some (IGet n, None # \<Sigma>)" |
  "optim_instr _ _ pc (IGetUbx \<tau> n) \<Sigma> = Some (IGetUbx \<tau> n, Some \<tau> # \<Sigma>)" |
  "optim_instr _ _ _ (ISet n) (None # \<Sigma>) = Some (ISet n, \<Sigma>)" |
  "optim_instr _ _ _ (ISet n) (Some \<tau> # \<Sigma>) = Some (ISetUbx \<tau> n, \<Sigma>)" |
  "optim_instr _ _ _ (ISetUbx _ n) (None # \<Sigma>) = Some (ISet n, \<Sigma>)" |
  "optim_instr _ _ _ (ISetUbx _ n) (Some \<tau> # \<Sigma>) = Some (ISetUbx \<tau> n, \<Sigma>)" |
  "optim_instr _ _ pc (ILoad x) (None # \<Sigma>) =
    map_option (\<lambda>\<tau>. (ILoadUbx \<tau> x, Some \<tau> # \<Sigma>)) (load_oracle pc) orelse
    Some (ILoad x, None # \<Sigma>)" |
  "optim_instr _ _ _ (ILoadUbx \<tau> x) (None # \<Sigma>) = Some (ILoadUbx \<tau> x, Some \<tau> # \<Sigma>)" |
  "optim_instr _ _ _ (IStore x) (None # None # \<Sigma>) = Some (IStore x, \<Sigma>)" |
  "optim_instr _ _ _ (IStore x) (None # Some \<tau> # \<Sigma>) = Some (IStoreUbx \<tau> x, \<Sigma>)" |
  "optim_instr _ _ _ (IStoreUbx _ x) (None # None # \<Sigma>) = Some (IStore x, \<Sigma>)" |
  "optim_instr _ _ _ (IStoreUbx _ x) (None # Some \<tau> # \<Sigma>) = Some (IStoreUbx \<tau> x, \<Sigma>)" |
  "optim_instr _ _ _ (IOp op) \<Sigma> =
    map_option (\<lambda>\<Sigma>o. (IOp op, None # \<Sigma>o)) (drop_prefix (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> op) None) \<Sigma>)" |
  "optim_instr _ _ _ (IOpInl opinl) \<Sigma> = (
    let ar = \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) in
    if ar \<le> length \<Sigma> then
      case \<UU>\<bb>\<xx> opinl (take ar \<Sigma>) of
        None \<Rightarrow> map_option (\<lambda>\<Sigma>o. (IOpInl opinl, None # \<Sigma>o)) (drop_prefix (replicate ar None) \<Sigma>) |
        Some opubx \<Rightarrow> map_option (\<lambda>\<Sigma>o. (IOpUbx opubx, snd (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx) # \<Sigma>o))
          (drop_prefix (fst (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx)) \<Sigma>)
    else
      None
  )" |
  "optim_instr _ _ _ (IOpUbx opubx) \<Sigma> =
    (let p = \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx in
     map_option (\<lambda>\<Sigma>o. (IOpUbx opubx, snd p # \<Sigma>o)) (drop_prefix (fst p) \<Sigma>))" |
  "optim_instr _ _ _ (ICJump l\<^sub>t l\<^sub>f) [None] = Some (ICJump l\<^sub>t l\<^sub>f, []) " |
  "optim_instr F _ _ (ICall f) \<Sigma> = do {
    (ar, ret) \<leftarrow> F f;
    \<Sigma>o \<leftarrow> drop_prefix (replicate ar None) \<Sigma>;
    Some (ICall f, replicate ret None @ \<Sigma>o)
  }" |
  "optim_instr _ ret _ IReturn \<Sigma> = (if \<Sigma> = replicate ret None then Some (IReturn, []) else None)" |
  "optim_instr _ _ _ _ _ = None"

definition optim_instrs where
  "optim_instrs F ret \<equiv> \<lambda>pc \<Sigma>i instrs.
    map_option (\<lambda>((_, \<Sigma>o), instrs'). (\<Sigma>o, instrs'))
      (monadic_fold_map (\<lambda>(pc, \<Sigma>) instr.
        map_option (\<lambda>(instr', \<Sigma>o). ((Suc pc, \<Sigma>o), instr')) (optim_instr F ret pc instr \<Sigma>))
      (pc, \<Sigma>i) instrs)"

lemma optim_instrs_length:
  assumes "optim_instrs F ret pc \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "length xs = length ys"
  using assms unfolding optim_instrs_def
  by (auto intro: monadic_fold_map_length)

lemma optim_instrs_not_Nil: "optim_instrs F ret pc \<Sigma>i xs = Some (\<Sigma>o, ys) \<Longrightarrow> xs \<noteq> [] \<longleftrightarrow> ys \<noteq> []"
  using optim_instrs_length by fastforce

lemma optim_instrs_NilD[dest]:
  assumes "optim_instrs F ret pc \<Sigma>i [] = Some (\<Sigma>o, ys)"
  shows "\<Sigma>o = \<Sigma>i \<and> ys = []"
  using assms
  by (simp_all add: optim_instrs_def)

lemma optim_instrs_ConsD[dest]:
  assumes "optim_instrs F ret pc \<Sigma>i (x # xs) = Some (\<Sigma>o, ys)"
  shows "\<exists>y ys' \<Sigma>. ys = y # ys' \<and>
    optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>) \<and>
    optim_instrs F ret (Suc pc) \<Sigma> xs = Some (\<Sigma>o, ys')"
  using assms
  unfolding optim_instrs_def
  by (auto simp: bind_eq_Some_conv)

lemma optim_instr_norm:
  assumes "optim_instr F ret pc instr1 \<Sigma>1 = Some (instr2, \<Sigma>2)"
  shows "norm_instr instr1 = norm_instr instr2"
  using assms
  by (cases "(F, ret, pc, instr1, \<Sigma>1)" rule: optim_instr.cases)
    (auto simp: ap_option_eq_Some_conv Let_def if_split_eq1 bind_eq_Some_conv option.case_eq_if
      orelse_eq_Some_conv
      dest!: Subx.box_unbox_inverse dest: Subx.\<UU>\<bb>\<xx>_invertible)

lemma optim_instrs_all_norm:
  assumes "optim_instrs F ret pc \<Sigma>1 instrs1 = Some (\<Sigma>2, instrs2)"
  shows "list_all2 (\<lambda>i1 i2. norm_instr i1 = norm_instr i2) instrs1 instrs2"
  using assms unfolding optim_instrs_def
  by (auto simp: optim_instr_norm elim!: monadic_fold_map_list_all2)

lemma optim_instr_is_jump:
  assumes "optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "is_jump x \<longleftrightarrow> is_jump y"
  using assms
  by (cases "(F, ret, pc, x, \<Sigma>i)" rule: optim_instr.cases;
      simp add: orelse_eq_Some_conv ap_option_eq_Some_conv bind_eq_Some_conv
        Let_def if_split_eq1 option.case_eq_if;
      safe; simp)

lemma optim_instr_is_return:
  assumes "optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "is_return x \<longleftrightarrow> is_return y"
  using assms
  by (cases "(F, ret, pc, x, \<Sigma>i)" rule: optim_instr.cases;
      simp add: orelse_eq_Some_conv ap_option_eq_Some_conv bind_eq_Some_conv
        Let_def if_split_eq1 option.case_eq_if;
      safe; simp)

lemma optim_instrs_all_butlast_not_jump_not_return:
  assumes "optim_instrs F ret pc \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows
    "list_all (\<lambda>i. \<not> is_jump i \<and> \<not> is_return i) (butlast xs) \<longleftrightarrow>
     list_all (\<lambda>i. \<not> is_jump i \<and> \<not> is_return i) (butlast ys)"
  using optim_instrs_length[OF assms(1)] assms
proof (induction xs ys arbitrary: pc \<Sigma>i \<Sigma>o rule: list_induct2)
  case Nil
  thus ?case by simp
next
  case (Cons x xs y ys)
  from Cons.prems obtain \<Sigma> where
    optim_x: "optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>)" and
    optim_xs: "optim_instrs F ret (Suc pc) \<Sigma> xs = Some (\<Sigma>o, ys)"
    by auto
  show ?case
    using Cons.hyps
    using optim_x optim_xs
    apply (simp add: Cons.IH optim_instr_is_jump optim_instr_is_return)
    by fastforce
qed

lemma optim_instr_jump_in_range:
  assumes "optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.jump_in_range L x \<longleftrightarrow> Subx.jump_in_range L y"
  using assms
  by (cases "(F, ret, pc, x, \<Sigma>i)" rule: optim_instr.cases)
    (auto simp: ap_option_eq_Some_conv Let_def if_split_eq1 option.case_eq_if
      bind_eq_Some_conv orelse_eq_Some_conv)

lemma optim_instrs_all_jump_in_range:
  assumes "optim_instrs F ret pc \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "list_all (Subx.jump_in_range L) xs \<longleftrightarrow> list_all (Subx.jump_in_range L) ys"
  using assms
  by (induction xs arbitrary: pc \<Sigma>i \<Sigma>o ys) (auto simp: optim_instr_jump_in_range)

lemma optim_instr_fun_call_in_range:
  assumes "optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.fun_call_in_range F x \<longleftrightarrow> Subx.fun_call_in_range F y"
  using assms
  by (cases "(F, ret, pc, x, \<Sigma>i)" rule: optim_instr.cases)
    (auto simp: ap_option_eq_Some_conv Let_def if_split_eq1 option.case_eq_if
      bind_eq_Some_conv orelse_eq_Some_conv)

lemma optim_instrs_all_fun_call_in_range:
  assumes "optim_instrs F ret pc \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "list_all (Subx.fun_call_in_range F) xs \<longleftrightarrow> list_all (Subx.fun_call_in_range F) ys"
  using assms
  by (induction xs arbitrary: pc \<Sigma>i \<Sigma>o ys) (auto simp: optim_instr_fun_call_in_range)

lemma optim_instr_local_var_in_range:
  assumes "optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.local_var_in_range N x \<longleftrightarrow> Subx.local_var_in_range N y"
  using assms
  by (cases "(F, ret, pc, x, \<Sigma>i)" rule: optim_instr.cases)
    (auto simp: ap_option_eq_Some_conv Let_def if_split_eq1 option.case_eq_if
      bind_eq_Some_conv orelse_eq_Some_conv)

lemma optim_instrs_all_local_var_in_range:
  assumes "optim_instrs F ret pc \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "list_all (Subx.local_var_in_range N) xs \<longleftrightarrow> list_all (Subx.local_var_in_range N) ys"
  using assms
  by (induction xs arbitrary: pc \<Sigma>i \<Sigma>o ys) (auto simp: optim_instr_local_var_in_range)

lemma optim_instr_sp:
  assumes "optim_instr F ret pc x \<Sigma>i = Some (y, \<Sigma>o)"
  shows "Subx.sp_instr F ret y \<Sigma>i \<Sigma>o"
  using assms
  by (cases "(F, ret, pc, x, \<Sigma>i)" rule: optim_instr.cases)
    (auto simp add: Let_def if_split_eq1 option.case_eq_if
      simp: ap_option_eq_Some_conv orelse_eq_Some_conv drop_prefix_eq_Some_conv bind_eq_Some_conv
      intro: Subx.sp_instr.intros)

lemma optim_instrs_sp:
  assumes "optim_instrs F ret pc \<Sigma>i xs = Some (\<Sigma>o, ys)"
  shows "Subx.sp_instrs F ret ys \<Sigma>i \<Sigma>o"
  using assms
  by (induction xs arbitrary: pc \<Sigma>i \<Sigma>o ys)
    (auto intro!: Subx.sp_instrs.intros optim_instr_sp)


section \<open>Compilation of function definition\<close>

definition lift_basic_block where
  "lift_basic_block F L ret N \<equiv>
    ap_map_prod Some (\<lambda>i1. do {
      _ \<leftarrow> if i1 \<noteq> [] then Some () else None;
      _ \<leftarrow> if list_all (\<lambda>i. \<not> Inca.is_jump i \<and> \<not> Inca.is_return i) (butlast i1) then Some () else None;
      (\<Sigma>o, i2) \<leftarrow> lift_instrs F L ret N ([] :: type option list) i1;
      (\<Sigma>o', i2') \<leftarrow> optim_instrs F ret 0 ([] :: type option list) i2;
      (if \<Sigma>o' = [] then
        Some i2'
      else (if \<Sigma>o = [] then
        Some i2
      else
        None))
    })"

lemma lift_basic_block_rel_prod_all_norm_eq:
  assumes "lift_basic_block F L ret N bblock1 = Some bblock2"
  shows "rel_prod (=) (list_all2 norm_eq) bblock1 bblock2"
  using assms
  unfolding lift_basic_block_def
  apply (auto simp add: ap_map_prod_eq_Some_conv bind_eq_Some_conv
      simp: if_split_eq1
      intro: lift_instrs_all_norm
      dest!: optim_instrs_all_norm lift_instrs_all_norm)
  subgoal for _ xs zs ys
    using list_all2_trans[of norm_eq "\<lambda>i. norm_eq (norm_instr i)" norm_eq xs ys zs, simplified]
    by simp
  done

lemma list_all_iff_butlast_last:
  assumes "xs \<noteq> []"
  shows "list_all P xs \<longleftrightarrow> list_all P (butlast xs) \<and> P (last xs)"
  using assms
  by (induction xs) auto

lemma lift_basic_block_wf:
  assumes "lift_basic_block F L ret N x = Some y"
  shows "Subx.wf_basic_block F (set L) ret N y"
proof -
  obtain f instrs1 \<Sigma>2 instrs2 \<Sigma>3 instrs3 instrs4 where
    x_def: "x = (f, instrs1)" and
    y_def: "y = (f, instrs4)" and
    "instrs1 \<noteq> []" and
    all_not_jump_not_return_instrs1:
      "list_all (\<lambda>i. \<not> Inca.is_jump i \<and> \<not> Inca.is_return i) (butlast instrs1)" and
    lift_instrs1: "lift_instrs F L ret N ([] :: type option list) instrs1 = Some (\<Sigma>2, instrs2)" and
    optim_instrs2: "optim_instrs F ret 0 ([] :: type option list) instrs2 = Some (\<Sigma>3, instrs3)" and
    instr4_defs: "instrs4 = instrs3 \<and> \<Sigma>3 = [] \<or> instrs4 = instrs2 \<and> \<Sigma>2 = []"
    using assms
    unfolding lift_basic_block_def ap_map_prod_eq_Some_conv
    apply (auto simp: bind_eq_Some_conv if_split_eq1)
    by auto

  have "instrs4 \<noteq> []"
    using instr4_defs \<open>instrs1 \<noteq> []\<close>
    using lift_instrs_not_Nil[OF lift_instrs1]
    using optim_instrs_not_Nil[OF optim_instrs2]
    by meson
  moreover have "list_all (Subx.local_var_in_range N) instrs4"
    using instr4_defs lift_instrs1 optim_instrs2
    by (auto dest: lift_instrs_all_local_var_in_range simp: optim_instrs_all_local_var_in_range)
  moreover have "list_all (Subx.fun_call_in_range F) instrs4"
    using instr4_defs lift_instrs1 optim_instrs2
    by (auto dest: lift_instrs_all_fun_call_in_range simp: optim_instrs_all_fun_call_in_range)
  moreover have "list_all (Subx.jump_in_range (set L)) instrs4"
    using instr4_defs lift_instrs1 optim_instrs2
    by (auto dest: lift_instrs_all_jump_in_range simp: optim_instrs_all_jump_in_range)
  moreover have "list_all (\<lambda>i. \<not> Ubx.instr.is_jump i \<and> \<not> Ubx.instr.is_return i) (butlast instrs4)"
    using instr4_defs lift_instrs1 optim_instrs2 all_not_jump_not_return_instrs1
    by (auto simp:
        lift_instrs_all_butlast_not_jump_not_return
        optim_instrs_all_butlast_not_jump_not_return)
  moreover have "Subx.sp_instrs F ret instrs4 [] []"
    using instr4_defs lift_instrs1 optim_instrs2
    by (auto intro: lift_instrs_sp optim_instrs_sp)
  ultimately show ?thesis
    by (auto simp: y_def intro!: Subx.wf_basic_blockI)
qed

fun compile_fundef where
  "compile_fundef F (Fundef bblocks1 ar ret locals) = do {
    _ \<leftarrow> if bblocks1 = [] then None else Some ();
    bblocks2 \<leftarrow> ap_map_list (lift_basic_block F (map fst bblocks1) ret (ar + locals)) bblocks1;
    Some (Fundef bblocks2 ar ret locals)
  }"

lemma compile_fundef_arities: "compile_fundef F fd1 = Some fd2 \<Longrightarrow> arity fd1 = arity fd2"
  by (cases fd1) (auto simp: bind_eq_Some_conv)

lemma compile_fundef_returns: "compile_fundef F fd1 = Some fd2 \<Longrightarrow> return fd1 = return fd2"
  by (cases fd1) (auto simp: bind_eq_Some_conv)

lemma compile_fundef_locals:
  "compile_fundef F fd1 = Some fd2 \<Longrightarrow> fundef_locals fd1 = fundef_locals fd2"
  by (cases fd1) (auto simp: bind_eq_Some_conv)

lemma if_then_None_else_Some_eq[simp]:
  "(if a then None else Some b) = Some c \<longleftrightarrow> \<not> a \<and> b = c"
  "(if a then None else Some b) = None \<longleftrightarrow> a"
  by (cases a) simp_all

lemma
  assumes "compile_fundef F fd1 = Some fd2"
  shows
    rel_compile_fundef: "rel_fundef (=) norm_eq fd1 fd2" (is ?REL) and
    wf_compile_fundef: "Subx.wf_fundef F fd2" (is ?WF)
  unfolding atomize_conj
proof (cases fd1)
  case (Fundef bblocks1 ar ret locals)
  with assms obtain bblocks2 where
    "bblocks1 \<noteq> []" and
    lift_bblocks1:
      "ap_map_list (lift_basic_block F (map fst bblocks1) ret (ar + locals)) bblocks1 = Some bblocks2" and
    fd2_def: "fd2 = Fundef bblocks2 ar ret locals"
    by (auto simp add: bind_eq_Some_conv)

  show "?REL \<and> ?WF"
  proof (rule conjI)
    show ?REL
      unfolding Fundef fd2_def
    proof (rule fundef.rel_intros)
      show "list_all2 (rel_prod (=) (list_all2 norm_eq)) bblocks1 bblocks2"
        using lift_bblocks1
        unfolding ap_map_list_iff_list_all2
        by (auto elim: list.rel_mono_strong intro: lift_basic_block_rel_prod_all_norm_eq)
    qed simp_all
  next
    have "bblocks2 \<noteq> []"
      using \<open>bblocks1 \<noteq> []\<close> length_ap_map_list[OF lift_bblocks1] by force
    moreover have "list_all (Subx.wf_basic_block F (fst ` set bblocks1) ret (ar + locals)) bblocks2"
      using lift_bblocks1
      unfolding ap_map_list_iff_list_all2
      by (auto elim!: list_rel_imp_pred2 dest: lift_basic_block_wf)
    moreover have "fst ` set bblocks1 = fst ` set bblocks2"
      using lift_bblocks1
      unfolding ap_map_list_iff_list_all2
      by (induction bblocks1 bblocks2 rule: list.rel_induct)
        (auto simp add: lift_basic_block_def ap_map_prod_eq_Some_conv)
    ultimately show ?WF
      unfolding fd2_def
      by (auto intro: Subx.wf_fundefI)
  qed
qed

end

end

locale inca_ubx_compiler =
  inca_to_ubx_simulation Finca_empty Finca_get
  for
    Finca_empty and
    Finca_get :: "_ \<Rightarrow> 'fun \<Rightarrow> _ option" +
  fixes
    load_oracle :: "'fun \<Rightarrow> nat \<Rightarrow> type option"
begin


section \<open>Compilation of function environment\<close>

definition compile_env_entry where
  "compile_env_entry F \<equiv> \<lambda>p. ap_map_prod Some (compile_fundef (load_oracle (fst p)) F) p"

lemma rel_compile_env_entry:
  assumes "compile_env_entry F (f, fd1) = Some (f, fd2)"
  shows "rel_fundef (=) norm_eq fd1 fd2"
  using assms unfolding compile_env_entry_def
  by (auto simp: ap_map_prod_eq_Some_conv intro!: rel_compile_fundef)

definition compile_env where
  "compile_env e \<equiv> do {
    let fundefs1 = Finca_to_list e;
    fundefs2 \<leftarrow> ap_map_list (compile_env_entry (map_option funtype \<circ> Finca_get e)) fundefs1;
    Some (Subx.Fenv.from_list fundefs2)
  }"

lemma rel_ap_map_list_ap_map_list_compile_env_entries:
  assumes "ap_map_list (compile_env_entry F) xs = Some ys"
  shows "rel_fundefs (Finca_get (Sinca.Fenv.from_list xs)) (Fubx_get (Subx.Fenv.from_list ys))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  thus ?case
    using rel_fundefs_empty by simp
next
  case (Cons x xs)
  from Cons.prems obtain y ys' where
    ys_def: "ys = y # ys'" and
    compile_env_x: "compile_env_entry F x = Some y" and
    compile_env_xs: "ap_map_list (compile_env_entry F) xs = Some ys'"
    by (auto simp add: ap_option_eq_Some_conv)

  obtain f fd1 fd2 where
    prods: "x = (f, fd1)" "y = (f, fd2)" and "compile_fundef (load_oracle f) F fd1 = Some fd2"
    using compile_env_x
    by (cases x) (auto simp: compile_env_entry_def eq_fst_iff ap_map_prod_eq_Some_conv)

  have "rel_fundef (=) norm_eq fd1 fd2"
    using compile_env_x[unfolded prods]
    by (auto intro: rel_compile_env_entry)
  thus ?case
    using Cons.IH[OF compile_env_xs, THEN rel_fundefsD]
    unfolding prods ys_def
    unfolding Sinca.Fenv.from_list_correct Subx.Fenv.from_list_correct
    by (auto intro: rel_fundefsI)
qed

lemma rel_fundefs_compile_env:
  assumes "compile_env F1 = Some F2"
  shows "rel_fundefs (Finca_get F1) (Fubx_get F2)"
proof -
  from assms obtain xs where
    ap_map_list_F1: "ap_map_list (compile_env_entry (map_option funtype \<circ> Finca_get F1)) (Finca_to_list F1) = Some xs" and
    F2_def: "F2 = Subx.Fenv.from_list xs"
    by (auto simp: compile_env_def bind_eq_Some_conv)

  show ?thesis
    using rel_ap_map_list_ap_map_list_compile_env_entries[OF ap_map_list_F1]
    unfolding F2_def Sinca.Fenv.get_from_list_to_list
    by assumption
qed


section \<open>Compilation of program\<close>

fun compile where
  "compile (Prog F1 H f) = Some Prog \<diamondop> compile_env F1 \<diamondop> Some H \<diamondop> Some f"

lemma ap_map_list_cong:
  assumes "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x" and "xs = ys"
  shows "ap_map_list f xs = ap_map_list g ys"
  using assms
  by (induction xs arbitrary: ys) auto

lemma compile_env_wf_fundefs:
  assumes "compile_env F1 = Some F2"
  shows "Subx.wf_fundefs (Fubx_get F2)"
proof (intro Subx.wf_fundefsI allI)
  fix f
  obtain xs where
    ap_map_list_F1: "ap_map_list (compile_env_entry (map_option funtype \<circ> Finca_get F1)) (Finca_to_list F1) = Some xs" and
    F2_def: "F2 = Subx.Fenv.from_list xs"
    using assms by (auto simp: compile_env_def bind_eq_Some_conv)

  have rel_map_of_F1_xs:
    "\<And>f. rel_option (\<lambda>x y. compile_fundef (load_oracle f) (map_option funtype \<circ> Finca_get F1) x = Some y)
      (map_of (Finca_to_list F1) f) (map_of xs f)"
    using ap_map_list_F1
    by (auto simp: compile_env_entry_def ap_map_prod_eq_Some_conv
        dest: ap_map_list_imp_rel_option_map_of)

  have funtype_F1_eq_funtype_F2:
    "map_option funtype \<circ> Finca_get F1 = map_option funtype \<circ> Fubx_get F2"
  proof (rule ext, simp)
    fix x
    show "map_option funtype (Finca_get F1 x) = map_option funtype (Fubx_get F2 x)"
      unfolding F2_def Subx.Fenv.from_list_correct Sinca.Fenv.to_list_correct[symmetric]
      using rel_map_of_F1_xs[of x]
      by (cases rule: option.rel_cases)
        (simp_all add: funtype_def compile_fundef_arities compile_fundef_returns)
  qed

  show "pred_option (Subx.wf_fundef (map_option funtype \<circ> Fubx_get F2)) (Fubx_get F2 f) "
  proof (cases "map_of (Finca_to_list F1) f")
    case None
    thus ?thesis
      using rel_map_of_F1_xs[of f, unfolded None]
      by (simp add: F2_def Subx.Fenv.from_list_correct)
  next
    case (Some fd1)
    show ?thesis
      using rel_map_of_F1_xs[of f, unfolded Some option_rel_Some1]
      unfolding funtype_F1_eq_funtype_F2 F2_def Subx.Fenv.from_list_correct
      by (auto intro: wf_compile_fundef)
  qed
qed

lemma compile_load:
  assumes
    compile_p1: "compile p1 = Some p2" and
    load: "Subx.load p2 s2"
  shows "\<exists>s1. Sinca.load p1 s1 \<and> match s1 s2"
proof -
  obtain F1 H main where p1_def: "p1 = Prog F1 H main"
    by (cases p1) simp
  then obtain F2 where
    compile_F1: "compile_env F1 = Some F2" and
    p2_def: "p2 = Prog F2 H main"
    using compile_p1
    by (auto simp: ap_option_eq_Some_conv)

  note rel_F1_F2 = rel_fundefs_compile_env[OF compile_F1]

  show ?thesis
    using assms(2) unfolding p2_def Subx.load_def
  proof (cases _ _ _ s2 rule: Global.load.cases)
    case (1 fd2)
    then obtain fd1 where
      F1_main: "Finca_get F1 main = Some fd1" and rel_fd1_fd2: "rel_fundef (=) norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2]
      by auto
      
    let ?s1 = "State F1 H [allocate_frame main fd1 [] uninitialized]"

    show ?thesis
    proof (intro exI conjI)
      show "Sinca.load p1 ?s1"
        unfolding Sinca.load_def p1_def
        using 1 F1_main rel_fd1_fd2
        by (auto simp: rel_fundef_arities intro!: Global.load.intros dest: rel_fundef_body_length)
    next
      have "Subx.wf_state s2"
        unfolding 1
        using compile_F1
        by (auto intro!: Subx.wf_stateI intro: compile_env_wf_fundefs)
      then show "match ?s1 s2"
        using 1 rel_F1_F2 rel_fd1_fd2
        by (auto simp: allocate_frame_def rel_fundef_locals
            simp: rel_fundef_rel_fst_hd_bodies[OF rel_fd1_fd2 disjI2]
            intro!: match.intros rel_stacktraces.intros intro: Subx.sp_instrs.Nil)
    qed
  qed
qed

interpretation std_to_inca_compiler:
  compiler Sinca.step Subx.step "final Finca_get Inca.IReturn" "final Fubx_get Ubx.IReturn"
    Sinca.load Subx.load
    "\<lambda>_ _. False" "\<lambda>_. match" compile
using compile_load
  by unfold_locales auto

end

end