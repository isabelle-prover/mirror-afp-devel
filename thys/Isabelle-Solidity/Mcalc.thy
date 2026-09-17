theory Mcalc
  imports Solidity WP
begin

section "Weakest precondition calculus"

text \<open>Some adaptations to the general wp calculus\<close>

declare(in Contract) inv_state_def[wpsimps]
declare icall_def[wpsimps]
declare ecall_def[wpsimps]

declare(in Contract) wp_assign_stack_kdvalue[wprules del]

declare(in Contract) wp_stackCheck[wprules del]
lemma (in Contract) wp_assign_stack_kdvalue_memory[wprules]:
  assumes "Stack s $$ i = Some (kdata.Memory p)"
      and "mupdate xs (p, mdata.Value v, state.Memory s) = None \<Longrightarrow> E Err s"
      and "\<And>y. Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
         mupdate xs (p, mdata.Value v, state.Memory s) = Some y \<Longrightarrow>
         P Empty (Memory_update (K y) s)"
    shows "wp (assign_stack i xs (rvalue.Value v)) P E s"
  apply wp+
  using assms(1)
  apply (simp add:stack_check_def)
  apply wp+
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  apply wp+
  using assms by simp+

lemma (in Contract) wp_assign_stack_memory[wprules]:
  assumes "Stack s $$ i = Some (kdata.Memory p)"
      and "\<And>a list.
       Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
       is = a # list \<Longrightarrow> state.Memory s $ l = None \<Longrightarrow> E Err s"
      and "\<And>a list aa.
       Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
       is = a # list \<Longrightarrow>
       mupdate (a # list) (p, aa, state.Memory s) = None \<Longrightarrow>
       state.Memory s $ l = Some aa \<Longrightarrow> E Err s"
      and "is = [] \<Longrightarrow> P Empty (stack_update i (kdata.Memory l) s)"
      and "\<And>a list y aa.
       Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
       is = a # list \<Longrightarrow>
       mupdate (a # list) (p, aa, state.Memory s) = Some y \<Longrightarrow>
       state.Memory s $ l = Some aa \<Longrightarrow> P Empty (Memory_update (K y) s)" 
  shows "wp (assign_stack i is (rvalue.Memory l)) P E s"
  apply wp+
  using assms(1)
  apply (simp add:stack_check_def)
  apply wp+
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  apply (cases "is")
  apply wp+
  using assms apply simp
  apply wp+
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  apply wp+
  apply (cases " state.Memory s $ l")
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  using assms apply simp
  apply (cases "state.Memory s $ l")
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  using assms by simp+

declare(in Contract) wp_stackCheck[wprules]

lemma is_Array_write:
  assumes "Memory.write cd ba = (l, baa)"
      and "mlookup baa y l = Some a"
      and "baa $ a = Some b"
      and "\<exists>as. alookup y cd = Some (adata.Array as)"
    shows "mdata.is_Array b"
  using assms
proof -
  have *: "a_data.read_safe {||} baa l = Some cd"
    using write_read[OF assms(1)] by (simp add: a_data.read_def prefix_id)
  then obtain as where "a_data.read_safe {||} baa a = Some (adata.Array as)" using read_alookup_obtains[OF * assms(2)]
    using assms(4) by fastforce
  then show ?thesis using assms(3)
    by (metis assms(2) adata.distinct(1) aread_safe_def data.mlookup_read_safe mdata.collapse(1) mdata.exhaust_disc)
qed

declare(in Contract) assign_stack.simps [simp del]

section "Memory Calculus"

definition pred_memory where
  "pred_memory i P r s =
    (case (Stack s) $$ i of
      Some (kdata.Memory l) \<Rightarrow> pred_some P (aread (State.Memory s) l)
    | _ \<Rightarrow> False)"

text \<open>Needs to be used manually\<close>
lemma pred_some_read:
  assumes "aread m l = Some cd"
      and "P cd"
    shows "pred_some P (aread m l)"
  using assms unfolding pred_some_def by auto

text \<open>This destruction rule needs to be instantiated manually\<close>

lemma aliasing_1:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "is1 = is3@is4"
      and "is4 \<noteq> []"
      and "mlookup m is3 l1 = Some l3"
      and "m $ l3 = Some l4"
      and "mlookup m is2 l2 \<bind> ($) m = Some l4"
    shows "mupdate (is2 @ is4) (l2, v, m) = Some m'"
  using mlookup_append_same[OF assms(3,4,5,6)]
  by (metis assms(1,2) mupdate.simps)

lemma aliasing_2:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "is1 = is3@is4"
      and "is4 \<noteq> []"
      and "mlookup m is2 l2 = Some l3"
      and "m $ l3 = Some l4"
      and "mlookup m is3 l1 \<bind> ($) m = Some l4"
    shows "mupdate (is2 @ is4) (l2, v, m) = Some m'"
  using mlookup_append_same[OF assms(3,4,5,6)]
  by (metis assms(1,2) mupdate.simps)

subsection \<open>Safe List Lookup\<close>

lemma nth_some:
  assumes "mupdate is (l1, v, m) = Some m'"
      and "m $ l2 = Some v"
      and "the (mlookup m is l1) \<noteq> l2"
    shows "m' $ l2 = Some v"
proof -
  obtain l
    where 0: "mlookup m is l1 = Some l"
    and m'_def: "m' = m[l:=v]"
    using mvalue_update_obtain[OF assms(1)] by auto
  then have "m $ l2 = m' $ l2" using assms(3)
    by (metis length_list_update nth_list_update_neq nth_safe_def option.sel)
  then show ?thesis using assms(2) by argo
qed

subsection \<open>Rules for Memory Lookups\<close>

lemma mlookup_some_write_1:
  assumes "Memory.write a m = (l, m')"
      and "\<not>Option.is_none (alookup is a)"
    shows "mlookup m' is l = Some (the (mlookup m' is l))"
  using assms
  by (metis is_none_code(1) mlookup_some option.distinct(1) option.exhaust_sel)

lemma mlookup_some_write_2:
  assumes "Memory.write a m = (l1, m')"
      and "mlookup m is l2 = Some (the (mlookup m is l2))"
    shows "mlookup m' is l2 = Some (the (mlookup m' is l2))"
  using assms
  by (metis write_sprefix mlookup_prefix_mlookup snd_conv sprefix_prefix)

lemma mlookup_mupdate:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "mlookup m is2 l2 = Some l3"
      and "locations m is2 l2 = Some (the (locations m is2 l2))"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is2 l2)"
    shows "mlookup m' is2 l2 = Some l3"
proof -
  have m1_def: "m' = m[(the (mlookup m is1 l1)) := v]" using mvalue_update_obtain[OF assms(1)] by fastforce
  then have "mlookup m' is2 l2 = mlookup m is2 l2" using mlookup_update_val[OF assms(2) assms(3) assms(4)]
    by (simp add: assms(2))
  then show ?thesis using assms(2) by simp
qed

lemma mlookup_nth_mupdate:
  assumes "mupdate is (l, v, m) = Some m'"
      and "the (mlookup m is l) |\<notin>| the (locations m is l)"
    shows "mlookup m' is l \<bind> ($) m' = Some v"
proof -
  from assms(1) obtain ll
    where l_def: "mlookup m is l = Some ll"
      and "ll < length m"
      and "m' = m[ll:=v]"
    using mvalue_update_obtain by metis
  moreover from l_def obtain L where "locations m is l = Some L"
    using mlookup_locations_some by blast
  ultimately show ?thesis
    by (metis assms(2) bind.bind_lunit length_list_update mlookup_update_val nth_list_update_eq nth_safe_some
        option.sel)
qed

lemma mlookup_neq_write_1:
  assumes "Memory.write a m = (l1, m')"
      and "mlookup m' is1 l1 = Some l3"
      and "mlookup m is2 l2 = Some (the (mlookup m is2 l2))"
      and "the (mlookup m is2 l2) \<in> loc m"
    shows "the (mlookup m' is2 l2) \<noteq> l3"
proof -
  from assms(1) have "sprefix m m'" using write_sprefix by (metis snd_conv)
  then have "prefix m m'" using sprefix_prefix by auto
  moreover from write_arange[OF assms(1)] obtain L
    where "arange_safe {||} m' l1 = Some L"
      and *: "fset L \<inter> loc m = {}"
      unfolding s_disj_fs_def pred_some_def Utils.s_union_fs_def pred_some_def unfolding arange_safe_def arange_def data.range_def by blast
  then have "l3 |\<in>| L" using a_data.range_safe_mlookup assms(2) by blast
  with * have "l3 \<notin> loc m" by blast
  ultimately show ?thesis using assms(3,4)
    by (metis \<open>prefix m m'\<close> mlookup_prefix_mlookup)
qed

lemma mlookup_neq_write_2:
  assumes "Memory.write a m = (l, m')"
      and "mlookup m' is1 l1 = Some l3"
      and "mlookup m is2 l2 = Some (the (mlookup m is2 l2))"
      and "mlookup m is1 l1 = Some (the (mlookup m is1 l1))"
      and "\<And>l. mlookup m is1 l1 = Some l \<Longrightarrow> the (mlookup m is2 l2) \<noteq> l"
    shows "the (mlookup m' is2 l2) \<noteq> l3"
proof -
  from assms(1) have *: "prefix m m'"
    by (metis write_sprefix snd_conv sprefix_prefix)
  with assms(2,4) have "mlookup m is1 l1 = Some l3"
    by (metis mlookup_prefix_mlookup)
  with assms(5) have "the (mlookup m is2 l2) \<noteq> l3" by blast
  with * show ?thesis
    by (metis assms(3) mlookup_prefix_mlookup)
qed

lemma mlookup_neq_mupdate_2:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "mlookup m' is2 l2 = Some l4"
      and "mlookup m is2 l2 = Some (the (mlookup m is2 l2))"
      and "mlookup m is3 l3 = Some (the (mlookup m is3 l3))"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is2 l2)"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is3 l3)"
      and "\<And>l. mlookup m is2 l2 = Some l \<Longrightarrow> the (mlookup m is3 l3) \<noteq> l"
    shows "the (mlookup m' is3 l3) \<noteq> l4"
proof -
  obtain l
    where 0: "mlookup m is1 l1 = Some l"
    and m'_def: "m' = m[l:=v]"
    using mvalue_update_obtain[OF assms(1)] by auto
  moreover from assms(2,3,5,7) have "the (mlookup m is3 l3) \<noteq> l4"
    by (metis "0" m'_def mlookup_locations_some mlookup_update_val option.sel)
  ultimately show ?thesis using assms(4,6)
    by (metis mlookup_locations_some mlookup_update_val option.sel)
qed

lemma mlookup_neq_mupdate_1:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "mlookup m is2 l2 = Some l4"
      and "m $ l4 = Some v"
      and "mlookup m' is3 l3 = Some l5"
      and "is4 \<noteq> []"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is1 l1)"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m (is2 @ is4) l2)"
      and "mlookup m is3 l3 = Some (the (mlookup m is3 l3))"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is3 l3)"
      and "mlookup m (is2 @ is4) l2 = Some (the (mlookup m (is2 @ is4) l2))"
      and "\<And>l. mlookup m is3 l3 = Some l \<Longrightarrow> the (mlookup m (is2 @ is4) l2) \<noteq> l"
    shows "the (mlookup m' (is1 @ is4) l1) \<noteq> l5"
proof -
  from assms(10) obtain L where "locations m (is2 @ is4) l2 = Some L"
    using mlookup_locations_some by blast
  then obtain L' L''
    where L'_def: "locations m is2 l2 = Some L'"
      and L''_def: "locations m is4 l4 = Some L''"
      and 1: "locations m (is2 @ is4) l2 = Some (L' |\<union>| L'')"
    using locations_app_mlookup_exists[OF _ assms(2)] by force

  obtain l
    where 0: "mlookup m is1 l1 = Some l"
    and m'_def: "m' = m[l:=v]"
    and "l < length m"
  using mvalue_update_obtain[OF assms(1)] by auto
  then have *: "m' $ l = m $ l4" unfolding nth_safe_def
    by (metis assms(3) length_list_update nth_list_update_eq nth_safe_def)
  moreover
  from L'_def L''_def 1 have "\<forall>l|\<in>|the (locations m is4 l4). m $ l = m' $ l"
   using assms(1,7) 0 m'_def
   by (metis funionI2 length_list_update nth_list_update_neq nth_safe_def option.sel)
  moreover from assms(6) have "\<forall>l|\<in>|the (locations m is1 l1). m $ l = m' $ l"
    using m'_def `l < length m` unfolding nth_safe_def apply (auto)
    by (metis "0" nth_list_update_neq option.sel)
  moreover obtain ll where "mlookup m is4 l4 = Some ll"
    by (metis append_self_conv2 assms(2,10) mlookup.simps(1) mlookup_append) 
  moreover from assms(1,4,8,9) have "mlookup m is3 l3 = Some l5"
    by (metis "0" m'_def mlookup_locations_some mlookup_update_val option.sel)
  then have "ll \<noteq> l5"
    by (metis assms(2,11) bind_eq_Some_conv calculation(4) mlookup_append option.sel)
  ultimately show ?thesis using mlookup_mlookup_mlookup[OF 0 * assms(5)] by fastforce
qed

lemma mlookup_loc_write_1:
  assumes "Memory.write a m = (l, m')"
      and "\<not> Option.is_none (alookup is a)"
    shows "the (mlookup m' is l) \<in> loc m'"
proof -
  from Memory.write_loc[OF assms(1)] obtain L
    where "arange m' l = Some L"
      and "loc m' = loc m \<union> fset L"
    unfolding Utils.s_union_fs_def pred_some_def arange_safe_def arange_def data.range_def
    by blast
  moreover from mlookup_some[OF assms(1)] assms(2)
  obtain y where "mlookup m' is l = Some y"
    by force
  ultimately show ?thesis
    by (metis UnCI option.sel a_data.range_mlookup)
qed

lemma mlookup_loc_write_2:
  assumes "Memory.write a m = (l1, m')"
      and "mlookup m is l2 = Some (the (mlookup m is l2))"
      and "the (mlookup m is l2) \<in> loc m"
    shows "the (mlookup m' is l2) \<in> loc m'"
proof -
  from assms(1) have *: "prefix m m'"
    by (metis write_sprefix snd_conv sprefix_prefix)
  with assms(2,3) have "the (mlookup m' is l2) \<in> loc m"
    using mlookup_prefix_mlookup by fastforce
  then show ?thesis using * unfolding loc_def
    by (metis mem_Collect_eq nth_safe_length nth_safe_prefix nth_safe_some)
qed

lemma mlookup_nin_loc_write:
  assumes "Memory.write a m = (l, m')"
      and "mlookup m' is l = Some (the (mlookup m' is l))"
    shows "the (mlookup m' is l) \<notin> loc m"
  using assms
  by (metis mlookup.simps(1) mlookup_neq_write_1)

subsection \<open>Rules for Locations\<close>

lemma locations_write_1:
  assumes "Memory.write a m = (l, m')"
      and "\<not>Option.is_none (alookup is a)"
    shows "locations m' is l = Some (the (locations m' is l))"
  using assms
  by (metis is_none_code(2) is_none_mlookup_locations is_none_simps(1) mlookup_some_write_1 option.collapse)

lemma locations_write_2:
  assumes "Memory.write a m = (l1, m')"
      and "locations m is l2 = Some (the (locations m is l2))"
    shows "locations m' is l2 = Some (the (locations m' is l2))"
proof -
  from assms(1) have *: "prefix m m'"
    by (metis write_sprefix snd_conv sprefix_prefix)
  then have "locations m' is l2 = Some (the (locations m is l2))"
    using locations_prefix_locations[OF _ *] assms(2) by simp
  then show ?thesis by simp
qed

lemma locations_mupdate:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "the (mlookup m is1 l1) |\<notin>| (the (locations m is2 l2))"
      and "locations m is2 l2 = Some (the (locations m is2 l2))"
    shows "locations m' is2 l2 = Some (the (locations m' is2 l2))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m is1 l1 = Some l"
      and "l < length m"
      and "m' = m[l:=v]"
    using mvalue_update_obtain by metis
  then have "locations m' is2 l2 = Some (the (locations m is2 l2))"
    by (smt (verit, best) assms(1,2,3) locations_same mvalue_update_length nth_list_update_neq
        nth_safe_def option.sel)
  then show ?thesis by auto
qed

subsection \<open>Memory Lookup and Locations\<close>

lemma mlookup_locations_write_1:
  assumes "Memory.write a m = (l, m')"
      and "\<not> Option.is_none (alookup is a)"
    shows "the (mlookup m' is l) |\<notin>| the (locations m' is l)" 
  using assms locations_write_1 write_mlookup_locations mlookup_some_write_1 by blast

lemma mlookup_locations_write_2:
  assumes "Memory.write a m = (l1, m')"
      and "\<not> Option.is_none (alookup is1 a)"
      and "mlookup m is2 l2 = Some (the (mlookup m is2 l2))"
      and "the (mlookup m is2 l2) \<in> loc m"
    shows "the (mlookup m' is2 l2) |\<notin>| the (locations m' is1 l1)"
proof -
  have *: "prefix m m'" using write_sprefix[of m a] assms(1) sprefix_prefix by simp

  from write_locations_some[OF assms(1), of is1]
  obtain L' where L'_def: "locations m' is1 l1 = Some L'" using assms(2) by fastforce
  moreover obtain L where L_def: "arange m' l1 = Some L" and **: "fset L \<inter> loc m = {}"
    using write_arange[OF assms(1)] unfolding pred_some_def s_disj_fs_def by auto
  ultimately have "L' |\<subseteq>| L" using a_data.range_locations by blast
  moreover from assms(3,4) obtain l where "mlookup m is2 l2 = Some l" and ***: "l \<in> loc m" by blast
  then have "mlookup m' is2 l2 = Some l" using mlookup_prefix_mlookup * by blast
  ultimately show ?thesis using ** *** L'_def unfolding pred_some_def by auto
qed

lemma mlookup_locations_write_3:
  assumes "Memory.write a m = (l1, m')"
      and "\<not> Option.is_none (alookup is1 a)"
      and "locations m is2 l2 = Some (the (locations m is2 l2))"
    shows "the (mlookup m' is1 l1) |\<notin>| the (locations m' is2 l2)"
proof -
  have *: "prefix m m'" using write_sprefix[of m a] assms(1) sprefix_prefix by simp

  from mlookup_some[OF assms(1), of is1]
  obtain l where l_def: "mlookup m' is1 l1 = Some l" using assms(2) by fastforce
  moreover have "l \<notin> loc m"
    by (metis assms(1) l_def mlookup_nin_loc_write option.sel)
  moreover have "fset (the (locations m is2 l2)) \<subseteq> loc m" using locations_subs_loc[OF assms(3)] by blast
  ultimately show ?thesis using assms
    by (metis "*" locations_prefix_locations option.sel subsetD)
qed

lemma mlookup_locations_write_4:
  assumes "Memory.write a m = (l, m')"
    and "mlookup m is1 l1 = Some (the (mlookup m is1 l1))"
    and "locations m is2 l2 = Some (the (locations m is2 l2))"
    and "the (mlookup m is1 l1) |\<notin>| the (locations m is2 l2)"
  shows "the (mlookup m' is1 l1) |\<notin>| the (locations m' is2 l2)"
proof -
  from assms(1) have "sprefix m m'" using write_sprefix
    by (metis snd_conv)
  then have "prefix m m'" using sprefix_prefix by auto
  then have "mlookup m' is1 l1 = Some (the (mlookup m is1 l1))" using mlookup_prefix_mlookup[OF assms(2)] by simp
  moreover have "locations m' is2 l2 = Some (the (locations m is2 l2))"
    using locations_prefix_locations[OF assms(3) `prefix m m'`] by blast
  ultimately show ?thesis using assms(4) by simp
qed

lemma mlookup_locations_mupdate_1:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "mlookup m is2 l2 = Some l3"
      and "m $ l3 = Some v"
      and "is3 = i # is4"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is1 l1)"
      and "\<And>l. mlookup m (is2 @ is3) l2 = Some l
          \<Longrightarrow> mlookup m is1 l1 = Some (the (mlookup m is1 l1))
          \<Longrightarrow> the (mlookup m is1 l1) \<noteq> l"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m (is2 @ is3) l2)"
      and "the (mlookup m (is2 @ is3) l2) |\<notin>| the (locations m is1 l1)"
      and "mlookup m (is2 @ is3) l2 = Some (the (mlookup m (is2 @ is3) l2))"
      and "the (mlookup m (is2 @ is3) l2) |\<notin>| the (locations m (is2 @ is3) l2)"
    shows "the (mlookup m' (is1 @ is3) l1) |\<notin>| the (locations m' (is1 @ is3) l1)"
proof -
  from assms(9) have a0: "locations m (is2 @ is3) l2 = Some (the (locations m (is2 @ is3) l2))"
    by (simp add: mlookup_locations_some)

  obtain L L'
    where L_def: "locations m is2 l2 = Some L"
      and L'_def: "locations m is3 l3 = Some L'"
      and 1: "locations m (is2 @ is3) l2 = Some (L |\<union>| L')"
    using locations_app_mlookup_exists[OF a0 assms(2)] by (metis a0)
  from L'_def obtain l''
    where l''_def: "mlookup m [i] l3 = Some l''"
    using assms(4)
    apply (auto simp add:locations.simps mlookup.simps case_memory_def split:option.split_asm mdata.split_asm)
    apply (case_tac "vtype_class.to_nat i", auto)
    by (case_tac "x2a$a", auto)
  then obtain L''
    where L''_def: "locations m is4 (the (mlookup m [i] l3)) = Some L''"
      and 2: "L'' |\<subseteq>| L'"
    using locations_cons_mlookup_exists L'_def assms(4) by (metis option.sel)

  obtain l
    where 3: "mlookup m is1 l1 = Some l"
    and m'_def: "m' = m[l:=v]"
    and 4: "length m > l"
  using mvalue_update_obtain[OF assms(1)] by auto
  then have "m $ l3 = m' $ l" unfolding nth_safe_def
    by (metis assms(3) length_list_update nth_list_update_eq nth_safe_def)
  moreover have *: "locations m is1 l1 = Some (the (locations m is1 l1))"
    by (simp add: "3" mlookup_locations_some)
  moreover have **: "\<forall>l|\<in>|the (locations m is1 l1). m $ l = m' $ l"
    using assms(5) 3 m'_def unfolding nth_safe_def apply auto
    by (metis nth_list_update_neq)
  moreover
    have ***: "locations m is4 (the (mlookup m [i] l3))
      = Some (the (locations m is4 (the (mlookup m [i] l3))))"
      using L''_def by simp
  moreover have "\<forall>l|\<in>|the (locations m is4 (the (mlookup m [i] l3))). m $ l = m' $ l"
  proof
    fix l' assume "l' |\<in>| the (locations m is4 (the (mlookup m [i] l3)))"
    then have "l' |\<in>| the (locations m (is2 @ is3) l2)"
      using L''_def 2 1 by auto
    then show "m $ l' = m' $ l'"
      using assms(7) m'_def 3 unfolding nth_safe_def apply auto
      by (metis nth_list_update_neq)
  qed
  moreover have "mlookup m [i] l3 = Some (the (mlookup m [i] l3))"
    using l''_def by auto
  ultimately have
    "locations m' (is1 @ is3) l1
      = Some (finsert l (the (locations m is1 l1))
      |\<union>| the (locations m is4 (the (mlookup m [i] l3))))" 
    using locations_union_mlookup_nth[OF assms(4) 3 , of _ _ _  "the (locations m is1 l1)"]
    by simp
  moreover have "the (mlookup m' (is1 @ is3) l1) = the (mlookup m (is2 @ is3) l2)"
  proof -
    from L'_def L''_def 1 have "\<forall>l|\<in>|the (locations m is3 l3). m $ l = m' $ l"
      using assms(7) 3 m'_def
      by (metis funionI2 length_list_update nth_list_update_neq nth_safe_def option.sel)
    moreover from assms(2,9)
      obtain ll where "mlookup m is3 l3 = Some ll" by (simp add: mlookup_append)
    ultimately show ?thesis using mlookup_mlookup_mlookup[OF 3, of m' l3 is3 ll] \<open>m $ l3 = m' $ l\<close> ** assms(4)
      by (simp add: assms(2) mlookup_append)
  qed
  moreover from assms have "the (mlookup m (is2 @ is3) l2) |\<notin>| (finsert l (the (locations m is1 l1)))" 
    using "3" by force
  moreover have "the (mlookup m (is2 @ is3) l2) |\<notin>| the (locations m is4 (the (mlookup m [i] l3)))"
    using "1" "2" L''_def assms(10) by auto
  ultimately show ?thesis using assms(8,10) by auto
qed

lemma mlookup_locations_mupdate_2:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "mlookup m is2 l2 = Some l3"
      and "m $ l3 = Some v"
      and "is3 \<noteq> []"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is1 l1)"
      and "locations m is4 l4 = Some (the (locations m is4 l4))"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m is4 l4)"
      and "mlookup m (is2 @ is3) l2 = Some (the (mlookup m (is2 @ is3) l2))"
      and "the (mlookup m is1 l1) |\<notin>| the (locations m (is2 @ is3) l2)"
      and "the (mlookup m (is2 @ is3) l2) |\<notin>| the (locations m is4 l4)"
    shows "the (mlookup m' (is1 @ is3) l1) |\<notin>| the (locations m' is4 l4)"
proof -
  obtain l
    where 0: "mlookup m is1 l1 = Some l"
    and m'_def: "m' = m[l:=v]"
    and "l < length m"
  using mvalue_update_obtain[OF assms(1)] by auto
  then have *:"m' $ l = Some v" unfolding nth_safe_def by simp
  moreover have "l |\<notin>| the (locations m is1 l1)" using assms(5) 0 by simp
  then have **: "mlookup m' is1 l1 = Some l" using m'_def
    by (metis "0" assms(1) mlookup_locations_some mlookup_mupdate option.sel)
  moreover have "mlookup m' is2 l2 = Some (the (mlookup m is2 l2))" using assms
    by (metis funion_iff locations_app_mlookup_exists mlookup_locations_some mlookup_mupdate
        option.sel)
  then have ***: "mlookup m' is2 l2 \<bind> ($) m' = Some v" using assms(1,2)
    by (metis "*" "0" assms(3) bind.bind_lunit nth_some option.sel)
  ultimately have "mlookup m' (is1 @ is3) l1 = mlookup m' (is2 @ is3) l2" using mlookup_append_same[OF assms(4) ** * ***] by simp
  moreover from assms(8,9) 0 m'_def have "mlookup m' (is2 @ is3) l2 = mlookup m (is2 @ is3) l2"
    by (metis mlookup_locations_some mlookup_update_val option.sel)
  moreover from assms(7,8) 0 m'_def have "\<forall>l|\<in>|the (locations m is4 l4). m' $ l = m $ l" unfolding nth_safe_def apply (auto)
    by (metis nth_list_update_neq)
  with assms(6,7) 0 m'_def have "the (locations m' is4 l4) = the (locations m is4 l4)"
    by (metis locations_same)
  ultimately show ?thesis by (simp add: assms(10))
qed

subsection \<open>Rules for Range\<close>

lemma range_range_write_1:
  assumes "Memory.write a m = (l, m')"
    shows "arange m' l = Some (the (arange m' l))"
  using Memory.write_loc[OF assms(1)] unfolding s_union_fs_def pred_some_def by auto

lemma range_range_write_2:
  assumes "Memory.write a m = (l1, m')"
    and "arange m l2 = Some (the (arange m l2))"
  shows "arange m' l2 = Some (the (arange m' l2))"
proof -
  from assms(1) have "prefix m m'"
    by (metis write_sprefix snd_eqD sprefix_prefix)
  then show ?thesis
    by (metis assms(2) a_data.range_prefix)
qed

lemma range_some_mupdate_value:
  assumes "mupdate is (l, mdata.Value v, m) = Some m'"
      and "arange m l = Some (the (arange m l))"
    shows "arange m' l = Some (the (arange m' l))"
  using assms
    a_data.mupdate_range_subset[of m l m' _ "v"]
    mvalue_update_obtain[OF assms(1)]
  apply (cases "mlookup m is l")
  apply (auto simp add: mupdate.simps list_update_safe_def split:if_split_asm)
  by fastforce

lemma range_some_mupdate_1:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "mlookup m is2 l2 = Some l3"
      and "m $ l3 = Some v"
      and "adisjoint m (the (arange m l1))"
      and "the (arange m l1) |\<inter>| the (arange m l2) = {||}"
      and "arange m l2 = Some (the (arange m l2))"
      and "arange m l1 = Some (the (arange m l1))"
    shows "arange m' l1 = Some (the (arange m' l1))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m is1 l1 = Some l"
    and *: "l < length m"
    and **: "m' = m[l:=v]" using mvalue_update_obtain by metis
  then have 0: "m' $ l = m $ l3" by (simp add: assms(3))
  moreover from assms(7) obtain L1 where L1_def: "arange m l1 = Some L1" by simp
  moreover from assms(2,6) obtain L2 where L2_def: "arange m l3 = Some L2" and *: "L2 |\<subseteq>| the (arange m l2)"
    by (metis a_data.range_def a_data.range_safe_mlookup_range)
  moreover from L1_def obtain L1' where "arange m l = Some L1'" using l_def
    by (metis a_data.range_def a_data.range_safe_mlookup_range)
  moreover have "\<forall>l|\<in>|L1 |-| L1'. m' $ l = m $ l"
  proof
    fix l' assume "l' |\<in>|L1 |-| L1'"
    moreover have "l |\<notin>| L1 |-| L1'"
      by (meson \<open>arange m l = Some L1'\<close> fminusD2 a_data.range_subs)
    ultimately have "l \<noteq> l'" by blast
    then show "m' $ l' = m $ l'" unfolding nth_safe_def using ** by simp
  qed
  moreover have "\<forall>l|\<in>|L2. m' $ l = m $ l"
  proof
    fix l' assume "l'|\<in>|L2"
    moreover have "l |\<in>|L1"
      using L1_def l_def a_data.range_mlookup by blast
    ultimately have "l \<noteq> l'" using assms(5) L1_def L2_def * by auto
    then show "m' $ l' = m $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover from assms(4) have "adisjoint m L1" using L1_def by auto
  moreover have "the (locations m is1 l1) |\<inter>| L2 = {||}"
  proof -
    from l_def obtain LL where "locations m is1 l1 = Some LL"
      using mlookup_locations_some by blast
    then have "LL |\<subseteq>| L1" using L1_def using a_data.range_locations by blast
    then show ?thesis using assms(5) *
      using L1_def \<open>locations m is1 l1 = Some LL\<close> by auto
  qed
  moreover have "l |\<notin>| L2"
  proof -
    have "l |\<in>| L1"
      using L1_def l_def a_data.range_mlookup by blast
    then show ?thesis using assms(5) * L2_def L1_def by auto
  qed
  ultimately show ?thesis using range_update_some[OF l_def 0, of L1 L1' L2] by simp
qed

lemma range_some_mupdate_2:
  assumes "mupdate is (l1, v, m) = Some m'"
    and "the (mlookup m is l1) |\<notin>| the (arange m l2)"
    and "arange m l2 = Some (the (arange m l2))"
  shows "arange m' l2 = Some (the (arange m' l2))"
proof -
  obtain l'
    where 0: "mlookup m is l1 = Some l'"
    and m'_def: "m' = m[l':=v]"
  using mvalue_update_obtain[OF assms(1)] by auto
  moreover from assms(2) have "\<forall>l''|\<in>|the (arange m l2). m' $ l'' = m $ l''"
    using 0 m'_def unfolding nth_safe_def apply (simp split:if_split_asm)
    by (metis nth_list_update_neq)
  ultimately show ?thesis using a_data.range_same[of m l2] by (metis assms(3))
qed

lemma range_range_disj_write:
  assumes "Memory.write a m = (l1, m')"
    and "arange m l2 = Some (the (arange m l2))"
  shows "the (arange m' l2) |\<inter>| the (arange m' l1) = {||}"
proof -
  from assms(1) have "prefix m m'"
    by (metis write_sprefix snd_eqD sprefix_prefix)
  moreover from assms(2) have "fset (the (arange m l2)) \<subseteq> loc m" using a_data.range_subs2 by auto
  ultimately have "fset (the (arange m' l2)) \<subseteq> loc m"
    by (metis assms(2) a_data.range_prefix)
  then show ?thesis using write_arange[OF assms(1)] unfolding s_disj_fs_def pred_some_def
    by auto
qed

lemma range_disj_write:
assumes "Memory.write a m = (l1, m')"
    and "arange m l2 = Some (the (arange m l2))"
    and "arange m l3 = Some (the (arange m l3))"
    and "the (arange m l2) |\<inter>| the (arange m l3) = {||}"
  shows "the (arange m' l2) |\<inter>| the (arange m' l3) = {||}"
proof -
  from assms(1) have "prefix m m'"
    by (metis write_sprefix snd_conv sprefix_prefix)
  moreover from assms(2) obtain L where "arange m l2 = Some L" by blast
  ultimately have "arange m' l2 = Some L" using a_data.range_prefix by auto
  moreover from assms(3) obtain L' where L'_def: "arange m l3 = Some L'" by blast
  moreover have "arange m' l3 = Some L'" using L'_def `prefix m m'` a_data.range_prefix by auto
  ultimately show ?thesis using assms(4)
    by (simp add: \<open>arange m l2 = Some L\<close>)
qed

lemma range_disj_mupdate:
  assumes "mupdate is1 (l1, v, m) = Some m'"
      and "mlookup m is2 l2 = Some l3"
      and "m $ l3 = Some v"
      and "arange m l1 = Some (the (arange m l1))"
      and "arange m l2 = Some (the (arange m l2))"
      and "arange m l4 = Some (the (arange m l4))"
      and "the (arange m l1) |\<inter>| the (arange m l2) = {||}"
      and "the (mlookup m is1 l1) |\<notin>| the (arange m l4)"
      and "adisjoint m (the (arange m l1))"
      and "the (arange m l1) |\<inter>| the (arange m l4) = {||}"
      and "the (arange m l2) |\<inter>| the (arange m l4) = {||}"
    shows "the (arange m' l1) |\<inter>| the (arange m' l4) = {||}"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m is1 l1 = Some l"
    and *: "l < length m"
    and **: "m' = m[l:=v]" using mvalue_update_obtain by metis
  then have 0: "m' $ l = m $ l3" by (simp add: assms(3))
  moreover obtain L0 where "arange m' l1 = Some L0" using range_some_mupdate_1[OF assms(1,2,3,9,7,5,4)] by simp
  moreover from assms(4) obtain L1 where L1_def: "arange m l1 = Some L1" by simp
  moreover from assms(5) obtain L2 where L2_def: "arange m l3 = Some L2" and ***: "L2 |\<subseteq>| the (arange m l2)"
    by (metis assms(2) a_data.range_def a_data.range_safe_mlookup_range)
  moreover have "arange m l = Some (the (arange m l))"
    by (metis L1_def l_def option.sel a_data.range_def a_data.range_safe_mlookup_range)
  moreover have "\<forall>l|\<in>|L1 |-| the (arange m l). m' $ l = m $ l" using ** unfolding nth_safe_def apply (simp split:if_split_asm)
    by (metis Diff_iff calculation(6) nth_list_update_neq a_data.range_subs)
  moreover have "\<forall>l|\<in>|the (arange m l2). m' $ l = m $ l"
  proof
    fix l' assume "l'|\<in>|the (arange m l2)"
    moreover from l_def have "l|\<in>|the (arange m l1)" using a_data.range_mlookup[OF L1_def] L1_def by simp
    ultimately have "l' \<noteq> l" using assms(7) L1_def L2_def by auto
    then show "m' $ l' = m $ l'" using ** unfolding nth_safe_def by simp
  qed
  then have "\<forall>l|\<in>|L2. m' $ l = m $ l" using *** by blast
  moreover from assms(9) have "adisjoint m L1" using L1_def by simp
  ultimately have "L0 |\<subseteq>| L1 |\<union>| L2" using range_update_subs[OF l_def 0, of L1 "the (arange m l)" L2 L0] by blast
  moreover have "L2 |\<subseteq>| the (arange m l2)"
    by (metis \<open>arange m l3 = Some L2\<close> assms(2,5) a_data.range_def a_data.mlookup_range_safe_subs)
  moreover have "the (arange m l4) = the (arange m' l4)"
  proof -
    obtain L where L_def: "arange m l4 = Some L" using assms(6) by simp
    moreover from assms(8) ** * have "\<forall>l |\<in>| L. m$l = m'$l" unfolding nth_safe_def l_def apply (auto split:if_split_asm)
      by (metis calculation nth_list_update_neq option.sel)
    ultimately have "arange m' l4 = Some L"
      by (metis a_data.range_same)
    then show ?thesis using L_def by simp
  qed
  ultimately show ?thesis using assms(10,11)
    using \<open>arange m' l1 = Some L0\<close> L1_def by auto
qed

lemma mlookup_range_write_1:
  assumes "Memory.write a m = (l1, m')"
      and "mlookup m is l2 = Some (the (mlookup m is l2))"
      and "the (mlookup m is l2) \<in> loc m"
    shows "the (mlookup m' is l2) |\<notin>| the (arange m' l1)"
proof -
  from assms(1) obtain L where L_def: "arange m' l1 = Some L"
    using range_range_write_1 by blast
  then have "fset L \<inter> loc m = {}"
    by (metis Diff_disjoint Memory.write_loc assms(1) inf_commute write_arange option.sel s_disj_union_fs)
  moreover from assms(1) have "prefix m m'"
    by (metis write_sprefix snd_conv sprefix_prefix)
  with assms(2) have "the (mlookup m' is l2) = the (mlookup m is l2)"
    by (metis mlookup_prefix_mlookup)
  ultimately show ?thesis using L_def assms by auto
qed

lemma mlookup_range_write_3:
  assumes "Memory.write a m = (l1, m')"
      and "mlookup m is l2 = Some (the (mlookup m is l2))"
      and "arange m l3 = Some (the (arange m l3))"
      and "the (mlookup m is l2) |\<notin>| the (arange m l3)"
    shows "the (mlookup m' is l2) |\<notin>| the (arange m' l3)"
proof -
  from assms(1) have "prefix m m'"
    by (metis write_sprefix snd_conv sprefix_prefix)
  then have "the (mlookup m is l2) = the (mlookup m' is l2)"
    by (metis assms(2) mlookup_prefix_mlookup)
  moreover have "the (arange m l3) = the (arange m' l3)"
    by (metis \<open>prefix m m'\<close> assms(3) a_data.range_prefix)
  ultimately show ?thesis using assms(4) by simp
qed

lemma mlookup_range_write_2:
  assumes "Memory.write a m = (l1, m')"
      and "\<not> Option.is_none (alookup is a)"
      and "arange m l2 = Some (the (arange m l2))"
    shows "the (mlookup m' is l1) |\<notin>| the (arange m' l2)"
proof -
  from mlookup_some[OF assms(1), of "is"]
  obtain l where l_def: "mlookup m' is l1 = Some l" using assms(2) by fastforce
  moreover have "l \<notin> loc m"
    by (metis assms(1) l_def mlookup_nin_loc_write option.sel)
  moreover from assms obtain L where "arange m' l2 = Some L" and "fset L \<subseteq> loc m"
    by (smt (verit) arange_def mlookup.simps(1) mlookup_range_write_3 option.sel range_range_write_2
        range_storage_def storage_data.range_subs2 subset_iff)
  ultimately show ?thesis by auto
qed

subsection \<open>Rules for Read\<close>

corollary write_read_1:
  assumes "Memory.write a m = (l, m')"
  shows "aread m' l = Some a"
  using Memory.write_read assms by blast

lemma write_read_2:
  assumes "Memory.write a2 m = (l2, m')"
      and "aread m l1 = Some a1"
    shows "aread m' l1 = Some a1"
  using assms
  by (metis write_sprefix a_data.read_append snd_conv sprefix_prefix)

lemma read_mupdate_value:
  assumes "mupdate is (l, mdata.Value v, m) = Some m'"
      and "adisjoint m (the (arange m l))"
      and "aread m l = Some a"
    shows "aread m' l = Some (the (aupdate is (adata.Value v) a))" 
proof-
  from assms(1) obtain ll
    where l_def: "mlookup m is l = Some ll"
    and *: "ll < length m"
    and **: "m' = m[ll:=mdata.Value v]" using mvalue_update_obtain by metis
  moreover have 1: "arange_safe {||} m l = Some (the (arange_safe {||} m l))" using a_data.range_read_some
    by (metis assms(3) option.sel a_data.read_def)
  moreover have 2: "arange_safe {||} m ll = Some (the (arange_safe {||} m ll))"
    by (metis "1" l_def option.sel a_data.range_def a_data.range_safe_mlookup_range)
  moreover have 3: "\<forall>l'|\<in>|the (arange_safe {||} m l) |-| (the (arange_safe {||} m ll)). m' $ l' = m $ l'"
  proof
    fix l' assume "l' |\<in>|the (arange_safe {||} m l) |-| (the (arange_safe {||} m ll))"
    moreover have "ll |\<notin>| the (arange_safe {||} m l) |-| (the (arange_safe {||} m ll))"
      by (meson "2" fminusD2 a_data.range_safe_subs)
    ultimately have "ll \<noteq> l'" by blast
    then show " m' $ l' = m $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover from assms(2) have 4: "aread_safe {||} m l = Some (the (aread_safe {||} m l))"
    by (metis assms(3) option.sel a_data.read_def)
  moreover from assms obtain cd' where 6: "aread_safe {||} m' l = Some cd'"
    by (metis mvalue_update_obtain a_data.read_safe_update_value
        a_data.read_def)
  ultimately show ?thesis using read_safe_lookup_update_value[OF l_def * ** 1 ]
    by (metis assms(2,3) option.distinct(1) option.exhaust_sel a_data.read_def a_data.range_def)
qed

lemma read_mupdate_1:
  assumes "mupdate is1 (l1, l4, m) = Some m'"
      and "mlookup m is2 l2 = Some l3"
      and "m $ l3 = Some l4"
      and "adisjoint m (the (arange m l1))"
      and "the (arange m l1) |\<inter>| the (arange m l2) = {||}"
      and "aread m l1 = Some a1"
      and "aread m l2 = Some a2"
    shows "aread m' l1 = Some (the (alookup is2 a2 \<bind> (\<lambda>cd. aupdate is1 cd a1)))"
proof-
  from assms(1) obtain ll
    where l_def: "mlookup m is1 l1 = Some ll"
    and *: "ll < length m"
    and **: "m' = m[ll:=l4]" using mvalue_update_obtain by metis
  then have 0: "m' $ ll = m $ l3" by (simp add: assms(3))
  moreover have 1: "arange_safe {||} m l1 = Some (the (arange_safe {||} m l1))" using a_data.range_read_some
    by (metis assms(6) option.sel a_data.read_def)
  moreover have 2: "arange_safe {||} m ll = Some (the (arange_safe {||} m ll))"
    by (metis "1" l_def option.sel a_data.range_def a_data.range_safe_mlookup_range)
  moreover have 3: "arange_safe {||} m l2= Some (the (arange_safe {||} m l2))"  using a_data.range_read_some
    by (metis assms(7) option.sel a_data.read_def)
  moreover have 4: "\<forall>l|\<in>|the (arange_safe {||} m l1) |-| the (arange_safe {||} m ll). m' $ l = m $ l"
  proof
    fix l' assume "l' |\<in>|the (arange_safe {||} m l1) |-| (the (arange_safe {||} m ll))"
    moreover have "ll |\<notin>| the (arange_safe {||} m l1) |-| (the (arange_safe {||} m ll))"
      by (meson "2" fminusD2 a_data.range_safe_subs)
    ultimately have "ll \<noteq> l'" by blast
    then show "m' $ l' = m $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover have 5: "\<forall>l|\<in>|the (arange_safe {||} m l3). m' $ l = m $ l"
  proof
    fix ll' assume "ll'|\<in>| the (arange_safe {||} m l3)"
    moreover have "ll |\<in>| the (arange_safe {||} m l1)"
      by (metis "1" data.range_safe_mlookup l_def arange_safe_def)
    moreover have 3: "arange_safe {||} m l3= Some (the (arange_safe {||} m l3))"  using a_data.range_read_some
      by (metis assms(2,7) data.range_safe_mlookup data.range_safe_in_subs arange_safe_def option.sel a_data.read_def)
    ultimately have "ll \<noteq> ll'" using assms(5)
      by (smt (verit, ccfv_SIG) "3" assms(2,7) data.mlookup_range_safe_subs disjoint_iff_fnot_equal finsert_fsubset
          arange_safe_def mk_disjoint_finsert option.sel a_data.read_def a_data.range_read_some
          a_data.range_def)
    then show "m' $ ll' = m $ ll'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover have 6: "locations m is1 l1 = Some (the (locations m is1 l1))"
    by (simp add: l_def mlookup_locations_some)
  moreover have 7: "the (locations m is1 l1) |\<inter>| the (arange_safe {||} m l3) = {||}"
  proof -
    have "the (locations m is1 l1) |\<subseteq>| the (arange m l1)"
      by (metis "1" "6" a_data.range_def a_data.range_safe_locations)
    moreover have "the (arange_safe {||} m l3) |\<subseteq>| the (arange_safe {||} m l2)"
      by (metis "3" assms(2) option.sel a_data.range_def a_data.range_safe_mlookup_range)
    ultimately show ?thesis using assms(5)
      by (metis (no_types, lifting) ext boolean_algebra_cancel.inf1 inf.order_iff inf_bot_right inf_commute
          a_data.range_def)
  qed
  moreover have 8: "ll |\<notin>| the (arange_safe {||} m l3)" using assms(5)
  proof -
    have "ll |\<in>| the (arange_safe {||} m l1)"
      by (metis "1" data.range_safe_mlookup l_def arange_safe_def)
    moreover have 3: "arange_safe {||} m l3= Some (the (arange_safe {||} m l3))"  using a_data.range_read_some
      by (metis assms(2,7) data.range_safe_mlookup data.range_safe_in_subs arange_safe_def option.sel a_data.read_def)
    ultimately show ?thesis using assms(5)
      by (smt (verit, ccfv_SIG) "3" assms(2,7) data.mlookup_range_safe_subs disjoint_iff_fnot_equal finsert_fsubset
          arange_safe_def mk_disjoint_finsert option.sel a_data.read_def a_data.range_read_some
          a_data.range_def)
  qed
  moreover have "arange_safe {||} m l3= Some (the (arange_safe {||} m l3))"  using a_data.range_read_some
      by (metis assms(2,7) data.range_safe_mlookup data.range_safe_in_subs arange_safe_def option.sel a_data.read_def)
  ultimately obtain cd' where 9: "aread_safe {||} m' l1 = Some cd'"
    using a_data.update_some_obtains_read[OF l_def 0 1 2 _ 4 5 _ _ _ 6 7 8] assms(4,6,7) 
    by (metis inf_bot_left a_data.read_def a_data.range_def
        a_data.range_safe_read_safe)
  moreover have "\<forall>l|\<in>|the (arange_safe {||} m l2). m' $ l = m $ l"
  proof
    fix l' assume "l'|\<in>| the (arange_safe {||} m l2)"
    moreover have "ll |\<in>| the (arange_safe {||} m l1)"
      by (metis "1" data.range_safe_mlookup l_def arange_safe_def)
    moreover have 3: "arange_safe {||} m l3= Some (the (arange_safe {||} m l3))"  using a_data.range_read_some
      by (metis assms(2,7) data.range_safe_mlookup data.range_safe_in_subs arange_safe_def option.sel a_data.read_def)
    ultimately have "ll \<noteq> l'" using assms(5) by (metis disjoint_iff_fnot_equal a_data.range_def)
    then show "m' $ l' = m $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover from assms(6) have "aread_safe {||} m l1 = Some a1"
    by (simp add: a_data.read_def)
  moreover from assms(7) have "aread_safe {||} m l2 = Some a2"
    by (simp add: a_data.read_def)
  moreover have "adisjoint m (the (arange_safe {||} m l1))"
    by (metis assms(4) a_data.range_def)
  ultimately show ?thesis using read_safe_lookup_update[OF l_def assms(2) 0 1 2 3 4 ]
    by (metis option.sel a_data.read_def)
qed

lemma read_mupdate_2:
  assumes "mupdate is (l1, v, m) = Some m'"
      and "the (mlookup m is l1) |\<notin>| the (arange m l2)"
      and "aread m l2 = Some a"
    shows "aread m' l2 = Some a"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m is l1 = Some l"
    and *: "l < length m"
    and **: "m' = m[l:=v]" using mvalue_update_obtain by metis
  moreover from assms(3) obtain L where L_def: "arange m l2 = Some L"
    by (metis a_data.read_def a_data.range_read_some a_data.range_def)
  moreover from assms(2) ** L_def l_def have "\<forall>l |\<in>| L. m' $ l = m $ l" unfolding nth_safe_def
    apply (simp add: split:if_split_asm)
    by (metis nth_list_update_neq)
  ultimately show ?thesis using Memory.a_data.read_range[OF assms(3)] by blast
qed

subsection \<open>Rules for Disjointness\<close>

lemma disjoint_range_write_1:
  assumes "Memory.write a m = (l, m')"
    shows "adisjoint m' (the (arange m' l))"
proof -
  from assms(1) obtain L where "arange m' l = Some L" using range_range_write_1 by blast
  then show ?thesis using write_adisjoint[OF assms(1)]
    by (metis option.sel)
qed

lemma disjoint_range_write_2:
  assumes "Memory.write a m = (l2, m')"
      and "arange m l1 = Some (the (arange m l1))"
      and "adisjoint m (the (arange m l1))"
    shows "adisjoint m' (the (arange m' l1))"
proof -
  from assms(1) have "prefix m m'"
    by (metis write_sprefix snd_eqD sprefix_prefix)
  moreover have "fset (the (arange m l1)) \<subseteq> loc m" using a_data.range_subs2 assms(2) by blast
  ultimately have "adisjoint m' (the (arange m l1))" using a_data.disjoint_prefix[OF _ _ assms(3)] assms(2)
    by (metis a_data.range_def a_data.range_prefix)
  then show ?thesis
    by (metis \<open>prefix m m'\<close> assms(2) data.range_prefix arange_def)
qed

lemma disjoint_mupdate_value:
  assumes "mupdate is (l, mdata.Value v, m) = Some m'"
      and "arange m l = Some (the (arange m l))"
      and "adisjoint m (the (arange m l))"
    shows "adisjoint m' (the (arange m' l))"
unfolding a_data.disjoint_def
proof (rule, rule, rule)
  fix x xs
  assume 1: "x |\<in>| the (arange m' l)"
     and 2: "m' $ x = Some (mdata.Array xs)"

  from assms(1) obtain ll
    where l_def: "mlookup (m) is l = Some ll"
    and "ll < length (m)"
    and yg_def: "m' = (m)[ll:= mdata.Value v]"
    using mvalue_update_obtain by metis

  then obtain LL
    where "arange m' l = Some LL"
      and "LL |\<subseteq>| the (arange (m) l)"
    using assms(2) a_data.mupdate_range_subset[of "(m)" l m' ll]
    by blast

  then have 3: "x |\<in>| the (arange (m) l)" using 1 by auto
  moreover have 4: "m $ x = Some (mdata.Array xs)" using 2 yg_def
    apply (auto simp add:nth_safe_def split:if_split_asm)
    by (metis mdata.distinct(1) nth_list_update_eq nth_list_update_neq)

  ultimately have 5:
    "(\<forall>i j i' j' L L'.
        i \<noteq> j \<and>
        xs $ i = Some i' \<and>
        xs $ j = Some j' \<and>
        arange (m) i' = Some L \<and> arange (m) j' = Some L'
      \<longrightarrow> L |\<inter>| L' = {||})"
    using assms(3) by (auto simp add:a_data.disjoint_def)

  show "\<forall>i j i' j' L L'.
          i \<noteq> j \<and> xs $ i = Some i' \<and> xs $ j = Some j'
          \<and> arange m' i' = Some L \<and> arange m' j' = Some L'
        \<longrightarrow> L |\<inter>| L' = {||}"
  proof (rule, rule, rule, rule, rule, rule, rule, (erule conjE)+)
    fix i j i' j' L L'
    assume "i \<noteq> j"
       and "xs $ i = Some i'"
       and "xs $ j = Some j'"
       and L_def: "arange m' i' = Some L"
       and L'_def: "arange m' j' = Some L'"
    have 1: "arange (m) i' = Some (the (arange (m) i'))"
      by (metis (lifting) 3 4 \<open>xs $ i = Some i'\<close> assms(2) option.sel a_data.range_def a_data.range_safe_in_range)
    have 2: "arange (m) j' = Some (the (arange (m) j'))"
      by (metis (lifting) 3 4 \<open>xs $ j = Some j'\<close> assms(2) option.sel a_data.range_def a_data.range_safe_in_range)
    from 1 have "L |\<subseteq>| the (arange (m) i')"
      using L_def yg_def \<open>ll < length (m)\<close>
        a_data.mupdate_range_subset[of "(m)" i' m' ll v]
      by auto
    moreover from 2 have "L' |\<subseteq>| the (arange (m) j')"
      using L'_def yg_def \<open>ll < length (m)\<close>
        a_data.mupdate_range_subset[of "(m)" j' m' ll v] 
      by auto
    moreover have
      "the (arange (m) i') |\<inter>| the (arange (m) j') = {||}"
      using 1 2 5 \<open>i \<noteq> j\<close> \<open>xs $ i = Some i'\<close> \<open>xs $ j = Some j'\<close> by auto
    ultimately show "L |\<inter>| L' = {||}" by auto
  qed
qed

lemma disjoint_mupdate_1:
  assumes "mupdate is1 (l1, l4, m) = Some m'"
      and "mlookup m is2 l2 = Some l3"
      and "m $ l3 = Some l4"
      and "arange m l1 = Some (the (arange m l1))"
      and "adisjoint m (the (arange m l1))"
      and "arange m l2 = Some (the (arange m l2))"
      and "adisjoint m (the (arange m l2))"
      and "the (arange m l1) |\<inter>| the (arange m l2) = {||}"
    shows "adisjoint m' (the (arange m' l1))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m is1 l1 = Some l"
    and *: "l < length m"
    and **: "m' = m[l:=l4]" using mvalue_update_obtain by metis
  then have 0: "m' $ l = m $ l3" by (simp add: assms(3))
  moreover have 2: "arange_safe {||} m l = Some (the (arange_safe {||} m l))"
    by (metis assms(4) l_def option.sel a_data.range_def a_data.range_safe_mlookup_range)
  moreover have 4: "\<forall>l|\<in>|the (arange_safe {||} m l1) |-| the (arange_safe {||} m l). m' $ l = m $ l"
  proof
    fix l' assume "l' |\<in>|the (arange_safe {||} m l1) |-| (the (arange_safe {||} m l))"
    moreover have "l |\<notin>| the (arange_safe {||} m l1) |-| (the (arange_safe {||} m l))"
      by (meson "2" fminusD2 a_data.range_safe_subs)
    ultimately have "l \<noteq> l'" by blast
    then show "m' $ l' = m $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover have "\<forall>l|\<in>|the (arange_safe {||} m l2). m' $ l = m $ l"
  proof
    fix l' assume "l'|\<in>| the (arange_safe {||} m l2)"
    moreover have "l |\<in>| the (arange_safe {||} m l1)"
      by (metis assms(4) l_def a_data.range_def a_data.range_mlookup)
    ultimately have "l \<noteq> l'" using assms(5,8)
      by (metis fempty_iff finterI a_data.range_def)
    then show "m' $ l' = m $ l'" unfolding nth_safe_def using ** by simp
  qed
  then have 5: "\<forall>l|\<in>|the (arange_safe {||} m l3). m' $ l = m $ l"
    by (metis assms(2,6) fsubsetD option.sel a_data.range_def a_data.range_safe_mlookup_range)
  moreover have 6: "locations m is1 l1 = Some (the (locations m is1 l1))"
    by (simp add: l_def mlookup_locations_some)
  moreover have "the (locations m is1 l1) |\<inter>| the (arange_safe {||} m l2) = {||}"
    by (smt (verit, best) "6" assms(4,8) finter_absorb1 finter_assoc finter_commute finter_fempty_left a_data.range_def
        a_data.range_locations)
  then have 7: "the (locations m is1 l1) |\<inter>| the (arange_safe {||} m l3) = {||}"
    by (smt (verit, best) assms(2,6) fsubset_fempty inf.cobounded1 inf.cobounded2 inf.order_iff inf_mono
        option.sel a_data.range_def a_data.range_safe_mlookup_range)
  moreover have "l |\<notin>| the (arange_safe {||} m l2)" using assms(5)
    by (metis assms(4,8) disjoint_iff_fnot_equal l_def a_data.range_def a_data.range_mlookup)
  then have 8: "l |\<notin>| the (arange_safe {||} m l3)"
    by (metis assms(2,6) finterD1 inf.absorb_iff2 option.sel a_data.range_def
        a_data.range_safe_mlookup_range)
  moreover have 9: "arange_safe {||} m l1 = Some (the (arange_safe {||} m l1))"
    by (metis assms(4) a_data.range_def)
  ultimately obtain L where L_def: "arange_safe {||} m' l1 = Some L"
    using a_data.update_some_obtains_range[OF l_def 0 _ 2 _ 4 5 _ 6 7 8 ] assms(5)
    by (metis assms(2,6) finter_fempty_left option.sel a_data.range_def a_data.range_safe_mlookup_range)
  
  moreover from 9 have 9: "data.range_safe {||} m l1 = Some (the (data.range_safe {||} m l1))"
    by (metis arange_safe_def)
  moreover from 2 have 2: "data.range_safe {||} m l = Some (the (arange_safe {||} m l))"
    by (metis arange_safe_def)
  moreover have 10: "data.range_safe {||} m l3 = Some (the (data.range_safe {||} m l3))"
    by (metis assms(2,6) data.range_safe_mlookup_range arange_def arange_safe_def option.sel
        a_data.range_def)
  moreover from 4 have 4: "\<forall>l|\<in>|the (data.range_safe {||} m l1) |-| the (arange_safe {||} m l). m' $ l = m $ l"
    by (metis arange_safe_def)
  moreover from 5 have 5: "\<forall>l|\<in>|the (data.range_safe {||} m l3). m' $ l = m $ l"
    by (metis arange_safe_def)
  moreover have 11: "storage_data.disjoint m (the (data.range_safe {||} m l1))"
    by (metis assms(5) adisjoint_def data.range_def arange_def)
  moreover have 12: "storage_data.disjoint m (the (data.range_safe {||} m l3))"
  proof -
    from assms(7) have "storage_data.disjoint m (the (arange m l2))"
      by (simp add: adisjoint_def)
    with 10 show ?thesis
      by (metis (no_types, lifting) assms(2,6) adisjoint_def data.range_safe_mlookup_range arange_def
          arange_safe_def option.sel a_data.disjoint_subs a_data.range_def)
  qed
  moreover from L_def have 13: "data.range_safe {||} m' l1 = Some L"
    by (metis arange_safe_def)
  moreover have "the (data.range_safe {||} m l1) |-| the (arange_safe {||} m l) |\<inter>| the (data.range_safe {||} m l3) =
    {||}"
  proof -
    from assms(8) have "the (data.range_safe {||} m l1) |\<inter>| the (data.range_safe {||} m l2) = {||}"
      by (simp add: arange_safe_def a_data.range_def)
    then have "the (data.range_safe {||} m l1) |\<inter>| the (data.range_safe {||} m l3) = {||}"
      by (smt (verit, best) "10" assms(2,6) disjoint_iff_fnot_equal fsubsetD arange_safe_def range_storage_safe_def
          a_data.range_def storage_data.mlookup_range_safe_subs)
    then show ?thesis by blast
  qed
  ultimately have "storage_data.disjoint m' L" using data.disjoint_update [OF l_def 0 9 2 10 4 5 11 12 13] by blast
  then show ?thesis
    by (simp add: "13" adisjoint_def data.range_def arange_def)
qed

lemma disjoint_mupdate_2:
  assumes "mupdate is (l1, v, m) = Some m'"
      and "arange m l2 = Some (the (arange m l2))"
      and "the (mlookup m is l1) |\<notin>| the (arange m l2)"
      and "adisjoint m (the (arange m l2))"
    shows "adisjoint m' (the (arange m' l2))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m is l1 = Some l"
    and *: "l < length m"
    and **: "m' = m[l:=v]" using mvalue_update_obtain by metis
  
  from assms(2) obtain L where L_def: "arange m l2 = Some L" by blast
  moreover from assms(3) l_def * ** have "\<forall>l'|\<in>|L. m' $ l' = m $ l'" unfolding nth_safe_def apply (auto split:if_split)
    by (metis calculation nth_list_update_neq option.sel)
  ultimately have *: "arange m' l2 = Some L" using assms(3) a_data.range_same[of m l2 L] by blast
  then have "\<forall>l|\<in>|the (arange m l2). m $ l = m' $ l" using L_def
    by (simp add: \<open>\<forall>l'|\<in>|L. m' $ l' = m $ l'\<close>)
  then have "adisjoint m' (the (arange m l2))" using a_data.disjoint_disjoint[OF assms(4,2)] by blast
  then show ?thesis using * L_def by auto 
qed

subsection \<open>Value Array\<close>

text \<open>Needs to be used manually\<close>
lemma isValue_isArray_all:
  assumes "mdata.is_Value aa"
      and "mlookup m0 xs l0 = Some ya"
      and "m0 $ ya = Some aa"
      and "aread m0 l0 = Some cd"
      and "adata.is_Array (the (alookup xs cd))"
  shows thesis
proof -
  from read_alookup_obtains[OF _ assms(2), of "{||}" cd]
  obtain cd' where "aread_safe {||} m0 ya = Some cd'" and "alookup xs cd = Some cd'"
    using assms(4) unfolding a_data.read_def by blast
  with assms(1,3) have "adata.is_Value cd'" by (auto simp add:case_memory_def split:option.split mdata.split_asm)
  then show ?thesis using assms
    by (simp add: \<open>alookup xs cd = Some cd'\<close> adata.distinct_disc(1))
qed

subsection \<open>Proof Method\<close>

method slookup uses lookup = solves\<open>rule lookup | (simp(no_asm), rule lookup)\<close>

method mc uses lookup
  = (erule range_range_write_1)
  | (erule range_range_write_2)
  | (erule range_range_disj_write)
  | (erule range_disj_write)
  | (erule range_disj_mupdate, assumption, assumption)
  | (erule range_some_mupdate_value)
  | (erule range_some_mupdate_1, assumption, assumption)
  | (erule range_some_mupdate_2)
  | (erule write_read_1)
  | (erule write_read_2)
  | (erule read_mupdate_value)
  | (erule read_mupdate_1, solves\<open>simp\<close>, solves\<open>simp\<close>)
  | (erule read_mupdate_2)
  | (erule disjoint_range_write_1)
  | (erule disjoint_range_write_2)
  | (erule disjoint_mupdate_value)
  | (erule disjoint_mupdate_1, solves\<open>simp\<close>, solves\<open>simp\<close>)
  | (erule nth_some, solves\<open>simp\<close>)
  | (erule mlookup_mupdate, solves\<open>simp\<close>)
  | (erule mlookup_some_write_1, (slookup lookup: lookup)?)
  | (erule mlookup_some_write_2)
  | (erule mlookup_nth_mupdate)
  | (erule mlookup_neq_write_1, solves\<open>simp\<close>)
  | (erule mlookup_neq_write_2, assumption)
  | (erule mlookup_neq_mupdate_1, assumption, assumption, assumption, solves\<open>simp\<close>)
  | (erule mlookup_neq_mupdate_2, assumption, assumption, assumption, solves\<open>simp\<close>)
  | (erule mlookup_loc_write_1, (slookup lookup: lookup)?)
  | (erule mlookup_loc_write_2)
  | (erule mlookup_nin_loc_write, solves\<open>simp\<close>)
  | (erule mlookup_range_write_1)
  | (erule mlookup_range_write_2, (slookup lookup: lookup)?)
  | (erule mlookup_range_write_3)
  | (erule locations_write_1, (slookup lookup: lookup)?)
  | (erule locations_write_2)
  | (erule locations_mupdate)
  | (erule mlookup_locations_write_1, (slookup lookup: lookup)?)
  | (erule mlookup_locations_write_2, (slookup lookup: lookup)?)
  | (erule mlookup_locations_write_3, (slookup lookup: lookup)?)
  | (erule mlookup_locations_write_4)
  | (erule mlookup_locations_mupdate_1, assumption, assumption, solves\<open>simp\<close>)
  | (erule mlookup_locations_mupdate_2, assumption, assumption, solves\<open>simp\<close>)
  | (erule disjoint_mupdate_2)

end