(*
 * Copyright (c) 2022-2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


chapter "HL phase: Heap Lifting / Split Heap"

theory Split_Heap
  imports
   TypHeapSimple
begin

ML_file "ac_names.ML"

definition array_fields :: "nat \<Rightarrow> qualified_field_name list" where
  "array_fields n = map (\<lambda>n. [replicate n CHR ''1'']) [0..<n]"

lemma Nil_nmem_array_fields[simp]: "[] \<notin> set (array_fields n)"
  by (auto simp add: array_fields_def)

lemma distinct_prop_disj_fn_array_fields[simp]: "distinct_prop disj_fn (array_fields n)"
  by (simp add: array_fields_def distinct_prop_iff_nth)

lemma field_lookup_field_ti':
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 = Some (a, b) \<Longrightarrow> field_ti TYPE('a) f = Some a"
  unfolding field_ti_def by simp

lemma field_lookup_append_add:
  "wf_desc t \<Longrightarrow>
    field_lookup t (f @ g) n =
      Option.bind (field_lookup t f n) (\<lambda>(t', m).
        Option.bind (field_lookup t' g 0) (\<lambda>(t'', m'). Some (t'', m + m')))"
  by (subst field_lookup_append_eq)
     (auto simp: field_lookup_offset intro: field_lookup_offset_None[THEN iffD2]
           split: bind_split)

lemma nth_array_fields: "i < n \<Longrightarrow> array_fields n ! i =  [replicate i CHR ''1'']"
  by (simp add: array_fields_def)
lemma array_fields_Suc: "array_fields (Suc n) = array_fields n @ [[replicate n CHR ''1'']]"
  by (simp add: array_fields_def)

lemma find_append: "find P (xs @ ys) = (case find P xs of None \<Rightarrow> find P ys | Some x => Some x)"
  by (induct xs) auto

lemma length_array_fields: "length (array_fields n) = n"
  by (simp add: array_fields_def)

lemma set_array_fields: "set (array_fields n) = (\<Union>i<n. {[replicate i CHR ''1'']})"
  by (induct n) (auto simp add: array_fields_def)
lemma find_array_fields_Some: 
  "find P (array_fields n) = Some y \<longleftrightarrow> 
   (\<exists>i < n. y = [replicate i CHR ''1''] \<and> P y \<and> (\<forall>j<i. \<not> P ([replicate j CHR ''1''])))"
proof (induct n arbitrary: y)
  case 0
  then show ?case 
    by (simp add: array_fields_def)
next
  case (Suc n)
  show ?case
  proof (cases "find P (array_fields n)")
    case None
    then show ?thesis
      apply (simp add:  array_fields_Suc find_append )
      using less_Suc_eq
      by (auto dest!: findNoneD simp add: set_array_fields)
  next
    case (Some a)
    then show ?thesis 
      apply (simp add:  array_fields_Suc find_append )
      apply (simp add: Suc.hyps)
      by (metis less_Suc_eq linorder_neqE_nat)
  qed
qed

lemma Bex_intvl_conv: "(\<exists>x \<in> {0..<n::nat}. P x) \<longleftrightarrow> (\<exists>i. i < n \<and> P i)"
  by auto

lemma Bex_union_conv: "(\<exists>x \<in> A \<union> B. P x) \<longleftrightarrow> ((\<exists>x \<in> A. P x) \<or> (\<exists>x \<in> B. P x))"
  by auto

lemma ex_intvl_conj_distribR: " ((\<exists>x\<in>{0..<n}. P x) \<and> Q) \<longleftrightarrow> (\<exists>x\<in>{0..<n}. P x \<and> Q)"
  by blast

lemma ex_less_conj_distribR: "((\<exists>i<n::nat. P i) \<and> Q) \<longleftrightarrow> (\<exists>i<n. P i \<and> Q)"
  by blast

lemma map_filter_map_Some_conv:
  assumes all_Some: "\<And>x. x \<in> set xs \<Longrightarrow> f x = Some (g x)"
  shows "List.map_filter f xs = map g xs"
  using all_Some
  apply (induct xs)
   apply (auto simp add: List.map_filter_def)
  done

lemma map_filter_map_compose:
  "List.map_filter f (map g xs) = List.map_filter (f o g) xs"
  by (induct xs) (auto simp add: List.map_filter_def)

lemma map_filter_fun_eq_conv:
  assumes all_same: "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "List.map_filter f xs = List.map_filter g xs"
  using all_same
  apply (induct xs)
   apply (auto simp add: List.map_filter_def)
  done

lemma map_filter_empty[simp]: "List.map_filter Map.empty xs = []"
  by (simp add: List.map_filter_def)

lemma map_filter_Some[simp]: "List.map_filter (\<lambda>x. Some (f x)) xs = map f xs"
  by (simp add: List.map_filter_def)

lemma list_all_field_lookup[simp]:
  "CARD('n) = m \<Longrightarrow>
  list_all
    (\<lambda>f. \<exists>a b. field_lookup (typ_uinfo_t TYPE('a::c_type['n::finite])) f 0 = Some (a, b))
    (map (\<lambda>n. [replicate n CHR ''1'']) [0..<m])"
  using field_lookup_array[where 'b='n and 'a='a]
  apply (simp add: list_all_iff atLeast0LessThan typ_uinfo_t_def flip: All_less_Ball)
  using field_lookup_export_uinfo_Some by blast

lemma ptr_span_with_stack_byte_type_subset_field[simp]:
  "\<forall>a\<in>ptr_span (p::'a::mem_type ptr). root_ptr_valid h (PTR(stack_byte) a) \<Longrightarrow>
    \<exists>u. field_ti TYPE('a::mem_type) f = Some u \<and> size_td u = sz \<Longrightarrow>
    (\<forall>a\<in>{&(p\<rightarrow>f)..+sz}. root_ptr_valid h (PTR(stack_byte) a)) \<longleftrightarrow> True"
  by (auto simp: dest!: mem_type_class.field_tag_sub field_tiD)

lemma (in pointer_lense) pointer_lense_field_lvalue:
  assumes f: "field_ti TYPE('c::mem_type) f = Some u"
    and u: "size_td u = size_of TYPE('a)"
  shows "pointer_lense (\<lambda>h (p::'c ptr). r h (PTR('a) &(p\<rightarrow>f))) (\<lambda>p. w (PTR('a) &(p\<rightarrow>f)))"
  apply unfold_locales
  apply (simp_all add: read_write_same write_same)
  apply (subst write_other_commute)
  subgoal for p q
    using field_tag_sub[OF field_tiD, OF f, of p]
    using field_tag_sub[OF field_tiD, OF f, of q]
    apply (simp add: u)
    apply (rule disjnt_subset1, erule disjnt_subset2)
    by auto
  apply simp
  done

lemma exists_nat_numeral: "\<exists>x::nat. x < numeral k"
  apply (rule exI[where x=0])
  apply (rule Num.rel_simps)
  done

lemma fun_upd_eq_cases: "f(p:=x) = g \<longleftrightarrow> (g p = x \<and> (\<forall>q. p\<noteq>q \<longrightarrow> f q = g q))"
  by (auto simp add: fun_upd_def)

lemma fun_upd_apply_eq_cases: "(f(p:=x)) q = g q \<longleftrightarrow> ((p = q \<longrightarrow> g q = x) \<and> (p \<noteq> q \<longrightarrow> f q = g q))"
  by (auto simp add: fun_upd_def)

lemma comp_fun_upd_same_fuse:
  "(\<lambda>f. f(p := x)) o (\<lambda>f. f(p := y)) = (\<lambda>f. f(p:=x))"
  by auto

lemma comp_fun_upd_other_commute:
  "p \<noteq> q \<Longrightarrow> (\<lambda>f. f(q := y)) o (\<lambda>f. f(p := x)) = (\<lambda>f. f(p := x)) o (\<lambda>f. f(q := y))"
  by (auto simp add: comp_def fun_upd_def fun_eq_iff)

lemma map_td_compose:
  fixes t::"('a, 'b) typ_desc"
  and st::"('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
shows
  "map_td f1 g1 (map_td f2 g2 t) = map_td (\<lambda>n algn. f1 n algn o f2 n algn) (g1 o g2) t" and
  "map_td_struct f1 g1 (map_td_struct f2 g2 st) = map_td_struct (\<lambda>n algn. f1 n algn o f2 n algn) (g1 o g2) st" and
  "map_td_list f1 g1 (map_td_list f2 g2 ts) = map_td_list (\<lambda>n algn. f1 n algn o f2 n algn) (g1 o g2) ts" and
  "map_td_tuple f1 g1 (map_td_tuple f2 g2 x) = map_td_tuple (\<lambda>n algn. f1 n algn o f2 n algn) (g1 o g2) x"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by auto
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case by auto
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by auto
qed


lemma (in mem_type) distinct_all_field_names:
  "distinct (all_field_names (typ_info_t TYPE('a)))"
  using distinct_all_field_names wf_desc by blast

lemma field_lookup_same_type_disjoint:
  "\<lbrakk>field_lookup t f m = Some (d,n);
      field_lookup t f' m = Some (d',n'); f \<noteq> f'; export_uinfo d = export_uinfo d';
      wf_desc t; size_td t < addr_card\<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}" and

  "\<lbrakk>field_lookup_struct st f m = Some (d,n);
      field_lookup_struct st f' m = Some (d',n'); f \<noteq> f'; export_uinfo d = export_uinfo d';
      wf_desc_struct st; size_td_struct st < addr_card \<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}" and

  "\<lbrakk>field_lookup_list ts f m = Some (d,n);
      field_lookup_list ts f' m = Some (d',n'); f \<noteq> f'; export_uinfo d = export_uinfo d';
      wf_desc_list ts; size_td_list ts < addr_card\<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}" and
  "\<lbrakk>field_lookup_tuple x f m = Some (d,n) ;
      field_lookup_tuple x f' m = Some (d',n'); f \<noteq> f'; export_uinfo d = export_uinfo d';
      wf_desc_tuple x; size_td_tuple x < addr_card\<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
proof (induct t and st and ts and x arbitrary: f m d n f' m d' n' and  f m d n f' m d' n' and
    f m d n f' m d' n' and  f m d n f' m d' n')
  case (TypDesc algn st nm)
  then show ?case
    by (metis field_lookup.simps field_lookup_export_uinfo_Some field_lookup_same_type_empty(1)
        size_td.simps wf_desc.simps)
next
  case (TypScalar n algn x)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc x xs)
  from Cons_typ_desc.prems obtain
    f: "field_lookup_list (x # xs) f m = Some (d, n)" and
    f': "field_lookup_list (x # xs) f' m = Some (d', n')" and
    neq_f_f': "f \<noteq> f'" and
    eq_d_d': "export_uinfo d = export_uinfo d'" and
    sz: "size_td_tuple x + size_td_list xs < addr_card" and
    wf_x: "wf_desc_tuple x" and
    distinct: "dt_snd x \<notin> dt_snd ` set xs" and
    wf_xs: "wf_desc_list xs" by clarsimp
  from sz have sz_xs: "size_td_list xs < addr_card" by auto
  from sz have sz_x: "size_td_tuple x < addr_card" by auto
  show ?case
  proof (cases "field_lookup_tuple x f m")
    case None
    note f_None = this
    from f None have f_xs: "field_lookup_list xs f (m + size_td (dt_fst x)) = Some (d, n)" by simp
    from td_set_list_field_lookup_listD [OF f_xs] have "(d, n) \<in> td_set_list xs (m + size_td (dt_fst x))" .
    from td_set_list_intvl_sub [OF this]
    have contained_f: "{word_of_nat n..+size_td d} \<subseteq> {word_of_nat (m + size_td (dt_fst x))..+size_td_list xs}" .
    show ?thesis
    proof (cases "field_lookup_tuple x f' m")
      case None
      from f' None have f'_xs: "field_lookup_list xs f' (m + size_td (dt_fst x)) = Some (d', n')" by simp
      from Cons_typ_desc.hyps(2) [OF f_xs f'_xs neq_f_f' eq_d_d' wf_xs sz_xs]
      show ?thesis .
    next
      case (Some _)
      with f' have f'_x: "field_lookup_tuple x f' m = Some (d', n')" by simp
      from td_set_tuple_field_lookup_tupleD [OF f'_x] have "(d', n') \<in> td_set_tuple x m" .
      from td_set_tuple_intvl_sub [OF this]
      have "{word_of_nat n'..+size_td d'} \<subseteq> {word_of_nat m..+size_td_tuple x}" .
      with contained_f sz show ?thesis
        by (smt (verit, ccfv_SIG) disj_subset init_intvl_disj of_nat_add size_td_tuple_dt_fst)
    qed
  next
    case (Some _)
    from f Some have f_x: "field_lookup_tuple x f m = Some (d, n)" by simp
    from td_set_tuple_field_lookup_tupleD [OF f_x] have "(d, n) \<in> td_set_tuple x m" .
    from td_set_tuple_intvl_sub [OF this]
    have contained_f: "{word_of_nat n..+size_td d} \<subseteq> {word_of_nat m..+size_td_tuple x}" .
    show ?thesis
    proof (cases "field_lookup_tuple x f' m")
      case None
      from f' None have f'_xs: "field_lookup_list xs f' (m + size_td (dt_fst x)) = Some (d', n')" by simp
      from td_set_list_field_lookup_listD [OF f'_xs]
      have "(d', n') \<in> td_set_list xs (m + size_td (dt_fst x))" .
      from td_set_list_intvl_sub [OF this]
      have "{word_of_nat n'..+size_td d'} \<subseteq> {word_of_nat (m + size_td (dt_fst x))..+size_td_list xs}" .
      with contained_f sz show ?thesis
        by (smt (verit, ccfv_threshold) Int_commute disjoint_subset init_intvl_disj
            of_nat_add size_td_tuple_dt_fst)
    next
      case (Some _)
      with f' have f'_x: "field_lookup_tuple x f' m = Some (d', n')" by simp
      from Cons_typ_desc.hyps(1) [OF f_x f'_x neq_f_f' eq_d_d' wf_x sz_x]
      show ?thesis .
    qed
  qed
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case
    by (metis fl5 list.expand option.simps(3) size_td_tuple.simps wf_desc_tuple.simps)
qed


lemma field_lookup_same_type_u_disjoint:
  "\<lbrakk>field_lookup t f m = Some (d,n);
      field_lookup t f' m = Some (d,n'); f \<noteq> f';
      wf_desc t; size_td t < addr_card\<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td d} \<inter> {of_nat n'..+size_td d} = {}" and

  "\<lbrakk>field_lookup_struct st f m = Some (d,n);
      field_lookup_struct st f' m = Some (d,n'); f \<noteq> f';
      wf_desc_struct st; size_td_struct st < addr_card \<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td d} \<inter> {of_nat n'..+size_td d} = {}" and

  "\<lbrakk>field_lookup_list ts f m = Some (d,n);
      field_lookup_list ts f' m = Some (d,n'); f \<noteq> f';
      wf_desc_list ts; size_td_list ts < addr_card\<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td d} \<inter> {of_nat n'..+size_td d} = {}" and
  "\<lbrakk>field_lookup_tuple x f m = Some (d,n) ;
      field_lookup_tuple x f' m = Some (d,n'); f \<noteq> f';
      wf_desc_tuple x; size_td_tuple x < addr_card\<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td d} \<inter> {of_nat n'..+size_td d} = {}"
proof (induct t and st and ts and x arbitrary: f m d n f' m  n' and  f m d n f' m  n' and
    f m d n f' m  n' and  f m d n f' m  n')
  case (TypDesc algn st nm)
  then show ?case
    by (metis field_lookup.simps  field_lookup_same_type_empty(1)
        size_td.simps wf_desc.simps)
next
  case (TypScalar n algn x)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by simp
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc x xs)
  from Cons_typ_desc.prems obtain
    f: "field_lookup_list (x # xs) f m = Some (d, n)" and
    f': "field_lookup_list (x # xs) f' m = Some (d, n')" and
    neq_f_f': "f \<noteq> f'" and
    sz: "size_td_tuple x + size_td_list xs < addr_card" and
    wf_x: "wf_desc_tuple x" and
    distinct: "dt_snd x \<notin> dt_snd ` set xs" and
    wf_xs: "wf_desc_list xs" by clarsimp
  from sz have sz_xs: "size_td_list xs < addr_card" by auto
  from sz have sz_x: "size_td_tuple x < addr_card" by auto
  show ?case
  proof (cases "field_lookup_tuple x f m")
    case None
    note f_None = this
    from f None have f_xs: "field_lookup_list xs f (m + size_td (dt_fst x)) = Some (d, n)" by simp
    from td_set_list_field_lookup_listD [OF f_xs] have "(d, n) \<in> td_set_list xs (m + size_td (dt_fst x))" .
    from td_set_list_intvl_sub [OF this]
    have contained_f: "{word_of_nat n..+size_td d} \<subseteq> {word_of_nat (m + size_td (dt_fst x))..+size_td_list xs}" .
    show ?thesis
    proof (cases "field_lookup_tuple x f' m")
      case None
      from f' None have f'_xs: "field_lookup_list xs f' (m + size_td (dt_fst x)) = Some (d, n')" by simp
      from Cons_typ_desc.hyps(2) [OF f_xs f'_xs neq_f_f' wf_xs sz_xs]
      show ?thesis .
    next
      case (Some _)
      with f' have f'_x: "field_lookup_tuple x f' m = Some (d, n')" by simp
      from td_set_tuple_field_lookup_tupleD [OF f'_x] have "(d, n') \<in> td_set_tuple x m" .
      from td_set_tuple_intvl_sub [OF this]
      have "{word_of_nat n'..+size_td d} \<subseteq> {word_of_nat m..+size_td_tuple x}" .
      with contained_f sz show ?thesis
        by (smt (verit, ccfv_SIG) disj_subset init_intvl_disj of_nat_add size_td_tuple_dt_fst)
    qed
  next
    case (Some _)
    from f Some have f_x: "field_lookup_tuple x f m = Some (d, n)" by simp
    from td_set_tuple_field_lookup_tupleD [OF f_x] have "(d, n) \<in> td_set_tuple x m" .
    from td_set_tuple_intvl_sub [OF this]
    have contained_f: "{word_of_nat n..+size_td d} \<subseteq> {word_of_nat m..+size_td_tuple x}" .
    show ?thesis
    proof (cases "field_lookup_tuple x f' m")
      case None
      from f' None have f'_xs: "field_lookup_list xs f' (m + size_td (dt_fst x)) = Some (d, n')" by simp
      from td_set_list_field_lookup_listD [OF f'_xs]
      have "(d, n') \<in> td_set_list xs (m + size_td (dt_fst x))" .
      from td_set_list_intvl_sub [OF this]
      have "{word_of_nat n'..+size_td d} \<subseteq> {word_of_nat (m + size_td (dt_fst x))..+size_td_list xs}" .
      with contained_f sz show ?thesis
        by (smt (verit, ccfv_threshold) Int_commute disjoint_subset init_intvl_disj
            of_nat_add size_td_tuple_dt_fst)
    next
      case (Some _)
      with f' have f'_x: "field_lookup_tuple x f' m = Some (d, n')" by simp
      from Cons_typ_desc.hyps(1) [OF f_x f'_x neq_f_f'  wf_x sz_x]
      show ?thesis .
    qed
  qed
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case
    by (metis fl5 list.expand option.simps(3) size_td_tuple.simps wf_desc_tuple.simps)
qed

lemma td_set_list_intvl_sub_nat:
  "(d,n) \<in> td_set_list t m \<Longrightarrow> {n..< n +size_td d} \<subseteq> {m..< m +size_td_list t}"
  apply(frule td_set_list_offset_le)
  apply(drule td_set_list_offset_size_m)
  apply auto
  done

lemma td_set_tuple_intvl_sub_nat:
  "(d,n) \<in> td_set_tuple t m \<Longrightarrow> {n..<n+size_td d} \<subseteq> {m..<m+size_td_tuple t}"
  apply(frule td_set_tuple_offset_le)
  apply(drule td_set_tuple_offset_size_m)
  apply auto
  done

lemma field_lookup_same_type_u_disjoint_nat:
  "\<lbrakk>field_lookup t f m = Some (d,n);
      field_lookup t f' m = Some (d,n'); f \<noteq> f';
      wf_desc t\<rbrakk> \<Longrightarrow>
      {n..<n + size_td d} \<inter> {n'..<n' + size_td d} = {}" and

  "\<lbrakk>field_lookup_struct st f m = Some (d,n);
      field_lookup_struct st f' m = Some (d,n'); f \<noteq> f';
      wf_desc_struct st \<rbrakk> \<Longrightarrow>
      {n..< n + size_td d} \<inter> {n'..< n' + size_td d} = {}" and

  "\<lbrakk>field_lookup_list ts f m = Some (d,n);
      field_lookup_list ts f' m = Some (d,n'); f \<noteq> f';
      wf_desc_list ts\<rbrakk> \<Longrightarrow>
      {n..<n + size_td d} \<inter> {n'..<n' + size_td d} = {}" and
  "\<lbrakk>field_lookup_tuple x f m = Some (d,n) ;
      field_lookup_tuple x f' m = Some (d,n'); f \<noteq> f';
      wf_desc_tuple x\<rbrakk> \<Longrightarrow>
      {n..<n + size_td d} \<inter> {n'..<n' +size_td d} = {}"
proof (induct t and st and ts and x arbitrary: f m d n f' m  n' and  f m d n f' m  n' and
    f m d n f' m  n' and  f m d n f' m  n')
  case (TypDesc algn st nm)
  then show ?case
    by (metis field_lookup.simps  field_lookup_same_type_empty(1)
        wf_desc.simps)
next
  case (TypScalar n algn x)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc x xs)

  from Cons_typ_desc.prems obtain
    f: "field_lookup_list (x # xs) f m = Some (d, n)" and
    f': "field_lookup_list (x # xs) f' m = Some (d, n')" and
    neq_f_f': "f \<noteq> f'" and
    wf_x: "wf_desc_tuple x" and
    distinct: "dt_snd x \<notin> dt_snd ` set xs" and
    wf_xs: "wf_desc_list xs" by clarsimp

  show ?case
  proof (cases "field_lookup_tuple x f m")
    case None
    note f_None = this
    from f None have f_xs: "field_lookup_list xs f (m + size_td (dt_fst x)) = Some (d, n)" by simp
    from td_set_list_field_lookup_listD [OF f_xs] have "(d, n) \<in> td_set_list xs (m + size_td (dt_fst x))" .
    from td_set_list_intvl_sub_nat [OF this]
    have contained_f: "{n..<n+size_td d} \<subseteq> {(m + size_td (dt_fst x))..<(m + size_td (dt_fst x)) +size_td_list xs}" .
    show ?thesis
    proof (cases "field_lookup_tuple x f' m")
      case None
      from f' None have f'_xs: "field_lookup_list xs f' (m + size_td (dt_fst x)) = Some (d, n')" by simp
      from Cons_typ_desc.hyps(2) [OF f_xs f'_xs neq_f_f' wf_xs ]
      show ?thesis .
    next
      case (Some _)
      with f' have f'_x: "field_lookup_tuple x f' m = Some (d, n')" by simp
      from td_set_tuple_field_lookup_tupleD [OF f'_x] have "(d, n') \<in> td_set_tuple x m" .
      from td_set_tuple_intvl_sub_nat[OF this]
      have "{n'..<n'+size_td d} \<subseteq> {m..<m+size_td_tuple x}" .
      with contained_f show ?thesis
        by (smt (verit, best) disj_inter_swap disj_subset ivl_disj_int_two(3) size_td_tuple_dt_fst)
    qed

  next
    case (Some _)
    from f Some have f_x: "field_lookup_tuple x f m = Some (d, n)" by simp
    from td_set_tuple_field_lookup_tupleD [OF f_x] have "(d, n) \<in> td_set_tuple x m" .
    from td_set_tuple_intvl_sub_nat [OF this]
    have contained_f: "{n..<n+size_td d} \<subseteq> {m..<m+size_td_tuple x}" .
    show ?thesis
    proof (cases "field_lookup_tuple x f' m")
      case None
      from f' None have f'_xs: "field_lookup_list xs f' (m + size_td (dt_fst x)) = Some (d, n')" by simp
      from td_set_list_field_lookup_listD [OF f'_xs]
      have "(d, n') \<in> td_set_list xs (m + size_td (dt_fst x))" .
      from td_set_list_intvl_sub_nat [OF this]
      have "{n'..<n'+size_td d} \<subseteq> {(m + size_td (dt_fst x))..<(m + size_td (dt_fst x))+size_td_list xs}" .
      with contained_f show ?thesis
        by (metis Int_commute disjoint_subset ivl_disj_int_two(3) size_td_tuple_dt_fst)
    next
      case (Some _)
      with f' have f'_x: "field_lookup_tuple x f' m = Some (d, n')" by simp
      from Cons_typ_desc.hyps(1) [OF f_x f'_x neq_f_f'  wf_x ]
      show ?thesis .
    qed
  qed
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case
    by (metis fl5 list.expand option.simps(3) wf_desc_tuple.simps)
qed

lemma (in mem_type) field_lookup_same_type_disjoint:
  assumes f: "field_lookup (typ_info_t TYPE('a)) f m = Some (t, n) "
  assumes f': "field_lookup (typ_info_t TYPE('a)) f' m = Some (t', n')"
  assumes neq: "f \<noteq> f'"
  assumes same: "export_uinfo t = export_uinfo t'"
  shows "{(of_nat n)::addr..+size_td t} \<inter> {of_nat n'..+size_td t'} = {}"
proof -
  have "size_td (typ_info_t TYPE('a)) < addr_card"
    by (simp add: size_of_fold)

  from field_lookup_same_type_disjoint(1) [OF f f' neq same wf_desc this]
  show ?thesis
    by simp
qed

lemma (in mem_type) field_lookup_same_type_ptr_span_disjoint:
  fixes p::"'a ptr"
  assumes f: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n) "
  assumes f': "field_lookup (typ_info_t TYPE('a)) f' 0 = Some (t', n')"
  assumes neq: "f \<noteq> f'"
  assumes t: "export_uinfo t = typ_uinfo_t (TYPE('b::c_type))"
  assumes t': "export_uinfo t' = typ_uinfo_t (TYPE('b::c_type))"
  shows "ptr_span (PTR('b) &(p\<rightarrow>f)) \<inter> ptr_span (PTR('b) &(p\<rightarrow>f')) = {}"
proof -
  from t t' have "export_uinfo t = export_uinfo t'" by simp
  from field_lookup_same_type_disjoint [OF f f' neq this]
  have "{word_of_nat n::addr..+size_td t} \<inter> {word_of_nat n'..+size_td t'} = {}" .
  moreover
  from t have "size_td t = size_of TYPE('b)"
    by (simp add: export_size_of)
  moreover
  from t' have "size_td t' = size_of TYPE('b)"
    by (simp add: export_size_of)
  ultimately
  show ?thesis
    using f f'
    by (simp add: field_lvalue_def intvl_disj_offset)
qed



lemma sub_type_valid_field_lvalue_overlap:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"
  assumes subtype: "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes valid_p: "d \<Turnstile>\<^sub>t p"
  assumes overlap: "ptr_span p \<inter> ptr_span q \<noteq> {}"
  shows "d \<Turnstile>\<^sub>t q \<longleftrightarrow>
           (\<exists>f t n. field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n) \<and>
                    export_uinfo t = typ_uinfo_t TYPE('b) \<and>
                    q = PTR('b) (&(p\<rightarrow>f)))"
proof 
  assume valid_q: "d \<Turnstile>\<^sub>t q"
  show "\<exists>f t n. field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n) \<and>
          export_uinfo t = typ_uinfo_t TYPE('b) \<and> q = PTR('b) (&(p\<rightarrow>f))"
  proof -

    from subtype have "typ_uinfo_t TYPE('b) \<le> typ_uinfo_t TYPE('a)" by (simp add: sub_typ_def)

    from this overlap valid_footprint_sub_cases [OF h_t_valid_valid_footprint [OF valid_q]  h_t_valid_valid_footprint [OF valid_p]]
    have field_of: "field_of (ptr_val q - ptr_val p) (typ_uinfo_t TYPE('b)) (typ_uinfo_t TYPE('a))"
      apply (simp add: size_of_def)
      by (metis Int_commute le_less_trans less_irrefl)
    then obtain f where
      fl: "field_lookup (typ_uinfo_t (TYPE('a))) f 0 = Some (typ_uinfo_t TYPE('b), unat (ptr_val q - ptr_val p))"
      using field_of_lookup_info by blast

    then obtain t where
      fl': "field_lookup  (typ_info_t (TYPE('a))) f 0 = Some (t, unat (ptr_val q - ptr_val p))" and
      t: "export_uinfo t = typ_uinfo_t TYPE('b)"
      using field_lookup_uinfo_Some_rev by blast

    from fl'
    have ptr_val_q: "ptr_val q = &(p\<rightarrow>f)"
      by (simp add: field_lvalue_def)

    with fl' t show ?thesis
      by (metis Ptr_ptr_val)
  qed
next
  assume "\<exists>f t n.
       field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n) \<and> export_uinfo t = typ_uinfo_t TYPE('b) \<and>
       q = PTR('b) &(p\<rightarrow>f)"
  then show "d \<Turnstile>\<^sub>t q"
    using valid_p
    using c_guard_mono h_t_valid_mono by blast
qed

lemma field_lookup_intvl_contained_left:
  fixes p::"'a::mem_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, k)"
  assumes n: "n = size_td t"
  assumes m: "m = size_of TYPE('a)"
  shows "{&(p\<rightarrow>f)..+n} \<inter> {ptr_val p..+m} \<noteq> {}"
proof -
  from field_tag_sub [OF fl] have "{&(p\<rightarrow>f)..+size_td t} \<subseteq> ptr_span p" .
  moreover from fl have "0 < size_td t"
    by (simp add: field_lookup_wf_size_desc_gt)
  ultimately show ?thesis using n m
    by (simp add: intvl_non_zero_non_empty le_iff_inf)
qed

lemma field_lookup_intvl_contained_right:
  fixes p::"'a::mem_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, k)"
  assumes n: "n = size_td t"
  assumes m: "m = size_of TYPE('a)"
  shows " {ptr_val p..+m} \<inter> {&(p\<rightarrow>f)..+n}  \<noteq> {}"
  using field_lookup_intvl_contained_left [OF fl n m] by blast

lemma field_overlap_right:
  fixes p::"'a::mem_type ptr"
  assumes field_lookup: "field_lookup (typ_info_t TYPE('a)) path 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('f)"
  shows "(ptr_span p) \<inter> ptr_span (PTR('f::c_type) &(p\<rightarrow>path)) \<noteq> {}"
  using field_lookup match
  by (simp add: export_size_of field_lookup_intvl_contained_right)

locale nested_field' =
  fixes t      :: "'a::mem_type xtyp_info"
  fixes path   :: "string list"
  fixes sel    :: "'a::mem_type \<Rightarrow> 'f::mem_type"
  fixes upd    :: "'f \<Rightarrow> 'a \<Rightarrow> 'a"

  assumes field_ti: "field_ti TYPE('a) path = Some t"
  assumes field_typ_match: "export_uinfo t = typ_uinfo_t TYPE('f)"

  assumes sel_def: "sel \<equiv> from_bytes o access_ti\<^sub>0 t"
  assumes upd_def: "upd \<equiv> update_ti t o to_bytes_p"
begin

lemma sub_typ: "TYPE('f) \<le>\<^sub>\<tau> TYPE('a)"
  using field_ti field_typ_match
  using field_ti_sub_typ sub_typ_def by blast

lemma h_val_field:
  shows "h_val h (PTR('f) &(p\<rightarrow>path)) = sel (h_val h p)"
  using TypHeap.h_val_field_from_bytes' field_ti field_typ_match sel_def  typ_uinfo_t_def
  by fastforce

lemma clift_field_update:
  assumes typed: "hrs_htd h \<Turnstile>\<^sub>t p"
  shows "clift (hrs_mem_update (heap_update (PTR('f) &(p\<rightarrow>path)) x) h) =
          (clift h)(p\<mapsto> upd x (h_val (hrs_mem h) p))"
proof -
  from h_t_valid_clift_Some_iff typed obtain v where clift: "clift h p = Some v" by blast
  from h_val_clift' [OF this]
  have v: "v = h_val (hrs_mem h) p" by simp
  from clift_field_update [OF field_ti _ clift [simplified v], where val=x,OF field_typ_match [simplified typ_uinfo_t_def]]
  show ?thesis
    by (simp add: upd_def export_size_of field_typ_match update_ti_t_def)
qed

lemma clift_field_update_padding:
  assumes typed: "hrs_htd h \<Turnstile>\<^sub>t p"
  assumes lbs: "length bs = size_of TYPE('f)"
  shows "clift (hrs_mem_update (heap_update_padding (PTR('f) &(p\<rightarrow>path)) x bs) h) =
          (clift h)(p\<mapsto> upd x (h_val (hrs_mem h) p))"
proof -
  from h_t_valid_clift_Some_iff typed obtain v where clift: "clift h p = Some v" by blast
  from h_val_clift' [OF this]
  have v: "v = h_val (hrs_mem h) p" by simp
  from clift_field_update_padding [OF field_ti _ clift [simplified v] lbs, where val=x,OF field_typ_match [simplified typ_uinfo_t_def]]
  show ?thesis
    by (simp add: upd_def export_size_of field_typ_match update_ti_t_def)
qed

lemma h_val_field_lvalue_update: "d \<Turnstile>\<^sub>t p \<Longrightarrow> d \<Turnstile>\<^sub>t q \<Longrightarrow>
  h_val (heap_update (PTR('f) &(p\<rightarrow>path)) x h) q = ((h_val h)(p := upd x (h_val h p))) q"
  by (smt (verit, best) c_type_class.lift_def clift_Some_eq_valid h_val_clift' 
      hrs_htd_def hrs_mem_def hrs_mem_update lift_heap_update lift_t_heap_update 
      nested_field'.clift_field_update nested_field'_axioms prod.sel(1) prod.sel(2))

lemma h_val_field_lvalue_update_padding: "d \<Turnstile>\<^sub>t p \<Longrightarrow> d \<Turnstile>\<^sub>t q \<Longrightarrow> length bs = size_of TYPE('f) \<Longrightarrow>
  h_val (heap_update_padding (PTR('f) &(p\<rightarrow>path)) x bs h) q = ((h_val h)(p := upd x (h_val h p))) q"
  by (smt (verit, ccfv_threshold) clift_Some_eq_valid fst_conv h_val_clift hrs_htd_def
          hrs_htd_mem_update hrs_mem_def hrs_mem_update clift_field_update_padding
          clift_field_update h_val_field_lvalue_update prod.collapse snd_conv)

end




lemma align_addr_card:
  assumes wf_size_desc: "wf_size_desc t"
  assumes max_size: "size_td t < addr_card"
  assumes align_size_of: "2 ^ align_td t dvd size_td t"
  shows  "2 ^ align_td t dvd addr_card"
proof -
  from wf_size_desc have sz_nzero: "0 < size_td t"
    by (simp add: wf_size_desc_gt(1))
  with align_size_of max_size
  have align_bound: "align_td t < addr_bitsize"
    by (metis addr_card linorder_not_le nat_dvd_not_less power_le_dvd)
  then have bound: "2 ^ align_td t < addr_card"
    by (metis addr_card one_less_numeral_iff power_strict_increasing semiring_norm(76))
  from bound align_bound
  show ?thesis
    apply (clarsimp simp: dvd_def)
    apply (rule exI[where x="2^(len_of TYPE(addr_bitsize) - align_td t)"])
    apply clarsimp
    apply(simp add: addr_card flip: power_add)
    done
qed

lemma ptr_aligned_u_field_lookup:
  assumes wf_size_desc: "wf_size_desc t"
  assumes wf_align: "wf_align t"
  assumes align_field: "align_field t"
  assumes max_size: "size_td t < addr_card"
  assumes align_size_of: "2 ^ align_td t dvd size_td t"
  assumes align_size_of_u:  "2 ^ align_td u dvd size_td u" \<comment> \<open>does not follow from a well-formedness condition on t\<close>
  assumes fl: "field_lookup t path 0 = Some (u, n)"
  assumes ptr_aligned_u: "ptr_aligned_u t a"
  shows "ptr_aligned_u u (a + of_nat n)"
proof -

  from wf_size_desc fl have wf_size_desc_u: "wf_size_desc u"
    using field_lookup_wf_size_desc_pres(1) by blast


  from fl have u_n_bound: "size_td u + n \<le> size_td t"
    by (simp add: field_lookup_offset_size')
  with max_size have n_bound: "n < addr_card"
    by simp
  from u_n_bound max_size have sz_u: "size_td u < addr_card"
    by simp

  from align_td_field_lookup(1) [OF wf_align fl] have align_u_t: "align_td u \<le> align_td t" .
  from align_field fl
  have "2 ^ (align_td u) dvd n" by (simp add: align_field_def)
  moreover
  from ptr_aligned_u have "2 ^ align_td t dvd unat a" by (simp add: ptr_aligned_u_def)


  ultimately have "2 ^ align_td u dvd unat (a + word_of_nat n)"
    apply -
    apply(subst unat_word_ariths)
   apply(rule dvd_mod)
    apply(rule dvd_add)
    subgoal
      using align_u_t
      using power_le_dvd by blast
    subgoal
      apply(subst unat_of_nat)
      apply(subst Euclidean_Rings.mod_less)
       apply(subst len_of_addr_card)
       apply (rule n_bound)
      apply assumption
      done
    subgoal
      apply(subst len_of_addr_card)
      apply (rule align_addr_card)
        apply (rule wf_size_desc_u)
       apply (rule sz_u)
      apply (rule align_size_of_u)
      done
    done

  then show ?thesis
    by (simp add: ptr_aligned_u_def)
qed


lemma c_guard_u_field_looup:
  assumes wf_size_desc: "wf_size_desc t"
  assumes wf_align: "wf_align t"
  assumes align_field: "align_field t"
  assumes max_size: "size_td t < addr_card"
  assumes align_size_of: "2 ^ align_td t dvd size_td t"
  assumes align_size_of_u:  "2 ^ align_td u dvd size_td u" \<comment> \<open>does not follow from a well-formedness condition on t\<close>
  assumes fl: "field_lookup t path 0 = Some (u, n)"
  assumes c_guard_u: "c_guard_u t a"
  shows "c_guard_u u (a + of_nat n)"
proof -
  from wf_size_desc have sz_t: "0 < size_td t"
    using wf_size_desc_gt(1) by blast
  from wf_size_desc fl have sz_u: "0 < size_td u"
    by (simp add: field_lookup_wf_size_desc_gt)
  show ?thesis
    using fl c_guard_u
    apply (clarsimp simp add: c_guard_u_def)
    apply safe
    subgoal by (rule ptr_aligned_u_field_lookup [OF wf_size_desc wf_align align_field max_size align_size_of align_size_of_u fl])
    subgoal by (meson c_null_guard_u_def field_lookup_offset_size' intvl_le subsetD)
    done
qed

lemma cvalid_u_field_lookup:
  assumes wf_size_desc: "wf_size_desc t"
  assumes wf_align: "wf_align t"
  assumes align_field: "align_field t"
  assumes max_size: "size_td t < addr_card"
  assumes align_size_of: "2 ^ align_td t dvd size_td t"
  assumes align_size_of_u:  "2 ^ align_td u dvd size_td u" \<comment> \<open>does not follow from a well-formedness condition on t\<close>
  assumes fl: "field_lookup t path 0 = Some (u, n)"
  assumes cvalid_u: "cvalid_u t d a"
  shows "cvalid_u u d (a + of_nat n)"
proof -
  from wf_size_desc have sz_t: "0 < size_td t"
    using wf_size_desc_gt(1) by blast
  from wf_size_desc fl have sz_u: "0 < size_td u"
    by (simp add: field_lookup_wf_size_desc_gt)

  from fl have u_n_bound: "size_td u + n \<le> size_td t"
    by (simp add: field_lookup_offset_size')
  with max_size have n_bound: "n < addr_card"
    by simp
  from u_n_bound max_size have sz_u_addr_card: "size_td u < addr_card"
    by simp

  note c_guard = c_guard_u_field_looup [OF wf_size_desc wf_align align_field max_size align_size_of align_size_of_u fl]

  from cvalid_u
  show ?thesis
    apply(clarsimp simp: cvalid_u_def valid_footprint_def Let_def  sz_t sz_u c_guard)
    subgoal for y
      apply(drule_tac x="n+y" in spec)
      apply (erule impE)
      subgoal using u_n_bound by simp
      subgoal
        by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1)
            fl map_list_map_trans of_nat_add td_set_field_lookupD typ_slice_td_set)
      done
    done
qed

locale mem_type_u =
  fixes t::typ_uinfo
  assumes wf_desc: "wf_desc t"
  assumes wf_size_desc: "wf_size_desc t"
  assumes wf_align: "wf_align t"
  assumes align_field: "align_field t"
  assumes max_size: "size_td t < addr_card"
  assumes align_size: "2 ^ align_td t dvd size_td t"
begin
lemmas ptr_aligned_u_field_lookup = ptr_aligned_u_field_lookup [OF wf_size_desc wf_align align_field max_size align_size]
lemmas c_guard_u_field_looup = c_guard_u_field_looup [OF wf_size_desc wf_align align_field max_size align_size]
lemmas cvalid_u_field_lookup = cvalid_u_field_lookup [OF wf_size_desc wf_align align_field max_size align_size]

end


lemma wf_size_desc_export_uinfo:
  fixes t::"('a, 'b) typ_info"
  and st::"('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
 "wf_size_desc t \<Longrightarrow> wf_size_desc (export_uinfo t)" and
 "wf_size_desc_struct st \<Longrightarrow> wf_size_desc_struct ( map_td_struct field_norm (\<lambda>_. ()) st)" and
 "wf_size_desc_list ts \<Longrightarrow> wf_size_desc_list ( map_td_list field_norm (\<lambda>_. ()) ts)" and
 "wf_size_desc_tuple x \<Longrightarrow> wf_size_desc_tuple ( map_td_tuple field_norm (\<lambda>_. ()) x)"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by auto
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case by auto
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (auto simp add: export_uinfo_def)
qed


context mem_type
begin

lemma typ_uinfo_t_mem_type[simp]: "mem_type_u (typ_uinfo_t(TYPE('a)))"
  apply (simp only: typ_uinfo_t_def)
  apply (unfold_locales)
       apply (simp add: typ_uinfo_t_def wf_desc_export_uinfo_pres(1))
      apply (simp add:wf_size_desc_export_uinfo)
     apply (metis export_uinfo_typdesc_simp local.wf_align typ_desc.exhaust wf_align_map_td(1))
    using local.align_field local.align_field_uinfo local.typ_uinfo_t_def apply fastforce
   apply (simp add: size_of_fold)
  using align_size_of
  apply (simp add: size_of_def align_of_def)
  done

sublocale u: mem_type_u "typ_uinfo_t(TYPE('a))"
  by (rule typ_uinfo_t_mem_type)

end



lemma field_names_u_composeI:
assumes wf_t: "wf_desc t"
assumes path1: "path1 \<in> set (field_names_u t u)"
assumes path2: "path2 \<in> set (field_names_u u v)"
shows "path1 @ path2 \<in> set (field_names_u t v)"
proof -
  from path1 wf_t obtain n where fl1: "field_lookup t path1 0 = Some (u, n)"
    using field_names_u_filter_all_field_names_conv(1) by fastforce
  with wf_t have wf_u: "wf_desc u"
    using field_lookup_wf_desc_pres(1) by blast
  from path2 wf_u obtain m where "field_lookup u path2 0 = Some (v, m)"
    using field_names_u_filter_all_field_names_conv(1) by fastforce
  hence fl2:  "field_lookup u path2 n = Some (v, n + m)"
    by (simp add: field_lookup_offset)
  from field_lookup_prefix_Some''(1)[rule_format, OF fl1 wf_t, of path2] fl2
  have "field_lookup t (path1 @ path2) 0 = Some (v, n + m)" by simp
  then
  show ?thesis
    by (simp add: field_lookup_all_field_names(1) field_names_u_filter_all_field_names_conv(1) wf_t)
qed


lemma field_names_u_composeD:
  assumes wf_t: "wf_desc t"
  assumes append: "path1 @ path2 \<in> set (field_names_u t v)"
  shows "\<exists>u. path1 \<in> set (field_names_u t u) \<and> path2 \<in> set (field_names_u u v)"
proof -

  from append wf_t obtain n where fl1: "field_lookup t (path1 @ path2) 0 = Some (v, n)"
    using field_names_u_filter_all_field_names_conv(1) by fastforce
  from  fl1
  obtain u m where
    path1: "field_lookup t path1 0 = Some (u, m)" and path2: "field_lookup u path2 m = Some (v, n)"
    using field_lookup_append_Some wf_t by blast
  thus ?thesis
    by (smt (verit, ccfv_threshold) all_field_names_exists_field_names_u(1)
        field_lookup_all_field_names(1) field_names_u_composeI field_names_u_filter_all_field_names_conv(1)
        local.fl1 mem_Collect_eq option.inject prod.inject set_filter wf_t)
qed


lemma field_names_u_field_offset_untyped_append:
  assumes "wf_desc root"
  assumes path1: "path1 \<in> set (field_names_u root outer)"
  assumes path2: "path2 \<in> set (field_names_u outer inner)"
  shows "field_offset_untyped root (path1 @ path2) = field_offset_untyped root path1 + field_offset_untyped outer path2"
  by (smt (verit, ccfv_threshold) assms(1) field_lookup_offset field_lookup_prefix_Some''(1)
      field_lookup_wf_desc_pres(1) field_names_u_filter_all_field_names_conv(1) field_offset_untyped_def
      mem_Collect_eq option.sel path1 path2 prod.sel(2) set_filter)


lemma root_ptr_valid_u_cases:
  assumes "root_ptr_valid_u t1 d a1"
  assumes "root_ptr_valid_u t2 d a2"
  shows "(t1 = t2 \<and> a1 = a2) \<or> ({a1 ..+ size_td t1} \<inter> {a2 ..+ size_td t2} = {})"
  apply (rule valid_root_footprints_cases )
  using assms
  by (auto simp add: root_ptr_valid_u_def )

lemma field_offset_untyped_empty[simp]: "field_offset_untyped t [] = 0"
  by (simp add: field_offset_untyped_def)

lemma field_names_u_refl[simp]: "field_names_u t t = [[]]"
  by (cases t) auto

lemma field_names_u_size_td_bounds:
  assumes wf_t: "wf_desc t"
  assumes path: "path \<in> set (field_names_u t u)"
  shows "field_offset_untyped t path + size_td u \<le> size_td t"
proof -
  from wf_t path obtain n where fl: "field_lookup t path 0 = Some (u, n)"
    using field_names_u_filter_all_field_names_conv(1) by auto

  hence n: "field_offset_untyped t path = n"
    by (simp add: field_offset_untyped_def)
  from field_lookup_offset_size' [OF fl] n
  show ?thesis by simp
qed

lemma field_lookup_path_cases:
  assumes fl1: "field_lookup t path 0 = Some (u, n)"
  shows "(t = u \<and> path = []) \<or> ((t \<noteq> u) \<and> path \<noteq> [])"
  using field_lookup_same_type_empty(1) local.fl1 by blast

lemma field_lookup_cycle_cases:
 assumes fl1: "field_lookup t path1 0 = Some (u, n1)"
 assumes fl2: "field_lookup u path2 0 = Some (v, n2)"
 shows "(t = v \<and> u = v \<and> path1 = [] \<and> path2 = [] \<and> n1 = 0 \<and> n2 = 0) \<or>
        (t \<noteq> v)"
  using field_lookup_path_cases [OF fl1] field_lookup_path_cases [OF fl2] fl1 fl2
  by (metis add.right_neutral diff_add_0 nat_less_le ordered_cancel_comm_monoid_diff_class.add_diff_inverse
   td_set_field_lookupD td_set_size_lte'(1))

lemma field_lookup_refl_iff: "field_lookup t p n = Some (t, m) \<longleftrightarrow> p = [] \<and> n = m"
proof
  assume fl: "field_lookup t p n = Some (t, m)"
  note CTypes.field_lookup_offset2[OF this]
  from field_lookup_cycle_cases[OF this this] fl show "p = [] \<and> n = m"
    by auto
qed auto

lemma valid_root_footprint_contained_sub_typ:
  assumes valid_root_x: "valid_root_footprint d x t"
  assumes valid_y: "valid_footprint d y s"
  assumes contained: "{y ..+ size_td s} \<subseteq> {x ..+ size_td t}"
  shows "s \<le> t"
proof -
  from valid_y have "0 < size_td s" by (simp add: valid_footprint_def Let_def)
  hence "{y ..+ size_td s} \<noteq> {}"
    by (simp add: intvl_non_zero_non_empty)
  with contained have "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}" by blast
  from valid_root_footprint_overlap_sub_typ [OF valid_root_x valid_y this]
  show ?thesis.
qed

lemma c_null_guard_u_no_overlow: "c_null_guard_u t a \<Longrightarrow> unat a + size_td t \<le> addr_card"
  unfolding c_null_guard_u_def addr_card_def
  using zero_not_in_intvl_no_overflow
  by (metis card_word)

lemma c_null_guard_u_size_td_limit: "c_null_guard_u t a \<Longrightarrow> size_td t < addr_card"
  unfolding c_null_guard_u_def addr_card_def
  by (metis (no_types, lifting) Abs_fnat_hom_0 add_diff_cancel_right' add_leE cancel_comm_monoid_add_class.diff_cancel
      card_word first_in_intvl linorder_not_less nat_less_le unat_eq_of_nat zero_less_card_finite zero_not_in_intvl_no_overflow)

lemma c_null_guard_u_intvl_nat_conv:
  assumes c_null_guard: "c_null_guard_u t a"
  shows "{a  ..+ size_td t} = {x. (unat a \<le> unat x \<and> unat x < (unat a + size_td t))}"
  using intvl_no_overflow_nat_conv [OF c_null_guard_u_no_overlow [OF c_null_guard]] by simp

lemma valid_footprint_overlap_sub_typ:
  assumes valid_x: "valid_footprint d x t"
  assumes valid_y: "valid_footprint d y s"
  assumes overlap: "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}"
  shows "s \<le> t \<or> t \<le> s"
  by (meson field_of_sub order_less_imp_le overlap
      valid_footprint_neq_disjoint valid_x valid_y)

lemma valid_footprint_overlap_sub_typ_cases [consumes 3, case_names eq less1 less2]:
  assumes valid_x: "valid_footprint d x t"
  assumes valid_y: "valid_footprint d y s"
  assumes overlap: "{x ..+ size_td t} \<inter> {y ..+ size_td s} \<noteq> {}"
  assumes eq: "s = t \<Longrightarrow> P"
  assumes less_s_t: "s < t \<Longrightarrow> P"
  assumes less_t_s: "t < s \<Longrightarrow> P"
  shows P
  using valid_footprint_overlap_sub_typ [OF valid_x valid_y overlap] eq less_s_t less_t_s
  by fastforce

lemma valid_footprint_contained_sub_typ:
  assumes valid_x: "valid_footprint d x t"
  assumes valid_y: "valid_footprint d y s"
  assumes contained: "{x ..+ size_td t} \<subseteq> {y ..+ size_td s}"
  shows "s \<le> t \<or> t \<le> s"
  by (metis intvl_non_zero_non_empty le_iff_inf contained valid_footprint_def
      valid_footprint_overlap_sub_typ valid_x valid_y)


lemma valid_footprint_contained_sub_typ_cases:
  assumes valid_x: "valid_footprint d x t"
  assumes valid_y: "valid_footprint d y s"
  assumes contained: "{x ..+ size_td t} \<subseteq> {y ..+ size_td s}"
  assumes eq: "s = t \<Longrightarrow> P"
  assumes less_s_t: "s < t \<Longrightarrow> P"
  assumes less_t_s: "t < s \<Longrightarrow> P"
  shows P
  using valid_footprint_contained_sub_typ [OF valid_x valid_y contained] eq less_s_t less_t_s
  by fastforce

lemma all_field_names_field_lookup':
  fixes t::"('a, 'b) typ_desc"
  and st::"('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
shows
  "wf_desc t \<Longrightarrow> f \<in> set (all_field_names t) \<Longrightarrow> \<exists>u n. field_lookup t f 0 = Some (u, n)" and
  "wf_desc_struct st \<Longrightarrow> f \<in> set (all_field_names_struct st) \<Longrightarrow> \<exists>u n. field_lookup_struct st f 0 = Some (u, n)" and
  "wf_desc_list ts \<Longrightarrow> f \<in> set (all_field_names_list ts) \<Longrightarrow> \<exists>u n. field_lookup_list ts f 0 = Some (u, n)" and
  "wf_desc_tuple x \<Longrightarrow> f \<in> set (all_field_names_tuple x) \<Longrightarrow> \<exists>u n. field_lookup_tuple x f 0 = Some (u, n)"
proof (induct t and st and ts and x arbitrary: f and f and f and f)
  case (TypDesc nat typ_struct list)
  then show ?case by auto
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case apply (cases dt_tuple)
    apply (clarsimp split: option.splits simp add:  all_field_names_list_conv)
    by (metis field_lookup_list_offset_None not_Some_eq_tuple)
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by auto
qed

lemma valid_foot_print_intvl_self: "valid_footprint d a t \<Longrightarrow> a \<in> {a ..+ size_td t}"
  by (simp add: valid_footprint_def Let_def intvl_self)

lemma field_lookup_Some_field_names_u:
  fixes t  :: "typ_uinfo" and
        st :: "typ_uinfo_struct" and
        ts :: "typ_uinfo_tuple list" and
        x  :: "typ_uinfo_tuple"
      shows
 "field_lookup t f n = Some (s, m) \<Longrightarrow>  f \<in> set (field_names_u t s)"
 "field_lookup_struct st f n = Some (s, m) \<Longrightarrow> f \<in> set (field_names_struct_u st s)"
 "field_lookup_list ts f n = Some (s, m) \<Longrightarrow> f \<in> set (field_names_list_u ts s)"
 "field_lookup_tuple x f n = Some (s, m) \<Longrightarrow> f \<in> set (field_names_tuple_u x s)"
proof (induct t and st and ts and x arbitrary: f n m  and f n m  and f n m  and f n m)
  case (TypDesc nat typ_struct list)
  then show ?case
    apply clarsimp
    by (metis TypDesc.prems field_lookup_same_type_empty(1))
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case
    by (auto split: option.splits)
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case apply clarsimp
    by (metis imageI list.exhaust_sel option.distinct(1))
qed

lemma field_lookup_non_prefix_disj':
  assumes wf: "mem_type_u t"
  assumes f: "field_lookup t f 0 = Some (tf, n)"
  assumes g: "field_lookup t g 0 = Some (tg, m)"
  assumes f_g: "disj_fn f g"
  shows "disjnt {(of_nat n::addr) ..+ size_td tf} {of_nat m ..+ size_td tg}"
  using mem_type_u.max_size[OF wf] f_g
  using field_lookup_offset_size'[OF f]
  using field_lookup_offset_size'[OF g]
  using field_lookup_non_prefix_disj[OF wf[THEN mem_type_u.wf_desc] f g]
  unfolding intvl_eq_of_nat_Ico_add
  apply (subst disjnt_of_nat)
  unfolding len_of_addr_card
  by (auto simp add: disjnt_def disj_fn_def less_eq_list_def)

(* FIXME: put the untyped versions first (already in CLanguage) and then prove the
   typed versions as corelarry*)

lemma sub_typ_stack_byte_u:
  "t \<le> typ_uinfo_t (TYPE(stack_byte)) \<Longrightarrow> t = typ_uinfo_t TYPE(stack_byte)"
  by (simp add: sub_typ_def typ_uinfo_t_def typ_info_stack_byte typ_tag_le_def)

lemma root_ptr_valid_not_subtype_disjoint_u:
  "\<lbrakk> root_ptr_valid d (p::'a::mem_type ptr);
     cvalid_u t d q;
     \<not> t \<le> typ_uinfo_t TYPE('a) \<rbrakk> \<Longrightarrow>
   ptr_span p \<inter> {q ..+ size_td t} = {}"
  by (metis cvalid_u_def root_ptr_valid_valid_root_footprint size_of_fold
      typ_uinfo_size valid_root_footprint_overlap_sub_typ)

lemma stack_allocs_disjoint_u:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "t \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "cvalid_u t d q"
  shows "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t} = {}"
proof -
  from stack_alloc obtain
    "typ_uinfo_t (TYPE('a)) \<noteq> typ_uinfo_t (TYPE(stack_byte))" and
    stack_bytes: "\<forall>a \<in> {ptr_val p ..+ n * size_of TYPE('a)}. root_ptr_valid d (PTR (stack_byte) a)"
    by (cases rule: stack_allocs_cases) auto
  from no_stack have no_sub_typ: "\<not> t \<le> typ_uinfo_t (TYPE(stack_byte))" by (metis sub_typ_stack_byte_u)
  {
    fix a
    assume a: "a \<in> {ptr_val p ..+ n * size_of TYPE('a)}"
    have "a \<notin> {q ..+ size_td t}"
    proof -
      from stack_bytes [rule_format, OF a] have "root_ptr_valid d (PTR (stack_byte) a)" .

      from root_ptr_valid_not_subtype_disjoint_u [OF this typed no_sub_typ ] show ?thesis
        by (simp add: disjoint_iff first_in_intvl)
    qed
  }
  then show "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t} = {}"
    by auto
qed

lemma fold_ptr_retyp_disjoint_u:
  fixes p::"'a::mem_type ptr"
  shows "\<lbrakk> cvalid_u t d q; {ptr_val p..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t} = {} \<rbrakk> \<Longrightarrow>
          cvalid_u t (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d) q"
  apply(clarsimp simp: cvalid_u_def)
  apply(erule fold_ptr_retyp_valid_footprint_disjoint)
  apply(fastforce simp: size_of_def)
  done

lemma fold_ptr_force_type_disjoint_u:
  fixes p::"'a::mem_type ptr"
  shows "\<lbrakk> cvalid_u t d q; {ptr_val p..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t} = {} \<rbrakk> \<Longrightarrow>
          cvalid_u t (fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d) q"
  apply(clarsimp simp: cvalid_u_def)
  apply(erule fold_ptr_force_type_valid_footprint_disjoint)
  apply(fastforce simp: size_of_def)
  done

lemma fold_ptr_retyp_disjoint2_u:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
shows "\<lbrakk>cvalid_u t (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d) q;
    {ptr_val p..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t}= {} \<rbrakk>
  \<Longrightarrow> cvalid_u t d q"
apply(clarsimp simp: cvalid_u_def)
apply(erule fold_ptr_retyp_valid_footprint_disjoint2 [OF no_overflow])
apply(simp add: size_of_def)
apply fast
done

lemma fold_ptr_force_type_disjoint2_u:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
shows "\<lbrakk>cvalid_u t (fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d) q;
    {ptr_val p..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t}= {} \<rbrakk>
  \<Longrightarrow> cvalid_u t d q"
apply(clarsimp simp: cvalid_u_def)
apply(erule fold_ptr_force_type_valid_footprint_disjoint2 [OF no_overflow])
apply(simp add: size_of_def)
apply fast
  done

lemma fold_ptr_retyp_disjoint_iff_u:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  shows "{ptr_val p..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t} = {}
  \<Longrightarrow> cvalid_u t (fold (\<lambda>i. ptr_retyp (p +\<^sub>p int i)) [0..<n] d) q = cvalid_u t d q"
  apply standard
   apply (erule (1) fold_ptr_retyp_disjoint2_u [OF no_overflow])
  apply (erule (1) fold_ptr_retyp_disjoint_u)
  done

lemma fold_ptr_force_type_disjoint_iff_u:
  fixes p::"'a::mem_type ptr"
  assumes no_overflow: "0 \<notin> {ptr_val p..+ n * size_of TYPE('a)}"
  shows "{ptr_val p..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t} = {}
  \<Longrightarrow> cvalid_u t (fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d) q = cvalid_u t d q"
  apply standard
   apply (erule (1) fold_ptr_force_type_disjoint2_u [OF no_overflow])
  apply (erule (1) fold_ptr_force_type_disjoint_u)
  done

lemma stack_allocs_preserves_typing_u:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "t \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "cvalid_u t d q"
  shows "cvalid_u t d' q"
proof -
  from stack_alloc obtain
    d': "d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d" and
    no_overflow: "0 \<notin> {ptr_val p ..+ n * size_of TYPE('a)}"
    by (cases rule: stack_allocs_cases) auto

  from stack_allocs_disjoint_u [OF stack_alloc no_stack typed]
  have "{ptr_val p..+n * size_of TYPE('a)} \<inter> {q..+size_td t} = {}" .
  from fold_ptr_force_type_disjoint_iff_u [OF no_overflow this, where d=d ] typed show ?thesis
    by (simp add: d')
qed

lemma stack_allocs_root_ptr_valid_u_new_cases:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes valid: "root_ptr_valid_u t d' q"
  shows "(\<exists>i<n. q = ptr_val (p +\<^sub>p int i) \<and> t = typ_uinfo_t (TYPE('a))) \<or> root_ptr_valid_u t d q"
proof (cases "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> {q ..+ size_td t} = {}")
  case True
  with stack_alloc valid show ?thesis
    by (smt (verit) disjoint_iff fold_ptr_force_type_other intvlI root_ptr_valid_u_def
        stack_allocs_cases valid_root_footprint_def)
next
  case False
  with stack_alloc array_to_index_span stack_alloc valid show ?thesis
    by (smt (verit, ccfv_SIG) disjoint_iff root_ptr_valid_root_ptr_valid_u_conv
        root_ptr_valid_u_cases size_of_tag stack_allocs_root_ptr_valid_same_type_cases)
qed

lemma cvalid_u_c_guard_u:
  "cvalid_u t d a \<Longrightarrow> c_guard_u t a"
  by (simp add: cvalid_u_def)

lemma stack_allocs_preserves_root_ptr_valid_u:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes no_stack: "t \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  assumes typed: "root_ptr_valid_u t d q"
  shows "root_ptr_valid_u t d' q"
proof -
  from stack_alloc obtain
    d': "d' = fold (\<lambda>i. ptr_force_type (p +\<^sub>p int i)) [0..<n] d" and
    no_overflow: "0 \<notin> {ptr_val p ..+ n * size_of TYPE('a)}"
    by (cases rule: stack_allocs_cases) auto

  from typed have typed_q: "cvalid_u t d q"
    by (simp add: root_ptr_valid_u_cvalid_u)

  from stack_allocs_disjoint_u [OF stack_alloc no_stack this]
  have disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> {q..+size_td t} = {}" .
  from stack_allocs_preserves_typing_u [OF stack_alloc no_stack typed_q]
  have typed': "cvalid_u t d' q " .
  hence valid_fp: "valid_footprint d' q t"
    by (simp add: cvalid_u_def)

  show ?thesis
    apply (simp add: root_ptr_valid_u_def valid_root_footprint_valid_footprint_dom_conv valid_fp
        cvalid_u_c_guard_u [OF typed'])
    apply (simp add: d')
    using disj fold_ptr_force_type_other
    by (smt (verit) d' disjoint_iff intvlI root_ptr_valid_u_def stack_alloc
        stack_allocs_cases typed valid_root_footprint_dom_typing)
qed

lemma stack_allocs_root_ptr_valid_u_other:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes valid_d: "root_ptr_valid_u t d q"
  assumes non_stack: "t \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  shows "root_ptr_valid_u t d' q"
proof (cases "root_ptr_valid_u t d' q")
  case True
  then show ?thesis by simp
next
  case False
  from stack_alloc
  show ?thesis
    apply (rule stack_allocs_cases)
    using False valid_d non_stack
    using stack_alloc stack_allocs_preserves_root_ptr_valid_u by blast
qed

lemma stack_allocs_root_ptr_valid_u_same:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes i: "i < n"
  assumes addr_eq: "q = ptr_val (p +\<^sub>p int i)"
  assumes match: "t = typ_uinfo_t (TYPE('a))"
  shows "root_ptr_valid_u t d' q"
proof (cases "root_ptr_valid_u t d' q")
  case True
  then show ?thesis by simp
next
  case False
  from stack_alloc have "root_ptr_valid d' (p +\<^sub>p int i)"
    apply  (rule stack_allocs_cases)
    using i
    by auto

  with addr_eq match show ?thesis
    apply (clarsimp simp add: root_ptr_valid_def root_ptr_valid_u_def)
    apply (simp add: c_guard_def c_guard_u_def c_null_guard_def c_null_guard_u_def
        ptr_aligned_def ptr_aligned_u_def)
    apply (auto simp add: align_of_def align_td_uinfo[symmetric] size_of_def  )
    done
qed

lemma stack_allocs_root_ptr_valid_u_cases:
  assumes stack_alloc: "(p, d') \<in> stack_allocs n \<S> (TYPE('a::mem_type)) d"
  assumes non_stack_byte: "t \<noteq> typ_uinfo_t (TYPE(stack_byte))"
  shows "root_ptr_valid_u t d' q \<longleftrightarrow>
    (\<exists>i<n. q = ptr_val (p +\<^sub>p int i) \<and> t = typ_uinfo_t (TYPE('a))) \<or>
    root_ptr_valid_u t d q
    "
  using stack_alloc non_stack_byte
    stack_allocs_root_ptr_valid_u_new_cases  stack_allocs_root_ptr_valid_u_other
    stack_allocs_root_ptr_valid_u_same
  by metis

lemma stack_releases_root_ptr_valid_u1:
  fixes p::"'a::mem_type ptr"
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes non_stack_q: "t \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes root_q: "root_ptr_valid_u t (stack_releases n p d) q"
  shows  "{ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> {q ..+ size_td t} = {} \<and> root_ptr_valid_u t d q"
  apply (rule context_conjI)
  subgoal
    using assms
    by (smt (verit, best) cvalid_u_def disjoint_iff in_ptr_span_itself ptr_val.ptr_val_def
      root_ptr_valid_u_cvalid_u size_of_tag stack_releases_valid_root_footprint sub_typ_stack_byte_u
      valid_root_footprint_overlap_sub_typ)
  subgoal
    using assms
    by (smt (verit, best) disjoint_iff intvlI root_ptr_valid_u_def stack_releases_other valid_root_footprint_def)
  done

lemma stack_releases_root_ptr_valid_u2:
  fixes p::"'a::mem_type ptr"
  assumes disj: "{ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> {q ..+ size_td t} = {}"
  assumes valid_q: "root_ptr_valid_u t d q"
  shows "root_ptr_valid_u t (stack_releases n p d) q"
  using assms
  by (simp add: intvlI orthD2 root_ptr_valid_u_def stack_releases_other valid_root_footprint_def)

lemma stack_release_root_ptr_valid_u2:
  fixes p::"'a::mem_type ptr"
  assumes disj: "ptr_span p \<inter> {q ..+ size_td t} = {}"
  assumes valid_q: "root_ptr_valid_u t d q"
  shows "root_ptr_valid_u t (stack_release p d) q"
  using assms
  by (smt (verit, best) disjoint_iff intvlI root_ptr_valid_u_def stack_release_other valid_root_footprint_def)

lemma stack_releases_root_ptr_valid_u_cases:
  fixes p::"'a::mem_type ptr"
  assumes non_stack_p: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes non_stack_q: "t \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows  "root_ptr_valid_u t (stack_releases n p d) q \<longleftrightarrow>
    {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> {q ..+ size_td t} = {} \<and> root_ptr_valid_u t d q"
  using assms stack_releases_root_ptr_valid_u1 stack_releases_root_ptr_valid_u2 by blast

lemma valid_root_footprint_is_root:
  assumes wf: "wf_desc t"
  assumes wf_size: "wf_size_desc t"
  assumes f: "field_lookup t path 0 = Some (s, n)"
  assumes footprint_t: "valid_footprint d a t"
  assumes root_s: "valid_root_footprint d (a + of_nat n) s"
  shows "(t = s \<and> path = [])"
proof (cases "path")
  case Nil
  with f have "t = s"
    by simp
  with Nil show ?thesis by simp
next
  case (Cons fld path')
  from f have neq: "t \<noteq> s"
    using field_lookup_same_type_empty(1) local.Cons by blast
  from f have s_t: "s \<le> t"
    using td_set_field_lookupD typ_tag_le_def by blast
  from neq s_t have "\<not> t \<le> s"
    using sub_tag_antisym by blast
  with valid_root_footprint_overlap_sub_typ [OF root_s footprint_t]
  have "{a + word_of_nat n..+size_td s} \<inter> {a..+size_td t} = {}"
    by blast
  moreover
  from f have td_set: "(s,n) \<in> td_set t 0"
    using local.wf td_set_field_lookup by blast
  from td_set_offset_size [OF td_set] have "{a + word_of_nat n..+size_td s} \<subseteq>  {a..+size_td t}"
    by (simp add: intvl_le)
  moreover
  from field_lookup_wf_size_desc_gt [OF f wf_size] have "0 < size_td s" .
  hence "{a + word_of_nat n..+size_td s} \<noteq> {}"
    by (simp add: intvl_non_zero_non_empty)
  ultimately have False
    by blast
  then show ?thesis by simp
qed

corollary root_ptr_valid_u_is_root:
  assumes wf: "wf_desc t"
  assumes wf_size: "wf_size_desc t"
  assumes f: "field_lookup t path 0 = Some (s, n)"
  assumes cvalid_u_t: "cvalid_u t d a"
  assumes root_s: "root_ptr_valid_u s d (a + of_nat n)"
  shows "(t = s \<and> path = [])"
proof -
  from cvalid_u_t have footprint_t: "valid_footprint d a t" by (simp add: cvalid_u_def)
  from root_s have "valid_root_footprint d (a + of_nat n) s" by (simp add: root_ptr_valid_u_def)
  from valid_root_footprint_is_root [OF wf wf_size f footprint_t this] show ?thesis .
qed

lemma valid_footprint_field_lookup:
  assumes wf: "wf_desc t"
  assumes wf_size_desc: "wf_size_desc t"
  assumes valid_t: "valid_footprint d a t"
  assumes fl: "field_lookup t path1 0 = Some (s, n)"
  shows "valid_footprint d (a + word_of_nat n) s"
  using valid_t fl wf_size_desc
  apply (clarsimp simp add: valid_footprint_def Let_def, intro conjI)
  subgoal using field_lookup_wf_size_desc_gt by blast
  subgoal by (smt (verit, ccfv_SIG) Abs_fnat_hom_add add.commute add_less_mono1 field_lookup_offset_size'
      group_cancel.add2 map_list_map_trans order_less_le_trans td_set_field_lookupD typ_slice_td_set)
  done

lemma in_set_mapD:"x \<in> set (map f xs) \<Longrightarrow> \<exists>y \<in> set xs. x = f y "
  by (induct xs) auto

lemma findSomeI: "x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> \<exists>x. find P xs = Some x"
  by (induct xs) auto


lemma find_in_set_inj_distinct:
  "inj_on P (set (map fst xs)) \<Longrightarrow> (x, v) \<in> set xs \<Longrightarrow> P x \<Longrightarrow>  distinct (map fst xs) \<Longrightarrow>
    find (\<lambda>(x, _). P x) xs = Some (x, v)"
  by (induct xs) (auto simp add: injD rev_image_eqI)

definition "inj_on_true P A = (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> P x \<longrightarrow> P y \<longrightarrow> x = y)"

lemma "inj_on P A \<Longrightarrow> inj_on_true P A"
  by (auto simp add: inj_on_def inj_on_true_def)

lemma inj_on_trueD: "inj_on_true P A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P x \<Longrightarrow> P y  \<Longrightarrow> x = y"
  by (simp add: inj_on_true_def)

lemma inj_on_trueI: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P x \<Longrightarrow> P y  \<Longrightarrow> x = y) \<Longrightarrow> inj_on_true P A"
  by (simp add: inj_on_true_def)

lemma inj_on_true_mono: "A \<subseteq> B \<Longrightarrow> inj_on_true P B \<Longrightarrow> inj_on_true P A"
  by (auto simp add: inj_on_true_def)

lemma find_in_set_inj_on_true_distinct:
  "inj_on_true P (set (map fst xs)) \<Longrightarrow> (x, v) \<in> set xs \<Longrightarrow> P x \<Longrightarrow>  distinct (map fst xs) \<Longrightarrow>
    find (\<lambda>(x, _). P x) xs = Some (x, v)"
  apply (induct xs)
   apply simp
  apply simp
  by (smt (verit, best) case_prod_beta' fst_conv image_iff inj_on_true_def insertCI)

lemma find_in_set_inj_on_true_distinct':
  "inj_on_true P (set xs) \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x \<Longrightarrow>  distinct xs \<Longrightarrow>
    find (\<lambda>x. P x) xs = Some x"
  apply (induct xs)
   apply simp
  apply simp
  by (metis inj_on_true_def insertCI)


lemma typ_tag_le_size_le: "t < (u::typ_uinfo) \<Longrightarrow> size t < size u"
  using td_set_size_lte
  by (metis typ_tag_le_def typ_tag_lt_def)

lemma c_null_guard_intvl_nat_conv:
  fixes p::"'a::mem_type ptr"
  assumes c_null_guard: "c_null_guard p"
  shows "ptr_span p = {x. (unat (ptr_val p) \<le> unat x \<and> unat x < (unat (ptr_val p) + size_of TYPE('a)))}"
proof -
  from c_null_guard
  have "c_null_guard_u (typ_uinfo_t TYPE('a)) (ptr_val p)"
    by (simp add:  c_null_guard_c_null_guard_u_conv)
  from c_null_guard_u_intvl_nat_conv [OF this]
  show ?thesis
    by (simp add: size_of_def)
qed

lemma c_null_guard_ptr_add:
  fixes p::"'a::mem_type ptr"
  assumes bound:  "unat (ptr_val p) + Suc n * size_of TYPE('a) \<le> addr_card"
  assumes not_null: "ptr_val p \<noteq> 0"
  assumes le: "i \<le> n"
  shows "c_null_guard (p +\<^sub>p int i)"
proof -

  from bound le have bound1: "unat (ptr_val p) + i * size_of TYPE('a) \<le> addr_card"
    by (meson add_le_mono dual_order.eq_iff dual_order.trans le_SucI mult_le_cancel2)
  from bound le have bound2: "unat (ptr_val p) + i * size_of TYPE('a) + size_of TYPE('a) \<le> addr_card"
    by (smt (verit, ccfv_SIG) bound1 less_le_mult mult_strict_right_mono not_less_eq_eq of_nat_add of_nat_le_iff of_nat_mult)

  show ?thesis
    apply (clarsimp simp add: ptr_add_def c_null_guard_def intvl_def)
    using bound1 bound2 not_null
    by (smt (verit, del_insts) Abs_fnat_hom_add Abs_fnat_hom_mult add_eq_0_iff_both_eq_0 add_mono_thms_linordered_field(4) eq_imp_le le_Suc_ex len_of_addr_card trans_less_add1 unat_of_nat_len unsigned_0 word_unat.Rep_inverse')
qed

lemma ptr_add_disjoint_index:
  fixes p::"'a::mem_type ptr"
  assumes bound:  "unat (ptr_val p) + Suc n * size_of TYPE('a) \<le> addr_card"
  assumes le: "i < n"
  assumes n: "c_null_guard (p +\<^sub>p int n)"
  assumes i: "c_null_guard (p +\<^sub>p int i)"
  shows "ptr_span (p +\<^sub>p int n) \<inter> ptr_span (p +\<^sub>p int i) = {}"
proof -
  from bound le have bound_i: "unat (ptr_val p) + Suc i * size_of TYPE('a) \<le> addr_card"
    by (smt (verit, best) Suc_less_SucD add_le_cancel_left dual_order.strict_iff_not le_trans mult_less_cancel2 nat_le_linear)


  from bound have bound1: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card" by simp
  from bound have bound2: "unat (ptr_val p) + n * size_of TYPE('a) + size_of TYPE('a) \<le> addr_card"
    by simp

  from bound_i have bound_i1: "unat (ptr_val p) + i * size_of TYPE('a) \<le> addr_card" by simp
  from bound_i have bound_i2: "unat (ptr_val p) + i * size_of TYPE('a) + size_of TYPE('a) \<le> addr_card"
    by simp

  show ?thesis
    apply (simp add: c_null_guard_intvl_nat_conv n i)
    using le bound n i bound1 bound2 bound_i1 bound_i2
    by (auto simp add: ptr_add_def)
      (smt (verit) len_of_addr_card less_le_mult mult_strict_right_mono of_nat_add of_nat_inverse of_nat_le_iff of_nat_less_iff of_nat_mult word_unat.Rep_inverse)
qed

lemma ptr_add_disjoint_last:
  fixes p::"'a::mem_type ptr"
  assumes bound:  "unat (ptr_val p) + Suc n * size_of TYPE('a) \<le> addr_card"
  assumes not_null: "ptr_val p \<noteq> 0"
  shows  "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span (p +\<^sub>p int n) = {}"
proof -
  {
    fix i assume i_bound: "i<n"
    have "ptr_span (p +\<^sub>p int i) \<inter> ptr_span (p +\<^sub>p int n) = {}"
    proof -
      from c_null_guard_ptr_add [OF bound not_null] i_bound obtain
        "c_null_guard (p +\<^sub>p int n)" and "c_null_guard (p +\<^sub>p int i)" by auto
      from ptr_add_disjoint_index [OF bound i_bound this]
      show ?thesis by blast
    qed
  }

  then show ?thesis
    by (auto simp add: array_index_span_conv)
qed

lemma h_val_fold:
  fixes p::"'a::mem_type ptr"
  assumes bound: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card"
  assumes not_null: "ptr_val p \<noteq> 0"
  assumes i_bound: "i < n"
  shows"h_val ((fold (\<lambda>i. heap_update (p +\<^sub>p int i) v) [0..<n]) h) (p +\<^sub>p int i) = v"
  using bound i_bound
proof (induct n arbitrary: h i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain i_bound: "i < Suc n" and bound: "unat (ptr_val p) + Suc n * size_of TYPE('a) \<le> addr_card" by blast
  hence bound': "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card" by simp
  show ?case
  proof (cases "i = n")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    with i_bound have i_bound': "i < n" by simp
    note hyp = Suc.hyps [OF bound' i_bound']
    from c_null_guard_ptr_add [OF bound not_null, of n]
    have null_guard_n: "c_null_guard (p +\<^sub>p int n)" by simp
    from c_null_guard_ptr_add [OF bound not_null, of i] i_bound'
    have null_guard_i: "c_null_guard (p +\<^sub>p int i)" by simp
    from ptr_add_disjoint_index [OF bound i_bound' null_guard_n null_guard_i]
    have disj: "ptr_span (p +\<^sub>p int n) \<inter> ptr_span (p +\<^sub>p int i) = {}" .
    show ?thesis
      by (simp add: h_val_update_regions_disjoint [OF disj] hyp)
  qed
qed

lemma h_val_fold_disjoint:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}"
  shows "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) (v i)) [0..<n] h) q =
         h_val h q"
  using disj
proof (induct n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems have disj: "{ptr_val p..+Suc n * size_of TYPE('a)} \<inter> ptr_span q = {}" .
  from disj have disj': "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}"
    by (smt (verit, best) first_in_intvl intvlD intvlI intvl_inter le_add2 mult_Suc order_less_le_trans orthD2 sz_nzero)
  have "ptr_span (p +\<^sub>p int n) \<subseteq>{ptr_val p..+Suc n * size_of TYPE('a)}"
    by (metis (no_types, lifting) CTypesDefs.ptr_add_def intvl_le mult_Suc nat_le_linear
        of_int_of_nat_eq of_nat_mult ptr_val.simps)

  with disj have disj_n: "ptr_span (p +\<^sub>p int n) \<inter> ptr_span q = {}"
    using intvl_le by fastforce

  note hyp = Suc.hyps [OF disj']
  show ?case by (simp add: h_val_update_regions_disjoint [OF disj_n] hyp)
qed

lemma h_val_fold_zero_disjoint:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}"
  shows "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n] h) q =
         h_val h q"
  using disj
  by (rule  h_val_fold_disjoint)

lemma fold_heap_update_commute:
  fixes p::"'a:: mem_type ptr"
  fixes q::"'b:: mem_type ptr"
  assumes disjoint: "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {} "
  shows "fold (\<lambda>i. heap_update (p +\<^sub>p int i) (v i)) [0..<n] (heap_update q x h) =
          (heap_update q x) (fold (\<lambda>i. heap_update (p +\<^sub>p int i) (v i)) [0..<n] h)"
  using disjoint
proof (induct n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems have disj: "{ptr_val p..+Suc n * size_of TYPE('a)} \<inter> ptr_span q = {}" .
  from disj have disj': "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}"
    by (smt (verit, best) first_in_intvl intvlD intvlI intvl_inter le_add2 mult_Suc order_less_le_trans orthD2 sz_nzero)
  have "ptr_span (p +\<^sub>p int n) \<subseteq>{ptr_val p..+Suc n * size_of TYPE('a)}"
    by (metis (no_types, lifting) CTypesDefs.ptr_add_def intvl_le mult_Suc nat_le_linear
        of_int_of_nat_eq of_nat_mult ptr_val.simps)

  with disj have disj_n: "ptr_span (p +\<^sub>p int n) \<inter> ptr_span q = {}"
    using intvl_le by fastforce
  note hyp = Suc.hyps [OF disj']
  note commute =  heap_update_commute [OF disj_n, simplified]
  show ?case apply simp
    by (simp add:  hyp commute)
qed

lemma fold_heap_update_padding_commute:
  fixes p::"'a:: mem_type ptr"
  fixes q::"'b:: mem_type ptr"
  assumes disjoint: "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {} "
  assumes lbs: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)"
  assumes lbs': "length bs' = size_of TYPE('b)"
  shows "fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n] (heap_update_padding q x bs' h) =
          (heap_update_padding q x bs') (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n] h)"
  using disjoint lbs
proof (induct n arbitrary: h bs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain disj: "{ptr_val p..+Suc n * size_of TYPE('a)} \<inter> ptr_span q = {}" and
    lbs_n: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)" and lbs_n': "length (bs n) = size_of TYPE('a)"
    by auto
  from disj have disj': "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}"
    by (smt (verit, best) first_in_intvl intvlD intvlI intvl_inter le_add2 mult_Suc order_less_le_trans orthD2 sz_nzero)
  have "ptr_span (p +\<^sub>p int n) \<subseteq>{ptr_val p..+Suc n * size_of TYPE('a)}"
    by (metis (no_types, lifting) CTypesDefs.ptr_add_def intvl_le mult_Suc nat_le_linear
        of_int_of_nat_eq of_nat_mult ptr_val.simps)

  with disj have disj_n: "ptr_span (p +\<^sub>p int n) \<inter> ptr_span q = {}"
    using intvl_le by fastforce
  note hyp = Suc.hyps [OF disj' lbs_n]
  note commute =  heap_update_padding_commute [OF disj_n lbs_n'  lbs', simplified]
  show ?case
    apply simp
    apply (simp add: hyp commute )
    done
qed

lemma fold_heap_update_padding_heap_update_commute:
  fixes p::"'a:: mem_type ptr"
  fixes q::"'b:: mem_type ptr"
  assumes disjoint: "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {} "
  assumes lbs: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)"
  shows "fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n] (heap_update q x h) =
          (heap_update q x) (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n] h)"
  using disjoint lbs
proof (induct n arbitrary: h bs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain disj: "{ptr_val p..+Suc n * size_of TYPE('a)} \<inter> ptr_span q = {}" and
    lbs_n: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)" and lbs_n': "length (bs n) = size_of TYPE('a)"
    by auto
  from disj have disj': "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}"
    by (smt (verit, best) first_in_intvl intvlD intvlI intvl_inter le_add2 mult_Suc order_less_le_trans orthD2 sz_nzero)
  have "ptr_span (p +\<^sub>p int n) \<subseteq>{ptr_val p..+Suc n * size_of TYPE('a)}"
    by (metis (no_types, lifting) CTypesDefs.ptr_add_def intvl_le mult_Suc nat_le_linear
        of_int_of_nat_eq of_nat_mult ptr_val.simps)

  with disj have disj_n: "ptr_span (p +\<^sub>p int n) \<inter> ptr_span q = {}"
    using intvl_le by fastforce
  note hyp = Suc.hyps [OF disj' lbs_n]
  note commute =  heap_update_padding_heap_update_commute [OF disj_n lbs_n' , simplified]
  show ?case
    apply simp
    apply (simp add: hyp commute )
    done
qed

lemma fold_heap_update_collapse:
  fixes p::"'a::xmem_type ptr"
  assumes bound: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card"
  assumes not_null: "ptr_val p \<noteq> 0"
  shows "fold (\<lambda>i. heap_update (p +\<^sub>p int i) (v i)) [0..<n]
          ((fold (\<lambda>i. heap_update (p +\<^sub>p int i) (w i)) [0..<n]) h) =
         fold (\<lambda>i. heap_update (p +\<^sub>p int i) (v i)) [0..<n] h"
  using bound
proof (induct n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain bound: "unat (ptr_val p) + Suc n * size_of TYPE('a) \<le> addr_card" by blast
  hence bound': "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card" by simp
  from ptr_add_disjoint_last [OF bound not_null]
  have disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span (p +\<^sub>p int n) = {}" .
  show ?case
    apply simp
    apply (subst (2)  Suc.hyps [OF bound', symmetric])
    apply (subst fold_heap_update_commute [OF disj])
    apply (simp add: heap_update_collapse)
    done
qed

lemma fold_heap_update_padding_collapse:
  fixes p::"'a::xmem_type ptr"
  assumes bound: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card"
  assumes not_null: "ptr_val p \<noteq> 0"
  assumes lbs: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)"
  assumes lbs': "\<And>i. i < n \<Longrightarrow> length (bs' i) = size_of TYPE('a)"
  shows "fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n]
          ((fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (w i) (bs' i)) [0..<n]) h) =
         fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n] h"
  using bound lbs lbs'
proof (induct n arbitrary: h bs bs')
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain
    bound: "unat (ptr_val p) + Suc n * size_of TYPE('a) \<le> addr_card" and
    lbs_n: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)" and
    lbs'_n: "\<And>i. i < n \<Longrightarrow> length (bs' i) = size_of TYPE('a)" and
    lbs'_n': "length (bs' n) = size_of TYPE('a)" and
    lbs_n': "length (bs n) = size_of TYPE('a)"
    by auto
  hence bound': "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card" by simp
  from ptr_add_disjoint_last [OF bound not_null]
  have disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span (p +\<^sub>p int n) = {}" .
  show ?case
    apply simp
    apply (subst (2)  Suc.hyps [OF bound' lbs_n lbs'_n, symmetric])
    apply (assumption)
    apply assumption
    apply (subst fold_heap_update_padding_commute [OF disj lbs_n lbs'_n'])
     apply (assumption)
    apply (simp add: heap_update_padding_collapse [OF lbs_n' lbs'_n'])
    done
qed

lemma fold_heap_update_padding_heap_update_collapse:
  fixes p::"'a::xmem_type ptr"
  assumes bound: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card"
  assumes not_null: "ptr_val p \<noteq> 0"
  assumes lbs: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)"
  shows "fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n]
          ((fold (\<lambda>i. heap_update (p +\<^sub>p int i) (w i) ) [0..<n]) h) =
         fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (v i) (bs i)) [0..<n] h"
  using bound lbs
proof (induct n arbitrary: h bs )
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain
    bound: "unat (ptr_val p) + Suc n * size_of TYPE('a) \<le> addr_card" and
    lbs_n: "\<And>i. i < n \<Longrightarrow> length (bs i) = size_of TYPE('a)" and
    lbs_n': "length (bs n) = size_of TYPE('a)"
    by auto
  hence bound': "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card" by simp
  from ptr_add_disjoint_last [OF bound not_null]
  have disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span (p +\<^sub>p int n) = {}" .
  show ?case
    apply simp
    apply (subst (2)  Suc.hyps [OF bound' lbs_n , symmetric])
    apply (assumption)
    apply (subst fold_heap_update_padding_heap_update_commute [OF disj lbs_n ])
     apply (assumption)
    thm heap_update_padding_heap_update_collapse
    apply (simp add: heap_update_padding_heap_update_collapse [OF lbs_n'])
    done
qed

section "Open Types"

named_theorems \<T>_def and
  ptr_valid_definition and fold_ptr_valid and ptr_valid and ptr_valid_u_recursion and
  addressable_ptr_valid_field and plift_simps and stack_the_default_plift and
  plift_heap_update_padding_heap_update_conv and
  plift_heap_update_list_stack_byte

lemma list_ex_array_fields[simp]:
  "list_ex P (array_fields m) \<longleftrightarrow> (\<exists>n<m. P [replicate n CHR ''1''])"
  by (simp add: array_fields_def list_ex_iff Bex_def)

lemma list_all_field_lookup_array_fields[simp]:
  "CARD('n) = m \<Longrightarrow>
  list_all
    (\<lambda>f. \<exists>a b. field_lookup (typ_uinfo_t TYPE('a::c_type['n::finite])) f 0 = Some (a, b))
    (array_fields m)"
  by (simp add: array_fields_def)

lemma list_ex_subst_def:
  "c \<equiv> xs \<Longrightarrow> list_ex P c = list_ex P xs"
  by simp

lemma ex_field_lookup_append:
  "wf_desc t \<Longrightarrow>
    field_lookup t p1 n1 = Some (u, m1) \<Longrightarrow>
    field_lookup u p2 n2 = Some (v, m2) \<Longrightarrow>
  \<exists>m. field_lookup t (p1 @ p2) n3 = Some (v, m)"
  by (metis field_lookup_offset_shift' field_lookup_prefix_Some')

named_theorems addressable_field_exec

locale open_types =
  fixes \<T>:: "(typ_uinfo * qualified_field_name list) list" \<comment> \<open>toplevel addressable fields of a type\<close>
  assumes mem_type_u: "\<And>t fs. (t, fs) \<in> set \<T> \<Longrightarrow> mem_type_u t"
  assumes wf_\<T>':
    "list_all (\<lambda>(t, fs).
      [] \<notin> set fs \<and>
      list_all (\<lambda>f. field_lookup t f 0 \<noteq> None) fs \<and>
      distinct_prop disj_fn fs) \<T>"
  assumes distinct_\<T>: "distinct (map fst \<T>)"
begin

inductive addressable_field :: "typ_uinfo \<Rightarrow> qualified_field_name \<Rightarrow> typ_uinfo \<Rightarrow> bool" where
  addressable_field_refl[intro!, simp]: "\<And>t. addressable_field t [] t"
| addressable_field_step: "\<And>t fs p p' u v n.
    map_of \<T> t = Some fs \<Longrightarrow> p \<in> set fs \<Longrightarrow> field_lookup t p 0 = Some (u, n) \<Longrightarrow>
    addressable_field u p' v \<Longrightarrow> addressable_field t (p @ p') v"

inductive ptr_valid_u :: "typ_uinfo \<Rightarrow> heap_typ_desc \<Rightarrow> addr \<Rightarrow> bool" for t d where
  "\<And>r p a. root_ptr_valid_u r d a \<Longrightarrow> addressable_field r p t \<Longrightarrow>
    ptr_valid_u t d (a + of_nat (field_offset_untyped r p))"

definition ptr_valid :: "heap_typ_desc \<Rightarrow> 'a::mem_type ptr \<Rightarrow> bool" where
  [ptr_valid_definition]:
    "ptr_valid d p \<equiv> ptr_valid_u (typ_uinfo_t TYPE('a)) d (ptr_val p)"

lemma addressable_field_single:
  "map_of \<T> t = Some fs \<Longrightarrow> p \<in> set fs \<Longrightarrow> field_lookup t p 0 = Some (v, n) \<Longrightarrow>
     addressable_field t p v"
  using addressable_field_step[of t fs p v n "[]"] by auto

lemma addressable_field_append:
  assumes *: "addressable_field t p1 u" "addressable_field u p2 v"
  shows "addressable_field t (p1 @ p2) v"
proof (use * in \<open>induction arbitrary: p2 v\<close>)
  case *: (addressable_field_step t fs p p' u v n w p1)

  show ?case
    unfolding append_assoc
    apply (rule addressable_field_step[OF *(1,2,3)])
    apply (rule *)+
    done
qed simp

lemma addressable_field_rev_induct[consumes 1, case_names refl step]:
  assumes *: "addressable_field t p u"
  assumes 1: "\<And>t. P t [] t"
  assumes 2: "\<And>t p' u fs f v n.
    addressable_field t p' u \<Longrightarrow> map_of \<T> u = Some fs \<Longrightarrow> f \<in> set fs \<Longrightarrow>
      field_lookup u f 0 = Some (v, n) \<Longrightarrow> P t p' u \<Longrightarrow> P t (p' @ f) v"
  shows "P t p u"
proof -
  have "addressable_field t p1 u \<Longrightarrow> P t p1 u \<Longrightarrow> P t (p1 @ p2) v"
    if *: "addressable_field u p2 v" for t p1 u p2 v
  proof (use * in \<open>induction arbitrary: t p1\<close>)
    case *: (addressable_field_step t fs f q u v n w)
    show ?case
      unfolding append_assoc[symmetric]
      by (intro "*.IH" 2[OF "*.prems"(1) "*"(1,2,3)] *)
         (intro addressable_field_append[OF "*.prems"(1)]
                addressable_field_single[OF *(1,2,3)])
  qed simp
  from this[OF * addressable_field_refl 1] show ?thesis by simp
qed

lemma addressable_field_rev_cases[consumes 1, case_names refl step]:
  assumes *: "addressable_field t p u"
  assumes 1: "t = u \<Longrightarrow> p = [] \<Longrightarrow> P"
  assumes 2: "\<And>p' fs f v n.
    addressable_field t p' v \<Longrightarrow> map_of \<T> v = Some fs \<Longrightarrow> f \<in> set fs \<Longrightarrow>
      field_lookup v f 0 = Some (u, n) \<Longrightarrow> p = p' @ f \<Longrightarrow> P"
  shows P
  using *
  by (induction t==t p==p u==u rule: addressable_field_rev_induct)
     (use 1 2 in auto)

lemma wf_\<T>: "map_of \<T> t = Some fs \<Longrightarrow> list_all (\<lambda>f. field_lookup t f 0 \<noteq> None) fs"
  using wf_\<T>' by (auto simp: list_all_iff dest!: map_of_SomeD)

lemma \<T>_not_nil: "map_of \<T> t = Some fs \<Longrightarrow> [] \<notin> set fs"
  using wf_\<T>' by (auto simp: list_all_iff dest!: map_of_SomeD)

lemma addressable_field_refl_iff[simp]:
  "addressable_field t [] u \<longleftrightarrow> t = u"
  by (subst addressable_field.simps) (auto simp add: \<T>_not_nil cong: HOL.conj_cong)

lemma addressable_field_domain:
  "addressable_field t p u \<Longrightarrow> t \<in> fst ` set \<T> \<or> (t = u \<and> p = [])"
  apply (subst (asm) addressable_field.simps)
  by (auto simp: image_iff split_paired_Ball dest!: map_of_SomeD) blast+

lemma addressable_fieldD_mem_type_u:
  "addressable_field t p u \<Longrightarrow> mem_type_u t \<or> (t = u \<and> p = [])"
  by (auto dest!: addressable_field_domain mem_type_u)

lemma addressable_fieldD_field_lookup:
  assumes p: "addressable_field t p u" shows "\<exists>n. field_lookup t p 0 = Some (u, n)"
  by (use p in induction)
     (auto intro: ex_field_lookup_append mem_type_u mem_type_u.wf_desc dest: map_of_SomeD)

lemma addressable_field_same_iff[simp]:
  "addressable_field t p t \<longleftrightarrow> p = []"
  using addressable_fieldD_field_lookup[of t p t] field_lookup_same_type_empty(1)[of t p 0 t]
  by auto

lemma addressable_fieldD_field_lookup':
  "addressable_field t p u \<Longrightarrow> field_lookup t p 0 = Some (u, field_offset_untyped t p)"
  using addressable_fieldD_field_lookup[of t p u] by (auto simp add: field_offset_untyped_def)

lemma addressable_fieldD_field_ti:
  assumes p: "addressable_field (typ_uinfo_t TYPE('a::c_type)) p t"
  shows "\<exists>u. field_ti TYPE('a) p = Some u \<and> export_uinfo u = t"
  using field_lookup_uinfo_Some_rev[OF addressable_fieldD_field_lookup'[OF p]]
  by (clarsimp simp: field_ti_def simp del: field_lookup_offset_untyped_eq)

lemma addressable_fieldD_field_names:
  "addressable_field t p u \<Longrightarrow> p \<in> set (field_names_u t u)"
  by (auto dest: addressable_fieldD_field_lookup intro: field_lookup_Some_field_names_u(1))

lemma mem_type_u_addressable_field:
  assumes *: "addressable_field t fs u"
  shows "mem_type_u u \<Longrightarrow> mem_type_u t"
  by (use * in induction) (auto intro: mem_type_u dest!: map_of_SomeD)

lemma wf_desc_addressable_field:
  assumes *: "addressable_field t fs u"
  shows "wf_desc t \<Longrightarrow> wf_desc u"
  using addressable_fieldD_field_lookup'[OF *] by (auto intro: field_lookup_wf_desc_pres)

lemma wf_size_desc_addressable_field:
  assumes *: "addressable_field t fs u"
  shows "wf_size_desc t \<Longrightarrow> wf_size_desc u"
  using addressable_fieldD_field_lookup'[OF *] by (auto intro: field_lookup_wf_size_desc_pres)

lemma field_offset_append_of_addressable_field:
  assumes p: "addressable_field t p u" and q: "addressable_field u q v"
  shows "field_offset_untyped t (p @ q) = field_offset_untyped t p + field_offset_untyped u q"
proof -
  have "p = [] \<and> q = [] \<or> mem_type_u t"
    using addressable_fieldD_mem_type_u[OF p] addressable_fieldD_mem_type_u[OF q] by auto
  then show ?thesis
  proof (elim disjE conjE)
    assume "mem_type_u t" then show ?thesis
      by (intro field_names_u_field_offset_untyped_append[OF mem_type_u.wf_desc
                  addressable_fieldD_field_names[OF p] addressable_fieldD_field_names[OF q]])
  qed simp
qed

lemma intvl_subset_of_addressable_field:
  assumes p: "addressable_field t p u"
  shows "{a + of_nat (field_offset_untyped t p) ..+ size_td u} \<subseteq> {a ..+ size_td t}"
  using addressable_fieldD_field_lookup[OF p]
  using intvl_subset_of_field_lookup[of t p u "field_offset_untyped t p" a]
  by (auto simp: field_offset_untyped_def)

lemma root_ptr_valid_u_ptr_valid_u:
  assumes a: "root_ptr_valid_u t d a" shows "ptr_valid_u t d a"
  using ptr_valid_u.intros[OF a addressable_field_refl] by simp

lemma root_ptr_valid_ptr_valid: "root_ptr_valid d p \<Longrightarrow> ptr_valid d p"
  unfolding root_ptr_valid_root_ptr_valid_u_conv ptr_valid_def
  by (rule root_ptr_valid_u_ptr_valid_u)

lemma fold_ptr_valid'[fold_ptr_valid]:
  "ptr_valid_u (typ_uinfo_t TYPE('a::mem_type)) d x = ptr_valid d (PTR('a) x)"
  by (simp add: ptr_valid_def)

lemma ptr_valid_u_trans:
  assumes *: "ptr_valid_u t d a"
  shows "addressable_field t p u \<Longrightarrow> ptr_valid_u u d (a + of_nat (field_offset_untyped t p))"
proof (use * in induction)
  case (1 r q a)
  have eq:
    "a + word_of_nat (field_offset_untyped r q) + word_of_nat (field_offset_untyped t p) =
      a + word_of_nat (field_offset_untyped r (q @ p))"
    using field_offset_append_of_addressable_field[OF 1(2,3)] by simp
  show ?case unfolding eq
    by (intro ptr_valid_u.intros 1 addressable_field_append[OF 1(2,3)])
qed

lemma ptr_valid_u_step:
  assumes *: "map_of \<T> t = Some F" "f \<in> set F" "field_lookup t f 0 = Some (u, n)"
    and a: "ptr_valid_u t d a"
  shows "ptr_valid_u u d (a + of_nat (field_offset_untyped t f))"
  by (rule ptr_valid_u_trans[OF a]) (rule addressable_field_single[OF *])

lemma ptr_valid_u_recursion'[ptr_valid_u_recursion]:
  "ptr_valid_u t d a \<longleftrightarrow>
    root_ptr_valid_u t d a \<or>
    list_ex (\<lambda>(u, fs). list_ex (\<lambda>f. \<exists>a' n. field_lookup u f 0 = Some (t, n) \<and>
      ptr_valid_u u d a' \<and> a = a' + of_nat (field_offset_untyped u f)) fs) \<T>"
proof -
  have
    "root_ptr_valid_u t d
        (a + word_of_nat (field_offset_untyped r p)) \<or>
    (\<exists>x\<in>set \<T>. case x of (u, fs) \<Rightarrow> \<exists>f\<in>set fs.
      (\<exists>n. field_lookup u f 0 = Some (t, n)) \<and>
      (\<exists>a'. ptr_valid_u u d a' \<and>
        a + word_of_nat (field_offset_untyped r p) =
        a' + word_of_nat (field_offset_untyped u f)))"
    if p: "addressable_field r p t" and r: "root_ptr_valid_u r d a"
    for a r p
  proof (use p in \<open>cases rule: addressable_field_rev_cases\<close>)
    case refl with r show ?thesis by simp
  next
    case *: (step p' fs p'' u m)
    then have **: "(u, fs) \<in> set \<T>"
      by (auto simp: map_of_SomeD)
    have "mem_type_u u"
      using mem_type_u[of u fs] *(2) by (auto dest: map_of_SomeD)
    with * have mem_r: "mem_type_u r"
      by (auto dest: mem_type_u_addressable_field)

    have u_t: "addressable_field u p'' t"
      using *(2,3,4) by (rule addressable_field_single)

    show ?thesis
      apply (intro disjI2 bexI[of _ "(u, fs)"] **)
      apply simp
      apply (intro conjI bexI[of _ p''] * exI[of _ "a + of_nat (field_offset_untyped r p')"])
      subgoal using *(4) by (rule exI)
      subgoal using r *(1) by (rule ptr_valid_u.intros)
      apply (simp add: field_offset_append_of_addressable_field[OF *(1) u_t] \<open>p = p' @ p''\<close>)
      done
  qed
  moreover have
    "ptr_valid_u t d
        (a' + word_of_nat (field_offset_untyped r p) + word_of_nat (field_offset_untyped u f))"
    if 1: "(u, fs) \<in> set \<T>" and 2: "f \<in> set fs" "field_lookup u f 0 = Some (t, n)"
      and r: "root_ptr_valid_u r d a'" "addressable_field r p u"
    for u fs f n r p a'
  proof -
    have 1: "map_of \<T> u = Some fs"
      using 1 by (simp add:  map_of_eq_Some_iff[OF distinct_\<T>])
    show ?thesis
      using ptr_valid_u.intros[OF r] addressable_field_single[OF 1 2]
      by (rule ptr_valid_u_trans)
  qed
  ultimately show ?thesis
    by (auto simp: list_ex_iff del: disjCI
             elim!: ptr_valid_u.cases intro: root_ptr_valid_u_ptr_valid_u)
qed

lemma \<T>_distinct: "map_of \<T> t = Some fs \<Longrightarrow> distinct_prop disj_fn fs"
  using wf_\<T>' by (auto simp: list_all_iff dest!: map_of_SomeD)

lemma addressable_field_unique:
  assumes t: "addressable_field r p t" shows "addressable_field r p t' \<Longrightarrow> t = t'"
proof (use t in induction)
  case 1: (addressable_field_step t fs p p' u v n)
  from \<open>addressable_field t (p @ p') t'\<close> show ?case
  proof cases
    case 2: (addressable_field_step fs' q q' w m)
    with 1 have "map_of \<T> t = Some fs" "p \<in> set fs" "q \<in> set fs" by auto
    with 1 \<T>_distinct[of t fs] have "p = q \<or> disj_fn p q"
      using pairwise_set_of_distinct_prop[of disj_fn, OF disj_fn_comm, of fs]
      by (auto simp: pairwise_def)
    with \<open>p @ p' = q @ q'\<close> have [simp]: "q = p \<and> q' = p'"
      by (auto simp: disj_fn_def less_eq_list_def prefix_def append_eq_append_conv2)
    with 1(3) 2(4) have "u = w"
      by simp
    with 1(5) \<open>addressable_field w q' t'\<close> show ?thesis
      by simp
  qed (use 1 in simp)
qed simp

lemma addressable_fields_split:
  assumes r: "addressable_field r p t" "addressable_field r (p @ p') u"
  shows "addressable_field t p' u"
proof (use r in induction)
  case 1: (addressable_field_step t fs p0 p1 u v n)
  from 1(6, 1-5) show ?case
  proof cases
    case 2: (addressable_field_step fs' q q' t' m)
    with 1 have "map_of \<T> t = Some fs" "p0 \<in> set fs" "q \<in> set fs" by auto
    with 1 \<T>_distinct[of t fs] have "p0 = q \<or> disj_fn p0 q"
      using pairwise_set_of_distinct_prop[of disj_fn, OF disj_fn_comm, of fs]
      by (auto simp: pairwise_def)
    with 2(1) have "p0 = q \<and> p1 @ p' = q'"
      by (auto simp: disj_fn_def less_eq_list_def prefix_def append_eq_append_conv2)
    with 1 2 show ?thesis
      by simp
  qed simp
qed simp

lemma addressable_field_antisymm:
  "addressable_field t p u \<Longrightarrow> addressable_field u q t \<Longrightarrow> u = t"
  using addressable_field_append[of t p u q t] by simp

lemma addressable_field_sub_typ: "addressable_field t path u \<Longrightarrow> u \<le> t"
  using addressable_fieldD_field_lookup[of t path u] typ_tag_le_def
  by (blast dest: td_set_field_lookupD)

lemma sub_typ_of_field_lookup:
  "field_lookup (typ_uinfo_t TYPE('a)) p 0 = Some (typ_uinfo_t TYPE('b), n) \<Longrightarrow>
    TYPE('b::mem_type) \<le>\<^sub>\<tau> TYPE('a::mem_type)"
  apply (clarsimp simp add: sub_typ_def)
  apply (rule field_of_sub[of "of_nat n"])
  using field_lookup_offset_size'[of "typ_uinfo_t TYPE('a)" p]
    mem_type_class.u.max_size[where 'a='a]
  by (auto simp add: field_of_def field_offset_def field_offset_untyped_def addr_card_len_of_conv
              intro!: td_set_field_lookupD[of _ p] unat_of_nat_eq[symmetric])

lemma addressable_fields_imp_sub_typ:
  "addressable_field (typ_uinfo_t TYPE('a)) p (typ_uinfo_t TYPE('b)) \<Longrightarrow>
    TYPE('b::mem_type) \<le>\<^sub>\<tau> TYPE('a::mem_type)"
  by (simp add: addressable_field_sub_typ sub_typ_def)

lemma ptr_valid_u_cases:
  assumes t: "mem_type_u t"
  assumes t_a: "ptr_valid_u t d a"
  assumes u_b: "ptr_valid_u u d b"
  shows "disjnt {a..+size_td t} {b..+size_td u} \<or>
    (t = u \<and> a = b) \<or>
    (\<exists>p. addressable_field t p u \<and> t \<noteq> u \<and> b = a + word_of_nat (field_offset_untyped t p)) \<or>
    (\<exists>p. addressable_field u p t \<and> t \<noteq> u \<and> a = b + word_of_nat (field_offset_untyped u p))"
    (is "?disj \<or> ?addr")
proof (rule disjCI2)
  assume a_b: "\<not> ?disj"
  from t_a obtain r f0 x where x0: "root_ptr_valid_u r d x"
    and a: "a = x + of_nat (field_offset_untyped r f0)"
    and r_t: "addressable_field r f0 t"
    by (auto elim!: ptr_valid_u.cases)
  from u_b obtain r' f1 x' where x1: "root_ptr_valid_u r' d x'"
    and b: "b = x' + of_nat (field_offset_untyped r' f1)"
    and r_u: "addressable_field r' f1 u"
    by (auto elim!: ptr_valid_u.cases)
  from a_b have "\<not> disjnt {x ..+ size_td r} {x' ..+ size_td r'}"
    using intvl_subset_of_addressable_field[OF r_t, of x]
    using intvl_subset_of_addressable_field[OF r_u, of x']
    by (auto intro: disjnt_subset1 disjnt_subset2 simp: a b)
  with root_ptr_valid_u_cases[OF x0 x1] have [simp]: "r' = r" "x' = x"
    by (auto simp: disjnt_def)
  have r: "mem_type_u r"
    using r_t t by (rule mem_type_u_addressable_field)
  then have wf_r: "wf_desc r"
    by (rule mem_type_u.wf_desc)
  have "\<not> disjnt
      {(word_of_nat (field_offset_untyped r f0)::addr)..+size_td t}
      {word_of_nat (field_offset_untyped r f1)..+size_td u}"
    using a_b by (simp add: a b)
  with field_lookup_non_prefix_disj'[OF r
      addressable_fieldD_field_lookup'[OF r_t]
      addressable_fieldD_field_lookup'[of r f1 u]] r_u
  obtain f' where "f0 = f1 @ f' \<or> f1 = f0 @ f'"
    by (auto simp: disj_fn_def less_eq_list_def prefix_def)
  then show ?addr
  proof (elim disjE)
    assume "f0 = f1 @ f'"
    with r_t r_u addressable_fields_split[of r f1 u f' t]
    show ?thesis
      by (cases "u = t") (auto simp add: a b field_offset_append_of_addressable_field)
  next
    assume "f1 = f0 @ f'"
    with r_t r_u addressable_fields_split[of r f0 t f' u]
    show ?thesis
      by (cases "u = t") (auto simp add: a b field_offset_append_of_addressable_field)
  qed
qed

lemma ptr_valid_cases':
  fixes p :: "'a::mem_type ptr"
  fixes q :: "'b::mem_type ptr"
  assumes p: "ptr_valid d p"
  assumes q: "ptr_valid d q"
  shows "disjnt (ptr_span p) (ptr_span q) \<or>
    (typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE('b) \<and> ptr_val p = ptr_val q) \<or>
    (\<exists>f. addressable_field (typ_uinfo_t TYPE('a)) f (typ_uinfo_t TYPE('b)) \<and>
      typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<and>
      q = PTR('b) &(p \<rightarrow> f)) \<or>
    (\<exists>f. addressable_field (typ_uinfo_t TYPE('b)) f (typ_uinfo_t TYPE('a)) \<and>
      typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<and>
      p = PTR('a) &(q \<rightarrow> f))"
  using ptr_valid_u_cases[OF _ p[unfolded ptr_valid_def] q[unfolded ptr_valid_def]]
  by (simp add: size_of_def ptr_val_conv field_lvalue_def field_offset_def)

lemma ptr_valid_u_cases_weak:
  assumes "mem_type_u t"
  assumes "ptr_valid_u t d a"
  assumes "ptr_valid_u u d b"
  shows "disjnt {a..+size_td t} {b..+size_td u} \<or>
    (\<exists>p. addressable_field t p u \<and> b = a + word_of_nat (field_offset_untyped t p)) \<or>
    (\<exists>p. addressable_field u p t \<and> a = b + word_of_nat (field_offset_untyped u p))"
  using ptr_valid_u_cases[OF assms] by (cases "t = u") auto

lemma ptr_valid_cases_weak:
  fixes p :: "'a::mem_type ptr"
  fixes q :: "'b::mem_type ptr"
  assumes p: "ptr_valid d p"
  assumes q: "ptr_valid d q"
  shows "disjnt (ptr_span p) (ptr_span q) \<or>
    (\<exists>f. addressable_field (typ_uinfo_t TYPE('a)) f (typ_uinfo_t TYPE('b)) \<and>
      q = PTR('b) &(p \<rightarrow> f)) \<or>
    (\<exists>f. addressable_field (typ_uinfo_t TYPE('b)) f (typ_uinfo_t TYPE('a)) \<and>
      p = PTR('a) &(q \<rightarrow> f))"
  using ptr_valid_cases'[OF assms]
  by (cases "typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE('b)")
     (auto simp: ptr_val_conv field_lvalue_def)

lemma ptr_valid_u_cvalid_u:
  assumes t: "mem_type_u t"
  assumes ptr_valid: "ptr_valid_u t d a"
  shows "cvalid_u t d a"
  using ptr_valid
proof
  fix r fs a' assume r_t: "addressable_field r fs t"
    and a_eq: "a = a' + word_of_nat (field_offset_untyped r fs)"
    and a': "root_ptr_valid_u r d a'"
  have r: "mem_type_u r"
    using mem_type_u_addressable_field[OF r_t t] .
  have align_t: "2 ^ align_td t dvd size_td t"
    using t by (rule mem_type_u.align_size)

  show "cvalid_u t d a" unfolding a_eq
    using r align_t addressable_fieldD_field_lookup'[OF r_t] root_ptr_valid_u_cvalid_u[OF a']
    by (rule mem_type_u.cvalid_u_field_lookup)
qed

lemma ptr_valid_h_t_valid: "ptr_valid d p \<Longrightarrow> d \<Turnstile>\<^sub>t (p::'a::mem_type ptr)"
  unfolding ptr_valid_def cvalid_cvalid_u_conv
  by (rule ptr_valid_u_cvalid_u) simp_all

sublocale ptr_valid?: wf_ptr_valid ptr_valid
  by unfold_locales (rule ptr_valid_h_t_valid)

lemma h_val_heap_update' [plift_simps]:
  fixes p::"'a::mem_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes ptr_valid_p: "ptr_valid d p"
  assumes ptr_valid_q: "ptr_valid d q"
  shows "h_val (heap_update p v h) q = ((h_val h)(p:=v)) q"
  by (metis c_type_class.lift_def lift_heap_update ptr_valid_h_t_valid ptr_valid_p ptr_valid_q)


lemma h_val_heap_update_padding' [plift_simps]:
  fixes p::"'a::mem_type ptr"
  fixes q::"'a::mem_type ptr"
  assumes ptr_valid_p: "ptr_valid d p"
  assumes ptr_valid_q: "ptr_valid d q"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows "h_val (heap_update_padding p v bs h) q = ((h_val h)(p:=v)) q"
  by (smt (verit, best) fun_upd_apply_eq_cases h_val_heap_update_padding
      h_val_heap_update_padding_disjoint lbs local.ptr_valid_h_t_valid ptr_valid_p ptr_valid_q
      ptr_valid_same_type_cases)

lemmas ptr_valid_plift_Some_hval [plift_simps]

theorem disjoint_type_plift:
  fixes p::"'a::mem_type ptr"
  assumes unrelated1: "\<not> TYPE('a) \<le>\<^sub>\<tau> TYPE('b::mem_type)"
  assumes unrelated2: "\<not> TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes ptr_valid_p: "ptr_valid (hrs_htd h) p"
  shows "plift ((hrs_mem_update (heap_update p v) h)) = (plift h::'b ptr \<Rightarrow> 'b option)"
proof -
  from unrelated1 unrelated2 have disj: "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
    using tag_disj_def unfolding sub_typ_def by blast
  from ptr_valid_p have "hrs_htd h \<Turnstile>\<^sub>t p"
    by (simp add: ptr_valid_h_t_valid)

  from clift_heap_update_same [OF this disj]
  have "clift (hrs_mem_update (heap_update p v) h)  = (clift h::'b ptr \<Rightarrow> 'b option) "
    by simp
  then show ?thesis
    apply -
    apply (rule ext)
    by (metis hrs_htd_mem_update plift_None plift_clift_conv)
qed

theorem disjoint_type_update_h_val:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"
  assumes unrelated1: "\<not> TYPE('a) \<le>\<^sub>\<tau> TYPE('b)"
  assumes unrelated2: "\<not> TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  assumes typed_p: "hrs_htd h \<Turnstile>\<^sub>t p"
  assumes typed_q: "hrs_htd h \<Turnstile>\<^sub>t q"
  shows "h_val (hrs_mem (hrs_mem_update (heap_update p v) h)) q = h_val (hrs_mem h) q"
proof -
  from unrelated1 unrelated2 have disj: "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
    using tag_disj_def unfolding sub_typ_def by blast
  from clift_heap_update_same [OF typed_p disj]
  have "clift (hrs_mem_update (heap_update p v) h) q = clift h q"
    by simp
  with typed_p typed_q
  show ?thesis
    by (metis clift_Some_eq_valid h_val_clift hrs_mem_def prod.collapse)
qed

lemma intvl_Suc_0: "{x ..+ Suc 0} = {x}"
  by (auto simp: intvl_def)

lemma ptr_span_subset_of_addressable_field:
  fixes q:: "'a::mem_type  ptr"
  shows "addressable_field t p (typ_uinfo_t TYPE('a)) \<Longrightarrow>
    ptr_val q = x + word_of_nat (field_offset_untyped t p) \<Longrightarrow>
    ptr_span q \<subseteq> {x..+size_td t}"
  using intvl_subset_of_addressable_field[of t p "typ_uinfo_t TYPE('a)" x]
  by (simp flip: size_of_tag)

lemma addressable_field_wf_descD:
  assumes path: "addressable_field t path u"
  shows "t = u \<or> (wf_desc t \<and> wf_desc u)"
  using addressable_fieldD_mem_type_u[OF path] wf_desc_addressable_field[OF path]
  by (blast intro: mem_type_u.wf_desc)

lemma addressable_field_wf_size_descD:
  assumes path: "addressable_field t path u"
  shows "t = u \<or> (wf_size_desc t \<and> wf_size_desc u)"
  using addressable_fieldD_mem_type_u[OF path] wf_size_desc_addressable_field[OF path]
  by (blast intro: mem_type_u.wf_size_desc)

lemma root_ptr_valid_u_ptr_valid_u_cases:
  fixes p q :: addr
  assumes root_valid_p: "root_ptr_valid_u t d p"
  assumes valid_q: "ptr_valid_u s d q"
  shows "{p ..+ size_td t} \<inter> {q ..+ size_td s} = {} \<or>
    (\<exists>path. addressable_field t path s \<and> q = p + of_nat (field_offset_untyped t path))"
proof (cases "{p ..+ size_td t} \<inter> {q ..+ size_td s} = {}")
  case True
  then show ?thesis by simp
next
  case False
  from valid_q
  obtain root path x where
    path: "addressable_field root path s" and
    root_ptr_valid_u: "root_ptr_valid_u root d x" and
    q: "q = x + word_of_nat (field_offset_untyped root path)"
    by (clarsimp simp add: ptr_valid_def elim!: ptr_valid_u.cases)

  then have contained: "{q ..+ size_td s} \<subseteq> {x..+size_td root}"
    using intvl_subset_of_addressable_field[OF path] by (simp add: size_of_def)

  from root_valid_p have root_ptr_valid_u_p: "root_ptr_valid_u t d p"
    by (simp add: root_ptr_valid_root_ptr_valid_u_conv)
  from root_ptr_valid_u_cases [OF root_ptr_valid_u_p root_ptr_valid_u] False contained
  obtain "t = root" "p = x"
    by (metis (no_types, lifting) disj_subset preorder_class.dual_order.refl)
  with path q False show ?thesis
    by auto
qed

lemma root_ptr_valid_u_ptr_valid_cases:
  fixes p :: addr and q :: "'b::mem_type ptr"
  assumes root_valid_p: "root_ptr_valid_u t d p"
  assumes valid_q: "ptr_valid d q"
  shows "{p ..+ size_td t} \<inter> ptr_span q = {} \<or>
    (\<exists>path. addressable_field t path (typ_uinfo_t TYPE('b)) \<and>
      ptr_val q = p + of_nat (field_offset_untyped t path))"
  using root_ptr_valid_u_ptr_valid_u_cases[OF root_valid_p valid_q[unfolded ptr_valid_def]]
  by (simp add: size_of_def)

lemma root_ptr_valid_ptr_valid_cases:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes root_valid_p: "root_ptr_valid d p"
  assumes valid_q: "ptr_valid d q"
  shows "ptr_span p \<inter> ptr_span q = {} \<or>
    (\<exists>path. addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b)) \<and>
       q = PTR ('b) &(p\<rightarrow>path))"
  using root_ptr_valid_u_ptr_valid_cases[OF
      root_valid_p[unfolded root_ptr_valid_root_ptr_valid_u_conv] valid_q]
  by (simp add: size_of_def field_lvalue_def ptr_val_conv field_offset_def)

lemma stack_allocs_ptr_valid_cases1:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type  ptr"
  assumes alloc: "(p, d') \<in> stack_allocs n \<S> TYPE('a) d"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes valid_q: "ptr_valid d' q"
  shows "((\<exists>i path. i < n \<and>
            addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b)) \<and>
            q = PTR ('b) &((p +\<^sub>p int i)\<rightarrow>path)) \<and> \<not> ptr_valid d q) \<or>
         (ptr_valid d q \<and> {ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {})"
proof -
  from valid_q
  obtain root path x where
    path: "addressable_field root path (typ_uinfo_t TYPE('b))" and
    root_ptr_valid_u: "root_ptr_valid_u root d' x" and
    q: "ptr_val q = x + word_of_nat (field_offset_untyped root path)"
    by (clarsimp simp add: ptr_valid_def elim!: ptr_valid_u.cases)
  from path q_not_stack_byte have root_not_stack_byte: "root \<noteq> typ_uinfo_t TYPE(stack_byte)"
    using addressable_field_sub_typ sub_typ_stack_byte_u by blast

  from stack_allocs_root_ptr_valid_u_cases [OF alloc root_not_stack_byte] root_ptr_valid_u
  consider i where "i<n" "x = ptr_val (p +\<^sub>p int i)" "root = typ_uinfo_t TYPE('a)"
    | "root_ptr_valid_u root d x" by auto
  then show ?thesis
  proof cases
    case 1

    have "ptr_span q \<subseteq> ptr_span (p +\<^sub>p int i)"
      using ptr_span_subset_of_addressable_field[OF path q] by (simp add: size_of_def 1)
    also have "\<dots> \<subseteq> {ptr_val p..+n * size_of TYPE('a)}"
      using alloc 1(1) by (rule stack_allocs_contained)
    finally have "ptr_val q \<in> {ptr_val p..+n * size_of TYPE('a)}"
      using mem_type_self by auto
    then have root_q: "root_ptr_valid d (PTR_COERCE('b \<rightarrow> stack_byte) q)"
      using stack_allocs_cases[OF alloc] by (auto simp add: q 1 simp flip: Ptr_ptr_coerce)
    have False if q': "ptr_valid d q"
      using root_ptr_valid_ptr_valid_cases[OF root_q q'] q_not_stack_byte
      by (auto simp add: intvl_Suc_0 dest!: addressable_field_sub_typ sub_typ_stack_byte_u)
    then have "\<not> ptr_valid d q" by auto
    with 1 path show ?thesis
      by (auto simp: ptr_val_conv q field_lvalue_def field_offset_def
               intro!: exI[of _ i] exI[of _ path])
  next
    case 2
    then have "ptr_valid d q"
      by (auto simp add: ptr_valid_def q intro!: ptr_valid_u.intros path)
    with stack_allocs_disjoint [OF alloc q_not_stack_byte ptr_valid_h_t_valid, of q]
    show ?thesis by simp
  qed
qed

lemma stack_allocs_ptr_valid_cases1' [consumes 3, case_names addressable_field disjoint]:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type  ptr"
  assumes alloc: "(p, d') \<in> stack_allocs n \<S> TYPE('a) d"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes valid_q: "ptr_valid d' q"
  assumes addressable_field: "\<And>i path. i < n \<Longrightarrow>
            addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b)) \<Longrightarrow>
            q = PTR ('b) &((p +\<^sub>p int i)\<rightarrow>path) \<Longrightarrow> \<not> ptr_valid d q \<Longrightarrow>  P"
  assumes disjoint: "ptr_valid d q \<Longrightarrow> {ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {} \<Longrightarrow> P"
  shows "P"
  using stack_allocs_ptr_valid_cases1 [OF alloc q_not_stack_byte valid_q] addressable_field disjoint by blast

lemma stack_allocs_ptr_valid_cases2:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type  ptr"
  assumes alloc: "(p, d') \<in> stack_allocs n \<S> TYPE('a) d"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes valid_q: "ptr_valid d q"
  shows "ptr_valid d' q"
proof -
  from valid_q
  obtain root path x where
    path: "addressable_field root path (typ_uinfo_t TYPE('b))" and
    root_ptr_valid_u: "root_ptr_valid_u root d x" and
    x: "ptr_val q = x + word_of_nat (field_offset_untyped root path)"
    by (clarsimp simp add: ptr_valid_def ptr_valid_u.simps)

  from path q_not_stack_byte have root_not_stack_byte: "root \<noteq> typ_uinfo_t TYPE(stack_byte)"
    using addressable_field_sub_typ sub_typ_stack_byte_u by blast

  from stack_allocs_root_ptr_valid_u_other [OF alloc root_ptr_valid_u root_not_stack_byte]
  have "root_ptr_valid_u root d' x" .
  with path x
  show "ptr_valid d' q"
    using ptr_valid_def ptr_valid_u.simps by blast
qed

lemma stack_allocs_ptr_valid_cases3:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes alloc: "(p, d') \<in> stack_allocs n \<S> TYPE('a) d"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes i: "i < n"
  assumes path: "addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b))"
  assumes q: "q = PTR ('b) &((p +\<^sub>p int i)\<rightarrow>path)"
  shows "ptr_valid d' q"
  apply (simp add: q ptr_valid_def field_lvalue_def field_offset_def)
  apply (intro ptr_valid_u.intros[OF _ path])
  apply (subst stack_allocs_root_ptr_valid_u_cases[OF alloc stack_allocs_no_stack_byte[OF alloc]])
  apply (auto intro: i)
  done

theorem stack_allocs_ptr_valid_cases:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes alloc: "(p, d') \<in> stack_allocs n \<S> TYPE('a) d"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows "ptr_valid d' q \<longleftrightarrow>
    (((\<exists>i path. i < n \<and> addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b)) \<and>
            q = PTR ('b) &((p +\<^sub>p int i)\<rightarrow>path)) \<and> \<not> ptr_valid d q) \<or>
     (ptr_valid d q \<and> {ptr_val p ..+ n * size_of TYPE('a)} \<inter> ptr_span q = {}))"
  using stack_allocs_ptr_valid_cases1 [OF alloc q_not_stack_byte]
    stack_allocs_ptr_valid_cases2 [OF alloc q_not_stack_byte]
    stack_allocs_ptr_valid_cases3 [OF alloc q_not_stack_byte]
  by blast

lemma stack_releases_ptr_valid_cases1:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type  ptr"
  assumes p_not_stack_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes valid_q: "ptr_valid (stack_releases n p d) q"
  shows "{ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> ptr_span q = {} \<and>
         ptr_valid d q"
proof -
  from valid_q
  obtain root path x where
    path: "addressable_field root path (typ_uinfo_t TYPE('b))" and
    root_ptr_valid_u: "root_ptr_valid_u root (stack_releases n p d) x" and
    x: "ptr_val q = x + word_of_nat (field_offset_untyped root path)"
    by (clarsimp simp add: ptr_valid_def ptr_valid_u.simps)
  from path q_not_stack_byte have root_not_stack_byte: "root \<noteq> typ_uinfo_t TYPE(stack_byte)"
    using addressable_field_sub_typ sub_typ_stack_byte_u by blast

  from stack_releases_root_ptr_valid_u_cases [OF p_not_stack_byte root_not_stack_byte, of n p d x  ] root_ptr_valid_u
  obtain root_cases:
     "{ptr_val p..+n * size_of TYPE('a)} \<inter> {x..+size_td root} = {}"
     "root_ptr_valid_u root d x" by auto
  moreover
  have "ptr_span q \<subseteq> {x..+size_td root}"
    using path x by (rule ptr_span_subset_of_addressable_field)
  moreover
  from root_cases(2) path x have "ptr_valid d q"
    using ptr_valid_def ptr_valid_u.simps by blast
  ultimately
  show ?thesis by blast
qed

lemma stack_releases_ptr_valid_cases2:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type  ptr"
  assumes p_not_stack_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes root_p: "\<And>i. i < n \<Longrightarrow> root_ptr_valid d (p +\<^sub>p int i)"
  assumes disj: "{ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> ptr_span q = {}"
  assumes valid_q: "ptr_valid d q"
  shows "ptr_valid (stack_releases n p d) q"
proof -
  from valid_q
  obtain root path x where
    path: "addressable_field root path (typ_uinfo_t TYPE('b))" and
    root_ptr_valid_u: "root_ptr_valid_u root d x" and
    x: "ptr_val q = x + word_of_nat (field_offset_untyped root path)"
    by (clarsimp simp add: ptr_valid_def ptr_valid_u.simps)

  from path q_not_stack_byte have root_not_stack_byte: "root \<noteq> typ_uinfo_t TYPE(stack_byte)"
    using addressable_field_sub_typ sub_typ_stack_byte_u by blast

  have contained: "ptr_span q \<subseteq> {x..+size_td root}"
    using path x by (rule ptr_span_subset_of_addressable_field)

  have "{ptr_val p..+n * size_of TYPE('a)} \<inter> {x..+size_td root} = {}"
  proof (rule ccontr)
    assume "{ptr_val p..+n * size_of TYPE('a)} \<inter> {x..+size_td root} \<noteq> {}"
    then obtain i where i: "i < n" and overlap: "ptr_span (p +\<^sub>p int i) \<inter> {x..+size_td root} \<noteq> {}"
      by (meson array_to_index_span disjoint_iff)
    from root_p [OF i] have "root_ptr_valid_u (typ_uinfo_t TYPE('a)) d (ptr_val (p +\<^sub>p int i))"
      by (simp add: root_ptr_valid_root_ptr_valid_u_conv)
    from root_ptr_valid_u_cases [OF root_ptr_valid_u this] overlap
    obtain "root = typ_uinfo_t TYPE('a)" "x = ptr_val (p +\<^sub>p int i)"
      by (simp add: inf_commute size_of_tag)
    then have "ptr_span (p +\<^sub>p int i) = {x..+size_td root}"
      by (simp add: size_of_def)
    with contained have "ptr_span q \<subseteq> ptr_span (p +\<^sub>p int i)" by simp
    with disj i show False
      apply (simp add:  array_index_span_conv)
      by (smt (verit, ccfv_SIG) UN_I disjoint_iff mem_type_self ord_class.lessThan_iff subsetD)
  qed

  with stack_releases_root_ptr_valid_u_cases [OF p_not_stack_byte root_not_stack_byte] root_ptr_valid_u

  have "root_ptr_valid_u root (stack_releases n p d) x" by auto
  with path x
  show "ptr_valid (stack_releases n p d) q"
    using ptr_valid_def ptr_valid_u.simps by blast
qed


lemma stack_releases_ptr_valid_cases3:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type  ptr"
  assumes p_not_stack_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes root_p: "\<And>i. i < n \<Longrightarrow> root_ptr_valid d (p +\<^sub>p int i)"
  assumes valid_q: "ptr_valid d q"
  assumes invalid_q: "\<not> ptr_valid (stack_releases n p d) q"
  shows "\<exists>path i.
    addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b)) \<and> i < n \<and>
    q = PTR('b) &(p +\<^sub>p int i\<rightarrow>path)"
proof -
  from valid_q  invalid_q stack_releases_ptr_valid_cases2 [OF p_not_stack_byte q_not_stack_byte root_p _ valid_q, of n ]
  have "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q \<noteq> {} " by auto
  then obtain i where i_bound: "i < n" and overlap: "ptr_span (p +\<^sub>p int i) \<inter> ptr_span q \<noteq> {}"
    by (auto simp add: array_index_span_conv )

  from root_ptr_valid_ptr_valid_cases [OF root_p [OF i_bound] valid_q, simplified overlap, simplified] i_bound
  show ?thesis by blast
qed

lemma stack_releases_ptr_valid_cases:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'b::mem_type  ptr"
  assumes p_not_stack_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes root_p: "\<And>i. i < n \<Longrightarrow> root_ptr_valid d (p +\<^sub>p int i)"
shows "ptr_valid (stack_releases n p d) q \<longleftrightarrow>
       ptr_valid d q \<and> {ptr_val p ..+ n * size_of TYPE('a::mem_type)} \<inter> ptr_span q = {}"
  using stack_releases_ptr_valid_cases1 [OF p_not_stack_byte q_not_stack_byte]
    stack_releases_ptr_valid_cases2 [OF p_not_stack_byte q_not_stack_byte root_p] by blast

lemma ptr_valid_same_type_neq_no_overlap_conv:
  fixes p:: "'a::mem_type ptr"
  fixes q:: "'a::mem_type ptr"
  assumes valid_p: "ptr_valid d p"
  assumes valid_q: "ptr_valid d q"
  shows "p \<noteq> q \<longleftrightarrow> ptr_span p \<inter> ptr_span q = {}"
  using cvalid_same_type_neq_disjoint assms ptr_valid_h_t_valid
  by blast

theorem stack_allocs_the_default_plift [stack_the_default_plift]:
  fixes p:: "'a::xmem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes alloc: "(p, d') \<in> stack_allocs n \<S> TYPE('a) (hrs_htd h)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows "the_default c_type_class.zero
            (plift (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) (hrs_htd_update (\<lambda>_. d') h)) q) =
         the_default c_type_class.zero (plift h q)"
proof (cases "ptr_valid d' q")
  case True
  from alloc q_not_stack_byte True
  show ?thesis
  proof (cases rule: stack_allocs_ptr_valid_cases1')
    case (addressable_field i path)
    from addressable_field obtain
      i: "i < n" and
      path: "addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b))" and
      q: "q = PTR('b) &(p +\<^sub>p int i\<rightarrow>path)" and
      invalid: "\<not> ptr_valid (hrs_htd h) q"
      by blast
    from invalid have "(plift h q) = None"
      by (simp add: plift_None)
    moreover
    from stack_allocs_cases [OF alloc]
    obtain bound: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card" and not_null: "ptr_val p \<noteq> 0"
      by (metis Ptr_ptr_val c_guard_NULL_simp)

    from path obtain m where
      "field_lookup (typ_uinfo_t TYPE('a)) path 0 = Some ((typ_uinfo_t TYPE('b)), m)"
      by (auto dest: addressable_fieldD_field_lookup)

    then obtain t where fl: "field_lookup (typ_info_t TYPE('a)) path 0 = Some (t, m)" and
      match: "export_uinfo t = typ_uinfo_t TYPE('b)"
      using field_lookup_uinfo_Some_rev by blast
    from fl have field_ti: "field_ti TYPE('a) path  = Some t"
      using field_lookup_field_ti by blast
    from field_lookup_zero [OF fl match] have from_bytes_zero: "from_bytes (access_ti\<^sub>0 t c_type_class.zero) = (c_type_class.zero::'b)" .
    note h_val_field =  h_val_field_from_bytes' [OF field_ti match [simplified typ_uinfo_t_def]]
    from h_val_fold  [OF bound not_null i]
    have h_val_zero:
      "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]  (hrs_mem h)) (p +\<^sub>p int i) = c_type_class.zero" .
    have path_zero:
      "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n] (hrs_mem h)) (PTR('b) &(p +\<^sub>p int i\<rightarrow>path)) = c_type_class.zero"
      by (simp add: h_val_field h_val_zero from_bytes_zero)

    from True i path q
    have "(plift (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) (hrs_htd_update (\<lambda>_. d') h)) q) = Some c_type_class.zero"
      apply -
      apply (subst ptr_valid_plift_Some_hval)
       apply (simp add: hrs_htd_update)
      apply (simp add: path_zero hrs_mem_update)
      done
    ultimately
    show ?thesis by simp
  next
    case disjoint
    then obtain valid_q: "ptr_valid (hrs_htd h) q" and
        disj: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}" by blast

    from valid_q have "(plift h q) = Some (h_val (hrs_mem h) q)"
      by (simp add: ptr_valid_plift_Some_hval valid_q)
    moreover
    have h_val_eq:
      "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n] (hrs_mem h)) q =
        h_val (hrs_mem h) q" by (simp add: h_val_fold_zero_disjoint [OF disj])
    from True have valid_q':
      "ptr_valid (hrs_htd ((hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n])
                      (hrs_htd_update (\<lambda>_. d') h)))) q"
      by (simp add: hrs_htd_update)
    have "plift (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n])
            (hrs_htd_update (\<lambda>_. d') h)) q = Some (h_val (hrs_mem h) q)"
      using True by (simp add: ptr_valid_plift_Some_hval [OF valid_q'] hrs_mem_update h_val_eq)
    ultimately
    show ?thesis
      by simp
  qed
next
  case False
  from  False
  have invalid: "\<not> ptr_valid (hrs_htd h) q"
    using alloc q_not_stack_byte stack_allocs_ptr_valid_cases2 by blast
  then
  have "plift (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) (hrs_htd_update (\<lambda>_. d') h)) q = None"
    using plift_None
    by (metis (no_types, lifting) False hrs_htd_mem_update hrs_htd_update)
  moreover
  have "(plift h q) = None"
    using invalid by (simp add: plift_None)
  ultimately show ?thesis by simp
qed

theorem stack_releases_the_default_plift [stack_the_default_plift]:
  fixes p:: "'a::xmem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes roots: "\<And>i. i < n \<Longrightarrow> root_ptr_valid (hrs_htd h) (p +\<^sub>p int i)"
  assumes p_not_stack_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows "the_default c_type_class.zero
            (plift
                (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) h)
              q) =
         the_default c_type_class.zero (plift (hrs_htd_update (stack_releases n p) h) q)"
proof (cases "ptr_valid (stack_releases n p (hrs_htd h)) q")
  case True
  from  stack_releases_ptr_valid_cases1 [OF p_not_stack_byte q_not_stack_byte True]
  obtain disjoint: "{ptr_val p..+n * size_of TYPE('a)} \<inter> ptr_span q = {}" and
    valid_q: "ptr_valid (hrs_htd h) q" by blast

  from True valid_q have "plift (hrs_htd_update (stack_releases n p) h) q = Some (h_val (hrs_mem h) q)"
    using ptr_valid_plift_Some_hval
    by (metis hrs_htd_update hrs_mem_htd_update)

  moreover
  from h_val_fold_zero_disjoint [OF disjoint]
  have "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n] (hrs_mem h)) q = h_val (hrs_mem h) q" .
  with valid_q
  have "(plift (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) h) q) = Some (h_val (hrs_mem h) q)"
    by (simp add: hrs_mem_update ptr_valid_plift_Some_hval)
  ultimately show ?thesis by simp
next
  case False
  from False
  have eq1: "plift (hrs_htd_update (stack_releases n p) h) q = None"
    by (simp add: plift_None hrs_htd_update)
  show ?thesis
  proof (cases "ptr_valid (hrs_htd h) q")
    case True
    show ?thesis
    proof (cases n)
      case 0
      then show ?thesis
        using False True by (auto simp add: stack_releases_def)
    next
      case (Suc n')

      from roots [of 0] Suc
      have not_null: "ptr_val p \<noteq> 0"
        by (metis CTypesDefs.ptr_add_def Ptr_ptr_val Zero_not_Suc add.right_neutral
            bot_nat_0.not_eq_extremum mem_type_self mult_zero_left of_int_0 root_ptr_valid_range_not_NULL roots semiring_1_class.of_nat_0)

      from roots Suc
      have bound: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card"
        by (metis array_to_index_span len_of_addr_card root_ptr_valid_range_not_NULL zero_not_in_intvl_no_overflow)

      from stack_releases_ptr_valid_cases3  [OF p_not_stack_byte q_not_stack_byte roots True False]
      obtain path i where
        path: "addressable_field (typ_uinfo_t TYPE('a)) path (typ_uinfo_t TYPE('b))" and
        q: "q = PTR('b) &(p +\<^sub>p int i\<rightarrow>path)" and
        i_bound: "i < n"
        by blast
      from path obtain m where
        "field_lookup (typ_uinfo_t TYPE('a)) path 0 = Some ((typ_uinfo_t TYPE('b)), m)"
        by (auto dest: addressable_fieldD_field_lookup)

      then obtain t where fl: "field_lookup (typ_info_t TYPE('a)) path 0 = Some (t, m)" and
        match: "export_uinfo t = typ_uinfo_t TYPE('b)"
        using field_lookup_uinfo_Some_rev by blast
      from fl have field_ti: "field_ti TYPE('a) path  = Some t"
        using field_lookup_field_ti by blast
      from field_lookup_zero [OF fl match] have from_bytes_zero: "from_bytes (access_ti\<^sub>0 t c_type_class.zero) = (c_type_class.zero::'b)" .
      note h_val_field =  h_val_field_from_bytes' [OF field_ti match [simplified typ_uinfo_t_def]]
      from h_val_fold  [OF bound not_null i_bound]
      have h_val_zero:
        "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]  (hrs_mem h)) (p +\<^sub>p int i) = c_type_class.zero" .
      have path_zero:
        "h_val (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n] (hrs_mem h)) (PTR('b) &(p +\<^sub>p int i\<rightarrow>path)) = c_type_class.zero"
        by (simp add: h_val_field h_val_zero from_bytes_zero)
      from True i_bound path q
      have "plift (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) h) q = Some c_type_class.zero"
        apply -
        apply (subst ptr_valid_plift_Some_hval)
         apply (simp add: hrs_htd_update)
        apply (simp add: path_zero hrs_mem_update)
        done
      then show ?thesis by (simp add: eq1)
    qed
  next
    case False
    from False
    have "plift (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) h) q = None"
      using plift_None
      by (metis False hrs_htd_mem_update )
    with eq1 show ?thesis by simp
  qed
qed

lemma h_val_heap_update_padding_heap_update_conv:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"
  assumes valid_p: "ptr_valid d p"
  assumes valid_q: "ptr_valid d q"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows "h_val ((heap_update_padding p v bs h)) q = h_val (heap_update p v h) q"
  using ptr_valid_cases_weak[OF valid_p valid_q]
proof (elim disjE exE conjE)
  assume "disjnt (ptr_span p) (ptr_span q)" then show ?thesis
    by (simp add: h_val_heap_update_padding_disjoint h_val_update_regions_disjoint lbs disjnt_def)
next
  fix f assume f: "addressable_field (typ_uinfo_t TYPE('a)) f (typ_uinfo_t TYPE('b))"
    and q: "q = PTR('b) &(p\<rightarrow>f)"
  from addressable_fieldD_field_ti[OF f]
  obtain t where t: "field_ti TYPE('a) f = Some t" "export_uinfo t = typ_uinfo_t TYPE('b)"
    by auto

  let ?s = "from_bytes o access_ti\<^sub>0 t :: 'a \<Rightarrow> 'b"
  interpret f: nested_field' t f ?s "update_ti t o to_bytes_p"
    using t by unfold_locales simp_all

  show ?thesis unfolding q using lbs
    by (subst (1 2) f.h_val_field) (simp add: h_val_heap_update_padding)
next
  fix f assume f: "addressable_field (typ_uinfo_t TYPE('b)) f (typ_uinfo_t TYPE('a))"
    and p: "p = PTR('a) &(q\<rightarrow>f)"
  from addressable_fieldD_field_ti[OF f]
  obtain t where t: "field_ti TYPE('b) f = Some t" "export_uinfo t = typ_uinfo_t TYPE('a)"
    by auto

  let ?s = "from_bytes o access_ti\<^sub>0 t :: 'b \<Rightarrow> 'a"
  interpret f: nested_field' t f ?s "update_ti t o to_bytes_p"
    using t by unfold_locales simp_all

  note q = ptr_valid_h_t_valid[OF valid_q]
  show ?thesis unfolding p
    apply (subst f.h_val_field_lvalue_update_padding[OF q q lbs])
    apply (subst f.h_val_field_lvalue_update[OF q q])
    apply simp
    done
qed

lemma plift_heap_update_padding_heap_update_conv:
  fixes p::"'a::mem_type ptr"
  fixes q::"'b::mem_type ptr"
  assumes valid_p: "ptr_valid (hrs_htd h) p"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows "plift (hrs_mem_update (heap_update_padding p v bs) h) q = plift (hrs_mem_update (heap_update p v) h) q"
  using h_val_heap_update_padding_heap_update_conv
  by (metis hrs_htd_mem_update hrs_mem_update lbs valid_p wf_ptr_valid.plift_None
      wf_ptr_valid.ptr_valid_plift_Some_hval wf_ptr_valid_axioms)

theorem plift_heap_update_padding_heap_update_pointless_conv [plift_heap_update_padding_heap_update_conv]:
  fixes p::"'a::mem_type ptr"
  assumes valid_p: "ptr_valid (hrs_htd h) p"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows "plift (hrs_mem_update (heap_update_padding p v bs) h) = plift (hrs_mem_update (heap_update p v) h)"
  apply (rule ext)
  using plift_heap_update_padding_heap_update_conv assms
  by blast

lemma ptr_valid_stack_byte_disjoint:
  fixes q::"'a::{mem_type, stack_type} ptr"
  fixes p::"stack_byte ptr"
  assumes "root_ptr_valid h p"
  assumes "ptr_valid h q"
  shows "ptr_span p \<inter> ptr_span q = {}"
  using assms local.ptr_valid_h_t_valid no_stack_byte root_ptr_valid_not_subtype_disjoint sub_typ_stack_byte
    by blast

lemma h_val_heap_update_list_stack_byte:
  fixes q::"'a::{mem_type, stack_type} ptr"
  assumes valid_p: "root_ptr_valid d (p::stack_byte ptr)"
  assumes valid_q: "ptr_valid d q"
  assumes lbs: "length bs = size_of TYPE(stack_byte)"
  shows "h_val (heap_update_list (ptr_val p) bs h) q = h_val h q"
  using ptr_valid_stack_byte_disjoint [OF valid_p valid_q] lbs
  by (simp add: h_val_def heap_list_update_disjoint_same)


lemma h_val_heap_update_list_stack_byte':
  fixes q::"'a::{mem_type, stack_type} ptr"
  fixes p::"stack_byte ptr"
  assumes valid_p: "\<And>i. i < length bs \<Longrightarrow> root_ptr_valid d (p +\<^sub>p int i)"
  assumes valid_q: "ptr_valid d q"
  shows "h_val (heap_update_list (ptr_val p) bs h) q = h_val h q"
  using valid_p
proof (induct bs arbitrary: p h)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  from Cons.prems Cons.prems [of 0] obtain
    valid_bs: "\<And>i. i < Suc (length bs) \<Longrightarrow> root_ptr_valid d (p +\<^sub>p int i)" and
    valid_p: "root_ptr_valid d p" by auto
  from valid_bs have valid_bs': "\<And>i. i < length bs \<Longrightarrow> root_ptr_valid d ((p +\<^sub>p 1) +\<^sub>p int i)"
    apply (clarsimp simp add: ptr_add_def)
    by (metis Ex_less_Suc group_cancel.add1 less_trans_Suc of_nat_Suc)

  have "length [b] = size_of TYPE(stack_byte)" by auto
  note b_eq = h_val_heap_update_list_stack_byte [OF valid_p valid_q this]
  have val_eq: "ptr_val (p +\<^sub>p 1) = ptr_val p + 1"
    by (auto simp add: ptr_add_def)

  note hyp = Cons.hyps [OF valid_bs', simplified val_eq]
  show ?case
    apply (simp add: hyp)
    using b_eq
    apply (auto simp add: fun_upd_def)
    done
qed

lemma plift_heap_update_list_stack_byte:
  fixes q::"'a::{mem_type, stack_type} ptr"
  fixes p::"stack_byte ptr"
  assumes valid_p: "\<And>i. i < length bs \<Longrightarrow> root_ptr_valid (hrs_htd h) (p +\<^sub>p int i)"
  shows "plift (hrs_mem_update (heap_update_list (ptr_val p) bs) h) q = plift h q"
  using h_val_heap_update_list_stack_byte'
  by (metis hrs_htd_mem_update hrs_mem_update valid_p wf_ptr_valid.plift_None
      wf_ptr_valid.ptr_valid_plift_Some_hval wf_ptr_valid_axioms)

lemma plift_heap_update_list_stack_byte_pointless[plift_heap_update_list_stack_byte]:
  fixes p::"stack_byte ptr"
  assumes valid_p: "\<And>i. i < length bs \<Longrightarrow> root_ptr_valid (hrs_htd h) (p +\<^sub>p int i)"
  shows "plift (hrs_mem_update (heap_update_list (ptr_val p) bs) h) =
    (plift h::'a::{mem_type, stack_type} ptr \<Rightarrow> 'a option)"
  using assms plift_heap_update_list_stack_byte by blast

lemma plift_eq_plift:
  "hrs_htd h = hrs_htd h' \<Longrightarrow>
    (\<And>p::'a ptr. ptr_valid (hrs_htd h') p \<Longrightarrow>
      h_val (hrs_mem h) p = h_val (hrs_mem h') p) \<Longrightarrow>
    (plift h::'a::mem_type ptr \<Rightarrow> 'a option) = plift h'"
  apply (rule ext)
  apply (cases h; cases h')
  apply (simp add: plift_def lift_t_if h_t_valid_def root_ptr_valid_def hrs_htd_def
                   hrs_mem_def)
  done

definition addressable_fields :: "'a::mem_type itself \<Rightarrow> (field_name list \<times> 'a xtyp_info) list" where
  "addressable_fields TYPE('a) = (case map_of \<T> (typ_uinfo_t TYPE('a)) of
        None \<Rightarrow> []
      | Some fs \<Rightarrow> map (\<lambda>f. (f, the (field_ti TYPE('a) f))) fs)"

abbreviation merge_addressable_fields :: "'a::mem_type \<Rightarrow> 'a \<Rightarrow> 'a" where
  "merge_addressable_fields \<equiv> merge_ti_list (map snd (addressable_fields TYPE('a)))"

definition read_dedicated_heap :: "heap_raw_state \<Rightarrow> 'a::mem_type typ_heap_g" where
  "read_dedicated_heap h p = merge_addressable_fields ZERO('a) (the_default ZERO('a) (plift h p))"

definition write_dedicated_heap :: "'a::mem_type ptr \<Rightarrow> 'a \<Rightarrow> heap_raw_state \<Rightarrow> heap_raw_state" where
  "write_dedicated_heap p v = hrs_mem_update (heap_upd p (\<lambda>old. merge_addressable_fields old v))"

lemma mem_addressable_fields:
  assumes F: "map_of \<T> (typ_uinfo_t TYPE('a::mem_type)) = Some F"
  shows "f \<in> set F \<Longrightarrow> field_ti TYPE('a) f = Some u \<Longrightarrow> (f, u) \<in> set (addressable_fields TYPE('a))"
  using wf_\<T>[of "typ_uinfo_t TYPE('a)"]
  by (force simp add: addressable_fields_def F image_iff list_all_iff field_ti_def)

lemma mem_snd_addressable_fields:
  assumes F: "map_of \<T> (typ_uinfo_t TYPE('a::mem_type)) = Some F" "f \<in> set F"
    "field_ti TYPE('a) f = Some u"
  shows "u \<in> snd ` set (addressable_fields TYPE('a))"
  using mem_addressable_fields[OF assms] by (force simp: image_iff)

lemma list_all_field_ti_addressable_fields:
  "list_all (\<lambda>(f, u). field_ti TYPE('a) f = Some u) (addressable_fields TYPE('a::mem_type))"
  apply (clarsimp simp add: addressable_fields_def split: option.splits)
  subgoal premises prems
    using prems[THEN wf_\<T>]
    unfolding list.pred_map
    by (rule list.pred_mono_strong)
       (auto simp: list_all_iff field_ti_def typ_uinfo_t_def
             dest!: field_lookup_export_uinfo_Some_rev field_lookup_field_ti')
  done

lemma distinct_disj_fn_addressable_fields:
  "distinct_prop disj_fn (map fst (addressable_fields TYPE('a::mem_type)))"
  using wf_\<T>'
  by (auto simp: list_all_iff addressable_fields_def comp_def dest!: map_of_SomeD split: option.splits)

lemma list_all_field_ti_snd_addressable_fields:
  "list_all (\<lambda>u. \<exists>f. field_ti TYPE('a) f = Some u) (map snd (addressable_fields TYPE('a::mem_type)))"
  unfolding list.pred_map
  using list_all_field_ti_addressable_fields
  by (rule list.pred_mono_strong) auto

sublocale merge_addressable_fields: is_scene "merge_addressable_fields :: 'a::xmem_type \<Rightarrow> 'a \<Rightarrow> 'a"
  using list_all_field_ti_snd_addressable_fields by (rule is_scene_merge_ti_list)

lemma ptr_valid_u_cases_same_type:
  assumes t: "mem_type_u t" and a: "ptr_valid_u t d a" and b: "ptr_valid_u t d b"
  shows "a = b \<or> disjnt {a..+size_td t} {b..+size_td t}"
  using ptr_valid_u_cases_weak[OF t a b] by auto

lemma read_dedicated_heap_heap_update_list_stack_byte_pointless[simp]:
  fixes p::"stack_byte ptr"
  assumes valid_p: "\<And>i. i < length bs \<Longrightarrow> root_ptr_valid (hrs_htd h) (p +\<^sub>p int i)"
  shows "read_dedicated_heap (hrs_mem_update (heap_update_list (ptr_val p) bs) h) =
    (read_dedicated_heap h::'a::{mem_type, stack_type} ptr \<Rightarrow> 'a)"
  unfolding read_dedicated_heap_def
  by (simp add: plift_heap_update_list_stack_byte_pointless[OF valid_p])

lemma read_dedicated_heap_write_dedicated_heap_ne[simp]:
  fixes p :: "'a::xmem_type ptr" and q :: "'b::xmem_type ptr"
  assumes ne: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  assumes p: "ptr_valid (hrs_htd h) p"
  shows "read_dedicated_heap (write_dedicated_heap p x h) q = read_dedicated_heap h q"
proof cases
  let ?A = "typ_uinfo_t TYPE('a)" and ?B = "typ_uinfo_t TYPE('b)"
  assume q: "ptr_valid (hrs_htd h) q"
  from ptr_valid_cases_weak[OF p q]
  show ?thesis
  proof (elim disjE exE conjE)
    assume "disjnt (ptr_span p) (ptr_span q)" with p q show ?thesis
      by (simp add: read_dedicated_heap_def write_dedicated_heap_def disjnt_def
                    hrs_mem_update_heap_upd plift_disjoint_region)
  next
    fix f' assume f'_n: "addressable_field ?A f' ?B" and q_eq: "q = PTR('b) &(p\<rightarrow>f')"

    obtain F f1 f2 u where f'_eq: "f' = f1 @ f2"
      and F: "f1 \<in> set F" "map_of \<T> ?A = Some F"
      and f_u: "field_ti TYPE('a) f1 = Some u"
      and "addressable_field (export_uinfo u) f2 ?B"
      using f'_n ne by (cases rule: addressable_field.cases) (auto simp: field_ti_def dest!: field_lookup_uinfo_Some_rev)

    obtain v n where v: "export_uinfo v = ?B"
      and f_fs: "field_lookup (typ_info_t TYPE('a)) (f1 @ f2) 0 = Some (v, n)"
      using addressable_fieldD_field_lookup[OF f'_n] unfolding f'_eq
      by (auto dest: field_lookup_uinfo_Some_rev)
    obtain m where u_v: "field_lookup u f2 0 = Some (v, m)"
      using f_fs f_u
      apply (subst (asm) field_lookup_append_eq)
      apply (auto simp add: f_u field_ti_def split: option.splits
          dest: CTypes.field_lookup_offset2)
      done
    have p': "hrs_htd h \<Turnstile>\<^sub>t p"
      using p by (rule ptr_valid_h_t_valid)

    have u_mem: "u \<in> snd ` set (addressable_fields TYPE('a))"
      using F(2,1) f_u(1) by (rule mem_snd_addressable_fields)
    have f1u_mem: "(f1, u) \<in> set (addressable_fields TYPE('a))"
      using F(2,1) f_u(1) by (rule mem_addressable_fields)
    have sz: "size_of TYPE('b) = size_td v"
      using v unfolding export_uinfo_size[symmetric] by (simp add: size_of_def)

    have "length bs = size_of TYPE('b) \<Longrightarrow>
      access_ti v (merge_addressable_fields y x) bs = access_ti v y bs" for y bs
      by (intro access_ti_merge_ti_list[OF list_all_field_ti_addressable_fields
                     distinct_disj_fn_addressable_fields f1u_mem u_v])
         (simp add: sz)
    then show ?thesis using q unfolding f'_eq q_eq
      apply (simp add: read_dedicated_heap_def write_dedicated_heap_def ptr_valid_plift_Some_hval
                       hrs_mem_update)
      apply (simp add: heap_upd_def
                  ptr_valid_heap_update_subtype_field_access_ti_indep[OF p' p' f_fs v])
      done
  next
    fix f' n assume f'_n: "addressable_field ?B f' ?A" and p_eq: "p = PTR('a) &(q \<rightarrow> f')"
    from f'_n ne obtain F f0 f1 t0 n where *: "map_of \<T> ?B = Some F" "f0 \<in> set F" "f' = f0 @ f1"
      and f0: "field_lookup ?B f0 0 = Some (t0, n)" and f1: "addressable_field t0 f1 ?A"
      by cases auto
    from addressable_fieldD_field_ti[OF f'_n]
    obtain tA where f'_u: "field_ti TYPE('b) f' = Some tA" and tA: "export_uinfo tA = ?A"
      by auto
    have [simp]: "size_td tA = size_of TYPE('a)"
      unfolding export_uinfo_size[symmetric] tA by (simp add: size_of_def)

    from f0[unfolded typ_uinfo_t_def, THEN field_lookup_export_uinfo_Some_rev]
    obtain t0' where f0_t0': "field_ti TYPE('b) f0 = Some t0'" and t0: "t0 = export_uinfo t0'"
      by (auto simp: field_ti_def typ_uinfo_t_def
                  split: option.splits)

    obtain tA' n where t0'_f1: "field_lookup t0' f1 0 = Some (tA', n)"
      using addressable_fieldD_field_lookup'[OF f1, unfolded t0,
          THEN field_lookup_export_uinfo_Some_rev]
      by auto

    with field_ti_append_field_lookup[OF f0_t0' t0'_f1] f'_u
    have f0'_f1: "field_lookup t0' f1 0 = Some (tA, n)"
      by (simp add: *)

    note q' = ptr_valid.ptr_valid_h_t_valid[OF q]

    have f0t'_mem: "(f0, t0') \<in> set (addressable_fields TYPE('b))"
      using *(1,2) f0_t0' by (rule mem_addressable_fields)

    from q f'_n merge_ti_list_update_ti[OF
        list_all_field_ti_addressable_fields f0t'_mem distinct_disj_fn_addressable_fields]
        merge_ti_list_update_ti[OF
          list_all_field_ti_addressable_fields f0t'_mem distinct_disj_fn_addressable_fields f0'_f1]
    show ?thesis unfolding p_eq
      by (simp add: read_dedicated_heap_def write_dedicated_heap_def hrs_mem_update heap_upd_def
                       ptr_valid_plift_Some_hval h_val_field_update[OF f'_u tA q' q']
                       update_ti_t_def)
  qed
qed (simp add: read_dedicated_heap_def write_dedicated_heap_def plift_None)

lemma read_dedicated_heap_write_dedicated_heap[simp]:
  "ptr_valid (hrs_htd h) (p::'a::xmem_type ptr) \<Longrightarrow>
    read_dedicated_heap (write_dedicated_heap p x h) =
    upd_fun p (\<lambda>old. merge_addressable_fields old x) (read_dedicated_heap h)"
  by (simp add: fun_eq_iff the_plift_hval_fun_upd_eqI read_dedicated_heap_def[abs_def] upd_fun_def
                write_dedicated_heap_def hrs_mem_update_heap_upd fun_upd_def)

lemma hrs_mem_update_heap_update:
  fixes p :: "'a::xmem_type ptr"
  shows "hrs_mem_update (heap_update p x) h =
    fold (\<lambda>(f, u). hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti u x)))
      (addressable_fields TYPE('a))
      (write_dedicated_heap p x h)"
proof -
  show ?thesis
    apply (subst heap_update_eq_fold_subfields[OF list_all_field_ti_addressable_fields,
        where y="h_val (hrs_mem h) p"])
    unfolding hrs_mem_update_comp'[symmetric] write_dedicated_heap_def hrs_mem_update_heap_upd
    apply (subst fold_functor[of hrs_mem_update])
    apply (simp add: hrs_mem_update_def)
    apply (simp add: hrs_mem_update_def fun_eq_iff)
    apply (simp add: split_beta')
    done
qed

lemma hrs_mem_update_heap_update':
  fixes p :: "'a::xmem_type ptr"
  shows "hrs_mem_update (heap_update p x) =
    fold (\<lambda>(f, u). hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti u x)))
      (addressable_fields TYPE('a)) \<circ>
    write_dedicated_heap p x"
  apply (rule ext)
  unfolding comp_apply
  apply (rule hrs_mem_update_heap_update)
  done

lemma hrs_htd_write_dedicated_heap[simp]:
  "hrs_htd (write_dedicated_heap p x h) = hrs_htd h"
  by (simp add: write_dedicated_heap_def)

lemma partial_pointer_lense_merge_addressable_fields:
  fixes r :: "'h \<Rightarrow> 'a::xmem_type ptr \<Rightarrow> 'a"
  assumes "lense r w"
  shows
    "partial_pointer_lense (\<lambda>x y. merge_addressable_fields y x)
      (\<lambda>h p x . merge_addressable_fields x (r h p)) (\<lambda>p x. w (upd_fun p (\<lambda>old. merge_addressable_fields old x)))"
proof -
  interpret lense r w by fact
  show ?thesis
    apply unfold_locales
    apply (simp_all add: upd_fun.upd_same upd_same)
    subgoal by (simp add: comp_def)
    subgoal for p q x y h
      by (simp add: upd_fun_commute disj_ptr_span_ptr_neq disjnt_def Int_commute)
    done
qed

lemma pointer_lense_of_partials_cover:
  fixes rs :: "('h \<Rightarrow> 'a::xmem_type ptr \<Rightarrow> 'a \<Rightarrow> 'a) list"
  assumes g_u: "lense g u"
  assumes *:
    "length ms = length rs" "length ms = length ws"
    "list_all (\<lambda>(m, r, w). partial_pointer_lense m r w) (zip ms (zip rs ws))"
    and **:
    "\<And>a b c. distinct_prop (\<lambda>m1 m2. m1 a (m2 b c) = m2 b (m1 a c)) ms"
    "\<And>p a q b h. distinct_prop (\<lambda>w1 w2. p = q \<or> disjnt (ptr_span p) (ptr_span q) \<longrightarrow>
      w1 p a (w2 q b h) = w2 q b (w1 p a h)) ((\<lambda>p x. u (upd_fun p (\<lambda>old. merge_addressable_fields old x))) # ws)"
  assumes ms_cover: "\<And>a b. fold (\<lambda>m. m a) ms b = merge_addressable_fields a b"
  assumes R: "\<And>h p. R h p = fold (\<lambda>r. r h p) rs (g h p)"
  assumes W: "\<And>p f h. W p f h =
    fold (\<lambda>w. w p (f (R h p))) ws (u (upd_fun p (\<lambda>old. merge_addressable_fields old (f (R h p)))) h)"
  shows "pointer_lense R W"
  apply (rule pointer_lense_of_partials[where
    ms="(\<lambda>a b. merge_addressable_fields b a) # ms" and
    rs = "(\<lambda>h p x. merge_addressable_fields x (g h p)) # rs" and
    ws = "(\<lambda>p x. u (upd_fun p (\<lambda>old. merge_addressable_fields old x)))#ws"])
  subgoal by (simp add: *(1))
  subgoal by (simp add: *(2))
  subgoal
    apply (rule list_all_zip_zip_cons)
    apply (rule partial_pointer_lense_merge_addressable_fields[OF g_u])
    apply (rule *)
    done
  subgoal for a b c
  proof -
    have scenes_ms: "list_all is_scene ms"
      using * by (simp add: list_all_length partial_pointer_lense_def)
    have dis_ms: "distinct_prop disjnt_scene ms"
      using **(1) by (simp add: disjnt_scene_def[abs_def] distinct_prop_distrib_all)
    have comm_ms: "pairwise comm_scene (set ms)"
      apply (rule pairwise_set_of_distinct_prop)
      apply (simp add: comm_scene_comm)
      apply (use dis_ms in \<open>auto simp: distinct_prop_iff_nth\<close>)
      done
    have ms_y: "list_all (\<lambda>m. disjnt_scene m y \<or> m = y) ms" if y: "y \<in> set ms" for y
      using in_set_conv_decomp[THEN iffD1, OF y] dis_ms
      by (auto simp: distinct_prop_append list_all_iff disjnt_scene_comm)

    show ?thesis
      apply (simp add: **)
      apply (simp flip: ms_cover)
      apply (intro ballI)
      apply (rule fold_disjnt_scene[OF scenes_ms comm_ms ms_y])
      apply auto
      done
  qed
  subgoal by (rule **)
  subgoal by (simp add: ms_cover)
  subgoal for h p
  proof -
    interpret fold: partial_pointer_lense
      "\<lambda>a. fold (\<lambda>m. m a) ms" "\<lambda>h p. fold (\<lambda>r. r h p) rs" "\<lambda>p x. fold (\<lambda>w. w p x) ws"
      apply (rule partial_pointer_lense_fold[OF *])
      subgoal using **(1) by auto
      subgoal using **(2) by auto
      done
    show "R h p = fold (\<lambda>r. r h p) ((\<lambda>h p x. merge_addressable_fields x (g h p)) # rs) x"
      using fold.r_m by (simp add: R flip: ms_cover)
  qed
  subgoal by (simp add: W)
  done

lemma cover_read_dedicated_heap[simp]:
  "merge_addressable_fields (read_dedicated_heap h p) = merge_addressable_fields ZERO('a::xmem_type)"
  by (simp add: fun_eq_iff read_dedicated_heap_def)

lemma read_dedicated_heap_fun_upd_cover_zero_eq_upd_fun[simp]:
  "((read_dedicated_heap h)(p := merge_addressable_fields ZERO('a::xmem_type) x)) q =
    upd_fun p (\<lambda>old. merge_addressable_fields old x) (read_dedicated_heap h) q"
  by (simp add: upd_fun_def fun_upd_def fun_eq_iff)

theorem stack_allocs_read_dedicated_heap [stack_the_default_plift]:
  fixes p:: "'a::xmem_type ptr"
  assumes alloc: "(p, d') \<in> stack_allocs n \<S> TYPE('a) (hrs_htd h)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b::xmem_type) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows "read_dedicated_heap (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) (hrs_htd_update (\<lambda>_. d') h)) =
    (read_dedicated_heap h :: 'b ptr \<Rightarrow> _)"
  apply (rule ext)
  unfolding read_dedicated_heap_def stack_allocs_the_default_plift[OF assms] ..

theorem stack_releases_read_dedicated_heap [stack_the_default_plift]:
  fixes p:: "'a::xmem_type ptr"
  assumes roots: "\<And>i. i < n \<Longrightarrow> root_ptr_valid (hrs_htd h) (p +\<^sub>p int i)"
  assumes p_not_stack_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes q_not_stack_byte: "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  shows "read_dedicated_heap (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) h) =
    (read_dedicated_heap (hrs_htd_update (stack_releases n p) h) :: 'b::xmem_type ptr \<Rightarrow> _)"
  unfolding read_dedicated_heap_def stack_releases_the_default_plift[OF assms, of n, simplified] ..

lemma ptr_valid_addressable_field_field_lvalue[addressable_field_exec]:
  fixes p::"'a::mem_type ptr"
  assumes "ptr_valid h p"
  assumes "addressable_field (typ_uinfo_t (TYPE('a))) fs (typ_uinfo_t (TYPE('b::mem_type)))"
  shows "ptr_valid h (PTR('b) (&(p\<rightarrow>fs)))"
  using assms
  by (metis field_lvalue_def field_offset_def local.fold_ptr_valid' 
      local.open_types_axioms local.ptr_valid_u_trans open_types.ptr_valid_def)

lemma addressable_field_exec[addressable_field_exec]:
  shows 
    "addressable_field t ps v =
      (case ps of
         [] => t = v
       |  _ \<Rightarrow> (\<exists>fs p. map_of \<T> t = Some fs \<and>
          List.find (\<lambda>p. \<exists>u n. field_lookup t p 0 = Some (u, n) \<and> p @ drop (length p) ps = ps \<and>
               addressable_field u (drop (length p) ps) v) fs = Some p))"
proof (cases ps)
  case Nil
  then show ?thesis by simp
next
  case (Cons f ps')
  show ?thesis
  proof (cases "map_of \<T> t")
    case None
    then show ?thesis 
      apply (simp add: Cons)
      by (metis list.simps(2) local.addressable_field.cases option.simps(3))
  next
    case (Some fs)
    show ?thesis
    proof (cases "\<exists>p. List.find (\<lambda>p. \<exists>u n. field_lookup t p 0 = Some (u, n) \<and> 
               p @ drop (length p) ps = ps \<and>
               addressable_field u (drop (length p) ps) v) fs = Some p")
      case True
      then obtain p where 
        find: "List.find (\<lambda>p. \<exists>u n. field_lookup t p 0 = Some (u, n) \<and> 
               p @ drop (length p) ps = ps \<and>
               addressable_field u (drop (length p) ps) v) fs = Some p"
        by auto
      then obtain u n where 
        p: "p \<in> set fs" and 
        ps: "p @ drop (length p) ps = ps" and
        u: "field_lookup t p 0 = Some (u, n)" and
        addr: "addressable_field u (drop (length p) ps) v"
        using findSomeD
        by (smt (verit, best))
      from addressable_field_step [OF Some p u addr]
      have addr': "addressable_field t (p @ drop (length p) ps) v" .
      from addressable_fieldD_field_lookup [OF addr] obtain m 
        where v: "field_lookup u (drop (length p) ps) 0 = Some (v, m)"
        by blast
      from addressable_fieldD_field_lookup [OF addr'] obtain k where
         "field_lookup t (p @ drop (length p) ps) 0 = Some (v, k)"
        by blast
      have ps_eq: "(p @ drop (length p) (f # ps')) = ps"
        using ps
        by (simp add: Cons ps)
      show ?thesis
        using find addr'
        by (simp add: Cons Some ps_eq)
    next
      case False 
      with Some show ?thesis 
        apply (simp add: Cons)
        apply (force simp add: find_None_iff elim: addressable_field.cases)
        done
    qed
  qed
qed

local_setup \<open>
let
  fun unfold_ss ctxt = ctxt addsimps
    Named_Theorems.get ctxt @{named_theorems "\<T>_def"} @
    @{thms
      list_ex_iff
      fun_upd_other
      field_lookup_typ_uinfo_t_Some
      fold_typ_uinfo_t
      exists_nat_numeral}
in
  Cached_Theory_Simproc.declare_init_thy_simpset @{named_theorems "\<T>_def"} unfold_ss
end
\<close>

simproc_setup \<T> (\<open>map_of \<T> (typ_uinfo_t TYPE('a::mem_type))\<close> | \<open>map fst \<T>\<close> | \<open>set \<T>\<close>) = \<open>
  let
    exception Abort;
    fun cache_simproc augment ctxt =
      let val umm_ctxt = Cached_Theory_Simproc.put_time_warp_simpset' @{named_theorems "\<T>_def"} ctxt
      in Cached_Theory_Simproc.gen_simproc (umm_ctxt, Cached_Theory_Simproc.recert, Cached_Theory_Simproc.add_cache) augment end
  in
    fn phi => fn ctxt => fn ct =>
      let
        val check =
          Match_Cterm.switch [
            (@{cterm_morph_match "map_of \<T> (typ_uinfo_t ?T)"} phi) #> (fn {T, ...} =>
                if UMM_Proofs.is_ctype (Thm.term_of T) then () else raise Abort)
          , fn _ => ()];
        val _ = check ct
        val _ = Utils.verbose_msg 3 ctxt (fn _ =>
               "\<T> invoked: " ^ Syntax.string_of_term ctxt (Thm.term_of ct))
      in
        cache_simproc (K single) ctxt ct
      end handle Match => NONE | Abort => NONE
  end
\<close>

end

lemma fold_field_lvalue:
  "x + word_of_nat (field_offset_untyped (typ_uinfo_t TYPE('a::c_type)) f) = &(PTR('a) x\<rightarrow>f)"
  by (simp add: field_lvalue_def field_offset_def)

lemma field_lvalue_same_root_ptr_conv:
  "&(p::'a:: c_type ptr\<rightarrow>f) = &(q::'a:: c_type ptr\<rightarrow>f) \<longleftrightarrow> p = q"
  by (auto simp add: field_lvalue_same_conv)

lemma ptr_exhaust_eq: fixes p::"'a::c_type ptr" shows "PTR('a) (ptr_val p) = p"
  by (cases p) simp

lemma fold_exists_ptr: "(\<exists>x. P (PTR('a::c_type) x)) \<longleftrightarrow> (\<exists>q. P q)"
  by (metis ptr.exhaust)

subsection \<open>Syntax \<open>PTR_VALID('a)\<close>\<close>

context open_types
begin
text \<open>We want to provide syntax that makes the type of \<^const>\<open>ptr_valid\<close> visible on the term level for
interpretations of the @{locale open_types}.
This is a bit tricky as Isabelle does not (yet) provide local syntax and local print / parse translations.
We implement it by a combination of theory level syntax and translations and a local
declarations for the interpretations.
\<close>
end
syntax
  "_ptr_valid" :: "type \<Rightarrow> logic" (\<open>(1PTR'_VALID/(1'(_')))\<close>)

ML \<open>
structure Ptr_Valid_Translation =
struct

val show_ptr_valid = Attrib.setup_config_bool @{binding show_ptr_valid} (K true)

val ptr_validN = @{const_name open_types.ptr_valid} |> Long_Name.base_name
val local_ptr_validN = Long_Name.qualify Long_Name.localN ptr_validN

type options = {ptr_valid:term, ptr_valid_name: string} option \<comment> \<open>
 NONE means we are within the (abstract) locale,
 SOME provides the relevant parameters from the global interpretations\<close>

fun ptr_valid_term NONE ctxt = Syntax.read_term ctxt local_ptr_validN
  | ptr_valid_term (SOME {ptr_valid, ...}) _ = ptr_valid


fun instantiate_ptr_valid opt ctxt typ =
  let
    val \<^Const_>\<open>open_types.ptr_valid _ for T\<close> = ptr_valid_term opt ctxt
  in
    \<^Const>\<open>open_types.ptr_valid typ for T\<close>
  end

fun const_name check ctxt s =
  let
    val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} ctxt s
    val res = check (Proof_Context.consts_of ctxt, c)
        handle TYPE (msg, _, _) => error (msg ^ Position.here \<^here>);
  in
    res
  end

fun const_syntax (SOME {ptr_valid_name, ...}) ctxt =
      const_name (fn (_, c) => Lexicon.mark_const c) ctxt ptr_valid_name
  | const_syntax NONE ctxt =
      Lexicon.mark_const local_ptr_validN

fun gen_ptr_valid_tr' ptr_valid ctxt T ts = if Config.get ctxt show_ptr_valid then
  let
    val ptr_valid' as \<^Const_>\<open>open_types.ptr_valid typ for _\<close> =
             Syntax.read_term ctxt ptr_validN
    val [_, \<^Type>\<open>ptr typ\<close>] = T |> binder_types
    val head = Syntax.const \<^syntax_const>\<open>_ptr_valid\<close> $ Syntax_Phases.term_of_typ ctxt typ
  in
    Term.betapplys (head, ts)
  end
  handle Bind => raise Match
  else raise Match

fun add_ptr_valid_print_translation (opt:options) thy =
  let
    val ctxt = Proof_Context.init_global thy
    val const_syntax = const_syntax opt ctxt
    val ptr_valid = instantiate_ptr_valid opt
  in
    thy |> Sign.typed_print_translation [(const_syntax, gen_ptr_valid_tr' ptr_valid)]
  end
end\<close>

parse_translation \<open>
 let
   fun ptr_valid_tr ctxt [t] =
     let
       val \<^Const_>\<open>open_types.ptr_valid _ for T \<close> =
             Syntax.read_term ctxt Ptr_Valid_Translation.ptr_validN
       val typ = Syntax_Phases.decode_typ t
     in
       \<^Const>\<open>open_types.ptr_valid typ\<close> $ T
     end
     handle Bind => error ("PTR_VALID: no instance of ptr_valid in context ")
 in
   [(\<^syntax_const>\<open>_ptr_valid\<close>, ptr_valid_tr)]
 end\<close>

setup \<open>Ptr_Valid_Translation.add_ptr_valid_print_translation NONE\<close>
text \<open>This theory level setup actually provides the local syntax when working within
a locale like @{locale open_types}. The \<open>print_translation\<close> is
triggered on constant (abbreviation) \<open>local.ptr_valid\<close>\<close>

context open_types
begin
term "PTR_VALID(32 word)" \<comment> \<open>Works in both directions by theory level setup above.\<close>
declaration \<open>fn phi => fn context =>
  let
    val ptr_valid = Morphism.term phi \<^term>\<open>ptr_valid\<close>
    val ptr_valid_name = Morphism.binding phi (Binding.make (Ptr_Valid_Translation.ptr_validN, \<^here>))
      |> Binding.name_of
    val opt = SOME {ptr_valid = ptr_valid, ptr_valid_name = ptr_valid_name}
  in
    context |> Context.mapping (Ptr_Valid_Translation.add_ptr_valid_print_translation opt) I
  end\<close>
text \<open>This declaration provides the setup for global interpretations. The print translation
is triggered on constant (abbreviation) \<open><instance-name>.ptr_valid\<close> introduced by the
iterpretation.
Keep in mind, that when printing a term on the internal @{term "open_types.ptr_valid \<T>"} first
the notations / abbreviatons are applied. These introduce the syntactic constant \<^term>\<open>ptr_valid\<close>
on which the translation then triggers.
\<close>
end

subsection \<open>Syntax \<open>IS_VALID('a)\<close>\<close>

context open_types
begin
text \<open>Building on top of \<open>PTR_VALID\<close> we provide syntax that also takes the \<open>heap_typing\<close> of
lifted globals into accound: \<open>IS_VALID(32 word) s p\<close> is translated to \<^term>\<open>ptr_valid (heap_typing s) p\<close>
Note that \<^term>\<open>heap_typing\<close> is a field of the lifted globals record that is defined later.
\<close>

end

syntax
  "_is_valid" :: "type \<Rightarrow> logic \<Rightarrow> logic" (\<open>(1IS'_VALID/(1'(_'))) _\<close> [0, 1000] 1000)

parse_translation \<open>
let
  fun is_valid_tr ctxt [t, s] =
    let
      val \<^Const_>\<open>open_types.ptr_valid _ for T \<close>  =
             Syntax.read_term ctxt Ptr_Valid_Translation.ptr_validN
      val typ = Syntax_Phases.decode_typ t
    in ( \<^Const>\<open>open_types.ptr_valid typ\<close> $ T) $ ((Const (AC_Names.heap_typingN, dummyT)) $ s) end
    handle Bind => error ("IS_VALID: no instance of ptr_valid in context ")
in
  [(\<^syntax_const>\<open>_is_valid\<close>, is_valid_tr)]
end
\<close>

print_translation \<open>
let
  val show_is_valid = Attrib.setup_config_bool @{binding show_is_valid} (K true)
  fun is_valid_tr' ctxt (typ::Const (marked_heap_typing_name, heap_typingT)$s::ts) =
    if Config.get ctxt show_is_valid then
      let
        val heap_typing_name = \<^try>\<open>Lexicon.unmark_const marked_heap_typing_name
                                catch _ => raise Match\<close>
        val _ = if Long_Name.base_name heap_typing_name = AC_Names.heap_typingN then () else raise Match
      in
        Term.betapplys (Syntax.const \<^syntax_const>\<open>_is_valid\<close> $ typ $ s, ts)
      end
    else raise Match
in
  [(\<^syntax_const>\<open>_ptr_valid\<close>, is_valid_tr')]
end
\<close>

end
