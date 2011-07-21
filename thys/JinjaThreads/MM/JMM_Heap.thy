(*  Title:      JinjaThreads/MM/JMM_Heap.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{ Locales for heap operations with set of allocated addresses} *}

theory JMM_Heap imports
  JMM_Spec
  "../Common/WellForm"
  "SC_Completion"
begin


definition mrw_addrs :: "(('addr \<times> addr_loc) \<rightharpoonup> ('addr val \<times> bool)) \<Rightarrow> 'addr set"
where "mrw_addrs vs = {a. Addr a \<in> fst ` ran vs}"

lemma mrw_addrs_empty [simp]: "mrw_addrs empty = {}"
by(simp add: mrw_addrs_def)

locale allocated_heap_base = heap_base +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  fixes allocated :: "'heap \<Rightarrow> 'addr set"

locale allocated_heap = 
  allocated_heap_base +
  heap +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'m prog"

  assumes allocated_empty: "allocated empty_heap = {}"
  and new_obj_allocatedD:
  "new_obj h C = (h', Some a) \<Longrightarrow> allocated h' = insert a (allocated h) \<and> a \<notin> allocated h"
  and new_obj_allocated_fail:
  "new_obj h C = (h', None) \<Longrightarrow> allocated h' = allocated h"
  and new_arr_allocatedD:
  "new_arr h T n = (h', Some a) \<Longrightarrow> allocated h' = insert a (allocated h) \<and> a \<notin> allocated h"
  and new_arr_allocated_fail:
  "new_arr h T n = (h', None) \<Longrightarrow> allocated h' = allocated h"
  and heap_write_allocated_same:
  "heap_write h a al v h' \<Longrightarrow> allocated h' = allocated h"
begin

lemma new_obj_allocated_mono: "new_obj h C = (h', ao) \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(cases ao)(simp_all add: new_obj_allocated_fail new_obj_allocatedD)

lemma new_arr_allocated_mono: "new_arr h T n = (h', ao) \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(cases ao)(simp_all add: new_arr_allocated_fail new_arr_allocatedD)

lemma new_obj_allocated_mono': "allocated h \<subseteq> allocated (fst (new_obj h C))"
  and new_arr_allocated_mono': "allocated h \<subseteq> allocated (fst (new_arr h T n))"
apply(cases "new_obj h C", simp add: new_obj_allocated_mono)
apply(cases "new_arr h T n", simp add: new_arr_allocated_mono)
done

lemma
  shows start_addrs_allocated: "allocated start_heap = set start_addrs"
  and distinct_start_addrs': "distinct start_addrs"
proof -
  { fix h ads b and xs :: "cname list"
    let "?start_addrs h ads b xs" = "fst (snd (foldl create_initial_object (h, ads, b) xs))"
    let "?start_heap h ads b xs" = "fst (foldl create_initial_object (h, ads, b) xs)"
    assume "allocated h = set ads"
    hence "allocated (?start_heap h ads b xs) = set (?start_addrs h ads b xs) \<and>
           (distinct ads \<longrightarrow> distinct (?start_addrs h ads b xs))"
      (is "?concl xs h ads b")
    proof(induct xs arbitrary: h ads b)
      case Nil thus ?case by auto
    next
      case (Cons x xs)
      note ads = `allocated h = set ads`
      show ?case
      proof(cases b)
        case False thus ?thesis using ads
          by(simp add: create_initial_object_simps zip_append1)
      next
        case True[simp]
        obtain h' ao where new_obj: "new_obj h x = (h', ao)" by(cases "new_obj h x")
        show ?thesis
        proof(cases ao)
          case None
          with new_obj have "allocated h' = allocated h" by(simp add: new_obj_allocated_fail)
          with ads None show ?thesis by(simp add: create_initial_object_simps new_obj)
        next
          case (Some a')
          with new_obj have "allocated h' = insert a' (allocated h)" "a' \<notin> allocated h"
            by(auto dest: new_obj_allocatedD)
          with ads have "allocated h' = set (ads @ [a'])" by auto
          hence "?concl xs h' (ads @ [a']) True" by(rule Cons)
          moreover have "a' \<notin> set ads" using `a' \<notin> allocated h` ads by blast
          ultimately show ?thesis by(simp add: create_initial_object_simps new_obj Some)
        qed
      qed
    qed }
  from this[of empty_heap "[]" True initialization_list]
  show "allocated start_heap = set start_addrs"
    and distinct_start_addrs: "distinct start_addrs"
    unfolding start_heap_def start_addrs_def start_heap_data_def
    by(auto simp add: allocated_empty)
qed

lemma mrw_addrs_start_heap_obs: "mrw_addrs (mrw_values P vs (map NormalAction start_heap_obs)) \<subseteq> mrw_addrs vs"
proof -
  { fix xs
    let ?NewObj = "NewObj :: 'addr \<Rightarrow> cname \<Rightarrow> ('addr, 'thread_id) obs_event"
    let "?start_heap_obs xs" = "map (\<lambda>(C, a). ?NewObj a C) xs"
    have "mrw_addrs (mrw_values P vs (map NormalAction (?start_heap_obs xs))) \<subseteq> mrw_addrs vs"
      (is "?concl xs")
    proof(induct xs arbitrary: vs)
      case Nil thus ?case by simp
    next
      case (Cons x xs)
      have "mrw_addrs (mrw_values P vs (map NormalAction (map (\<lambda>(C, a). ?NewObj a C) (x # xs))))
        = mrw_addrs (mrw_values P (mrw_value P vs (NormalAction (?NewObj (snd x) (fst x)))) (map NormalAction (map (\<lambda>(C, a). ?NewObj a C) xs)))"
        by(simp add: split_beta)
      also have "\<dots> \<subseteq> mrw_addrs (mrw_value P vs (NormalAction (?NewObj (snd x) (fst x))))" by(rule Cons)
      also have "\<dots> \<subseteq> mrw_addrs vs"
        by(auto 4 4 simp add: mrw_addrs_def ran_def default_val_not_Addr Addr_not_default_val intro: rev_image_eqI split del: option.split)
      finally show ?case .
    qed }
  thus ?thesis by(simp add: start_heap_obs_def)
qed

end

context heap_base begin

definition vs_conf :: "'m prog \<Rightarrow> 'heap \<Rightarrow> (('addr \<times> addr_loc) \<rightharpoonup> ('addr val \<times> bool)) \<Rightarrow> bool"
where "vs_conf P h vs \<longleftrightarrow> (\<forall>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<longrightarrow> (\<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T))"

lemma vs_confI:
  "(\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T) \<Longrightarrow> vs_conf P h vs"
unfolding vs_conf_def by blast

lemma vs_confD:
  "\<lbrakk> vs_conf P h vs; vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T"
unfolding vs_conf_def by blast

end

context heap begin

lemma vs_conf_hext: "\<lbrakk> vs_conf P h vs; h \<unlhd> h' \<rbrakk> \<Longrightarrow> vs_conf P h' vs"
by(blast intro!: vs_confI intro: conf_hext addr_loc_type_hext_mono dest: vs_confD)

lemma vs_conf_new_obj:
  "\<lbrakk> vs_conf P h vs; new_obj h C = (h', \<lfloor>a\<rfloor>) \<rbrakk> 
  \<Longrightarrow> vs_conf P h' (mrw_value P vs (NormalAction (NewObj a C)))"
apply(drule vs_conf_hext)
 apply(erule hext_new_obj)
apply(auto intro!: vs_confI split: split_if_asm)
apply(blast intro: addr_loc_type.intros is_class_type_of.intros defval_conf dest: new_obj_SomeD has_field_is_class vs_confD)+
done

lemma vs_conf_new_arr:
  "\<lbrakk> vs_conf P h vs; new_arr h T n = (h', \<lfloor>a\<rfloor>); is_type P (T\<lfloor>\<rceil>) \<rbrakk> 
  \<Longrightarrow> vs_conf P h' (mrw_value P vs (NormalAction (NewArr a T n)))"
apply(drule vs_conf_hext)
 apply(erule hext_new_arr)
apply(auto intro!: vs_confI split: split_if_asm simp del: is_type.simps)
apply(blast intro: addr_loc_type.intros defval_conf is_class_type_of.intros dest: new_arr_SomeD vs_confD)+
done

end

context heap_conf_base begin

definition heap_read_typeable :: "bool"
where "heap_read_typeable \<longleftrightarrow> (\<forall>h ad al v T. hconf h \<longrightarrow> P,h \<turnstile> ad@al : T \<longrightarrow> P,h \<turnstile> v :\<le> T \<longrightarrow> heap_read h ad al v)"

lemma heap_read_typeableI:
  "(\<And>h ad al v T. \<lbrakk> P,h \<turnstile> ad@al : T; P,h \<turnstile> v :\<le> T; hconf h \<rbrakk> \<Longrightarrow> heap_read h ad al v) \<Longrightarrow> heap_read_typeable"
unfolding heap_read_typeable_def by blast

lemma heap_read_typeableD:
  "\<lbrakk> heap_read_typeable; P,h \<turnstile> ad@al : T; P,h \<turnstile> v :\<le> T; hconf h \<rbrakk> \<Longrightarrow> heap_read h ad al v"
unfolding heap_read_typeable_def by blast

end

context heap_base begin

definition heap_read_typed :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
where "heap_read_typed P h ad al v \<longleftrightarrow> heap_read h ad al v \<and> (\<forall>T. P,h \<turnstile> ad@al : T \<longrightarrow> P,h \<turnstile> v :\<le> T)"

lemma heap_read_typedI:
  "\<lbrakk> heap_read h ad al v; \<And>T. P,h \<turnstile> ad@al : T \<Longrightarrow> P,h \<turnstile> v :\<le> T \<rbrakk> \<Longrightarrow> heap_read_typed P h ad al v"
unfolding heap_read_typed_def by blast

lemma heap_read_typed_into_heap_read:
  "heap_read_typed P h ad al v \<Longrightarrow> heap_read h ad al v"
unfolding heap_read_typed_def by blast

lemma heap_read_typed_typed:
  "\<lbrakk> heap_read_typed P h ad al v; P,h \<turnstile> ad@al : T \<rbrakk> \<Longrightarrow> P,h \<turnstile> v :\<le> T"
unfolding heap_read_typed_def by blast

end

context heap_conf begin

lemma heap_conf_read_heap_read_typed:
  "heap_conf_read addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write hconf P"
proof
  fix h a al v T
  assume "heap_read_typed P h a al v" "P,h \<turnstile> a@al : T" 
  thus "P,h \<turnstile> v :\<le> T" by(rule heap_read_typed_typed)
qed

end

context heap begin

lemma start_addrs_dom_mrw_values:
  assumes wf: "wf_syscls P"
  and a: "a \<in> set start_addrs"
  and adal: "P,start_heap \<turnstile> a@al : T"
  shows "(a, al) \<in> dom (mrw_values P empty (map NormalAction start_heap_obs))"
proof -
  from a obtain CTn where CTn: "NewHeapElem a CTn \<in> set start_heap_obs"
    unfolding in_set_start_addrs_conv_NewHeapElem ..
  then obtain obs obs' where obs: "start_heap_obs = obs @ NewHeapElem a CTn # obs'" by(auto dest: split_list)
  have "(a, al) \<in> dom (mrw_value P (mrw_values P empty (map NormalAction obs)) (NormalAction (NewHeapElem a CTn)))"
  proof(cases CTn)
    case (Class_type C)[simp]
    with wf CTn have "typeof_addr start_heap a = \<lfloor>Class C\<rfloor>" by(auto intro: NewObj_start_heap_obsD)
    with adal show ?thesis by cases(auto 4 4)
  next
    case (Array_type T n)[simp]
    with wf CTn have "typeof_addr start_heap a = \<lfloor>Array T\<rfloor>" "array_length start_heap a = n"
      by(auto dest: NewArr_start_heap_obsD)
    with adal show ?thesis by cases(frule has_field_decl_above, auto 4 3)
  qed
  also have "dom (mrw_value P (mrw_values P empty (map NormalAction obs)) (NormalAction (NewHeapElem a CTn :: ('addr, 'thread_id) obs_event))) 
    \<subseteq> dom (mrw_values P empty (map NormalAction start_heap_obs))"
    by(simp add: obs)(rule mrw_values_dom_mono)
  finally show ?thesis .
qed

end

end
