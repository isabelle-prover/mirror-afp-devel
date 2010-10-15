(*  Title:      JinjaThreads/Common/StartConfig.thy
    Author:     Andreas Lochbihler
*)

header {* 
  \isaheader{The initial configuration}
*}
theory StartConfig imports
  Exceptions
  Observable_Events
begin

definition initialization_list :: "cname list"
where
  "initialization_list = Thread # sys_xcpts_list"

context heap_base begin

definition create_initial_object :: "'heap \<times> addr list \<times> bool \<Rightarrow> cname \<Rightarrow> 'heap \<times> addr list \<times> bool"
where
  "create_initial_object = 
  (\<lambda>(h, ads, b) C. 
     if b 
     then let (h', a') = new_obj h C
          in case a' of None \<Rightarrow> (h', ads, False)
             | Some a'' \<Rightarrow> (h', ads @ [a''], True)
     else (h, ads, False))"

definition start_heap_data :: "'heap \<times> addr list \<times> bool"
where
  "start_heap_data = foldl create_initial_object (empty_heap, [], True) initialization_list"

definition start_heap :: 'heap
where "start_heap = fst start_heap_data"

definition start_heap_ok :: bool
where "start_heap_ok = snd (snd (start_heap_data))"

definition start_heap_obs :: "obs_event list"
where
  "start_heap_obs =
  map (\<lambda>(C, a). NewObj a C) (zip initialization_list (fst (snd start_heap_data)))"

definition start_addrs :: "addr list"
where "start_addrs = fst (snd start_heap_data)"

definition addr_of_sys_xcpt :: "cname \<Rightarrow> addr"
where "addr_of_sys_xcpt C = the (map_of (zip initialization_list start_addrs) C)"

definition start_tid :: addr
where "start_tid = addr_of_sys_xcpt Thread"

definition start_state :: "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm \<Rightarrow> val list \<Rightarrow> 'x) \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> (addr,thread_id,'x,'heap,addr) state"
where
  "start_state f P C M vs \<equiv>
   let (D, Ts, T, m) = method P C M
   in (\<lambda>\<^isup>f None, ([start_tid \<mapsto> (f D M Ts T m vs, no_wait_locks)], start_heap), empty)"

lemma create_initial_object_simps:
  "create_initial_object (h, ads, b) C = 
   (if b 
    then let (h', a') = new_obj h C
         in case a' of None \<Rightarrow> (h', ads, False)
            | Some a'' \<Rightarrow> (h', ads @ [a''], True)
    else (h, ads, False))"
unfolding create_initial_object_def by simp

lemma create_initial_object_False [simp]:
  "create_initial_object (h, ads, False) C = (h, ads, False)"
by(simp add: create_initial_object_simps)

lemma foldl_create_initial_object_False [simp]:
  "foldl create_initial_object (h, ads, False) Cs = (h, ads, False)"
by(induct Cs) simp_all

lemma NewHeapElem_start_heap_obs_start_addrsD:
  "NewHeapElem a CTn \<in> set start_heap_obs \<Longrightarrow> a \<in> set start_addrs"
unfolding start_heap_obs_def start_addrs_def
by(auto dest: set_zip_rightD)

lemma shr_start_state: "shr (start_state f P C M vs) = start_heap"
by(simp add: start_state_def split_beta)

lemma distinct_initialization_list:
  "distinct initialization_list"
by(simp add: initialization_list_def sys_xcpts_list_def sys_xcpts_neqs Thread_neq_sys_xcpts)

lemma start_heap_obs_not_Read: 
  "ReadMem ad al v \<notin> set start_heap_obs"
unfolding start_heap_obs_def by auto

lemma length_initialization_list_le_length_start_addrs:
  "length initialization_list \<ge> length start_addrs"
proof -
  { fix h ads xs
    have "length (fst (snd (foldl create_initial_object (h, ads, True) xs))) \<le> length ads + length xs"
    proof(induct xs arbitrary: h ads)
      case Nil thus ?case by simp
    next
      case (Cons x xs)
      from this[of "fst (new_obj h x)" "ads @ [the (snd (new_obj h x))]"]
      show ?case by(clarsimp simp add: create_initial_object_simps split_beta)
    qed }
  from this[of empty_heap "[]" initialization_list]
  show ?thesis unfolding start_heap_def start_addrs_def start_heap_data_def by simp
qed

lemma start_addrs_NewHeapElem_start_heap_obsD:
  "a \<in> set start_addrs \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set start_heap_obs"
using length_initialization_list_le_length_start_addrs
unfolding start_heap_obs_def start_addrs_def
by(force simp add: set_zip in_set_conv_nth intro: rev_image_eqI)

lemma in_set_start_addrs_conv_NewHeapElem:
  "a \<in> set start_addrs \<longleftrightarrow> (\<exists>CTn. NewHeapElem a CTn \<in> set start_heap_obs)"
by(blast dest: start_addrs_NewHeapElem_start_heap_obsD intro: NewHeapElem_start_heap_obs_start_addrsD)


subsection {* @{term preallocated} *}

definition preallocated :: "'heap \<Rightarrow> bool"
where "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class C\<rfloor>"

lemma typeof_addr_sys_xcp: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class C\<rfloor>"
by(simp add: preallocated_def)

lemma typeof_sys_xcp:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr (addr_of_sys_xcpt C)) = \<lfloor>Class C\<rfloor>"
by(simp add: typeof_addr_sys_xcp)

lemma [simp]:
  assumes "preallocated h"
  shows typeof_ClassCast: "typeof_addr h (addr_of_sys_xcpt ClassCast) = Some(Class ClassCast)"
  and typeof_OutOfMemory: "typeof_addr h (addr_of_sys_xcpt OutOfMemory) = Some(Class OutOfMemory)" 
  and typeof_NullPointer: "typeof_addr h (addr_of_sys_xcpt NullPointer) = Some(Class NullPointer)" 
  and typeof_ArrayIndexOutOfBounds: 
  "typeof_addr h (addr_of_sys_xcpt ArrayIndexOutOfBounds) = Some(Class ArrayIndexOutOfBounds)" 
  and typeof_ArrayStore: "typeof_addr h (addr_of_sys_xcpt ArrayStore) = Some(Class ArrayStore)" 
  and typeof_NegativeArraySize: "typeof_addr h (addr_of_sys_xcpt NegativeArraySize) = Some(Class NegativeArraySize)" 
  and typeof_IllegalMonitorState: "typeof_addr h (addr_of_sys_xcpt IllegalMonitorState) = Some(Class IllegalMonitorState)"
  and typeof_IllegalThreadState: "typeof_addr h (addr_of_sys_xcpt IllegalThreadState) = Some(Class IllegalThreadState)" 
  and typeof_CloneNotSupported: "typeof_addr h (addr_of_sys_xcpt CloneNotSupported) = Some(Class CloneNotSupported)" 
  and typeof_InterruptedException: "typeof_addr h (addr_of_sys_xcpt InterruptedException) = Some(Class InterruptedException)"
using assms
by(simp_all add: typeof_addr_sys_xcp)

lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
by(drule (1) typeof_addr_sys_xcp)(simp add: cname_of_def)

lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
by (simp add: preallocated_def hext_def)


end

context heap begin

lemma preallocated_heap_ops:
  assumes "preallocated h"
  shows preallocated_new_obj: "\<And>a. new_obj h C = (h', a) \<Longrightarrow> preallocated h'"
  and preallocated_new_arr: "\<And>a. new_arr h T n = (h', a) \<Longrightarrow> preallocated h'"
  and preallocated_write_field: "heap_write h a al v h' \<Longrightarrow> preallocated h'"
using preallocated_hext[OF assms, of h']
by(blast intro: hext_heap_ops)+

lemma preallocated_start_heap:
  "start_heap_ok \<Longrightarrow> preallocated start_heap"
unfolding start_heap_ok_def start_heap_data_def initialization_list_def sys_xcpts_list_def 
  preallocated_def start_heap_def start_addrs_def
apply(clarsimp split: prod.split_asm simp add: create_initial_object_simps)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(frule new_obj_SomeD, frule hext_new_obj, rotate_tac 1)
apply(clarsimp)
apply(erule sys_xcpts_cases)
apply(simp_all add: addr_of_sys_xcpt_def sys_xcpts_neqs Thread_neq_sys_xcpts initialization_list_def sys_xcpts_list_def start_heap_data_def start_addrs_def create_initial_object_simps)
apply(assumption|erule typeof_addr_hext_mono)+
done

lemma
  shows dom_typeof_addr_start_heap: "set start_addrs \<subseteq> dom (typeof_addr start_heap)"
  and distinct_start_addrs: "distinct start_addrs"
  and dom_typeof_addr_start_heap_eq_start_addrs:
  "heap_ops_typeof_minimal \<Longrightarrow> dom (typeof_addr start_heap) = set start_addrs"
proof -
  { fix h ads b xs
    assume "set ads \<subseteq> dom (typeof_addr h)"
    hence "set (fst (snd (foldl create_initial_object (h, ads, b) xs))) \<subseteq> dom (typeof_addr (fst (foldl create_initial_object (h, ads, b) xs))) \<and> 
           (distinct ads \<longrightarrow> distinct (fst (snd (foldl create_initial_object (h, ads, b) xs)))) \<and>
           (dom (typeof_addr h) \<subseteq> set ads \<longrightarrow> heap_ops_typeof_minimal \<longrightarrow> 
            dom (typeof_addr (fst (foldl create_initial_object (h, ads, b) xs))) \<subseteq> set (fst (snd (foldl create_initial_object (h, ads, b) xs))))"
      (is "?concl xs h ads b")
    proof(induct xs arbitrary: h ads b)
      case Nil thus ?case by simp
    next
      case (Cons x xs)
      note ads = `set ads \<subseteq> dom (typeof_addr h)`
      show ?case
      proof(cases b)
        case False thus ?thesis
          using ads by(simp add: create_initial_object_simps)
      next
        case True[simp]
        obtain h' ao where new_obj: "new_obj h x = (h', ao)" by(cases "new_obj h x")
        with ads have ads': "set ads \<subseteq> dom (typeof_addr h')"
          by(auto dest: typeof_addr_hext_mono[OF hext_new_obj])
        moreover {
          fix a
          assume ao: "ao = Some a"
          with new_obj ads' have "set (ads @ [a]) \<subseteq> dom (typeof_addr h')"
            by(auto dest: new_obj_SomeD)
          hence "?concl xs h' (ads @ [a]) True" by(rule Cons)
          moreover have "a \<notin> set ads" 
            using new_obj ads ao by(auto dest: new_obj_SomeD)
          moreover {
            assume "dom (typeof_addr h) \<subseteq> set ads" "heap_ops_typeof_minimal"
            with new_obj ao have "dom (typeof_addr h') \<subseteq> insert a (set ads)"
              by(auto dest: heap_ops_typeof_minimalD del: subsetI) }
          moreover note calculation }
        moreover {
          assume "ao = None" "heap_ops_typeof_minimal"
          hence "dom (typeof_addr h') = dom (typeof_addr h)"
            using new_obj by(auto dest: heap_ops_typeof_minimalD del: equalityI) }
        ultimately show ?thesis by(simp add: create_initial_object_simps new_obj)
      qed
    qed }
  from this[of "[]" empty_heap True initialization_list]
  show "set start_addrs \<subseteq> dom (typeof_addr start_heap)"
    and "distinct start_addrs"
    and "heap_ops_typeof_minimal \<Longrightarrow> dom (typeof_addr start_heap) = set start_addrs"
    unfolding start_heap_def start_addrs_def start_heap_data_def by auto
qed

lemma NewArr_start_heap_obsD:
  assumes "NewArr a T n \<in> set start_heap_obs"
  shows "typeof_addr start_heap a = \<lfloor>Array T\<rfloor>"
  and "array_length start_heap a = n"
using assms
unfolding start_heap_obs_def start_heap_def
by clarsimp+

lemma NewObj_start_heap_obsD:
  assumes "NewObj a C \<in> set start_heap_obs"
  shows "typeof_addr start_heap a = \<lfloor>Class C\<rfloor>"
proof -
  { fix h ads b xs Cs
    assume "(C, a) \<in> set (zip (Cs @ xs) (fst (snd (foldl create_initial_object (h, ads, b) xs))))"
      and "\<forall>(C, a) \<in> set (zip Cs ads). typeof_addr h a = \<lfloor>Class C\<rfloor>"
      and "length Cs = length ads"
    hence "typeof_addr (fst (foldl create_initial_object (h, ads, b) xs)) a = \<lfloor>Class C\<rfloor>"
    proof(induct xs arbitrary: h ads b Cs)
      case Nil thus ?case by auto
    next
      case (Cons x xs)
      note inv = `\<forall>(C, a) \<in> set (zip Cs ads). typeof_addr h a = \<lfloor>Class C\<rfloor>`
        and Ca = `(C, a) \<in> set (zip (Cs @ x # xs) (fst (snd (foldl create_initial_object (h, ads, b) (x # xs)))))`
        and len = `length Cs = length ads`
      show ?case
      proof(cases b)
        case False thus ?thesis
          using inv Ca len by(auto simp add: create_initial_object_simps zip_append1)
      next
        case True[simp]
        obtain h' ao where new_obj: "new_obj h x = (h', ao)" by(cases "new_obj h x")
        hence hext: "h \<unlhd> h'" by(rule hext_new_obj)
        { assume "ao = None"
          hence "typeof_addr h' a = \<lfloor>Class C\<rfloor>"
            using inv Ca new_obj len hext
            by(auto simp add: create_initial_object_simps zip_append1 dest: typeof_addr_hext_mono) }
        moreover
        { fix a'
          assume ao: "ao = Some a'"
          hence "(C, a) \<in> set (zip ((Cs @ [x]) @ xs) (fst (snd (foldl create_initial_object (h', ads @ [a'], True) xs))))"
            using Ca new_obj by(simp add: create_initial_object_simps)
          moreover have "\<forall>(C, a)\<in>set (zip (Cs @ [x]) (ads @ [a'])).  typeof_addr h' a = \<lfloor>Class C\<rfloor>"
          proof(clarify)
            fix C a
            assume "(C, a) \<in> set (zip (Cs @ [x]) (ads @ [a']))"
            thus "typeof_addr h' a = \<lfloor>Class C\<rfloor>"
              using inv len hext new_obj ao by(auto dest: new_obj_SomeD typeof_addr_hext_mono)
          qed
          moreover have "length (Cs @ [x]) = length (ads @ [a'])" using len by simp
          ultimately have "typeof_addr (fst (foldl create_initial_object (h', ads @ [a'], True) xs)) a = \<lfloor>Class C\<rfloor>"
            by(rule Cons) }
        ultimately show ?thesis using new_obj by(simp add: create_initial_object_simps)
      qed
    qed }
  from this[of "[]" initialization_list empty_heap "[]" True] assms
  show ?thesis by(auto simp add: start_heap_obs_def start_heap_data_def start_heap_def)
qed

end

subsection {* Code generation *}

lemmas [code] =
  heap_base.create_initial_object_def
  heap_base.start_heap_data_def
  heap_base.start_heap_def
  heap_base.start_heap_ok_def
  heap_base.start_heap_obs_def
  heap_base.start_addrs_def
  heap_base.addr_of_sys_xcpt_def
  heap_base.start_tid_def
  heap_base.start_state_def

end