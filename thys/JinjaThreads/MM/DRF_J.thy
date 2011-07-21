theory DRF_J imports
  "JMM_Common"
  "../J/ProgressThreaded"
begin

primrec ka :: "'addr expr \<Rightarrow> 'addr set"
  and kas :: "'addr expr list \<Rightarrow> 'addr set"
where 
  "ka (new C) = {}"
| "ka (newA T\<lfloor>e\<rceil>) = ka e"
| "ka (Cast T e) = ka e"
| "ka (e instanceof T) = ka e"
| "ka (Val v) = ka_Val v"
| "ka (Var V) = {}"
| "ka (e1 \<guillemotleft>bop\<guillemotright> e2) = ka e1 \<union> ka e2"
| "ka (V := e) = ka e"
| "ka (a\<lfloor>e\<rceil>) = ka a \<union> ka e"
| "ka (a\<lfloor>e\<rceil> := e') = ka a \<union> ka e \<union> ka e'"
| "ka (a\<bullet>length) = ka a"
| "ka (e\<bullet>F{D}) = ka e"
| "ka (e\<bullet>F{D} := e') = ka e \<union> ka e'"
| "ka (e\<bullet>M(es)) = ka e \<union> kas es"
| "ka {V:T=vo; e} = ka e \<union> (case vo of None \<Rightarrow> {} | Some v \<Rightarrow> ka_Val v)"
| "ka (Synchronized x e e') = ka e \<union> ka e'"
| "ka (InSynchronized x a e) = insert a (ka e)"
| "ka (e;; e') = ka e \<union> ka e'"
| "ka (if (e) e1 else e2) = ka e \<union> ka e1 \<union> ka e2"
| "ka (while (b) e) = ka b \<union> ka e"
| "ka (throw e) = ka e"
| "ka (try e catch(C V) e') = ka e \<union> ka e'"

| "kas [] = {}"
| "kas (e # es) = ka e \<union> kas es" 

definition ka_locals :: "'addr locals \<Rightarrow> 'addr set"
where "ka_locals xs = {a. Addr a \<in> ran xs}"

lemma ka_Val_subset_ka_locals:
  "xs V = \<lfloor>v\<rfloor> \<Longrightarrow> ka_Val v \<subseteq> ka_locals xs"
by(cases v)(auto simp add: ka_locals_def ran_def)

lemma ka_locals_update_subset: 
  "ka_locals (xs(V := None)) \<subseteq> ka_locals xs"
  "ka_locals (xs(V \<mapsto> v)) \<subseteq> ka_Val v \<union> ka_locals xs"
by(auto simp add: ka_locals_def ran_def)

lemma ka_locals_empty [simp]: "ka_locals empty = {}"
by(simp add: ka_locals_def)

lemma kas_append [simp]: "kas (es @ es') = kas es \<union> kas es'"
by(induct es) auto

lemma kas_map_Val [simp]: "kas (map Val vs) = (\<Union>ka_Val ` set vs)"
by(induct vs) auto

lemma ka_blocks:
  "\<lbrakk> length pns = length Ts; length vs = length Ts \<rbrakk> 
  \<Longrightarrow> ka (blocks pns Ts vs body) = (\<Union>ka_Val ` set vs) \<union> ka body"
by(induct pns Ts vs body rule: blocks.induct)(auto)

lemma WT_ka: "P,E \<turnstile> e :: T \<Longrightarrow> ka e = {}"
  and WTs_kas: "P,E \<turnstile> es [::] Ts \<Longrightarrow> kas es = {}"
by(induct rule: WT_WTs.inducts)(auto simp add: typeof_ka)

context J_heap_base begin

primrec J_known_addrs :: "'thread_id \<Rightarrow> 'addr expr \<times> 'addr locals \<Rightarrow> 'addr set"
where "J_known_addrs t (e, xs) = insert (thread_id2addr t) (ka e \<union> ka_locals xs \<union> set start_addrs)"

lemma assumes wf: "wf_J_prog P" 
  and ok: "start_heap_ok"
  shows red_known_addrs_mono:
  "P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> J_known_addrs t (e', lcl s') \<subseteq> J_known_addrs t (e, lcl s) \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and reds_known_addrs_mono:
  "P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> kas es' \<union> ka_locals (lcl s') \<subseteq> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s)) \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<union> set start_addrs"
proof(induct rule: red_reds.inducts)
  case RedVar thus ?case by(auto dest: ka_Val_subset_ka_locals)
next
  case RedLAss thus ?case by(auto simp add: ka_locals_def ran_def)
next
  case RedBinOp thus ?case by(auto dest: binop_known_addrs[OF ok])
next
  case RedBinOpFail thus ?case by(auto dest: binop_known_addrs[OF ok])
next
  case RedCall thus ?case
    by(auto simp add: ka_blocks new_obs_addrs_def wf_mdecl_def dest!: sees_wf_mdecl[OF wf] WT_ka)
next
  case (RedCallExternal s a T M vs ta va h') thus ?case
    by(cases va)(auto dest!: red_external_known_addrs_mono[OF ok])
next
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    apply(cases "l V")
    apply(auto simp del: fun_upd_apply del: subsetI)
    apply(blast dest: ka_Val_subset_ka_locals)+
    done
qed(simp_all add: new_obs_addrs_def addr_of_sys_xcpt_start_addr[OF ok] subset_Un1 subset_Un2 subset_insert ka_Val_subset_new_obs_Addr_ReadMem ka_blocks del: fun_upd_apply, blast+)

lemma red_known_addrs_ReadMem:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> \<Longrightarrow> ad \<in> J_known_addrs t (e, lcl s)"
  and reds_known_addrss_ReadMem:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s)) \<union> set start_addrs"
proof(induct rule: red_reds.inducts)
  case RedCallExternal thus ?case by simp (blast dest: red_external_known_addrs_ReadMem)
next
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    by(auto simp del: fun_upd_apply)
qed(simp_all, blast+)

lemma red_known_addrs_WriteMem:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a \<in> J_known_addrs t (e, lcl s) \<or> a \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and reds_known_addrss_WriteMem:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a \<in> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s)) \<union> set start_addrs \<union> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
proof(induct rule: red_reds.inducts)
  case RedCallExternal thus ?case by simp (blast dest: red_external_known_addrs_WriteMem)
next
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    by(auto simp del: fun_upd_apply)
qed(simp_all, blast+)

end

context J_heap begin

lemma
  assumes wf: "wf_J_prog P" 
  and ok: "start_heap_ok"
  shows red_known_addrs_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t' x' h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> J_known_addrs t' x' \<subseteq> J_known_addrs t (e, lcl s)"
  and reds_known_addrss_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t' x' h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> J_known_addrs t' x' \<subseteq> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s) \<union> set start_addrs)"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h') thus ?case
    apply clarsimp
    apply(frule (1) red_external_new_thread_sub_thread)
    apply(frule (1) red_external_NewThread_idD)
    apply clarsimp
    
    apply(drule (1) addr2thread_id_inverse)
    apply simp
    apply(drule sub_Thread_sees_run[OF wf])
    apply clarsimp
    apply(auto 4 4 dest: sees_wf_mdecl[OF wf] WT_ka simp add: wf_mdecl_def)
    done
next
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    by(cases "l V")(auto simp del: fun_upd_apply)
qed(simp_all, blast+)

lemma red_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
  and reds_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(induct rule: red_reds.inducts)
apply(auto dest: red_external_New_same_addr_same)
done

end

locale J_allocated_heap = allocated_heap +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'addr J_prog"

sublocale J_allocated_heap < J_heap
by(unfold_locales)

context J_allocated_heap begin

lemma red_allocated_mono: "P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> allocated (hp s) \<subseteq> allocated (hp s')"
  and reds_allocated_mono: "P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> allocated (hp s) \<subseteq> allocated (hp s')"
by(induct rule: red_reds.inducts)(auto dest: new_obj_allocatedD new_obj_allocated_fail new_arr_allocatedD new_arr_allocated_fail heap_write_allocated_same red_external_allocated_mono del: subsetI)

lemma red_allocatedD:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> \<Longrightarrow> ad \<in> allocated (hp s') \<and> ad \<notin> allocated (hp s)"
  and reds_allocatedD:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> \<Longrightarrow> ad \<in> allocated (hp s') \<and> ad \<notin> allocated (hp s)"
by(induct rule: red_reds.inducts)(auto dest: new_obj_allocatedD new_obj_allocated_fail new_arr_allocatedD new_arr_allocated_fail heap_write_allocated_same red_external_allocatedD)

lemma red_allocated_NewHeapElemD:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; ad \<in> allocated (hp s'); ad \<notin> allocated (hp s) \<rbrakk> \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and reds_allocated_NewHeapElemD:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; ad \<in> allocated (hp s'); ad \<notin> allocated (hp s) \<rbrakk> \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(induct rule: red_reds.inducts)(auto dest: new_obj_allocatedD new_obj_allocated_fail new_arr_allocatedD new_arr_allocated_fail heap_write_allocated_same red_external_NewHeapElemD)

lemma mred_allocated_multithreaded:
  "allocated_multithreaded addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length heap_write allocated final_expr (mred P) P"
proof
  fix t x m ta x' m'
  assume "mred P t (x, m) ta (x', m')"
  thus "allocated m \<subseteq> allocated m'"
    by(auto dest: red_allocated_mono del: subsetI simp add: split_beta)
next
  fix x t m ta x' m' ad CTn
  assume "mred P t (x, m) ta (x', m')"
    and "NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> allocated m' \<and> ad \<notin> allocated m"
    by(auto dest: red_allocatedD simp add: split_beta)
next
  fix t x m ta x' m' ad
  assume "mred P t (x, m) ta (x', m')"
    and "ad \<in> allocated m'" "ad \<notin> allocated m"
  thus "\<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    by(auto dest: red_allocated_NewHeapElemD simp add: split_beta)
next
  fix t x m ta x' m' i a CTn j CTn'
  assume "mred P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a CTn" "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a CTn'" "j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "i = j" by(auto dest: red_New_same_addr_same simp add: split_beta)
qed

end

sublocale J_allocated_heap < red_mthr!: allocated_multithreaded 
  addr2thread_id thread_id2addr 
  empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write allocated 
  final_expr "mred P" 
  P
by(rule mred_allocated_multithreaded)

context J_allocated_heap begin

lemma mred_known_addrs: 
  assumes wf: "wf_J_prog P"
  and ok: "start_heap_ok"
  shows "known_addrs addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length heap_write allocated J_known_addrs final_expr (mred P) P"
proof
  fix t x m ta x' m'
  assume "mred P t (x, m) ta (x', m')"
  thus "J_known_addrs t x' \<subseteq> J_known_addrs t x \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    by(auto del: subsetI simp add: split_beta dest: red_known_addrs_mono[OF wf ok])
next
  fix t x m ta x' m' t' x'' m''
  assume "mred P t (x, m) ta (x', m')"
    and "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  thus "J_known_addrs t' x'' \<subseteq> J_known_addrs t x"
    by(auto del: subsetI simp add: split_beta dest: red_known_addrs_new_thread[OF wf ok])
next
  fix t x m ta x' m' ad al v
  assume "mred P t (x, m) ta (x', m')"
    and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> J_known_addrs t x"
    by(auto simp add: split_beta dest: red_known_addrs_ReadMem)
next
  fix t x m ta x' m' n ad al ad'
  assume "mred P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr ad')" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad' \<in> J_known_addrs t x \<or> ad' \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    by(auto simp add: split_beta dest: red_known_addrs_WriteMem)
next
  fix t x m ta x' m'
  assume "mred P t (x, m) ta (x', m')"
  thus "m \<unlhd> m'" by(auto dest: red_hext_incr simp add: split_beta)
qed

end








context J_heap begin

lemma red_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
  and reds_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedAAcc thus ?case
    by(fastsimp intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def)
next
  case RedFAcc thus ?case
    by(fastsimp intro: addr_loc_type.intros dest: typeof_addr_eq_Some_conv)
next
  case RedCallExternal thus ?case
    by(auto intro: red_external_read_mem_typeable)
qed auto

end

primrec new_types :: "('a, 'b, 'addr) exp \<Rightarrow> ty set"
  and new_typess :: "('a, 'b, 'addr) exp list \<Rightarrow> ty set"
where 
  "new_types (new C) = {Class C}"
| "new_types (newA T\<lfloor>e\<rceil>) = insert (T\<lfloor>\<rceil>) (new_types e)"
| "new_types (Cast T e) = new_types e"
| "new_types (e instanceof T) = new_types e"
| "new_types (Val v) = {}"
| "new_types (Var V) = {}"
| "new_types (e1 \<guillemotleft>bop\<guillemotright> e2) = new_types e1 \<union> new_types e2"
| "new_types (V := e) = new_types e"
| "new_types (a\<lfloor>e\<rceil>) = new_types a \<union> new_types e"
| "new_types (a\<lfloor>e\<rceil> := e') = new_types a \<union> new_types e \<union> new_types e'"
| "new_types (a\<bullet>length) = new_types a"
| "new_types (e\<bullet>F{D}) = new_types e"
| "new_types (e\<bullet>F{D} := e') = new_types e \<union> new_types e'"
| "new_types (e\<bullet>M(es)) = new_types e \<union> new_typess es"
| "new_types {V:T=vo; e} = new_types e"
| "new_types (Synchronized x e e') = new_types e \<union> new_types e'"
| "new_types (InSynchronized x a e) = new_types e"
| "new_types (e;; e') = new_types e \<union> new_types e'"
| "new_types (if (e) e1 else e2) = new_types e \<union> new_types e1 \<union> new_types e2"
| "new_types (while (b) e) = new_types b \<union> new_types e"
| "new_types (throw e) = new_types e"
| "new_types (try e catch(C V) e') = new_types e \<union> new_types e'"

| "new_typess [] = {}"
| "new_typess (e # es) = new_types e \<union> new_typess es"

lemma new_types_blocks:
  "\<lbrakk> length pns = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow> new_types (blocks pns vs Ts e) = new_types e"
apply(induct rule: blocks.induct)
apply(simp_all)
done

context J_heap_base begin

lemma WTrt_new_types_types: "P,E,h \<turnstile> e : T \<Longrightarrow> new_types e \<subseteq> types P"
  and WTrts_new_typess_types: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> new_typess es \<subseteq> types P"
by(induct rule: WTrt_WTrts.inducts) simp_all

lemma WT_new_types_types: "P,E \<turnstile> e :: T \<Longrightarrow> new_types e \<subseteq> types P"
  and WTs_new_typess_types: "P,E \<turnstile> es [::] Ts \<Longrightarrow> new_typess es \<subseteq> types P"
by(induct rule: WT_WTs.inducts) simp_all

lemma assumes wf: "wf_J_prog P"
  shows "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; new_types e \<subseteq> types P \<rbrakk> \<Longrightarrow> new_types e' \<subseteq> types P"
  and "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; new_typess es \<subseteq> types P \<rbrakk> \<Longrightarrow> new_typess es' \<subseteq> types P"
proof(induct rule: red_reds.inducts)
  case (RedCall s a U C M Ts T pns body D vs)
  from wf `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
  have "wf_mdecl wf_J_mdecl P D (M, Ts, T, pns, body)" by(rule sees_wf_mdecl)
  then obtain T' where "P,[this \<mapsto> Class D, pns [\<mapsto>] Ts] \<turnstile> body :: T'" by(auto simp add: wf_mdecl_def)
  hence "new_types body \<subseteq> types P" by(rule WT_new_types_types)
  with RedCall show ?case by(simp add: new_types_blocks)
next
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  thus ?case by(cases va)(simp_all)
qed(simp_all)

end

context J_heap_conf begin

lemma red_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; new_types e \<subseteq> types P; hconf (hp s); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s') a = Some (ty_of_htype x)"
  and reds_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; new_typess es \<subseteq> types P; hconf (hp s); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s') a = Some (ty_of_htype x)"
apply(induct rule: red_reds.inducts)
apply(auto dest: new_obj_SomeD new_arr_SomeD red_external_New_typeof_addrD)
done

lemma red_NewArr_lengthD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; new_types e \<subseteq> types P; hconf (hp s); NewArr a T' n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length (hp s') a = n"
  and reds_NewArr_lengthD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; new_typess es \<subseteq> types P; hconf (hp s); NewArr a T' n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length (hp s') a = n"
apply(induct rule: red_reds.inducts)
apply(auto dest: new_arr_SomeD red_external_NewArr_lengthD)
done

lemma J_conf_read_heap_read_typed:
  "J_conf_read addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write hconf P"
proof -
  interpret conf!: heap_conf_read
    addr2thread_id thread_id2addr 
    empty_heap new_obj new_arr typeof_addr array_length "heap_read_typed P" heap_write hconf 
    P
    by(rule heap_conf_read_heap_read_typed)
  show ?thesis by(unfold_locales)
qed

lemma red_ta_seq_consist_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T;
    ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)); vs_conf P (hp s) vs; hconf (hp s) \<rbrakk>
  \<Longrightarrow> J_heap_base.red addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write (convert_extTA extTA) P t e s ta e' s' \<and> vs_conf P (hp s') (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and reds_ta_seq_consist_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts;
    ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)); vs_conf P (hp s) vs; hconf (hp s) \<rbrakk>
  \<Longrightarrow> J_heap_base.reds addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write (convert_extTA extTA) P t es s ta es' s' \<and> vs_conf P (hp s') (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedNew thus ?case
    by(auto dest: vs_conf_new_obj intro: J_heap_base.red_reds.intros)
next
  case RedNewFail thus ?case
    by(auto dest: hext_new_obj intro: vs_conf_hext intro: J_heap_base.red_reds.intros)
next
  case RedNewArray thus ?case
    by(auto dest: vs_conf_new_arr intro: J_heap_base.red_reds.intros)
next
  case RedNewArrayFail thus ?case
    by(auto dest: hext_new_arr intro: vs_conf_hext J_heap_base.red_reds.intros)
next
  case RedAAcc thus ?case
    by(auto intro: J_heap_base.red_reds.RedAAcc intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)
next
  case (RedAAss h a U i w V h' xs)
  from `sint i < int (array_length h a)` `0 <=s i` have "nat (sint i) < array_length h a"
    by (metis nat_less_iff sint_0 word_sle_def)
  with `typeof_addr h a = \<lfloor>U\<lfloor>\<rceil>\<rfloor>` have "P,h \<turnstile> a@ACell (nat (sint i)) : U"
    by(auto intro: addr_loc_type.intros)
  moreover from `heap_write h a (ACell (nat (sint i))) w h'` have "h \<unlhd> h'" by(rule hext_heap_write)
  ultimately have "P,h' \<turnstile> a@ACell (nat (sint i)) : U" by(rule addr_loc_type_hext_mono)
  moreover from `typeof\<^bsub>h\<^esub> w = \<lfloor>V\<rfloor>` `P \<turnstile> V \<le> U` have "P,h \<turnstile> w :\<le> U" by(simp add: conf_def)
  with `h \<unlhd> h'` have "P,h' \<turnstile> w :\<le> U" by(rule conf_hext)
  ultimately have "\<exists>T. P,h' \<turnstile> a@ACell (nat (sint i)) : T \<and> P,h' \<turnstile> w :\<le> T" by blast 
  thus ?case using RedAAss
    by(auto intro: J_heap_base.red_reds.intros intro!: vs_confI split: split_if_asm dest: vs_confD)(blast dest: vs_confD hext_heap_write intro: addr_loc_type_hext_mono conf_hext)+
next
  case RedFAcc thus ?case
    by(auto intro: J_heap_base.red_reds.RedFAcc intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)
next
  case (RedFAss h e D F v h' xs)
  hence "\<exists>T. P,h' \<turnstile> e@CField D F : T \<and> P,h' \<turnstile> v :\<le> T"
    by(force dest: typeof_addr_eq_Some_conv dest!: hext_heap_write intro!: addr_loc_type.intros intro: typeof_addr_hext_mono type_of_hext_type_of simp add: conf_def)
  thus ?case using RedFAss
    by(auto intro: J_heap_base.red_reds.intros intro!: vs_confI split: split_if_asm dest: vs_confD typeof_addr_eq_Some_conv)(blast dest: vs_confD hext_heap_write intro: addr_loc_type_hext_mono conf_hext)+
next
  case RedCall thus ?case
    by(safe)((blast intro: J_heap_base.red_reds.RedCall)+, simp_all)
next
  case RedCallExternal thus ?case
    by(auto intro: J_heap_base.red_reds.RedCallExternal red_external_ta_seq_consist_typeable)
qed(auto intro: J_heap_base.red_reds.intros)

end

sublocale J_heap_base < red_mthr!: 
  if_multithreaded
    final_expr
    "mred P"
    convert_RA
  for P
by(unfold_locales)




locale J_allocated_heap_conf = 
  J_heap_conf 
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf
    P
  +
  J_allocated_heap 
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
    allocated
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr J_prog"
begin

lemma mred_known_addrs_typing:
  assumes wf: "wf_J_prog P"
  and ok: "start_heap_ok"
  shows "known_addrs_typing addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length heap_write allocated J_known_addrs final_expr (mred P) (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h) P"
proof -
  interpret known_addrs
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" P
    using wf ok by(rule mred_known_addrs)
  
  show ?thesis
  proof
    fix s t ta s' vs
    assume red: "P \<turnstile> s -t\<triangleright>ta\<rightarrow> s'"
      and ts_ok: "ts_ok (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h) (thr s) (shr s)"
      and vs: "vs_conf P (shr s) vs"
      and sc: "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
    let ?mred = "J_heap_base.mred addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write P"
    have "lifting_inv final_expr ?mred sconf_type_ok"
      by(intro J_conf_read.lifting_inv_sconf_subject_ok J_conf_read_heap_read_typed wf)
    moreover
    from red have "multithreaded_base.redT final_expr ?mred convert_RA s (t, ta) s'"
    proof(cases)
      case redT_normal thus ?thesis using sc vs ts_ok
        by(auto simp add: split_beta sconf_type_ok_def type_ok_def sconf_def intro!: multithreaded_base.redT.redT_normal)(auto dest!: ts_okD dest: red_ta_seq_consist_typeable)
    qed(blast intro: multithreaded_base.redT.intros)
    moreover
    from ts_ok_Ex_into_ts_inv[OF ts_ok[simplified split_def]] obtain ET
      where tsinv: "ts_inv sconf_type_ok ET (thr s) (shr s)" by(auto)
    ultimately
    have "ts_inv sconf_type_ok (upd_invs ET sconf_type_ok \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) (thr s') (shr s')"
      by(rule lifting_inv.redT_invariant)
    hence "ts_ok (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h) (thr s') (shr s')" (is ?thesis1)
      by(rule ts_inv_into_ts_ok_Ex)
    moreover from red have "vs_conf P (shr s') (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" (is ?thesis2)
    proof(cases)
      case (redT_normal x x' m')
      thus ?thesis using sc vs ts_ok
        by(cases x)(auto dest!: ts_okD simp add: sconf_type_ok_def type_ok_def sconf_def dest: red_ta_seq_consist_typeable)
    next
      case (redT_acquire x ln l)
      have "mrw_values P vs (map NormalAction (convert_RA ln :: ('addr, 'thread_id) obs_event list)) = vs"
        by(auto simp add: convert_RA_not_write fun_eq_iff intro!: mrw_values_no_write_unchanged)
      thus ?thesis using vs redT_acquire by auto
    qed
    ultimately show "?thesis1 \<and> ?thesis2" ..
  next
    fix t x m ta x' m' ad al v
    assume "mred P t (x, m) ta (x', m')"
      and "\<exists>ET. sconf_type_ok ET t x m"
      and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "\<exists>T. P,m \<turnstile> ad@al : T"
      by(fastsimp simp add: sconf_type_ok_def type_ok_def sconf_def split_beta dest: red_read_typeable)
  next
    fix t x m ta x' m' ad C
    assume "mred P t (x, m) ta (x', m')"
      and "\<exists>ET. sconf_type_ok ET t x m"
      and "NewObj ad C \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "typeof_addr m' ad = \<lfloor>Class C\<rfloor>"
      by(auto dest: red_New_typeof_addrD[where x="Class_type C"] dest!: WTrt_new_types_types simp add: split_beta sconf_type_ok_def sconf_def type_ok_def)
  next
    fix t x m ta x' m' ad T n
    assume "mred P t (x, m) ta (x', m')"
      and "\<exists>ET. sconf_type_ok ET t x m"
      and "NewArr ad T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "typeof_addr m' ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor> \<and> array_length m' ad = n"
      by(auto dest: red_New_typeof_addrD[where x="Array_type T n"] red_NewArr_lengthD dest!: WTrt_new_types_types simp add: split_beta sconf_type_ok_def sconf_def type_ok_def)
  qed
qed

end

context J_allocated_heap_conf begin

lemma executions_sc:
  assumes wf: "wf_J_prog P"
  and ok: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=(pns, body) in D"
  and vs1: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and vs2: "\<Union>ka_Val ` set vs \<subseteq> set start_addrs"
  shows
  "executions_sc (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` red_mthr.if.\<E> P (init_fin_lift_state status (J_start_state P C M vs))) P"
  (is "executions_sc ?E P")
proof -
  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" "\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h" P
    using wf ok by(rule mred_known_addrs_typing)
  
  from wf_prog_wf_syscls[OF wf] ok
  show ?thesis
  proof(rule executions_sc)
    from wf ok sees vs1
    have "sconf_type_ts_ok [start_tid \<mapsto> (empty, T)] (thr (J_start_state P C M vs)) (shr (J_start_state P C M vs))"
      by(rule J_start_state_sconf_type_ok)
    thus "ts_ok (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h) (thr (J_start_state P C M vs)) start_heap"
      by -(rule ts_inv_into_ts_ok_Ex, simp add: start_state_def split_beta)
  next
    from start_state_vs_conf[OF wf]
    show "vs_conf P start_heap (mrw_values P empty (map NormalAction start_heap_obs))"
      by(simp add: start_state_def lift_start_obs_def o_def)
  next
    from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, pns, body)" by(rule sees_wf_mdecl)
    then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
      by(auto simp add: wf_mdecl_def)
    from vs1 have len2: "length vs = length Ts" by(rule list_all2_lengthD)
    show "J_known_addrs start_tid ((\<lambda>(pns, body) vs. (blocks (this # pns) (Class (fst (method P C M)) # fst (snd (method P C M))) (Null # vs) body, empty)) (snd (snd (snd (method P C M)))) vs) \<subseteq> allocated start_heap"
      using sees vs2 len1 len2 WT_ka[OF wt]
      by(auto simp add: split_beta start_addrs_allocated ka_blocks intro: start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok])
  qed
qed

end


declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

context J_progress begin

lemma ex_WTrt_simps:
  "P,E,h \<turnstile> e : T \<Longrightarrow> \<exists>E T. P,E,h \<turnstile> e : T"
by blast

lemma assumes hrt: "heap_read_typeable"
  and vs: "vs_conf P (shr s) vs"
  and hconf: "hconf (shr s)"
  shows red_cut_and_update:
  "\<lbrakk> P,t \<turnstile> \<langle>e, (shr s, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>; \<exists>E T. P,E,shr s \<turnstile> e : T;
    red_mthr.if.actions_ok s t ta; 
   (\<Union>a \<in> J_known_addrs t (e, xs) \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs \<rbrakk>
  \<Longrightarrow> \<exists>ta' e'' xs'' h''. P,t \<turnstile> \<langle>e, (shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e'', (h'', xs'')\<rangle> \<and> 
           red_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
  and reds_cut_and_update:
  "\<lbrakk> P,t \<turnstile> \<langle>es, (shr s, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>; \<exists>E Ts. P,E,shr s \<turnstile> es [:] Ts;
     red_mthr.if.actions_ok s t ta;
     (\<Union>a \<in> {thread_id2addr t} \<union> kas es \<union> ka_locals xs \<union> set start_addrs \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs \<rbrakk>
  \<Longrightarrow> \<exists>ta' es'' xs'' h''. P,t \<turnstile> \<langle>es, (shr s, xs)\<rangle> [-ta'\<rightarrow>] \<langle>es'', (h'', xs'')\<rangle> \<and> 
           red_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
unfolding J_known_addrs.simps
proof(induct e hxs\<equiv>"(shr s, xs)" ta e' hxs'\<equiv>"(h', xs')" 
        and es hxs\<equiv>"(shr s, xs)" ta es' hxs'\<equiv>"(h', xs')"
      arbitrary: xs xs' and xs xs' rule: red_reds.inducts)
  case (RedAAcc a U i v e)
  hence adal: "P,shr s \<turnstile> a@ACell (nat (sint i)) : U"
    by(auto intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def)
  with RedAAcc obtain b v' where bv': "vs (a, ACell (nat (sint i))) = \<lfloor>(v', b)\<rfloor>"
    by(auto)(thin_tac "?P \<subseteq> dom vs", drule subsetD, auto)
  with vs adal have "P,shr s \<turnstile> v' :\<le> U" by(auto dest!: vs_confD dest: addr_loc_type_fun)
  with hrt adal have "heap_read (shr s) a (ACell (nat (sint i))) v'" using hconf by(rule heap_read_typeableD)
  with bv' `typeof_addr (shr s) a = \<lfloor>U\<lfloor>\<rceil>\<rfloor>` `0 <=s i` `sint i < int (array_length (shr s) a)` 
    `red_mthr.if.actions_ok s t \<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>`
  show ?case by(fastsimp intro: red_reds.RedAAcc)
next
  case (RedFAcc a D F v)
  then obtain T where "P,E,shr s \<turnstile> addr a\<bullet>F{D} : T" by blast
  with RedFAcc have adal: "P,shr s \<turnstile> a@CField D F : T"
    by(auto dest: typeof_addr_eq_Some_conv intro: addr_loc_type.intros)
  with RedFAcc obtain b v' where bv': "vs (a, CField D F) = \<lfloor>(v', b)\<rfloor>"
    by(auto)(thin_tac "?P \<subseteq> dom vs", drule subsetD, auto)+
  with vs adal have "P,shr s \<turnstile> v' :\<le> T" by(auto dest!: vs_confD dest: addr_loc_type_fun)
  with hrt adal have "heap_read (shr s) a (CField D F) v'" using hconf by(rule heap_read_typeableD)
  with bv' `red_mthr.if.actions_ok s t \<lbrace>ReadMem a (CField D F) v\<rbrace>`
  show ?case by(fastsimp intro: red_reds.RedFAcc)
next
  case (RedCallExternal a U M ps ta' va h' ta e')
  from `P,t \<turnstile> \<langle>a\<bullet>M(ps),hp (shr s, xs)\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>`
  have red: "P,t \<turnstile> \<langle>a\<bullet>M(ps),shr s\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
  from RedCallExternal have aok: "red_mthr.if.actions_ok s t ta'" by simp
  from RedCallExternal have "{(a, al) |al. \<exists>T. P,shr s \<turnstile> a@al : T} \<subseteq> dom vs" by auto
  from red_external_cut_and_update[OF hrt vs this red aok hconf]
    `typeof_addr (hp (shr s, xs)) a = \<lfloor>U\<rfloor>` `is_native P U M` `ta = extTA2J P ta'`
  show ?case by(fastsimp intro: red_reds.RedCallExternal)
next
  case RedNew thus ?case by(fastsimp intro!: red_reds.RedNew exI)
next
  case RedNewFail thus ?case by(fastsimp intro!: red_reds.RedNewFail exI)
next
  case NewArrayRed thus ?case by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.NewArrayRed)
next 
  case RedNewArray thus ?case by(fastsimp intro!: red_reds.RedNewArray exI)
next
  case RedNewArrayFail thus ?case by(fastsimp intro!: red_reds.RedNewArrayFail exI)
next
  case RedNewArrayNegative thus ?case by(fastsimp intro!: red_reds.RedNewArrayNegative exI)
next
  case CastRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CastRed)
next
  case RedCast thus ?case by(fastsimp intro!: red_reds.RedCast exI)
next
  case RedCastFail thus ?case by(fastsimp intro!: red_reds.RedCastFail exI)
next
  case InstanceOfRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.InstanceOfRed)
next
  case RedInstanceOf thus ?case
    by(intro exI conjI)(rule red_reds.RedInstanceOf, simp_all)
next
  case BinOpRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.BinOpRed1)
next
  case BinOpRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.BinOpRed2)
next
  case RedBinOp thus ?case by(fastsimp intro!: red_reds.RedBinOp exI)
next
  case RedBinOpFail thus ?case by(fastsimp intro!: red_reds.RedBinOpFail exI)
next
  case RedVar thus ?case by(fastsimp intro!: red_reds.RedVar exI)
next
  case LAssRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.LAssRed)
next
  case RedLAss thus ?case by(fastsimp intro!: red_reds.RedLAss exI)
next
  case AAccRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAccRed1)
next
  case AAccRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAccRed2)
next
  case RedAAccNull thus ?case by(fastsimp intro!: red_reds.RedAAccNull exI)
next
  case RedAAccBounds thus ?case by(fastsimp intro!: red_reds.RedAAccBounds exI)
next
  case AAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAssRed1)
next
  case AAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAssRed2)
next
  case AAssRed3 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAssRed3)+
next
  case RedAAss thus ?case by(fastsimp intro!: red_reds.RedAAss exI)
next
  case RedAAssBounds thus ?case by(fastsimp intro!: red_reds.RedAAssBounds exI)
next
  case RedAAssStore thus ?case
    by(clarsimp simp add: ex_WTrt_simps)(fastsimp intro!: red_reds.RedAAssStore exI)
next
  case RedAAssNull thus ?case by(fastsimp intro!: red_reds.RedAAssNull exI)
next
  case ALengthRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ALengthRed)
next
  case RedALength thus ?case by(fastsimp intro!: red_reds.RedALength exI)
next
  case RedALengthNull thus ?case by(fastsimp intro!: red_reds.RedALengthNull exI)
next
  case FAccRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.FAccRed)
next
  case RedFAccNull thus ?case by(fastsimp intro!: red_reds.RedFAccNull exI)
next
  case FAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.FAssRed1)
next
  case FAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.FAssRed2)
next
  case RedFAss thus ?case by(fastsimp intro!: red_reds.RedFAss exI)
next
  case RedFAssNull thus ?case by(fastsimp intro!: red_reds.RedFAssNull exI)
next
  case CallObj thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CallObj)
next
  case CallParams thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CallParams)
next
  case RedCall thus ?case by(fastsimp intro!: red_reds.RedCall exI)
next
  case RedCallNull thus ?case by(fastsimp intro!: red_reds.RedCallNull exI)
next
  case (BlockRed e xs V vo)
  note domIff[iff del]
  from BlockRed.prems(3) ka_locals_update_subset[where xs=xs and V=V]
  have "(\<Union>a\<in>ka_locals (xs(V := vo)). {(a, al) |al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs"
    apply(clarsimp)
     apply(drule (1) subsetD)
     apply(rotate_tac -4)
     apply(erule subsetD)
     apply blast
    apply(erule meta_allE)
    apply(drule (1) subsetD)
    apply(safe)
     apply(rotate_tac -5)
     apply(erule subsetD)
     apply blast
    apply(rotate_tac -4)
    apply(erule subsetD)
    apply blast
    done
  with BlockRed show ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(fastsimp intro: red_reds.BlockRed)+
next
  case RedBlock thus ?case by(fastsimp intro!: red_reds.RedBlock exI)
next
  case SynchronizedRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.SynchronizedRed1)
next
  case SynchronizedNull thus ?case by(fastsimp intro!: red_reds.SynchronizedNull exI)
next
  case LockSynchronized thus ?case by(fastsimp intro!: red_reds.LockSynchronized exI)
next
  case SynchronizedRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.SynchronizedRed2)
next
  case UnlockSynchronized thus ?case by(fastsimp intro!: red_reds.UnlockSynchronized exI)
next
  case SeqRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.SeqRed)
next
  case RedSeq thus ?case by(fastsimp intro!: red_reds.RedSeq exI)
next
  case CondRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CondRed)
next
  case RedCondT thus ?case by(fastsimp intro!: red_reds.RedCondT exI)
next
  case RedCondF thus ?case by(fastsimp intro!: red_reds.RedCondF exI)
next
  case RedWhile thus ?case by(fastsimp intro!: red_reds.RedWhile exI)
next
  case ThrowRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ThrowRed)
next
  case RedThrowNull thus ?case by(fastsimp intro!: red_reds.RedThrowNull exI)
next
  case TryRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.TryRed)
next
  case RedTry thus ?case by(fastsimp intro!: red_reds.RedTry exI)
next
  case RedTryFail thus ?case by(fastsimp intro!: red_reds.RedTryFail exI)
next
  case RedTryCatch thus ?case by(fastsimp intro!: red_reds.RedTryCatch exI)
next
  case ListRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ListRed1)
next
  case ListRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ListRed2)
next
  case BlockThrow thus ?case by(fastsimp intro!: red_reds.BlockThrow exI)
qed(clarsimp simp add: ex_WTrt_simps, force intro: red_reds.intros intro!: exI)+

end


sublocale J_allocated_heap_conf < if_known_addrs_base
  J_known_addrs
  final_expr "mred P" convert_RA 
.


declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

locale J_allocated_progress = 
  J_progress
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf
    P
  +
  J_allocated_heap_conf
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf
    allocated
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr J_prog"
begin

lemma cut_and_update:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable"
  and ok: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and ka: "\<Union>ka_Val ` set vs \<subseteq> set start_addrs"
  shows "red_mthr.if.cut_and_update (init_fin_lift_state status (J_start_state P C M vs)) 
                                    (mrw_values P empty (map snd (lift_start_obs start_tid start_heap_obs)))"
  (is "red_mthr.if.cut_and_update ?start_state ?start_vs")
proof(rule red_mthr.if.cut_and_updateI)

  fix ttas s' t x ta x' m'
  assume \<tau>Red: "red_mthr.if.RedT P ?start_state ttas s'"
    and sc: "ta_seq_consist P ?start_vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ts't: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "red_mthr.init_fin P t (x, shr s') ta (x', m')"
    and aok: "red_mthr.if.actions_ok s' t ta"

  let ?conv = "\<lambda>ttas. concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  let ?vs' = "mrw_values P ?start_vs (?conv ttas)"
  let ?wt_ok = "init_fin_lift_inv sconf_type_ok"
  let ?ET_start = "J_sconf_type_ET_start P C M"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"
  let ?start_state = "init_fin_lift_state status (J_start_state P C M vs)"

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" "\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h" P
    using wf ok by(rule mred_known_addrs_typing)

  from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, pns, body)" by(rule sees_wf_mdecl)
  then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
    by(auto simp add: wf_mdecl_def)
  from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)

  from wf ok sees conf
  have "sconf_type_ts_ok [start_tid \<mapsto> (empty, T)] (thr (J_start_state P C M vs)) (shr (J_start_state P C M vs))"
    by(rule J_start_state_sconf_type_ok)
  hence ts_ok_start: "ts_ok (init_fin_lift (\<lambda>t x h. \<exists>i. sconf_type_ok i t x h)) (thr ?start_state) (shr ?start_state)"
    unfolding ts_ok_init_fin_lift_init_fin_lift_state by(rule ts_inv_into_ts_ok_Ex)
  have sc': "ta_seq_consist P ?start_vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of ttas))))"
    using sc by(simp add: lmap_lconcat lmap_compose[symmetric] o_def split_def lconcat_llist_of[symmetric] del: lmap_compose)
  from start_state_vs_conf[OF wf]
  have vs_conf_start: "vs_conf P (shr ?start_state) ?start_vs"
    by(simp add:init_fin_lift_state_conv_simps start_state_def split_beta)
  with \<tau>Red ts_ok_start sc
  have wt': "ts_ok (init_fin_lift (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h)) (thr s') (shr s')"
    and vs': "vs_conf P (shr s') ?vs'" by(rule if_RedT_ta_seq_consist_invar)+

  note \<tau>Red sc
  moreover
  have "(\<Union>a\<in>if.known_addrs_state ?start_state \<union> mrw_addrs ?start_vs. {(a, al) |al. \<exists>T. P,shr ?start_state \<turnstile> a@al : T})
 \<subseteq> dom ?start_vs"
    using sees len2 len1 ka WT_ka[OF wt] mrw_addrs_start_heap_obs[of empty]
      start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok]
    by(auto simp add: start_state_def if.known_addrs_state_def if.known_addrs_thr_def split_beta init_fin_lift_state_def lift_start_obs_def o_def ka_blocks dest: WT_ka split: split_if_asm)(force dest: start_addrs_dom_mrw_values[OF wf_prog_wf_syscls[OF wf]])+
  moreover have "if.known_addrs_state ?start_state \<union> mrw_addrs ?start_vs \<subseteq> dom (typeof_addr (shr ?start_state))"
    using sees len1 len2 ka WT_ka[OF wt]
      dom_typeof_addr_start_heap[OF wf_prog_wf_syscls[OF wf]]
      start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok]
      mrw_addrs_lift_start_heap_obs[where vs="empty"]
    by(auto 4 4 simp add: start_state_def if.known_addrs_state_def if.known_addrs_thr_def split_beta init_fin_lift_state_def ka_blocks split: split_if_asm)
  ultimately have dom_vs: "(\<Union>a\<in>if.known_addrs_state s' \<union> mrw_addrs ?vs'. {(a, al) |al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom ?vs'"
    and "if.known_addrs_state s' \<union> mrw_addrs ?vs' \<subseteq> dom (typeof_addr (shr s'))"
    using ts_ok_start vs_conf_start by(rule if_RedT_known_addrs_mrw_addrs_dom_vs)+

  show "\<exists>ta' x'' m''. red_mthr.init_fin P t (x, shr s') ta' (x'', m'') \<and>
                      red_mthr.if.actions_ok s' t ta' \<and>
                      ta_seq_consist P ?vs' (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                      eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs'"
  proof(cases "ta_seq_consist P ?vs' (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)")
    case True
    hence "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ?vs'"
      by(rule ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
    with red aok True show ?thesis by blast
  next
    case False
    with red obtain e xs e' xs' ta'
      where x: "x = (Running, e, xs)" and x': "x' = (Running, e', xs')"
      and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
      and red': "P,t \<turnstile> \<langle>e, (shr s', xs)\<rangle> -ta'\<rightarrow> \<langle>e', (m', xs')\<rangle>"
      by cases fastsimp+

    from ts't wt' x obtain E T where wte: "P,E,shr s' \<turnstile> e : T"
      and hconf: "hconf (shr s')"
      by(auto dest!: ts_okD simp add: sconf_type_ok_def sconf_def type_ok_def)

    have aok': "red_mthr.if.actions_ok s' t ta'"
      using aok unfolding ta by simp

    from dom_vs ts't x
    have "(\<Union>a\<in>J_known_addrs t (e, xs) \<union>  mrw_addrs ?vs'. {(a, al) |al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom ?vs'"
      by -(rule UN_least, erule UNION_subsetD, clarify, rule if.known_addrs_stateI, auto)

    from red_cut_and_update[OF hrt vs' hconf red' _ aok' this] wte
    obtain ta'' e'' xs'' h''
      where red'': "P,t \<turnstile> \<langle>e, (shr s', xs)\<rangle> -ta''\<rightarrow> \<langle>e'', (h'', xs'')\<rangle>"
      and aok'': "red_mthr.if.actions_ok s' t ta''"
      and sc'': "ta_seq_consist P ?vs' (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
      and eq'': "eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) ?vs'"
      by blast

    let ?x' = "(Running, e'', xs'')"
    let ?ta' = "convert_TA_initial (convert_obs_initial ta'')"
    from red'' have "red_mthr.init_fin P t (x, shr s') ?ta' (?x', h'')"
      unfolding x by -(rule red_mthr.init_fin.NormalAction, simp)
    moreover from aok'' have "red_mthr.if.actions_ok s' t ?ta'" by simp
    moreover from sc'' have "ta_seq_consist P ?vs' (llist_of \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub>)" by simp
    moreover from eq'' have "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> ?vs'" unfolding ta by simp
    ultimately show ?thesis by blast
  qed
qed

lemma J_executions:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable"
  and ok: "start_heap_ok"
  and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and ka: "\<Union>ka_Val ` set vs \<subseteq> set start_addrs"
shows "executions (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
                   red_mthr.if.\<E> P (init_fin_lift_state status (J_start_state P C M vs))) P"
proof -
  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" "\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h" P
    using wf ok by(rule mred_known_addrs_typing)

  from cut_and_update[OF wf hrt ok sees conf ka] wf_prog_wf_syscls[OF wf] ok
  show ?thesis
  proof(rule executions)
    from wf ok sees conf
    have "sconf_type_ts_ok [start_tid \<mapsto> (empty, T)] (thr (J_start_state P C M vs)) (shr (J_start_state P C M vs))"
      by(rule J_start_state_sconf_type_ok)
    thus "ts_ok (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h) (thr (J_start_state P C M vs)) start_heap"
      by -(rule ts_inv_into_ts_ok_Ex, simp add: start_state_def split_beta)
  next
    from start_state_vs_conf[OF wf]
    show "vs_conf P start_heap (mrw_values P empty (map NormalAction start_heap_obs))"
      by(simp add: start_state_def lift_start_obs_def o_def)
  next
    from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, pns, body)" by(rule sees_wf_mdecl)
    then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
      by(auto simp add: wf_mdecl_def)
    from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)
    show "J_known_addrs start_tid ((\<lambda>(pns, body) vs. (blocks (this # pns) (Class (fst (method P C M)) # fst (snd (method P C M))) (Null # vs) body, empty)) (snd (snd (snd (method P C M)))) vs) \<subseteq> allocated start_heap"
      using sees ka len1 len2 WT_ka[OF wt]
      by(auto simp add: split_beta start_addrs_allocated ka_blocks intro: start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok])
  qed
qed

end

end