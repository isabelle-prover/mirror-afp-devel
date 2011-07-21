theory DRF_JVM imports
  "JMM_Common"
  "../BV/BVProgressThreaded"
begin

subsection {* Und jetzt alles fuer die JVM nochmal *}


abbreviation (input) ka_xcp :: "'addr option \<Rightarrow> 'addr set"
where "ka_xcp \<equiv> Option.set"

primrec jvm_ka :: "'addr jvm_thread_state \<Rightarrow> 'addr set"
where
  "jvm_ka (xcp, frs) = 
   ka_xcp xcp \<union> (\<Union>(stk, loc, C, M, pc) \<in> set frs. (\<Union>v \<in> set stk. ka_Val v) \<union> (\<Union>v \<in> set loc. ka_Val v))"

context heap begin

lemma red_external_aggr_read_mem_typeable:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; is_native P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,h \<turnstile> ad@al : T'"
by(auto simp add: red_external_aggr_def split_beta is_native_def2 native_call_def external_WT_defs.simps split: split_if_asm dest: heap_clone_read_typeable)

end

context JVM_heap_base begin

definition jvm_known_addrs :: "'thread_id \<Rightarrow> 'addr jvm_thread_state \<Rightarrow> 'addr set"
where "jvm_known_addrs t xcpfrs = {thread_id2addr t} \<union> jvm_ka xcpfrs \<union> set start_addrs"

end

context JVM_heap begin

lemma exec_instr_known_addrs:
  assumes ok: "start_heap_ok"
  and exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  shows "jvm_known_addrs t (xcp', frs') \<subseteq> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs) \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
proof -
  
  note [simp] = jvm_known_addrs_def new_obs_addrs_def addr_of_sys_xcpt_start_addr[OF ok] subset_Un1 subset_Un2 subset_insert ka_Val_subset_new_obs_Addr_ReadMem SUP_subset_mono split_beta neq_Nil_conv tl_conv_drop set_drop_subset is_Ref_def

  from exec check show ?thesis
  proof(cases "i")
    case Load with exec check show ?thesis by auto
  next
    case (Store V) with exec check show ?thesis
      using set_update_subset_insert[of loc V]
      by(clarsimp simp del: set_update_subsetI) blast
  next
    case (Push v)
    with check have "ka_Val v = {}" by(cases v) simp_all
    with Push exec check show ?thesis by(simp)
  next
    case (Invoke M' n)
    show ?thesis
    proof(cases "stk ! n = Null")
      case True with exec check Invoke show ?thesis by(simp)
    next
      case False[simp]
      with check Invoke obtain a where stkn: "stk ! n = Addr a" "n < length stk" by auto
      hence a: "a \<in> (\<Union>v \<in> set stk. ka_Val v)" by(fastsimp dest: nth_mem)
      show ?thesis
      proof(cases "is_native P (the (typeof_addr h (the_Addr (stk ! n)))) M'")
        case True
        with exec check Invoke a stkn show ?thesis
          apply clarsimp
          apply(drule red_external_aggr_known_addrs_mono[OF ok], simp)
          apply(auto dest!: in_set_takeD dest: bspec subsetD split: extCallRet.split_asm)
          done
      next
        case False
        with exec check Invoke a stkn show ?thesis
          by(auto simp add: set_replicate_conv_if dest!: in_set_takeD)
      qed
    qed
  next
    case Swap with exec check show ?thesis
      by(cases stk)(simp, case_tac list, auto)
  next
    case (BinOpInstr bop) with exec check show ?thesis
      using binop_known_addrs[OF ok, of bop "hd (drop (Suc 0) stk)" "hd stk"]
      apply(cases stk)
      apply(simp, case_tac list, simp)
      apply clarsimp
      apply(drule (2) binop_progress)
      apply(auto 6 2 split: sum.split_asm)
      done
  next
    case MExit with exec check show ?thesis by(auto split: split_if_asm)
  qed(clarsimp split: split_if_asm)+
qed

lemma exec_d_known_addrs_mono:
  assumes ok: "start_heap_ok"
  and exec: "mexecd P t (xcpfrs, h) ta (xcpfrs', h')"
  shows "jvm_known_addrs t xcpfrs' \<subseteq> jvm_known_addrs t xcpfrs \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using exec
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp add: split_beta)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
 apply(fastsimp simp add: check_def split_beta del: subsetI dest!: exec_instr_known_addrs[OF ok])
apply(fastsimp simp add: jvm_known_addrs_def split_beta dest!: in_set_dropD)
done

lemma exec_instr_known_addrs_ReadMem:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs)"
using assms
proof(cases i)
  case ALoad thus ?thesis using assms
    by(cases stk)(case_tac [2] list, auto simp add: split_beta is_Ref_def jvm_known_addrs_def split: split_if_asm)
next
  case (Invoke M n)
  with check have "stk ! n \<noteq> Null \<longrightarrow> the_Addr (stk ! n) \<in> ka_Val (stk ! n)" "stk ! n \<in> set stk"
    by(auto simp add: is_Ref_def)
  with assms Invoke show ?thesis
    by(auto simp add: split_beta is_Ref_def simp del: ka_Val.simps nth_mem split: split_if_asm dest!: red_external_aggr_known_addrs_ReadMem in_set_takeD del: is_AddrE)(auto simp add: jvm_known_addrs_def simp del: ka_Val.simps nth_mem del: is_AddrE)
next
  case Getfield thus ?thesis using assms
    by(auto simp add: jvm_known_addrs_def neq_Nil_conv is_Ref_def split: split_if_asm)
qed(auto simp add: split_beta is_Ref_def neq_Nil_conv split: split_if_asm)

lemma mexecd_known_addrs_ReadMem:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> jvm_known_addrs t xcpfrs"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply simp
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto simp add: check_def dest: exec_instr_known_addrs_ReadMem)
done

lemma exec_instr_known_addrs_WriteMem:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and "write": "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a)" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "a \<in> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs) \<or> a \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
using assms
proof(cases i)
  case (Invoke M n)
  with check have "stk ! n \<noteq> Null \<longrightarrow> the_Addr (stk ! n) \<in> ka_Val (stk ! n)" "stk ! n \<in> set stk"
    by(auto simp add: is_Ref_def)
  thus ?thesis using assms Invoke
    by(auto simp add: is_Ref_def split_beta split: split_if_asm simp del: ka_Val.simps nth_mem dest!: red_external_aggr_known_addrs_WriteMem in_set_takeD del: is_AddrE)(auto simp add: jvm_known_addrs_def del: is_AddrE)
next
  case AStore with assms show ?thesis
    by(cases stk)(auto simp add: jvm_known_addrs_def split: split_if_asm)
next
  case Putfield with assms show ?thesis
    by(cases stk)(auto simp add: jvm_known_addrs_def split: split_if_asm)
qed(auto simp add: split_beta split: split_if_asm)

lemma mexecd_known_addrs_WriteMem:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a \<in> jvm_known_addrs t xcpfrs \<or> a \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply simp
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto simp add: check_def dest: exec_instr_known_addrs_WriteMem)
done

lemma exec_instr_known_addrs_new_thread:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and new: "NewThread t' x' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "jvm_known_addrs t' x' \<subseteq> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs)"
using assms
proof(cases i)
  case (Invoke M n)
  with assms have "stk ! n \<noteq> Null \<longrightarrow> the_Addr (stk ! n) \<in> ka_Val (stk ! n) \<and> thread_id2addr (addr2thread_id (the_Addr (stk ! n))) = the_Addr (stk ! n)" "stk ! n \<in> set stk"
    apply(auto simp add: is_Ref_def split: split_if_asm)
    apply(frule red_external_aggr_NewThread_idD, simp, simp)
    apply(drule red_external_aggr_new_thread_sub_thread)
    apply(auto intro: addr2thread_id_inverse)
    done
  with assms Invoke show ?thesis
    apply(auto simp add: is_Ref_def split_beta split: split_if_asm simp del: nth_mem del: is_AddrE)
    apply(drule red_external_aggr_NewThread_idD)
    apply(auto simp add: extNTA2JVM_def jvm_known_addrs_def split_beta simp del: nth_mem del: is_AddrE)
    done
qed(auto simp add: split_beta split: split_if_asm)

lemma mexecd_known_addrs_new_thread:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); NewThread t' x' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> jvm_known_addrs t' x' \<subseteq> jvm_known_addrs t xcpfrs"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply simp
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto 4 3 simp add: check_def dest: exec_instr_known_addrs_new_thread)
done

lemma exec_instr_New_same_addr_same:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr ins P t h stk loc C M pc frs;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(cases ins)
apply(auto split: prod.split_asm split_if_asm)
apply(auto split: extCallRet.split_asm dest: red_external_aggr_New_same_addr_same)
done

lemma exec_New_same_addr_same:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec P t (xcp, h, frs); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto dest: exec_instr_New_same_addr_same)
done

lemma exec_1_d_New_same_addr_same:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(erule jvmd_NormalE)(rule exec_New_same_addr_same)

end



locale JVM_allocated_heap = allocated_heap +
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
  and P :: "'addr jvm_prog"

sublocale JVM_allocated_heap < JVM_heap
by(unfold_locales)

context JVM_allocated_heap begin

lemma exec_instr_allocated_mono:
  "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(cases i)(auto simp add: split_beta split: split_if_asm sum.split_asm intro: new_obj_allocated_mono' new_arr_allocated_mono' dest: heap_write_allocated_same red_external_aggr_allocated_mono del: subsetI)

lemma mexecd_allocated_mono:
  "mexecd P t (xcpfrs, h) ta (xcpfrs', h') \<Longrightarrow> allocated h \<subseteq> allocated h'"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto del: subsetI dest: exec_instr_allocated_mono)
done

lemma exec_instr_allocatedD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> allocated h' \<and> ad \<notin> allocated h"
apply(cases i)
apply(auto split: split_if_asm prod.split_asm dest: new_obj_allocatedD new_obj_allocated_fail new_arr_allocatedD red_external_aggr_allocatedD)
done

lemma mexecd_allocatedD:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> ad \<in> allocated h' \<and> ad \<notin> allocated h"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto del: subsetI dest: exec_instr_allocatedD)
done

lemma exec_instr_NewHeapElemD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; ad \<in> allocated h'; ad \<notin> allocated h \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
apply(cases i)
apply(auto 4 3 split: split_if_asm prod.split_asm sum.split_asm dest: new_obj_allocatedD new_arr_allocatedD new_obj_allocated_fail new_arr_allocated_fail heap_write_allocated_same red_external_aggr_NewHeapElemD)
done

lemma mexecd_NewHeapElemD:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); ad \<in> allocated h'; ad \<notin> allocated h \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto dest: exec_instr_NewHeapElemD)
done

lemma mexecd_allocated_multithreaded:
  "allocated_multithreaded addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length heap_write allocated JVM_final (mexecd P) P"
proof
  fix t x m ta x' m'
  assume "mexecd P t (x, m) ta (x', m')"
  thus "allocated m \<subseteq> allocated m'" by(rule mexecd_allocated_mono)
next
  fix x t m ta x' m' ad CTn
  assume "mexecd P t (x, m) ta (x', m')"
    and "NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> allocated m' \<and> ad \<notin> allocated m" by(rule mexecd_allocatedD)
next
  fix t x m ta x' m' ad
  assume "mexecd P t (x, m) ta (x', m')"
    and "ad \<in> allocated m'" "ad \<notin> allocated m"
  thus "\<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by(rule mexecd_NewHeapElemD)
next
  fix t x m ta x' m' i a CTn j CTn'
  assume "mexecd P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a CTn" "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a CTn'" "j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "i = j" by(auto dest: exec_1_d_New_same_addr_same simp add: split_beta)
qed

end

sublocale JVM_allocated_heap < execd_mthr!: allocated_multithreaded 
  addr2thread_id thread_id2addr 
  empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write allocated 
  JVM_final "mexecd P" 
  P
by(rule mexecd_allocated_multithreaded)

context JVM_allocated_heap begin

lemma mexecd_known_addrs: 
  assumes wf: "wf_prog wfmd P"
  and ok: "start_heap_ok"
  shows "known_addrs addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length heap_write allocated jvm_known_addrs JVM_final (mexecd P) P"
proof
  fix t x m ta x' m'
  assume "mexecd P t (x, m) ta (x', m')"
  thus "jvm_known_addrs t x' \<subseteq> jvm_known_addrs t x \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    by(rule exec_d_known_addrs_mono[OF ok])
next
  fix t x m ta x' m' t' x'' m''
  assume "mexecd P t (x, m) ta (x', m')"
    and "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  thus "jvm_known_addrs t' x'' \<subseteq> jvm_known_addrs t x" by(rule mexecd_known_addrs_new_thread)
next
  fix t x m ta x' m' ad al v
  assume "mexecd P t (x, m) ta (x', m')"
    and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> jvm_known_addrs t x" by(rule mexecd_known_addrs_ReadMem)
next
  fix t x m ta x' m' n ad al ad'
  assume "mexecd P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr ad')" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad' \<in> jvm_known_addrs t x \<or> ad' \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    by(rule mexecd_known_addrs_WriteMem)
next
  fix t x m ta x' m'
  assume "mexecd P t (x, m) ta (x', m')"
  thus "m \<unlhd> m'" by(auto simp add: split_beta intro: exec_1_d_hext)
qed

end

context JVM_heap begin

lemma exec_instr_read_typeable:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h \<turnstile> ad@al : T'"
using exec check read
proof(cases i)
  case ALoad
  with assms show ?thesis
    by(fastsimp simp add: split_beta is_Ref_def nat_less_iff word_sless_alt intro: addr_loc_type.intros split: split_if_asm)
next
  case (Getfield F D)
  with assms show ?thesis
    by(clarsimp simp add: split_beta is_Ref_def is_class_type_of_conv_class_type_of_Some[symmetric] split: split_if_asm)(blast intro: addr_loc_type.intros dest: has_visible_field has_field_mono)
next
  case (Invoke M n)
  with exec check read obtain a vs ta' va T
    where "(ta', va, h') \<in> red_external_aggr P t a M vs h"
    and "ReadMem ad al v \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
    and "is_native P (the (typeof_addr h a)) M"
    by(auto split: split_if_asm simp add: is_Ref_def)
  thus ?thesis by(rule red_external_aggr_read_mem_typeable)
qed(auto simp add: split_beta is_Ref_def split: split_if_asm)

lemma exec_1_d_read_typeable:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); 
     ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,h \<turnstile> ad@al : T'"
apply(erule jvmd_NormalE)
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto intro: exec_instr_read_typeable simp add: check_def)
done

end

sublocale JVM_heap_base < execd_mthr!: 
  if_multithreaded
    JVM_final
    "mexecd P"
    convert_RA
  for P
by(unfold_locales)

context JVM_heap_conf begin

lemma JVM_conf_read_heap_read_typed:
  "JVM_conf_read addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write hconf P"
proof -
  interpret conf!: heap_conf_read
    addr2thread_id thread_id2addr 
    empty_heap new_obj new_arr typeof_addr array_length "heap_read_typed P" heap_write hconf 
    P
    by(rule heap_conf_read_heap_read_typed)
  show ?thesis by(unfold_locales)
qed

lemma exec_instr_New_typeof_addrD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; 
     check_instr i P h stk loc C M pc frs; hconf h;
     NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a = Some (ty_of_htype x)"
apply(cases i)
apply(auto dest: new_obj_SomeD new_arr_SomeD split: prod.split_asm split_if_asm)
apply(auto split: extCallRet.split_asm dest: red_external_aggr_New_typeof_addrD)
done

lemma exec_1_d_New_typeof_addrD:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; hconf h \<rbrakk>
  \<Longrightarrow> typeof_addr h' a = Some (ty_of_htype x)"
apply(erule jvmd_NormalE)
apply(cases "xcp")
apply(auto dest: exec_instr_New_typeof_addrD simp add: check_def)
done

lemma exec_instr_ta_seq_consist_typeable:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and sc: "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and vs_conf: "vs_conf P h vs"
  and hconf: "hconf h"
  shows "(ta, xcp', h', frs') \<in> JVM_heap_base.exec_instr addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write i P t h stk loc C M pc frs" (is ?thesis1)
  and "vs_conf P h' (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" (is ?thesis2)
proof -
  note [simp] = JVM_heap_base.exec_instr.simps
    and [split] = split_if_asm prod.split_asm sum.split_asm
    and [split del] = split_if
  from assms have "?thesis1 \<and> ?thesis2"
  proof(cases i)
    case New with assms show ?thesis by(auto dest: hext_new_obj vs_conf_new_obj intro: vs_conf_hext)
  next
    case NewArray with assms show ?thesis by(auto dest: hext_new_arr vs_conf_new_arr intro: vs_conf_hext cong: if_cong)
  next
    case ALoad with assms show ?thesis
      by(auto 4 3 intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)
  next
    case Getfield with assms show ?thesis
      by(auto 4 3 intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)
  next
    case Invoke with assms show ?thesis
      by(fastsimp dest: red_external_aggr_ta_seq_consist_typeable)
  next
    case AStore
    { 
      assume "hd (tl (tl stk)) \<noteq> Null"
        and "\<not> the_Intg (hd (tl stk))  <s 0"
        and "\<not> int (array_length h (the_Addr (hd (tl (tl stk))))) \<le> sint (the_Intg (hd (tl stk)))"
        and "P \<turnstile> the (typeof\<^bsub>h\<^esub> (hd stk)) \<le> the_Array (the (typeof_addr h (the_Addr (hd (tl (tl stk))))))"
      moreover hence "nat (sint (the_Intg (hd (tl stk)))) < array_length h (the_Addr (hd (tl (tl stk))))"
        by(auto simp add: not_le nat_less_iff word_sle_def word_sless_def not_less)
      with assms AStore have "nat (sint (the_Intg (hd (tl stk)))) < array_length h' (the_Addr (hd (tl (tl stk))))"
        by(auto dest!: hext_arrD hext_heap_write)
      ultimately have "\<exists>T. P,h' \<turnstile> the_Addr (hd (tl (tl stk)))@ACell (nat (sint (the_Intg (hd (tl stk))))) : T \<and> P,h' \<turnstile> hd stk :\<le> T"
        using assms AStore
        by(auto 4 4 simp add: is_Ref_def conf_def dest!: hext_heap_write intro!: addr_loc_type.intros intro: typeof_addr_hext_mono type_of_hext_type_of) }
    thus ?thesis using assms AStore
      by(auto intro!: vs_confI)(blast intro: addr_loc_type_hext_mono conf_hext dest: hext_heap_write vs_confD)+
  next
    case Putfield
    show ?thesis using assms Putfield
      by(auto intro!: vs_confI dest!: hext_heap_write)(blast intro: addr_loc_type.intros addr_loc_type_hext_mono typeof_addr_hext_mono is_class_type_of_conv_class_type_of_Some[THEN iffD2] has_field_mono[OF has_visible_field] conf_hext dest: vs_confD)+
  qed(auto)
  thus ?thesis1 ?thesis2 by(rule conjunct1 conjunct2)+
qed

lemma mexecd_ta_seq_consist_typeable:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, stk) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>));
    vs_conf P h vs; hconf h \<rbrakk>
  \<Longrightarrow> JVM_heap_base.exec_1_d addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write P t (Normal (xcp, h, stk)) ta (Normal (xcp', h', frs')) \<and> vs_conf P h' (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
apply(erule jvmd_NormalE)
apply(cases xcp)
apply(auto intro!: JVM_heap_base.exec_1_d.intros simp add: JVM_heap_base.exec_d_def check_def JVM_heap_base.exec.simps intro: exec_instr_ta_seq_consist_typeable)
done

lemma exec_instr_NewArr_lengthD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs;
     check_instr i P h stk loc C M pc frs;
     NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; hconf h \<rbrakk>
  \<Longrightarrow> array_length h' a = n"
apply(cases i)
apply(auto dest: new_arr_SomeD split: prod.split_asm split_if_asm)
apply(auto split: extCallRet.split_asm dest: red_external_aggr_NewArr_lengthD)
done

lemma exec_1_d_NewArr_lengthD:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; hconf h \<rbrakk>
  \<Longrightarrow> array_length h' a = n"
apply(erule jvmd_NormalE)
apply(cases xcp)
apply(auto dest: exec_instr_NewArr_lengthD simp add: check_def)
done

end

locale JVM_allocated_heap_conf = 
  JVM_heap_conf 
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf
    P
  +
  JVM_allocated_heap 
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
  and P :: "'addr jvm_prog"
begin

lemma mexecd_known_addrs_typing:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and ok: "start_heap_ok"
  shows "known_addrs_typing addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length heap_write allocated jvm_known_addrs JVM_final (mexecd P) (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>) P"
proof -
  from wf obtain wf_md where "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  then
  interpret known_addrs
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" P
    using ok by(rule mexecd_known_addrs)
  
  show ?thesis
  proof
    fix s t ta s' vs
    assume exec: "P \<turnstile> s -t\<triangleright>ta\<rightarrow>\<^bsub>jvmd\<^esub> s'"
      and ts_ok: "correct_state_ts \<Phi> (thr s) (shr s)"
      and vs: "vs_conf P (shr s) vs"
      and sc: "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
    let ?mexecd = "JVM_heap_base.mexecd addr2thread_id thread_id2addr empty_heap new_obj new_arr typeof_addr array_length (heap_read_typed P) heap_write P"
    have "lifting_wf JVM_final ?mexecd (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"
      by(intro JVM_conf_read.lifting_wf_correct_state_d JVM_conf_read_heap_read_typed wf)
    moreover
    from exec have "multithreaded_base.redT JVM_final ?mexecd convert_RA s (t, ta) s'"
    proof(cases)
      case redT_normal thus ?thesis using sc vs ts_ok
        by(auto simp add: split_beta correct_state_def intro!: multithreaded_base.redT.redT_normal dest!: ts_okD dest: mexecd_ta_seq_consist_typeable)
    qed(blast intro: multithreaded_base.redT.intros)
    ultimately have "correct_state_ts \<Phi> (thr s') (shr s')" (is ?thesis1)
      using ts_ok by(rule lifting_wf.redT_preserves)
    moreover from exec have "vs_conf P (shr s') (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" (is ?thesis2)
    proof(cases)
      case redT_normal thus ?thesis using sc vs ts_ok
        by(auto dest!: ts_okD simp add: correct_state_def dest: mexecd_ta_seq_consist_typeable)
    next
      case (redT_acquire x ln l)
      have "mrw_values P vs (map NormalAction (convert_RA ln :: ('addr, 'thread_id) obs_event list)) = vs"
        by(auto simp add: convert_RA_not_write fun_eq_iff intro!: mrw_values_no_write_unchanged)
      thus ?thesis using vs redT_acquire by auto
    qed
    ultimately show "?thesis1 \<and> ?thesis2" ..
  next
    fix t x m ta x' m' ad al v
    assume "mexecd P t (x, m) ta (x', m')"
      and "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x m"
      and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "\<exists>T. P,m \<turnstile> ad@al : T"
      by(auto simp add: correct_state_def split_beta dest: exec_1_d_read_typeable)
  next
    fix t x m ta x' m' ad C
    assume "mexecd P t (x, m) ta (x', m')"
      and "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x m"
      and "NewObj ad C \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "typeof_addr m' ad = \<lfloor>Class C\<rfloor>"
      by(auto dest: exec_1_d_New_typeof_addrD[where x="Class_type C"] simp add: split_beta correct_state_def)
  next
    fix t x m ta x' m' ad T n
    assume "mexecd P t (x, m) ta (x', m')"
      and "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x m"
      and "NewArr ad T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "typeof_addr m' ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor> \<and> array_length m' ad = n"
      by(auto dest: exec_1_d_New_typeof_addrD[where x="Array_type T n"] exec_1_d_NewArr_lengthD simp add: split_beta correct_state_def)
  qed
qed

lemma executions_sc:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and ok: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=(pns, body) in D"
  and vs1: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and vs2: "\<Union>ka_Val ` set vs \<subseteq> set start_addrs"
  shows
  "executions_sc (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` execd_mthr.if.\<E> P (init_fin_lift_state status (JVM_start_state P C M vs))) P"
  (is "executions_sc ?E P")
proof -
  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>" P
    using wf ok by(rule mexecd_known_addrs_typing)
  
  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  hence "wf_syscls P" by(rule wf_prog_wf_syscls) 
  thus ?thesis using ok
  proof(rule executions_sc)
    from correct_jvm_state_initial[OF wf ok sees vs1]
    show "correct_state_ts \<Phi> (thr (JVM_start_state P C M vs)) start_heap"
      by(simp add: correct_jvm_state_def start_state_def split_beta)
  next
    from start_state_vs_conf[OF wf']
    show "vs_conf P start_heap (mrw_values P empty (map NormalAction start_heap_obs))"
      by(simp add: start_state_def lift_start_obs_def o_def)
  next
    show "jvm_known_addrs start_tid ((\<lambda>(mxs, mxl0, b) vs. (None, [([], Null # vs @ replicate mxl0 undefined_value, fst (method P C M), M, 0)])) (snd (snd (snd (method P C M)))) vs) \<subseteq> allocated start_heap"
      using vs2
      by(auto simp add: split_beta start_addrs_allocated jvm_known_addrs_def intro: start_tid_start_addrs[OF `wf_syscls P` ok])
  qed
qed

end

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

context JVM_progress begin

lemma exec_instr_cut_and_update:
  assumes hrt: "heap_read_typeable"
  and vs: "vs_conf P (shr s) vs"
  and dom_vs: "(\<Union>a \<in> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs). {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs"
  and hconf: "hconf (shr s)"
  and exec_i: "(ta, xcp', h', frs') \<in> exec_instr i P t (shr s) stk loc C M pc frs"
  and check: "check_instr i P (shr s) stk loc C M pc frs"
  and aok: "execd_mthr.if.actions_ok s t ta"
  shows "\<exists>ta' xcp'' h'' frs''. (ta', xcp'', h'', frs'') \<in> exec_instr i P t (shr s) stk loc C M pc frs \<and>
           execd_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
using exec_i aok
proof(cases i)
  case MExit thus ?thesis using exec_i aok
    by(simp add: split_beta split: split_if_asm)(safe, fastsimp, fastsimp intro!: disjI2 del: disjCI)
next
  case ALoad[simp]
  let ?a = "the_Addr (hd (tl stk))"
  let ?i = "the_Intg (hd stk)"
  show ?thesis
  proof(cases "hd (tl stk) = Null \<or> ?i <s 0 \<or> int (array_length (shr s) ?a) \<le> sint ?i")
    case True
    with exec_i aok show ?thesis by(auto split: split_if_asm)
  next
    case False
    hence Null: "hd (tl stk) \<noteq> Null"
      and bounds: "0 <=s ?i" "sint ?i < int (array_length (shr s) ?a)" by auto
    from Null check obtain a T 
      where a: "length stk > 1" "hd (tl stk) = Addr a"
      and type: "typeof_addr (shr s) ?a = \<lfloor>Array T\<rfloor>" by(auto simp add: is_Ref_def)
    from bounds have "nat (sint ?i) < array_length (shr s) ?a"
      by(simp add: word_sle_def nat_less_iff)
    with type have adal: "P,shr s \<turnstile> ?a@ACell (nat (sint ?i)) : T"
      by(rule addr_loc_type.intros)
    moreover from a have "a \<in> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs)"
      by(cases stk)(auto simp add: jvm_known_addrs_def neq_Nil_conv)
    ultimately obtain b v' where bv': "vs (?a, ACell (nat (sint ?i))) = \<lfloor>(v', b)\<rfloor>"
      using subsetD[OF dom_vs, where c="(?a, ACell (nat (sint ?i)))"] a by fastsimp
    with adal vs have "P,shr s \<turnstile> v' :\<le> T" by(auto dest: vs_confD addr_loc_type_fun)
    with hrt adal have "heap_read (shr s) ?a (ACell (nat (sint ?i))) v'"
      using hconf by(rule heap_read_typeableD)
    with bv' type bounds Null aok exec_i show ?thesis by fastsimp
  qed
next
  case (Getfield F D)[simp]
  let ?a = "the_Addr (hd stk)"
  show ?thesis
  proof(cases "hd stk = Null")
    case True
    with exec_i aok show ?thesis by(auto)
  next
    case False
    with check obtain U T fm C' a
      where sees: "P \<turnstile> D sees F:T (fm) in D"
      and type: "typeof_addr (shr s) ?a = \<lfloor>U\<rfloor>" 
      and U: "class_type_of U = Some C'"
      and sub: "P \<turnstile> C' \<preceq>\<^sup>* D" 
      and a: "hd stk = Addr a" "length stk > 0" by(auto simp add: is_Ref_def)
    from has_visible_field[OF sees] sub
    have "P \<turnstile> C' has F:T (fm) in D" by(rule has_field_mono)
    with type U have adal: "P,shr s \<turnstile> ?a@CField D F : T"
      unfolding is_class_type_of_conv_class_type_of_Some[symmetric]
      by(rule addr_loc_type.intros)
    moreover from a have "a \<in> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs)"
      by(auto simp add: jvm_known_addrs_def neq_Nil_conv)
    ultimately obtain b v' where bv': "vs (?a, CField D F) = \<lfloor>(v', b)\<rfloor>"
      using subsetD[OF dom_vs, where c="(?a, CField D F)"] a by fastsimp
    with adal vs have "P,shr s \<turnstile> v' :\<le> T" by(auto dest: vs_confD addr_loc_type_fun)
    with hrt adal have "heap_read (shr s) ?a (CField D F) v'"
      using hconf by(rule heap_read_typeableD)
    with bv' aok False exec_i show ?thesis by(auto)
  qed
next
  case (Invoke M n)[simp]
  let ?a = "the_Addr (stk ! n)"
  let ?vs = "rev (take n stk)"
  show ?thesis
  proof(cases "stk ! n = Null \<or> \<not> is_native P (the (typeof_addr (shr s) ?a)) M")
    case True with exec_i aok show ?thesis by auto
  next
    case False
    hence Null: "stk ! n \<noteq> Null" 
      and iec: "is_native P (the (typeof_addr (shr s) ?a)) M" by simp_all
    with check obtain a T U
      where a: "stk ! n = Addr a" "n < length stk"
      and type: "typeof_addr (shr s) ?a = \<lfloor>T\<rfloor>"
      and extwt: "P,shr s \<turnstile> ?a\<bullet>M(?vs) : U" by(auto simp add: is_Ref_def)
    from Null iec type exec_i obtain ta' va
      where red: "(ta', va, h') \<in> red_external_aggr P t ?a M ?vs (shr s)"
      and ta: "ta = extTA2JVM P ta'" by(fastsimp)
    from aok ta have aok': "execd_mthr.if.actions_ok s t ta'" by simp
    from dom_vs a have "{(a, al) |al. \<exists>T. P,shr s \<turnstile> a@al : T} \<subseteq> dom vs"
      by(auto simp add: jvm_known_addrs_def in_set_conv_nth iff del: domIff del: subsetI dest!: UNION_subsetD[where a="Addr a" and A="set stk"])
    from red_external_aggr_cut_and_update[OF hrt vs this red[unfolded a the_Addr.simps] iec[unfolded a the_Addr.simps] aok' hconf]
    obtain ta'' va'' h'' where "(ta'', va'', h'') \<in> red_external_aggr P t ?a M ?vs (shr s)"
      and "execd_mthr.if.actions_ok s t ta''"
      and "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
      and "eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) vs"
      using a by auto
    thus ?thesis using Null iec ta by(cases va'') force+
  qed
qed(auto simp add: split_beta split: split_if_asm)

lemma exec_1_d_cut_and_update:
  assumes hrt: "heap_read_typeable"
  and vs: "vs_conf P (shr s) vs"
  and ka: "(\<Union>a \<in> jvm_known_addrs t (xcp, frs). {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs"
  and exec: "P,t \<turnstile> Normal (xcp, shr s, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and aok: "execd_mthr.if.actions_ok s t ta"
  and hconf: "hconf (shr s)"
  shows "\<exists>ta' xcp'' h'' frs''. P,t \<turnstile> Normal (xcp, shr s, frs) -ta'-jvmd\<rightarrow> Normal (xcp'', h'', frs'') \<and>
           execd_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
using assms
apply -
apply(erule jvmd_NormalE)
apply(cases "(P, t, xcp, shr s, frs)" rule: exec.cases)
  apply simp
 prefer 2
 apply(fastsimp simp add: exec_1_d.simps exec_d_def split_beta)
apply clarsimp
apply(drule (4) exec_instr_cut_and_update)
  apply(clarsimp simp add: check_def has_method_def)
 apply simp
apply(clarsimp simp add: exec_1_d.simps exec_d_def)
done

end

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

locale JVM_allocated_progress = 
  JVM_progress
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf
    P
  +
  JVM_allocated_heap_conf
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
  and P :: "'addr jvm_prog"
begin

lemma cut_and_update:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and hrt: "heap_read_typeable"
  and ok: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and ka: "\<Union>ka_Val ` set vs \<subseteq> set start_addrs"
  shows "execd_mthr.if.cut_and_update (init_fin_lift_state status (JVM_start_state P C M vs)) 
                                      (mrw_values P empty (map snd (lift_start_obs start_tid start_heap_obs)))"
  (is "execd_mthr.if.cut_and_update ?start_state ?start_vs")
proof(rule execd_mthr.if.cut_and_updateI)

  fix ttas s' t x ta x' m'
  assume \<tau>Red: "execd_mthr.if.RedT P ?start_state ttas s'"
    and sc: "ta_seq_consist P ?start_vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ts't: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "execd_mthr.init_fin P t (x, shr s') ta (x', m')"
    and aok: "execd_mthr.if.actions_ok s' t ta"

  let ?conv = "\<lambda>ttas. concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  let ?vs' = "mrw_values P ?start_vs (?conv ttas)"
  let ?wt_ok = "init_fin_lift (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"

  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>"
    using wf ok by(rule mexecd_known_addrs_typing)

  from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)


  from correct_jvm_state_initial[OF wf ok sees conf]
  have "correct_state_ts \<Phi> (thr (JVM_start_state P C M vs)) start_heap"
    by(simp add: correct_jvm_state_def start_state_def split_beta)
  hence ts_ok_start: "ts_ok ?wt_ok (thr ?start_state) (shr ?start_state)"
    unfolding ts_ok_init_fin_lift_init_fin_lift_state by(simp add: start_state_def split_beta)

  have sc': "ta_seq_consist P ?start_vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of ttas))))"
    using sc by(simp add: lmap_lconcat lmap_compose[symmetric] o_def split_def lconcat_llist_of[symmetric] del: lmap_compose)
  from start_state_vs_conf[OF wf']
  have vs_conf_start: "vs_conf P (shr ?start_state) ?start_vs"
    by(simp add:init_fin_lift_state_conv_simps start_state_def split_beta)
  with \<tau>Red ts_ok_start sc
  have wt': "ts_ok ?wt_ok (thr s') (shr s')"
    and vs': "vs_conf P (shr s') ?vs'" by(rule if_RedT_ta_seq_consist_invar)+

  note \<tau>Red sc
  moreover
  have "(\<Union>a\<in>if.known_addrs_state ?start_state \<union> mrw_addrs ?start_vs. {(a, al) |al. \<exists>T. P,shr ?start_state \<turnstile> a@al : T})
 \<subseteq> dom ?start_vs"
    using sees ka mrw_addrs_start_heap_obs[of empty] start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf'] ok]
    by(auto simp add: start_state_def if.known_addrs_state_def if.known_addrs_thr_def split_beta init_fin_lift_state_def lift_start_obs_def o_def jvm_known_addrs_def split: split_if_asm)(force dest: start_addrs_dom_mrw_values[OF wf_prog_wf_syscls[OF wf']])+
  moreover have "if.known_addrs_state ?start_state \<union> mrw_addrs ?start_vs \<subseteq> dom (typeof_addr (shr ?start_state))"
    using sees ka dom_typeof_addr_start_heap[OF wf_prog_wf_syscls[OF wf']]
      start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf'] ok]
      mrw_addrs_lift_start_heap_obs[where vs="empty"]
    by(auto simp add: start_state_def if.known_addrs_state_def if.known_addrs_thr_def jvm_known_addrs_def split_beta init_fin_lift_state_def split: split_if_asm dest: subsetD) blast+
  ultimately have dom_vs: "(\<Union>a\<in>if.known_addrs_state s' \<union> mrw_addrs ?vs'. {(a, al) |al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom ?vs'"
    and "if.known_addrs_state s' \<union> mrw_addrs ?vs' \<subseteq> dom (typeof_addr (shr s'))"
    using ts_ok_start vs_conf_start by(rule if_RedT_known_addrs_mrw_addrs_dom_vs)+

  show "\<exists>ta' x'' m''. execd_mthr.init_fin P t (x, shr s') ta' (x'', m'') \<and>
                      execd_mthr.if.actions_ok s' t ta' \<and>
                      ta_seq_consist P ?vs' (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                      eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs'"
  proof(cases "ta_seq_consist P ?vs' (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)")
    case True
    hence "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ?vs'"
      by(rule ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
    with red aok True show ?thesis by blast
  next
    case False
    with red obtain xcp frs xcp' frs' ta'
      where x: "x = (Running, xcp, frs)" and x': "x' = (Running, xcp', frs')"
      and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
      and red': "P,t \<turnstile> Normal (xcp, shr s', frs) -ta'-jvmd\<rightarrow> Normal (xcp', m', frs')"
      by cases fastsimp+

    from ts't wt' x have hconf: "hconf (shr s')" by(auto dest!: ts_okD simp add: correct_state_def)

    have aok': "execd_mthr.if.actions_ok s' t ta'" using aok unfolding ta by simp

    from dom_vs ts't x
    have "(\<Union>a\<in>jvm_known_addrs t (xcp, frs) \<union> mrw_addrs ?vs'. {(a, al) |al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom ?vs'"
      by -(rule UN_least, erule UNION_subsetD, clarify, rule if.known_addrs_stateI, auto)
    hence "(\<Union>a\<in>jvm_known_addrs t (xcp, frs). {(a, al) |al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom ?vs'" by blast

    from exec_1_d_cut_and_update[OF hrt vs' this red' aok' hconf]
    obtain ta'' xcp'' frs'' h''
      where red'': "P,t \<turnstile> Normal (xcp, shr s', frs) -ta''-jvmd\<rightarrow> Normal (xcp'', h'', frs'')"
      and aok'': "execd_mthr.if.actions_ok s' t ta''"
      and sc'': "ta_seq_consist P ?vs' (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
      and eq'': "eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) ?vs'"
      by blast

    let ?x' = "(Running, xcp'', frs'')"
    let ?ta' = "convert_TA_initial (convert_obs_initial ta'')"
    from red'' have "execd_mthr.init_fin P t (x, shr s') ?ta' (?x', h'')"
      unfolding x by -(rule execd_mthr.init_fin.NormalAction, simp)
    moreover from aok'' have "execd_mthr.if.actions_ok s' t ?ta'" by simp
    moreover from sc'' have "ta_seq_consist P ?vs' (llist_of \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub>)" by simp
    moreover from eq'' have "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> ?vs'" unfolding ta by simp
    ultimately show ?thesis by blast
  qed
qed

lemma JVM_executions:
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"
  and hrt: "heap_read_typeable"
  and ok: "start_heap_ok"
  and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  and ka: "\<Union>ka_Val ` set vs \<subseteq> set start_addrs"
shows "executions (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
                   execd_mthr.if.\<E> P (init_fin_lift_state status (JVM_start_state P C M vs))) P"
proof -
  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>"
    using wf ok by(rule mexecd_known_addrs_typing)

  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  hence "wf_syscls P" by(rule wf_prog_wf_syscls)
  with cut_and_update[OF wf hrt ok sees conf ka]
  show ?thesis using ok
  proof(rule executions)
    from correct_jvm_state_initial[OF wf ok sees conf]
    show "correct_state_ts \<Phi> (thr (JVM_start_state P C M vs)) start_heap"
      by(simp add: correct_jvm_state_def start_state_def split_beta)
  next
    from start_state_vs_conf[OF wf']
    show "vs_conf P start_heap (mrw_values P empty (map NormalAction start_heap_obs))"
      by(simp add: start_state_def lift_start_obs_def o_def)
  next
    show "jvm_known_addrs start_tid ((\<lambda>(mxs, mxl0, b) vs. (None, [([], Null # vs @ replicate mxl0 undefined_value, fst (method P C M), M, 0)])) (snd (snd (snd (method P C M)))) vs) \<subseteq> allocated start_heap"
      using ka
      by(auto simp add: split_beta start_addrs_allocated jvm_known_addrs_def intro: start_tid_start_addrs[OF `wf_syscls P` ok])
  qed
qed

end

text {*
  One could now also prove that the aggressive JVM satisfies @{term executions}.
  The key would be that @{text welltyped_commute} also holds for @{term "ta_seq_consist"} prefixes from start.
*}

end