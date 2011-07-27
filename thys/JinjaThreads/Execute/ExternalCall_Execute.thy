theory ExternalCall_Execute imports
  "../Common/ExternalCall"
  "Cset_without_equal"
begin

abbreviation (input) cset_sup :: "'a Cset.set \<Rightarrow> 'a Cset.set \<Rightarrow> 'a Cset.set"
where "cset_sup \<equiv> semilattice_sup_class.sup"

(* Use locale context to obtain a Cset. prefix: should use proper name spaces instead *)
locale Cset begin

definition undefined :: "'a Cset.set"
where [simp]: "undefined = Cset.Set HOL.undefined"

definition Undefined :: "unit \<Rightarrow> 'a Cset.set"
where [code]: "Undefined _ = Cset.Set HOL.undefined"

lemma undefined_code:
  "undefined = Undefined ()"
by(simp add: Undefined_def)

end

declare
  Cset.undefined_def [simp]
  Cset.undefined_code [code_inline]

code_abort Cset.Undefined

section {* Translated versions of external calls for the JVM *}

locale heap_execute = addr_base +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id" 
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr" 
  fixes empty_heap :: "'heap" 
  and new_obj :: "'heap \<Rightarrow> String.literal \<Rightarrow> 'heap \<times> 'addr option" 
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> 'heap \<times> 'addr option" 
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<Rightarrow> ty option" 
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat" 
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val Cset.set" 
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap Cset.set"

sublocale heap_execute < execute!: heap_base
  addr2thread_id thread_id2addr 
  empty_heap new_obj new_arr typeof_addr array_length
  "\<lambda>h a ad v. v \<in> Cset.member (heap_read h a ad)" "\<lambda>h a ad v h'. h' \<in> Cset.member (heap_write h a ad v)"
.

context heap_execute begin

definition heap_copy_loc :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'heap \<Rightarrow> (('addr, 'thread_id) obs_event list \<times> 'heap) Cset.set"
where
  "heap_copy_loc a a' al h = Cset.Set (\<lambda>(obs, h'). execute.heap_copy_loc a a' al h obs h')"

lemma member_heap_copy_loc [simp]:
  "member (heap_copy_loc a a' al h) = {(obs, h'). execute.heap_copy_loc a a' al h obs h'}"
by(auto simp add: heap_copy_loc_def mem_def)

lemma heap_copy_loc_code:
  "heap_copy_loc a a' al h =
   (do {
      v \<leftarrow> heap_read h a al;
      h' \<leftarrow> heap_write h a' al v;
      Cset.single ([ReadMem a al v, WriteMem a' al v], h')
   })"
apply(auto simp add: Cset.set_eq_iff)
apply(auto simp add: elim!: execute.heap_copy_loc.cases intro: execute.heap_copy_loc.intros)
done

definition heap_copies :: "'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc list \<Rightarrow> 'heap \<Rightarrow> (('addr, 'thread_id) obs_event list \<times> 'heap) Cset.set"
where "heap_copies a a' al h = Cset.Set (\<lambda>(obs, h'). execute.heap_copies a a' al h obs h')"

lemma member_heap_copies [simp]:
  "member (heap_copies a a' al h) = {(obs, h'). execute.heap_copies a a' al h obs h'}"
by(auto simp add: heap_copies_def mem_def)

lemma heap_copies_code:
  shows heap_copies_Nil: 
  "heap_copies a a' [] h = Cset.single ([], h)"
  and heap_copies_Cons:
  "heap_copies a a' (al # als) h =
  (do {
     (ob, h') \<leftarrow> heap_copy_loc a a' al h;
     (obs, h'') \<leftarrow> heap_copies a a' als h';
     Cset.single (ob @ obs, h'')
  })"
by(auto simp add: Cset.set_eq_iff elim!: execute.heap_copies_cases intro: execute.heap_copies.intros)

definition heap_clone :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> ('heap \<times> (('addr, 'thread_id) obs_event list \<times> 'addr) option) Cset.set"
where "heap_clone P h a = Cset.Set {(h', obsa). execute.heap_clone P h a h' obsa}"

lemma member_heap_clone [simp]: 
  "member (heap_clone P h a) = {(h', obsa). execute.heap_clone P h a h' obsa}"
by(simp add: heap_clone_def)

lemma heap_clone_code:
  "heap_clone P h a =
  (case typeof_addr h a of
    \<lfloor>Class C\<rfloor> \<Rightarrow> 
    (case new_obj h C of
       (h', None) \<Rightarrow> Cset.single (h', None)
     | (h', Some a') \<Rightarrow> do {
          FDTs \<leftarrow> Cset.of_pred (Fields_i_i_o P C);
          (obs, h'') \<leftarrow> heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs) h';
          Cset.single (h'', \<lfloor>(NewObj a' C # obs, a')\<rfloor>)
       })
  | \<lfloor>Array T\<rfloor> \<Rightarrow>
    (let n = array_length h a
     in case new_arr h T n of
          (h', None) \<Rightarrow> Cset.single (h', None)
        | (h', \<lfloor>a'\<rfloor>) \<Rightarrow> do {
             FDTs \<leftarrow> Cset.of_pred (Fields_i_i_o P Object);
             (obs, h'') \<leftarrow> heap_copies a a' (map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]) h';
             Cset.single (h'', \<lfloor>(NewArr a' T n # obs, a')\<rfloor>)
           })
  | _ \<Rightarrow> Cset.empty)"
by(auto simp add: Cset.set_eq_iff split: ty.splits elim!: execute.heap_clone.cases intro: execute.heap_clone.intros simp add: eval_Fields_conv split_beta Pair_fst_snd_eq)

definition red_external_aggr :: 
  "'m prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'heap \<Rightarrow> 
  (('addr, 'thread_id, 'heap) external_thread_action \<times> 'addr extCallRet \<times> 'heap) Cset.set"
where
  "red_external_aggr P t a M vs h = Cset.Set (execute.red_external_aggr P t a M vs h)"

lemma member_red_external_aggr [simp]:
  "member (red_external_aggr P t a M vs h) = execute.red_external_aggr P t a M vs h"
by(simp add: red_external_aggr_def)

lemma red_external_aggr_code:
  "red_external_aggr P t a M vs h =
   (if M = wait then
      let ad_t = thread_id2addr t
      in Cset.set
         [(\<lbrace>Unlock\<rightarrow>a, Lock\<rightarrow>a, IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, execute.RetEXC InterruptedException, h),
          (\<lbrace>Suspend a, Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a, IsInterrupted t False, SyncUnlock a\<rbrace>, RetStaySame, h),
          (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, execute.RetEXC IllegalMonitorState, h),
          (\<lbrace>Notified\<rbrace>, RetVal Unit, h),
          (\<lbrace>WokenUp, ClearInterrupt t, ObsInterrupted t\<rbrace>, execute.RetEXC InterruptedException, h)]
    else if M = notify then
       Cset.set [(\<lbrace>Notify a, Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>, RetVal Unit, h),
                 (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, execute.RetEXC IllegalMonitorState, h)]
    else if M = notifyAll then 
       Cset.set [(\<lbrace>NotifyAll a, Unlock\<rightarrow>a, Lock\<rightarrow>a \<rbrace>, RetVal Unit, h),
                 (\<lbrace>UnlockFail\<rightarrow>a\<rbrace>, execute.RetEXC IllegalMonitorState, h)]
    else if M = clone then
       do {
         (h', obsa) \<leftarrow> heap_clone P h a;
         Cset.single 
           (case obsa of None \<Rightarrow> (\<epsilon>, execute.RetEXC OutOfMemory, h')
             | Some (obs, a') \<Rightarrow> ((\<lambda>\<^isup>f [], [], [], [], [], obs), RetVal (Addr a'), h'))
       }
    else if M = hashcode then Cset.single ((\<epsilon>, RetVal (Intg (word_of_int (hash_addr a))), h))
    else if M = print then Cset.single (\<lbrace>ExternalCall a M vs Unit\<rbrace>, RetVal Unit, h)
    else if M = currentThread then Cset.single (\<epsilon>, RetVal (Addr (thread_id2addr t)), h)
    else if M = interrupted then 
      Cset.set [(\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, RetVal (Bool True), h),
                (\<lbrace>IsInterrupted t False\<rbrace>, RetVal (Bool False), h)]
    else if M = yield then Cset.single (\<lbrace>Yield\<rbrace>, RetVal Unit, h)
    else
      let T = the (typeof_addr h a)
      in if P \<turnstile> T \<le> Class Thread then
        let t_a = addr2thread_id a 
        in if M = start then 
             Cset.set [(\<lbrace>NewThread t_a (the_Class T, run, a) h, ThreadStart t_a\<rbrace>, RetVal Unit, h),
                       (\<lbrace>ThreadExists t_a True\<rbrace>, execute.RetEXC IllegalThreadState, h)]
           else if M = join then
             Cset.set [(\<lbrace>Join t_a, IsInterrupted t False, ThreadJoin t_a\<rbrace>, RetVal Unit, h),
                       (\<lbrace>IsInterrupted t True, ClearInterrupt t, ObsInterrupted t\<rbrace>, execute.RetEXC InterruptedException, h)]
           else if M = interrupt then
             Cset.set [(\<lbrace>ThreadExists t_a True, WakeUp t_a, Interrupt t_a, ObsInterrupt t_a\<rbrace>, RetVal Unit, h),
                       (\<lbrace>ThreadExists t_a False\<rbrace>, RetVal Unit, h)]
           else if M = isInterrupted then
             Cset.set [(\<lbrace>IsInterrupted t_a False\<rbrace>, RetVal (Bool False), h),
                       (\<lbrace>IsInterrupted t_a True, ObsInterrupted t_a\<rbrace>, RetVal (Bool True), h)]
         else Cset.undefined
    else Cset.undefined)"
by(fastsimp simp add: execute.red_external_aggr_def Cset.set_eq_iff split_beta Collect_conv_UN_singleton split: val.split)

end

lemmas [code] =
  heap_execute.heap_copy_loc_code
  heap_execute.heap_copies_code
  heap_execute.heap_clone_code
  heap_execute.red_external_aggr_code

end