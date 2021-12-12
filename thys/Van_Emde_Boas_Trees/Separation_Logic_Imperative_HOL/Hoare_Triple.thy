section \<open>Hoare-Triples\<close>
theory Hoare_Triple
imports Assertions
begin

text \<open>In this theory, we define Hoare-Triples, which are our basic tool
  for specifying properties of Imperative HOL programs.\<close>

subsection \<open>Definition\<close>

text \<open>Analyze the heap before and after executing a command, to add
  the allocated addresses to the covered address range.\<close>
definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"

lemma new_addr_refl[simp]: "new_addrs h as h = as"
  unfolding new_addrs_def by auto

text \<open>
  Apart from correctness of the program wrt. the pre- and post condition,
  a Hoare-triple also encodes some well-formedness conditions of the command:
  The command must not change addresses outside the address range of the 
  precondition, and it must not decrease the heap limit. 

  Note that we do not require that the command only reads from heap locations
  inside the precondition's address range, as this condition would be quite
  complicated to express with the heap model of Imperative/HOL, and is not 
  necessary in our formalization of partial heaps, that always contain the 
  information for all addresses.
\<close>

definition hoare_triple 
  :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>")
  where
  "<P> c <Q> \<equiv> \<forall>h as. (h,as)\<Turnstile>P \<longrightarrow> (\<exists>r h' t. execute c h = Some (r,h',t) 
  \<and> (let as'=new_addrs h as h' in  
      (h',as')\<Turnstile>Q r \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
    \<and> lim h \<le> lim h'))"
    
    
text \<open>Sanity checking theorems for Hoare-Triples\<close>  
lemma
  assumes "<P> c <Q>"
  assumes "(h,as)\<Turnstile>P"
  shows hoare_triple_success: "success c h" 
    and hoare_triple_effect: "\<exists>h' r t. effect c h h' r t \<and> (h',new_addrs h as h')\<Turnstile>Q r"
  using assms 
  unfolding hoare_triple_def success_def effect_def
  apply -
  apply (auto simp: Let_def) apply fastforce+ done

    
lemma hoare_tripleE:
  assumes "<P> c <Q>"
  assumes "(h,as)\<Turnstile>P"
  obtains r h' t where
    "execute c h = Some (r,h',t)"
    "(h',new_addrs h as h')\<Turnstile>Q r"
    "relH ({a . a<lim h \<and> a\<notin>as}) h h'"
    "lim h \<le> lim h'"
  using assms 
  unfolding hoare_triple_def Let_def
  by blast
  
lemma hoare_tripleI[intro?]:
  assumes "\<And>h as. (h,as)\<Turnstile>P \<Longrightarrow> (\<exists>r h' t. 
    execute c h = Some (r,h',t) 
  \<and> (h',new_addrs h as h') \<Turnstile> Q r
  \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
  \<and> lim h \<le> lim h'
  )"
  shows "<P> c <Q>"
  using assms unfolding hoare_triple_def Let_def 
  by blast
  
    
  
(*lemma hoare_tripleD:
  fixes h h' as as' r
  assumes "<P> c <Q>"
  assumes "(h,as)\<Turnstile>P"
  assumes "execute c h = Some (r,h')"
  defines "as'\<equiv>new_addrs h as h'"
  shows "(h',as')\<Turnstile>Q r"
  and "relH ({a . a<lim h \<and> a\<notin>as}) h h'"
  and "lim h \<le> lim h'"
  using assms 
  unfolding hoare_triple_def as'_def 
  apply (auto simp: Let_def)
*)  

text \<open>For garbage-collected languages, specifications usually allow for some
  arbitrary heap parts in the postcondition. The following abbreviation defines
  a handy shortcut notation for such specifications.\<close>
abbreviation hoare_triple' 
  :: "assn \<Rightarrow> 'r Heap \<Rightarrow> ('r \<Rightarrow> assn) \<Rightarrow> bool" ("<_> _ <_>\<^sub>t") 
  where "<P> c <Q>\<^sub>t \<equiv> <P> c <\<lambda>r. Q r * true>"

subsection \<open>Rules\<close>
text \<open>
  In this section, we provide a set of rules to prove Hoare-Triples correct.
\<close>
subsubsection \<open>Basic Rules\<close>


lemma hoare_triple_preI: 
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> <P> c <Q>"
  shows "<P> c <Q>"
  using assms
  unfolding hoare_triple_def
  by auto

lemma frame_rule: 
  assumes A: "<P> c <Q>"
  shows "<P*R> c <\<lambda>x. Q x * R>"
  unfolding hoare_triple_def Let_def
  apply (intro allI impI)
proof -
  fix h as
  assume "(h,as) \<Turnstile> P * R"
  then obtain as1 as2 where [simp]: "as=as1\<union>as2" and DJ: "as1\<inter>as2={}"
    and M1: "(h,as1)\<Turnstile>P" and M2: "(h,as2)\<Turnstile>R"
    by (auto simp: mod_star_conv)

    
  from hoare_tripleE[OF A M1] obtain r h' t where
    EX: "execute c h = Some (r, h',t)" 
    and MDL: "(h', new_addrs h as1 h') \<Turnstile> Q r" 
    and RH1: "relH {a. a < lim h \<and> a \<notin> as1} h h'"
    and "lim h \<le> lim h'"
    .
  
  have "{a. a < lim h \<and> a \<notin> as} \<subseteq> {a. a < lim h \<and> a \<notin> as1}"
    by auto
  then have "relH {a. a < lim h \<and> a \<notin> as} h h'" using RH1
    by (blast intro: relH_subset)
      
  have DJN: "new_addrs h as1 h' \<inter> as2 = {}"
    using DJ models_in_range[OF M2]
    by (auto simp: in_range.simps new_addrs_def)
  moreover have "as2 \<subseteq> {a. a < lim h \<and> a \<notin> as1}" 
    using DJ models_in_range[OF M2]
    by (auto simp: in_range.simps)
  hence "relH as2 h h'" using RH1
    by (blast intro: relH_subset)
  with M2 have "(h', as2)\<Turnstile>R"
    by (metis mem_Collect_eq Rep_assn  
      proper_iff relH_in_rangeI(2))
  moreover have "new_addrs h as h' 
    = new_addrs h as1 h' \<union> as2"
    by (auto simp: new_addrs_def)
  ultimately have 
    M: "(h', new_addrs h as h') \<Turnstile> Q r * R"
    using MDL
    unfolding times_assn_def
    apply (simp add: Abs_assn_inverse)
    apply blast
    done
    
  show "\<exists>r h' t.
          execute c h = Some (r, h',t) \<and>
          (h', new_addrs h as h') \<Turnstile> Q r * R \<and> relH {a. a < lim h \<and> a \<notin> as} h h' \<and> lim h \<le> lim h'"  
    apply (rule exI[where x=r])          
    apply (rule exI[where x=h'])          
    apply (rule exI[where x=t])
    apply safe
    apply fact
    apply fact
    apply fact
    apply fact
    done
qed    
   

lemma false_rule[simp, intro!]: "<false> c <Q>"
  unfolding hoare_triple_def by simp

  
lemma cons_rule:
  assumes CPRE: "P \<Longrightarrow>\<^sub>A P'"
  assumes CPOST: "\<And>x. Q x \<Longrightarrow>\<^sub>A Q' x"
  assumes R: "<P'> c <Q>"
  shows "<P> c <Q'>"
  using assms  
  unfolding hoare_triple_def Let_def
  using entailsD by blast
  

lemmas cons_pre_rule = cons_rule[OF _ ent_refl]
lemmas cons_post_rule = cons_rule[OF ent_refl, rotated]

lemma cons_rulet: "\<lbrakk>P\<Longrightarrow>\<^sub>tP'; \<And>x. Q x \<Longrightarrow>\<^sub>t Q' x; <P'> c <Q>\<^sub>t \<rbrakk> \<Longrightarrow> <P> c <Q'>\<^sub>t"
  unfolding entailst_def
  apply (rule cons_pre_rule)
  apply assumption
  apply (rule cons_post_rule)
  apply (erule frame_rule)
  by (simp add: enttD enttI)  

lemmas cons_pre_rulet = cons_rulet[OF _ entt_refl]
lemmas cons_post_rulet = cons_rulet[OF entt_refl, rotated]

  
  
lemma norm_pre_ex_rule:
  assumes A: "\<And>x. <P x> f <Q>"
  shows "<\<exists>\<^sub>Ax. P x> f <Q>"
  unfolding hoare_triple_def Let_def
  apply (intro allI impI, elim conjE mod_exE)
  using assms hoare_tripleE by fastforce

lemma norm_pre_pure_iff[simp]:
  "<P*\<up>b> f <Q> \<longleftrightarrow> (b \<longrightarrow> <P> f <Q>)"
  unfolding hoare_triple_def Let_def
  by auto

lemma norm_pre_pure_iff_sng[simp]:
  "<\<up>b> f <Q> \<longleftrightarrow> (b \<longrightarrow> <emp> f <Q>)"
  using norm_pre_pure_iff[where P=emp]
  by simp

lemma norm_pre_pure_rule1: 
  "\<lbrakk>b \<Longrightarrow> <P> f <Q>\<rbrakk> \<Longrightarrow> <P*\<up>b> f <Q>" by simp

lemma norm_pre_pure_rule2:
  "\<lbrakk> b \<Longrightarrow> <emp> f <Q> \<rbrakk> \<Longrightarrow> <\<up>b> f <Q>" by simp

lemmas norm_pre_pure_rule = norm_pre_pure_rule1 norm_pre_pure_rule2

lemma post_exI_rule: "<P> c <\<lambda>r. Q r x> \<Longrightarrow> <P> c <\<lambda>r. \<exists>\<^sub>Ax. Q r x>"
  by (blast intro: cons_post_rule ent_ex_postI ent_refl)


  
subsubsection \<open>Rules for Time Commands\<close>
lemma wait_rule: "<emp> wait n <\<lambda>_. emp>"
  apply rule
  apply (simp add: execute_simps)
  by (simp add: in_range.simps relH_refl)
    
lemma wait_bind_decon: "<P> m <Q> \<Longrightarrow> <P> do {wait n; m} <Q>"
  apply rule
  apply (auto elim!: hoare_tripleE simp: execute_simps)
  done
  
 
  
subsubsection \<open>Rules for Atomic Commands\<close>
lemma ref_rule:
  "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>"
  unfolding one_assn_def sngr_assn_def hoare_triple_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (simp add: execute_simps)
  apply (auto 
    simp: new_addrs_def Ref_Time.alloc_def Let_def
    Ref_Time.set_def Ref_Time.get_def relH_def in_range.simps)
  done

lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>"
  unfolding hoare_triple_def sngr_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (simp add: execute_simps)
  apply (auto elim: simp add: relH_refl in_range.simps new_addrs_def)
  done

lemma update_rule:
  "<p \<mapsto>\<^sub>r y> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>"
  unfolding hoare_triple_def sngr_assn_def
  apply (simp add: execute_simps)
  apply (auto elim!: 
    simp: Let_def Abs_assn_inverse new_addrs_def in_range.simps 
    intro!: relH_set_ref)
  done

lemma update_wp_rule:
  "<r \<mapsto>\<^sub>r y * ((r \<mapsto>\<^sub>r x) -* (Q ()))> r := x <Q>"
  apply (rule cons_post_rule)
  apply (rule frame_rule[OF update_rule[where p=r and x=x], 
    where R="((r \<mapsto>\<^sub>r x) -* (Q ()))"])
  apply (rule ent_trans)
  apply (rule ent_mp)
  by simp

lemma new_rule:
  "<emp> Array_Time.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (simp add: execute_simps)
  apply (auto 
    simp: Let_def new_addrs_def Array_Time.get_def Array_Time.set_def Array_Time.alloc_def
      relH_def in_range.simps
  )
  done

lemma make_rule: "<emp> Array_Time.make n f <\<lambda>r. r \<mapsto>\<^sub>a (map f [0 ..< n])>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (simp add: execute_simps)
  apply (auto 
    simp: Let_def new_addrs_def Array_Time.get_def Array_Time.set_def Array_Time.alloc_def
      relH_def in_range.simps
  )
  done
    
lemma of_list_rule: "<emp> Array_Time.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (simp add: execute_simps)
  apply (auto 
    simp: Let_def new_addrs_def Array_Time.get_def Array_Time.set_def Array_Time.alloc_def
      relH_def in_range.simps
  )
  by (simp add: map_idI)

lemma length_rule:
  "<a \<mapsto>\<^sub>a xs> Array_Time.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (simp add: execute_simps)
  apply (auto 
    simp: Let_def new_addrs_def Array_Time.get_def Array_Time.set_def Array_Time.alloc_def
      relH_def in_range.simps Array_Time.length_def
  )
  done

text \<open>Note that the Boolean expression is placed at meta level and not 
  inside the precondition. This makes frame inference simpler.\<close>
lemma nth_rule:
  "\<lbrakk>i < length xs\<rbrakk> \<Longrightarrow> <a \<mapsto>\<^sub>a xs> Array_Time.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    simp: Let_def new_addrs_def Array_Time.get_def Array_Time.set_def Array_Time.alloc_def
      relH_def in_range.simps Array_Time.length_def
      execute_simps
  )
  done

lemma upd_rule:
  "\<lbrakk>i < length xs\<rbrakk> \<Longrightarrow> 
  <a \<mapsto>\<^sub>a xs> 
  Array_Time.upd i x a 
  <\<lambda>r. (a \<mapsto>\<^sub>a (list_update xs i x)) * \<up>(r = a)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    simp: Let_def new_addrs_def Array_Time.get_def Array_Time.set_def Array_Time.alloc_def
      relH_def in_range.simps Array_Time.length_def Array_Time.update_def comp_def
      execute_simps
  )
  done

lemma freeze_rule:
  "<a \<mapsto>\<^sub>a xs> Array_Time.freeze a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs)>"
  unfolding hoare_triple_def snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    simp: Let_def new_addrs_def Array_Time.get_def Array_Time.set_def Array_Time.alloc_def
      relH_def in_range.simps Array_Time.length_def Array_Time.update_def
      execute_simps
  )
  done
  
lemma return_wp_rule:
  "<Q x> return x <Q>"
  unfolding hoare_triple_def Let_def
  apply (auto simp: execute_simps)
  apply (rule relH_refl)
  apply (simp add: in_range.simps)
  done

lemma return_sp_rule:
  "<P> return x <\<lambda>r. P * \<up>(r = x)>"
  unfolding hoare_triple_def Let_def
  apply (simp add: Abs_assn_inverse)
  apply (auto intro!: relH_refl intro: models_in_range simp: execute_simps)
  apply (simp add: in_range.simps)
  done

lemma raise_iff: 
  "<P> raise s <Q> \<longleftrightarrow> P = false"
  unfolding hoare_triple_def Let_def
  apply (rule iffI)
  apply (unfold bot_assn_def) []
  apply rule
  apply (auto simp add: execute_simps) []

  apply (auto simp add: execute_simps) []
  done

lemma raise_rule: "<false> raise s <Q>"
  by (simp add: raise_iff)

subsubsection \<open>Rules for Composed Commands\<close>
lemma bind_rule: 
  assumes T1: "<P> f <R>"
  assumes T2: "\<And>x. <R x> g x <Q>"
  shows "<P> bind f g <Q>"
proof  
  fix h as
  assume "(h, as) \<Turnstile> P"
  
  from hoare_tripleE[OF T1 this] obtain rf h' t' where
    EX_F: "execute f h = Some (rf, h',t')" 
    and POST_F: "(h', new_addrs h as h') \<Turnstile> R rf"
    and RH_F: "relH {a. a < lim h \<and> a \<notin> as} h h'"
    and LIM_F: "lim h \<le> lim h'"
    .
    
  from hoare_tripleE[OF T2 POST_F] obtain rg h'' t'' where
    EX_G: "execute (g rf) h' = Some (rg, h'',t'')"
    and POST_G: "(h'', new_addrs h' (new_addrs h as h') h'') \<Turnstile> Q rg"
    and RH_G: "relH {a. a < lim h' \<and> a \<notin> new_addrs h as h'} h' h''"
    and LIM_G: "lim h' \<le> lim h''"
    .
  
  have  
    "new_addrs 
      h' 
      (new_addrs h as h') 
      h''
    = new_addrs h as h''" 
    using LIM_F LIM_G
    by (auto simp add: new_addrs_def)
  with POST_G have
    "(h'', new_addrs h as h'') \<Turnstile> Q rg"
    by simp

  note RH_F
  also have "relH {a. a < lim h \<and> a \<notin> as} h' h''"
    apply (rule relH_subset[OF RH_G])
    using LIM_F LIM_G
    by (auto simp: new_addrs_def)
  finally have "relH {a. a < lim h \<and> a \<notin> as} h h''" .

  note LIM_F
  also note LIM_G
  finally have "lim h \<le> lim h''" .
    
  
  show "\<exists>r h' t'.
          execute (f \<bind> g) h = Some (r, h',t') \<and>
          (h', new_addrs h as h') \<Turnstile> Q r \<and> relH {a. a < lim h \<and> a \<notin> as} h h' \<and> lim h \<le> lim h'"
    apply (intro exI conjI)
    apply (simp add: EX_F EX_G execute_simps; fail)
    apply fact+
    done   
qed  

lemma bind_rule' :
  assumes T1: "\<And> r. <P> f <\<lambda> r. (P * R r) >"
  assumes T2: "\<And>x. <R x * P> g x <Q>"
  shows "<P> bind f g <Q>" 
  by (metis (no_types, lifting) T1 T2 ab_semigroup_mult_class.mult.commute bind_rule)


lemma if_rule:
  assumes  "b \<Longrightarrow> <P> f <Q>"
  assumes  "\<not>b \<Longrightarrow> <P> g <Q>"
  shows "<P> if b then f else g <Q>"
  using assms by auto

lemma if_rule_split:
  assumes  B: "b \<Longrightarrow> <P> f <Q1>"
  assumes  NB: "\<not>b \<Longrightarrow> <P> g <Q2>"
  assumes M: "\<And>x. (Q1 x * \<up>b) \<or>\<^sub>A (Q2 x * \<up>(\<not>b)) \<Longrightarrow>\<^sub>A Q x"
  shows "<P> if b then f else g <Q>"
  apply (cases b)
  apply simp_all
  apply (rule cons_post_rule)
  apply (erule B)
  apply (rule ent_trans[OF _ ent_disjI1[OF M]])
  apply simp

  apply (rule cons_post_rule)
  apply (erule NB)
  apply (rule ent_trans[OF _ ent_disjI2[OF M]])
  apply simp
  done

lemma split_rule: 
  assumes P: "<P> c <R>"
  assumes Q: "<Q> c <R>"
  shows "<P \<or>\<^sub>A Q> c <R>"
  apply rule
  using assms
  apply (auto elim!: hoare_tripleE)
  done

lemmas decon_if_split = if_rule_split split_rule
  \<comment> \<open>Use with care: Complete splitting of if statements\<close>

lemma case_prod_rule: 
  "(\<And>a b. x = (a, b) \<Longrightarrow> <P> f a b <Q>) \<Longrightarrow> <P> case x of (a, b) \<Rightarrow> f a b <Q>"
  by (auto split: prod.split)

lemma case_list_rule:
  "\<lbrakk> l=[] \<Longrightarrow> <P> fn <Q>; \<And>x xs. l=x#xs \<Longrightarrow> <P> fc x xs <Q> \<rbrakk> \<Longrightarrow> 
  <P> case_list fn fc l <Q>"
  by (auto split: list.split)

lemma case_option_rule:
  "\<lbrakk> v=None \<Longrightarrow> <P> fn <Q>; \<And>x. v=Some x \<Longrightarrow> <P> fs x <Q> \<rbrakk> 
  \<Longrightarrow> <P> case_option fn fs v <Q>"
  by (auto split: option.split)

lemma case_sum_rule:
  "\<lbrakk> \<And>x. v=Inl x \<Longrightarrow> <P> fl x <Q>; 
     \<And>x. v=Inr x \<Longrightarrow> <P> fr x <Q> \<rbrakk> 
  \<Longrightarrow> <P> case_sum fl fr v <Q>"
  by (auto split: sum.split)

lemma let_rule: "(\<And>x. x = t \<Longrightarrow> <P> f x <Q>) \<Longrightarrow> <P> Let t f <Q>"
  by (auto)

end
