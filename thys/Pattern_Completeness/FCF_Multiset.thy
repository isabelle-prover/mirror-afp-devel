theory FCF_Multiset
  imports 
    FCF_Set
    Pattern_Completeness_Multiset
begin

fun depth_gterm :: "('f,'v)term \<Rightarrow> nat" where
  "depth_gterm (Fun f ts) = Suc (max_list (map depth_gterm ts))" 
| "depth_gterm _ = Suc 0" 

lemma depth_gterm_arg: "t \<in> set ts \<Longrightarrow> depth_gterm t < depth_gterm (Fun f ts)" 
  unfolding less_eq_Suc_le by (auto intro: max_list)


(* **************************************** 
     MULTISET LEVEL 
   *****************************************)

type_synonym('f,'s)simple_match_problem_ms = "('f,nat \<times> 's)term multiset multiset"

type_synonym('f,'s)simple_pat_problem_ms = "('f,'s)simple_match_problem_ms multiset"

abbreviation mset2 :: "('f,'s)simple_match_problem_ms \<Rightarrow> ('f,'s)simple_match_problem" where
  "mset2 \<equiv> image set_mset o set_mset" 

abbreviation mset3 :: "('f,'s)simple_pat_problem_ms \<Rightarrow> ('f,'s)simple_pat_problem" where
  "mset3 \<equiv> image mset2 o set_mset" 

lemma mset2_simps: 
  "mset2 (add_mset eq mp) = insert (set_mset eq) (mset2 mp)"
  "set_mset (add_mset t eq) = insert t (set_mset eq)" 
  "set_mset {#} = {}" 
  "mset2 (mp1 + mp2) = mset2 mp1 \<union> mset2 mp2" 
  "mset3 (add_mset mp p) = insert (mset2 mp) (mset3 p)"
  by auto

context pattern_completeness_context
begin
 
inductive smp_step_ms :: "('f,'s)simple_match_problem_ms \<Rightarrow> ('f,'s)simple_match_problem_ms \<Rightarrow> bool"
  (infix \<open>\<rightarrow>\<^sub>s\<^sub>s\<close> 50) where
  smp_dup: "add_mset (add_mset t (add_mset t eqc)) mp \<rightarrow>\<^sub>s\<^sub>s add_mset (add_mset t eqc) mp" 
| smp_singleton: "add_mset {# t #} mp \<rightarrow>\<^sub>s\<^sub>s mp" 
| smp_triv_sort: "t : \<iota> in \<T>(C,\<V>) \<Longrightarrow> cd_sort \<iota> = 1 \<Longrightarrow> add_mset (add_mset t eq) mp \<rightarrow>\<^sub>s\<^sub>s mp" 
| smp_decomp: "(\<And> t. t \<in> set_mset eqc \<Longrightarrow> root t = Some (f,n))
    \<Longrightarrow> eqcn = {#{#args t ! i. t \<in># eqc#}. i \<in># mset [0..<n]#}
    \<Longrightarrow> (\<And> eq. eq \<in> set_mset eqcn \<Longrightarrow> UNIQ (\<T>(C,\<V>) ` set_mset eq))
    \<Longrightarrow> add_mset eqc mp \<rightarrow>\<^sub>s\<^sub>s eqcn + mp"  

inductive smp_fail_ms :: "('f,'s)simple_match_problem_ms \<Rightarrow> bool" where
  smp_clash: "Conflict_Clash s t \<Longrightarrow> 
      s \<in> eqc \<Longrightarrow> t \<in> eqc \<Longrightarrow> eqc \<in> mset2 mp \<Longrightarrow> smp_fail_ms mp" 
| smp_decomp_fail: "(\<And> t. t \<in> set_mset eqc \<Longrightarrow> root t = Some (f,n))
    \<Longrightarrow> i < n 
    \<Longrightarrow> \<not> UNIQ (\<T>(C,\<V>) ` (\<lambda> t. args t ! i) ` set_mset eqc)
    \<Longrightarrow> smp_fail_ms (add_mset eqc mp)" 
 
inductive spp_step_ms :: "('f,'s)simple_pat_problem_ms \<Rightarrow> ('f,'s)simple_pat_problem_ms multiset \<Rightarrow> bool"
  (infix \<open>\<Rightarrow>\<^sub>s\<^sub>s\<close> 50) where
  spp_solved: "add_mset {#} p \<Rightarrow>\<^sub>s\<^sub>s {#}" 
| spp_simp: "mp \<rightarrow>\<^sub>s\<^sub>s mp' \<Longrightarrow> add_mset mp p \<Rightarrow>\<^sub>s\<^sub>s {#add_mset mp' p#}" 
| spp_delete: "smp_fail_ms mp \<Longrightarrow> add_mset mp p \<Rightarrow>\<^sub>s\<^sub>s {#p#}"
| spp_delete_large_sort: "
    (\<And> i. i \<le> (n :: nat) \<Longrightarrow> snd (x i) = \<iota> \<and> eq i \<in># mp i \<and> Var (x i) \<noteq> t i \<and> {Var (x i), t i} \<subseteq> set_mset (eq i)) \<Longrightarrow>
    x ` {0..n} \<inter> tvars_spat (mset3 p) = {} \<Longrightarrow>
    (card (t ` {0..n}) < card_of_sort C \<iota>) \<Longrightarrow>
    p + mset (map mp [0..< Suc n]) \<Rightarrow>\<^sub>s\<^sub>s {# p #}" 
| spp_inst: "{#{#Var x, t#}#} \<in># p 
   \<Longrightarrow> is_Fun t 
   \<Longrightarrow> fst ` tvars_spat (mset3 p) \<inter> {n..<n + m} = {}
   \<Longrightarrow> p \<Rightarrow>\<^sub>s\<^sub>s mset (map (\<lambda> \<tau>. image_mset (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>))) p) (\<tau>s_list n x))" 
| spp_split: "mp = add_mset (add_mset s (add_mset t eqc)) mp'
   \<Longrightarrow> is_Var s \<noteq> is_Var t \<Longrightarrow> eqc \<noteq> {#} \<or> mp' \<noteq> {#}
   \<Longrightarrow> add_mset mp p \<Rightarrow>\<^sub>s\<^sub>s {#add_mset {# {# s, t #} #} p, add_mset (add_mset (add_mset s eqc) mp') p#}" 
end

context pattern_completeness_context_with_assms
begin

lemma smp_fail_ms: assumes "smp_fail_ms mp"
  and "finite_constructor_form_pat (insert (mset2 mp) p)" 
shows "finite_constructor_form_pat p" 
  "simple_pat_complete C SS (insert (mset2 mp) p) \<longleftrightarrow> simple_pat_complete C SS p"
proof -
  show "finite_constructor_form_pat p" using assms(2) unfolding finite_constructor_form_pat_def by auto
  show "simple_pat_complete C SS (insert (mset2 mp) p) \<longleftrightarrow> simple_pat_complete C SS p"
    using assms
  proof (induct mp rule: smp_fail_ms.induct)
    case *: (smp_clash s t eqc mp)
    from *(4) obtain eq mp' where mp: "mp = add_mset eq mp'" and eqc: "eqc = set_mset eq"
      by (metis comp_apply image_iff mset_add)
    from eqc *(2-3) have "set_mset eq = {s,t} \<union> eqc" by auto
    from eliminate_clash_spp(1)[OF *(5)[unfolded mset2_simps mp] refl refl this *(1)]
    show ?case unfolding mp mset2_simps .
  next
    case *: (smp_decomp_fail eqc f n i mp)
    from *(2-3) have "(\<forall>eq\<in>{{args t ! i |. t \<in> set_mset eqc} |. i \<in> {0..<n}}. UNIQ (\<T>(C,\<V>) ` eq)) = False" 
      by auto
    from decompose_spp(1)[OF *(4)[unfolded mset2_simps] refl refl *(1) refl refl, unfolded this if_False]
    show ?case unfolding mset2_simps by auto
  qed
qed
  

lemma smp_step_ms: assumes "mp \<rightarrow>\<^sub>s\<^sub>s mp'"
  and "finite_constructor_form_pat (insert (mset2 mp) p)" 
shows "finite_constructor_form_pat (insert (mset2 mp') p)" 
  "simple_pat_complete C SS (insert (mset2 mp) p) \<longleftrightarrow> simple_pat_complete C SS (insert (mset2 mp') p)" 
proof (atomize(full), insert assms, induct mp mp' rule: smp_step_ms.induct)
  case (smp_singleton t mp)
  from eliminate_uniq_spp[OF this[unfolded mset2_simps] refl refl refl]
  show ?case by (auto simp: Uniq_def)
next
  case *: (smp_triv_sort t \<iota> eq mp)
  show ?case 
  proof (intro conjI)
    show "finite_constructor_form_pat (insert (mset2 mp) p)" 
      using * unfolding finite_constructor_form_pat_def finite_constructor_form_mp_def by auto
    show "simple_pat_complete C SS (insert (mset2 (add_mset (add_mset t eq) mp)) p) =
      simple_pat_complete C SS (insert (mset2 mp) p)" 
      unfolding simple_pat_complete_def bex_simps
    proof (rule all_cong, intro disj_cong refl)
      fix \<sigma>
      assume sig: "\<sigma> :\<^sub>s \<V> |` SS \<rightarrow> \<T>(C)" 
      from * obtain \<tau> where typed: "u \<in> insert t (set_mset eq) \<Longrightarrow> u : \<tau> in \<T>(C,\<V> |` SS)" for u 
        unfolding finite_constructor_form_pat_def finite_constructor_form_mp_def by auto
      from typed_S_eq[OF this *(1)] have tau: "\<tau> = \<iota>" by auto
      from typed_imp_S[OF typed, of t] tau have "\<iota> \<in> S" by auto
      from cd[OF this] * k1
      have card: "card_of_sort C \<iota> = 1" by auto
      have "UNIQ_subst \<sigma> (insert t (set_mset eq))" unfolding UNIQ_subst_alt_def
      proof (intro allI impI, goal_cases)
        case (1 u v)
        {
          fix w
          assume "w \<in> {u,v}" 
          with 1 typed tau have "w : \<iota> in \<T>(C,\<V> |` SS)" by auto
          with sig have "w \<cdot> \<sigma> : \<iota> in \<T>(C)" by (rule subst_hastype)
        }
        hence "u \<cdot> \<sigma> : \<iota> in \<T>(C)" "v \<cdot> \<sigma> : \<iota> in \<T>(C)" by auto
        with card
        show "u \<cdot> \<sigma> = v \<cdot> \<sigma>" unfolding card_of_sort_def card_eq_1_iff by auto
      qed
      thus "simple_match_complete_wrt \<sigma> (mset2 (add_mset (add_mset t eq) mp)) =
         simple_match_complete_wrt \<sigma> (mset2 mp)" 
        unfolding simple_match_complete_wrt_def by simp
    qed
  qed
next
  case *: (smp_decomp eqc f n eqcn mp)
  have eq: "(\<forall>eq\<in>mset2 eqcn. UNIQ (\<T>(C,\<V>) ` eq)) = True" 
    using *(2-3) by auto
  define N where "N = {0..<n}" 
  have fin: "finite N" unfolding N_def by auto
  have "mset2 eqcn = {{args t ! i |. t \<in> set_mset eqc} |. i \<in> {0..<n}}" 
    unfolding *(2) mset_upt N_def[symmetric] 
    apply (subst (2) finite_set_mset_mset_set[OF fin, symmetric])
    by (metis (no_types, lifting) comp_apply image_cong image_image multiset.set_map)
  from decompose_spp[OF *(4)[unfolded mset2_simps] refl refl *(1) this, unfolded eq if_True, OF _ refl]
  show ?case unfolding mset2_simps by auto
qed auto

lemma spp_step_ms_size: assumes "p \<Rightarrow>\<^sub>s\<^sub>s Q" and "q \<in># Q" 
  shows "size q \<le> size p" 
  using assms by (cases, auto)
  

lemma spp_step_ms: assumes "p \<Rightarrow>\<^sub>s\<^sub>s Pn"
  and "finite_constructor_form_pat (mset3 p)" 
shows "Ball (set_mset Pn) (\<lambda> p'. finite_constructor_form_pat (mset3 p'))" 
  "simple_pat_complete C SS (mset3 p) \<longleftrightarrow> Ball (set_mset Pn) (\<lambda> p'. simple_pat_complete C SS (mset3 p'))"
proof (atomize(full), insert assms, induct p Pn rule: spp_step_ms.induct)
  case (spp_solved p)  
  show ?case unfolding mset2_simps using detect_sat_spp by auto
next
  case *: (spp_simp mp mp' p)
  from smp_step_ms[OF *(1) *(2)[unfolded mset2_simps]]
  show ?case unfolding mset2_simps by auto
next
  case *: (spp_delete mp p)
  from smp_fail_ms[OF *(1) *(2)[unfolded mset2_simps]]
  show ?case unfolding mset2_simps by auto
next
  case *: (spp_inst x t p n)
  from mset_add[OF *(1)] have mem: "{{Var x,t}} \<in> mset3 p" by fastforce
  define p' where "p' = mset3 p" 
  have id: "{(`) ((`) (\<lambda>t. t \<cdot> \<tau>)) ` mset3 p |. \<tau> \<in> \<tau>s n x} = mset3 ` {image_mset (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>))) p |. \<tau> \<in> \<tau>s n x}" 
    unfolding image_comp o_def image_mset.comp set_image_mset by auto
  from mem have "x \<in> tvars_spat (mset3 p)" unfolding p'_def[symmetric] 
    by (auto intro!: bexI[of _ "{{Var x, t}}"])
  from instantiate_spp[OF *(4,3) this refl]
  show ?case unfolding id using \<tau>s_list by auto
next
  case *: (spp_split mp s t eqc mp' p)
  have "insert s (insert t (set_mset eqc)) = {s, t} \<union> set_mset eqc" by auto
  from separate_var_fun_spp_single[OF *(4)[unfolded mset2_simps *(1)] refl refl this refl]
  show ?case unfolding mset2_simps *(1) by auto
next
  case *: (spp_delete_large_sort n x \<iota> eq mp t p)
  have "mset3 (p + mset (map mp [0..<Suc n])) = mset3 p \<union> (mset2 o mp) ` set [0..< Suc n]" 
    by auto
  also have "set [0..< Suc n] = {0..n}" by auto
  finally have id: "mset3 (p + mset (map mp [0..<Suc n])) = mset3 p \<union> (mset2 \<circ> mp) ` {0..n} " by auto
  have main: "simple_pat_complete C SS (mset3 (p + mset (map mp [0..<Suc n]))) = 
     simple_pat_complete C SS (mset3 p)" unfolding id
    apply (rule eliminate_large_sort[OF _ *(2,3), of "set_mset o eq"])
    subgoal for i using *(1)[of i] by auto
    subgoal using *(4) unfolding id by (auto simp: finite_constructor_form_pat_def)
    done
  show ?case unfolding main using *(4) by (auto simp: finite_constructor_form_pat_def)
qed

lemma finite_tvars_spat_mset3: "finite (tvars_spat (mset3 p))" 
  by (intro finite_Union; fastforce)  

lemma finite_tvars_smp_mset2: "finite (tvars_smp (mset2 mp))" 
  by (intro finite_Union; fastforce)  

lemma normal_form_spp_step_fvf: assumes "finite_constructor_form_pat (mset3 p)" 
  and "\<nexists> P. p \<Rightarrow>\<^sub>s\<^sub>s P \<and> P \<noteq> {#}" 
  and mp: "mp \<in> mset3 p" 
  and eqc: "eqc \<in> mp"
  and t: "t \<in> eqc" 
shows "is_Var t" 
proof (rule ccontr)
  assume f: "is_Fun t"  
  from mp obtain mp' where mp': "mp' \<in> set_mset p" and mp: "mp = mset2 mp'" by auto
  from eqc[unfolded mp] obtain eqc' where eqc': "eqc' \<in> set_mset mp'" and eqc: "eqc = set_mset eqc'" by auto
  from t[unfolded eqc] obtain eqc2 where id1: "eqc' = add_mset t eqc2" by (rule mset_add)
  from eqc' obtain mp2 where id2: "mp' = add_mset eqc' mp2" by (rule mset_add)
  from mp' obtain p2 where id3: "p = add_mset mp' p2" by (rule mset_add)
  have p: "p = add_mset (add_mset (add_mset t eqc2) mp2) p2" unfolding id1 id2 id3 ..
  with assms have contra: "add_mset (add_mset (add_mset t eqc2) mp2) p2 \<Rightarrow>\<^sub>s\<^sub>s P \<Longrightarrow> P \<noteq> {#} \<Longrightarrow> False" for P by auto
  from assms(1)[unfolded finite_constructor_form_pat_def p] 
  have fin: "finite_constructor_form_mp (mset2 (add_mset (add_mset t eqc2) mp2))" by auto
  show False
  proof (cases "eqc2 = {#}")
    case True
    show False  
      apply (rule contra)
      apply (unfold True)
      by (rule spp_simp, rule smp_singleton, auto)
  next
    case ne: False   
    show False
    proof (cases "\<exists> s \<in> set_mset eqc2. is_Var s")
      case True
      then obtain s eqc3 where "eqc2 = add_mset s eqc3" and "is_Var s" by (metis mset_add)
      then obtain x where eqc: "add_mset t eqc2 = add_mset (Var x) (add_mset t eqc3)" by (cases s, auto)
      from fin[unfolded eqc finite_constructor_form_mp_def] obtain \<iota> 
        where "Var x : \<iota> in \<T>(C,\<V> |` SS)" by auto
      hence xS: "snd x \<in> S" unfolding hastype_def by (auto simp: restrict_map_def split: if_splits)
      show False
      proof (cases "eqc3 = {#} \<and> mp2 = {#}")
        case True
        hence True: "eqc3 = {#}" "mp2 = {#}" by auto
        define names where "names = fst ` \<Union> (\<Union> (\<Union> ((`) ((`) vars) ` insert (insert {Var x, t} (mset2 {#})) (mset3 p2))))" 
        define n where "n = Max names" 
        have id: "mset3 (add_mset {#{#Var x, t#}#} p2) = 
             insert (insert {Var x, t} (mset2 {#})) (mset3 p2)" by auto
        have "names = fst ` tvars_spat (mset3 p)" unfolding p eqc True names_def by simp
        also have "finite \<dots>" using finite_tvars_spat_mset3[of p] by blast
        finally have names: "\<And> k. k \<in> names \<Longrightarrow> k \<le> n" unfolding n_def by auto
        from not_empty_sort[OF xS, unfolded empty_sort_def]
        obtain t where "t : snd x in \<T>(C)" by auto 
        then obtain f ss where "f : ss \<rightarrow> snd x in C" 
          by (induct, auto)
        hence "set (Cl (snd x)) \<noteq> {}" unfolding Cl by auto
        hence Cl: "Cl (snd x) \<noteq> []" by auto
        show False 
          apply (rule contra)
          apply (unfold eqc, unfold True)
          apply (rule spp_inst[OF _ f, of x _ "Suc n"])
           apply force
          apply (unfold id)
           apply (unfold names_def[symmetric])
           apply (insert names, fastforce)
          apply (insert Cl, auto simp: \<tau>s_list_def)
          done
      next
        case False
        hence diff: "eqc3 \<noteq> {#} \<or> mp2 \<noteq> {#}" by auto
        from contra[OF spp_split[OF _ _ diff], unfolded eqc True, OF refl] f
        show ?thesis by auto
      qed
    next
      case False
      hence funs: "\<And> s. s \<in># eqc2 \<Longrightarrow> is_Fun s" by auto
      show False
      proof (cases "\<exists> s \<in># eqc2. root s \<noteq> root t")
        case True
        then obtain s eqc3 where eqc2: "eqc2 = add_mset s eqc3" and diff: "root s \<noteq> root t" 
          by (meson mset_add)
        from funs[of s] eqc2 diff f obtain f g where rt: "root t = Some f" "root s = Some g" and diff: "f \<noteq> g" 
          by (cases s; cases t; auto)
        hence conf: "Conflict_Clash s t" by (cases s; cases t; auto simp: conflicts.simps)
        show False 
          apply (rule contra)
          apply (unfold eqc2)
          apply (rule spp_delete)
          apply (rule smp_clash[OF conf, of "insert t (insert s (set_mset eqc3))"])
          by auto
      next
        case False
        from f obtain f n where "root t = Some (f,n)" by (cases t, auto)
        with False have rt: "\<And> s. s \<in># add_mset t eqc2 \<Longrightarrow> root s = Some (f,n)" by auto
        let ?cond = "\<forall> eq \<in># {#{#args t ! i. t \<in># add_mset t eqc2#}. i \<in># mset [0..<n]#}. UNIQ (\<T>(C,\<V>) ` set_mset eq)" 
        show False
        proof (cases ?cond)
          case True
          show False
            apply (rule contra)
            apply (rule spp_simp)
            apply (rule smp_decomp[OF rt refl])
            using True by auto
        next
          case False
          define eqc3 where "eqc3 = add_mset t eqc2" 
          from False obtain i where i: "i < n" and nuniq: "\<not> UNIQ (\<T>(C,\<V>) ` set_mset {#args t ! i. t \<in># add_mset t eqc2 #})" 
            unfolding mset2_simps by auto
          show False
            apply (rule contra)
            apply (rule spp_delete)
            apply (rule smp_decomp_fail[OF rt i])
            using nuniq by auto
        qed
      qed
    qed
  qed
qed

text \<open>Every normal form consists purely of variables, and these variable are of sorts
  that have a small cardinality (upper bound is the number of matching problems in p).\<close>
lemma NF_spp_step_fvf_with_small_card: assumes "finite_constructor_form_pat (mset3 p)" 
  and "\<nexists> P. p \<Rightarrow>\<^sub>s\<^sub>s P \<and> P \<noteq> {#}" 
  and mp: "mp \<in># p" 
  and eqc: "eqc \<in># mp"
  and t: "t \<in># eqc" 
shows "\<exists> x \<iota>. t = Var (x,\<iota>) \<and> card_of_sort C \<iota> \<le> size p"
proof -
  from normal_form_spp_step_fvf[OF assms(1-2), of "mset2 mp" "set_mset eqc" t] mp eqc t
  obtain x \<iota> where tx: "t = Var (x,\<iota>)" by force
  from assms(1)[unfolded finite_constructor_form_pat_def finite_constructor_form_mp_def, 
      rule_format, of "mset2 mp" "set_mset eqc"] mp eqc t tx 
  have ts: "t : \<iota> in \<T>(C,\<V> |` SS)" 
    by auto (metis Term.simps(1) comp_eq_dest_lhs hastype_def snd_eqD typed_S_eq)
  with tx have iota: "\<iota> \<in> S" by (metis typed_imp_S)  
  show ?thesis
  proof (intro exI conjI, rule tx)
    show "card_of_sort C \<iota> \<le> size p" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      hence large: "card_of_sort C \<iota> > size p" by auto
      define filt where "filt mp = (\<exists> eqc \<in># mp. \<exists> t \<in># eqc. t : \<iota> in \<T>(C, \<V> |` SS))" for mp
      define p1 where "p1 = filter_mset filt p" 
      define p2 where "p2 = filter_mset (Not o filt) p" 
      have p: "p = p1 + p2" unfolding p1_def p2_def by auto
      have large: "card_of_sort C \<iota> > size p1" using large unfolding p by auto
      have mp: "mp \<in># p1" unfolding p1_def filt_def using mp eqc t ts by auto
      hence p1: "p1 \<noteq> {#}" by auto
      obtain p1l where p1l: "p1 = mset p1l" by (metis ex_mset)
      have len: "length p1l = size p1" unfolding p1l by auto
      with p1 obtain n where lenp: "length p1l = Suc n" by (cases p1l, auto)
      define mp where "mp i = p1l ! i" for i
      {
        fix i
        assume "i \<le> n" 
        hence "i < length p1l" unfolding lenp by auto
        hence "mp i \<in> set p1l" unfolding mp_def by auto
        hence mp: "mp i \<in># p1" unfolding p1l by auto
        from this[unfolded p1_def] have mpp: "mp i \<in># p" and filt: "filt (mp i)" by auto
        from assms(1)[unfolded finite_constructor_form_pat_def] mpp
        have fin: "finite_constructor_form_mp (mset2 (mp i))" by auto
        from filt[unfolded filt_def] obtain eqc t where eqc: "eqc \<in># mp i" 
          and t: "t \<in># eqc" and ts: "t : \<iota> in \<T>(C,\<V> |` SS)" 
          by auto
        from fin[unfolded finite_constructor_form_mp_def, rule_format, of "set_mset eqc"] eqc
        obtain \<iota>' where eqcs: "\<And> s. s \<in>#eqc \<Longrightarrow> s : \<iota>' in \<T>(C,\<V> |` SS)" by auto
        from eqcs[OF t] ts have "\<iota>' = \<iota>" by fastforce
        note eqcs = eqcs[unfolded this]
        {
          fix mp'
          assume "mp i \<rightarrow>\<^sub>s\<^sub>s mp'"        
          from spp_simp[OF this, of "p - {# mp i #}"] mpp
          have "\<exists> P. p \<Rightarrow>\<^sub>s\<^sub>s P \<and> P \<noteq> {#}" by auto
          with assms have False by auto
        } note nf = this
        from eqc obtain mp' where mpi: "mp i = add_mset eqc mp'" by (metis mset_add)
        from t obtain eqc' where eqct: "eqc = add_mset t eqc'" by (metis mset_add)
        from smp_singleton[of t mp'] nf[unfolded mpi eqct] have "eqc' \<noteq> {#}" by auto
        then obtain s eqc2 where "eqc' = add_mset s eqc2" by (cases eqc', auto)
        note eqct = eqct[unfolded this]
        from smp_dup[of t eqc2 mp'] nf[unfolded mpi eqct] 
        have st: "s \<noteq> t" by auto
        from eqct have s: "s \<in># eqc" by auto
        from normal_form_spp_step_fvf[OF assms(1-2), of "mset2 (mp i)" "set_mset eqc", OF _ _ this]
          mpp eqc obtain x where sx: "s = Var x" by auto
        from eqcs[OF s, unfolded sx] have snd: "snd x = \<iota>"
          by (metis Term.simps(1) comp_apply hastypeD option.inject typed_restrict_imp_typed)
        have summary: 
          "snd x = \<iota> \<and> eqc \<in># mp i \<and> Var x \<noteq> t \<and> {Var x, t} \<subseteq> set_mset eqc \<and> t : \<iota> in \<T>(C,\<V> |` SS)" 
          using st snd eqc eqct sx ts by auto
        hence "\<exists> x eqc t. snd x = \<iota> \<and> eqc \<in># mp i \<and> Var x \<noteq> t \<and> {Var x, t} \<subseteq> set_mset eqc \<and> t : \<iota> in \<T>(C,\<V> |` SS)" by blast
      }
      hence "\<forall> i. \<exists> x eqc t. i \<le> n \<longrightarrow> snd x = \<iota> \<and> eqc \<in># mp i \<and> Var x \<noteq> t \<and> {Var x, t} \<subseteq> set_mset eqc \<and> t : \<iota> in \<T>(C,\<V> |` SS)" by blast
      from choice[OF this] obtain x where 
        "\<forall> i. \<exists> eqc t. i \<le> n \<longrightarrow> snd (x i) = \<iota> \<and> eqc \<in># mp i \<and> Var (x i) \<noteq> t \<and> {Var (x i), t} \<subseteq> set_mset eqc \<and> t : \<iota> in \<T>(C,\<V> |` SS)" by blast
      from choice[OF this] obtain eqc where 
        "\<forall> i. \<exists> t. i \<le> n \<longrightarrow> snd (x i) = \<iota> \<and> eqc i \<in># mp i \<and> Var (x i) \<noteq> t \<and> {Var (x i), t} \<subseteq> set_mset (eqc i) \<and> t : \<iota> in \<T>(C,\<V> |` SS)" by blast
      from choice[OF this] obtain t where 
        witnesses: "\<And> i. i \<le> n \<Longrightarrow> snd (x i) = \<iota> \<and> eqc i \<in># mp i \<and> Var (x i) \<noteq> t i \<and> {Var (x i), t i} \<subseteq> set_mset (eqc i)"
          and ti: "\<And> i. i \<le> n \<Longrightarrow> t i : \<iota> in \<T>(C,\<V> |` SS)" by blast
      note step = spp_delete_large_sort[of n x \<iota> eqc mp t p2, OF witnesses] 
      have "card (t ` {0..n}) \<le> card {0..n}" using card_image_le by blast
      also have "\<dots> = size p1" using len lenp p1l by auto
      also have "\<dots> < card_of_sort C \<iota>" by fact
      finally have "card (t ` {0..n}) < card_of_sort C \<iota>" . 
      note step = step[OF _ _ this]
      have id: "map mp [0..<Suc n] = p1l" unfolding mp_def using lenp by (rule map_nth')
      have "p2 + mset (map mp [0..<Suc n]) = p" unfolding id p p1l by auto
      note step = step[unfolded this]
      let ?Var = "Var :: nat \<times> 's \<Rightarrow> ('f, nat \<times> 's) Term.term" 
      define Vs where "Vs = tvars_spat (mset3 p2)" 
      have "x ` {0..n} \<inter> tvars_spat (mset3 p2) = {}"
      proof (rule ccontr)
        assume "\<not> ?thesis" 
        then obtain s where s1: "s \<in> x ` {0..n}" 
           and s2: "s \<in> tvars_spat (mset3 p2)" unfolding Vs_def[symmetric] by blast
        from s1 obtain i where "i \<le> n" and s: "s = x i" by auto
        with witnesses[of i] ti[of i] have s\<iota>: "Var s : \<iota> in \<T>(C,\<V>)"
          by (metis Term.simps(1) comp_eq_dest_lhs hastypeI)
        from s2 obtain mp eqc u where *: "mp \<in># p2" "eqc \<in># mp" "u \<in># eqc" "s \<in> vars u"  
          by fastforce
        from *(1)[unfolded p2_def] have mp: "mp \<in># p" and "\<not> filt mp" by auto
        from this(2)[unfolded filt_def] * have ns: "\<not> u : \<iota> in \<T>(C,\<V> |` SS)" by auto
        from normal_form_spp_step_fvf[OF assms(1-2), of "mset2 mp" "set_mset eqc" u] mp *
        have "is_Var u" by auto
        with * have u: "u = Var s" by auto
        note ns = ns[unfolded this]
        from s\<iota> iota u ns show False
          by (smt (verit, del_insts) SigmaE SigmaI UNIV_I UNIV_Times_UNIV Var_hastype comp_apply eq_Some_iff_hastype
              hastype_restrict option.inject snd_conv)  
      qed
      note step = step[OF _ this]
      from step assms(2) show False by auto
    qed
  qed
qed


definition max_depth_sort :: "'s \<Rightarrow> nat" where
  "max_depth_sort s = Maximum (depth_gterm ` {t. t : s in \<T>(C)})" 

lemma max_depth_sort_wit: assumes "finite_sort C s" 
  and "s \<in> S" 
shows "\<exists> t. t : s in \<T>(C) \<and> 
    depth_gterm t = max_depth_sort s \<and> 
    (\<forall> t'. t' : s in \<T>(C) \<longrightarrow> depth_gterm t' \<le> depth_gterm t)"
proof -
  let ?T = "{t. t : s in \<T>(C)}" 
  from sorts_non_empty[OF assms(2)] have "depth_gterm ` ?T \<noteq> {}" by auto
  moreover from assms(1)[unfolded finite_sort_def] have fin: "finite (depth_gterm ` ?T)" by auto
  ultimately obtain d where "d \<in> depth_gterm ` ?T" and d: "d = Maximum (depth_gterm ` ?T)"
    by (metis has_MaximumD(1) has_Maximum_nat_iff_finite)
  from this obtain t where t: "t \<in> ?T" 
    and depth: "depth_gterm t = Maximum (depth_gterm ` ?T)" "d = depth_gterm t" by auto
  have "t' \<in> ?T \<Longrightarrow> depth_gterm t' \<le> depth_gterm t" for t' 
    unfolding depth(2)[symmetric] unfolding d using fin 
    by (meson bdd_above_Maximum_nat bdd_above_nat image_iff)
  thus ?thesis unfolding max_depth_sort_def depth(1)[symmetric] using t
    by (intro exI[of _ t], auto)
qed

lemma max_depth_sort_Fun: assumes f: "f : \<sigma>s \<rightarrow> s in C" 
  and si: "si \<in> set \<sigma>s" 
  and fins: "finite_sort C s" 
shows "max_depth_sort si < max_depth_sort s" 
proof -
  from C_sub_S[OF f] si have s: "s \<in> S" and siS: "si \<in> S" by auto
  from finite_arg_sort[OF fins f si] 
  have "finite_sort C si" .
  from max_depth_sort_wit[OF this siS] obtain ti where
    ti: "ti : si in \<T>(C)" and depi: "depth_gterm ti = max_depth_sort si" by auto
  define t where "t s = (SOME t. t : s in \<T>(C))" for s
  have t: "s \<in> set \<sigma>s \<Longrightarrow> t s : s in \<T>(C)" for s 
    using someI_ex[OF sorts_non_empty[of s]] C_sub_S[OF f] 
    unfolding t_def by auto
  from si obtain i where si: "si = \<sigma>s ! i" and i: "i < length \<sigma>s" by (auto simp: set_conv_nth)
  define trm where "trm = Fun f (map (\<lambda> j. if j = i then ti else t (\<sigma>s ! j)) [0..<length \<sigma>s])"
  have trm: "trm : s in \<T>(C)" 
    unfolding trm_def
    apply (intro Fun_hastypeI[OF f] list_all2_all_nthI)
     apply force
    subgoal for j using t si ti by (auto simp: set_conv_nth)
    done
  have "max_depth_sort si = depth_gterm ti" using depi by auto
  also have "\<dots> < depth_gterm trm" unfolding trm_def
    by (rule depth_gterm_arg, insert i, auto)
  also have "\<dots> \<le> max_depth_sort s" 
    using max_depth_sort_wit[OF fins s] trm by auto
  finally show ?thesis .
qed

lemma max_depth_sort_var: assumes "t : s in \<T>(C, \<V> |` SS)" 
  and "x \<in> vars t" 
  and "finite_sort C s" 
shows "max_depth_sort (snd x) \<le> max_depth_sort s" 
  using assms
proof (induct)
  case (Var y s)
  thus ?case by (auto simp: hastype_def restrict_map_def split: if_splits)
next
  case (Fun f ts \<sigma>s \<tau>)
  from Fun(4) obtain i where i: "i < length ts" and x: "x \<in> vars (ts ! i)" 
    by (auto simp: set_conv_nth)
  from i Fun(2) have mem: "\<sigma>s ! i \<in> set \<sigma>s" by (auto simp: set_conv_nth list_all2_conv_all_nth)
  from finite_arg_sort[OF Fun(5,1) mem] 
  have "finite_sort C (\<sigma>s ! i)" .
  with Fun(3) i x have "max_depth_sort (snd x) \<le> max_depth_sort (\<sigma>s ! i)" 
    by (auto simp: list_all2_conv_all_nth)
  with max_depth_sort_Fun[OF Fun(1) mem Fun(5)]
  show ?case by simp
qed

definition max_depth_sort_smp :: "('f,'s) simple_match_problem_ms \<Rightarrow> nat" where
  "max_depth_sort_smp mp = Max (insert 0 (max_depth_sort ` snd ` tvars_smp (mset2 mp)))"

definition max_depth_sort_p :: "('f,'s) simple_pat_problem_ms \<Rightarrow> nat" where
  "max_depth_sort_p p = sum_mset (image_mset max_depth_sort_smp p)" 

lemma max_depth_sort_p_add[simp]: "max_depth_sort_p (add_mset mp p) = 
  max_depth_sort_smp mp + max_depth_sort_p p" 
  unfolding max_depth_sort_p_def by simp

lemma finite_constructor_form_pat_add: "finite_constructor_form_pat (mset3 (add_mset mp p))
  = (finite_constructor_form_mp (mset2 mp) \<and> finite_constructor_form_pat (mset3 p))"
  unfolding finite_constructor_form_pat_def by auto

lemma mds_decrease_inst: assumes ft: "is_Fun t"
  and tau: "\<tau> \<in> \<tau>s n x" 
  and mp: "mp = {#{#Var x, t#}#}" 
  and fin: "finite_constructor_form_mp (mset2 mp)" 
shows "max_depth_sort_smp mp > max_depth_sort_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp)" 
proof -
  from fin[unfolded finite_constructor_form_mp_def mp] obtain \<iota>
    where fin: "finite_sort C \<iota>" and x: "Var x : \<iota> in \<T>(C,\<V> |` SS)" and t: "t : \<iota> in \<T>(C,\<V> |` SS)" 
    by auto
  from x have iota: "\<iota> = snd x" and xS: "snd x \<in> S" by (auto simp: hastype_def restrict_map_def split: if_splits)
  from ft obtain f ts where ft: "t = Fun f ts" by (cases t, auto)
  from t[unfolded ft Fun_hastype] obtain \<sigma>s where f: "f : \<sigma>s \<rightarrow> \<iota> in C" 
    and ts: "ts :\<^sub>l \<sigma>s in \<T>(C,\<V> |` SS)" 
    by auto
  {
    fix y
    assume "y \<in> vars t" 
    from this[unfolded ft] obtain ti where y: "y \<in> vars ti" and ti: "ti \<in> set ts" by auto
    from ti ts obtain \<sigma>i where \<sigma>i: "\<sigma>i \<in> set \<sigma>s" and ti: "ti : \<sigma>i in \<T>(C,\<V> |` SS)" 
      unfolding list_all2_conv_all_nth set_conv_nth by force
    from max_depth_sort_var[OF ti y finite_arg_sort[OF fin f \<sigma>i]]
    have "max_depth_sort (snd y) \<le> max_depth_sort \<sigma>i" .
    also have "\<dots> < max_depth_sort (snd x)" 
      using max_depth_sort_Fun[OF f \<sigma>i fin] iota by auto
    finally have "max_depth_sort (snd y) < max_depth_sort (snd x)" by auto
  } note max_x = this

  from max_depth_sort_wit[OF fin, unfolded iota, OF xS] obtain wx
    where wx: "wx : snd x in \<T>(C)" and to_wx: "max_depth_sort (snd x) = depth_gterm wx" 
      and wx_max: "\<And> t'. t' : snd x in \<T>(C) \<Longrightarrow> depth_gterm t' \<le> depth_gterm wx" by auto
      
  have "max_depth_sort_smp mp = Max (max_depth_sort ` snd ` insert x (vars t))" unfolding mp
    max_depth_sort_smp_def by auto
  also have "\<dots> = max_depth_sort (snd x)" 
    by (rule Max_eqI, insert max_x, force+)
  finally have max_mp: "max_depth_sort_smp mp = max_depth_sort (snd x)" .

  from tau[unfolded \<tau>s_def] obtain f \<sigma>s where f: "f : \<sigma>s \<rightarrow> snd x in C" 
    and tau: "\<tau> = \<tau>c n x (f,\<sigma>s)" by auto
  have "max_depth_sort_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp) = 
     Max (insert 0 (max_depth_sort ` snd ` (vars (\<tau> x) \<union> vars (t \<cdot> \<tau>))))" 
    unfolding max_depth_sort_smp_def mp by simp
  also have "\<dots> \<le> Max (insert 0 (max_depth_sort ` (snd ` vars (\<tau> x) \<union> snd ` vars t)))" 
    by (rule Max_mono, auto simp: vars_term_subst tau \<tau>c_def subst_def)
  also have "snd ` vars (\<tau> x) = set \<sigma>s" unfolding tau \<tau>c_def subst_def 
    by (force simp: set_zip set_conv_nth[of \<sigma>s])
  also have "Max (insert 0 (max_depth_sort ` (set \<sigma>s \<union> snd ` vars t))) < max_depth_sort (snd x)"
  proof (subst Max_less_iff, force, force, intro ballI)
    fix d
    assume d: "d \<in> insert 0 (max_depth_sort ` (set \<sigma>s \<union> snd ` vars t))" 
    show "d < max_depth_sort (snd x)" 
    proof (cases "d \<in> max_depth_sort ` snd ` vars t")
      case True
      with max_x show ?thesis by auto
    next
      case False
      hence "d = 0 \<or> d \<in> max_depth_sort ` set \<sigma>s" using d by auto
      thus ?thesis
      proof
        assume "d = 0" 
        thus ?thesis unfolding to_wx by (cases wx, auto)
      next
        assume "d \<in> max_depth_sort ` set \<sigma>s" 
        then obtain \<sigma> where mem: "\<sigma> \<in> set \<sigma>s" and d: "d = max_depth_sort \<sigma>" by auto
        from max_depth_sort_Fun[OF f mem] d fin iota show ?thesis by auto
      qed
    qed
  qed
  finally show ?thesis unfolding max_mp .
qed
  
lemma mds_weak_decrease_inst: assumes tau: "\<tau> \<in> \<tau>s n x" 
  and fin: "finite_sort C (snd x)" 
shows "max_depth_sort_smp mp \<ge> max_depth_sort_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp)" 
proof -
  from tau[unfolded \<tau>s_def] obtain f \<sigma>s where f: "f : \<sigma>s \<rightarrow> snd x in C" 
    and tau: "\<tau> = \<tau>c n x (f,\<sigma>s)" by auto
  note tau = tau[unfolded \<tau>c_def split]
  show ?thesis
  proof (cases "x \<in> tvars_smp (mset2 mp)")
    case False
    have "image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp = image_mset (image_mset (\<lambda> t. t \<cdot> Var)) mp" 
    proof (intro image_mset_cong refl term_subst_eq, goal_cases)
      case (1 eqc t y)
      with False have "x \<noteq> y" by auto
      thus ?case unfolding tau by (auto simp: subst_def)
    qed 
    also have "\<dots> = mp" by simp
    finally show ?thesis by simp
  next
    case True
    define tv where "tv = tvars_smp (mset2 mp)" 
    let ?mp = "image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp" 
    from True have x: "x \<in> tv" unfolding tv_def .
    have fin: "finite tv" unfolding tv_def by auto
    have "max_depth_sort_smp mp = Max (insert 0 (max_depth_sort ` snd ` (insert x tv)))" 
      unfolding max_depth_sort_smp_def tv_def using True by auto
    also have "\<dots> = Max (max_depth_sort ` snd ` (insert x tv))" using fin by simp
    finally have max_mp: "max_depth_sort_smp mp = Max (max_depth_sort ` snd ` insert x tv)" .

    have "tvars_smp (mset2 ?mp) = \<Union> (vars ` \<tau> ` tv)"
      by (fastforce simp add: tv_def vars_term_subst)
    also have "\<dots> = vars (\<tau> x) \<union> \<Union> (vars ` \<tau> ` tv)" using x by auto
    also have "\<dots> = vars (\<tau> x) \<union> (tv - {x})" unfolding tau subst_def by auto
    finally have tvars: "tvars_smp (mset2 ?mp) = vars (\<tau> x) \<union> (tv - {x})" .
      
    have "max_depth_sort_smp ?mp = Max (insert 0 (max_depth_sort ` (snd ` vars (\<tau> x) \<union> snd ` (tv - {x}))))"
      unfolding max_depth_sort_smp_def tvars by (metis image_Un)
    also have "snd ` vars (\<tau> x) = set \<sigma>s" unfolding tau subst_def 
      by (force simp: set_zip set_conv_nth[of \<sigma>s])
    also have "Max (insert 0 (max_depth_sort ` (set \<sigma>s \<union> snd ` (tv - {x})))) 
       \<le> max_depth_sort_smp mp" unfolding max_mp
    proof (intro Max_le_MaxI)
      fix d
      assume d: "d \<in> insert 0 (max_depth_sort ` (set \<sigma>s \<union> snd ` (tv - {x})))" 
      show "\<exists>d'\<in>max_depth_sort ` snd ` insert x tv. d \<le> d'"
      proof (cases "d \<in> max_depth_sort ` set \<sigma>s")
        case True
        then obtain \<sigma> where mem: "\<sigma> \<in> set \<sigma>s" and d: "d = max_depth_sort \<sigma>" by auto
        from max_depth_sort_Fun[OF f mem assms(2)]
        show ?thesis unfolding d by auto
      qed (insert d, auto)
    qed (insert fin, auto)
    finally show ?thesis .
  qed
qed

lemma max_depth_sort_le: assumes "tvars_smp (mset2 mp) \<subseteq> tvars_smp (mset2 mp')"
  shows "max_depth_sort_smp mp \<le> max_depth_sort_smp mp'"
  unfolding max_depth_sort_smp_def
  apply (rule Max_le_MaxI)
     apply force
    apply force
   apply force
  using assms by auto

lemma mp_step_tvars: "mp \<rightarrow>\<^sub>s\<^sub>s mp' \<Longrightarrow> tvars_smp (mset2 mp') \<subseteq> tvars_smp (mset2 mp)"
proof (induct rule: smp_step_ms.induct)
  case *: (smp_decomp eqc f n eqcn mp)
  from *(2) show ?case 
  proof (clarsimp, goal_cases)
    case (1 x s i ti)
    from *(1)[OF 1(4)] 1(2,3)
    show ?case by (intro bexI[OF _ 1(4)], cases ti, auto)
  qed
qed auto

lemma max_depth_sort_p_inst: assumes mem: "{#{#Var x, t#}#} \<in># p" 
  and t: "is_Fun t" 
  and tau: "\<tau> \<in> \<tau>s n x" 
  and fin: "finite_constructor_form_pat (mset3 p)"
shows "max_depth_sort_p p > max_depth_sort_p (image_mset (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>))) p)" 
proof -
  obtain mp p' where p: "p = add_mset mp p'" and mp: "mp = {#{#Var x, t#}#}" 
    using mset_add[OF mem, of thesis] by simp
  from fin[unfolded finite_constructor_form_pat_def p]
  have fin: "finite_constructor_form_mp (mset2 mp)" by auto
  show ?thesis unfolding p
  proof (simp add: max_depth_sort_p_def image_mset.compositionality o_def)
    show "max_depth_sort_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp) +
      (\<Sum>x\<in>#p'. max_depth_sort_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) x))
    < max_depth_sort_smp mp + \<Sum>\<^sub># (image_mset max_depth_sort_smp p')" (is "?a1 + ?b1 < ?a2 + ?b2")
    proof (rule add_less_le_mono)
      show "?a1 < ?a2" 
        by (rule mds_decrease_inst[OF t tau mp fin])
      show "?b1 \<le> ?b2" 
      proof (rule sum_mset_mono, rule mds_weak_decrease_inst[OF tau])
        from fin[unfolded finite_constructor_form_mp_def mp] obtain \<iota>
          where fin: "finite_sort C \<iota>" and x: "Var x : \<iota> in \<T>(C,\<V> |` SS)" 
          by auto
        from x fin show "finite_sort C (snd x)" 
          by (auto simp: hastype_def restrict_map_def split: if_splits)
      qed
    qed
  qed
qed

lemma depth_gterm_le_card: "finite_sort C \<sigma> \<Longrightarrow> t : \<sigma> in \<T>(D) \<Longrightarrow> D \<subseteq>\<^sub>m C \<Longrightarrow> depth_gterm t \<le> card (dom D)"
proof (induct t arbitrary: \<sigma> D)
  case *: (Fun f ts \<sigma> D)
  from *(3)[unfolded Fun_hastype] obtain \<sigma>s where f: "f : \<sigma>s \<rightarrow> \<sigma> in D" and ts: "ts :\<^sub>l \<sigma>s in \<T>(D)" by auto
  from *(4) have "dom D \<subseteq> dom C" by (rule map_le_implies_dom_le)
  with finite_C have fin: "finite (dom D)" by (metis finite_subset)
  from f have mem: "(f,\<sigma>s) \<in> dom D" by auto
  define domD' where "domD' = dom D - {(f,\<sigma>s)}" 
  define D' where "D' = D |` domD'" 
  have dom: "dom D = insert (f,\<sigma>s) (dom D')" unfolding D'_def domD'_def using mem by auto
  from arg_cong[OF this, of card] 
  have cardD: "card (dom D) = Suc (card (dom D'))" 
    unfolding D'_def domD'_def using mem fin by auto
  from f *(4) have "f : \<sigma>s \<rightarrow> \<sigma> in C" by (metis subssigD)
  hence sig: "\<sigma> \<in> S" using C_sub_S by blast
  show ?case 
  proof (cases ts)  
    case Nil
    thus ?thesis unfolding cardD by simp
  next
    case (Cons t ts')
    hence "map depth_gterm ts \<noteq> []" by auto
    from max_list_mem[OF this] obtain t where t: "t \<in> set ts" 
      and "max_list (map depth_gterm ts) = depth_gterm t" by auto
    hence depth: "depth_gterm (Fun f ts) = Suc (depth_gterm t)" by simp
    note IH = *(1)[OF t]
    have "D' \<subseteq>\<^sub>m C" using *(4) unfolding D'_def
      using map_le_trans by blast
    note IH = IH[OF _ _ this]
    from t ts obtain \<tau> where tau: "\<tau> \<in> set \<sigma>s" and tt: "t : \<tau> in \<T>(D)" 
      by (force simp: list_all2_conv_all_nth set_conv_nth)
    have "f : \<sigma>s \<rightarrow> \<sigma> in C" by fact
    from finite_arg_sort[OF *(2) this tau] have "finite_sort C \<tau>" by auto
    note IH = IH[OF this]
    have "t : \<tau> in \<T>(D')" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      from tt this have "\<exists> s. t \<unrhd> s \<and> s : \<sigma> in \<T>(D)" 
      proof induct
        case (Fun g ss \<tau>s \<tau>)
        show ?case
        proof (cases "ss :\<^sub>l \<tau>s in \<T>(D')")
          case True
          from this Fun(4) have "\<not> (g : \<tau>s \<rightarrow> \<tau> in D')" 
            by (metis Fun_hastypeI)
          with Fun(1) have "(g,\<tau>s) = (f,\<sigma>s)" unfolding D'_def domD'_def 
            by (auto simp: restrict_map_def fun_hastype_def hastype_def split: if_splits)
          with Fun(1) f have "\<tau> = \<sigma>" by (simp add: fun_has_same_type)
          from Fun(1,2)[unfolded this] have "Fun g ss : \<sigma> in \<T>(D)" by (rule Fun_hastypeI)
          thus ?thesis by blast
        next
          case False
          with Fun(2) obtain i where i: "i < length ss"
            and ssi: "\<not> (ss ! i : \<tau>s ! i in \<T>(D'))"
            by (force simp: list_all2_conv_all_nth set_conv_nth)
          from list_all2_nthD[OF Fun(3) i, rule_format, OF ssi]
          obtain s where "s \<unlhd> ss ! i" and s: "s : \<sigma> in \<T>(D)" 
            by auto
          show ?thesis
          proof (intro exI[of _ s] conjI s)
            have "s \<unlhd> ss ! i" by fact
            also have "ss ! i \<unlhd> Fun g ss" using i by simp
            finally show "s \<unlhd> Fun g ss" by auto
          qed
        qed
      qed auto
      then obtain s where "s \<unlhd> t" and s: "s : \<sigma> in \<T>(D)" by auto
      with t have sub: "Fun f ts \<rhd> s" by auto
      from s *(4) have s: "s : \<sigma> in \<T>(C)" by (metis hastype_in_Term_mono_left)
      from *(3,4) have t: "Fun f ts : \<sigma> in \<T>(C)" by (metis hastype_in_Term_mono_left)
      from sub obtain c where "c \<noteq> \<box>" and "Fun f ts = c \<langle>s\<rangle>" by blast
      from apply_ctxt_hastype_imp_hastype_context[OF t[unfolded this] s] 
      have c: "c : \<sigma> \<rightarrow> \<sigma> in \<C>(C,\<lambda>x. None)" by auto
      from max_depth_sort_wit[OF *(2) sig]
      obtain t where t: "t : \<sigma> in \<T>(C)" and large: "\<And> t'. t' : \<sigma> in \<T>(C) \<Longrightarrow> depth_gterm t' \<le> depth_gterm t" 
        by auto
      from t c have "c \<langle> t \<rangle> : \<sigma> in \<T>(C)" by (metis apply_ctxt_hastype)
      from large[OF this] have contra: "depth_gterm (c \<langle>t\<rangle>) \<le> depth_gterm t" .
      from \<open>c \<noteq> \<box>\<close> obtain f bef d aft where c: "c = More f bef d aft" by (cases c, auto)
      have "depth_gterm t \<le> depth_gterm (d \<langle>t\<rangle>)" 
      proof (induct d)
        case (More f bef d aft)
        thus ?case using max_list[of "depth_gterm (d\<langle>t\<rangle>)" "map depth_gterm bef @ depth_gterm d\<langle>t\<rangle> # map depth_gterm aft"] 
          by auto
      qed auto
      also have "\<dots> < depth_gterm (c \<langle>t\<rangle>)" unfolding c 
        using max_list[of "depth_gterm (d\<langle>t\<rangle>)" "map depth_gterm bef @ depth_gterm d\<langle>t\<rangle> # map depth_gterm aft"] 
        by auto
      also have "\<dots> \<le> depth_gterm t" by (rule contra)
      finally show False by simp 
    qed
    from IH[OF this] show ?thesis unfolding depth cardD by auto
  qed
qed auto


lemma max_depth_sort_smp_le_card: assumes "finite_constructor_form_mp (mset2 mp)"
  shows "max_depth_sort_smp mp \<le> card (dom C)" 
  unfolding max_depth_sort_smp_def
proof (subst Max_le_iff, force intro!: finite_imageI, force, intro ballI)
  fix d
  assume d: "d \<in> insert 0 (max_depth_sort ` snd ` \<Union> (\<Union> ((`) vars ` mset2 mp)))" 
  show "d \<le> card (dom C)" 
  proof (cases "d = 0")
    case False
    with d obtain eqc t x where "eqc \<in> mset2 mp" "t \<in> eqc" and 
      x: "x \<in> vars t" and d: "d = max_depth_sort (snd x)" 
      by blast
    with assms[unfolded finite_constructor_form_mp_def] obtain \<iota> where fin: "finite_sort C \<iota>" 
      and t: "t : \<iota> in \<T>(C,\<V> |` SS)" by force
    define \<sigma> where "\<sigma> = snd x" 
    from t x have inS: "\<sigma> \<in> S" 
      by induct (auto simp: restrict_map_def hastype_def list_all2_conv_all_nth set_conv_nth 
          \<sigma>_def split: if_splits)
    from t fin x have fin: "finite_sort C \<sigma>"
    proof (induct)
      case (Var v \<sigma>)
      then show ?case by (auto simp: restrict_map_def hastype_def \<sigma>_def split: if_splits)
    next
      case *: (Fun f ss \<sigma>s \<tau>)
      from finite_arg_sort[OF *(4,1)] *(2,3,5)
      show ?case by (auto simp: list_all2_conv_all_nth set_conv_nth)
    qed
    from max_depth_sort_wit[OF this inS, folded d[folded \<sigma>_def]]
    obtain t where t\<sigma>: "t : \<sigma> in \<T>(C)" "depth_gterm t = d" 
      "\<And> t'. t' : \<sigma> in \<T>(C) \<Longrightarrow> depth_gterm t' \<le> d" by auto
    from depth_gterm_le_card[OF fin t\<sigma>(1), unfolded t\<sigma>] show ?thesis by simp
  qed auto
qed 

lemma max_depth_sort_p_le_card_size: assumes "finite_constructor_form_pat (mset3 p)"
  shows "max_depth_sort_p p \<le> card (dom C) * size p" 
proof -
  have "max_depth_sort_p p = sum_mset (image_mset max_depth_sort_smp p)" unfolding max_depth_sort_p_def ..
  also have "\<dots> \<le> sum_mset (image_mset (\<lambda> mp. card (dom C)) p)" 
    by (rule sum_mset_mono, rule max_depth_sort_smp_le_card, 
      insert assms, auto simp: finite_constructor_form_pat_def)
  finally show ?thesis by (simp add: ac_simps)
qed


definition num_syms_smp :: "('f,'s)simple_match_problem_ms \<Rightarrow> nat" where
  "num_syms_smp mp = sum_mset (image_mset num_syms (sum_mset mp))" 

lemma num_syms_subset: assumes "sum_mset mp \<subset># sum_mset mp'" 
  shows "num_syms_smp mp < num_syms_smp mp'"
proof -
  from assms obtain ts where "sum_mset mp' = ts + sum_mset mp" and "ts \<noteq> {#}" 
    by (metis add.commute subset_mset.lessE)
  thus ?thesis unfolding num_syms_smp_def 
    by (cases ts, auto)
qed

definition max_dupl_smp where
  "max_dupl_smp mp = Max (insert 0 ((\<lambda> x. (\<Sum> t\<in># sum_mset mp. count (syms_term t) (Inl x))) ` tvars_smp (mset2 mp)))" 

definition max_dupl_p :: "('f,'s)simple_pat_problem_ms \<Rightarrow> nat" where
  "max_dupl_p p = sum_mset (image_mset max_dupl_smp p)" 


lemma max_dupl_smp: "(\<Sum> t\<in># sum_mset mp. count (syms_term t) (Inl x)) \<le> max_dupl_smp mp" 
proof (cases "x \<in> tvars_smp (mset2 mp)")
  case True
  thus ?thesis unfolding max_dupl_smp_def
    by (intro Max_ge[OF finite.insertI[OF finite_imageI]], auto)
next
  case False
  have "(\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x)) = 0" 
  proof (clarsimp)
    fix eq t
    assume "eq \<in># mp" "t \<in># eq" 
    with False have "x \<notin> vars t" by auto
    thus "count (syms_term t) (Inl x) = 0" unfolding vars_term_syms_term
      by (simp add: count_eq_zero_iff)
  qed
  thus ?thesis by linarith
qed

lemma max_dupl_smp_le_num_syms: "max_dupl_smp mp \<le> num_syms_smp mp" 
  unfolding max_dupl_smp_def
proof (subst Max_le_iff, force intro!: finite_imageI simp: tvars_match_def, force, intro ballI)
  fix n
  assume n: "n \<in> insert 0 {\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x) |. x \<in> tvars_smp (mset2 mp)}" 
  show "n \<le> num_syms_smp mp" 
  proof (cases "n = 0")
    case False
    with n obtain x where x: "x \<in> tvars_smp (mset2 mp)" 
      and n: "n = (\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x))" by auto
    have nt: "num_syms_smp mp = \<Sum>\<^sub># (image_mset num_syms (\<Sum>\<^sub># mp))" 
      unfolding num_syms_smp_def ..
    show ?thesis unfolding n nt
    proof (rule sum_mset_mono, goal_cases)
      case (1 t)
      show "count (syms_term t) (Inl x) \<le> num_syms t" 
        unfolding num_syms_def by (rule count_le_size)
    qed
  qed auto
qed 

lemma num_syms_smp_\<tau>s: assumes \<tau>: "\<tau> \<in> \<tau>s n x"
  shows "num_syms_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp) \<le> num_syms_smp mp + max_dupl_smp mp * m" 
proof - 
  have "num_syms_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp) = 
    (\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. num_syms (t \<cdot> \<tau>)))" 
    unfolding num_syms_smp_def image_mset.compositionality o_def
    by (induct mp, auto simp: image_mset.compositionality o_def)
  also have "\<dots> \<le> (\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. num_syms t + count (syms_term t) (Inl x) * m))" 
    using num_syms_\<tau>s[OF \<tau>] 
    by (intro sum_mset_mono, auto)
  also have "\<dots> = (\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. num_syms t)) + (\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. count (syms_term t) (Inl x) * m))" 
    unfolding sum_mset.distrib by simp
  also have "(\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. num_syms t)) = num_syms_smp mp" 
    unfolding num_syms_smp_def by (induct mp, auto)
  also have "(\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. count (syms_term t) (Inl x) * m))
     = (\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. count (syms_term t) (Inl x))) * m" 
    unfolding sum_mset_distrib_right by simp
  also have "(\<Sum> eq\<in>#mp. (\<Sum> t\<in>#eq. count (syms_term t) (Inl x)))
     = (\<Sum> t\<in># sum_mset mp. count (syms_term t) (Inl x))" 
    by (induct mp, auto)
  also have "\<dots> * m \<le> max_dupl_smp mp * m" 
    using max_dupl_smp[of x mp] by simp
  finally show ?thesis by simp
qed

lemma max_dupl_smp_\<tau>s: assumes \<tau>: "\<tau> \<in> \<tau>s n x"
    and disj: "fst ` tvars_smp (mset2 mp) \<inter> {n..<n + m} = {}" 
  shows "max_dupl_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp) \<le> max_dupl_smp mp" 
proof - 
  from \<tau>[unfolded \<tau>s_def] obtain f ss 
    where f: "f : ss \<rightarrow> snd x in C" and \<tau>: "\<tau> = \<tau>c n x (f,ss)" by auto
  define vs where "vs = (zip [n..<n + length ss] ss)" 
  define s where "s = (Fun f (map Var vs))" 
  have tau: "\<tau> = subst x s" unfolding \<tau> \<tau>c_def s_def vs_def by auto
  show ?thesis
  proof (cases "x \<in> tvars_smp (mset2 mp)")
    case False
    have "image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp = image_mset (image_mset (\<lambda>t. t \<cdot> Var)) mp" 
    proof (intro image_mset_cong term_subst_eq, goal_cases)
      case (1 eq t y)
      with False show ?case by (auto simp: tau subst_def)
    qed
    thus ?thesis by simp
  next
    case x: True
    show ?thesis unfolding max_dupl_smp_def
    proof ((intro Max_le_MaxI; (intro finite.insertI, force)?), force, goal_cases)
      case (1 d)
      show ?case
      proof (cases "d = 0")
        case False
        with 1 obtain y where 
          d: "d = (\<Sum>t\<in>#\<Sum>\<^sub># (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp). count (syms_term t) (Inl y))" 
          and y: "y \<in> tvars_smp (mset2 (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp))" by auto
        have syms_s: "syms_term s = add_mset (Inr f) (mset (map Inl vs))" unfolding s_def
          by (simp, induct vs, auto)
        define repl :: "('f, nat \<times> 's) Term.term \<Rightarrow> (nat \<times> 's + 'f) multiset"  
          where "repl t = replicate_mset (count (syms_term t) (Inl x)) (Inl x)" for t
        let ?add = "(\<Sum>t\<in>#\<Sum>\<^sub># mp. count (repl t) (Inl y))" 
        let ?symsy = "(\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl y))" 
        let ?symsxy = "(\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x) * count (syms_term s) (Inl y))" 
        let ?symsx = "(\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x))" 
        have "d = (\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term (t \<cdot> \<tau>)) (Inl y))" 
          unfolding d
        proof (induct mp, auto, goal_cases)
          case (1 eq mp)
          show ?case by (induct eq, auto)
        qed
        also have "\<dots> \<le> \<dots> + ?add" by simp
        also have "\<dots> = 
           (\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term (t \<cdot> \<tau>) + repl t) (Inl y))" 
          unfolding sum_mset.distrib[symmetric]
          by (rule arg_cong[of _ _ sum_mset], rule image_mset_cong, simp)
        also have "\<dots> = ?symsy + ?symsxy" 
          unfolding repl_def tau syms_term_subst sum_mset.distrib[symmetric] by simp
        finally have d: "d \<le> ?symsy + ?symsxy" .
        show ?thesis
        proof (cases "y \<in> set vs")
          case False
          hence "?symsxy = 0" unfolding syms_s by auto
          with d have d: "d \<le> ?symsy" by auto
          from y[simplified] obtain eq t 
            where eq: "eq \<in># mp" and t: "t \<in># eq" and y: "y \<in> vars (t \<cdot> \<tau>)" 
            by auto
          from False this[unfolded vars_term_subst tau subst_def s_def]
          have "y \<in> vars t" by (auto split: if_splits)
          hence "y \<in> tvars_smp (mset2 mp)" using eq t by auto
          with d show ?thesis by auto
        next
          case True
          have dist: "distinct vs" unfolding vs_def
            by (metis distinct_enumerate enumerate_eq_zip)
          from split_list[OF True] obtain vs1 vs2 where vs: "vs = vs1 @ y # vs2" by auto
          with dist have nmem: "y \<notin> set vs1" "y \<notin> set vs2" by auto
          have "count (syms_term s) (Inl y) = 1" unfolding syms_s vs using nmem
            by (auto simp: count_eq_zero_iff) 
          with d have d: "d \<le> ?symsy + ?symsx" by auto
          from True have "fst y \<in> {n..<n + m}" unfolding vs_def using m[OF f] 
            by (auto simp: set_zip)
          with disj have "y \<notin> tvars_smp (mset2 mp)" by blast
          hence "?symsy = 0" 
            by (auto simp: count_eq_zero_iff vars_term_syms_term)
          with d have "d \<le> ?symsx" by auto
          with x show ?thesis by auto
        qed
      qed auto
    qed
  qed
qed


definition num_syms_p :: "('f,'s)simple_pat_problem_ms \<Rightarrow> nat" where
  "num_syms_p p = sum_mset (image_mset num_syms_smp p)" 

lemma num_syms_p_add[simp]: "num_syms_p (add_mset mp p) = num_syms_smp mp + num_syms_p p" 
  unfolding num_syms_p_def by simp

lemma max_dupl_p_le_num_syms: "max_dupl_p p \<le> num_syms_p p"
  unfolding max_dupl_p_def num_syms_p_def
  by (rule sum_mset_mono[OF max_dupl_smp_le_num_syms])

lemma max_dupl_p_add[simp]: "max_dupl_p (add_mset mp p) = max_dupl_smp mp + max_dupl_p p" 
  unfolding max_dupl_p_def by simp

lemma max_dupl_mono_main: assumes "\<And> x. (\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x)) \<le> (\<Sum>t\<in>#\<Sum>\<^sub># mp'. count (syms_term t) (Inl x))" 
  and "tvars_smp (mset2 mp) \<subseteq> tvars_smp (mset2 mp')" 
shows "max_dupl_smp mp \<le> max_dupl_smp mp'" 
  unfolding max_dupl_smp_def
proof ((intro Max_le_MaxI; (intro finite.insertI, force)?), force, goal_cases)
  case (1 d)
  show ?case
  proof (cases "d = 0")
    case False
    with 1 obtain x where d: "d = (\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x))" 
      and x: "x \<in> tvars_smp (mset2 mp)" by auto
    with x assms(2) have x: "x \<in> tvars_smp (mset2 mp')" by blast
    define d' where "d' = (\<Sum>t\<in>#\<Sum>\<^sub># mp'. count (syms_term t) (Inl x))"  
    have "d \<le> d'" unfolding d d'_def by fact
    with x show ?thesis unfolding d'_def by blast
  qed auto
qed


lemma max_dupl_mono: assumes "sum_mset mp \<subseteq># sum_mset mp'"
  shows "max_dupl_smp mp \<le> max_dupl_smp mp'" 
proof (rule max_dupl_mono_main)
  from set_mp[OF set_mset_mono[OF assms]] 
  show "tvars_smp (mset2 mp) \<subseteq> tvars_smp (mset2 mp')" by force
  from assms obtain mp2 where eq: "sum_mset mp' = sum_mset mp + mp2" by (rule subset_mset.less_eqE) 
  fix x
  show "(\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x)) \<le> (\<Sum>t\<in>#\<Sum>\<^sub># mp'. count (syms_term t) (Inl x))" 
    unfolding eq image_mset_union by auto
qed  


definition syms_smp :: "('f,'s)simple_match_problem_ms \<Rightarrow> (nat \<times> 's + 'f) multiset" where
  "syms_smp mp = sum_mset (image_mset syms_term (sum_mset mp))" 

definition syms_eqc :: "('f,nat \<times> 's)term multiset \<Rightarrow> (nat \<times> 's + 'f) multiset" where
  "syms_eqc eqc = sum_mset (image_mset syms_term eqc)" 

lemma syms_smp_to_eqc: "syms_smp mp = sum_mset (image_mset syms_eqc mp)" 
  unfolding syms_smp_def syms_eqc_def 
  by (induct mp, auto)

lemma nums_eq_size_syms_smp: "num_syms_smp mp = size (syms_smp mp)" 
  unfolding num_syms_smp_def syms_smp_def num_syms_def 
proof (induct mp)
  case (add eq mp)
  show ?case
    apply (simp add: add)
    apply (induct eq, auto)
    done
qed auto

lemma num_syms_sym_subset: assumes "syms_smp mp \<subset># syms_smp mp'" 
  shows "num_syms_smp mp < num_syms_smp mp'" 
proof -
  from assms obtain d where mp': "syms_smp mp' = d + syms_smp mp" and d: "d \<noteq> {#}"
    by (metis add.commute subset_mset.lessE)
  thus ?thesis unfolding nums_eq_size_syms_smp by (cases d, auto)
qed

lemma num_syms_smp_step: "mp \<rightarrow>\<^sub>s\<^sub>s mp' \<Longrightarrow> finite_constructor_form_mp (mset2 mp) 
  \<Longrightarrow> num_syms_smp mp' < num_syms_smp mp" 
proof (induct rule: smp_step_ms.induct)
  case (smp_dup t eqc mp)
  show ?case by (rule num_syms_subset, auto)
next
  case (smp_singleton t mp)
  show ?case by (rule num_syms_subset, auto)
next
  case (smp_triv_sort t \<iota> eq mp)
  show ?case by (rule num_syms_subset, auto)
next
  case *: (smp_decomp eqc f n eqcn mp)
  define nums where "nums = mset_set {0..<n}" 
  from *(4) have eqc: "eqc \<noteq> {#}" unfolding finite_constructor_form_mp_def by auto
  define arg where "arg t = (\<Sum>i\<in>#nums. syms_term (args t ! i))" for t :: "('f, nat \<times> 's) term" 
  {
    fix t
    assume "t \<in># eqc" 
    from *(1)[OF this] obtain ts where t: "t = Fun f ts" and len: "n = length ts" by (cases t, auto)
    have id: "mset ts = image_mset ((!) ts) (mset [0..<length ts])" 
      by (metis map_nth' mset_map)
    have "syms_term t = add_mset (Inr f) (arg t)" unfolding t arg_def nums_def len
      by (auto simp: id image_mset.compositionality o_def)
  } note step = this
  have "?case \<longleftrightarrow> num_syms_smp eqcn < num_syms_smp {#eqc#}" using * unfolding num_syms_smp_def by auto
  also have \<dots>
  proof (rule num_syms_sym_subset)
    from eqc obtain t eqc' where eqc: "eqc = add_mset t eqc'" by (cases eqc, auto)
    have "syms_smp eqcn = (\<Sum>i\<in>#nums. syms_eqc {#args t ! i. t \<in># eqc#})" 
      unfolding  image_mset.compositionality o_def nums_def syms_smp_to_eqc *(2)
      by simp
    also have "\<dots> = (\<Sum>t\<in>#eqc. arg t)" unfolding arg_def
      unfolding syms_eqc_def image_mset.compositionality o_def 
      by (rule sum_mset.swap)
    also have "\<dots> = arg t + (\<Sum>t\<in>#eqc'. arg t)" unfolding eqc by auto
    also have "\<dots> \<subset># syms_term t + (\<Sum>t\<in>#eqc'. syms_term t)" 
    proof (rule subset_mset.add_less_le_mono)
      from step[of t] eqc 
      show "arg t \<subset># syms_term t" by auto
      from step have step: "t \<in># eqc' \<Longrightarrow> syms_term t = add_mset (Inr f) (arg t)" for t unfolding eqc by auto
      have "\<Sum>\<^sub># (image_mset syms_term eqc') = \<Sum>\<^sub># (image_mset (\<lambda> t. add_mset (Inr f) (arg t)) eqc')"
        by (subst image_mset_cong[OF step], auto)
      also have "\<dots> = \<Sum>\<^sub># (image_mset (\<lambda> t. arg t) eqc') + image_mset (\<lambda> t. Inr f) eqc'" 
        by (induct eqc', auto)
      finally 
      show "\<Sum>\<^sub># (image_mset arg eqc') \<subseteq># \<Sum>\<^sub># (image_mset syms_term eqc')" by simp
    qed
    also have "syms_term t + (\<Sum>t\<in>#eqc'. syms_term t) = (\<Sum>t\<in>#eqc. syms_term t)" unfolding eqc by simp
    also have "\<dots> = syms_smp {#eqc#}" unfolding syms_smp_to_eqc syms_eqc_def by simp
    finally show "syms_smp eqcn \<subset># syms_smp {#eqc#}" .
  qed
  finally show ?case .
qed

lemma num_syms_smp_pos[simp]: assumes "finite_constructor_form_mp (mset2 mp)" 
  and "mp \<noteq> {#}" 
shows "num_syms_smp mp > 0" 
proof -
  from assms obtain eqc mp' where mp: "mp = add_mset eqc mp'" by (cases mp, auto)
  with assms have "eqc \<noteq> {#}" unfolding  finite_constructor_form_mp_def by auto
  thus ?thesis unfolding mp num_syms_smp_def by (cases eqc, auto)
qed

lemma count_syms_smp: "(\<Sum>t\<in>#\<Sum>\<^sub># mp. count (syms_term t) (Inl x)) = (count (syms_smp mp) (Inl x))" 
  unfolding syms_smp_def 
proof (induct mp, auto simp: image_mset.compositionality o_def, goal_cases)
  case (1 eq mp)
  show ?case by (induct eq, auto)
qed


lemma max_dupl_smp_step: "mp \<rightarrow>\<^sub>s\<^sub>s mp' \<Longrightarrow> max_dupl_smp mp' \<le> max_dupl_smp mp" 
proof (induct rule: smp_step_ms.induct)
  case (smp_dup t eqc mp)
  show ?case by (rule max_dupl_mono, auto)
next
  case (smp_singleton t mp)
  show ?case by (rule max_dupl_mono, auto)
next
  case (smp_triv_sort t \<iota> eq mp)
  show ?case by (rule max_dupl_mono, auto)
next
  case *: (smp_decomp eqc f n eqcn mp)
  show ?case
  proof (rule max_dupl_mono_main, unfold count_syms_smp, rule mset_subset_eq_count)
    have "syms_smp eqcn \<subseteq># syms_smp {#eqc#}" 
    proof -
      define nums where "nums = mset_set {0..<n}" 
      define arg where "arg t = (\<Sum>i\<in>#nums. syms_term (args t ! i))" for t :: "('f, nat \<times> 's) term" 
      have "syms_smp eqcn = (\<Sum>i\<in>#nums. syms_eqc {#args t ! i. t \<in># eqc#})" 
        unfolding  image_mset.compositionality o_def nums_def syms_smp_to_eqc *(2)
        by simp
      also have "\<dots> = (\<Sum>t\<in>#eqc. arg t)" unfolding arg_def
        unfolding syms_eqc_def image_mset.compositionality o_def 
        by (rule sum_mset.swap)
      finally have transform: "syms_smp eqcn = \<Sum>\<^sub># (image_mset arg eqc)" .

      have "?thesis \<longleftrightarrow> \<Sum>\<^sub># (image_mset arg eqc) \<subseteq># \<Sum>\<^sub># (image_mset syms_term eqc)" 
        unfolding transform unfolding syms_smp_def by simp
      also have "\<dots>" 
      proof -
        {
          fix t
          assume "t \<in># eqc"
          from *(1)[OF this] obtain ts where t: "t = Fun f ts" and len: "length ts = n" by (cases t, auto)
          have id: "mset ts = mset (map (\<lambda> i. ts ! i) [0..< length ts])" 
            by (intro arg_cong[of _ _ mset], rule nth_equalityI, auto)
          have "arg t = (\<Sum>i\<in>#mset_set {0..<length ts}. syms_term (ts ! i))" 
            unfolding arg_def t nums_def len by simp
          also have "\<dots> = (\<Sum>\<^sub># (image_mset syms_term (mset ts)))" 
            unfolding id 
            by (auto simp: image_mset.compositionality o_def)
          finally have "arg t \<subseteq># syms_term t" unfolding t by simp
        }
        thus ?thesis 
          by (induct eqc, auto intro: subset_mset.add_mono)
      qed
      finally show ?thesis .
    qed 
    thus "syms_smp (eqcn + mp) \<subseteq># syms_smp (add_mset eqc mp)" 
      unfolding syms_smp_def by auto
 
    have "\<Union> (\<Union>x\<in>set_mset eqcn. vars ` set_mset x) \<subseteq> \<Union> (vars ` set_mset eqc)" unfolding *(2)
    proof (clarsimp, goal_cases)
      case (1 x s i t)
      from *(1) 1 have "root t = Some (f,n)" by auto
      with 1 have "(x,s) \<in> vars t" by (cases t, auto)
      with 1 show ?case by auto
    qed
    thus "tvars_smp (mset2 (eqcn + mp)) \<subseteq> tvars_smp (mset2 (add_mset eqc mp))" 
      by force
  qed  
qed

definition measure_p :: "('f,'s) simple_pat_problem_ms \<Rightarrow> nat" where
  "measure_p p = max_depth_sort_p p * (max_dupl_p p * m + 1) + num_syms_p p" 

lemma measure_p_bound: assumes "finite_constructor_form_pat (mset3 p)" 
  shows "measure_p p \<le> card (dom C) * size p * (num_syms_p p + 1) * (m + 1)" 
proof -
  {
    assume "num_syms_p p \<noteq> 0" 
    from this[unfolded num_syms_p_def] obtain mp where mp: "mp \<in># p" and "num_syms_smp mp \<noteq> 0" by auto
    from this[unfolded num_syms_smp_def] obtain eqc t where eqc: "eqc \<in># mp" and t: "t \<in># eqc" and "num_syms t \<noteq> 0" 
      by auto
    from assms mp have "finite_constructor_form_mp (mset2 mp)" 
      by (auto simp: finite_constructor_form_pat_def)
    from this[unfolded finite_constructor_form_mp_def] eqc t obtain \<iota> where "t : \<iota> in \<T>(C,\<V> |` SS)" by auto
    hence "t \<cdot> \<sigma>g : \<iota> in \<T>(C)"
      by (metis \<sigma>g' \<sigma>g'_def \<sigma>g_def sorted_map_cong subst_has_same_type)
    then obtain t where "t : \<iota> in \<T>(C)" by auto
    then obtain f where "f \<in> dom C" by (induct, auto simp: fun_hastype_def)
    hence "card (dom C) \<noteq> 0" "size p \<noteq> 0" using finite_C mp by auto 
  } note non_triv_p = this  
  have "measure_p p \<le> (card (dom C) * size p) * (num_syms_p p * m + 1) + num_syms_p p" 
    unfolding measure_p_def
    by (intro add_right_mono mult_mono max_dupl_p_le_num_syms max_depth_sort_p_le_card_size assms, auto)
  also have "\<dots> \<le> (card (dom C) * size p) * (num_syms_p p * m + 1) + (card (dom C) * size p) * num_syms_p p" 
  proof (cases "num_syms_p p = 0")
    case False
    from non_triv_p[OF this] have "card (dom C) * size p \<noteq> 0" by auto
    thus ?thesis by (cases "card (dom C) * size p", auto)
  qed auto
  also have "\<dots> = (card (dom C) * size p) * (num_syms_p p * m + 1 + num_syms_p p)" 
    by (simp add: algebra_simps)
  also have "\<dots> \<le> (card (dom C) * size p) * ((num_syms_p p + 1) * (m + 1))" 
    by (rule mult_left_mono, auto)
  finally show "measure_p p \<le> card (dom C) * size p * (num_syms_p p + 1) * (m + 1)" 
    by (simp add: algebra_simps)
qed 


lemma measure_p_num_syms: assumes "max_depth_sort_p p \<le> max_depth_sort_p p'" 
  and "max_dupl_p p \<le> max_dupl_p p'" 
  and "num_syms_p p < num_syms_p p'" 
shows "measure_p p < measure_p p'" 
  unfolding measure_p_def
  by (intro add_le_less_mono mult_mono, insert assms, auto)


lemma spp_step_complexity_and_termination: 
  assumes "p \<Rightarrow>\<^sub>s\<^sub>s Pn" 
  and "finite_constructor_form_pat (mset3 p)" 
  and "pn \<in># Pn" 
shows "measure_p pn < measure_p p" 
  using assms
proof (induct)
  case *: (spp_simp mp mp' p)
  hence pn: "pn = add_mset mp' p" by simp
  let ?p = "add_mset mp p" 
  from * have fin: "finite_constructor_form_mp (mset2 mp)" 
    unfolding finite_constructor_form_pat_def by auto
  from num_syms_smp_step[OF *(1) fin]
  have n: "num_syms_p pn < num_syms_p ?p" unfolding pn by simp
  have d: "max_depth_sort_p pn \<le> max_depth_sort_p ?p" 
    unfolding pn
    apply simp
    apply (rule max_depth_sort_le)
    apply (rule mp_step_tvars)
    by fact
  from max_dupl_smp_step[OF *(1)] *
  have m: "max_dupl_p pn \<le> max_dupl_p ?p" by simp
  from d n m show ?case by (intro measure_p_num_syms, auto)
next
  case *: (spp_delete mp p)  
  hence pn: "pn = p" 
    and fin: "finite_constructor_form_mp (mset2 mp)" 
      unfolding finite_constructor_form_pat_def by auto
  let ?p = "add_mset mp p" 
  have d: "max_depth_sort_p pn \<le> max_depth_sort_p ?p" unfolding pn max_depth_sort_p_def by auto
  from *(1) have "mp \<noteq> {#}" by (cases, auto)
  from num_syms_smp_pos[OF fin this]
  have n: "num_syms_p pn < num_syms_p ?p" unfolding pn by simp
  have m: "max_dupl_p pn \<le> max_dupl_p ?p" unfolding pn by simp
  from d n m show ?case by (intro measure_p_num_syms, auto)
next
  case *: (spp_delete_large_sort n x \<iota> eq mp t p)
  define pd where "pd = mset (map mp [0..<Suc n])" 
  from *(5) have pn: "pn = p" by auto
  let ?p = "p + pd" 
  have m: "max_dupl_p p \<le> max_dupl_p ?p" unfolding max_dupl_p_def by auto
  have d: "max_depth_sort_p p \<le> max_depth_sort_p ?p" unfolding max_depth_sort_p_def by auto
  have "num_syms_p p < num_syms_p p + 1" by auto
  also have "\<dots> \<le> num_syms_p p + num_syms_p pd"
  proof (rule add_left_mono)
    have mem: "mp n \<in># pd" unfolding pd_def by auto
    from *(4) have "finite_constructor_form_mp (mset2 (mp n))" 
      by (auto simp: finite_constructor_form_pat_def)
    from *(1)[OF le_refl] num_syms_smp_pos[OF this]
    have "1 \<le> num_syms_smp (mp n)" by (cases "mp n", auto)
    thus "1 \<le> num_syms_p pd" using mem unfolding num_syms_p_def
      by (metis One_nat_def add_eq_0_iff_both_eq_0 less_Suc0 linorder_not_less multi_member_split sum_mset.insert)
  qed
  finally have n: "num_syms_p p < num_syms_p ?p" unfolding num_syms_p_def by auto
  from n m d have "measure_p p < measure_p (p + pd)" by (metis measure_p_num_syms)
  thus ?case unfolding pn pd_def by auto
next
  case *: (spp_inst x t p n)
  then obtain \<tau> where pn: "pn = image_mset (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>))) p" 
    and \<tau>: "\<tau> \<in> \<tau>s n x" using \<tau>s_list by auto
  from max_depth_sort_p_inst[OF *(1-2) \<tau> *(4)] *(5)
  have d: "max_depth_sort_p pn < max_depth_sort_p p" unfolding pn by auto
  have "num_syms_p pn = (\<Sum>mp\<in>#p. num_syms_smp (image_mset (image_mset (\<lambda>t. t \<cdot> \<tau>)) mp))" 
    unfolding num_syms_p_def pn image_mset.compositionality o_def by simp
  also have "\<dots> \<le> (\<Sum>mp\<in>#p. num_syms_smp mp + max_dupl_smp mp * m)"
    by (rule sum_mset_mono, rule num_syms_smp_\<tau>s[OF \<tau>])
  also have "\<dots> = num_syms_p p + max_dupl_p p * m" 
    unfolding sum_mset.distrib num_syms_p_def max_dupl_p_def sum_mset_distrib_right by auto
  finally have n: "num_syms_p pn \<le> num_syms_p p + max_dupl_p p * m" .
  have m: "max_dupl_p pn \<le> max_dupl_p p" 
    unfolding max_dupl_p_def pn image_mset.compositionality o_def
  proof (rule sum_mset_mono, rule max_dupl_smp_\<tau>s[OF \<tau>], goal_cases)
    case (1 mp)
    thus ?case using *(3) by fastforce
  qed
  show ?case unfolding measure_p_def
    by (intro measure_expr_decrease n m d)
next
  case *: (spp_split mp x t eqc mp' p)
  let ?p = "add_mset mp p" 
  from *(1,5) have d: "max_depth_sort_p pn \<le> max_depth_sort_p ?p" 
    by (auto, auto intro!: max_depth_sort_le)
  from *(1,5) have m: "max_dupl_p pn \<le> max_dupl_p ?p" 
    by (auto, auto intro!: max_dupl_mono)
  have n: "num_syms_p pn < num_syms_p ?p"
  proof (cases eqc)
    case add
    from *(1,5) add
    show ?thesis by auto (auto intro!: num_syms_subset)
  next
    case empty
    with *(3) obtain eq2 mp2 where mp': "mp' = add_mset eq2 mp2" by (cases mp', auto)
    from *(1,4) mp' have eq2: "eq2 \<noteq> {#}" 
      unfolding finite_constructor_form_pat_def finite_constructor_form_mp_def by auto
    from *(1,5) mp' eq2 
    show ?thesis by auto (cases eq2, auto intro!: num_syms_subset)
  qed
  from d n m show ?case by (intro measure_p_num_syms, auto)
qed auto

(* ************************************* 
     non-deterministic algorithm  
   ************************************* *)
text \<open>snd = Simplified Non-Deterministic\<close>
inductive_set snd_step :: "('f,'s)simple_pat_problem_ms rel" (\<open>\<Rightarrow>\<^sub>s\<^sub>n\<^sub>d\<close>)
  where snd_step: "p \<Rightarrow>\<^sub>s\<^sub>s Q \<Longrightarrow> finite_constructor_form_pat (mset3 p) \<Longrightarrow> q \<in># Q \<Longrightarrow> (p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" 

lemma snd_step_measure: assumes "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d"
  shows "measure_p p > measure_p q"
  using assms
proof (cases)
  case (snd_step Q)
  thus ?thesis using spp_step_complexity_and_termination[of p Q q] by auto
qed

lemma snd_bound_steps: assumes "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d ^^ n" 
  shows "measure_p q + n \<le> measure_p p" 
  using steps_bound[of "\<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" measure_p p q n, OF snd_step_measure assms]
  by auto

lemma snd_steps_bound: assumes steps: "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d ^^ n" 
  and "finite_constructor_form_pat (mset3 p)" 
shows "n \<le> card (dom C) * size p * (num_syms_p p + 1) * (m + 1)" 
proof -
  from snd_bound_steps[OF steps] 
  have "n \<le> measure_p p" by auto
  also have "\<dots> \<le> card (dom C) * size p * (num_syms_p p + 1) * (m + 1)" 
    by (rule measure_p_bound[OF assms(2)])
  finally show ?thesis .
qed

lemma SN_snd_step: "SN \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" 
proof (rule SN_subset[OF SN_inv_image[OF SN_nat_gt]])
  show "\<Rightarrow>\<^sub>s\<^sub>n\<^sub>d \<subseteq> inv_image {(a, b). b < a} measure_p" using snd_step_measure by auto
qed

lemma snd_step_size: assumes "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d"
  shows "size p \<ge> size q"
  using assms
proof (cases)
  case (snd_step Q)
  thus ?thesis using spp_step_ms_size[of p Q q] by auto
qed

lemma snd_step_finite_constructor_form_pat: assumes "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d"
shows "finite_constructor_form_pat (mset3 q)" 
  using assms
proof (cases)
  case (snd_step Q)
  thus ?thesis using spp_step_ms[of p Q] by auto
qed

lemma snd_step_completeness: assumes "p \<notin> NF \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" 
  shows "simple_pat_complete C SS (mset3 p) \<longleftrightarrow> (\<forall> q. (p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d \<longrightarrow> simple_pat_complete C SS (mset3 q))"
  (is "?left = ?right")
proof -
  from assms obtain q where "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" by auto
  then obtain Q where "p \<Rightarrow>\<^sub>s\<^sub>s Q" and fin: "finite_constructor_form_pat (mset3 p)" 
    by cases auto
  from spp_step_ms[OF this] snd_step[OF this]
  have oneDir: "?right \<Longrightarrow> ?left" by auto
  {
    assume "\<not> ?right" 
    then obtain q where "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" and not: "\<not> simple_pat_complete C SS (mset3 q)" by auto
    from this(1) obtain Q where "p \<Rightarrow>\<^sub>s\<^sub>s Q" and "q \<in># Q" by cases auto
    from spp_step_ms[OF this(1) fin] this(2) not
    have "\<not> ?left" by auto
  }
  with oneDir show ?thesis by auto
qed

lemma snd_steps: assumes "(p,q) \<in> (\<Rightarrow>\<^sub>s\<^sub>n\<^sub>d)\<^sup>*" 
  shows "size p \<ge> size q" 
  "simple_pat_complete C SS (mset3 p) \<Longrightarrow> simple_pat_complete C SS (mset3 q)" 
  "finite_constructor_form_pat (mset3 p) \<Longrightarrow> finite_constructor_form_pat (mset3 q)" 
  using assms
proof (atomize(full), induct, force)
  case (step q r)
  from step(2) have "q \<notin> NF \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" by auto
  from snd_step_completeness[OF this] 
    snd_step_finite_constructor_form_pat[OF step(2)]
    snd_step_size[OF step(2)]
    step(2-3)
  show ?case by auto
qed

lemma snd_steps_complete: assumes "\<not> simple_pat_complete C SS (mset3 p)"
  shows "\<exists> q. (p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d\<^sup>! \<and> \<not> simple_pat_complete C SS (mset3 q)" 
  using assms
proof (induct p rule: SN_induct[OF SN_snd_step])
  case (1 p)
  show ?case
  proof (cases "p \<in> NF \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d")
    case True
    thus ?thesis using 1 by auto
  next
    case False
    from snd_step_completeness[OF False] 1 obtain q where step: "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" 
      and q: "\<not> simple_pat_complete C SS (mset3 q)" by auto 
    from 1(1)[OF this] step show ?thesis by blast
  qed
qed

lemma simple_pat_complete_via_snd_step_NFs: "simple_pat_complete C SS (mset3 p) \<longleftrightarrow> 
  (\<forall> q. (p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d\<^sup>! \<longrightarrow> simple_pat_complete C SS (mset3 q))"
  using snd_steps_complete[of p] snd_steps(2)[of p] by blast

lemma snd_steps_NF_fvf_small_sort: assumes "finite_constructor_form_pat (mset3 p)" 
  and "(p,q) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d\<^sup>!" 
shows "\<forall> mp \<in># q. \<forall> eqc \<in># mp. \<forall> t \<in># eqc. \<exists> x \<iota>. t = Var (x,\<iota>) \<and> card_of_sort C \<iota> \<le> size p"
proof -
  from snd_steps[of p q] assms 
  have fin: "finite_constructor_form_pat (mset3 q)" and 
    size: "size p \<ge> size q" by blast+
  from assms have "q \<in> NF (\<Rightarrow>\<^sub>s\<^sub>n\<^sub>d)" by auto
  hence "\<not> (\<exists> Q. q \<Rightarrow>\<^sub>s\<^sub>s Q \<and> Q \<noteq> {#})" using snd_step[OF _ fin] by blast
  from NF_spp_step_fvf_with_small_card[OF fin this] size show ?thesis by fastforce
qed

text \<open>Major soundness properties of non-deterministic algorithm to transform FCF into FVF\<close>
lemmas snd_step_combined = 
  snd_steps_bound \<comment> \<open>complexity\<close>
  SN_snd_step     \<comment> \<open>termination\<close>
  snd_steps_NF_fvf_small_sort \<comment> \<open>normal forms are in finite variable form with small sorts\<close>
  simple_pat_complete_via_snd_step_NFs \<comment> \<open>equivalence: complete iff all normal forms are complete\<close>

(* ************************************* 
     algorithm with don't-care non-determinism, 
     i.e., which can be implemented deterministically;
     this algorithm allows to invoke decision procedure for problems in finite variable form
   ************************************* *)

inductive_set spp_det_step_ms :: "('f,'s)simple_pat_problem_ms multiset rel" (\<open>\<Rrightarrow>\<^sub>s\<^sub>s\<close>)
  where spp_non_det_step: "p \<Rightarrow>\<^sub>s\<^sub>s P' \<Longrightarrow> finite_constructor_form_pat (mset3 p) \<Longrightarrow> (add_mset p P, P' + P) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" 
  | spp_non_det_fail: "P \<noteq> {#} \<Longrightarrow> (add_mset {#} P, {#{#}#}) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" 
  (* for finite-variable-form, we allow to just decide solvability *)
  | spp_fvf_succ: "(\<And> t. t \<in># \<Sum>\<^sub># (image_mset \<Sum>\<^sub># p) \<Longrightarrow> is_Var t) \<Longrightarrow> simple_pat_complete C SS (mset3 p)
      \<Longrightarrow> (add_mset p P, P) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" 
  | spp_fvf_fail: "(\<And> t. t \<in># \<Sum>\<^sub># (image_mset \<Sum>\<^sub># p) \<Longrightarrow> is_Var t) \<Longrightarrow> \<not> simple_pat_complete C SS (mset3 p)
      \<Longrightarrow> finite_constructor_form_pat (mset3 p) \<Longrightarrow> p \<noteq> {#} \<Longrightarrow> (add_mset p P, {#{#}#}) \<in> \<Rrightarrow>\<^sub>s\<^sub>s" 
  
definition spp_det_prob :: "('f,'s)simple_pat_problem_ms multiset \<Rightarrow> bool" where
  "spp_det_prob P = (\<forall> p \<in># P. finite_constructor_form_pat (mset3 p))" 

definition spp_pat_complete :: "('f,'s)simple_pat_problem_ms multiset \<Rightarrow> bool" where
  "spp_pat_complete P = (\<forall> p \<in># P. simple_pat_complete C SS (mset3 p))" 

lemma spp_det_prob_add[simp]: "spp_det_prob (add_mset p P) = 
  (finite_constructor_form_pat (mset3 p) \<and> spp_det_prob P)" 
  unfolding spp_det_prob_def by simp

lemma spp_det_prob_plus[simp]: "spp_det_prob (P + P') = 
  (spp_det_prob P \<and> spp_det_prob P')" 
  unfolding spp_det_prob_def by auto

lemma spp_det_prob_empty[simp]: "spp_det_prob {#}" 
  by (simp add: spp_det_prob_def)

lemma spp_det_step_ms: "(P,P') \<in> \<Rrightarrow>\<^sub>s\<^sub>s \<Longrightarrow> 
  spp_pat_complete P = spp_pat_complete P' \<and> (spp_det_prob P \<longrightarrow> spp_det_prob P')"
proof (induct rule: spp_det_step_ms.induct)
  case *: (spp_non_det_step p P' P)
  from spp_step_ms[OF *(1), folded spp_det_prob_def] *(2)
  show ?case by (auto simp: spp_pat_complete_def)
next
  case *: (spp_non_det_fail P)
  show ?case using detect_unsat_spp by (simp add: finite_constructor_form_pat_def spp_pat_complete_def)
next
  case (spp_fvf_succ p P)
  thus ?case by (auto simp: spp_pat_complete_def)
next
  case (spp_fvf_fail p P)
  thus ?case using detect_unsat_spp by (simp add: finite_constructor_form_pat_def spp_pat_complete_def)
qed

lemma spp_det_steps_ms: "(P,P') \<in> \<Rrightarrow>\<^sub>s\<^sub>s\<^sup>* \<Longrightarrow> 
  spp_pat_complete P = spp_pat_complete P' \<and> (spp_det_prob P \<longrightarrow> spp_det_prob P')"
  by (induct rule: rtrancl_induct, insert spp_det_step_ms, auto)

lemma SN_spp_det_step: "SN \<Rrightarrow>\<^sub>s\<^sub>s" 
proof (rule SN_subset)
  show "\<Rrightarrow>\<^sub>s\<^sub>s \<subseteq> (mult (measure measure_p))^-1" 
  proof (standard, simp, goal_cases)
    case (1 P P')
    thus ?case
    proof (induct rule: spp_det_step_ms.induct)
      case *: (spp_non_det_step p P' P)
      from spp_step_complexity_and_termination[OF *(1-2)] show ?case
        by (simp add: add_many_mult)
    next
      case *: (spp_non_det_fail P)
      then obtain p P' where P: "P = add_mset p P'" by (cases P, auto)
      show ?case unfolding P by (simp add: subset_implies_mult)
    next
      case (spp_fvf_succ p P)
      show ?case by (simp add: subset_implies_mult)
    next
      case *: (spp_fvf_fail p P)      
      then obtain mp p' where p: "p = add_mset mp p'" by (cases p, auto)
      with *(2) have "mp \<noteq> {#}" unfolding simple_pat_complete_def simple_match_complete_wrt_def by auto
      then obtain eq mp' where mp: "mp = add_mset eq mp'" by (cases mp, auto)
      with *(3,4) have eq: "eq \<noteq> {#}" 
        unfolding finite_constructor_form_pat_def finite_constructor_form_mp_def mp p
        by auto
      have p: "measure_p p > 0" unfolding measure_p_def p num_syms_p_def num_syms_smp_def mp 
        using eq by (cases eq, auto)
      have e: "measure_p {#} = 0" unfolding measure_p_def p num_syms_p_def max_depth_sort_p_def
        max_dupl_p_def by auto
      from p e have "({#}, p) \<in> measure measure_p" by auto
      thus ?case
        by (metis add_cancel_left_left add_mset_eq_single empty_not_add_mset multi_member_split
            one_step_implies_mult union_single_eq_member)
    qed
  qed
  show "SN ((mult (measure measure_p))\<inverse>)" 
    by (rule wf_imp_SN, simp add: wf_mult[OF wf_measure])
qed

lemma NF_spp_det_step: assumes "spp_det_prob P" 
  and "P \<in> NF \<Rrightarrow>\<^sub>s\<^sub>s" 
shows "P = {#} \<or> P = {#{#}#}"
proof (rule ccontr)
  assume contr: "\<not> ?thesis" 
  from assms(2) have NF: "(P,P') \<in> \<Rrightarrow>\<^sub>s\<^sub>s \<Longrightarrow> False" for P' by auto
  from contr obtain p P2 where P: "P = add_mset p P2" and disj: "p \<noteq> {#} \<or> P2 \<noteq> {#}" by (cases P, auto)
  from assms[unfolded P] have fin: "finite_constructor_form_pat (mset3 p)" by auto 
  show False
  proof (cases "p = {#}")
    case True
    with disj have P2: "P2 \<noteq> {#}" by auto
    show False 
      apply (rule NF)
      apply (unfold P True)
      by (rule spp_non_det_fail[OF P2])
  next
    case False
    have "\<nexists>P. p \<Rightarrow>\<^sub>s\<^sub>s P \<and> P \<noteq> {#}" using NF[unfolded P, OF spp_non_det_step[OF _ fin]] by auto
    note fvf = normal_form_spp_step_fvf[OF fin this]
    show ?thesis
    proof (cases "simple_pat_complete C SS (mset3 p)")
      case True
      show False
        by (rule NF, unfold P, rule spp_fvf_succ[OF _ True], insert fvf, auto)
    next
      case unsat: False
      show False
        by (rule NF, unfold P, rule spp_fvf_fail[OF _ unsat fin False], insert fvf, auto)
    qed
  qed
qed

lemma decision_procedure_spp_det:
  assumes  valid_input: "spp_det_prob P" and NF: "(P,Q) \<in> \<Rrightarrow>\<^sub>s\<^sub>s\<^sup>!"
  shows "Q = {#} \<and> spp_pat_complete P \<comment> \<open>either the result is {} and input P is complete\<close>
  \<or> Q = {#{#}#} \<and> \<not> spp_pat_complete P \<comment> \<open>or the result = bot and P is not complete\<close>" 
proof -
  from NF have steps: "(P,Q) \<in> \<Rrightarrow>\<^sub>s\<^sub>s\<^sup>*" and Q: "Q \<in> NF \<Rrightarrow>\<^sub>s\<^sub>s" by auto
  from spp_det_steps_ms[OF steps] valid_input
  have equiv: "spp_pat_complete P = spp_pat_complete Q" and valid_out: "spp_det_prob Q" by auto
  from NF_spp_det_step[OF valid_out Q]
  show ?thesis
  proof
    assume "Q = {#}" 
    thus ?thesis unfolding equiv by (simp add: spp_pat_complete_def)
  next
    assume "Q = {#{#}#}"
    thus ?thesis unfolding equiv using detect_unsat_spp by (simp add: spp_pat_complete_def)
  qed
qed 
    
text \<open>A combined complexity approximation\<close>

text \<open>Conversion from pattern problems in finite constructor form to their simplified representation,
  performed on multiset-representation\<close>
definition fcf_mp_to_smp :: "('f,'v,'s)match_problem_mset \<Rightarrow> ('f,'s)simple_match_problem_ms" where
  "fcf_mp_to_smp mp = (let xs = mset_set ((the_Var o snd) ` set_mset mp)
     in image_mset (\<lambda> x. image_mset fst (filter_mset (\<lambda> (t,l). l = Var x) mp)) xs)" 

lemma fcf_mp_to_smp: assumes fcf: "finite_constr_form_mp C (set_mset mp)" 
  and no_fail: "\<not> match_fail mp" 
  and wf_match: "wf_match (set_mset mp)" 
  shows "finite_constructor_form_mp (mset2 (fcf_mp_to_smp mp))" 
  unfolding finite_constructor_form_mp_def
proof
  fix seqc
  assume "seqc \<in> mset2 (fcf_mp_to_smp mp)" 
  from this[unfolded fcf_mp_to_smp_def Let_def, simplified]
  obtain x tx eqc where tx: "tx \<in># mp" and x: "x = the_Var (snd tx)"  
    and eqc: "eqc = image_mset fst {#(t, l) \<in># mp. l = Var x#}" 
    and seqc: "seqc = set_mset eqc" by force
  from fcf[unfolded finite_constr_form_mp_def, rule_format, of "fst tx" "snd tx"] tx x
  obtain t \<iota> where tx: "(t,Var x) \<in># mp" and fin: "finite_sort C \<iota>" and t: "t : \<iota> in \<T>(C,\<V>)" 
    by (cases tx, auto)
  from tx eqc seqc have seqc1: "seqc \<noteq> {}" by auto
  {
    fix t'
    assume "t' \<in> seqc" 
    from this[unfolded seqc eqc] have t': "(t',Var x) \<in># mp" by auto
    have "\<T>(C,\<V>) t' = \<T>(C,\<V>) t" 
    proof (rule ccontr)
      let ?p1 = "(t,Var x)" 
      let ?p2 = "(t',Var x)" 
      define mp' where "mp' = mp - {# ?p1, ?p2 #}" 
      assume "\<not> ?thesis" 
      hence "?p1 \<noteq> ?p2" by auto
      with tx t' have "mp = add_mset ?p1 (add_mset ?p2 mp')" 
        unfolding mp'_def using multi_member_split by fastforce
      from match_clash_sort[of t t' x mp', folded this] \<open>\<not> ?thesis\<close> no_fail
      show False by auto
    qed
    with t have t'i: "t' : \<iota> in \<T>(C,\<V>)" unfolding hastype_def by auto
    from wf_match[unfolded wf_match_def tvars_match_def] t' have "vars t' \<subseteq> SS" by force
    with t'i have "t' : \<iota> in \<T>(C,\<V> |` SS)" 
      by (meson hastype_in_Term_mono_right hastype_in_Term_restrict_vars restrict_map_mono_right)
  }
  with fin seqc1
  show "seqc \<noteq> {} \<and> (\<exists>\<iota>. finite_sort C \<iota> \<and> (\<forall>t\<in>seqc. t : \<iota> in \<T>(C,\<V> |` SS)))" 
    by auto
qed

definition fcf_pat_to_spat :: "('f,'v,'s)pat_problem_mset \<Rightarrow> ('f,'s)simple_pat_problem_ms" where
  "fcf_pat_to_spat = image_mset fcf_mp_to_smp" 

lemma fcf_pat_to_spat: assumes fcf: "finite_constr_form_pat C (pat_mset p)" 
  and NF: "p \<in> NF ( \<Rightarrow>\<^sub>n\<^sub>d )" 
  and wf_pat: "wf_pat (pat_mset p)" 
shows "finite_constructor_form_pat (mset3 (fcf_pat_to_spat p))" 
  unfolding finite_constructor_form_pat_def
proof
  fix ssmp
  assume "ssmp \<in> mset3 (fcf_pat_to_spat p)" 
  then obtain smp where "smp \<in># fcf_pat_to_spat p" and ssmp: "ssmp = mset2 smp" by auto
  from this[unfolded fcf_pat_to_spat_def] obtain mp where mp: "mp \<in># p" and 
    smp: "smp = fcf_mp_to_smp mp" by auto
  with ssmp have ssmp: "ssmp = mset2 (fcf_mp_to_smp mp)" by auto
  show "finite_constructor_form_mp ssmp" unfolding ssmp
  proof (rule fcf_mp_to_smp)
    from fcf[unfolded finite_constr_form_pat_def] mp
    show "finite_constr_form_mp C (mp_mset mp)" by auto
    from wf_pat[unfolded wf_pat_def] mp 
    show "wf_match (mp_mset mp)" by auto
    show "\<not> match_fail mp" 
    proof
      from mp obtain p' where p: "p = add_mset mp p'" by (metis mset_add)
      assume "match_fail mp" 
      from pat_remove_mp[OF this, of p', folded p]
      have "p \<Rightarrow>\<^sub>m {#p'#}" .
      hence "(p,p') \<in> \<Rightarrow>\<^sub>n\<^sub>d" by (intro pp_nd_step_mset.intros, auto)
      with NF show False by auto
    qed
  qed
qed

lemma wf_pat_nd_step: "(p,q) \<in> \<Rightarrow>\<^sub>n\<^sub>d \<Longrightarrow> wf_pat (pat_mset p) \<Longrightarrow> wf_pat (pat_mset q)" 
  by (smt (verit, ccfv_SIG) comp_def image_iff p_step_mset_imp_set pp_nd_step_mset.cases
      pp_step_wf)

lemma sum_smp_fcf_mp_to_smp_is_image_fst: 
  assumes "finite_constr_form_mp C (mp_mset mp)"
  shows "sum_mset (fcf_mp_to_smp mp) = image_mset fst mp"
  using assms
proof (induct "size mp" arbitrary: mp rule: less_induct)
  case (less mp)
  show ?case
  proof (cases mp)
    case empty
    thus ?thesis by (auto simp: fcf_mp_to_smp_def)
  next
    case (add tx mp')
    from less(2)[unfolded finite_constr_form_mp_def add]
    obtain t x where tx: "tx = (t,Var x)" by (cases tx; cases "snd tx"; auto)
    define mp1 where "mp1 = filter_mset (\<lambda> ty. snd ty = Var x) mp" 
    from tx add have tx: "(t, Var x) \<in># mp1" by (auto simp: mp1_def)
    define mp2 where "mp2 = filter_mset (Not o (\<lambda> ty. snd ty = Var x)) mp" 
    define ys where "ys = mset_set {the_Var (snd y) |. y \<in> mp_mset mp2}" 
    from tx have x: "x \<in> {the_Var (snd x) |. x \<in> mp_mset mp1 \<union> mp_mset mp2}" by force
    from less(2) have fcf: "finite_constr_form_mp C (mp_mset mp2)" 
      unfolding finite_constr_form_mp_def mp2_def by auto
    have mp: "mp = mp1 + mp2" unfolding mp1_def mp2_def by auto
    have x2: "x \<notin> ((the_Var \<circ> snd) ` mp_mset mp2)" unfolding mp2_def 
      using less(2)[unfolded finite_constr_form_mp_def]
      by auto
    hence xys: "x \<notin># ys" unfolding ys_def by auto
    have "(the_Var \<circ> snd) ` mp_mset mp = 
        insert x (((the_Var \<circ> snd) ` mp_mset mp2))" 
      using x unfolding mp by (auto simp: mp1_def)
    from arg_cong[OF this, of mset_set]
    have xs: "mset_set ((the_Var \<circ> snd) ` mp_mset mp) = add_mset x (mset_set (((the_Var \<circ> snd) ` mp_mset mp2)))" 
      using x2 by auto
    have "fcf_mp_to_smp mp = add_mset (image_mset fst mp1)
     {#image_mset fst {#(t, l) \<in># mp. l = Var y#}. y \<in># ys#}" 
      unfolding fcf_mp_to_smp_def xs Let_def ys_def
      by (auto simp add: mp1_def intro!: arg_cong[of _ _ "image_mset fst"]) (induct mp, auto)
    also have "{#image_mset fst {#(t, l) \<in># mp. l = Var y#}. y \<in># ys#} =
        {#image_mset fst {#(t, l) \<in># mp2. l = Var y#}. y \<in># ys#}" 
      unfolding mp using xys
    proof (induct ys)
      case (add y ys)
      hence "x \<noteq> y" by auto
      hence "{#(t, l) \<in># mp1. l = Var y#} = {#}" unfolding mp1_def by (induct mp, auto)
      with add show ?case by auto
    qed auto
    also have "\<dots> = fcf_mp_to_smp mp2" unfolding fcf_mp_to_smp_def Let_def ys_def by auto
    finally have "sum_mset (fcf_mp_to_smp mp) = 
       image_mset fst mp1 + sum_mset (fcf_mp_to_smp mp2)" 
      by (auto simp: num_syms_smp_def)
    also have "sum_mset (fcf_mp_to_smp mp2) = image_mset fst mp2" using less(1)[OF _ fcf]
      unfolding mp using tx by (cases mp1, auto)
    finally show ?thesis unfolding mp by auto
  qed
qed

lemma num_syms_smp_fcf_mp_to_smp_is_meas_tsymbols: 
  assumes "finite_constr_form_mp C (mp_mset mp)"
  shows "num_syms_smp (fcf_mp_to_smp mp) = num_tsyms_mp mp"
proof -
  let ?mp = "fcf_mp_to_smp mp" 
  have "num_syms_smp ?mp = (\<Sum>x\<in>#mp. num_syms (fst x))" 
    unfolding num_syms_smp_def sum_smp_fcf_mp_to_smp_is_image_fst[OF assms] image_mset.compositionality o_def
    by simp
  also have "\<dots> = num_tsyms_mp mp" 
    unfolding num_tsyms_mp_def o_def by simp
  finally show ?thesis .
qed


lemma num_syms_p_fcf_pat_to_spat_is_meas_tsymbols: 
  assumes "finite_constr_form_pat C (pat_mset p)"
  shows "num_syms_p (fcf_pat_to_spat p) = meas_tsymbols p" 
  using num_syms_smp_fcf_mp_to_smp_is_meas_tsymbols assms
  unfolding num_syms_p_def meas_tsymbols_def finite_constr_form_pat_def fcf_pat_to_spat_def
  unfolding image_mset.compositionality o_def
  by (metis image_eqI image_mset_cong)

lemma measure_pat_poly_to_measure_p:
  assumes "finite_constr_form_pat C (pat_mset p)"
    and "finite_constructor_form_pat (mset3 (fcf_pat_to_spat p))" 
    and c: "card (dom C) * size p \<le> c" 
  shows "measure_p (fcf_pat_to_spat p) \<le> measure_pat_poly c p" 
proof -
  show ?thesis 
    unfolding measure_p_def measure_pat_poly_def
    unfolding num_syms_p_fcf_pat_to_spat_is_meas_tsymbols[OF assms(1)]
  proof (intro add_mono le_refl mult_mono)  
    from max_depth_sort_p_le_card_size[OF assms(2)] c
    show "max_depth_sort_p (fcf_pat_to_spat p) \<le> c + meas_diff p" 
      unfolding fcf_pat_to_spat_def by simp
    have "max_dupl_p (fcf_pat_to_spat p) = meas_dupl p" 
      unfolding meas_dupl_def max_dupl_p_def fcf_pat_to_spat_def image_mset.compositionality o_def
    proof (intro arg_cong[of _ _ sum_mset] image_mset_cong)
      fix mp
      assume "mp \<in># p"
      with assms[unfolded finite_constr_form_pat_def] 
      have fcf: "finite_constr_form_mp C (mp_mset mp)" by auto
      have "\<Union> (\<Union> ((`) vars ` mset2 (fcf_mp_to_smp mp)))
        = \<Union> (vars ` (set_mset (\<Sum>\<^sub># (fcf_mp_to_smp mp))))" by auto
      also have "\<dots> = \<Union> (vars ` fst ` set_mset mp)" unfolding 
          sum_smp_fcf_mp_to_smp_is_image_fst[OF fcf] by auto
      also have "\<dots> = tvars_match (mp_mset mp)" 
        unfolding tvars_match_def o_def by auto
      finally have id1: "\<Union> (\<Union> ((`) vars ` mset2 (fcf_mp_to_smp mp))) = tvars_match (mp_mset mp)" .
      show "max_dupl_smp (fcf_mp_to_smp mp) = max_dupl_mp mp" 
        unfolding max_dupl_smp_def max_dupl_mp_def id1 
        unfolding image_mset.compositionality o_def
        unfolding sum_smp_fcf_mp_to_smp_is_image_fst[OF fcf]
      proof (intro arg_cong[of _ _ Max] arg_cong[of _ _ "insert 0"] image_cong refl) 
        fix x 
        show "(\<Sum>t\<in>#image_mset fst mp. count (syms_term t) (Inl x)) = (\<Sum>tl\<in>#mp. count (syms_term (fst tl)) (Inl x))" 
          by (induct mp, auto)
      qed
    qed
    thus "max_dupl_p (fcf_pat_to_spat p) \<le> meas_dupl p" by simp
  qed auto
qed


theorem complexity_combined: fixes p :: "('f,'v,'s)pat_problem_mset" 
  assumes impr: improved "infinite (UNIV :: 'v set)" 
    and wf: "wf_pat (pat_mset p)" 
    and phase1: "(p,p1) \<in> \<Rightarrow>\<^sub>n\<^sub>d ^^ n1" "(p,p1) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>!"  
    and translation: "p1' = fcf_pat_to_spat p1" 
    and phase2: "(p1',p2) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d ^^ n2" 
  shows "n1 + n2 + num_syms_p p2 \<le> (card (dom C) * size p + num_syms_pat p) * (num_syms_pat p * m + 2)" 
    "size p2 \<le> size p"
    "p2 \<in> NF \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d \<Longrightarrow> mp \<in># p2 \<Longrightarrow> eqc \<in># mp \<Longrightarrow> t \<in># eqc \<Longrightarrow> (x,\<iota>) \<in> vars t \<Longrightarrow> card_of_sort C \<iota> \<le> size p" 
proof -
  define c where "c = card (dom C) * size p"
  note nd = nd_step_improved[OF impr wf] 
  from nd(2)[OF phase1(1), of c] 
  have n1: "measure_pat_poly c p1 + n1 \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" .
  from phase1(2) have NF: "p1 \<in> NF (\<Rightarrow>\<^sub>n\<^sub>d)" by auto
  from phase1 have star: "(p,p1) \<in> \<Rightarrow>\<^sub>n\<^sub>d\<^sup>*" by auto
  from nd_steps_le_size[OF star] 
  have pp1: "size p1 \<le> size p" and c: "card (dom C) * size p1 \<le> c" unfolding c_def by auto
  from pp1 have p1'p: "size p1' \<le> size p" unfolding translation fcf_pat_to_spat_def by auto
  from nd(3)[OF phase1(2)] 
  have fcf: "finite_constr_form_pat C (pat_mset p1)" by auto
  from star wf have "wf_pat (pat_mset p1)" using wf_pat_nd_step by (rule rtrancl_induct)
  from fcf_pat_to_spat[OF fcf NF this, folded translation]
  have fcf': "finite_constructor_form_pat (mset3 p1')" .
  from measure_pat_poly_to_measure_p[OF fcf, folded translation, OF fcf' c] n1
  have "measure_p p1' + n1 \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" 
    by auto
  with snd_bound_steps[OF phase2(1)]
  have "measure_p p2 + n2 + n1 \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" by auto
  moreover have "num_syms_p p2 \<le> measure_p p2" unfolding measure_p_def by auto
  ultimately show "n1 + n2 + num_syms_p p2 \<le> (c + num_syms_pat p) * (num_syms_pat p * m + 2)" by auto
  from phase2 have "(p1',p2) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d\<^sup>*" by (rule relpow_imp_rtrancl)
  with fcf' have "size p2 \<le> size p1'" by (metis snd_steps(1))
  with p1'p show "size p2 \<le> size p" by simp
  
  assume NF: "p2 \<in> NF \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d" and mp: "mp \<in># p2" and e: "eqc \<in># mp" and t: "t \<in># eqc" and x: "(x,\<iota>) \<in> vars t" 
  from NF phase2 have "(p1',p2) \<in> \<Rightarrow>\<^sub>s\<^sub>n\<^sub>d\<^sup>!"
    by (meson normalizability_I relpow_imp_rtrancl)
  from snd_steps_NF_fvf_small_sort[OF fcf' this, rule_format, OF mp e t] x
  have "card_of_sort C \<iota> \<le> size p1'" by auto
  also have "\<dots> \<le> size p" by fact
  finally show "card_of_sort C \<iota> \<le> size p" .
qed
end

end