section \<open>Computing Nonempty and Infinite sorts\<close>

text \<open>This theory provides two algorithms, which both take a description of a set of sorts with
  their constructors. The first algorithm computes the set of sorts that are nonempty, i.e., those
  sorts that are inhabited by ground terms; 
  and the second algorithm computes the set of sorts that are infinite,
  i.e., where one can build arbitrary large ground terms.\<close>

theory Compute_Nonempty_Infinite_Sorts
  imports 
    Sorted_Terms.Sorted_Terms
    LP_Duality.Minimum_Maximum
    Matrix.Utility
begin

subsection \<open>Deciding the nonemptyness of all sorts under consideration\<close>

function compute_nonempty_main :: "'\<tau> set \<Rightarrow> (('f \<times> '\<tau> list) \<times> '\<tau>) list \<Rightarrow> '\<tau> set" where
  "compute_nonempty_main ne ls = (let rem_ls = filter (\<lambda> f. snd f \<notin> ne) ls in
     case partition (\<lambda> ((_,args),_). set args \<subseteq> ne) rem_ls of
      (new, rem) \<Rightarrow> if new = [] then ne else compute_nonempty_main (ne \<union> set (map snd new)) rem)"
  by pat_completeness auto

termination
proof (relation "measure (length o snd)", goal_cases)
  case (2 ne ls rem_ls new rem)   
  have "length new + length rem = length rem_ls" 
    using 2(2) sum_length_filter_compl[of _ rem_ls] by (auto simp: o_def)
  with 2(3) have "length rem < length rem_ls" by (cases new, auto)
  also have "\<dots> \<le> length ls" using 2(1) by auto
  finally show ?case by simp
qed simp

declare compute_nonempty_main.simps[simp del]

definition compute_nonempty_sorts :: "(('f \<times> '\<tau> list) \<times> '\<tau>) list \<Rightarrow> '\<tau> set" where
  "compute_nonempty_sorts Cs = compute_nonempty_main {} Cs" 

lemma compute_nonempty_sorts:  
  assumes "distinct (map fst Cs)" (* no conflicting asssignments in list-representation *)
  and "map_of Cs = C" (* list-representation corresponds to function representation *)
shows "compute_nonempty_sorts Cs = {\<tau>. \<exists> t :: ('f,'v)term. t : \<tau> in \<T>(C,\<emptyset>)}" (is "_ = ?NE")
proof -
  let ?TC = "\<T>(C,(\<emptyset> :: 'v \<Rightarrow> _))" 
  have "ne \<subseteq> ?NE \<Longrightarrow> set ls \<subseteq> set Cs \<Longrightarrow> snd ` (set Cs - set ls) \<subseteq> ne \<Longrightarrow>
    compute_nonempty_main ne ls = ?NE" for ne ls
  proof (induct ne ls rule: compute_nonempty_main.induct)
    case (1 ne ls)
    note ne = 1(2)
    define rem_ls where "rem_ls = filter (\<lambda> f. snd f \<notin> ne) ls" 
    have rem_ls: "set rem_ls \<subseteq> set Cs"
       "snd ` (set Cs - set rem_ls) \<subseteq> ne" 
      using 1(2-) by (auto simp: rem_ls_def)
    obtain new rem where part: "partition (\<lambda>((f, args), target). set args \<subseteq> ne) rem_ls = (new,rem)" by force
    have [simp]: "compute_nonempty_main ne ls = (if new = [] then ne else compute_nonempty_main (ne \<union> set (map snd new)) rem)" 
      unfolding compute_nonempty_main.simps[of ne ls] Let_def rem_ls_def[symmetric] part by auto
    have new: "set (map snd new) \<subseteq> ?NE"
    proof
      fix \<tau>
      assume "\<tau> \<in> set (map snd new)" 
      then obtain f args where "((f,args),\<tau>) \<in> set rem_ls" and args: "set args \<subseteq> ne" using part by auto
      with rem_ls have "((f,args),\<tau>) \<in> set Cs" by auto
      with assms have "C (f,args) = Some \<tau>" by auto
      hence fC: "f : args \<rightarrow> \<tau> in C" by (simp add: hastype_in_ssig_def)
      from args ne have "\<forall> tau. \<exists> t. tau \<in> set args \<longrightarrow> t : tau in ?TC" by auto
      from choice[OF this] obtain ts where "\<And> tau. tau \<in> set args \<Longrightarrow> ts tau : tau in ?TC" by auto
      hence "Fun f (map ts args) : \<tau> in ?TC" 
        apply (intro Fun_hastypeI[OF fC]) 
        by (simp add: list_all2_conv_all_nth)
      thus "\<tau> \<in> ?NE" by auto
    qed
    show ?case
    proof (cases "new = []")
      case False
      note IH = 1(1)[OF rem_ls_def part[symmetric] False]
      have "compute_nonempty_main ne ls = compute_nonempty_main (ne \<union> set (map snd new)) rem" using False by simp
      also have "\<dots> = ?NE" 
      proof (rule IH)
        show "ne \<union> set (map snd new) \<subseteq> ?NE" using new ne by auto
        show "set rem \<subseteq> set Cs" using rem_ls part by auto
        show "snd ` (set Cs - set rem) \<subseteq> ne \<union> set (map snd new)"
        proof
          fix \<tau>
          assume "\<tau> \<in> snd ` (set Cs - set rem)" 
          then obtain f args where in_ls: "((f,args),\<tau>) \<in> set Cs" and nrem: "((f,args),\<tau>) \<notin> set rem" by force
          thus "\<tau> \<in> ne \<union> set (map snd new)" using new part rem_ls by force (* takes a few seconds *)
        qed
      qed
      finally show ?thesis .
    next
      case True
      have "compute_nonempty_main ne ls = ne" using True by simp
      also have "\<dots> = ?NE" 
      proof (rule ccontr)
        assume "\<not> ?thesis" 
        with ne obtain \<tau> t where counter: "t : \<tau> in ?TC" "\<tau> \<notin> ne" by auto
        thus False 
        proof (induct t \<tau>)
          case (Fun f ts \<tau>s \<tau>)
          from Fun(1) have "C (f,\<tau>s) = Some \<tau>" by (simp add: hastype_in_ssig_def)
          with assms(2) have mem: "((f,\<tau>s),\<tau>) \<in> set Cs" by (meson map_of_SomeD)
          from Fun(3) have \<tau>s: "set \<tau>s \<subseteq> ne" by (induct, auto)
          from rem_ls mem Fun(4) have "((f,\<tau>s),\<tau>) \<in> set rem_ls" by auto
          with \<tau>s have "((f,\<tau>s),\<tau>) \<in> set new" using part by auto
          with True show ?case by auto
        qed auto
      qed
      finally show ?thesis .
    qed
  qed
  from this[of "{}" Cs] show ?thesis unfolding compute_nonempty_sorts_def by auto
qed

definition decide_nonempty_sorts :: "'t list \<Rightarrow> (('f \<times> 't list) \<times> 't)list \<Rightarrow> 't option" where
  "decide_nonempty_sorts \<tau>s Cs = (let ne = compute_nonempty_sorts Cs in
   find (\<lambda> \<tau>. \<tau> \<notin> ne) \<tau>s)" 

lemma decide_nonempty_sorts:  
  assumes "distinct (map fst Cs)" (* no conflicting asssignments in list-representation *)
  and "map_of Cs = C" (* list-representation corresponds to function representation *)
shows "decide_nonempty_sorts \<tau>s Cs = None \<Longrightarrow> \<forall> \<tau> \<in> set \<tau>s. \<exists> t :: ('f,'v)term. t : \<tau> in \<T>(C,\<emptyset>)"
  "decide_nonempty_sorts \<tau>s Cs = Some \<tau> \<Longrightarrow> \<tau> \<in> set \<tau>s \<and> \<not> (\<exists> t :: ('f,'v)term. t : \<tau> in \<T>(C,\<emptyset>))" 
  unfolding decide_nonempty_sorts_def Let_def compute_nonempty_sorts[OF assms, where ?'v = 'v]
    find_None_iff find_Some_iff by auto


subsection \<open>Deciding infiniteness of a sort\<close>

text \<open>We provide an algorithm, that given a list of sorts with constructors, computes the
  set of those sorts that are infinite. Here a sort is defined as infinite iff 
   there is no upper bound on the size of the ground terms of that sort.\<close>

(* second argument: take list of types combined with constructors *)
function compute_inf_main :: "'\<tau> set \<Rightarrow> ('\<tau> \<times> ('f \<times> '\<tau> list)list) list \<Rightarrow> '\<tau> set" where
  "compute_inf_main m_inf ls = (
   let (fin, ls') = 
         partition (\<lambda> (\<tau>,fs). \<forall> \<tau>s \<in> set (map snd fs). \<forall> \<tau> \<in> set \<tau>s. \<tau> \<notin> m_inf) ls 
    in if fin = [] then m_inf else compute_inf_main (m_inf - set (map fst fin)) ls')" 
  by pat_completeness auto

termination
proof (relation "measure (length o snd)", goal_cases)
  case (2 m_inf ls pair fin ls')   
  have "length fin + length ls' = length ls" 
    using 2 sum_length_filter_compl[of _ ls] by (auto simp: o_def)
  with 2(3) have "length ls' < length ls" by (cases fin, auto)
  thus ?case by auto
qed simp

lemma compute_inf_main: fixes E :: "'v \<rightharpoonup> 't" and C :: "('f,'t)ssig"
  assumes E: "E = \<emptyset>" 
  and C_Cs: "C = map_of Cs'" 
  and Cs': "set Cs' = set (concat (map ((\<lambda> (\<tau>, fs). map (\<lambda> f. (f,\<tau>)) fs)) Cs))" 
  and arg_types_inhabitet: "\<forall> f \<tau>s \<tau> \<tau>'. f : \<tau>s \<rightarrow> \<tau> in C \<longrightarrow> \<tau>' \<in> set \<tau>s \<longrightarrow> (\<exists> t. t : \<tau>' in \<T>(C,E))" 
  and dist: "distinct (map fst Cs)" "distinct (map fst Cs')"
  and inhabitet: "\<forall> \<tau> fs. (\<tau>,fs) \<in> set Cs \<longrightarrow> set fs \<noteq> {}" 
  and "\<forall> \<tau>. \<tau> \<notin> m_inf \<longrightarrow> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})" 
  and "set ls \<subseteq> set Cs" 
  and "fst ` (set Cs - set ls) \<inter> m_inf = {}" 
  and "m_inf \<subseteq> fst ` set ls" 
shows "compute_inf_main m_inf ls = {\<tau>. \<not> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})}" 
  using assms(8-)
proof (induct m_inf ls rule: compute_inf_main.induct)
  case (1 m_inf ls)
  let ?fin = "\<lambda> \<tau>. bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})" 
  define crit where "crit = (\<lambda> (\<tau> :: 't,fs :: ('f \<times> 't list) list). \<forall> \<tau>s \<in> set (map snd fs). \<forall> \<tau> \<in> set \<tau>s. \<tau> \<notin> m_inf)" 
  define S where "S \<tau>' = size ` {t. t : \<tau>' in \<T>(C,E)}" for \<tau>'
  define M where "M \<tau>' = Maximum (S \<tau>')" for \<tau>'
  define M' where "M' \<sigma>s = sum_list (map M \<sigma>s) + (1 + length \<sigma>s)" for \<sigma>s
  define L where "L = [ \<sigma>s . (\<tau>,cs) <- Cs, (f,\<sigma>s) <- cs]" 
  define N where "N = max_list (map M' L)" 
  obtain fin ls' where part: "partition crit ls = (fin, ls')" by force
  {
    fix \<tau> cs
    assume inCs: "(\<tau>,cs) \<in> set Cs" 
    have nonempty:"\<exists> t. t : \<tau> in \<T>(C,E)"
    proof -
      from inhabitet[rule_format, OF inCs] obtain f \<sigma>s where "(f,\<sigma>s) \<in> set cs" by (cases cs,auto )
      with inCs have "((f,\<sigma>s),\<tau>) \<in> set Cs'" unfolding Cs' by auto
      hence fC: "f : \<sigma>s \<rightarrow> \<tau> in C" using dist(2) unfolding C_Cs
        by (meson hastype_in_ssig_def map_of_is_SomeI)
      hence "\<forall>\<sigma>. \<exists> t. \<sigma> \<in> set \<sigma>s \<longrightarrow> t : \<sigma> in \<T>(C,E)" using arg_types_inhabitet[rule_format, of f \<sigma>s \<tau>] by auto
      from choice[OF this] obtain t where "\<sigma> \<in> set \<sigma>s \<Longrightarrow> t \<sigma> : \<sigma> in \<T>(C,E)" for \<sigma> by auto
      hence "Fun f (map t \<sigma>s) : \<tau> in \<T>(C,E)" using list_all2_conv_all_nth 
        apply (intro Fun_hastypeI[OF fC]) by (simp add: list_all2_conv_all_nth)
      then show ?thesis by auto
    qed
  } note inhabited = this
  {
    fix \<tau>
    assume asm: "\<tau> \<in> fst ` set fin"
    hence "?fin \<tau>"
    proof(cases "\<tau> \<in> m_inf")
      case True
      then obtain fs where taufs:"(\<tau>, fs) \<in> set fin" using asm by auto 
      {
        fix \<tau>' and t and args
        assume *: "\<tau>' \<in> set args" "args \<in> snd ` set fs" "t : \<tau>' in \<T>(C,E)" 
        from * have "\<tau>' \<notin> m_inf" using taufs unfolding compute_inf_main.simps[of m_inf] 
          using crit_def part by fastforce
        hence "?fin \<tau>'" using crit_def part 1(2) by auto
        hence hM: "bdd_above (S \<tau>')" unfolding S_def .
        from *(3) have "size t \<in> S \<tau>'" unfolding S_def by auto
        from this hM have "size t \<le> M \<tau>'" unfolding M_def by (metis bdd_above_Maximum_nat)
      } note arg_type_bounds = this
      {
        fix t
        assume t: "t : \<tau> in \<T>(C,E)" 
        then obtain f ts where tF: "t = Fun f ts" unfolding E by (induct, auto)
        from t[unfolded tF Fun_hastype]
        obtain \<sigma>s where f: "f : \<sigma>s \<rightarrow> \<tau> in C" and args: "ts :\<^sub>l \<sigma>s in \<T>(C,E)" by auto
        from part[simplified] asm 1(3) obtain cs where inCs: "(\<tau>,cs) \<in> set Cs" and crit: "crit (\<tau>,cs)" by auto
        {
          from f[unfolded hastype_in_ssig_def C_Cs]
          have "map_of Cs' (f, \<sigma>s) = Some \<tau>" by auto
          hence "((f,\<sigma>s), \<tau>) \<in> set Cs'" by (metis map_of_SomeD)
          from this[unfolded Cs', simplified] obtain cs' where 2: "(\<tau>,cs') \<in> set Cs" and mem: "(f,\<sigma>s) \<in> set cs'" by auto
          from inCs 2 dist have "cs' = cs" by (metis eq_key_imp_eq_value)
          with mem have mem: "(f,\<sigma>s) \<in> set cs" by auto
        } note mem = this
        from mem inCs have inL: "\<sigma>s \<in> set L" unfolding L_def by force
        {
          fix \<sigma> ti
          assume "\<sigma> \<in> set \<sigma>s" and ti: "ti : \<sigma> in \<T>(C,E)" 
          with mem crit have "\<sigma> \<notin> m_inf" unfolding crit_def by auto
          hence "?fin \<sigma>" using 1(2) by auto
          hence hM: "bdd_above (S \<sigma>)" unfolding S_def .
          from ti have "size ti \<in> S \<sigma>" unfolding S_def by auto
          from this hM have "size ti \<le> M \<sigma>" unfolding M_def by (metis bdd_above_Maximum_nat)
        } note arg_bound = this
        have len: "length \<sigma>s = length ts" using args by (auto simp: list_all2_conv_all_nth)
        have "size t = sum_list (map size ts) + (1 + length ts)" unfolding tF by (simp add: size_list_conv_sum_list)
        also have "\<dots> \<le> sum_list (map M \<sigma>s) + (1 + length ts)" unfolding tF args 
        proof -
          have id1: "map size ts = map (\<lambda> i. size (ts ! i)) [0 ..< length ts]" by (intro nth_equalityI, auto)
          have id2: "map M \<sigma>s = map (\<lambda> i. M (\<sigma>s ! i)) [0 ..< length ts]" using len by (intro nth_equalityI, auto)
          have "sum_list (map size ts) \<le> sum_list (map M \<sigma>s)" unfolding id1 id2
            apply (rule sum_list_mono) using arg_bound args
            by (auto, simp add: list_all2_conv_all_nth)
          thus ?thesis by auto
        qed
        also have "\<dots> = sum_list (map M \<sigma>s) + (1 + length \<sigma>s)" using args unfolding M_def using list_all2_lengthD by auto
        also have "\<dots> = M' \<sigma>s" unfolding M'_def by auto
        also have "\<dots> \<le> max_list (map M' L)" 
          by (rule max_list, insert inL, auto)
        also have "\<dots> = N" unfolding N_def ..
        finally have "size t \<le> N" .
      } 
      hence "\<And> s. s \<in> S \<tau> \<Longrightarrow> s \<le> N" unfolding S_def by auto
      hence "finite (S \<tau>)"
        using finite_nat_set_iff_bounded_le by auto
      moreover 
      have nonempty:"\<exists> t. t : \<tau> in \<T>(C,E)"
      proof -
        from part[simplified] asm 1(3) obtain cs where inCs: "(\<tau>,cs) \<in> set Cs" by auto
        thus ?thesis using inhabited by auto
      qed
      hence "S \<tau> \<noteq> {}" unfolding S_def by auto
      ultimately show ?thesis unfolding S_def[symmetric] by (metis Max_ge bdd_above_def)
    next
      case False
      then show ?thesis using 1(2) by simp
    qed
  } note fin = this
  show ?case 
  proof (cases "fin = []")
    case False
    hence "compute_inf_main m_inf ls = compute_inf_main (m_inf - set (map fst fin)) ls'" 
      unfolding compute_inf_main.simps[of m_inf] part[unfolded crit_def] by auto
    also have "\<dots> = {\<tau>. \<not> ?fin \<tau>}" 
    proof (rule 1(1)[OF refl part[unfolded crit_def, symmetric] False])
      show "set ls' \<subseteq> set Cs" using 1(3) part by auto
      show "fst ` (set Cs - set ls') \<inter> (m_inf - set (map fst fin)) = {}" using 1(3-4) part by force
      show "\<forall>\<tau>. \<tau> \<notin> m_inf - set (map fst fin) \<longrightarrow> ?fin \<tau>" using 1(2) fin by force
      show "m_inf - set (map fst fin) \<subseteq> fst ` set ls'" using 1(5) part by force
    qed
    finally show ?thesis .
  next
    case True
    hence "compute_inf_main m_inf ls = m_inf" 
      unfolding compute_inf_main.simps[of m_inf] part[unfolded crit_def] by auto
    also have "\<dots> = {\<tau>. \<not> ?fin \<tau>}" 
    proof
      show "{\<tau>. \<not> ?fin \<tau>} \<subseteq> m_inf" using fin 1(2) by auto
      {
        fix \<tau>
        assume "\<tau> \<in> m_inf" 
        with 1(5) obtain cs where mem: "(\<tau>,cs) \<in> set ls" by auto
        from part True have ls': "ls' = ls" by (induct ls arbitrary: ls', auto)
        from partition_P[OF part, unfolded ls']
        have "\<And> e. e \<in> set ls \<Longrightarrow> \<not> crit e" by auto
        from this[OF mem, unfolded crit_def split]
        obtain c \<tau>s \<tau>' where *: "(c,\<tau>s) \<in> set cs" "\<tau>' \<in> set \<tau>s" "\<tau>' \<in> m_inf" by auto
        from mem 1(2-) have "(\<tau>,cs) \<in> set Cs" by auto
        with * have "((c,\<tau>s),\<tau>) \<in> set Cs'" unfolding Cs' by force
        with dist(2) have "map_of Cs' ((c,\<tau>s)) = Some \<tau>" by simp
        from this[folded C_Cs] have c: "c : \<tau>s \<rightarrow> \<tau> in C" unfolding hastype_in_ssig_def .
        from arg_types_inhabitet this have "\<forall> \<sigma>. \<exists> t. \<sigma> \<in> set \<tau>s \<longrightarrow> t : \<sigma> in \<T>(C,E)" by auto
        from choice[OF this] obtain t where "\<And> \<sigma>. \<sigma> \<in> set \<tau>s \<Longrightarrow> t \<sigma> : \<sigma> in \<T>(C,E)" by auto
        hence list: "map t \<tau>s :\<^sub>l \<tau>s in \<T>(C,E)" by (simp add: list_all2_conv_all_nth)
        with c have "Fun c (map t \<tau>s) : \<tau> in \<T>(C,E)" by (intro Fun_hastypeI)
        with * c list have "\<exists> c \<tau>s \<tau>' ts. Fun c ts : \<tau> in \<T>(C,E) \<and> ts :\<^sub>l \<tau>s in \<T>(C,E) \<and> c : \<tau>s \<rightarrow> \<tau> in C \<and> \<tau>' \<in> set \<tau>s \<and> \<tau>' \<in> m_inf" 
          by blast
      } note m_invD = this
      {
        fix n :: nat
        have "\<tau> \<in> m_inf \<Longrightarrow> \<exists> t. t : \<tau> in \<T>(C,E) \<and> size t \<ge> n" for \<tau>
        proof (induct n arbitrary: \<tau>)
          case (0 \<tau>)
          from m_invD[OF 0] show ?case by blast
        next
          case (Suc n \<tau>)
          from m_invD[OF Suc(2)] obtain c \<tau>s \<tau>' ts
            where *: "ts :\<^sub>l \<tau>s in \<T>(C,E)" "c : \<tau>s \<rightarrow> \<tau> in C" "\<tau>' \<in> set \<tau>s" "\<tau>' \<in> m_inf" 
            by auto
          from *(1)[unfolded list_all2_conv_all_nth] *(3)[unfolded set_conv_nth]
          obtain i where i: "i < length \<tau>s" and tsi:"ts ! i : \<tau>' in \<T>(C,E)" and len: "length ts = length \<tau>s" by auto
          from Suc(1)[OF *(4)] obtain t where t:"t : \<tau>' in \<T>(C,E)" and ns:"n \<le> size t" by auto
          define ts' where "ts' = ts[i := t]" 
          have "ts' :\<^sub>l \<tau>s in \<T>(C,E)" using list_all2_conv_all_nth unfolding ts'_def 
            by (metis "*"(1) tsi has_same_type i list_all2_update_cong list_update_same_conv t(1))
          hence **:"Fun c ts' : \<tau> in \<T>(C,E)" apply (intro Fun_hastypeI[OF *(2)]) by fastforce 
          have "t \<in> set ts'" unfolding ts'_def using t 
            by (simp add: i len set_update_memI)
          hence "size (Fun c ts') \<ge> Suc n" using * 
            by (simp add: size_list_estimation' ns)
          thus ?case using ** by blast
        qed
      } note main = this
      show "m_inf \<subseteq> {\<tau>. \<not> ?fin \<tau>}"  
      proof (standard, standard)
        fix \<tau>
        assume asm: "\<tau> \<in> m_inf"         
        have "\<exists>t. t : \<tau> in \<T>(C,E) \<and> n < size t" for n using main[OF asm, of "Suc n"] by auto
        thus "\<not> ?fin \<tau>"
          by (metis bdd_above_Maximum_nat imageI mem_Collect_eq order.strict_iff)
      qed
    qed
    finally show ?thesis .
  qed
qed  

definition compute_inf_sorts :: "(('f \<times> 't list) \<times> 't)list \<Rightarrow> 't set" where
  "compute_inf_sorts Cs = (let 
       Cs' = map (\<lambda> \<tau>. (\<tau>, map fst (filter(\<lambda>f. snd f = \<tau>) Cs))) (remdups (map snd Cs))
    in compute_inf_main (set (map fst Cs')) Cs')" 

lemma compute_inf_sorts:
  fixes E :: "'v \<rightharpoonup> 't" and C :: "('f,'t)ssig"
  assumes E: "E = \<emptyset>" 
  and C_Cs: "C = map_of Cs" 
  and arg_types_inhabitet: "\<forall> f \<tau>s \<tau> \<tau>'. f : \<tau>s \<rightarrow> \<tau> in C \<longrightarrow> \<tau>' \<in> set \<tau>s \<longrightarrow> (\<exists> t. t : \<tau>' in \<T>(C,E))"
  and dist: "distinct (map fst Cs)" 
shows "compute_inf_sorts Cs = {\<tau>. \<not> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})}"
proof -
  define taus where "taus = remdups (map snd Cs)" 
  define Cs' where "Cs' = map (\<lambda> \<tau>. (\<tau>, map fst (filter(\<lambda>f. snd f = \<tau>) Cs))) taus" 
  have "compute_inf_sorts Cs = compute_inf_main (set (map fst Cs')) Cs'" 
    unfolding compute_inf_sorts_def taus_def Cs'_def Let_def by auto
  also have "\<dots> = {\<tau>. \<not> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})}"
  proof (rule compute_inf_main[OF E C_Cs _ arg_types_inhabitet _ dist _ _ subset_refl])  
    have "distinct taus" unfolding taus_def by auto
    thus "distinct (map fst Cs')" unfolding Cs'_def map_map o_def fst_conv by auto
    show "set Cs = set (concat (map (\<lambda>(\<tau>, fs). map (\<lambda>f. (f, \<tau>)) fs) Cs'))" 
      unfolding Cs'_def taus_def by force
    show "\<forall>\<tau> fs. (\<tau>, fs) \<in> set Cs' \<longrightarrow> set fs \<noteq> {}" 
      unfolding Cs'_def taus_def by (force simp: filter_empty_conv)
    show "fst ` (set Cs' - set Cs') \<inter> set (map fst Cs') = {}" by auto
    show "set (map fst Cs') \<subseteq> fst ` set Cs'" by auto
    show "\<forall>\<tau>. \<tau> \<notin> set (map fst Cs') \<longrightarrow> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})" 
    proof (intro allI impI)
      fix \<tau>
      assume "\<tau> \<notin> set (map fst Cs')" 
      hence "\<tau> \<notin> snd ` set Cs" unfolding Cs'_def taus_def by auto
      hence diff: "C f \<noteq> Some \<tau>" for f unfolding C_Cs
        by (metis Some_eq_map_of_iff dist imageI snd_conv)
      {
        fix t
        assume "t : \<tau> in \<T>(C,E)" 
        hence False using diff unfolding E
        proof induct
          case (Fun f ss \<sigma>s \<tau>)
          from Fun(1,4) show False unfolding hastype_in_ssig_def by auto
        qed auto
      }
      hence id: "{t. t : \<tau> in \<T>(C,E)} = {}" by auto
      show "bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})" unfolding id by auto
    qed
  qed
  finally show ?thesis .
qed
end
