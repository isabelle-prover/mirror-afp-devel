section \<open>Simple Convergence Graphs\<close>

text \<open>Alternative Implementation of the simple convergence graph using tries instead of sets.\<close>

theory Simple_Convergence_Graph_Trie
  imports Convergence_Graph Collections.TrieSetImpl
begin

subsection \<open>Basic Definitions\<close>

type_synonym 'a simple_cg = "'a ts list"

definition simple_cg_empty :: "'a simple_cg" where
  "simple_cg_empty = []"

thm TrieSetImpl.ts_ops_def

(* collects all traces in the same convergent class set as ys *)
fun simple_cg_lookup :: "('a::linorder) simple_cg \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "simple_cg_lookup xs ys = ts.to_list (ts.ins ys (foldl (ts.union) (ts.empty ()) (filter (\<lambda>x . ts.memb ys x) xs)))"

(* collects all traces (zs@ys'') such that there exists a prefix ys' of ys with (ys=ys'@ys'')
   and zs is in the same convergent class set as ys' *) 
fun simple_cg_lookup_with_conv :: "('a::linorder) simple_cg \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "simple_cg_lookup_with_conv g ys = (let
      lookup_for_prefix = (\<lambda>i . let
                                  pref = take i ys;
                                  suff = drop i ys;
                                  pref_conv = (foldl (ts.union) (ts.empty ()) (filter (\<lambda>x . ts.memb pref x) g))
                                in map (\<lambda> pref' . pref'@suff) (ts.to_list pref_conv))
    in ts.to_list (ts.from_list (ys # (concat (map lookup_for_prefix [0..<Suc (length ys)])))))"

fun simple_cg_insert' :: "('a::linorder) simple_cg \<Rightarrow> 'a list \<Rightarrow> 'a simple_cg" where
  "simple_cg_insert' xs ys = (case find (\<lambda>x . ts.memb ys x) xs
    of Some x \<Rightarrow> xs |
       None   \<Rightarrow> (ts.sng ys)#xs)"


fun simple_cg_insert :: "('a::linorder) simple_cg \<Rightarrow> 'a list \<Rightarrow> 'a simple_cg" where
  "simple_cg_insert xs ys = foldl (\<lambda> xs' ys' . simple_cg_insert' xs' ys') xs (prefixes ys)"

fun simple_cg_initial :: "('a,'b::linorder,'c::linorder) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) simple_cg" where
  "simple_cg_initial M1 T = foldl (\<lambda> xs' ys' . simple_cg_insert' xs' ys') simple_cg_empty (filter (is_in_language M1 (initial M1)) (sorted_list_of_sequences_in_tree T))"


subsection \<open>Merging by Closure\<close>

text \<open>The following implementation of the merge operation follows the closure operation described
      by Simão et al. in Simão, A., Petrenko, A. and Yevtushenko, N. (2012), On reducing test length 
      for FSMs with extra states. Softw. Test. Verif. Reliab., 22: 435-454. https://doi.org/10.1002/stvr.452.
      That is, two traces u and v are merged by adding {u,v} to the list of convergent classes
      followed by computing the closure of the graph based on two operations: 
      (1) classes A and B can be merged if there exists some class C such that C contains some w1, w2
          and there exists some w such that A contains w1.w and B contains w2.w.
      (2) classes A and B can be merged if one is a subset of the other.\<close>


(* classes x1 and x2 can be merged via class x if there exist \<alpha>, \<beta> in x and some suffix \<gamma>
   such that x1 contains \<alpha>@\<gamma> and x2 contains \<beta>@\<gamma> *)
fun can_merge_by_suffix :: "'a ts \<Rightarrow> 'a ts \<Rightarrow> 'a ts \<Rightarrow> bool" where
  "can_merge_by_suffix x x1 x2 = (\<exists> \<alpha> \<beta> \<gamma> . ts.memb \<alpha> x \<and> ts.memb \<beta> x \<and> ts.memb (\<alpha>@\<gamma>) x1 \<and> ts.memb (\<beta>@\<gamma>) x2)"

lemma can_merge_by_suffix_code[code] : 
  "can_merge_by_suffix x x1 x2 = 
    (ts.bex x
      (\<lambda> ys . ts.bex x1
        (\<lambda> ys1 . is_prefix ys ys1 \<and>
                 (let ys'' = (drop (length ys) ys1)
                   in ts.bex x (\<lambda> ys' . ts.memb (ys'@ys'') x2)))))"
  unfolding can_merge_by_suffix.simps
  unfolding ts.memb_correct[OF ts.invar]
  unfolding ts.bex_correct[OF ts.invar] Let_def is_prefix_prefix by force
  


lemma can_merge_by_suffix_validity :
  assumes "observable M1" and "observable M2"
  and     "\<And> u v . ts.memb u x \<Longrightarrow> ts.memb v x \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> u v . ts.memb u x1 \<Longrightarrow> ts.memb v x1 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> u v . ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "can_merge_by_suffix x x1 x2"
  and     "ts.memb u (ts.union x1 x2)"
  and     "ts.memb v (ts.union x1 x2)"
  and     "u \<in> L M1" and "u \<in> L M2" 
shows "converge M1 u v \<and> converge M2 u v"
proof -
  obtain \<alpha> \<beta> \<gamma> where "ts.memb \<alpha> x" and "ts.memb \<beta> x" and "ts.memb (\<alpha>@\<gamma>) x1" and "ts.memb (\<beta>@\<gamma>) x2"
    using \<open>can_merge_by_suffix x x1 x2\<close> by auto

  consider "ts.memb u x1" | "ts.memb u x2" 
    using \<open>ts.memb u (ts.union x1 x2)\<close>
    unfolding ts.memb_correct[OF ts.invar]
    unfolding ts.union_correct[OF ts.invar ts.invar]
    by blast
  then show ?thesis proof cases
    case 1

    then have "converge M1 u (\<alpha>@\<gamma>)" and "converge M2 u (\<alpha>@\<gamma>)"
      using \<open>ts.memb u (ts.union x1 x2)\<close> assms(4)[OF _ \<open>ts.memb (\<alpha>@\<gamma>) x1\<close> assms(9,10)] 
      by blast+
    then have "(\<alpha>@\<gamma>) \<in> L M1" and "(\<alpha>@\<gamma>) \<in> L M2"
      by auto
    then have "\<alpha> \<in> L M1" and "\<alpha> \<in> L M2"
      using language_prefix by metis+
    then have "converge M1 \<alpha> \<beta>" and "converge M2 \<alpha> \<beta>"
      using assms(3) \<open>ts.memb \<alpha> x\<close> \<open>ts.memb \<beta> x\<close>
      by blast+
    have "converge M1 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)" 
      using \<open>converge M1 \<alpha> \<beta>\<close>
      by (meson \<open>\<alpha> @ \<gamma> \<in> L M1\<close> assms(1) converge.simps converge_append) 
    then have "\<beta>@\<gamma> \<in> L M1"
      by auto
    have "converge M2 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)" 
      using \<open>converge M2 \<alpha> \<beta>\<close>
      by (meson \<open>\<alpha> @ \<gamma> \<in> L M2\<close> assms(2) converge.simps converge_append)   
    then have "\<beta>@\<gamma> \<in> L M2"
      by auto

    consider (11) "ts.memb v x1" | (12) "ts.memb v x2" 
      using \<open>ts.memb v (ts.union x1 x2)\<close> 
      unfolding ts.memb_correct[OF ts.invar]
      unfolding ts.union_correct[OF ts.invar ts.invar]
      by blast
    then show ?thesis proof cases
      case 11
      show ?thesis
        using "1" "11" assms(10) assms(4) assms(9) by blast 
    next
      case 12
      then have "converge M1 v (\<beta>@\<gamma>)" and "converge M2 v (\<beta>@\<gamma>)"
        using assms(5)[OF \<open>ts.memb (\<beta>@\<gamma>) x2\<close> _ \<open>\<beta>@\<gamma> \<in> L M1\<close> \<open>\<beta>@\<gamma> \<in> L M2\<close>] 
        by auto
      then show ?thesis 
        using \<open>converge M1 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)\<close> \<open>converge M2 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)\<close> \<open>converge M1 u (\<alpha>@\<gamma>)\<close> \<open>converge M2 u (\<alpha>@\<gamma>)\<close> 
        by auto
    qed 
  next
    case 2

    then have "converge M1 u (\<beta>@\<gamma>)" and "converge M2 u (\<beta>@\<gamma>)"
      using \<open>ts.memb u (ts.union x1 x2)\<close> assms(5)[OF _ \<open>ts.memb (\<beta>@\<gamma>) x2\<close> assms(9,10)] 
      by blast+
    then have "(\<beta>@\<gamma>) \<in> L M1" and "(\<beta>@\<gamma>) \<in> L M2"
      by auto
    then have "\<beta> \<in> L M1" and "\<beta> \<in> L M2"
      using language_prefix by metis+
    then have "converge M1 \<alpha> \<beta>" and "converge M2 \<alpha> \<beta>"
      using assms(3)[OF \<open>ts.memb \<beta> x\<close> \<open>ts.memb \<alpha> x\<close>]
      by auto
    have "converge M1 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)" 
        using \<open>converge M1 \<alpha> \<beta>\<close>
        using \<open>\<beta> @ \<gamma> \<in> L M1\<close> \<open>\<beta> \<in> L M1\<close> assms(1) converge_append converge_append_language_iff by blast
    then have "\<alpha>@\<gamma> \<in> L M1"
      by auto
    have "converge M2 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)" 
      using \<open>converge M2 \<alpha> \<beta>\<close> 
      using \<open>\<beta> @ \<gamma> \<in> L M2\<close> \<open>\<beta> \<in> L M2\<close> assms(2) converge_append converge_append_language_iff by blast
    then have "\<alpha>@\<gamma> \<in> L M2"
      by auto
      

    consider (21) "ts.memb v x1" | (22) "ts.memb v x2" 
      using \<open>ts.memb v (ts.union x1 x2)\<close> 
      unfolding ts.memb_correct[OF ts.invar]
      unfolding ts.union_correct[OF ts.invar ts.invar] by blast
    then show ?thesis proof cases
      case 22
      show ?thesis
        using "2" "22" assms(10) assms(5) assms(9) by blast 
    next
      case 21
      then have "converge M1 v (\<alpha>@\<gamma>)" and "converge M2 v (\<alpha>@\<gamma>)"
        using assms(4)[OF \<open>ts.memb (\<alpha>@\<gamma>) x1\<close> _ \<open>\<alpha>@\<gamma> \<in> L M1\<close> \<open>\<alpha>@\<gamma> \<in> L M2\<close>] 
        by auto
      then show ?thesis 
        using \<open>converge M1 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)\<close> \<open>converge M2 (\<alpha>@\<gamma>) (\<beta>@\<gamma>)\<close>  \<open>converge M1 u (\<beta>@\<gamma>)\<close> \<open>converge M2 u (\<beta>@\<gamma>)\<close> 
        by auto
    qed 
  qed
qed


fun simple_cg_closure_phase_1_helper' :: "'a ts \<Rightarrow> 'a ts \<Rightarrow> 'a simple_cg \<Rightarrow> (bool \<times> 'a ts \<times> 'a simple_cg)" where
  "simple_cg_closure_phase_1_helper' x x1 xs = 
    (let (x2s,others) = separate_by (can_merge_by_suffix x x1) xs;
         x1Union      = foldl (ts.union) x1 x2s
      in (x2s \<noteq> [],x1Union,others))"  

lemma simple_cg_closure_phase_1_helper'_False :
  "\<not>fst (simple_cg_closure_phase_1_helper' x x1 xs) \<Longrightarrow> simple_cg_closure_phase_1_helper' x x1 xs = (False,x1,xs)"
  unfolding simple_cg_closure_phase_1_helper'.simps Let_def separate_by.simps
  by (simp add: filter_empty_conv) 


lemma simple_cg_closure_phase_1_helper'_True :
  assumes "fst (simple_cg_closure_phase_1_helper' x x1 xs)" 
shows "length (snd (snd (simple_cg_closure_phase_1_helper' x x1 xs))) < length xs"
proof -
  have "snd (snd (simple_cg_closure_phase_1_helper' x x1 xs)) = filter (\<lambda>x2 . \<not> (can_merge_by_suffix x x1 x2)) xs"
    by auto
  moreover have "filter (\<lambda>x2 . (can_merge_by_suffix x x1 x2)) xs \<noteq> []"
    using assms unfolding simple_cg_closure_phase_1_helper'.simps Let_def separate_by.simps
    by fastforce
  ultimately show ?thesis 
    using filter_not_all_length[of "can_merge_by_suffix x x1" xs]
    by metis
qed

lemma simple_cg_closure_phase_1_helper'_length :
  "length (snd (snd (simple_cg_closure_phase_1_helper' x x1 xs))) \<le> length xs"
  by auto

lemma simple_cg_closure_phase_1_helper'_validity_fst :
  assumes "observable M1" and "observable M2"
  and     "\<And> u v . ts.memb u x \<Longrightarrow> ts.memb v x \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> u v . ts.memb u x1 \<Longrightarrow> ts.memb v x1 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> x2 u v . x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "ts.memb u (fst (snd (simple_cg_closure_phase_1_helper' x x1 xs)))"
  and     "ts.memb v (fst (snd (simple_cg_closure_phase_1_helper' x x1 xs)))"
  and     "u \<in> L M1" and "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
proof -

  

  have *:"\<And> w . ts.memb w (fst (snd (simple_cg_closure_phase_1_helper' x x1 xs))) \<Longrightarrow> 
                ts.memb w x1 \<or> (\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb w x2 \<and> can_merge_by_suffix x x1 x2)"
  proof -

    fix w assume "ts.memb w (fst (snd (simple_cg_closure_phase_1_helper' x x1 xs)))"
    then have "ts.memb w (foldl ts.union x1 (filter (can_merge_by_suffix x x1) xs))"
      unfolding simple_cg_closure_phase_1_helper'.simps 
      unfolding separate_by.simps Let_def case_prod_conv fst_conv snd_conv
      by auto
    then show "ts.memb w x1 \<or> (\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb w x2 \<and> can_merge_by_suffix x x1 x2)"
    proof (induction xs rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc x' xs)

      show ?case proof (cases "can_merge_by_suffix x x1 x'")
        case False
        then have "(foldl ts.union x1 (filter (can_merge_by_suffix x x1) (xs @ [x'])))
                     = (foldl ts.union x1 (filter (can_merge_by_suffix x x1) xs))"
          by auto
        then show ?thesis
          using snoc
          by (metis (no_types, opaque_lifting) append_Cons empty_append_eq_id insert_iff list.simps(15) list_set_sym) 
          
      next
        case True
        then have *: "(foldl ts.union x1 (filter (can_merge_by_suffix x x1) (xs @ [x'])))
            = ts.union (foldl ts.union x1 (filter (can_merge_by_suffix x x1) xs)) x'"
          by auto
        
        show ?thesis proof (cases "ts.memb w (foldl ts.union x1 (filter (can_merge_by_suffix x x1) xs))")
          case True 
          then show ?thesis using snoc
            by (metis (no_types, opaque_lifting) append_Cons empty_append_eq_id insert_iff list.simps(15) list_set_sym) 
        next
          case False
          then have "ts.memb w x'"
            using snoc.prems unfolding * 
            unfolding ts.memb_correct[OF ts.invar]
            unfolding ts.union_correct[OF ts.invar ts.invar] 
            by blast
          then show ?thesis 
            using True
            by force
        qed
      qed
    qed
  qed

  consider "ts.memb u x1" | "(\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb u x2 \<and> can_merge_by_suffix x x1 x2)"
    using *[OF assms(6)] by blast
  then show ?thesis proof cases
    case 1
    
    consider (a) "ts.memb v x1" | (b) "(\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb v x2 \<and> can_merge_by_suffix x x1 x2)"
      using *[OF assms(7)] by blast
    then show ?thesis proof cases
      case a
      then show ?thesis using assms(4)[OF 1 _ assms(8,9)] by auto
    next
      case b
      then obtain x2v where "x2v \<in> list.set xs" and "ts.memb v x2v" and "can_merge_by_suffix x x1 x2v"
        using *[OF assms(6)] 
        by blast

      then have "ts.memb u (ts.union x1 x2v)" and "ts.memb v (ts.union x1 x2v)"
        using 1 
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by auto

      show ?thesis
        using can_merge_by_suffix_validity[OF assms(1,2), of x x1 x2v, OF assms(3,4) assms(5)[OF \<open>x2v \<in> list.set xs\<close>] \<open>can_merge_by_suffix x x1 x2v\<close> \<open>ts.memb u (ts.union x1 x2v)\<close> \<open>ts.memb v (ts.union x1 x2v)\<close> assms(8,9)]
        by blast
    qed    
  next
    case 2
    then obtain x2u where "x2u \<in> list.set xs" and "ts.memb u x2u" and "can_merge_by_suffix x x1 x2u"
      using *[OF assms(6)] 
      by blast
    then have "ts.memb u (ts.union x1 x2u)"
      unfolding ts.memb_correct[OF ts.invar]
      unfolding ts.union_correct[OF ts.invar ts.invar] 
      by auto

    consider (a) "ts.memb v x1" | (b) "(\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb v x2 \<and> can_merge_by_suffix x x1 x2)"
      using *[OF assms(7)] by blast
    then show ?thesis proof cases
      case a
      then have "ts.memb v (ts.union x1 x2u)"
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by auto
      show ?thesis
        using can_merge_by_suffix_validity[OF assms(1,2), of x x1 x2u, OF assms(3,4) assms(5)[OF \<open>x2u \<in> list.set xs\<close>] \<open>can_merge_by_suffix x x1 x2u\<close> \<open>ts.memb u (ts.union x1 x2u)\<close> \<open>ts.memb v (ts.union x1 x2u)\<close> assms(8,9)]  
        by blast
    next 
      case b
      
      then obtain x2v where "x2v \<in> list.set xs" and "ts.memb v x2v" and "can_merge_by_suffix x x1 x2v"
        using *[OF assms(6)] 
        by blast
      then have "ts.memb v (ts.union x1 x2v)"
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by auto

      have "\<And> v . ts.memb v (ts.union x1 x2u) \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
        using can_merge_by_suffix_validity[OF assms(1,2), of x x1 x2u, OF assms(3,4) assms(5)[OF \<open>x2u \<in> list.set xs\<close>] \<open>can_merge_by_suffix x x1 x2u\<close> \<open>ts.memb u (ts.union x1 x2u)\<close> _ assms(8,9)]
        by blast
      have "\<And> u . ts.memb u (ts.union x1 x2v) \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
        using can_merge_by_suffix_validity[OF assms(1,2), of x x1 x2v, OF assms(3,4) assms(5)[OF \<open>x2v \<in> list.set xs\<close>] \<open>can_merge_by_suffix x x1 x2v\<close> _ \<open>ts.memb v (ts.union x1 x2v)\<close>]
        by blast

      obtain \<alpha>v \<beta>v \<gamma>v where "ts.memb \<alpha>v x" and "ts.memb \<beta>v x" and "ts.memb (\<alpha>v@\<gamma>v) x1" and "ts.memb (\<beta>v@\<gamma>v) x2v"
        using \<open>can_merge_by_suffix x x1 x2v\<close> by auto

      show ?thesis
        using \<open>\<And>u. \<lbrakk>ts.memb u (ts.union x1 x2v); u \<in> L M1; u \<in> L M2\<rbrakk> \<Longrightarrow> converge M1 u v \<and> converge M2 u v\<close> \<open>\<And>v. ts.memb v (ts.union x1 x2u) \<Longrightarrow> converge M1 u v \<and> converge M2 u v\<close> \<open>ts.memb (\<alpha>v @ \<gamma>v) x1\<close> 
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by fastforce
    qed
  qed
qed


lemma simple_cg_closure_phase_1_helper'_validity_snd :
  assumes "\<And> x2 u v . x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (snd (snd (simple_cg_closure_phase_1_helper' x x1 xs)))"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1" and "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
proof -
  have "list.set (snd (snd (simple_cg_closure_phase_1_helper' x x1 xs))) \<subseteq> list.set xs"
    by auto
  then show ?thesis
    using assms by blast  
qed


fun simple_cg_closure_phase_1_helper :: "'a ts \<Rightarrow> 'a simple_cg \<Rightarrow> (bool \<times> 'a simple_cg) \<Rightarrow> (bool \<times> 'a simple_cg)" where
  "simple_cg_closure_phase_1_helper x [] (b,done) = (b,done)" |
  "simple_cg_closure_phase_1_helper x (x1#xs) (b,done) = (let (hasChanged,x1',xs') = simple_cg_closure_phase_1_helper' x x1 xs
                                    in simple_cg_closure_phase_1_helper x xs' (b \<or> hasChanged, x1' # done))"


lemma simple_cg_closure_phase_1_helper_validity :
  assumes "observable M1" and "observable M2"
  and     "\<And> u v . ts.memb u x \<Longrightarrow> ts.memb v x \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> x2 u v . x2 \<in> list.set don \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> x2 u v . x2 \<in> list.set xss \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (snd (simple_cg_closure_phase_1_helper x xss (b,don)))"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1" and "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
  using assms(4,5,6)
proof (induction "length xss" arbitrary: xss don b rule: less_induct)
  case less
  show ?case proof (cases xss)
    case Nil
    then have "x2 \<in> list.set don"
      using less.prems(3) by auto
    then show ?thesis 
      using less.prems(1) assms(7,8,9,10)
      by blast 
  next
    case (Cons x1 xs)
    obtain b' x1' xs' where "simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')"
      using prod.exhaust by metis
    then have "simple_cg_closure_phase_1_helper x xss (b,don) = simple_cg_closure_phase_1_helper x xs' (b \<or> b', x1' # don)"
      unfolding Cons by auto


    have *:"\<And> u v . ts.memb u x1 \<Longrightarrow> ts.memb v x1 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
      using less.prems(2)[of x1] unfolding Cons
      by (meson list.set_intros(1)) 

    have **:"\<And> x2 u v . x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
      using less.prems(2) unfolding Cons
      by (meson list.set_intros(2)) 

    have ***:"\<And> u v. ts.memb u x1' \<Longrightarrow> ts.memb v x1' \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
      using simple_cg_closure_phase_1_helper'_validity_fst[of M1 M2 x x1 xs _ _, OF assms(1,2,3) * **, of "\<lambda> a b c . a"]
      unfolding \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> fst_conv snd_conv
      by blast

    have "length xs' < length xss"
      using simple_cg_closure_phase_1_helper'_length[of x x1 xs]
      unfolding \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> Cons by auto

    have "(\<And>x2 u v. x2 \<in> list.set (x1' # don) \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
      using *** less.prems(1)
      by (metis set_ConsD) 

    have "xs' = snd (snd (simple_cg_closure_phase_1_helper' x x1 xs))"
      using \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> by auto
    have "(\<And>x2 u v. x2 \<in> list.set xs' \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
      using simple_cg_closure_phase_1_helper'_validity_snd[of xs' M1]
      unfolding \<open>xs' = snd (snd (simple_cg_closure_phase_1_helper' x x1 xs))\<close>
      using ** simple_cg_closure_phase_1_helper'_validity_snd by blast 

    have "x2 \<in> list.set (snd (simple_cg_closure_phase_1_helper x xs' (b \<or> b', x1' # don)))"
      using less.prems(3) unfolding \<open>simple_cg_closure_phase_1_helper x xss (b,don) = simple_cg_closure_phase_1_helper x xs' (b \<or> b', x1' # don)\<close> .
    then show ?thesis
      using less.hyps[OF \<open>length xs' < length xss\<close> \<open>(\<And>x2 u v. x2 \<in> list.set (x1' # don) \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)\<close> \<open>(\<And>x2 u v. x2 \<in> list.set xs' \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)\<close>, of "x1'#don" "\<lambda> a b c . a" "\<lambda> a b c . a"]
      by force
  qed
qed



lemma simple_cg_closure_phase_1_helper_length :
  "length (snd (simple_cg_closure_phase_1_helper x xss (b,don))) \<le> length xss + length don"
proof (induction "length xss" arbitrary: xss b don rule: less_induct)
  case less
  show ?case proof (cases xss)
    case Nil
    then show ?thesis by auto
  next
    case (Cons x1 xs)
    obtain b' x1' xs' where "simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')"
      using prod.exhaust by metis
    then have "simple_cg_closure_phase_1_helper x xss (b,don) = simple_cg_closure_phase_1_helper x xs' (b \<or> b', x1' # don)"
      unfolding Cons by auto
    
    have "length xs' < length xss"
      using simple_cg_closure_phase_1_helper'_length[of x x1 xs]
      unfolding \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> Cons by auto
    then have "length (snd (simple_cg_closure_phase_1_helper x xs' (b \<or> b', x1'#don))) \<le> length xs' + length (x1'#don)"
      using less[of xs'] unfolding Cons by blast
    moreover have "length xs' + length (x1'#don) \<le> length xss + length don"
      using simple_cg_closure_phase_1_helper'_length[of x x1 xs]
      unfolding \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> snd_conv Cons by auto
    ultimately show ?thesis
      unfolding \<open>simple_cg_closure_phase_1_helper x xss (b,don) = simple_cg_closure_phase_1_helper x xs' (b \<or> b', x1' # don)\<close> 
      by presburger
  qed
qed 


lemma simple_cg_closure_phase_1_helper_True :
  assumes "fst (simple_cg_closure_phase_1_helper x xss (False,don))" 
  and     "xss \<noteq> []"
shows "length (snd (simple_cg_closure_phase_1_helper x xss (False,don))) < length xss + length don"
  using assms
proof (induction "length xss" arbitrary: xss don rule: less_induct)
  case less
  show ?case proof (cases xss)
    case Nil
    then show ?thesis using less.prems(2) by auto
  next
    case (Cons x1 xs)
    obtain b' x1' xs' where "simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')"
      using prod.exhaust by metis
    then have "simple_cg_closure_phase_1_helper x xss (False,don) = simple_cg_closure_phase_1_helper x xs' (b', x1' # don)"
      unfolding Cons by auto

    show ?thesis proof (cases b')
      case True
      then have "length xs' < length xs"
        using simple_cg_closure_phase_1_helper'_True[of x x1 xs]
        unfolding \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> fst_conv snd_conv
        by blast
      then have "length (snd (simple_cg_closure_phase_1_helper x xs' (b', x1' # don))) < length xss + length don"
        using simple_cg_closure_phase_1_helper_length[of x xs' b' "x1'#don"]
        unfolding Cons
        by auto
      then show ?thesis 
        unfolding \<open>simple_cg_closure_phase_1_helper x xss (False,don) = simple_cg_closure_phase_1_helper x xs' (b', x1' # don)\<close> .
    next
      case False
      then have "simple_cg_closure_phase_1_helper x xss (False,don) = simple_cg_closure_phase_1_helper x xs' (False, x1' # don)"
        using \<open>simple_cg_closure_phase_1_helper x xss (False,don) = simple_cg_closure_phase_1_helper x xs' (b', x1' # don)\<close> 
        by auto
      then have "fst (simple_cg_closure_phase_1_helper x xs' (False, x1' # don))"
        using less.prems(1) by auto

      have "length xs' < length xss"
        using simple_cg_closure_phase_1_helper'_length[of x x1 xs]
        unfolding \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> Cons by auto

      have "xs' \<noteq> []"
        using \<open>simple_cg_closure_phase_1_helper' x x1 xs = (b',x1',xs')\<close> False
        by (metis \<open>fst (simple_cg_closure_phase_1_helper x xs' (False, x1' # don))\<close> simple_cg_closure_phase_1_helper.simps(1) fst_eqD)
  
      show ?thesis 
        using less.hyps[OF \<open>length xs' < length xss\<close> \<open>fst (simple_cg_closure_phase_1_helper x xs' (False, x1' # don))\<close> \<open>xs' \<noteq> []\<close>] \<open>length xs' < length xss\<close>
        unfolding \<open>simple_cg_closure_phase_1_helper x xss (False,don) = simple_cg_closure_phase_1_helper x xs' (False, x1' # don)\<close> 
        unfolding Cons 
        by auto
    qed
  qed
qed



(* closure operation (1) *)
fun simple_cg_closure_phase_1 :: "'a simple_cg \<Rightarrow> (bool \<times> 'a simple_cg)" where
  "simple_cg_closure_phase_1 xs = foldl (\<lambda> (b,xs) x. let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xs"

lemma simple_cg_closure_phase_1_validity :
  assumes "observable M1" and "observable M2"
  and     "\<And> x2 u v . x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (snd (simple_cg_closure_phase_1 xs))"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1" and "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
proof -

  have "\<And> xss x2 u v . (\<And> x2 u v . x2 \<in> list.set xss \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v) \<Longrightarrow> x2 \<in> list.set (snd (foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss)) \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  proof -
    fix xss x2 u v
    assume "\<And> x2 u v . x2 \<in> list.set xss \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
    and    "x2 \<in> list.set (snd (foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss))"
    and    "ts.memb u x2"
    and    "ts.memb v x2"
    and    "u \<in> L M1" 
    and    "u \<in> L M2"

    then show "converge M1 u v \<and> converge M2 u v"
    proof (induction xss arbitrary: x2 u v rule: rev_induct)
      case Nil
      then have "x2 \<in> list.set xs"
        by auto
      then show ?case 
        using Nil.prems(3,4,5,6) assms(3) by blast
    next
      case (snoc x xss)

      obtain b xss' where "(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss) = (b,xss')"
        using prod.exhaust by metis
      moreover obtain b' xss'' where "simple_cg_closure_phase_1_helper x xss' (False,[]) = (b',xss'')"
        using prod.exhaust by metis
      ultimately have *:"(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) (xss@[x])) = (b\<or>b',xss'')"
        by auto

      have "(\<And>u v. ts.memb u x \<Longrightarrow> ts.memb v x \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        using snoc.prems(1)
        by (metis append_Cons list.set_intros(1) list_set_sym) 
      moreover have "(\<And>x2 u v. x2 \<in> list.set [] \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        by auto
      moreover have "(\<And>x2 u v. x2 \<in> list.set xss' \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
      proof -
        have "(\<And>x2 u v. x2 \<in> list.set xss \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)" 
          using snoc.prems(1)
          by (metis (no_types, lifting) append_Cons append_Nil2 insertCI list.simps(15) list_set_sym)
        then show "(\<And>x2 u v. x2 \<in> list.set xss' \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
          using snoc.IH
          unfolding \<open>(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss) = (b,xss')\<close> snd_conv
          by blast
      qed
      ultimately have "(\<And>x2 u v. x2 \<in> list.set xss'' \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        using simple_cg_closure_phase_1_helper_validity[OF assms(1,2), of x "[]" xss' _ False]
        unfolding \<open>simple_cg_closure_phase_1_helper x xss' (False,[]) = (b',xss'')\<close> snd_conv
        by blast
      then show ?case
        using snoc.prems(2,3,4,5,6)
        unfolding *  snd_conv
        by blast 
    qed
  qed

  then show ?thesis
    using assms(3,4,5,6,7,8)
    unfolding simple_cg_closure_phase_1.simps
    by blast
qed

lemma simple_cg_closure_phase_1_length_helper :
  "length (snd (foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss)) \<le> length xs"
proof (induction xss rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xss)

  obtain b xss' where "(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss) = (b,xss')"
    using prod.exhaust by metis
  moreover obtain b' xss'' where "simple_cg_closure_phase_1_helper x xss' (False,[]) = (b',xss'')"
    using prod.exhaust by metis
  ultimately have *:"(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) (xss@[x])) = (b\<or>b',xss'')"
    by auto

  have "length xss' \<le> length xs"
    using snoc.IH
    unfolding \<open>(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss) = (b,xss')\<close>
    by auto
  moreover have "length xss'' \<le> length xss'"
    using simple_cg_closure_phase_1_helper_length[of x xss' False "[]"]
    unfolding \<open>simple_cg_closure_phase_1_helper x xss' (False,[]) = (b',xss'')\<close>
    by auto
  ultimately show ?case
    unfolding * snd_conv
    by simp
qed

lemma simple_cg_closure_phase_1_length : 
  "length (snd (simple_cg_closure_phase_1 xs)) \<le> length xs"
  using simple_cg_closure_phase_1_length_helper by auto

lemma simple_cg_closure_phase_1_True :
  assumes "fst (simple_cg_closure_phase_1 xs)" 
  shows "length (snd (simple_cg_closure_phase_1 xs)) < length xs"
proof -
  have "\<And> xss . fst (foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss) \<Longrightarrow> length (snd (foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss)) < length xs"
  proof -
    fix xss
    assume "fst (foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss)"
    then show "length (snd (foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss)) < length xs"
    proof (induction xss rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc x xss)

      obtain b xss' where "(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss) = (b,xss')"
        using prod.exhaust by metis
      moreover obtain b' xss'' where "simple_cg_closure_phase_1_helper x xss' (False,[]) = (b',xss'')"
        using prod.exhaust by metis
      ultimately have "(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) (xss@[x])) = (b\<or>b',xss'')"
        by auto

      consider b | b'
        using snoc.prems
        unfolding \<open>(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) (xss@[x])) = (b\<or>b',xss'')\<close> fst_conv
        by blast
      then show ?case proof cases
        case 1
        then have "length xss' < length xs"
          using snoc.IH 
          unfolding \<open>(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) xss) = (b,xss')\<close> fst_conv snd_conv
          by auto
        moreover have "length xss'' \<le> length xss'"
          using simple_cg_closure_phase_1_helper_length[of x xss' False "[]"]
          unfolding \<open>simple_cg_closure_phase_1_helper x xss' (False,[]) = (b',xss'')\<close>
          by auto
        ultimately show ?thesis
          unfolding \<open>(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) (xss@[x])) = (b\<or>b',xss'')\<close> snd_conv
          by simp
      next
        case 2
        have "length xss' \<le> length xs"
          using simple_cg_closure_phase_1_length_helper[of xss xs]
          by (metis \<open>foldl (\<lambda>(b, xs) x. let (b', xs') = simple_cg_closure_phase_1_helper x xs (False, []) in (b \<or> b', xs')) (False, xs) xss = (b, xss')\<close> simple_cg_closure_phase_1_length_helper snd_conv)
        moreover have "length xss'' < length xss'"
        proof -
          have "xss' \<noteq> []"
            using "2" \<open>simple_cg_closure_phase_1_helper x xss' (False, []) = (b', xss'')\<close> by auto
          then show ?thesis
            using simple_cg_closure_phase_1_helper_True[of x xss' "[]"] 2
            unfolding \<open>simple_cg_closure_phase_1_helper x xss' (False,[]) = (b',xss'')\<close> fst_conv snd_conv 
            by auto
        qed
        ultimately show ?thesis
          unfolding \<open>(foldl (\<lambda> (b,xs) x . let (b',xs') = simple_cg_closure_phase_1_helper x xs (False,[]) in (b\<or>b',xs')) (False,xs) (xss@[x])) = (b\<or>b',xss'')\<close> snd_conv
          by simp
      qed 
    qed
  qed
  then show ?thesis
    using assms by auto
qed




fun can_merge_by_intersection :: "'a ts \<Rightarrow> 'a ts \<Rightarrow> bool" where
  "can_merge_by_intersection x1 x2 = (\<exists> \<alpha> . ts.memb \<alpha> x1 \<and> ts.memb \<alpha> x2)"

lemma can_merge_by_intersection_code[code] : 
  "can_merge_by_intersection x1 x2 = ts.bex x1 (\<lambda> \<alpha> . ts.memb \<alpha> x2)"
  unfolding can_merge_by_intersection.simps
  unfolding ts.memb_correct[OF ts.invar]
  unfolding ts.bex_correct[OF ts.invar]
  by (meson notin_fset) 


lemma can_merge_by_intersection_validity :
  assumes "\<And> u v . ts.memb u x1 \<Longrightarrow> ts.memb v x1 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> u v . ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "can_merge_by_intersection x1 x2"
  and     "ts.memb u (ts.union x1 x2)"
  and     "ts.memb v (ts.union x1 x2)"
  and     "u \<in> L M1"
  and     "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
proof -
  obtain \<alpha> where "ts.memb \<alpha> x1" and "ts.memb \<alpha> x2" 
    using assms(3) by auto

  have "converge M1 u \<alpha> \<and> converge M2 u \<alpha>"
    using \<open>ts.memb \<alpha> x1\<close> \<open>ts.memb \<alpha> x2\<close> assms(1,2,4,6,7)
    unfolding ts.memb_correct[OF ts.invar]
    unfolding ts.union_correct[OF ts.invar ts.invar]
    by blast
  moreover have "converge M1 v \<alpha> \<and> converge M2 v \<alpha>"
    by (metis UnE \<open>ts.memb \<alpha> x1\<close> \<open>ts.memb \<alpha> x2\<close> assms(1) assms(2) assms(5) calculation converge.elims(2) ts.correct(18) ts.correct(5) ts.invar) 
  ultimately show ?thesis
    by simp
qed


fun simple_cg_closure_phase_2_helper :: "'a ts \<Rightarrow> 'a simple_cg \<Rightarrow> (bool \<times> 'a ts \<times> 'a simple_cg)" where
  "simple_cg_closure_phase_2_helper x1 xs = 
    (let (x2s,others) = separate_by (can_merge_by_intersection x1) xs;
         x1Union      = foldl (ts.union) x1 x2s
      in (x2s \<noteq> [],x1Union,others))"  

lemma simple_cg_closure_phase_2_helper_length :
  "length (snd (snd (simple_cg_closure_phase_2_helper x1 xs))) \<le> length xs"
  by auto

lemma simple_cg_closure_phase_2_helper_validity_fst :
  assumes "\<And> u v . ts.memb u x1 \<Longrightarrow> ts.memb v x1 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> x2 u v . x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "ts.memb u (fst (snd (simple_cg_closure_phase_2_helper x1 xs)))"
  and     "ts.memb v (fst (snd (simple_cg_closure_phase_2_helper x1 xs)))"
  and     "u \<in> L M1"
  and     "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
proof -

  have *:"\<And> w . ts.memb w (fst (snd (simple_cg_closure_phase_2_helper x1 xs))) \<Longrightarrow> 
                ts.memb w x1 \<or> (\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb w x2 \<and> can_merge_by_intersection x1 x2)"
  proof -

    fix w assume "ts.memb w (fst (snd (simple_cg_closure_phase_2_helper x1 xs)))"
    then have "ts.memb w (foldl ts.union x1 (filter (can_merge_by_intersection x1) xs))"
      unfolding simple_cg_closure_phase_1_helper'.simps 
      unfolding separate_by.simps Let_def case_prod_conv fst_conv snd_conv
      by auto
    then show "ts.memb w x1 \<or> (\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb w x2 \<and> can_merge_by_intersection x1 x2)"
    proof (induction xs rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc x' xs)

      show ?case proof (cases "can_merge_by_intersection x1 x'")
        case False
        then have "(foldl ts.union x1 (filter (can_merge_by_intersection x1) (xs @ [x'])))
                     = (foldl ts.union x1 (filter (can_merge_by_intersection x1) xs))"
          by auto
        then show ?thesis
          using snoc
          by (metis (no_types, opaque_lifting) append_Cons empty_append_eq_id insert_iff list.simps(15) list_set_sym) 
          
      next
        case True
        then have *: "(foldl ts.union x1 (filter (can_merge_by_intersection x1) (xs @ [x'])))
            = ts.union (foldl ts.union x1 (filter (can_merge_by_intersection x1) xs)) x'"
          by auto
        
        show ?thesis proof (cases "ts.memb w (foldl ts.union x1 (filter (can_merge_by_intersection x1) xs))")
          case True 
          then show ?thesis using snoc
            by (metis (no_types, opaque_lifting) append_Cons empty_append_eq_id insert_iff list.simps(15) list_set_sym) 
        next
          case False
          then have "ts.memb w x'"
            using snoc.prems unfolding * 
            unfolding ts.memb_correct[OF ts.invar]
            unfolding ts.union_correct[OF ts.invar ts.invar] 
            by blast
          then show ?thesis 
            using True
            by force
        qed
      qed
    qed
  qed

  consider "ts.memb u x1" | "(\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb u x2 \<and> can_merge_by_intersection x1 x2)"
    using *[OF assms(3)] by blast
  then show ?thesis proof cases
    case 1

    consider (a) "ts.memb v x1" | (b) "(\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb v x2 \<and> can_merge_by_intersection x1 x2)"
      using *[OF assms(4)] by blast
    then show ?thesis proof cases
      case a
      then show ?thesis using assms(1)[OF 1 _ assms(5,6)] by auto
    next
      case b
      then obtain x2v where "x2v \<in> list.set xs" and "ts.memb v x2v" and "can_merge_by_intersection x1 x2v"
        using *[OF assms(3)] 
        by blast
      show ?thesis 
        using can_merge_by_intersection_validity[of x1 M1 M2 x2v, OF assms(1) assms(2)[OF \<open>x2v \<in> list.set xs\<close>] \<open>can_merge_by_intersection x1 x2v\<close>]
        using 1 \<open>ts.memb v x2v\<close> assms(5,6)
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by blast
    qed    
  next
    case 2
    then obtain x2u where "x2u \<in> list.set xs" and "ts.memb u x2u" and "can_merge_by_intersection x1 x2u"
      using *[OF assms(3)] 
      by blast
    obtain \<alpha>u where "ts.memb \<alpha>u x1" and "ts.memb \<alpha>u x2u"
      using \<open>can_merge_by_intersection x1 x2u\<close> by auto

    consider (a) "ts.memb v x1" | (b) "(\<exists> x2 . x2 \<in> list.set xs \<and> ts.memb v x2 \<and> can_merge_by_intersection x1 x2)"
      using *[OF assms(4)] by blast
    then show ?thesis proof cases
      case a

      show ?thesis 
        using can_merge_by_intersection_validity[of x1 M1 M2 x2u, OF assms(1) assms(2)[OF \<open>x2u \<in> list.set xs\<close>] \<open>can_merge_by_intersection x1 x2u\<close>]
        using \<open>ts.memb u x2u\<close> a assms(5,6)
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by blast
    next 
      case b
      
      then obtain x2v where "x2v \<in> list.set xs" and "ts.memb v x2v" and "can_merge_by_intersection x1 x2v"
        using *[OF assms(4)] 
        by blast
      obtain \<alpha>v where "ts.memb \<alpha>v x1" and "ts.memb \<alpha>v x2v"
        using \<open>can_merge_by_intersection x1 x2v\<close> by auto

      have "\<And> v . ts.memb v (ts.union x1 x2u) \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
        using can_merge_by_intersection_validity[of x1 M1 M2 x2u, OF assms(1) assms(2)[OF \<open>x2u \<in> list.set xs\<close>] \<open>can_merge_by_intersection x1 x2u\<close> _ _ assms(5,6)] \<open>ts.memb u x2u\<close>
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by blast
      have "\<And> u . ts.memb u (ts.union x1 x2v) \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
        using can_merge_by_intersection_validity[of x1 M1 M2 x2v, OF assms(1) assms(2)[OF \<open>x2v \<in> list.set xs\<close>] \<open>can_merge_by_intersection x1 x2v\<close> ] \<open>ts.memb v x2v\<close>
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by blast


      show ?thesis
        using \<open>\<And>u. \<lbrakk>ts.memb u (ts.union x1 x2v); u \<in> L M1; u \<in> L M2\<rbrakk> \<Longrightarrow> converge M1 u v \<and> converge M2 u v\<close> \<open>\<And>v. ts.memb v (ts.union x1 x2u) \<Longrightarrow> converge M1 u v \<and> converge M2 u v\<close> \<open>ts.memb \<alpha>u x1\<close> 
        unfolding ts.memb_correct[OF ts.invar]
        unfolding ts.union_correct[OF ts.invar ts.invar] 
        by fastforce
    qed
  qed
qed


lemma simple_cg_closure_phase_2_helper_validity_snd :
  assumes "\<And> x2 u v . x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (snd (snd (simple_cg_closure_phase_2_helper x1 xs)))"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1"
  and     "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
proof -
  have "list.set (snd (snd (simple_cg_closure_phase_2_helper x1 xs))) \<subseteq> list.set xs"
    by auto
  then show ?thesis
    using assms by blast 
qed

lemma simple_cg_closure_phase_2_helper_True :
  assumes "fst (simple_cg_closure_phase_2_helper x xs)" 
shows "length (snd (snd (simple_cg_closure_phase_2_helper x xs))) < length xs"
proof -
  have "snd (snd (simple_cg_closure_phase_2_helper x xs)) = filter (\<lambda>x2 . \<not> (can_merge_by_intersection x x2)) xs"
    by auto
  moreover have "filter (\<lambda>x2 . (can_merge_by_intersection x x2)) xs \<noteq> []"
    using assms unfolding simple_cg_closure_phase_1_helper'.simps Let_def separate_by.simps
    by fastforce
  ultimately show ?thesis 
    using filter_not_all_length[of "can_merge_by_intersection x" xs]
    by metis
qed


function simple_cg_closure_phase_2' :: "'a simple_cg \<Rightarrow> (bool \<times> 'a simple_cg) \<Rightarrow> (bool \<times> 'a simple_cg)" where
  "simple_cg_closure_phase_2' [] (b,done) = (b,done)" |                                 
  "simple_cg_closure_phase_2' (x#xs) (b,done) = (let (hasChanged,x',xs') = simple_cg_closure_phase_2_helper x xs
    in if hasChanged then simple_cg_closure_phase_2' xs' (True,x'#done)
                     else simple_cg_closure_phase_2' xs (b,x#done))"
  by pat_completeness auto
termination  
proof -
  {
    fix xa :: "(bool \<times> 'a ts \<times> 'a simple_cg)"
    fix x xs b don xb y xaa ya
    assume "xa = simple_cg_closure_phase_2_helper x xs" 
    and    "(xb, y) = xa" 
    and    "(xaa, ya) = y" 
    and    xb
  
    have "length ya < Suc (length xs)"
      using simple_cg_closure_phase_2_helper_True[of x xs] \<open>xb\<close>
      unfolding \<open>xa = simple_cg_closure_phase_2_helper x xs\<close>[symmetric]
      unfolding \<open>(xb, y) = xa\<close>[symmetric] \<open>(xaa, ya) = y\<close>[symmetric]
      unfolding fst_conv snd_conv
      by auto
  
    then have "((ya, True, xaa # don), x # xs, b, don) \<in> measure (\<lambda>(xs, bd). length xs)"
      by auto
  }
  then show ?thesis by (relation "measure (\<lambda> (xs,bd) . length xs)"; force)
qed


lemma simple_cg_closure_phase_2'_validity :
  assumes "\<And> x2 u v . x2 \<in> list.set don \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "\<And> x2 u v . x2 \<in> list.set xss \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (snd (simple_cg_closure_phase_2' xss (b,don)))"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1"
  and     "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
  using assms(1,2,3)
proof (induction "length xss" arbitrary: xss b don rule: less_induct)
  case less
  show ?case proof (cases xss)
    case Nil
    show ?thesis using less.prems(3) less.prems(1)[OF _ assms(4,5,6,7)] unfolding Nil 
      by auto
  next
    case (Cons x xs)
    obtain hasChanged x' xs' where "simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')"
      using prod.exhaust by metis

    show ?thesis proof (cases hasChanged)
      case True
      then have "simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs' (True,x'#don)"
        using \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close>
        unfolding Cons  
        by auto

      have *:"(\<And>u v. ts.memb u x \<Longrightarrow> ts.memb v x \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)" and 
           **:"(\<And>x2 u v. x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        using less.prems(2) unfolding Cons
        by (meson list.set_intros)+

      have "length xs' < length xss"
        unfolding Cons 
        using simple_cg_closure_phase_2_helper_True[of x xs] True
        unfolding \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close> fst_conv snd_conv
        by auto
      moreover have "(\<And>x2 u v. x2 \<in> list.set (x' # don) \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"  
        using simple_cg_closure_phase_2_helper_validity_fst[of x M1 M2 xs, OF * **, of "\<lambda> a b c . a"] 
        using less.prems(1)
        unfolding \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close> fst_conv snd_conv
        using set_ConsD[of _ x' don] 
        by blast 
      moreover have "(\<And>x2 u v. x2 \<in> list.set xs' \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        using simple_cg_closure_phase_2_helper_validity_snd[of xs M1 M2 _ x, OF **, of "\<lambda> a b c . a"]
        unfolding \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close> fst_conv snd_conv
        by blast
      moreover have "x2 \<in> list.set (snd (simple_cg_closure_phase_2' xs' (True, x' # don)))"
        using less.prems(3) unfolding \<open>simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs' (True,x'#don)\<close> .
      ultimately show ?thesis 
        using less.hyps[of xs' "x'#don"]
        by blast
    next
      case False
      then have "simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs (b,x#don)"
        using \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close>
        unfolding Cons  
        by auto

      have "length xs < length xss"
        unfolding Cons by auto
      moreover have "(\<And>x2 u v. x2 \<in> list.set (x # don) \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        using less.prems(1,2) unfolding Cons
        by (metis list.set_intros(1) set_ConsD) 
      moreover have "(\<And>x2 u v. x2 \<in> list.set xs \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        using less.prems(2) unfolding Cons
        by (metis list.set_intros(2))
      moreover have "x2 \<in> list.set (snd (simple_cg_closure_phase_2' xs (b, x # don)))"
        using less.prems(3)
        unfolding \<open>simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs (b,x#don)\<close>
        unfolding Cons .
      ultimately show ?thesis 
        using less.hyps[of xs "x#don" b]
        by blast
    qed
  qed
qed


lemma simple_cg_closure_phase_2'_length :
  "length (snd (simple_cg_closure_phase_2' xss (b,don))) \<le> length xss + length don"
proof (induction "length xss" arbitrary: xss b don rule: less_induct)
  case less
  show ?case proof (cases xss)
    case Nil
    then show ?thesis by auto
  next
    case (Cons x xs)
    obtain hasChanged x' xs' where "simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')"
      using prod.exhaust by metis

    show ?thesis proof (cases hasChanged)
      case True
      then have "simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs' (True,x'#don)"
        using \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close>
        unfolding Cons  
        by auto
      have "length xs' < length xss"
        using simple_cg_closure_phase_2_helper_True[of x xs] True
        unfolding \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close> snd_conv fst_conv
        unfolding Cons
        by auto

      then show ?thesis
        using less.hyps[of xs' True "x'#don"] 
        unfolding \<open>simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs' (True,x'#don)\<close> 
        unfolding Cons by auto
    next
      case False 
      then have "simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs (b,x#don)"
        using \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close>
        unfolding Cons  
        by auto

      show ?thesis
        using less.hyps[of xs b "x#don"]
        unfolding \<open>simple_cg_closure_phase_2' xss (b,don) = simple_cg_closure_phase_2' xs (b,x#don)\<close>
        unfolding Cons
        by auto
    qed
  qed
qed


lemma simple_cg_closure_phase_2'_True :
  assumes "fst (simple_cg_closure_phase_2' xss (False,don))" 
  and     "xss \<noteq> []"
shows "length (snd (simple_cg_closure_phase_2' xss (False,don))) < length xss + length don"
  using assms
proof (induction "length xss" arbitrary: xss don rule: less_induct)
  case less
  show ?case proof (cases xss)
    case Nil
    then show ?thesis 
      using less.prems(2) by auto
  next
    case (Cons x xs)
    obtain hasChanged x' xs' where "simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')"
      using prod.exhaust by metis

    show ?thesis proof (cases hasChanged)
      case True
      then have "simple_cg_closure_phase_2' xss (False,don) = simple_cg_closure_phase_2' xs' (True,x'#don)"
        using \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close>
        unfolding Cons  
        by auto
      have "length xs' < length xs"
        using simple_cg_closure_phase_2_helper_True[of x xs] True
        unfolding \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close> snd_conv fst_conv
        unfolding Cons
        by auto
      moreover have "length (snd (simple_cg_closure_phase_2' xs' (True,x'#don))) \<le> length xs' + length (x'#don)"
        using simple_cg_closure_phase_2'_length by metis
      ultimately show ?thesis
        unfolding \<open>simple_cg_closure_phase_2' xss (False,don) = simple_cg_closure_phase_2' xs' (True,x'#don)\<close>
        unfolding Cons
        by auto
    next
      case False 
      then have "simple_cg_closure_phase_2' xss (False,don) = simple_cg_closure_phase_2' xs (False,x#don)"
        using \<open>simple_cg_closure_phase_2_helper x xs = (hasChanged,x',xs')\<close>
        unfolding Cons  
        by auto

      have "xs \<noteq> []"
        using \<open>simple_cg_closure_phase_2' xss (False, don) = simple_cg_closure_phase_2' xs (False, x # don)\<close> less.prems(1) by auto

      show ?thesis
        using less.hyps[of xs "x#don", OF _ _ \<open>xs \<noteq> []\<close>]
        using less.prems(1)
        unfolding \<open>simple_cg_closure_phase_2' xss (False,don) = simple_cg_closure_phase_2' xs (False,x#don)\<close>
        unfolding Cons
        by auto
    qed
  qed
qed


(* closure operation (2) *)
fun simple_cg_closure_phase_2 :: "'a simple_cg \<Rightarrow> (bool \<times> 'a simple_cg)" where
  "simple_cg_closure_phase_2 xs = simple_cg_closure_phase_2' xs (False,[])" 


lemma simple_cg_closure_phase_2_validity :
  assumes "\<And> x2 u v . x2 \<in> list.set xss \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (snd (simple_cg_closure_phase_2 xss))"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1"
  and     "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
  using assms(2)
  unfolding simple_cg_closure_phase_2.simps
  using simple_cg_closure_phase_2'_validity[OF _ assms(1) _ assms(3,4,5,6), of "[]" xss "\<lambda> a b c . a" False] 
  by auto

lemma simple_cg_closure_phase_2_length :
  "length (snd (simple_cg_closure_phase_2 xss)) \<le> length xss"
  unfolding simple_cg_closure_phase_2.simps
  using simple_cg_closure_phase_2'_length[of xss False "[]"] 
  by auto

lemma simple_cg_closure_phase_2_True :
  assumes "fst (simple_cg_closure_phase_2 xss)" 
shows "length (snd (simple_cg_closure_phase_2 xss)) < length xss"
proof -
  have "xss \<noteq> []"
    using assms by auto
  then show ?thesis
    using simple_cg_closure_phase_2'_True[of xss "[]"] assms by auto
qed



function simple_cg_closure :: "'a simple_cg \<Rightarrow> 'a simple_cg" where
  "simple_cg_closure g = (let (hasChanged1,g1) = simple_cg_closure_phase_1 g;
                       (hasChanged2,g2) = simple_cg_closure_phase_2 g1
     in if hasChanged1 \<or> hasChanged2
        then simple_cg_closure g2
        else g2)"
  by pat_completeness auto
termination
proof -
  {
    fix g :: "'a simple_cg"
    fix x hasChanged1 g1 xb hasChanged2 g2
    assume "x = simple_cg_closure_phase_1 g" 
           "(hasChanged1, g1) = x" 
           "xb = simple_cg_closure_phase_2 g1" 
           "(hasChanged2, g2) = xb" 
           "hasChanged1 \<or> hasChanged2"
  
    then have "simple_cg_closure_phase_1 g = (hasChanged1, g1)"
          and "simple_cg_closure_phase_2 g1 = (hasChanged2, g2)"
      by auto
  
    have "length g1 \<le> length g"
      using \<open>simple_cg_closure_phase_1 g = (hasChanged1, g1)\<close>
      using simple_cg_closure_phase_1_length[of g] 
      by auto 
    have "length g2 \<le> length g1"
      using \<open>simple_cg_closure_phase_2 g1 = (hasChanged2, g2)\<close>
      using simple_cg_closure_phase_2_length[of g1] 
      by auto
    
  
    consider hasChanged1 | hasChanged2
      using \<open>hasChanged1 \<or> hasChanged2\<close> by blast
    then have "length g2 < length g"
    proof cases
      case 1
      then have "length g1 < length g"
        using \<open>simple_cg_closure_phase_1 g = (hasChanged1, g1)\<close>
        using simple_cg_closure_phase_1_True[of g]
        by auto
      then show ?thesis
        using \<open>length g2 \<le> length g1\<close>
        by linarith
    next
      case 2
      then have "length g2 < length g1"
        using \<open>simple_cg_closure_phase_2 g1 = (hasChanged2, g2)\<close>
        using simple_cg_closure_phase_2_True[of g1]
        by auto
      then show ?thesis
        using \<open>length g1 \<le> length g\<close>
        by linarith
    qed
    then have "(g2, g) \<in> measure length"
      by auto
  }
  then show ?thesis by (relation "measure length"; simp)
qed


lemma simple_cg_closure_validity :
  assumes "observable M1" and "observable M2"
  and     "\<And> x2 u v . x2 \<in> list.set g \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (simple_cg_closure g)"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1"
  and     "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
  using assms(3,4)
proof (induction "length g" arbitrary: g rule: less_induct)
  case less

  obtain hasChanged1 hasChanged2 g1 g2 where "simple_cg_closure_phase_1 g = (hasChanged1, g1)"
                                         and "simple_cg_closure_phase_2 g1 = (hasChanged2, g2)"
    using prod.exhaust by metis

  have "length g1 \<le> length g"
    using \<open>simple_cg_closure_phase_1 g = (hasChanged1, g1)\<close>
    using simple_cg_closure_phase_1_length[of g] 
    by auto 
  have "length g2 \<le> length g1"
    using \<open>simple_cg_closure_phase_2 g1 = (hasChanged2, g2)\<close>
    using simple_cg_closure_phase_2_length[of g1] 
    by auto

  have "(\<And>x2 u v. x2 \<in> list.set g2 \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
  proof -
    have "(\<And>x2 u v. x2 \<in> list.set g1 \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
      using simple_cg_closure_phase_1_validity[OF assms(1,2), of g]
      using less.prems(1)
      unfolding \<open>simple_cg_closure_phase_1 g = (hasChanged1, g1)\<close> snd_conv 
      by blast
    then show "(\<And>x2 u v. x2 \<in> list.set g2 \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
      using simple_cg_closure_phase_2_validity[of g1]
      unfolding \<open>simple_cg_closure_phase_2 g1 = (hasChanged2, g2)\<close> snd_conv
      by blast
  qed 

  show ?thesis proof (cases "hasChanged1 \<or> hasChanged2")
    case True
    then consider hasChanged1 | hasChanged2
      by blast
    then have "length g2 < length g"
    proof cases
      case 1
      then have "length g1 < length g"
        using \<open>simple_cg_closure_phase_1 g = (hasChanged1, g1)\<close>
        using simple_cg_closure_phase_1_True[of g]
        by auto
      then show ?thesis
        using \<open>length g2 \<le> length g1\<close>
        by linarith
    next
      case 2
      then have "length g2 < length g1"
        using \<open>simple_cg_closure_phase_2 g1 = (hasChanged2, g2)\<close>
        using simple_cg_closure_phase_2_True[of g1]
        by auto
      then show ?thesis
        using \<open>length g1 \<le> length g\<close>
        by linarith
    qed
    moreover have "x2 \<in> list.set (simple_cg_closure g2)"
      using less.prems(2)
      using \<open>simple_cg_closure_phase_1 g = (hasChanged1, g1)\<close> \<open>simple_cg_closure_phase_2 g1 = (hasChanged2, g2)\<close> True
      by auto
    moreover note \<open>(\<And>x2 u v. x2 \<in> list.set g2 \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)\<close>
    ultimately show ?thesis 
      using less.hyps[of g2]
      by blast      
  next
    case False
    then have "(simple_cg_closure g) = g2"
      using \<open>simple_cg_closure_phase_1 g = (hasChanged1, g1)\<close> \<open>simple_cg_closure_phase_2 g1 = (hasChanged2, g2)\<close> 
      by auto
    show ?thesis 
      using less.prems(2)
      using \<open>(\<And>x2 u v. x2 \<in> list.set g2 \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)\<close> assms(5,6,7,8)
      unfolding \<open>(simple_cg_closure g) = g2\<close>
      by blast
  qed
qed


(* when inserting \<alpha> this also for all \<alpha>1@\<alpha>2 = \<alpha> and \<beta> in [\<alpha>1] inserts \<beta>@\<alpha>2 -- extremely inefficient *)
fun simple_cg_insert_with_conv :: "('a::linorder) simple_cg \<Rightarrow> 'a list \<Rightarrow> 'a simple_cg" where
  "simple_cg_insert_with_conv g ys = (let
      insert_for_prefix = (\<lambda> g i . let
                                    pref = take i ys;
                                    suff = drop i ys;
                                    pref_conv = simple_cg_lookup g pref
                                  in foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) g pref_conv);
      g' = simple_cg_insert g ys;
      g'' = foldl insert_for_prefix g' [0..<length ys]
  in simple_cg_closure g'')"


fun simple_cg_merge :: "'a simple_cg \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a simple_cg" where
  "simple_cg_merge g ys1 ys2 = simple_cg_closure (ts.from_list [ys1,ys2] #g)"

lemma simple_cg_merge_validity :
  assumes "observable M1" and "observable M2"
  and     "converge M1 u' v' \<and> converge M2 u' v'"
  and     "\<And> x2 u v . x2 \<in> list.set g \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
  and     "x2 \<in> list.set (simple_cg_merge g u' v')"
  and     "ts.memb u x2"
  and     "ts.memb v x2"
  and     "u \<in> L M1"
  and     "u \<in> L M2"
shows "converge M1 u v \<and> converge M2 u v"
proof -
  have "(\<And>x2 u v. x2 \<in> list.set ((ts.from_list [u',v'])#g) \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
  proof -
    fix x2 u v assume "x2 \<in> list.set ((ts.from_list [u',v'])#g)" and "ts.memb u x2" and "ts.memb v x2" and "u \<in> L M1" and "u \<in> L M2"
    then consider "x2 = (ts.from_list [u',v'])" | "x2 \<in> list.set g"
      by auto
    then show "converge M1 u v \<and> converge M2 u v" proof cases
      case 1
      have "u \<in> {u',v'}" and "v \<in> {u',v'}"
        using \<open>ts.memb u x2\<close> \<open>ts.memb v x2\<close> 
        unfolding ts.memb_correct[OF ts.invar] 1 ts.correct(35)
        by auto
      then show ?thesis 
        using assms(3) 
        by (cases "u = u'"; cases "v = v'"; auto)
    next
      case 2
      then show ?thesis 
        using assms(4) \<open>ts.memb u x2\<close> \<open>ts.memb v x2\<close> \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close>
        by blast
    qed
  qed
  moreover have "x2 \<in> list.set (simple_cg_closure ((ts.from_list [u',v'])#g))"  
    using assms(5) by auto
  ultimately show ?thesis
    using simple_cg_closure_validity[OF assms(1,2) _ _ assms(6,7,8,9)]
    by blast
qed
  



subsection \<open>Invariants\<close>


lemma simple_cg_lookup_iff :
  "\<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<longleftrightarrow> (\<beta> = \<alpha> \<or> (\<exists> x . x \<in> list.set G \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x))"
proof (induction G rule: rev_induct)
  case Nil
  then show ?case 
    unfolding simple_cg_lookup.simps
    unfolding ts.correct(33)[OF ts.invar]
    unfolding ts.ins_correct[OF ts.invar]
    unfolding ts.memb_correct[OF ts.invar]
    unfolding filter.simps foldl.simps 
    unfolding ts.empty_correct
    by auto
next
  case (snoc x G)
  show ?case proof (cases "ts.memb \<alpha> x \<and> ts.memb \<beta> x")
    case True
    then have *: "(foldl ts.union (ts.empty ()) (filter (ts.memb \<alpha>) (G @ [x])))
                = ts.union (foldl ts.union (ts.empty ()) (filter (ts.memb \<alpha>) G)) x"
      by auto
    have "\<beta> \<in> list.set (simple_cg_lookup (G@[x]) \<alpha>)"
      using True
      unfolding simple_cg_lookup.simps *
      unfolding ts.correct(33)[OF ts.invar]
      unfolding ts.ins_correct[OF ts.invar]
      unfolding ts.memb_correct[OF ts.invar]
      unfolding ts.union_correct[OF ts.invar ts.invar]
      by blast
    then show ?thesis
      by (meson True in_set_conv_decomp)
  next
    case False
    have "\<beta> \<in> list.set (simple_cg_lookup (G@[x]) \<alpha>) = (\<beta> = \<alpha> \<or> (\<beta> \<in> list.set (simple_cg_lookup G \<alpha>)))"
    proof -
      consider "\<not> (ts.memb \<alpha> x)" | "\<not> (ts.memb \<beta> x)"
        using False by blast
      then show "\<beta> \<in> list.set (simple_cg_lookup (G@[x]) \<alpha>) = (\<beta> = \<alpha> \<or> (\<beta> \<in> list.set (simple_cg_lookup G \<alpha>)))"
      proof cases
        case 1
        then show ?thesis  
          unfolding simple_cg_lookup.simps
          unfolding ts.correct(33)[OF ts.invar]
          unfolding ts.ins_correct[OF ts.invar]
          unfolding ts.memb_correct[OF ts.invar]
          unfolding ts.union_correct[OF ts.invar ts.invar]
          by auto
      next
        case 2 
        then have "ts.memb \<beta> (foldl ts.union (ts.empty ()) (filter (ts.memb \<alpha>) (G @ [x])))
                   = ts.memb \<beta> (foldl ts.union (ts.empty ()) (filter (ts.memb \<alpha>) G))"
        proof (cases "ts.memb \<alpha> x")
          case True
          then have *: "(foldl ts.union (ts.empty ()) (filter (ts.memb \<alpha>) (G @ [x])))
                     = ts.union (foldl ts.union (ts.empty ()) (filter (ts.memb \<alpha>) G)) x"
            by auto
          show ?thesis 
            using 2
            unfolding *
            unfolding ts.memb_correct[OF ts.invar]
            unfolding ts.union_correct[OF ts.invar ts.invar]
            by auto
        next
          case False
          then show ?thesis by auto
        qed
        then have "(\<beta> \<in> list.set (simple_cg_lookup (G@[x]) \<alpha>)) = (\<beta> \<in> Set.insert \<alpha> (list.set (simple_cg_lookup G \<alpha>)))"
          unfolding simple_cg_lookup.simps
          unfolding ts.correct(33)[OF ts.invar]
          unfolding ts.ins_correct[OF ts.invar]
          unfolding ts.memb_correct[OF ts.invar]
          unfolding ts.union_correct[OF ts.invar ts.invar]
          by auto
        then show ?thesis 
          by (induction G; auto)
      qed 
    qed
    moreover have "(\<exists> x' . x' \<in> list.set (G@[x]) \<and> ts.memb \<alpha> x' \<and> ts.memb \<beta> x') = (\<exists> x . x \<in> list.set G \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x)"
      using False by auto
    ultimately show ?thesis
      using snoc.IH
      by blast
  qed
qed


lemma simple_cg_insert'_invar :
  "convergence_graph_insert_invar M1 M2 simple_cg_lookup simple_cg_insert'"
proof -
  have "\<And> G \<gamma> \<alpha> \<beta> . \<gamma> \<in> L M1 \<Longrightarrow>
          \<gamma> \<in> L M2 \<Longrightarrow>
          (\<And>\<alpha> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup G \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)) \<Longrightarrow>
          \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup (simple_cg_insert' G \<gamma>) \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert' G \<gamma>) \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  proof 
    fix G \<gamma> \<alpha> 
    assume "\<gamma> \<in> L M1"
    and    "\<gamma> \<in> L M2"
    and  *:"(\<And>\<alpha> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup G \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>))"
    and    "\<alpha> \<in> L M1" 
    and    "\<alpha> \<in> L M2"

    show "\<alpha> \<in> list.set (simple_cg_lookup (simple_cg_insert' G \<gamma>) \<alpha>)"
      unfolding simple_cg_lookup.simps
      unfolding ts.correct(33)[OF ts.invar]
      unfolding ts.ins_correct[OF ts.invar]
      by blast

    have "\<And> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert' G \<gamma>) \<alpha>) \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"
    proof -
      fix \<beta>
      assume **: "\<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert' G \<gamma>) \<alpha>)"
      show "converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"

    proof (cases "\<beta> \<in> list.set (simple_cg_lookup G \<alpha>)")
      case True
      then show ?thesis 
        using *[OF \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close>]
        by presburger 
    next
      case False

      show ?thesis proof (cases "find (\<lambda>x . ts.memb \<gamma> x) G")
        case None
        then have "(simple_cg_insert' G \<gamma>) = (ts.sng \<gamma>)#G" 
          by auto

        have "\<alpha> = \<gamma> \<and> \<beta> = \<gamma>"
          using False \<open>\<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert' G \<gamma>) \<alpha>)\<close> 
          unfolding \<open>(simple_cg_insert' G \<gamma>) = (ts.sng \<gamma>)#G\<close>
          unfolding simple_cg_lookup_iff
          unfolding ts.memb_correct[OF ts.invar] 
          using ts.sng_correct(1)
          by auto
        then show ?thesis
          using \<open>\<gamma> \<in> L M1\<close> \<open>\<gamma> \<in> L M2\<close> by auto
      next
        case (Some x)
        then have "(simple_cg_insert' G \<gamma>) = G" 
          by auto
        then show ?thesis 
          using *[OF \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close>] **
          by presburger
        qed
      qed
    qed
    then show "(\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert' G \<gamma>) \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
      by blast
  qed
  then show ?thesis
    unfolding convergence_graph_insert_invar_def convergence_graph_lookup_invar_def
    by blast
qed


lemma simple_cg_insert'_foldl_helper:
  assumes "list.set xss \<subseteq> L M1 \<inter> L M2"
  and     "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
shows     "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (foldl (\<lambda> xs' ys' . simple_cg_insert' xs' ys') G xss) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  using \<open>list.set xss \<subseteq> L M1 \<inter> L M2\<close>
proof (induction xss rule: rev_induct)
  case Nil
  then show ?case 
    using \<open>(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)\<close>
    by auto
next
  case (snoc x xs)

  have "x \<in> L M1" and "x \<in> L M2"
    using snoc.prems by auto
  
  have "list.set xs \<subseteq> L M1 \<inter> L M2"
    using snoc.prems by auto
  then have *:"(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (foldl (\<lambda> xs' ys'. simple_cg_insert' xs' ys') G xs) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
    using snoc.IH
    by blast

  have **:"(foldl (\<lambda> xs' ys'. simple_cg_insert' xs' ys') G (xs@[x])) = simple_cg_insert' (foldl (\<lambda> xs' ys' . simple_cg_insert' xs' ys') G xs) x"
    by auto        

  show ?case 
    using snoc.prems(1,2,3) * \<open>x \<in> L M1\<close> \<open>x \<in> L M2\<close>
    unfolding **
    using simple_cg_insert'_invar[of M1 M2]
    unfolding convergence_graph_insert_invar_def convergence_graph_lookup_invar_def
    using simple_cg_lookup_iff 
    by blast
qed


lemma simple_cg_insert_invar :                  
  "convergence_graph_insert_invar M1 M2 simple_cg_lookup simple_cg_insert"
proof -

  have "\<And> G \<gamma> \<alpha> \<beta> . \<gamma> \<in> L M1 \<Longrightarrow>
          \<gamma> \<in> L M2 \<Longrightarrow>
          (\<And>\<alpha> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup G \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)) \<Longrightarrow>
          \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup (simple_cg_insert G \<gamma>) \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert G \<gamma>) \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  proof 
    fix G \<gamma> \<alpha> 
    assume "\<gamma> \<in> L M1"
    and    "\<gamma> \<in> L M2"
    and  *:"(\<And>\<alpha> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup G \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>))"
    and    "\<alpha> \<in> L M1" 
    and    "\<alpha> \<in> L M2"

    show "\<alpha> \<in> list.set (simple_cg_lookup (simple_cg_insert G \<gamma>) \<alpha>)" 
      unfolding simple_cg_lookup.simps
      unfolding ts.correct(33)[OF ts.invar]
      unfolding ts.ins_correct[OF ts.invar]
      by auto

    note simple_cg_insert'_foldl_helper[of "prefixes \<gamma>" M1 M2]
    moreover have "list.set (prefixes \<gamma>) \<subseteq> L M1 \<inter> L M2"
      by (metis (no_types, lifting) IntI \<open>\<gamma> \<in> L M1\<close> \<open>\<gamma> \<in> L M2\<close> language_prefix prefixes_set_ob subsetI) 
    ultimately show "(\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert G \<gamma>) \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"      
      using \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close>
      by (metis "*" simple_cg_insert.simps) 
  qed
  then show ?thesis
    unfolding convergence_graph_insert_invar_def convergence_graph_lookup_invar_def
    by blast
qed


lemma simple_cg_closure_invar_helper :
  assumes "observable M1" and "observable M2"
  and     "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  and     "\<beta> \<in> list.set (simple_cg_lookup (simple_cg_closure G) \<alpha>)"
  and     "\<alpha> \<in> L M1" and "\<alpha> \<in> L M2"
shows "converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"
proof (cases "\<beta> = \<alpha>")
  case True
  then show ?thesis using assms(5,6) by auto 
next
  case False
  show ?thesis 
  proof 
  
    obtain x where "x \<in> list.set (simple_cg_closure G)" and "ts.memb \<alpha> x" and "ts.memb \<beta> x"
      using False \<open>\<beta> \<in> list.set (simple_cg_lookup (simple_cg_closure G) \<alpha>)\<close> unfolding simple_cg_lookup_iff
      by blast
  
    have "\<And> x2 u v . x2 \<in> list.set G \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v"
      using \<open>(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)\<close> 
      unfolding simple_cg_lookup_iff
      by blast
  
  
  
    have "(\<And>x2 u v. x2 \<in> list.set G \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
      using \<open>(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)\<close> 
      unfolding simple_cg_lookup_iff by blast
    then show "converge M1 \<alpha> \<beta>"
      using \<open>ts.memb \<alpha> x\<close> \<open>ts.memb \<beta> x\<close> \<open>x \<in> list.set (simple_cg_closure G)\<close> assms(1) assms(2) assms(5) assms(6) simple_cg_closure_validity by blast
  
    have "(\<And>x2 u v. x2 \<in> list.set G \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
      using \<open>(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)\<close> 
      unfolding simple_cg_lookup_iff by blast
    then show "converge M2 \<alpha> \<beta>"
      using \<open>ts.memb \<alpha> x\<close> \<open>ts.memb \<beta> x\<close> \<open>x \<in> list.set (simple_cg_closure G)\<close> assms(1) assms(2) assms(5) assms(6) simple_cg_closure_validity by blast    
  qed
qed



lemma simple_cg_merge_invar :
  assumes "observable M1" and "observable M2"
shows "convergence_graph_merge_invar M1 M2 simple_cg_lookup simple_cg_merge"
proof -

  have *: "\<And> G \<gamma> \<gamma>' \<alpha> \<beta>.
       converge M1 \<gamma> \<gamma>' \<Longrightarrow>
       converge M2 \<gamma> \<gamma>' \<Longrightarrow>
       (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>) \<Longrightarrow>
       \<beta> \<in> list.set (simple_cg_lookup (simple_cg_merge G \<gamma> \<gamma>') \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"
  proof -
    fix G \<gamma> \<gamma>' \<alpha> \<beta>
    assume "converge M1 \<gamma> \<gamma>'"
           "converge M2 \<gamma> \<gamma>'"
           "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
           "\<beta> \<in> list.set (simple_cg_lookup (simple_cg_merge G \<gamma> \<gamma>') \<alpha>)"
           "\<alpha> \<in> L M1" 
           "\<alpha> \<in> L M2"
    show "converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"
    proof (cases "\<beta> = \<alpha>")
      case True
      then show ?thesis using \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close> by auto
    next
      case False
      then obtain x where "x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>')" and "ts.memb \<alpha> x" and "ts.memb \<beta> x"
        using \<open>\<beta> \<in> list.set (simple_cg_lookup (simple_cg_merge G \<gamma> \<gamma>') \<alpha>)\<close> unfolding simple_cg_lookup_iff
        by blast
  
      have "(\<And>x2 u v. x2 \<in> list.set G \<Longrightarrow> ts.memb u x2 \<Longrightarrow> ts.memb v x2 \<Longrightarrow> u \<in> L M1 \<Longrightarrow> u \<in> L M2 \<Longrightarrow> converge M1 u v \<and> converge M2 u v)"
        using \<open>(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)\<close> 
        unfolding simple_cg_lookup_iff by blast
      then show ?thesis
        using simple_cg_merge_validity[OF assms(1,2) _ _ \<open>x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>')\<close> \<open>ts.memb \<alpha> x\<close> \<open>ts.memb \<beta> x\<close> \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close>] 
              \<open>converge M1 \<gamma> \<gamma>'\<close> \<open>converge M2 \<gamma> \<gamma>'\<close>
        by blast
    qed
  qed

  have "\<And>G \<gamma> \<gamma>'.
       converge M1 \<gamma> \<gamma>' \<Longrightarrow>
       converge M2 \<gamma> \<gamma>' \<Longrightarrow>
       (\<And>\<alpha>. \<alpha> \<in> L M1 \<Longrightarrow>
             \<alpha> \<in> L M2 \<Longrightarrow>
             (\<alpha> = \<alpha> \<or> (\<exists>x. x \<in> list.set G \<and> ts.memb \<alpha> x \<and> ts.memb \<alpha> x)) \<and>
             (\<forall>\<beta>. \<beta> = \<alpha> \<or> (\<exists>x. x \<in> list.set G \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x) \<longrightarrow>
                  converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)) \<Longrightarrow>
       (\<And>\<alpha>. \<alpha> \<in> L M1 \<Longrightarrow>
             \<alpha> \<in> L M2 \<Longrightarrow>
             (\<alpha> = \<alpha> \<or> (\<exists>x. x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>') \<and> ts.memb \<alpha> x \<and> ts.memb \<alpha> x)) \<and>
             (\<forall>\<beta>. \<beta> = \<alpha> \<or>
                  (\<exists>x. x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>') \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x) \<longrightarrow>
                  converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>))"
  proof -
    fix G \<gamma> \<gamma>' assume a1: "converge M1 \<gamma> \<gamma>'"
                  and a2: "converge M2 \<gamma> \<gamma>'"
                  and a3: "(\<And>\<alpha>. \<alpha> \<in> L M1 \<Longrightarrow>
             \<alpha> \<in> L M2 \<Longrightarrow>
             (\<alpha> = \<alpha> \<or> (\<exists>x. x \<in> list.set G \<and> ts.memb \<alpha> x \<and> ts.memb \<alpha> x)) \<and>
             (\<forall>\<beta>. \<beta> = \<alpha> \<or> (\<exists>x. x \<in> list.set G \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x) \<longrightarrow>
                  converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>))"

    fix \<alpha> assume "\<alpha> \<in> L M1" and "\<alpha> \<in> L M2"

    have "\<And> \<beta>. \<beta> = \<alpha> \<or>
                  (\<exists>x. x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>') \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x) \<Longrightarrow>
                  converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"
    proof -
      fix \<beta> assume assm: "\<beta> = \<alpha> \<or> (\<exists>x. x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>') \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x)"
      show "converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"
      proof (cases "\<beta> = \<alpha>")
        case True
        then show ?thesis
          using \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close> assms(1,2) converge_refl by auto
      next
        case False
        then obtain x where "x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>')" and "ts.memb \<alpha> x" and "ts.memb \<beta> x"
          using assm by blast
        then have "\<beta> \<in> list.set (simple_cg_lookup (simple_cg_merge G \<gamma> \<gamma>') \<alpha>)"
          unfolding simple_cg_lookup_iff by blast
        show ?thesis
          using *[OF a1 a2 _ \<open>\<beta> \<in> list.set (simple_cg_lookup (simple_cg_merge G \<gamma> \<gamma>') \<alpha>)\<close> \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close>]
          by (metis a3 simple_cg_lookup_iff) 
      qed
    qed
    then show "(\<alpha> = \<alpha> \<or> (\<exists>x. x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>') \<and> ts.memb \<alpha> x \<and> ts.memb \<alpha> x)) \<and> (\<forall>\<beta>. \<beta> = \<alpha> \<or>
                  (\<exists>x. x \<in> list.set (simple_cg_merge G \<gamma> \<gamma>') \<and> ts.memb \<alpha> x \<and> ts.memb \<beta> x) \<longrightarrow>
                  converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
      by blast
  qed
  then show ?thesis 
    unfolding convergence_graph_merge_invar_def convergence_graph_lookup_invar_def
    unfolding simple_cg_lookup_iff [symmetric]
    by blast
qed


lemma simple_cg_empty_invar :
  "convergence_graph_lookup_invar M1 M2 simple_cg_lookup simple_cg_empty"
  unfolding convergence_graph_lookup_invar_def simple_cg_empty_def 
  unfolding simple_cg_lookup_iff
  using converge_refl
  by auto


lemma simple_cg_initial_invar :
  assumes "observable M1"
  shows "convergence_graph_initial_invar M1 M2 simple_cg_lookup simple_cg_initial"
proof -

  have "\<And> T . (L M1 \<inter> set T = (L M2 \<inter> set T)) \<Longrightarrow> finite_tree T \<Longrightarrow> (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (simple_cg_initial M1 T) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  proof -
    fix T assume "(L M1 \<inter> set T = (L M2 \<inter> set T))" and "finite_tree T"
    then have "list.set (filter (is_in_language M1 (initial M1)) (sorted_list_of_sequences_in_tree T)) \<subseteq> L M1 \<inter> L M2"
      unfolding is_in_language_iff[OF assms fsm_initial]
      using sorted_list_of_sequences_in_tree_set[OF \<open>finite_tree T\<close>]
      by auto 
    moreover have "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup simple_cg_empty \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
      using simple_cg_empty_invar
      unfolding convergence_graph_lookup_invar_def
      by blast
    ultimately show "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (simple_cg_initial M1 T) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
      using simple_cg_insert'_foldl_helper[of "(filter (is_in_language M1 (initial M1)) (sorted_list_of_sequences_in_tree T))" M1 M2]
      unfolding simple_cg_initial.simps
      by blast
  qed
  then show ?thesis
    unfolding convergence_graph_initial_invar_def convergence_graph_lookup_invar_def
    using simple_cg_lookup_iff by blast
qed


lemma simple_cg_insert_with_conv_invar :                  
  assumes "observable M1"
  assumes "observable M2"
  shows  "convergence_graph_insert_invar M1 M2 simple_cg_lookup simple_cg_insert_with_conv"
proof -
  have "\<And> G \<gamma> \<alpha> \<beta> . \<gamma> \<in> L M1 \<Longrightarrow>
          \<gamma> \<in> L M2 \<Longrightarrow>
          (\<And>\<alpha> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup G \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)) \<Longrightarrow>
          \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup (simple_cg_insert_with_conv G \<gamma>) \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert_with_conv G \<gamma>) \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  proof 
    fix G ys \<alpha> 
    assume "ys \<in> L M1"
    and    "ys \<in> L M2"
    and  *:"(\<And>\<alpha> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> \<alpha> \<in> list.set (simple_cg_lookup G \<alpha>) \<and> (\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>))"
    and    "\<alpha> \<in> L M1" 
    and    "\<alpha> \<in> L M2"

    show "\<alpha> \<in> list.set (simple_cg_lookup (simple_cg_insert_with_conv G ys) \<alpha>)"
      using simple_cg_lookup_iff by blast
      

    have "\<And> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert_with_conv G ys) \<alpha>) \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>"
    proof -
      fix \<beta>
      assume "\<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert_with_conv G ys) \<alpha>)"
  
      define insert_for_prefix where insert_for_prefix: 
        "insert_for_prefix = (\<lambda> g i . let
                                      pref = take i ys;
                                      suff = drop i ys;
                                      pref_conv = simple_cg_lookup g pref
                                    in foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) g pref_conv)"
      define g' where g': "g' = simple_cg_insert G ys"
      define g'' where g'': "g'' = foldl insert_for_prefix g' [0..<length ys]"
  
      have "simple_cg_insert_with_conv G ys = simple_cg_closure g''"
        unfolding simple_cg_insert_with_conv.simps g'' g' insert_for_prefix Let_def by force
  
      have g'_invar: "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup g' \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
        using g' *
        using simple_cg_insert_invar \<open>ys \<in> L M1\<close> \<open>ys \<in> L M2\<close>
        unfolding convergence_graph_insert_invar_def convergence_graph_lookup_invar_def
        by blast
  
      have insert_for_prefix_invar: "\<And> i g . (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup g \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>) \<Longrightarrow> (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (insert_for_prefix g i) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
      proof -
        fix i g assume "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup g \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  
        define pref where pref: "pref = take i ys"
        define suff where suff: "suff = drop i ys"
        let ?pref_conv = "simple_cg_lookup g pref"
  
        have "insert_for_prefix g i = foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) g ?pref_conv"
          unfolding insert_for_prefix pref suff Let_def by force
  
        have "ys = pref @ suff"
          unfolding pref suff by auto
        then have "pref \<in> L M1" and "pref \<in> L M2"
          using \<open>ys \<in> L M1\<close> \<open>ys \<in> L M2\<close> language_prefix by metis+
  
        have insert_step_invar: "\<And> ys' pc G . list.set pc \<subseteq> list.set (simple_cg_lookup g pref) \<Longrightarrow> ys' \<in> list.set pc \<Longrightarrow>
                        (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>) \<Longrightarrow> 
                        (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert' G (ys'@suff)) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
        proof -
          fix ys' pc G
          assume "list.set pc \<subseteq> list.set (simple_cg_lookup g pref)" 
             and "ys' \<in> list.set pc"
             and "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
          then have "converge M1 pref ys'" and "converge M2 pref ys'"
            using \<open>\<And>\<beta> \<alpha>. \<beta> \<in> list.set (simple_cg_lookup g \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>\<close> 
            using \<open>pref \<in> L M1\<close> \<open>pref \<in> L M2\<close>
            by blast+
  
          have "(ys'@suff) \<in> L M1"
            using \<open>converge M1 pref ys'\<close>
            using \<open>ys = pref @ suff\<close> \<open>ys \<in> L M1\<close> assms(1) converge_append_language_iff by blast
          moreover have "(ys'@suff) \<in> L M2"
            using \<open>converge M2 pref ys'\<close>
            using \<open>ys = pref @ suff\<close> \<open>ys \<in> L M2\<close> assms(2) converge_append_language_iff by blast
          ultimately show "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert' G (ys'@suff)) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
            using \<open>(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)\<close>
            using simple_cg_insert'_invar[of M1 M2]
            unfolding convergence_graph_insert_invar_def convergence_graph_lookup_invar_def
            using simple_cg_lookup_iff by blast
        qed
  
        have insert_foldl_invar: "\<And> pc G . list.set pc \<subseteq> list.set (simple_cg_lookup g pref) \<Longrightarrow> 
                        (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>) \<Longrightarrow> 
                        (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) G pc) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)" 
        proof -
          fix pc G assume "list.set pc \<subseteq> list.set (simple_cg_lookup g pref)" 
                     and "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  
          then show "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) G pc) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
          proof (induction pc rule: rev_induct)
            case Nil
            then show ?case by auto
          next
            case (snoc a pc)

            have **:"(foldl (\<lambda>g' ys'. simple_cg_insert' g' (ys' @ suff)) G (pc @ [a]))
                   = simple_cg_insert' (foldl (\<lambda>g' ys'. simple_cg_insert' g' (ys' @ suff)) G pc) (a@suff)"
              unfolding foldl_append by auto
            have "list.set pc \<subseteq> list.set (simple_cg_lookup g pref)"
              using snoc.prems(4) by auto 
            then have *: "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) G pc) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
              using snoc.IH
              using snoc.prems(5) by blast  
            
            have "a \<in> list.set (pc @ [a])" by auto
            then show ?case 
              using snoc.prems(1,2,3)
              unfolding **
              using insert_step_invar[OF snoc.prems(4), of a "(foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) G pc)", OF _  *]
              by blast
          qed
        qed
        
        show "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (insert_for_prefix g i) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
          using insert_foldl_invar[of ?pref_conv g, OF _ \<open>(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup g \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)\<close>]
          unfolding \<open>insert_for_prefix g i = foldl (\<lambda> g' ys' . simple_cg_insert' g' (ys'@suff)) g ?pref_conv\<close>
          by blast
      qed
  
      have insert_for_prefix_foldl_invar: "\<And> ns . (\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (foldl insert_for_prefix g' ns) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
      proof -
        fix ns show "(\<And>\<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup (foldl insert_for_prefix g' ns) \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
        proof (induction ns rule: rev_induct)
          case Nil
          then show ?case using g'_invar by auto
        next
          case (snoc a ns)
          show ?case 
            using snoc.prems          
            using insert_for_prefix_invar [OF snoc.IH]
            by auto
        qed
      qed
  
      show \<open>converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>\<close> 
        using \<open>\<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert_with_conv G ys) \<alpha>)\<close>
        unfolding \<open>simple_cg_insert_with_conv G ys = simple_cg_closure g''\<close> g''
        using insert_for_prefix_foldl_invar[of _ "[0..<length ys]" _]
        using simple_cg_closure_invar_helper[OF assms, of "(foldl insert_for_prefix g' [0..<length ys])", OF insert_for_prefix_foldl_invar[of _ "[0..<length ys]" _]]
        using \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close> by blast
    qed
    then show "(\<forall> \<beta> . \<beta> \<in> list.set (simple_cg_lookup (simple_cg_insert_with_conv G ys) \<alpha>) \<longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
      by blast
  qed

  then show ?thesis
    unfolding convergence_graph_insert_invar_def convergence_graph_lookup_invar_def
    by blast
qed

(*
fun simple_cg_lookup_with_conv :: "('a::linorder) simple_cg \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "simple_cg_lookup_with_conv g ys = (let
      lookup_for_prefix = (\<lambda>i . let
                                  pref = take i ys;
                                  suff = drop i ys;
                                  pref_conv = (foldl (ts.union) (ts.empty ()) (filter (\<lambda>x . ts.memb pref x) g))
                                in map (\<lambda> pref' . pref'@suff) (ts.to_list pref_conv))
    in ts.to_list (ts.from_list (ys # (concat (map lookup_for_prefix [0..<Suc (length ys)])))))"
*)

lemma simple_cg_lookup_with_conv_from_lookup_invar:
  fixes G :: "('a::linorder\<times>'b::linorder) simple_cg"
  assumes "observable M1" and "observable M2"
  and "convergence_graph_lookup_invar M1 M2 simple_cg_lookup G"
shows "convergence_graph_lookup_invar M1 M2 simple_cg_lookup_with_conv G"
proof -

  have "(\<And> \<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup_with_conv G \<alpha>) \<Longrightarrow> \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> L M2 \<Longrightarrow> converge M1 \<alpha> \<beta> \<and> converge M2 \<alpha> \<beta>)"
  proof -
    fix ys \<beta> assume "\<beta> \<in> list.set (simple_cg_lookup_with_conv G ys)" and "ys \<in> L M1" and "ys \<in> L M2"

    define lookup_for_prefix where lookup_for_prefix:
      "lookup_for_prefix = (\<lambda>i . let
                                  pref = take i ys;
                                  suff = drop i ys;
                                  pref_conv = (foldl (ts.union) (ts.empty ()) (filter (\<lambda>x . ts.memb pref x) G))
                                in map (\<lambda> pref' . pref'@suff) (ts.to_list pref_conv))"


    have "\<And> ns . \<beta> \<in> list.set (ts.to_list (ts.from_list (ys # (concat (map lookup_for_prefix ns))))) \<Longrightarrow> converge M1 ys \<beta> \<and> converge M2 ys \<beta>"
    proof -
      fix ns assume "\<beta> \<in> list.set (ts.to_list (ts.from_list (ys # (concat (map lookup_for_prefix ns)))))"
      then show "converge M1 ys \<beta> \<and> converge M2 ys \<beta>"
      proof (induction ns rule: rev_induct)
        case Nil
        then have "\<beta> = ys"
          unfolding ts.correct(33)[OF ts.invar]
          unfolding ts.correct(35)
          by auto
        then show ?case 
          using \<open>ys \<in> L M1\<close> \<open>ys \<in> L M2\<close>
          by auto
      next
        case (snoc a ns)

        have "list.set (ts.to_list (ts.from_list (ys # (concat (map lookup_for_prefix (ns@[a]))))))
              = list.set (lookup_for_prefix a) \<union> list.set (ts.to_list (ts.from_list (ys # (concat (map lookup_for_prefix ns)))))"
          unfolding ts.correct(33)[OF ts.invar]
          unfolding ts.correct(35)
          by auto
        then consider "\<beta> \<in> list.set (lookup_for_prefix a)" | "\<beta> \<in> list.set (ts.to_list (ts.from_list (ys # (concat (map lookup_for_prefix ns)))))"
          using snoc.prems by auto
        then show ?case proof cases
          case 1
          define pref where pref: "pref = take a ys"
          define suff where suff: "suff = drop a ys"
          define pref_conv where pref_conv: "pref_conv = (foldl (ts.union) (ts.empty ()) (filter (\<lambda>x . ts.memb pref x) G))"
                                
          have "lookup_for_prefix a = map (\<lambda> pref' . pref'@suff) (ts.to_list pref_conv)"
            unfolding lookup_for_prefix pref suff pref_conv
            by metis
          then have *:"\<beta> \<in> list.set (map (\<lambda> pref' . pref'@suff) (ts.to_list (foldl (ts.union) (ts.empty ()) (filter (\<lambda>x . ts.memb pref x) G))))"
            using 1 unfolding pref_conv by auto
          obtain \<gamma> where "\<gamma> \<in> list.set (simple_cg_lookup G pref)"
                     and "\<beta> = \<gamma>@suff"
            using set_map_elem[OF *]
            unfolding simple_cg_lookup.simps
            unfolding ts.correct(33)[OF ts.invar]
            unfolding ts.ins_correct[OF ts.invar]
            by blast
          then have "converge M1 \<gamma> pref" and "converge M2 \<gamma> pref"
            using \<open>convergence_graph_lookup_invar M1 M2 simple_cg_lookup G\<close>
            unfolding convergence_graph_lookup_invar_def
            by (metis \<open>ys \<in> L M1\<close> \<open>ys \<in> L M2\<close> append_take_drop_id converge_sym language_prefix pref)+
          then show ?thesis
            by (metis \<open>\<And>thesis. (\<And>\<gamma>. \<lbrakk>\<gamma> \<in> list.set (simple_cg_lookup G pref); \<beta> = \<gamma> @ suff\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>ys \<in> L M1\<close> \<open>ys \<in> L M2\<close> append_take_drop_id assms(1) assms(2) assms(3) converge_append converge_append_language_iff convergence_graph_lookup_invar_def language_prefix pref suff) 
        next
          case 2
          then show ?thesis using snoc.IH by blast
        qed
      qed
    qed

    then show "converge M1 ys \<beta> \<and> converge M2 ys \<beta>"
      using \<open>\<beta> \<in> list.set (simple_cg_lookup_with_conv G ys)\<close>  
      unfolding simple_cg_lookup_with_conv.simps Let_def lookup_for_prefix sorted_list_of_set_set
      by blast 
  qed
  moreover have "\<And> \<alpha> . \<alpha> \<in> list.set (simple_cg_lookup_with_conv G \<alpha>)"
    unfolding simple_cg_lookup_with_conv.simps Let_def
    unfolding ts.correct(33)[OF ts.invar]
    unfolding ts.correct(35)
    by auto
  ultimately show ?thesis
    unfolding convergence_graph_lookup_invar_def 
    by blast
qed

lemma simple_cg_lookup_from_lookup_invar_with_conv:
  assumes "convergence_graph_lookup_invar M1 M2 simple_cg_lookup_with_conv G"
shows "convergence_graph_lookup_invar M1 M2 simple_cg_lookup G"
proof -

  have "\<And> \<alpha> \<beta>. \<beta> \<in> list.set (simple_cg_lookup G \<alpha>) \<Longrightarrow> \<beta> \<in> list.set (simple_cg_lookup_with_conv G \<alpha>)"
  proof -

    fix \<alpha> \<beta> assume "\<beta> \<in> list.set (simple_cg_lookup G \<alpha>)"

    define lookup_for_prefix where lookup_for_prefix:
      "lookup_for_prefix = (\<lambda>i . let
                                  pref = take i \<alpha>;
                                  suff = drop i \<alpha>;
                                  pref_conv = simple_cg_lookup G pref
                                in map (\<lambda> pref' . pref'@suff) pref_conv)"

    have "lookup_for_prefix (length \<alpha>) = simple_cg_lookup G \<alpha>"
      unfolding lookup_for_prefix by auto
    moreover have "list.set (lookup_for_prefix (length \<alpha>)) \<subseteq> list.set (simple_cg_lookup_with_conv G \<alpha>)"
    proof -
      have "\<And> xs . list.set (map (\<lambda>pref'. pref' @ drop (length \<alpha>) \<alpha>) (ts.to_list (ts.ins (take (length \<alpha>) \<alpha>) xs))) =
                   list.set (\<alpha> # map (\<lambda>pref'. pref' @ drop (length \<alpha>) \<alpha>)  (ts.to_list xs))"
        using ts.ins_correct(1)[OF ts.invar]
        using ts.correct(33)[OF ts.invar]
        by (simp add: \<open>\<And>s. list.set (ts.to_list s) = ts.\<alpha> s\<close> \<open>\<And>x s. ts.\<alpha> (ts.ins x s) = Set.insert x (ts.\<alpha> s)\<close>)
      then have *:"list.set (lookup_for_prefix (length \<alpha>)) = list.set
        (\<alpha> #
         concat
          (map (\<lambda>i. map (\<lambda>pref'. pref' @ drop i \<alpha>)
                     (ts.to_list (foldl ts.union (ts.empty ()) (filter (ts.memb (take i \<alpha>)) G))))
            [length \<alpha>]))"
        unfolding simple_cg_lookup_with_conv.simps  Let_def
        unfolding simple_cg_lookup.simps lookup_for_prefix Let_def  
        unfolding ts.correct(33)[OF ts.invar]
        unfolding ts.correct(35) 
        unfolding list.map concat.simps
        by simp
      
      show ?thesis
        unfolding *
        unfolding simple_cg_lookup_with_conv.simps Let_def
        unfolding ts.correct(33)[OF ts.invar]
        unfolding ts.correct(35)  
        by auto
    qed
    ultimately show "\<beta> \<in> list.set (simple_cg_lookup_with_conv G \<alpha>)"
      using \<open>\<beta> \<in> list.set (simple_cg_lookup G \<alpha>)\<close>
      by (metis subsetD)
  qed

  then show ?thesis
    using assms
    unfolding convergence_graph_lookup_invar_def
    using simple_cg_lookup_iff by blast    
qed


lemma simple_cg_lookup_invar_with_conv_eq :
  assumes "observable M1" and "observable M2" 
  shows "convergence_graph_lookup_invar M1 M2 simple_cg_lookup_with_conv G = convergence_graph_lookup_invar M1 M2 simple_cg_lookup G"
  using simple_cg_lookup_with_conv_from_lookup_invar[OF assms] simple_cg_lookup_from_lookup_invar_with_conv[of M1 M2]
  by blast


lemma simple_cg_insert_invar_with_conv :    
  assumes "observable M1" and "observable M2"
shows "convergence_graph_insert_invar M1 M2 simple_cg_lookup_with_conv simple_cg_insert"
  using simple_cg_insert_invar[of M1 M2] 
  unfolding convergence_graph_insert_invar_def 
  unfolding simple_cg_lookup_invar_with_conv_eq[OF assms]
  .

lemma simple_cg_merge_invar_with_conv :
  assumes "observable M1" and "observable M2"
shows "convergence_graph_merge_invar M1 M2 simple_cg_lookup_with_conv simple_cg_merge"
  using simple_cg_merge_invar[OF assms] 
  unfolding convergence_graph_merge_invar_def 
  unfolding simple_cg_lookup_invar_with_conv_eq[OF assms]
  .

lemma simple_cg_initial_invar_with_conv :
  assumes "observable M1" and "observable M2"
  shows "convergence_graph_initial_invar M1 M2 simple_cg_lookup_with_conv simple_cg_initial"
  using simple_cg_initial_invar[OF assms(1), of M2] 
  unfolding convergence_graph_initial_invar_def 
  unfolding simple_cg_lookup_invar_with_conv_eq[OF assms]
  .


end