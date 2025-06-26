section \<open>Bisping's Updates\<close>

theory Update
  imports Energy_Order 
begin

text \<open>
In this theory we define a superset of Bisping's updates and their application. Further, we introduce Bisping's ``inversion''
of updates and relate the two.
\<close>

subsection \<open>Bisping's Updates\<close>

text \<open>
Bisping allows three ways of updating a component of an energy: \<open>zero\<close> does not change the respective entry, 
\<open>minus_one\<close> subtracts one and \<open>min_set\<close> $A$ for some set $A$ replaces the entry by the 
minimum of entries whose index is contained in $A$. We further add \<open>plus_one\<close> to add one and omit the assumption that the a minimum has to consider the component it replaces.
Updates are vectors where each entry contains the information, how the update changes the respective 
component of energies. We now introduce a datatype such that updates can be represented as lists of \<open>update_component\<close>s.
\<close>

datatype update_component = zero | minus_one | min_set "nat set" | plus_one
type_synonym update = "update_component list" 

abbreviation "valid_update u \<equiv> (\<forall>i D. u ! i = min_set D 
                                    \<longrightarrow> D \<noteq> {} \<and> D \<subseteq> {x. x < length u})"

text \<open>Now the application of updates \<open>apply_update\<close> will be defined.\<close>

fun apply_component::"nat \<Rightarrow> update_component \<Rightarrow> energy \<Rightarrow> enat option" where
  "apply_component i zero e = Some (e ! i)" |
  "apply_component i minus_one e = (if ((e ! i) > 0) then Some ((e ! i) - 1) 
                                    else None)" |
  "apply_component i (min_set A) e = Some (min_list (nths e A))"|
  "apply_component i plus_one e = Some ((e ! i)+1)" 

fun apply_update:: "update \<Rightarrow> energy \<Rightarrow> energy option"  where 
  "apply_update u e = (if (length u = length e) 
          then (those (map (\<lambda>i. apply_component i (u ! i) e) [0..<length e])) 
          else  None)"

abbreviation "upd u e \<equiv> the (apply_update u e)"

text \<open>We now observe some properties of updates and their application. 
In particular, the application of an update preserves the dimension and the domain of an update is upward closed.
\<close>

lemma len_appl: 
  assumes "apply_update u e \<noteq> None"
  shows "length (upd u e) = length e"
proof -  
  from assms have "apply_update u e = those (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e])" by auto
  thus ?thesis using assms len_those
    using length_map length_upt by force 
qed

lemma apply_to_comp_n:
  assumes "apply_update u e \<noteq> None" and "i < length e"
  shows  "(upd u e) ! i = the (apply_component i (u ! i) e)" 
proof- 
  have "(the (apply_update u e)) ! i =(the (those (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e])))!i" using apply_update.simps
    using assms by auto 
  also have "... = the ((map (\<lambda>n. apply_component n (u ! n) e) [0..<length e])! i)" using the_those_n
    by (metis (no_types, lifting) apply_update.simps assms(1) assms(2) calculation length_map map_nth)
  also have "... = the ( apply_component i (u ! i) e)" using nth_map
    by (simp add: assms(2) calculation linordered_semidom_class.add_diff_inverse not_less_zero nth_map_upt)
  finally show ?thesis.
qed

lemma upd_domain_upward_closed:
  assumes "apply_update u e \<noteq> None" and "e e\<le> e'" 
  shows "apply_update u e' \<noteq> None"
proof
  assume "apply_update u e' = None"
  from assms have "length u = length e'" unfolding apply_update.simps energy_leq_def by metis 
  hence A: "apply_update u e' = those (map (\<lambda>n. apply_component n (u ! n) e') [0..<length e'])" using apply_update.simps by simp
  hence "those (map (\<lambda>n. apply_component n (u ! n) e') [0..<length e']) = None" using \<open>apply_update u e' = None\<close> by simp
  hence "\<not> (\<forall>n < length e'. (\<lambda>n. apply_component n (u ! n) e') ([0..<length e'] ! n) \<noteq> None)" using those_map_not_None
    by (metis (no_types, lifting) length_map map_nth)
  hence "\<exists>n< length e'. (\<lambda>n. apply_component n (u ! n) e') ([0..<length e'] ! n) = None" by auto
  from this obtain n where "n< length e'" and "(\<lambda>n. apply_component n (u ! n) e') ([0..<length e'] ! n) = None" by auto
  hence "apply_component n (u ! n) e' = None" by simp
  hence "u ! n = minus_one" using apply_component.elims by blast
  hence  " e' ! n = 0" using \<open>apply_component n (u ! n) e' = None\<close> apply_component.elims
    by fastforce
  hence "e ! n = 0" using assms(2) energy_leq_def \<open>n < length e'\<close> by auto 
  hence "(\<lambda>n. apply_component n (u ! n) e) ([0..<length e] ! n) = None" using \<open>u ! n = minus_one\<close> apply_component.simps(2)
    using \<open>n < length e'\<close> assms(2) energy_leq_def by auto
  hence "those (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e]) = None" using those.simps option.map_sel  \<open>n < length e'\<close>
    by (smt (verit, ccfv_SIG) \<open>length u = length e'\<close> apply_update.simps assms(1) length_map map_nth nth_map those_all_Some)
  hence "apply_update u e = None" by simp 
  thus "False" using assms(1) by simp
qed

text \<open>Now we show that all valid updates are  monotonic. The proof follows directly 
from the definition of \<open>apply_update\<close> and \<open>valid_update\<close>.\<close> 

lemma updates_monotonic:
  assumes "apply_update u e \<noteq> None" and "e e\<le> e'" and "valid_update u"
  shows "(upd u e) e\<le> (upd u e')" 
  unfolding energy_leq_def proof
  have "apply_update u e' \<noteq> None" using assms upd_domain_upward_closed by auto
  thus "length (the (apply_update u e)) = length (the (apply_update u e'))" using assms len_appl
    by (metis energy_leq_def)
  show "\<forall>n<length (the (apply_update u e)). the (apply_update u e) ! n \<le> the (apply_update u e') ! n " 
  proof 
    fix n 
    show "n < length (the (apply_update u e)) \<longrightarrow> the (apply_update u e) ! n \<le> the (apply_update u e') ! n"
    proof 
      assume "n < length (the (apply_update u e))"
      hence "n < length e" using len_appl assms(1)
        by simp
      hence " e ! n \<le> e' !n " using assms energy_leq_def
        by simp
      consider (zero) "(u ! n) = zero" | (minus_one) "(u ! n) = minus_one" | (min_set) "(\<exists>A. (u ! n) = min_set A)" | (plus_one) "(u ! n) = plus_one"
        using update_component.exhaust by auto 
      thus "the (apply_update u e) ! n \<le> the (apply_update u e') ! n" 
      proof (cases)
        case zero
        then show ?thesis using apply_update.simps apply_component.simps assms \<open>e ! n \<le> e' !n\<close> \<open>apply_update u e' \<noteq> None\<close>
          by (metis \<open>n < length (the (apply_update u e))\<close> apply_to_comp_n len_appl option.sel)
      next
        case minus_one
        hence "the (apply_update u e) ! n = the (apply_component n (u ! n) e)" using apply_to_comp_n assms(1)
          by (simp add: \<open>n < length e\<close>)

        from assms(1) have A: "(map (\<lambda>n. apply_component n (u ! n) e) [0..<length e]) ! n \<noteq> None" using  \<open>n < length e\<close> those_all_Some apply_update.simps
          by (metis (no_types, lifting) length_map map_nth) 
        hence "(apply_component n (u ! n) e) = (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e]) ! n " using \<open>n < length e\<close>
          by simp
        hence "(apply_component n (u ! n) e) \<noteq> None" using A by simp
        hence "e ! n >0 " using minus_one apply_component.elims by auto 
        hence  "(e ! n) -1 \<le> (e' ! n) -1" using \<open>e ! n \<le> e' ! n\<close> by (metis eSuc_minus_1 iadd_Suc ileI1 le_iff_add)

        from \<open>e ! n >0\<close> have "e' ! n > 0" using assms(2) energy_leq_def
          using \<open>e ! n \<le> e' ! n\<close> by auto 
        have A: "the (apply_update u e') ! n = the (apply_component n (u ! n) e')" using apply_to_comp_n \<open>apply_update u e' \<noteq> None\<close>
          using \<open>n < length e\<close> assms(2) energy_leq_def by auto 
        have "the (apply_component n (u ! n) e' )= (e' ! n) -1" using minus_one \<open>e' ! n >0\<close>
          by simp
        hence "the (apply_update u e') ! n  = (e' ! n) -1" using A by simp
        then show ?thesis using \<open>(e ! n) -1 \<le> (e' ! n) -1\<close>
          using \<open>0 < e ! n\<close> \<open>the (apply_update u e) ! n = the (apply_component n (u ! n) e)\<close> minus_one by auto
      next
        case min_set
        from this obtain A where "u ! n = min_set A" by auto
        hence " A \<subseteq> {x. x < length e}" using assms(3)  by (metis apply_update.elims assms(1))
        hence "\<forall>a \<in> A. e!a \<le> e'!a" using assms(2) energy_leq_def
          by blast
        have "\<forall>a\<in> A. (Min (set (nths e A))) \<le> e! a" proof
          fix a
          assume "a \<in> A"
          hence "e!a \<in> set (nths e A)" using set_nths nths_def
            using \<open>A \<subseteq> {x. x < length e}\<close> in_mono by fastforce
          thus "Min (set (nths e A)) \<le> e ! a " using Min_le by simp
        qed
        hence "\<forall>a\<in> A. (Min (set (nths e A))) \<le> e'! a" using \<open>\<forall>a \<in> A. e!a \<le> e'!a\<close>
          using dual_order.trans by blast 
        hence "\<forall>x \<in> (set (nths e' A)). (Min (set (nths e A))) \<le> x" using set_nths
          by (smt (verit) mem_Collect_eq)        

        from assms(2) have "A\<noteq>{}"
          using \<open>u ! n = min_set A\<close> assms(3) by auto 
        have "A \<subseteq> {x. x < length e'}" using \<open>A \<subseteq> {x. x < length e}\<close> assms
          using energy_leq_def by auto 
        hence "set (nths e' A) \<noteq> {}" using \<open>A \<noteq>{}\<close> set_nths
          by (smt (verit, best) Collect_empty_eq Collect_mem_eq Collect_mono_iff) 
        hence "(nths e' A) \<noteq> []" by simp
        from \<open>A\<noteq>{}\<close> have "set (nths e A) \<noteq> {}" using set_nths \<open>A \<subseteq> {x. x < length e}\<close> Collect_empty_eq \<open>n < length e\<close> \<open>u ! n = min_set A\<close>
          by (smt (verit, best) \<open>set (nths e' A) \<noteq> {}\<close> assms(2) energy_leq_def)
        hence "(nths e A) \<noteq> []" by simp
        hence "(min_list (nths e A)) = Min (set (nths e A))" using min_list_Min by auto
        also have "... \<le> Min (set (nths e' A))"        
          using \<open>\<forall>x \<in> (set (nths e' A)). (Min (set (nths e A))) \<le> x\<close>
          by (simp add: \<open>nths e' A \<noteq> []\<close>) 
        finally have "(min_list (nths e A)) \<le> min_list (nths e' A)" using min_list_Min \<open>(nths e' A) \<noteq> []\<close> by metis
        then show ?thesis using apply_to_comp_n assms(1) \<open>apply_update u e' \<noteq> None\<close> apply_component.simps(3) \<open>u ! n = min_set A\<close>
          by (metis \<open>length (the (apply_update u e)) = length (the (apply_update u e'))\<close> \<open>n < length e\<close> len_appl option.sel)
      next
        case plus_one 
        have "upd u e ! n = the (apply_component n (u ! n) e)" using apply_to_comp_n \<open>n < length e\<close> assms(1) by auto 
        also have "... =  (e!n) +1" using apply_component.elims plus_one
          by simp
        also have "... \<le> (e'!n) +1" 
          using \<open>e ! n \<le> e' ! n\<close> by auto 
        also have "... = upd u e' ! n" using  apply_to_comp_n \<open>n < length e\<close> assms apply_component.elims plus_one
          by (metis \<open>apply_update u e' \<noteq> None\<close> apply_component.simps(4) energy_leq_def option.sel)
        finally show ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>Bisping's Inversion\<close>

text\<open>The ``inverse'' of an update $u$ is a function mapping energies $e$ to $\min \lbrace e' \ | \ e \leq u(e') \rbrace$ 
w.r.t\ the component-wise order.
We start by giving a calculation and later show that we indeed calculate such minima.  
For an energy $e = (e_0, ..., e_{n-1})$ we calculate this component-wise such that the $i$-th 
component is the maximum of $e_i$ (plus or minus one if applicable) 
and each entry $e_j$ where $i \in u_j \subseteq \lbrace 0, ..., n-1 \rbrace $.
Note that this generalises the inversion proposed by Bisping~\cite{bens-algo}.
\<close>

fun apply_inv_component::"nat \<Rightarrow> update \<Rightarrow> energy \<Rightarrow> enat" where
  "apply_inv_component i u e = Max (set (map (\<lambda>(j,up). 
          (case up of zero \<Rightarrow> (if i=j then (e ! i) else 0) | 
                minus_one \<Rightarrow> (if i=j then (e ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e ! j) else 0) | 
                plus_one \<Rightarrow> (if i=j then (e ! i)-1 else 0))) 
          (List.enumerate 0 u)))" 

fun apply_inv_update:: "update \<Rightarrow> energy \<Rightarrow> energy option" where 
  "apply_inv_update u e = (if (length u = length e) 
                    then Some (map (\<lambda>i. apply_inv_component i u e) [0..<length e])
                    else None)" 

abbreviation "inv_upd u e \<equiv> the (apply_inv_update u e)"

text \<open>We now observe the following properties, if an update $u$ and an energy $e$ have the same dimension:
\begin{itemize}
  \item \<open>apply_inv_update\<close> preserves dimension.
  \item The domain of \<open>apply_inv_update u\<close> is $\lbrace \<open>e\<close> \ | \ |\<open>e\<close>| = |\<open>u\<close>| \rbrace$.
  \item \<open>apply_inv_update u e\<close>  is in the domain of the update \<open>u\<close>.
\end{itemize}
The first two proofs follow directly from the definition of \<open>apply_inv_update\<close>, while the proof
of \<open>inv_not_none_then\<close> is done by a case analysis of the possible \<open>update_component\<close>s. \<close>

lemma len_inv_appl: 
  assumes "length u = length e"
  shows "length (inv_upd u e) = length e"
  using assms apply_inv_update.simps length_map option.sel by auto

lemma inv_not_none: 
  assumes "length u = length e"
  shows "apply_inv_update u e \<noteq> None" 
  using assms apply_inv_update.simps by simp  

lemma inv_not_none_then:
  assumes "apply_inv_update u e \<noteq> None"
  shows "(apply_update u (inv_upd u e)) \<noteq> None"
proof - 
  have len: "length u = length (the (apply_inv_update u e))" using assms apply_inv_update.simps len_those
    by auto 
  have "\<forall>n<length u. (apply_component n (u ! n) (the (apply_inv_update u e)))\<noteq>None" 
  proof
    fix n
    show "n < length u \<longrightarrow> apply_component n (u ! n) (the (apply_inv_update u e)) \<noteq> None " 
    proof 
      assume "n<length u"
      consider (zero) "(u ! n) = zero" | (minus_one) "(u ! n) = minus_one" | (min_set) "(\<exists>A. (u ! n) = min_set A)" | (plus_one) "(u ! n) = plus_one"
        using update_component.exhaust by auto 
      then show "apply_component n (u ! n) (the (apply_inv_update u e)) \<noteq> None" 
      proof(cases)
        case zero
        then show ?thesis by simp 
      next
        case minus_one
        have nth: "(the (apply_inv_update u e)) ! n = apply_inv_component n u e" using apply_inv_update.simps
          by (metis \<open>n < length u\<close> add_0 assms diff_add_inverse nth_map_upt option.sel)

        have n_minus_one: "List.enumerate 0 u ! n = (n,minus_one) " using minus_one
          by (simp add: \<open>n < length u\<close> nth_enumerate_eq) 
        have "(\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)))(n,minus_one) = (e ! n) +1"
          by simp
        hence "(e ! n) +1 \<in> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0) |
                plus_one \<Rightarrow>(if n=m then (nth e n)-1 else 0)))(List.enumerate 0 u))" using n_minus_one
          by (metis (no_types, lifting) \<open>n < length u\<close> case_prod_conv length_enumerate length_map nth_map nth_mem update_component.simps(15))
        hence "(nth e n)+1 \<le> apply_inv_component n u e" using minus_one nth apply_inv_component.simps Max_ge
          by simp
        hence "(nth (the (apply_inv_update u e)) n >0)" using nth by fastforce
        then show ?thesis by (simp add: minus_one) 
      next
        case min_set
        then show ?thesis by auto 
      next 
        case plus_one
        then show ?thesis by simp
      qed
    qed
  qed
  hence "\<forall>n<length (the (apply_inv_update u e)). apply_component n (u ! n) (the (apply_inv_update u e)) \<noteq> None" 
    using len by presburger 
  hence "those (map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))]) \<noteq> None" 
    using those_map_not_None
    by (smt (verit) add_less_cancel_left gen_length_def length_code length_map map_nth nth_upt) 
  thus ?thesis using apply_update.simps len by presburger
qed

text \<open>Now we show that \<open>apply_inv_update u\<close> is monotonic for all updates \<open>u\<close>. The proof follows directly 
from the definition of \<open>apply_inv_update\<close> and a case analysis of the possible update components.\<close>

lemma inverse_monotonic:
  assumes "e e\<le> e'" and "length u = length e'"
  shows "(inv_upd u e) e\<le> (inv_upd u e')"
  unfolding energy_leq_def proof
  show "length (the (apply_inv_update u e)) = length (the (apply_inv_update u e'))" using assms len_inv_appl energy_leq_def
    by simp 
  show "\<forall>i<length (the (apply_inv_update u e)). the (apply_inv_update u e) ! i \<le> the (apply_inv_update u e') ! i " 
  proof
    fix i
    show "i < length (the (apply_inv_update u e)) \<longrightarrow> the (apply_inv_update u e) ! i \<le> the (apply_inv_update u e') ! i "
    proof 
      assume "i < length (the (apply_inv_update u e))"
      have "the (apply_inv_update u e) ! i = (map (\<lambda>i. apply_inv_component i u e) [0..<length e]) ! i" 
        using apply_inv_update.simps assms
        using energy_leq_def by auto
      also have "... =  (\<lambda>i. apply_inv_component i u e) ([0..<length e] ! i)" using nth_map
        by (metis (full_types) \<open>i < length (the (apply_inv_update u e))\<close> add_less_mono assms(1) assms(2) energy_leq_def diff_add_inverse gen_length_def len_inv_appl length_code less_add_same_cancel2 not_less_less_Suc_eq nth_map_upt nth_upt plus_1_eq_Suc)
      also have "... = apply_inv_component i u e"
        using \<open>i < length (the (apply_inv_update u e))\<close> assms(1) assms(2) energy_leq_def by auto 
      finally have E: "the (apply_inv_update u e) ! i =
                Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if i=m then (nth e i) else 0)  | 
                minus_one \<Rightarrow> (if i=m then (e ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e ! m) else 0) |
                plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps
        by presburger 


      have "the (apply_inv_update u e') ! i = (map (\<lambda>i. apply_inv_component i u e') [0..<length e']) ! i" 
        using apply_inv_update.simps assms
        using energy_leq_def by auto
      also have "... =  (\<lambda>i. apply_inv_component i u e') ([0..<length e'] ! i)" using nth_map
        by (metis (full_types) \<open>i < length (the (apply_inv_update u e))\<close> add_less_mono assms(1) assms(2) energy_leq_def diff_add_inverse gen_length_def len_inv_appl length_code less_add_same_cancel2 not_less_less_Suc_eq nth_map_upt nth_upt plus_1_eq_Suc)
      also have "... = apply_inv_component i u e'"
        using \<open>i < length (the (apply_inv_update u e))\<close> assms(1) assms(2) energy_leq_def by auto 
      finally have E': "the (apply_inv_update u e') ! i =
                Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow>(if i=m then (nth e' i) else 0) | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0) |
                plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps
        by presburger 

      have fin': "finite (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if i=m then (nth e' i) else 0) | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0) |
                plus_one \<Rightarrow>(if i=m then (nth e' i)-1 else 0))) (List.enumerate 0 u)))" by simp
      have fin: "finite (set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if i=m then (nth e i) else 0) | minus_one \<Rightarrow> if i = m then e ! i + 1 else 0
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0 |
                            plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0)) 
                   (List.enumerate 0 u)))" by simp

      have "\<And>x. x \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if i=m then (nth e i) else 0) | 
                minus_one \<Rightarrow> (if i=m then (e ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e ! m) else 0) |
                plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0))) (List.enumerate 0 u))) \<Longrightarrow> (\<exists>y. x\<le> y \<and> y\<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if i=m then (nth e' i) else 0) | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0)|
                plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))) (List.enumerate 0 u))))"
      proof-
        fix x
        assume "x \<in> set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if i=m then (nth e i) else 0) | minus_one \<Rightarrow> if i = m then e ! i + 1 else 0
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0 |
                plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0))
                   (List.enumerate 0 u))" 
        hence "\<exists>j < length u. x = (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if i=m then (nth e i) else 0) | minus_one \<Rightarrow> if i = m then e ! i + 1 else 0
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0 |
                plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0))
                   (List.enumerate 0 u)) ! j" using in_set_conv_nth
          by (metis (no_types, lifting) length_enumerate length_map)
        from this obtain j where "j < length u" and X: "x = (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if i=m then (nth e i) else 0)| minus_one \<Rightarrow> if i = m then e ! i + 1 else 0
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0 |
                plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0))
                   (List.enumerate 0 u)) ! j" by auto
        hence "(List.enumerate 0 u) ! j = (j, (u !j))"
          by (simp add: nth_enumerate_eq) 
        hence X: "x=(case (u !j) of zero \<Rightarrow> (if i=j then (nth e i) else 0) | minus_one \<Rightarrow> if i = j then e ! i + 1 else 0
                          | min_set A \<Rightarrow> if i \<in> A then e ! j else 0 |
                plus_one \<Rightarrow> (if i=j then (nth e i)-1 else 0))" using X
          by (simp add: \<open>j < length u\<close>) 

        consider (zero) "(u !j) = zero" | (minus_one) "(u !j) = minus_one" | (min_set) "\<exists> A. (u !j) = min_set A" | (plus_one) "(u!j) = plus_one"
          by (meson update_component.exhaust)

        thus "(\<exists>y. x\<le> y \<and> y\<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if i=m then (nth e' i) else 0) | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0) |
                plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))) (List.enumerate 0 u))))" 
        proof(cases)
          case zero
          hence "x= (if i=j then (nth e i) else 0)" using X by simp
          also have "... \<le> (if i=j then (nth e' i) else 0)" using assms
            using \<open>i < length (the (apply_inv_update u e))\<close> energy_leq_def
            by force
          also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 |
                plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))(j, (u ! j))"
            by (simp add: zero)
          finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0|
                            plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))
                     (List.enumerate 0 u))!j"
            by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
          then show ?thesis
            using \<open>j < length u\<close> by auto 
        next
          case minus_one
          hence X: "x = (if i=j then (e ! i)+1 else 0)" using X by simp
          then show ?thesis proof(cases "i=j")
            case True
            hence "x = (e ! i) +1" using X by simp
            also have "...\<le> (e' ! i) +1" using assms
              using True \<open>j < length u\<close> energy_leq_def by auto
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 |
                plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))(j, (u ! j))"
            by (simp add: minus_one True)
             finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow>(if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0|
                plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))
                     (List.enumerate 0 u))!j"
            by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
          then show ?thesis
            using \<open>j < length u\<close> by auto
          next
            case False
            hence "x = 0 " using X by simp
            also have "...\<le> 0"
              by simp
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 |
                plus_one \<Rightarrow>(if i=m then (nth e' i)-1 else 0))(j, (u ! j))"
            by (simp add: minus_one False)
             finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))
                     (List.enumerate 0 u))!j"
            by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
          then show ?thesis
            using \<open>j < length u\<close> by auto
          qed
        next
          case min_set
          from this obtain A where A: "u ! j = min_set A " by auto
          hence X: "x = (if i \<in> A then e ! j else 0)" using X by auto
          then show ?thesis proof(cases "i \<in> A")
            case True
            hence "x=e ! j" using X by simp
            also have "...\<le> e'!j" using assms
              using \<open>j < length u\<close> energy_leq_def by auto
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow>(if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))(j, (u ! j))"
              by (simp add: A True)
            finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))
                     (List.enumerate 0 u))!j"
              by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
            then show ?thesis
              using \<open>j < length u\<close> by auto
          next
            case False
            hence "x=0" using X by simp
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))(j, (u ! j))"
              by (simp add: A False)
            finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))
                     (List.enumerate 0 u))!j"
              by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
            then show ?thesis
              using \<open>j < length u\<close> by auto
          qed
        next 
          case plus_one
          then show ?thesis proof(cases "i=j")
            case True
            hence "x=e!i -1" using X plus_one by simp
            have "x \<le> e' ! i -1"
            proof(cases "e!i =0")
              case True
              then show ?thesis
                by (simp add: \<open>x = e ! i - 1\<close>)
            next
              case False
              then show ?thesis
              proof(cases "e!i = \<infinity>")
                case True
                then show ?thesis using assms
                  using \<open>i < length (inv_upd u e)\<close> energy_leq_def by fastforce
              next
                case False
                from this obtain b where "e!i = enat (Suc b)" using \<open> e ! i \<noteq> 0\<close>
                  by (metis list_decode.cases not_enat_eq zero_enat_def)
                then show ?thesis 
                proof(cases "e'!i = \<infinity>")
                  case True
                  then show ?thesis
                    by simp
                next
                  case False
                  from this obtain c where "e'!i = enat (Suc c)" using  \<open>e!i = enat (Suc b)\<close> assms
                    by (metis (no_types, lifting) Nat.lessE Suc_ile_eq \<open>i < length (inv_upd u e)\<close> enat.exhaust enat_ord_simps(2) energy_leq_def len_inv_appl) 
                  hence "b \<le> c" using assms
                    using \<open>e ! i = enat (Suc b)\<close> \<open>i < length (inv_upd u e)\<close> energy_leq_def by auto 
                  then show ?thesis using  \<open>e!i = enat (Suc b)\<close>  \<open>e'!i = enat (Suc c)\<close>
                    by (simp add: \<open>x = e ! i - 1\<close> one_enat_def)
                qed
              qed
            qed
            show ?thesis
              using plus_one True \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close> \<open>x \<le> e' ! i - 1\<close>
              by (smt (verit, best) nth_map case_prod_conv length_enumerate length_map nth_mem update_component.simps(17))
          next
            case False
            hence "x = 0" using X
              using plus_one by auto
            also have "...\<le> 0" by simp
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow>(if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 |
                plus_one \<Rightarrow>(if i=m then (nth e' i)-1 else 0))(j, (u ! j))"
              by (simp add: plus_one False)
            finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> (if i=m then (nth e' i) else 0) | minus_one \<Rightarrow> if i = m then e' ! i + 1 else 0
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))
                     (List.enumerate 0 u))!j"
              by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
            then show ?thesis
              using \<open>j < length u\<close> by auto
          qed
        qed
      qed

      hence "\<forall>x\<in> (set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if i=m then (nth e i) else 0) | minus_one \<Rightarrow> if i = m then e ! i + 1 else 0
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0))
                   (List.enumerate 0 u))). 
            x\<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if i=m then (nth e' i) else 0) | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0) | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))) (List.enumerate 0 u)))"
        using fin'
        by (meson Max.coboundedI dual_order.trans) 
      hence "Max (set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if i=m then (nth e i) else 0) | minus_one \<Rightarrow> if i = m then e ! i + 1 else 0
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0 | plus_one \<Rightarrow> (if i=m then (nth e i)-1 else 0))
                   (List.enumerate 0 u)))
            \<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if i=m then (nth e' i) else 0) | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else 0) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0) | plus_one \<Rightarrow> (if i=m then (nth e' i)-1 else 0))) (List.enumerate 0 u)))"
        using fin assms Max_less_iff
        by (metis (no_types, lifting) Max_in \<open>i < length (the (apply_inv_update u e))\<close> \<open>length (the (apply_inv_update u e)) = length (the (apply_inv_update u e'))\<close> ex_in_conv len_inv_appl length_enumerate length_map nth_mem)

      thus "the (apply_inv_update u e) ! i \<le> the (apply_inv_update u e') ! i " using E E'
        by presburger 
    qed
  qed
qed

subsection \<open>Relating Updates and ``Inverse'' Updates\<close>

text \<open>
Since the minimum is not an injective function, for many updates there does not exist an inverse. The 
following $2$-dimensional examples show, that the function \<open>apply_inv_update\<close> does not map an update to its inverse.
\<close>

lemma not_right_inverse_example:
  shows "apply_update [minus_one, (min_set {0,1})] [1,2] = Some [0,1]"
        "apply_inv_update [minus_one, (min_set {0,1})] [0,1] = Some [1,1]"  
  by (auto simp add: nths_def)

lemma not_right_inverse:
  shows "\<exists>u. \<exists>e. apply_inv_update u (upd u e) \<noteq> Some e" 
  using not_right_inverse_example by force

lemma not_left_inverse_example:
  shows "apply_inv_update [zero, (min_set {0,1})] [0,1] = Some [1,1]"  
        "apply_update [zero, (min_set {0,1})] [1,1] = Some [1,1]"
  by (auto simp add: nths_def)

lemma not_left_inverse: 
  shows "\<exists>u. \<exists>e. apply_update u (inv_upd u e) \<noteq> Some e" 
  by (metis option.sel apply_update.simps length_0_conv not_Cons_self2 option.distinct(1))

text \<open>
We now show that the given calculation \<open>apply_inv_update\<close> indeed calculates $e \mapsto  \min \lbrace e' \ | \ e \leq u(e') \rbrace$
for all valid updates $u$.
For this we first name this set \<open>possible_inv u e\<close>. Then we show that \<open>inv_upd u e\<close> is an element 
of that set before showing that it is minimal. 
Considering one component at a time, the proofs follow by a case analysis of the possible 
update components from the definition of \<open>apply_inv_update\<close>
\<close>

abbreviation "possible_inv u e \<equiv> {e'. apply_update u e' \<noteq> None 
                                        \<and> (e e\<le> (upd u e'))}"

lemma leq_up_inv:
  assumes "length u = length e" and "valid_update u"
  shows "e e\<le> (upd u (inv_upd u e))"
  unfolding energy_leq_def proof
  from assms have notNone: "apply_update u (the (apply_inv_update u e)) \<noteq> None" using inv_not_none_then inv_not_none by blast
  thus len1: "length e = length (the (apply_update u (the (apply_inv_update u e))))" using assms len_appl len_inv_appl
    by presburger

  show "\<forall>n<length e. e ! n \<le> the (apply_update u (the (apply_inv_update u e))) ! n " 
  proof
    fix n 
    show "n < length e \<longrightarrow> e ! n \<le> the (apply_update u (the (apply_inv_update u e))) ! n " 
    proof
      assume "n < length e"

      have notNone_n: "(map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))]) ! n \<noteq> None" using notNone apply_update.simps
        by (smt (verit) \<open>n < length e\<close> assms(1) length_map map_nth nth_map option.distinct(1) those_all_Some)

      have "the (apply_update u (the (apply_inv_update u e))) ! n = the (those (map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))])) ! n" 
        using apply_update.simps assms(1) len1 notNone by presburger 
      also have " ... = the ((map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))]) ! n)" using the_those_n notNone
        by (smt (verit) \<open>n < length e\<close> apply_update.elims calculation assms(1) length_map map_nth nth_map) 
      also have "... = the ((\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) ([0..<length (the (apply_inv_update u e))] ! n))" using nth_map
        using \<open>n < length e\<close> assms len_inv_appl minus_nat.diff_0 nth_upt by auto
      also have " ... = the (apply_component n (u ! n) (the (apply_inv_update u e)))" using \<open>n < length e\<close> assms len_inv_appl
        by (simp add: plus_nat.add_0) 
      finally have unfolded_apply_update: "the (apply_update u (the (apply_inv_update u e))) ! n = the (apply_component n (u ! n) (the (apply_inv_update u e)))" .

      have "(the (apply_inv_update u e)) ! n = (the (Some (map (\<lambda>n. apply_inv_component n u e) [0..<length e])))!n " using apply_inv_update.simps assms(1) by auto
      also have "... = (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) ! n" by auto
      also have "... =  apply_inv_component n u e" using nth_map map_nth
        by (smt (verit) Suc_diff_Suc \<open>n < length e\<close> add_diff_inverse_nat diff_add_0 length_map less_diff_conv less_one nat_1 nat_one_as_int nth_upt plus_1_eq_Suc) 
      finally have unfolded_apply_inv: "(the (apply_inv_update u e)) ! n = apply_inv_component n u e". 

      consider (zero) "u ! n = zero" |(minus_one) "u ! n = minus_one" |(min_set) "\<exists>A. min_set A = u ! n" | (plus_one) "u!n = plus_one"
        by (metis update_component.exhaust) 
      thus "e ! n \<le> the (apply_update u (the (apply_inv_update u e))) ! n" 
      proof (cases)
        case zero
        hence "(List.enumerate 0 u) ! n = (n, zero)"
          by (simp add: \<open>n < length e\<close> assms(1) nth_enumerate_eq) 
        hence nth_in_set: "e ! n \<in> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u))" using nth_map
          by (smt (verit) \<open>n < length e\<close> assms(1) length_enumerate length_map nth_mem old.prod.case update_component.simps(14))

        from zero have "the (apply_update u (the (apply_inv_update u e))) ! n = the (apply_component n zero (the (apply_inv_update u e)))" using unfolded_apply_update by auto
        also have "... = ((the (apply_inv_update u e)) ! n)" using apply_component.simps(1) by simp
        also have "... = apply_inv_component n u e" using unfolded_apply_inv by auto
        also have "... =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps by auto
        also have "... \<ge> e ! n " using nth_in_set by simp
        finally show ?thesis .
      next
        case minus_one

        hence A: "(\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (n,(u!n)) = (e!n) +1"
          by simp 
        have "(List.enumerate 0 u)!n = (n,(u!n))"
          using \<open>n < length e\<close> assms(1) nth_enumerate_eq
          by (metis add_0)
        hence "(e!n) +1 \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))" using A nth_map
          by (metis (no_types, lifting) \<open>n < length e\<close> assms(1) length_enumerate length_map nth_mem) 
        hence leq: "(e!n) +1 \<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow>(if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))" using Max_ge by simp

        have notNone_comp: "apply_component n minus_one (the (apply_inv_update u e)) \<noteq> None" using notNone
          by (smt (z3) \<open>n < length e\<close> add_0 len1 len_appl length_map length_upt map_nth minus_one notNone_n nth_map_upt)

        from minus_one have "the (apply_update u (the (apply_inv_update u e))) ! n = the (apply_component n minus_one (the (apply_inv_update u e)))" using unfolded_apply_update by auto
        also have "... = ((the (apply_inv_update u e)) ! n) -1" using apply_component.simps(2) notNone_comp
          using calculation option.sel by auto 
        also have "... = apply_inv_component n u e -1" using unfolded_apply_inv by auto
        also have "... =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u))) -1" using apply_inv_component.simps by auto
        also have "... \<ge> e ! n" using leq 
          by (smt (verit) add.assoc add_diff_assoc_enat le_iff_add) 
        finally show ?thesis .
      next
        case min_set
        from this obtain A where "min_set A = u ! n" by auto

        have "upd u (inv_upd u e) ! n = the (apply_component n (min_set A) (inv_upd u e))"
          using \<open>min_set A = u ! n\<close> unfolded_apply_update by auto
        also have "... = (min_list (nths (inv_upd u e) A))" 
          using apply_component.elims
          by simp

        have leq: "\<And>j. j \<in> A \<Longrightarrow> e!n \<le> (inv_upd u e)!j"
        proof-
          fix j
          assume "j \<in> A"
          hence "j < length e" using assms
            by (metis \<open>min_set A = u ! n\<close> in_mono mem_Collect_eq) 
          hence "j < length [0..<length e]"
            by simp
          have "(inv_upd u e)!j = (map (\<lambda>i. apply_inv_component i u e) [0..<length e])!j"
            using apply_inv_update.simps assms
            by simp 
          hence "(inv_upd u e)!j = apply_inv_component j u e"
            using nth_map \<open>j < length [0..<length e]\<close>
            by (metis \<open>j < length e\<close> nth_upt plus_nat.add_0)
          hence "(inv_upd u e)!j =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if j=m then (nth e j) else 0) | 
                minus_one \<Rightarrow> (if j=m then (nth e j)+1 else 0) |
                min_set A \<Rightarrow> (if j\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if j=m then (nth e j)-1 else 0))) (List.enumerate 0 u)))"
            by auto

          have "(List.enumerate 0 u)! n = (n, u ! n)"
            by (simp add: \<open>n < length e\<close> assms(1) nth_enumerate_eq)

          have fin: "finite (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if j=m then (nth e j) else 0) | 
                minus_one \<Rightarrow> (if j=m then (nth e j)+1 else 0) |
                min_set A \<Rightarrow> (if j\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if j=m then (nth e j)-1 else 0))) (List.enumerate 0 u)))" by auto
          have "e!n =  (case (min_set A)  of 
                zero \<Rightarrow> (if j=n then (nth e j) else 0) | 
                minus_one \<Rightarrow> (if j=n then (nth e j)+1 else 0) |
                min_set A \<Rightarrow> (if j\<in>A then (nth e n) else 0)|
                plus_one \<Rightarrow> (if j=n then (nth e j)-1 else 0))"
            by (simp add: \<open>j \<in> A\<close>)
          hence "e!n = (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if j=m then (nth e j) else 0) | 
                minus_one \<Rightarrow> (if j=m then (nth e j)+1 else 0) |
                min_set A \<Rightarrow> (if j\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if j=m then (nth e j)-1 else 0))) (n, u ! n)"
            using \<open>min_set A = u ! n\<close> by simp
          hence "e!n \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if j=m then (nth e j) else 0) | 
                minus_one \<Rightarrow> (if j=m then (nth e j)+1 else 0) |
                min_set A \<Rightarrow> (if j\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if j=m then (nth e j)-1 else 0))) (List.enumerate 0 u)))"
            using \<open>(List.enumerate 0 u)! n = (n, u ! n)\<close> nth_map
            by (metis (no_types, lifting) \<open>n < length e\<close> assms(1) in_set_conv_nth length_enumerate length_map)

          thus "e!n \<le> (inv_upd u e)!j"
            using fin Max_le_iff
            using \<open>inv_upd u e ! j = Max (set (map (\<lambda>(k, y). case y of zero \<Rightarrow>(if j=k then (nth e j) else 0) | minus_one \<Rightarrow> if j = k then e ! j + 1 else 0 | min_set A \<Rightarrow> if j \<in> A then e ! k else 0 | plus_one \<Rightarrow> if j = k then e ! j - 1 else 0) (List.enumerate 0 u)))\<close> by fastforce
        qed

        have "A \<noteq> {} \<and> A \<subseteq> {x. x < length u}" using assms
          by (simp add: \<open>min_set A = u ! n\<close>)
        hence "A \<noteq> {} \<and> A \<subseteq> {x. x < length (inv_upd u e)}" using assms
          by auto

        have "set (nths (inv_upd u e) A) = {(inv_upd u e) ! i |i. i < length (inv_upd u e) \<and> i \<in> A}"
          using set_nths by metis
        hence not_empty: "(set (nths (inv_upd u e) A)) \<noteq> {}"
          using \<open>A \<noteq> {} \<and> A \<subseteq> {x. x < length (inv_upd u e)}\<close>
          by (smt (z3) Collect_empty_eq equals0I in_mono mem_Collect_eq)
        hence "(nths (inv_upd u e) A) \<noteq> []"
          by blast
        hence min_eq_Min: "min_list (nths (inv_upd u e) A) = Min (set (nths (inv_upd u e) A))"
          using min_list_Min by blast

        have "finite (set (nths (inv_upd u e) A))" using assms \<open>min_set A = u ! n\<close>
          by simp
        hence "(e!n \<le> Min (set (nths (inv_upd u e) A))) = (\<forall>a\<in>(set (nths (inv_upd u e) A)). e!n \<le> a)"
          using not_empty Min_ge_iff by auto

        have "e!n \<le> Min (set (nths (inv_upd u e) A))" 
          unfolding \<open>(e!n \<le> Min (set (nths (inv_upd u e) A))) = (\<forall>a\<in>(set (nths (inv_upd u e) A)). e!n \<le> a)\<close>
        proof
          fix x 
          assume "x \<in> set (nths (inv_upd u e) A)"
          hence "x\<in> {(inv_upd u e) ! i |i. i < length (inv_upd u e) \<and> i \<in> A}"
            using set_nths
            by metis 
          hence "\<exists>j. j \<in> A \<and> x = (inv_upd u e)!j"
            by blast 
          thus "e ! n \<le> x " using leq
            by auto 
        qed

        hence "e!n \<le> (min_list (nths (inv_upd u e) A))"
          using min_eq_Min
          by metis 
        thus ?thesis
          using calculation by auto 
      next
        case plus_one
        hence A: "(\<lambda>(m,up). (case up of 
                zero \<Rightarrow>(if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (n,(u!n)) = (e!n) -1"
          by simp 
        have "(List.enumerate 0 u)!n = (n,(u!n))"
          using \<open>n < length e\<close> assms(1) nth_enumerate_eq
          by (metis add_0)
        hence "(e!n) -1 \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))" using plus_one nth_map A
          by (metis (no_types, lifting) \<open>n < length e\<close> assms(1) length_enumerate length_map nth_mem)
        hence leq: "(e!n) -1 \<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))" using Max_ge by simp

        have "e ! n \<le> ((e!n)-1)+1"
          by (metis dual_order.trans eSuc_minus_1 eSuc_plus_1 le_iff_add linorder_le_cases plus_1_eSuc(1))
        also have "... \<le> ( Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))) +1" using leq
          by simp 
        also have "... = (inv_upd u e) ! n  +1"
          using apply_inv_component.simps unfolded_apply_inv by presburger
        also have "... = upd u (inv_upd u e) ! n"
          using unfolded_apply_update plus_one  by auto 
        finally show ?thesis .
      qed
    qed
  qed 
qed


lemma apply_inv_is_min:
  assumes "length u = length e" and "valid_update u"
  shows "energy_Min (possible_inv u e) = {inv_upd u e}"
proof
  have apply_inv_leq_possible_inv: "\<forall>e'\<in>(possible_inv u e). (inv_upd u e) e\<le> e'"
  proof 
    fix e'
    assume "e' \<in> possible_inv u e"
    hence "energy_leq e (the (apply_update u e'))" by auto
    hence B: "\<forall>n < length e. e! n \<le> (the (apply_update u e')) ! n" unfolding energy_leq_def by auto

    from\<open>e' \<in> possible_inv u e\<close> have "apply_update u e' \<noteq> None" by simp
    have geq_0:  "\<And>i. i < length u \<Longrightarrow> u!i = minus_one \<Longrightarrow> e'!i >0"
    proof-
      fix i
      assume "i < length u" and "u!i = minus_one"
      have " e'!i =0 \<Longrightarrow> False"
      proof-
        assume "e'!i =0"
        hence "apply_component i minus_one e' = None"
          by simp 
        hence "apply_component i (u!i) e' = None"
          using \<open>u!i = minus_one\<close> by simp

        from \<open>apply_update u e' \<noteq> None\<close> have "those (map (\<lambda>i. apply_component i (u ! i) e') [0..<length e'])\<noteq> None" unfolding apply_update.simps
          by meson 
        hence "(map (\<lambda>i. apply_component i (u ! i) e') [0..<length e']) ! i \<noteq> None" using those_all_Some
          by (metis \<open>apply_update u e' \<noteq> None\<close> \<open>i < length u\<close> apply_update.simps length_map map_nth)
        hence "(\<lambda>i. apply_component i (u ! i) e') ([0..<length e'] ! i) \<noteq> None" using nth_map
          by (metis \<open>apply_update u e' \<noteq> None\<close> \<open>i < length u\<close> apply_update.simps length_map map_nth) 
        hence "apply_component i (u ! i) e' \<noteq> None"
          by (metis \<open>apply_update u e' \<noteq> None\<close> \<open>i < length u\<close> apply_update.elims nth_upt plus_nat.add_0)
        thus "False"
          using \<open>apply_component i (u!i) e' = None\<close> by simp
      qed

      then show " e'!i >0"
        by auto
    qed
      

    show "energy_leq (the (apply_inv_update u e)) e'" unfolding energy_leq_def 
    proof
      show "length (the (apply_inv_update u e)) = length e'" using assms
        by (metis (mono_tags, lifting) \<open>e' \<in> possible_inv u e\<close> energy_leq_def len_appl len_inv_appl mem_Collect_eq) 
      show "\<forall>n<length (the (apply_inv_update u e)). the (apply_inv_update u e) ! n \<le> e' ! n" 
      proof
        fix n 
        show " n < length (the (apply_inv_update u e)) \<longrightarrow> the (apply_inv_update u e) ! n \<le> e' ! n" 
        proof
          assume "n < length (the (apply_inv_update u e))"
          have "the (apply_inv_update u e) ! n = (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) ! n" using apply_inv_update.simps
            by (metis assms(1) option.sel)
          also have "... = apply_inv_component n u e"
            by (metis \<open>n < length (the (apply_inv_update u e))\<close> assms(1) len_inv_appl minus_nat.diff_0 nth_map_upt plus_nat.add_0)
          also have "... =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0)| 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps by auto
          finally have inv_max: "the (apply_inv_update u e) ! n = Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0)| 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u)))".

          from B have "e ! n \<le> (the (apply_update u e')) ! n" using \<open>n < length (the (apply_inv_update u e))\<close>
            using assms(1) len_inv_appl by auto 
          hence upd_v: "e ! n \<le> the (apply_component n (u ! n) e')" using apply_to_comp_n
            using \<open>length (the (apply_inv_update u e)) = length e'\<close> \<open>n < length (the (apply_inv_update u e))\<close> \<open>e' \<in> possible_inv u e\<close> by auto 

          have Max_iff: "(Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0)| 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u))) \<le> e' ! n)
                = (\<forall>a\<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth e n) else 0)| 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth e n)-1 else 0))) (List.enumerate 0 u))). a \<le> e' ! n)"
          proof(rule Max_le_iff)
            show "finite (set (map (\<lambda>(m, y). case y of zero \<Rightarrow> if n = m then e ! n else 0 | minus_one \<Rightarrow> if n = m then e ! n + 1 else 0 | min_set A \<Rightarrow> if n \<in> A then e ! m else 0 | plus_one \<Rightarrow> if n = m then e ! n - 1 else 0) (List.enumerate 0 u)))"
              by simp
            show "set (map (\<lambda>(m, y). case y of zero \<Rightarrow> if n = m then e ! n else 0 | minus_one \<Rightarrow> if n = m then e ! n + 1 else 0 | min_set A \<Rightarrow> if n \<in> A then e ! m else 0 | plus_one \<Rightarrow> if n = m then e ! n - 1 else 0) (List.enumerate 0 u)) \<noteq> {} "
              by (metis (no_types, lifting) \<open>n < length (inv_upd u e)\<close> assms(1) empty_iff len_inv_appl length_enumerate length_map nth_mem)
          qed


          show "the (apply_inv_update u e) ! n \<le> e' ! n"
            unfolding inv_max Max_iff
          proof
            fix a 
            assume "a \<in>(set (map (\<lambda>(m, up). case up of zero \<Rightarrow> if n = m then e ! n else 0 | minus_one \<Rightarrow> if n = m then e ! n + 1 else 0 | min_set A \<Rightarrow> if n \<in> A then e ! m else 0 | plus_one \<Rightarrow> if n = m then e ! n - 1 else 0) (List.enumerate 0 u)))"
            hence "\<exists>i. i< length (List.enumerate 0 u) \<and> a = (\<lambda>(m, up). case up of zero \<Rightarrow> if n = m then e ! n else 0 | minus_one \<Rightarrow> if n = m then e ! n + 1 else 0 | min_set A \<Rightarrow> if n \<in> A then e ! m else 0 | plus_one \<Rightarrow> if n = m then e ! n - 1 else 0) ((List.enumerate 0 u) ! i) " 
              using set_map
              by (metis (no_types, lifting) in_set_conv_nth length_map nth_map)
            from this obtain m where A: "a =  (\<lambda>(m, up). case up of zero \<Rightarrow> if n = m then e ! n else 0 | minus_one \<Rightarrow> if n = m then e ! n + 1 else 0 | min_set A \<Rightarrow> if n \<in> A then e ! m else 0 | plus_one \<Rightarrow> if n = m then e ! n - 1 else 0) (m, (u!m))"
              and "m < length u"
              using nth_enumerate_eq by fastforce

            consider (zero) "u ! m = zero" | (minus_one) "u ! m = minus_one" | (min) "\<exists>A. u !m = min_set A" | (plus_one) "u!m = plus_one"
              using update_component.exhaust by auto
            then show " a \<le> e' ! n " proof(cases)
              case zero
              hence A: "a= (if n = m then e ! n  else 0)" using A by simp
              then show ?thesis
              proof(cases "n=m")
                case True
                hence "a= e!n" using zero A by simp
                also have "... \<le> the (apply_component n (u ! n) e')" using upd_v by simp
                also have "... = the (apply_component n zero e')" using zero True by simp
                also have  "... = e'!n"
                  by simp
                finally show ?thesis by simp
              next
                case False
                then show ?thesis using zero A by simp
              qed
            next
              case minus_one
              hence A: "a= (if n = m then e ! n + 1 else 0)" using A by simp
              then show ?thesis 
              proof(cases "n=m")
                case True
                hence "a = e!n +1" using minus_one A by simp
                also have "... \<le> (the (apply_component n (u ! n) e')) +1" using upd_v by simp
                also have "... = (the (apply_component n minus_one e')) +1" using minus_one True by simp
                also have "... = (the (if ((e' ! n) > 0) then Some ((e' ! n) - 1) 
                                    else None)) +1" using apply_component.simps
                  by auto
                also have "... = (e'!n -1) +1" using geq_0
                  using True \<open>n < length (inv_upd u e)\<close> assms(1) minus_one by fastforce 
                also have "... = e'!n"
                proof(cases "e'!n = \<infinity>")
                  case True
                  then show ?thesis
                    by simp 
                next
                  case False
                  hence "\<exists>b. e' ! n = enat (Suc b)" using geq_0 True \<open>n < length (inv_upd u e)\<close> assms(1) minus_one
                    by (metis len_inv_appl not0_implies_Suc not_enat_eq not_iless0 zero_enat_def)
                  from this obtain b where "e' ! n = enat (Suc b)"  by auto 
                  then show ?thesis
                    by (metis eSuc_enat eSuc_minus_1 eSuc_plus_1)
                qed

                finally show ?thesis .
              next
                case False
                then show ?thesis using minus_one A by simp
              qed
            next
              case min
              from this obtain A where "u !m = min_set A" by auto
              hence A: "a = (if n \<in> A then e ! m else 0)" using A by simp
              then show ?thesis 
              proof(cases "n \<in> A")
                case True
                hence "a = e!m" using A min by simp

                have "(set (nths e' A)) \<noteq> {}" using set_nths True assms
                  by (smt (verit) Collect_empty_eq \<open>length (inv_upd u e) = length e'\<close> \<open>n < length (inv_upd u e)\<close>) 
                hence "(nths e' A) \<noteq> []"
                  by auto 

                from B have "e! m \<le> (the (apply_update u e')) ! m"
                  using \<open>m < length u\<close> assms(1) len_inv_appl by auto 
                hence upd_v: "e ! m \<le> the (apply_component m (u ! m) e')" using apply_to_comp_n \<open>m < length u\<close>
                  by (metis \<open>apply_update u e' \<noteq> None\<close> \<open>length (inv_upd u e) = length e'\<close> assms(1) len_inv_appl)
                hence "e ! m \<le> the (apply_component m (min_set A) e')" using \<open>u !m = min_set A\<close> by simp
                also have "... = the (Some (min_list (nths e' A)))"
                  by simp
                also have "... = (min_list (nths e' A))"
                  by simp
                also have "... = Min (set (nths e' A))" using min_list_Min \<open>(nths e' A) \<noteq> []\<close>
                  by auto
                also have "... \<le> e'!n" using True Min_le
                  using \<open>length (inv_upd u e) = length e'\<close> \<open>n < length (inv_upd u e)\<close> set_nths by fastforce 
                finally show ?thesis using \<open>a = e!m\<close>
                  by simp
              next
                case False
                then show ?thesis using \<open>u !m = min_set A\<close> A by simp
              qed
            next
              case plus_one
              hence A: "a= (if n = m then e ! n - 1 else 0)" using A by simp
              then show ?thesis
              proof(cases "n=m")
                case True

                hence "a =(e!n) -1" using plus_one A by simp
                also have "... \<le> (the (apply_component n (u ! n) e')) -1" 
                proof(cases "(the (apply_component n (u ! n) e')) = 0")
                  case True
                  hence "e!n = 0" using upd_v
                    by simp
                  then show ?thesis using True
                    by auto
                next
                  case False
                  then show ?thesis 
                  proof(cases "e!n = \<infinity>")
                    case True
                    then show ?thesis using upd_v
                      by simp
                  next
                    case False
                    then show ?thesis 
                    proof(cases "e!n =0")
                      case True
                      then show ?thesis
                        by simp
                    next
                      case False
                      hence "\<exists>a. e!n = enat (Suc a)" using \<open> e ! n \<noteq> \<infinity>\<close>
                        by (metis enat.exhaust old.nat.exhaust zero_enat_def) 
                      then show ?thesis
                      proof(cases "(the (apply_component n (u ! n) e')) = \<infinity>")
                        case True
                        then show ?thesis
                          by simp
                      next
                        case False
                        hence "\<exists>b. (the (apply_component n (u ! n) e')) = enat (Suc b)" using \<open> (the (apply_component n (u ! n) e'))\<noteq> 0\<close>
                          by (metis enat.exhaust old.nat.exhaust zero_enat_def)
                        then show ?thesis using \<open>\<exists>a. e!n = enat (Suc a)\<close> upd_v
                          by (metis Suc_le_eq diff_Suc_1 enat_ord_simps(1) idiff_enat_enat less_Suc_eq_le one_enat_def)
                      qed
                    qed
                  qed
                qed
                also have "... = (the (apply_component n plus_one e')) -1" using plus_one True by simp
                also have "... = the (Some ((e'!n)+1)) -1" using apply_component.simps
                  by auto
                also have "... = (e'!n +1) -1"
                  using True \<open>n < length (inv_upd u e)\<close> assms(1) plus_one by fastforce 
                also have "... = e'!n"
                proof(cases "e'!n = \<infinity>")
                  case True
                  then show ?thesis
                    by simp
                next
                  case False
                  then show ?thesis
                    by (simp add: add.commute)
                qed

                finally show ?thesis .
              next
                case False
                then show ?thesis using plus_one A by simp
              qed
            qed
          qed        
        qed
      qed
    qed
  qed


  have apply_inv_is_possible_inv: "\<And>u v. length u = length v \<Longrightarrow> valid_update u \<Longrightarrow> inv_upd u v \<in> possible_inv u v"
  using leq_up_inv inv_not_none_then inv_not_none by blast

  show "energy_Min (possible_inv u e) \<subseteq> {the (apply_inv_update u e)}" 
    using apply_inv_leq_possible_inv apply_inv_is_possible_inv energy_Min_def assms
    by (smt (verit, ccfv_SIG) Collect_cong insert_iff mem_Collect_eq subsetI) 
  show "{the (apply_inv_update u e)} \<subseteq> energy_Min (possible_inv u e)"
    using apply_inv_leq_possible_inv apply_inv_is_possible_inv energy_Min_def
    by (smt (verit, ccfv_SIG) \<open>energy_Min (possible_inv u e) \<subseteq> {the (apply_inv_update u e)}\<close> assms(1) assms(2) energy_leq.strict_trans1 insert_absorb mem_Collect_eq subset_iff subset_singletonD) 
qed

text\<open>
We now show that\<open>apply_inv_update u\<close> is decreasing. 
\<close>

lemma inv_up_leq: 
  assumes "apply_update u e \<noteq> None" and "valid_update u" 
  shows "(inv_upd u (upd u e)) e\<le> e"
  unfolding energy_leq_def proof
  from assms(1) have "length e = length u"
    by (metis apply_update.simps)
  hence "length (the (apply_update u e)) = length u" using len_appl assms(1)
    by presburger
  hence "(apply_inv_update u (the (apply_update u e))) \<noteq> None"
    using inv_not_none by presburger 
  thus "length (the (apply_inv_update u (the (apply_update u e)))) = length e" using len_inv_appl \<open>length (the (apply_update u e)) = length u\<close> \<open>length e = length u\<close>
    by presburger
  show "\<forall>n<length (the (apply_inv_update u (the (apply_update u e)))).
       the (apply_inv_update u (the (apply_update u e))) ! n \<le> e ! n "
  proof
    fix n 
    show "n < length (the (apply_inv_update u (the (apply_update u e)))) \<longrightarrow>
         the (apply_inv_update u (the (apply_update u e))) ! n \<le> e ! n"
    proof 
      assume "n < length (the (apply_inv_update u (the (apply_update u e))))"
      hence "n < length e"
        using \<open>length (the (apply_inv_update u (the (apply_update u e)))) = length e\<close> by auto 
      show "the (apply_inv_update u (the (apply_update u e))) ! n \<le> e ! n"
      proof-
        have "the (apply_inv_update u (the (apply_update u e))) !n = (map (\<lambda>n. apply_inv_component n u (the (apply_update u e))) [0..<length (the (apply_update u e))]) ! n " using apply_inv_update.simps
          using \<open>length (the (apply_update u e)) = length u\<close> \<open>length e = length u\<close> option.sel by auto 
        hence A: "the (apply_inv_update u (the (apply_update u e))) !n = apply_inv_component n u (the (apply_update u e))"
          by (metis \<open>length (the (apply_inv_update u (the (apply_update u e)))) = length e\<close> \<open>length (the (apply_update u e)) = length u\<close> \<open>length e = length u\<close> \<open>n < length (the (apply_inv_update u (the (apply_update u e))))\<close> diff_diff_left length_upt nth_map nth_upt plus_nat.add_0 zero_less_diff)
        have "apply_inv_component n u (the (apply_update u e)) \<le> e ! n" proof-

          have "\<forall>x \<in> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth (the (apply_update u e)) m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0)
                )) (List.enumerate 0 u)). x \<le> e ! n" 
          proof
            fix x 
            assume X: "x \<in> set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n) else 0)
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else 0
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0|
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0))
                   (List.enumerate 0 u))"
            hence "\<exists>m < length (List.enumerate 0 u). x =  (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n) else 0)
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else 0
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0 |
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0))
                   (List.enumerate 0 u)) ! m" using in_set_conv_nth
              by (metis (no_types, lifting) length_map) 
            from this obtain m where "m < length (List.enumerate 0 u)" and "x =  (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n) else 0)
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else 0
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0 |
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0))
                   (List.enumerate 0 u)) ! m" by auto
            hence "x = (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n) else 0)
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else 0
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0 |
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0))
                   ((List.enumerate 0 u) ! m)" using nth_map \<open>m < length (List.enumerate 0 u)\<close>
              by simp 
            hence X: "x= (\<lambda>(m, up).
                          case up of zero \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n) else 0)
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else 0
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0 |
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0))
                   (m, (u ! m))"
              by (metis (no_types, lifting) \<open>m < length (List.enumerate 0 u)\<close> add_cancel_left_left length_enumerate nth_enumerate_eq)



            consider (zero) "u ! m = zero" | (minus_one) "u ! m = minus_one" | (min) "\<exists>A. u !m = min_set A" | (plus_one) "u!m = plus_one"
              using update_component.exhaust by auto
            thus "x \<le> e ! n" proof(cases)
              case zero
              hence "x = (if n=m then (nth (the (apply_update u e)) n) else 0)" using X by simp
                then show ?thesis proof(cases "n=m")
                  case True
                  hence "x= upd u e ! n"
                    by (simp add: \<open>x = (if n = m then upd u e ! n else 0)\<close>) 
                  also have "... = the (apply_component n (u!n) e)"
                    using \<open>n < length e\<close> apply_to_comp_n assms(1) by auto 
                  also have "... = the (apply_component n zero e)" using zero True by simp
                  also have "... = e!n"
                    by simp 
                  finally show ?thesis by auto
                next
                  case False
                  hence "x= 0"
                    by (simp add: \<open>x = (if n = m then upd u e ! n else 0)\<close>)
                  then show ?thesis by simp
                qed
              next
                case minus_one
                then show ?thesis proof(cases "m=n")
                  case True
                  hence "u ! n = minus_one" using minus_one by simp
                  have "(apply_component n (u ! n) e) \<noteq> None"  using assms(1) those_all_Some apply_update.simps apply_component.simps \<open>n < length e\<close>
                    by (smt (verit) add_cancel_right_left length_map map_nth nth_map nth_upt)
                  hence "e ! n > 0" using \<open>u ! n = minus_one\<close> by auto
                  hence "((e!n) -1 )+1 = e!n" proof(cases "e ! n = \<infinity>")
                    case True
                    then show ?thesis by simp
                  next
                    case False
                    hence "\<exists>b. e ! n = enat b" by simp
                    from this obtain b where "e ! n = enat b" by auto
                    hence "\<exists>b'. b = Suc b'" using \<open>e ! n > 0\<close>
                      by (simp add: not0_implies_Suc zero_enat_def)
                    from this obtain b' where "b = Suc b'" by auto
                    hence "e ! n = enat (Suc b')" using \<open>e ! n = enat b\<close> by simp
                    hence "(e!n)-1 = enat b'"
                      by (metis eSuc_enat eSuc_minus_1) 
                    hence "((e!n) -1 )+1 = enat (Suc b')"
                      using eSuc_enat plus_1_eSuc(2) by auto 
                    then show ?thesis using \<open>e ! n = enat (Suc b')\<close> by simp  
                  qed

                  from True have "x = (the (apply_update u e) ! n) +1" using X minus_one by simp
                  also have "... = (the (apply_component n (u ! n) e)) +1" using apply_to_comp_n assms
                    using \<open>length (the (apply_inv_update u (the (apply_update u e)))) = length e\<close> \<open>n < length (the (apply_inv_update u (the (apply_update u e))))\<close> by presburger
                  also have "... = ((e !n) -1 ) +1" using \<open>u ! n = minus_one\<close> assms those_all_Some apply_update.simps apply_component.simps
                    using \<open>0 < e ! n\<close> by auto 
                  finally have "x = e ! n" using \<open>((e!n) -1 )+1 = e!n\<close> by simp
                  then show ?thesis by simp
                next
                  case False
                  hence "x = 0" using X minus_one by simp
                  then show ?thesis
                    by simp 
                qed
              next
                case min
                from this obtain A where "u ! m = min_set A" by auto
                hence "A\<noteq>{} \<and> A \<subseteq> {x. x < length e}" using assms
                  by (simp add: \<open>length e = length u\<close>) 
                then show ?thesis proof(cases "n \<in> A")
                  case True
                  hence "x = the (apply_update u e) ! m" using X \<open>u ! m = min_set A\<close> by simp
                  also have "... = (the (apply_component n (u ! m) e))" using apply_to_comp_n
                    by (metis \<open>length e = length u\<close> \<open>m < length (List.enumerate 0 u)\<close> \<open>u ! m = min_set A\<close> apply_component.simps(3) assms(1) length_enumerate) 
                  also have "... = (min_list (nths e A))" using \<open>u ! m = min_set A\<close> apply_component.simps by simp
                  also have "... = Min (set (nths e A))" using \<open>A\<noteq>{} \<and> A \<subseteq> {x. x < length e}\<close> min_list_Min
                    by (smt (z3) True \<open>n < length e\<close> less_zeroE list.size(3) mem_Collect_eq set_conv_nth set_nths)
                  also have "... \<le> e!n" using True Min_le \<open>A\<noteq>{} \<and> A \<subseteq> {x. x < length e}\<close>
                    using List.finite_set \<open>n < length e\<close> set_nths by fastforce
                  finally show ?thesis .
                next
                  case False
                  hence "x = 0" using X \<open>u ! m = min_set A\<close> by simp
                  then show ?thesis by simp
                qed
              next 
                case plus_one 
                hence X: "x= (if n=m then (nth (the (apply_update u e)) n)-1 else 0)" using X
                  by simp
                then show ?thesis
                proof(cases "n=m")
                  case True
                  hence X: "x=(nth (the (apply_update u e)) n)-1" using X by simp

                  have "nth (the (apply_update u e)) n = the (apply_component n (u!n) e)" using apply_update.simps
                    using \<open>n < length e\<close> apply_to_comp_n assms(1) by auto 
                  also have "... = the (apply_component n plus_one e)" using plus_one True by simp
                  also have "... = (e ! n + 1)" unfolding apply_component.simps
                    by simp 
                  finally have "x = (e ! n + 1)-1" using X
                    by simp 
                  then show ?thesis
                    by (simp add: add.commute) 
                next
                  case False
                  hence "x = 0" using X plus_one by simp
                  then show ?thesis by simp
                qed
              qed
            qed

          hence leq: "\<forall>x \<in>(set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow>(if n=m then (nth (the (apply_update u e)) n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth (the (apply_update u e)) m) else 0) |
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0))) (List.enumerate 0 u))). x \<le> e ! n" by blast

          have "apply_inv_component n u (the (apply_update u e)) =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n) else 0) | 
                minus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)+1 else 0) |
                min_set A \<Rightarrow> (if n\<in>A then (nth (the (apply_update u e)) m) else 0)|
                plus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)-1 else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps
            by blast 
          also have "... \<le> e! n" using leq Max_le_iff
            by (smt (verit) List.finite_set \<open>length e = length u\<close> \<open>n < length e\<close> empty_iff length_enumerate length_map nth_mem)
          finally show ?thesis .
        qed
        thus ?thesis using A by presburger 
      qed
    qed
  qed
qed



text\<open>We now conclude that for any valid update the functions $e \mapsto  \min \lbrace e' \ | \ e \leq u(e') \rbrace$ and $u$ form a 
Galois connection between the domain of $u$ and the set of energies of the same length as $u$ w.r.t 
to the component-wise order.\<close>

lemma galois_connection:
  assumes "apply_update u e' \<noteq> None" and "length e = length e'" and 
          "valid_update u"
  shows "(inv_upd u e) e\<le> e' = e e\<le> (upd u e')"
proof
  show "energy_leq (the (apply_inv_update u e)) e' \<Longrightarrow> energy_leq e (upd u e')" 
  proof- 
    assume A: "energy_leq (the (apply_inv_update u e)) e'" 
    from assms(1) have "length u = length e" using apply_update.simps assms(2) by metis
    hence leq: "energy_leq e (the (apply_update u (the (apply_inv_update u e))))" using leq_up_inv assms(3) inv_not_none
      by presburger
    have "(apply_update u (the (apply_inv_update u e))) \<noteq> None" using \<open>length u = length e\<close>
      using inv_not_none inv_not_none_then by blast
    hence "energy_leq (the (apply_update u (the (apply_inv_update u e)))) (the (apply_update u e'))" using A updates_monotonic
      using \<open>length u = length e\<close> assms(3) inv_not_none len_inv_appl by presburger  
    thus "energy_leq e (the (apply_update u e'))" using leq
      using energy_leq.trans by blast 
  qed
  show "energy_leq e (the (apply_update u e')) \<Longrightarrow> energy_leq (the (apply_inv_update u e)) e' " 
  proof-
    assume A: "energy_leq e (the (apply_update u e'))"
    have "apply_inv_update u e \<noteq> None" using assms
      by (metis apply_update.simps inv_not_none) 
    have "length u = length e" using assms
      by (metis apply_update.elims) 
    from A have "e' \<in> possible_inv u e"
      using assms(1) mem_Collect_eq by auto
    thus "energy_leq (the (apply_inv_update u e)) e'" using apply_inv_is_min assms \<open>length u = length e\<close> energy_Min_def
      by (smt (verit) A Collect_cong energy_leq.strict_trans1 inv_up_leq inverse_monotonic len_appl) 
  qed
qed

end