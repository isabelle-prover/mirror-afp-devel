section \<open>Vectors of (extended) Naturals as Energies\<close>

theory Energy_Order
  imports Main List_Lemmas "HOL-Library.Extended_Nat" Well_Quasi_Orders.Well_Quasi_Orders
begin

text \<open>
We consider vectors with entries in the extended naturals as energies and fix a dimension later. 
In this theory we introduce the component-wise order on energies (represented as lists of enats) 
as well as a minimum and supremum.
\<close>

type_synonym energy = "enat list"

definition energy_leq:: "energy \<Rightarrow> energy \<Rightarrow> bool" (infix "e\<le>" 80) where 
  "energy_leq e e' = ((length e = length e') 
                      \<and> (\<forall>i < length e. (e ! i) \<le> (e' ! i)))"

abbreviation energy_l:: "energy \<Rightarrow> energy \<Rightarrow> bool" (infix "e<" 80) where 
  "energy_l e e' \<equiv>  e e\<le> e' \<and> e \<noteq> e'"

text\<open>We now establish that \<open>energy_leg\<close> is a partial order.\<close>

interpretation energy_leq: ordering "energy_leq" "energy_l"
proof
  fix e e' e''
  show "e e\<le> e" using energy_leq_def by simp
  show "e e\<le> e' \<Longrightarrow> e' e\<le> e'' \<Longrightarrow> e e\<le> e''" using energy_leq_def by fastforce 
  show "e e< e' = e e< e'" by simp
  show "e e\<le> e' \<Longrightarrow> e' e\<le> e \<Longrightarrow> e = e'" using energy_leq_def
    by (metis (no_types, lifting) nth_equalityI order_antisym_conv)
qed

text\<open> 
We now show that it is well-founded when considering a fixed dimension \<open>n\<close>. 
For the proof we define the subsequence of a given sequence of energies such that the last entry is 
increasing but never equals \<open>\<infinity>\<close>.\<close>

fun subsequence_index::"(nat \<Rightarrow> energy) \<Rightarrow> nat \<Rightarrow> nat" where
  "subsequence_index f 0 = (SOME x. (last (f x) \<noteq> \<infinity>))" | 
  "subsequence_index f (Suc n) = (SOME x. (last (f x) \<noteq> \<infinity> 
            \<and> (subsequence_index f n) < x 
            \<and> (last (f (subsequence_index f n)) \<le> last (f x))))"

lemma energy_leq_wqo: 
  shows "wqo_on energy_leq {e::energy. length e = n}"
proof
  show "transp_on {e. length e = n} (e\<le>)"
    by (metis energy_leq.trans transp_onI)
  show "almost_full_on (e\<le>) {e::energy. length e = n}" 
  proof(induct n)
    case 0
    then show ?case
      by (smt (verit, del_insts) almost_full_onI energy_leq.refl good_def length_0_conv mem_Collect_eq zero_less_Suc)
  next
    case (Suc n)
    hence allF: "\<forall>f \<in> SEQ {e::energy. length e = n}. (\<exists>i j. i < j \<and> (f i) e\<le> (f j))" 
      unfolding almost_full_on_def good_def by simp

    have "{e::energy. length e = Suc n} = {e@[x]|e x::enat. e \<in> {e::energy. length e = n}}"
      using length_Suc_conv_rev by auto
    show ?case 
    proof
      fix f (* f:: nat \<Rightarrow> {e. length e = Suc n} ist folge von energies*)
      show "\<forall>i. f i \<in> {e::energy. length e = Suc n} \<Longrightarrow> good (e\<le>) f" 
      proof-
        assume "\<forall>i. f i \<in> {e::energy. length e = Suc n}"
        show "good (e\<le>) f" unfolding good_def proof-
          show "\<exists>i j. i < j \<and> f i e\<le> f j" 
          proof(cases "finite {i::nat. (f i) ! n = \<infinity>}")
            case True 
            define upbound where "upbound = Sup {(f i) ! n| i::nat. (f i) ! n \<noteq> \<infinity>}" (* betrachte teilfolge ohne unendlich *)
            then show ?thesis 
            proof(cases "upbound = \<infinity>")
              case True (* dann existiert eine steigende Teilfolge, wende induktionshyps darauf an *)
              have exist: "\<And>i. (f i) ! n \<noteq> \<infinity> \<Longrightarrow> \<exists>j. i < j \<and> (f j) ! n \<noteq> \<infinity> \<and> (f i) ! n \<le> (f j) ! n"
              proof-
                fix i 
                assume "(f i) ! n \<noteq> \<infinity>"
                have "\<not>(\<exists>j. i < j \<and> (f j) ! n \<noteq> \<infinity> \<and>(f i) ! n \<le> (f j) ! n) \<Longrightarrow> False"
                proof-
                  assume "\<not>(\<exists>j. i < j \<and> (f j) ! n \<noteq> \<infinity> \<and> (f i) ! n \<le> (f j) ! n)"
                  hence A: "\<And>j. i < j \<Longrightarrow> (f j) ! n = \<infinity> \<or> (f i) ! n > (f j) ! n" by auto

                  define max_value where "max_value = Max {(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>}"
                  have "\<And>k. (f k) ! n \<noteq> \<infinity> \<Longrightarrow>(f k) ! n \<le> max_value" 
                  proof-
                    fix k 
                    assume not_inf: "(f k) ! n \<noteq> \<infinity>"
                    show "(f k) ! n \<le> max_value" 
                    proof(cases "k \<le> i")
                      case True
                      hence "(f k) ! n \<in> {(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>}" using not_inf  by auto              
                      then show ?thesis using Max_ge \<open>(f k) ! n \<in> {(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>}\<close> max_value_def by auto
                    next
                      case False
                      hence "(f k) ! n < (f i) ! n" using A not_inf
                        by (meson leI)
                      have "(f i) ! n \<in> {(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>}" using \<open>(f i) ! n \<noteq> \<infinity>\<close> by auto 
                      hence "(f i) ! n \<le> max_value" using Max_ge max_value_def by auto
                      then show ?thesis using \<open>(f k) ! n < (f i) ! n\<close> by auto
                    qed
                  qed

                  hence "upbound = max_value" using upbound_def
                    by (smt (verit) Sup_least True antisym enat_ord_code(3) mem_Collect_eq)

                  have " (f i)! n \<in> {(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>}" using \<open>(f i) ! n \<noteq> \<infinity>\<close> by auto
                  hence notempty: "{(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>} \<noteq> {}" by auto
                  have "finite {(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>}" by simp
                  hence "max_value \<in> {(f k) ! n| k. k \<le> i \<and> (f k) ! n \<noteq> \<infinity>}" unfolding max_value_def using Max_in notempty by blast
                  hence "max_value \<noteq> \<infinity>" using max_value_def by auto
                  hence "upbound \<noteq> \<infinity>" using \<open>upbound = max_value\<close> by simp
                  thus "False" using True by simp
                qed
                thus "\<exists>j. i < j \<and> (f j) ! n \<noteq> \<infinity> \<and>(f i) ! n \<le> (f j) ! n"
                  by blast 
              qed

              define f' where "f' \<equiv> \<lambda>i. butlast (f (subsequence_index f i))"
              
              have "f' \<in> SEQ {e::energy. length e = n}" 
              proof
                show "\<forall>i. f' i \<in> {e. length e = n}"
                proof
                  fix i 
                  have "(f (subsequence_index f i)) \<in> {e. length e = Suc n}" using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close>
                    by simp 
                  thus "f' i \<in> {e. length e = n}" 
                    using f'_def by auto
                qed
              qed
              hence "(\<exists>i j. i < j \<and> (f' i) e\<le> (f' j))" 
                using allF by simp
              from this obtain i j where ij: "i < j \<and> (f' i) e\<le> (f' j)" by auto
              hence le: "butlast (f (subsequence_index f i)) e\<le> butlast (f (subsequence_index f j))" using f'_def by simp

              have last: "\<And>x. last (f x) = (f x) ! n" using last_len
                using \<open>\<forall>i. f i \<in> {e. length e = Suc n}\<close> by auto 
              have "{x. (last (f x) \<noteq> \<infinity>)} \<noteq> {}" 
              proof
                assume "{x. last (f x) \<noteq> \<infinity>} = {}"
                hence "\<And>x. last (f x) = \<infinity>" by auto
                hence "\<And>x. (f x) ! n = \<infinity>" using \<open>\<And>x. last (f x) = (f x) ! n\<close> by auto
                thus "False" using \<open>finite {i::nat. (f i) ! n = \<infinity>}\<close> by simp
              qed
              hence subsequence_index_0: "(last (f (subsequence_index f 0)) \<noteq> \<infinity>)" 
                using subsequence_index.simps(1)
                by (metis (mono_tags, lifting) Collect_empty_eq some_eq_imp)

              have subsequence_index_Suc: "\<And>m. (last (f (subsequence_index f (Suc m))) \<noteq> \<infinity> \<and> (subsequence_index f m) < (subsequence_index f (Suc m)) \<and> (last (f (subsequence_index f m)) \<le> last (f (subsequence_index f (Suc m)))))"
              proof-
                fix m 
                have some: "subsequence_index f (Suc m) = (SOME x. last (f x) \<noteq> \<infinity> \<and> subsequence_index f m < x \<and> last (f (subsequence_index f m)) \<le> last (f x))" using subsequence_index.simps(2) by auto
                show "(last (f (subsequence_index f (Suc m))) \<noteq> \<infinity> \<and> (subsequence_index f m) < (subsequence_index f (Suc m)) \<and> (last (f (subsequence_index f m)) \<le> last (f (subsequence_index f (Suc m)))))" 
                proof(induct m)
                  case 0
                  have "{x. last (f x) \<noteq> \<infinity> \<and> subsequence_index f 0 < x \<and> last (f (subsequence_index f 0)) \<le> last (f x)} \<noteq> {}"
                    unfolding last using subsequence_index_0 exist
                    by (simp add: last)
                  then show ?case using some some_eq_ex
                    by (smt (z3) empty_Collect_eq subsequence_index.simps(2))
                next
                  case (Suc m)
                  hence "{x. last (f x) \<noteq> \<infinity> \<and> subsequence_index f (Suc m) < x \<and> last (f (subsequence_index f (Suc m))) \<le> last (f x)} \<noteq> {}"
                    unfolding last using exist by simp
                  then show ?case using some some_eq_ex 
                    by (smt (z3) empty_Collect_eq subsequence_index.simps(2))
                qed
              qed
              hence "\<And>i j. i < j \<Longrightarrow> subsequence_index f i < subsequence_index f j"
                by (simp add: lift_Suc_mono_less) 
              hence "subsequence_index f i < subsequence_index f j" using \<open>i < j \<and> (f' i) e\<le> (f' j)\<close> by simp

              have "\<And>i j. i < j \<Longrightarrow> last (f (subsequence_index f i)) \<le> last (f (subsequence_index f j))"
              proof-
                fix i j
                show "i < j \<Longrightarrow> last (f (subsequence_index f i)) \<le> last (f (subsequence_index f j))"
                proof-
                  assume "i < j"
                  show "last (f (subsequence_index f i)) \<le> last (f (subsequence_index f j))" using \<open>i < j\<close> 
                  proof(induct "j-i" arbitrary: i j)
                    case 0
                    then show ?case by simp
                  next
                    case (Suc x)
                    then show ?case 
                    proof(cases "x = 0")
                      case True
                      hence "j = Suc i" using Suc
                        by (simp add: Nat.lessE Suc_pred diff_diff_cancel) 
                      then show ?thesis using subsequence_index_Suc by simp
                    next
                      case False
                      hence "\<exists>x'. x = Suc x'"
                        by (simp add: not0_implies_Suc) 
                      then show ?thesis using Suc subsequence_index_Suc
                        by (smt (verit, ccfv_SIG) Suc_leD diff_Suc_Suc diff_diff_cancel diff_le_self dual_order.strict_trans2 not_less_eq_eq verit_comp_simplify1(3) zero_less_diff)
                    qed
                  qed
                qed
              qed
              hence "(f (subsequence_index f i))!n \<le> (f (subsequence_index f j))!n" using \<open>i < j \<and> (f' i) e\<le> (f' j)\<close> last by simp

              have "(f (subsequence_index f i)) e\<le> (f (subsequence_index f j))" unfolding energy_leq_def 
              proof
                show "length (f (subsequence_index f i)) = length (f (subsequence_index f j))" using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
                show "\<forall>ia<length (f (subsequence_index f i)). f (subsequence_index f i) ! ia \<le> f (subsequence_index f j) ! ia "
                proof
                  fix ia
                  show "ia < length (f (subsequence_index f i)) \<longrightarrow> f (subsequence_index f i) ! ia \<le> f (subsequence_index f j) ! ia"
                  proof
                    assume "ia < length (f (subsequence_index f i))"
                    hence "ia < Suc n" using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
                    show "f (subsequence_index f i) ! ia \<le> f (subsequence_index f j) ! ia " 
                    proof(cases "ia < n")
                      case True
                      hence "f (subsequence_index f i) ! ia = (butlast (f (subsequence_index f i))) ! ia" using nth_butlast \<open>ia < length (f (subsequence_index f i))\<close> \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close>
                        by (metis (mono_tags, lifting) SEQ_iff \<open>f' \<in> SEQ {e. length e = n}\<close> f'_def mem_Collect_eq)
                      also have "... \<le> (butlast (f (subsequence_index f j))) ! ia" using le unfolding energy_leq_def using True \<open>f' \<in> SEQ {e. length e = n}\<close> f'_def by simp
                      also have "... = f (subsequence_index f j) ! ia" using True nth_butlast \<open>ia < length (f (subsequence_index f i))\<close> \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close>
                        by (metis (mono_tags, lifting) SEQ_iff \<open>f' \<in> SEQ {e. length e = n}\<close> f'_def mem_Collect_eq)
                      finally show ?thesis .
                    next
                      case False
                      hence "ia = n" using \<open>ia < Suc n\<close> by simp
                      then show ?thesis using \<open>(f (subsequence_index f i))!n \<le> (f (subsequence_index f j))!n\<close> by simp
                    qed
                  qed
                qed
              qed
              then show ?thesis using \<open>subsequence_index f i < subsequence_index f j\<close> by auto
            next
              case False (* dann existiert ein x, sodass {(f i) ! n = x} unendlich ist \<Rightarrow> dann analog zu infinite infinity *)
              hence "\<exists>upbound_nat. upbound = enat upbound_nat" by simp
              from this obtain upbound_nat where "upbound = enat upbound_nat" by auto

              have "\<not>(\<exists>x. infinite {i::nat. (f i) ! n = x}) \<Longrightarrow> False " 
              proof- 
                assume "\<not>(\<exists>x. infinite {i::nat. (f i) ! n = x})"
                hence allfinite: "\<And>x. x \<le> upbound \<Longrightarrow> finite {i::nat. (f i) ! n = x}" by auto

                have "\<And>k. k \<noteq> \<infinity> \<Longrightarrow> finite {n::enat. n \<le> k}"
                  by (metis finite_enat_bounded mem_Collect_eq not_enat_eq)
                hence "finite ({x. x \<le> upbound} \<union> {\<infinity>}) " using False by simp
                hence "finite {{i::nat. (f i) ! n = x}| x. x \<le> upbound \<or> x = \<infinity>}" by simp
                hence union_finite: "finite (\<Union> {{i::nat. (f i) ! n = x}| x. x \<le> upbound \<or> x = \<infinity>})" using finite_Union allfinite True by auto

                have "{i::nat. True} = (\<Union> {{i::nat. (f i) ! n = x}| x. x \<le> upbound \<or> x = \<infinity>})" 
                proof
                  show "{i. True} \<subseteq> \<Union> {{i. f i ! n = x} |x. x \<le> upbound \<or> x = \<infinity>}" 
                  proof
                    fix x 
                    show "x \<in> {i. True} \<Longrightarrow> x \<in> \<Union> {{i. f i ! n = x} |x. x \<le> upbound \<or> x = \<infinity>}"
                    proof-
                      assume  "x \<in> {i. True}"
                      hence "x \<in> {i. f i ! n = f x ! n}" by simp
                      show "x \<in> \<Union> {{i. f i ! n = x} |x. x \<le> upbound \<or> x = \<infinity>}" 
                      proof(cases "f x ! n = \<infinity>")
                        case True
                        thus "x \<in> \<Union> {{i. f i ! n = x} |x. x \<le> upbound \<or> x = \<infinity>}" using \<open>x \<in> {i. f i ! n = f x ! n}\<close>
                          by auto
                      next
                        case False
                        hence "f x ! n \<le> upbound" using upbound_def
                          by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq) 
                        thus "x \<in> \<Union> {{i. f i ! n = x} |x. x \<le> upbound \<or> x = \<infinity>}" using \<open>x \<in> {i. f i ! n = f x ! n}\<close>
                          by auto
                      qed
                    qed
                  qed
                  show "\<Union> {{i. f i ! n = x} |x. x \<le> upbound \<or> x = \<infinity>} \<subseteq> {i. True}" by simp
                qed
                thus "False" using union_finite by simp
              qed
              hence "\<exists>x. infinite {i::nat. (f i) ! n = x}" by auto
              from this obtain x where inf_x: "infinite {i::nat. (f i) ! n = x}" by auto

              (* Copy Paste case infinite {i::nat. (f i) ! n = \<infinity>} *)
              define f' where "f' \<equiv> \<lambda>i. butlast (f (enumerate {i::nat. (f i) ! n = x} i))" (* unendliche Teilfolge mit letzter Eintrag = x, ohne diesen Eintrag*)
              have "\<forall>i. f' i \<in> {e. length e = n}" 
              proof
                fix i
                have "f (enumerate {i::nat. (f i) ! n = x} i) \<in> {e. length e = Suc n}" using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
                hence "length (f (enumerate {i::nat. (f i) ! n = x} i)) = Suc n" by simp
                hence "length (butlast (f (enumerate {i::nat. (f i) ! n = x} i))) = n" using length_butlast
                  by simp
                hence "butlast (f (enumerate {i::nat. (f i) ! n = x} i)) \<in> {e. length e = n}" by simp
                thus "f' i \<in> {e. length e = n}" using f'_def by simp
              qed
              hence "f' \<in> SEQ {e::energy. length e = n}"
                unfolding SEQ_def by simp
              hence "(\<exists>i j. i < j \<and> (f' i) e\<le> (f' j))" 
                using allF by simp
              from this obtain i j where ij: "i < j \<and> (f' i) e\<le> (f' j)" by auto
              hence le: "(enumerate {i::nat. (f i) ! n = x} i) < (enumerate {i::nat. (f i) ! n = x} j)" 
                using enumerate_mono inf_x by simp
              have "(f (enumerate {i::nat. (f i) ! n = x} i)) e\<le> (f (enumerate {i::nat. (f i) ! n = x} j))" 
                unfolding energy_leq_def 
              proof
                show " length (f (wellorder_class.enumerate {i. f i ! n = x} i)) =
                     length (f (wellorder_class.enumerate {i. f i ! n = x} j))" 
                  using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
                show "\<forall>ia<length (f (wellorder_class.enumerate {i. f i ! n = x} i)).
                      f (wellorder_class.enumerate {i. f i ! n = x} i) ! ia
                      \<le> f (wellorder_class.enumerate {i. f i ! n = x} j) ! ia " 
                proof
                  fix ia 
                  show "ia < length (f (wellorder_class.enumerate {i. f i ! n = x} i)) \<longrightarrow>
                      f (wellorder_class.enumerate {i. f i ! n = x} i) ! ia
                      \<le> f (wellorder_class.enumerate {i. f i ! n = x} j) ! ia" 
                  proof
                    assume "ia < length (f (wellorder_class.enumerate {i. f i ! n = x} i))"
                    hence "ia < Suc n" using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
                    show "f (wellorder_class.enumerate {i. f i ! n = x} i) ! ia
                        \<le> f (wellorder_class.enumerate {i. f i ! n = x} j) ! ia" 
                    proof(cases "ia < n")
                      case True
                      hence  "f (wellorder_class.enumerate {i. f i ! n = x} i) ! ia = (f' i) ! ia" using f'_def
                        by (smt (verit) SEQ_iff \<open>f' \<in> SEQ {e. length e = n}\<close> mem_Collect_eq nth_butlast) 
                      also have "... \<le> (f' j) ! ia" using ij energy_leq_def True \<open>f' \<in> SEQ {e. length e = n}\<close>
                        by simp
                      also have "... = f (wellorder_class.enumerate {i. f i ! n = x} j) ! ia" using f'_def True
                        by (smt (verit) SEQ_iff \<open>f' \<in> SEQ {e. length e = n}\<close> mem_Collect_eq nth_butlast)
                      finally show ?thesis .
                    next
                      case False
                      hence "ia = n" using \<open>ia < Suc n\<close> by simp
                      hence "f (wellorder_class.enumerate {i. f i ! n = x} i) ! ia = x" 
                        using enumerate_in_set \<open>infinite {i::nat. (f i) ! n = x}\<close>
                        by auto  
                      hence "f (wellorder_class.enumerate {i. f i ! n = x} i) ! ia = f (wellorder_class.enumerate {i. f i ! n = x} j) ! ia" 
                        using enumerate_in_set \<open>infinite {i::nat. (f i) ! n = x}\<close> \<open>ia = n\<close>
                        by force 
                      then show ?thesis by simp
                    qed
                  qed
                qed
              qed
              then show ?thesis using le by auto
            qed
          next
            case False (* betrachte teilfolge mit nur unendlich,  wende induktionshyps darauf an *)
            define f' where "f' \<equiv> \<lambda>i. butlast (f (enumerate {i::nat. (f i) ! n = \<infinity>} i))" (* unendliche Teilfolge mit letzter Eintrag = \<infinity>, ohne diesen Eintrag*)
            have "\<forall>i. f' i \<in> {e. length e = n}" 
            proof
              fix i
              have "f (enumerate {i::nat. (f i) ! n = \<infinity>} i) \<in> {e. length e = Suc n}" using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
              hence "length (f (enumerate {i::nat. (f i) ! n = \<infinity>} i)) = Suc n" by simp
              hence "length (butlast (f (enumerate {i::nat. (f i) ! n = \<infinity>} i))) = n" using length_butlast
                by simp
              hence "butlast (f (enumerate {i::nat. (f i) ! n = \<infinity>} i)) \<in> {e. length e = n}" by simp
              thus "f' i \<in> {e. length e = n}" using f'_def by simp
            qed
            hence "f' \<in> SEQ {e::energy. length e = n}"
              unfolding SEQ_def by simp
            hence "(\<exists>i j. i < j \<and> (f' i) e\<le> (f' j))" 
              using allF by simp
            from this obtain i j where ij: "i < j \<and> (f' i) e\<le> (f' j)" by auto
            hence le: "(enumerate {i::nat. (f i) ! n = \<infinity>} i) < (enumerate {i::nat. (f i) ! n = \<infinity>} j)" 
              using enumerate_mono False by simp
            have "(f (enumerate {i::nat. (f i) ! n = \<infinity>} i)) e\<le> (f (enumerate {i::nat. (f i) ! n = \<infinity>} j))" 
              unfolding energy_leq_def 
            proof
              show " length (f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i)) =
                     length (f (wellorder_class.enumerate {i. f i ! n = \<infinity>} j))" 
                using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
              show "\<forall>ia<length (f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i)).
                      f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i) ! ia
                      \<le> f (wellorder_class.enumerate {i. f i ! n = \<infinity>} j) ! ia " 
              proof
                fix ia 
                show "ia < length (f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i)) \<longrightarrow>
                      f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i) ! ia
                      \<le> f (wellorder_class.enumerate {i. f i ! n = \<infinity>} j) ! ia" 
                proof
                  assume "ia < length (f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i))"
                  hence "ia < Suc n" using \<open>\<forall>i. f i \<in> {e::energy. length e = Suc n}\<close> by simp
                  show "f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i) ! ia
                        \<le> f (wellorder_class.enumerate {i. f i ! n = \<infinity>} j) ! ia" 
                  proof(cases "ia < n")
                    case True
                    hence  "f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i) ! ia = (f' i) ! ia" using f'_def
                      by (smt (verit) SEQ_iff \<open>f' \<in> SEQ {e. length e = n}\<close> mem_Collect_eq nth_butlast) 
                    also have "... \<le> (f' j) ! ia" using ij energy_leq_def True \<open>f' \<in> SEQ {e. length e = n}\<close>
                      by simp
                    also have "... = f (wellorder_class.enumerate {i. f i ! n = \<infinity>} j) ! ia" using f'_def True
                      by (smt (verit) SEQ_iff \<open>f' \<in> SEQ {e. length e = n}\<close> mem_Collect_eq nth_butlast)
                    finally show ?thesis .
                  next
                    case False
                    hence "ia = n" using \<open>ia < Suc n\<close> by simp
                    hence "f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i) ! ia = \<infinity>" 
                      using enumerate_in_set \<open>infinite {i::nat. (f i) ! n = \<infinity>}\<close>
                      by auto  
                    hence "f (wellorder_class.enumerate {i. f i ! n = \<infinity>} i) ! ia = f (wellorder_class.enumerate {i. f i ! n = \<infinity>} j) ! ia" 
                      using enumerate_in_set \<open>infinite {i::nat. (f i) ! n = \<infinity>}\<close> \<open>ia = n\<close>
                      by force 
                    then show ?thesis by simp
                  qed
                qed
              qed
            qed
            thus "\<exists>i j. i < j \<and> (f i) e\<le> (f j)"using le by auto
          qed
        qed
      qed
    qed
  qed
qed

text\<open>\subsection*{Minimum}\<close>

definition energy_Min:: "energy set \<Rightarrow> energy set" where
  "energy_Min A = {e\<in>A . \<forall>e'\<in>A. e\<noteq>e' \<longrightarrow> \<not> (e' e\<le> e)}"

text\<open>We now observe that the minimum of a non-empty set is not empty. Further, each element $a \in A$ has a lower bound in \<open>energy_Min\<close> $A$.\<close>

lemma energy_Min_not_empty:
  assumes "A \<noteq> {}" and "\<And>e. e\<in> A \<Longrightarrow>length e = n"
  shows "energy_Min A \<noteq> {}"
using assms proof(induction n arbitrary: A)
  case 0
  hence "{[]} = A" using assms by auto
  hence "[] \<in> energy_Min A" using energy_Min_def by auto
  then show ?case by auto
next
  case (Suc n)
  have "{butlast a |a. a \<in> A} \<noteq> {}" using Suc(2) by simp
  have "\<And>a. a \<in> {butlast a |a. a \<in> A} \<Longrightarrow> length a = n" using Suc(3) by auto
  hence "energy_Min {butlast a |a. a \<in> A} \<noteq> {}" using \<open>{butlast a |a. a \<in> A} \<noteq> {}\<close> Suc(1)
    by meson
  hence "\<exists>x. x\<in> energy_Min {butlast a |a. a \<in> A}" by auto
  from this obtain x where "x\<in> energy_Min {butlast a |a. a \<in> A}" by auto
  hence "x\<in> {butlast a |a. a \<in> A}" using energy_Min_def by auto
  hence "\<exists>a. a\<in> A \<and> x = butlast a" by auto
  from this obtain a where "a\<in> A \<and> x = butlast a" by auto

  have "last a \<in> {x. (butlast a)@[x] \<in> A} "
    by (metis Suc.prems(2) Zero_neq_Suc \<open>a \<in> A \<and> x = butlast a\<close> append_butlast_last_id list.size(3) mem_Collect_eq) 
  hence "{x. (butlast a)@[x] \<in> A} \<noteq> {}" by auto
  have "\<exists>B. finite B \<and> B\<subseteq> {x. (butlast a)@[x] \<in> A} \<and> Inf {x. (butlast a)@[x] \<in> A} = Min B"
  proof(cases "Inf {x. butlast a @ [x] \<in> A} = \<infinity>")
    case True
    hence "\<infinity> \<in> {x. (butlast a)@[x] \<in> A}" using \<open>{x. (butlast a)@[x] \<in> A} \<noteq> {}\<close>
      by (metis \<open>last a \<in> {x. butlast a @ [x] \<in> A}\<close> wellorder_InfI)
    hence "finite {\<infinity>} \<and> {\<infinity>} \<subseteq>{x. (butlast a)@[x] \<in> A} \<and>Inf {x. (butlast a)@[x] \<in> A} = Min {\<infinity>}"
      by (simp add: True) 
    then show ?thesis by blast
  next
    case False
    hence "\<exists>m. (enat m) \<in> {x. butlast a @ [x] \<in> A}"
      by (metis Inf_top_conv(2) Succ_def \<open>a \<in> A \<and> x = butlast a\<close> not_infinity_eq top_enat_def) 
    from this obtain m where "(enat m) \<in> {x. butlast a @ [x] \<in> A}" by auto
    hence finite: "finite {x. (butlast a)@[x] \<in> A \<and> x\<le> enat m}"
      by (metis (no_types, lifting) finite_enat_bounded mem_Collect_eq) 
    have subset: "{x. (butlast a)@[x] \<in> A \<and> x\<le> enat m} \<subseteq> {x. (butlast a)@[x] \<in> A}" by (simp add: Collect_mono)
    have "Inf {x. (butlast a)@[x] \<in> A} = Inf {x. (butlast a)@[x] \<in> A \<and> x\<le> enat m}" using \<open>(enat m) \<in> {x. butlast a @ [x] \<in> A}\<close>
      by (smt (verit) Inf_lower mem_Collect_eq nle_le wellorder_InfI)
    hence "Inf {x. (butlast a)@[x] \<in> A} = Min {x. (butlast a)@[x] \<in> A \<and> x\<le> enat m}" using \<open>(enat m) \<in> {x. butlast a @ [x] \<in> A}\<close>
      using finite
      by (smt (verit, best) False Inf_enat_def Min_Inf) 
    hence "finite {x. (butlast a)@[x] \<in> A \<and> x\<le> enat m} \<and> {x. (butlast a)@[x] \<in> A \<and> x\<le> enat m} \<subseteq> {x. (butlast a)@[x] \<in> A} \<and> Inf {x. (butlast a)@[x] \<in> A} = Min {x. (butlast a)@[x] \<in> A \<and> x\<le> enat m}"
      using finite subset by simp
    then show ?thesis by blast
  qed
  from this obtain B where B: "finite B \<and> B\<subseteq> {x. (butlast a)@[x] \<in> A} \<and> Inf {x. (butlast a)@[x] \<in> A} = Min B" by auto
  hence "((butlast a)@[Min B])\<in> A"
    by (metis \<open>last a \<in> {x. butlast a @ [x] \<in> A}\<close> mem_Collect_eq wellorder_InfI) 

  have "\<forall>b \<in> A. ((butlast a)@[Min B])\<noteq>b \<longrightarrow> \<not> (energy_leq b ((butlast a)@[Min B]))" 
  proof
    fix b 
    assume "b\<in> A"
    have "energy_leq b (butlast a @ [Min B]) \<Longrightarrow> butlast a @ [Min B] = b" 
    proof-
      assume "energy_leq b (butlast a @ [Min B])"
      have "energy_leq (butlast b) (butlast a)" 
        unfolding energy_leq_def proof
        show "length (butlast b) = length (butlast a)"
          using \<open>\<And>a. a \<in> {butlast a |a. a \<in> A} \<Longrightarrow> length a = n\<close> \<open>a \<in> A \<and> x = butlast a\<close> \<open>b \<in> A\<close> mem_Collect_eq by blast
        show "\<forall>i<length (butlast b). butlast b ! i \<le> butlast a ! i" 
        proof
          fix i 
          show "i < length (butlast b) \<longrightarrow> butlast b ! i \<le> butlast a ! i "
          proof 
            assume " i < length (butlast b)"
            hence "i <length b"
              by (simp add: Suc.prems(2) \<open>b \<in> A\<close>) 
            hence B: "b ! i \<le> (butlast a @ [Min B]) !i" using \<open>energy_leq b (butlast a @ [Min B])\<close> energy_leq_def by auto

            have "butlast b ! i = b! i" using \<open>i < length (butlast b)\<close> nth_butlast by auto
            have "butlast a ! i = (butlast a @ [Min B]) !i "
              by (metis \<open>i < length (butlast b)\<close> \<open>length (butlast b) = length (butlast a)\<close> butlast_snoc nth_butlast)
            thus "butlast b ! i \<le> butlast a ! i " using B \<open>butlast b ! i = b! i\<close> by auto
          qed
        qed
      qed 
      hence "butlast b = butlast a" using \<open>x\<in> energy_Min {butlast a |a. a \<in> A}\<close> \<open>a\<in> A \<and> x = butlast a\<close>  energy_Min_def \<open>b\<in> A\<close> by auto
      hence "(butlast a)@[last b] \<in> A" using Suc(3)
        by (metis \<open>b \<in> A\<close> append_butlast_last_id list.size(3) nat.discI) 
      hence "Min B \<le> last b"
        by (metis (no_types, lifting) B Inf_lower mem_Collect_eq) 

      have "last b \<le>  Min B" using \<open>energy_leq b (butlast a @ [Min B])\<close> energy_leq_def
        by (metis (no_types, lifting) \<open>butlast b = butlast a\<close> append_butlast_last_id butlast.simps(1) dual_order.refl impossible_Cons length_Cons length_append_singleton lessI nth_append_length) 
      hence "last b =  Min B" using \<open>Min B \<le> last b\<close> by simp
      thus "butlast a @ [Min B] = b" using \<open>butlast b = butlast a\<close> Suc(3)
        by (metis Zero_not_Suc \<open>b \<in> A\<close> append_butlast_last_id list.size(3))
    qed
    thus "butlast a @ [Min B] \<noteq> b \<longrightarrow> \<not> energy_leq b (butlast a @ [Min B])"
      by auto
  qed
  hence "((butlast a)@[Min B]) \<in> energy_Min A" using energy_Min_def \<open>((butlast a)@[Min B])\<in> A\<close>
    by simp
  thus ?case by auto
qed

lemma energy_Min_contains_smaller:
  assumes "a \<in> A"
  shows "\<exists>b \<in> energy_Min A. b e\<le> a"
proof-
  define set where "set \<equiv> {e. e \<in> A \<and> e e\<le> a}"
  hence "a \<in> set"
    by (simp add: assms(1) energy_leq.refl) 
  hence "set \<noteq> {}" by auto
  have "\<And>s. s\<in> set \<Longrightarrow>length s =  length a" using energy_leq_def set_def
    by simp 
  hence "energy_Min set \<noteq> {}" using \<open>set \<noteq> {}\<close> energy_Min_not_empty by simp
  hence "\<exists>b. b \<in> energy_Min set" by auto
  from this obtain b where "b \<in> energy_Min set" by auto
  hence "\<And>b'. b'\<in> A \<Longrightarrow> b' \<noteq> b \<Longrightarrow> \<not> (b' e\<le> b)"
  proof-
    fix b'
    assume "b' \<in> A"
    assume "b' \<noteq> b"
    show "\<not> (b' e\<le> b)"
    proof
      assume "(b' e\<le> b)"
      hence "b' e\<le> a" using \<open>b \<in> energy_Min set\<close> energy_Min_def
        by (simp add: energy_leq.trans local.set_def) 
      hence "b' \<in> set" using \<open>b' \<in> A\<close> set_def by simp
      thus "False" using \<open>b \<in> energy_Min set\<close> energy_Min_def \<open>b' e\<le> b\<close> \<open>b' \<noteq> b\<close> by auto 
    qed
  qed
  hence "b\<in> energy_Min A" using energy_Min_def
    using \<open>b \<in> energy_Min set\<close> local.set_def by auto 
  thus ?thesis using \<open>b \<in> energy_Min set\<close> energy_Min_def set_def by auto
qed

text\<open>We now establish how the minimum relates to subsets.\<close>

lemma energy_Min_subset:
  assumes "A \<subseteq> B" 
  shows "A \<inter> (energy_Min B) \<subseteq> energy_Min A" and
        "energy_Min B \<subseteq> A \<Longrightarrow> energy_Min B = energy_Min A"
proof-
  show "A \<inter> energy_Min B \<subseteq> energy_Min A"
  proof
    fix e 
    assume "e \<in> A \<inter> energy_Min B"
    hence "\<exists>a \<in> energy_Min A. a e\<le> e" using assms energy_Min_contains_smaller by blast
    from this obtain a where "a \<in> energy_Min A" and " a e\<le> e" by auto
    hence "a = e" using \<open>e \<in> A \<inter> energy_Min B\<close> unfolding energy_Min_def
      using assms by auto 
    thus "e \<in> energy_Min A" using \<open>a \<in> energy_Min A\<close> by simp
  qed
  assume "energy_Min B \<subseteq> A"
  hence "energy_Min B \<subseteq> energy_Min A" using \<open>A \<inter> energy_Min B \<subseteq> energy_Min A\<close> by auto
  have "energy_Min A \<subseteq> energy_Min B"
  proof
    fix a
    assume "a \<in> energy_Min A"
    hence "a \<in> B" unfolding energy_Min_def using assms by blast
    hence "\<exists>b \<in> energy_Min B. b e\<le> a" using assms energy_Min_contains_smaller by blast
    from this obtain b where "b \<in> energy_Min B" and "b e\<le> a" by auto
    hence "a = b" using \<open>energy_Min B \<subseteq> A\<close> energy_Min_def
      using \<open>a \<in> energy_Min A\<close> by auto 
    thus "a \<in> energy_Min B"
      using \<open>b \<in> energy_Min B\<close> by simp
  qed
  thus "energy_Min B = energy_Min A" using \<open>energy_Min B \<subseteq> energy_Min A\<close> by simp
qed

text\<open>We now show that by well-foundedness the minimum is a finite set. For the proof we first generalise \<open>enumerate\<close>.\<close>

fun enumerate_arbitrary :: "'a set \<Rightarrow> nat \<Rightarrow> 'a"  where
  "enumerate_arbitrary A 0 = (SOME a. a \<in> A)" |
  "enumerate_arbitrary A (Suc n) 
    = enumerate_arbitrary (A - {enumerate_arbitrary A 0}) n"

lemma enumerate_arbitrary_in: 
  shows "infinite A \<Longrightarrow> enumerate_arbitrary A i \<in> A"
proof(induct i arbitrary: A)
  case 0
  then show ?case using enumerate_arbitrary.simps finite.simps some_in_eq by auto 
next
  case (Suc i)
  hence "infinite (A - {enumerate_arbitrary A 0})" using infinite_remove by simp
  hence "Energy_Order.enumerate_arbitrary (A - {enumerate_arbitrary A 0}) i \<in> (A - {enumerate_arbitrary A 0})" using Suc.hyps by blast
  hence "enumerate_arbitrary A (Suc i) \<in> (A - {enumerate_arbitrary A 0})" using enumerate_arbitrary.simps by simp
  then show ?case by auto
qed

lemma enumerate_arbitrary_neq:
  shows "infinite A \<Longrightarrow> i < j 
        \<Longrightarrow> enumerate_arbitrary A i \<noteq> enumerate_arbitrary A j"
proof(induct i arbitrary: j A)
  case 0
  then show ?case using enumerate_arbitrary.simps
    by (metis Diff_empty Diff_iff enumerate_arbitrary_in finite_Diff_insert gr0_implies_Suc insert_iff)
next
  case (Suc i)
  hence "\<exists>j'. j = Suc j'"
    by (simp add: not0_implies_Suc) 
  from this obtain j' where "j = Suc j'" by auto
  hence "i < j'" using Suc by simp
  from Suc have "infinite (A - {enumerate_arbitrary A 0})" using infinite_remove by simp
  hence "enumerate_arbitrary (A - {enumerate_arbitrary A 0}) i \<noteq> enumerate_arbitrary (A - {enumerate_arbitrary A 0}) j'" using Suc \<open>i < j'\<close>
    by force
  then show ?case using enumerate_arbitrary.simps
    by (simp add: \<open>j = Suc j'\<close>) 
qed

lemma energy_Min_finite:
  assumes "\<And>e. e\<in> A \<Longrightarrow> length e = n"
  shows "finite (energy_Min A)"
proof-
  have "wqo_on energy_leq (energy_Min A)" using energy_leq_wqo assms 
    by (smt (verit, del_insts) Collect_mono_iff energy_Min_def wqo_on_subset) 
  hence wqoMin: "(\<forall>f \<in> SEQ (energy_Min A). (\<exists>i j. i < j \<and> energy_leq (f i) (f j)))" unfolding wqo_on_def almost_full_on_def good_def by simp
  have "\<not> finite (energy_Min A) \<Longrightarrow> False" 
  proof-
    assume "\<not> finite (energy_Min A)"
    hence "infinite (energy_Min A)"
      by simp

    define f where "f \<equiv> enumerate_arbitrary (energy_Min A)"
    have fneq: "\<And>i j. f i \<in> energy_Min A \<and> (j \<noteq> i \<longrightarrow> f j \<noteq> f i)"
    proof
      fix i j 
      show "f i \<in> energy_Min A" unfolding f_def using enumerate_arbitrary_in \<open>infinite (energy_Min A)\<close> by auto 
      show "j \<noteq> i \<longrightarrow> f j \<noteq> f i" proof
        assume "j \<noteq> i"
        show "f j \<noteq> f i" proof(cases "j < i")
          case True
          then show ?thesis unfolding f_def using enumerate_arbitrary_neq \<open>infinite (energy_Min A)\<close> by auto 
        next
          case False
          hence "i < j" using \<open>j \<noteq> i\<close> by auto
          then show ?thesis unfolding f_def using enumerate_arbitrary_neq \<open>infinite (energy_Min A)\<close>
            by metis 
        qed
      qed
    qed
    hence "\<exists>i j. i < j \<and> energy_leq (f i) (f j)" using wqoMin SEQ_def by simp
    thus "False" using energy_Min_def fneq by force
  qed
  thus ?thesis by auto
qed

text\<open>\subsection*{Supremum}\<close>

definition energy_sup :: "nat \<Rightarrow> energy set \<Rightarrow> energy" where 
"energy_sup n A = map (\<lambda>i. Sup {(e!i)|e. e \<in> A}) [0..<n]" 

text\<open>We now show that we indeed defined a supremum, i.e.\ a least upper bound, when considering a fixed dimension \<open>n\<close>.\<close>

lemma energy_sup_is_sup: 
  shows energy_sup_in: "\<And>a. a \<in> A \<Longrightarrow> length a = n \<Longrightarrow> a e\<le> (energy_sup n A)" and
        energy_sup_leq: "\<And>s. (\<And>a. a\<in> A \<Longrightarrow>a e\<le> s) \<Longrightarrow> length s = n 
                        \<Longrightarrow> (energy_sup n A) e\<le> s"
proof-
  fix a
  assume A1: "a \<in> A" and A2: "length a = n"
  show "a e\<le> (energy_sup n A)"
    unfolding energy_leq_def energy_sup_def 
  proof
    show "length a = length (map (\<lambda>i. Sup {(v!i)|v. v \<in> A}) [0..<n])" using A2
      by simp 
    show "\<forall>i<length a. a ! i \<le> map (\<lambda>i. Sup {(v!i)|v. v \<in> A}) [0..<n] ! i " 
    proof 
      fix i 
      show "i < length a \<longrightarrow> a ! i \<le> map (\<lambda>i. Sup {(v!i)|v. v \<in> A}) [0..<n] ! i "
      proof 
        assume "i < length a"
        thus "a ! i \<le> map (\<lambda>i. Sup {(v!i)|v. v \<in> A}) [0..<n] ! i " using A1 A2
        by (smt (verit, del_insts) Sup_upper diff_add_inverse length_upt mem_Collect_eq minus_nat.diff_0 nth_map nth_upt)
      qed
    qed
  qed
next
  fix x 
  assume A1: "\<And>a. a\<in> A \<Longrightarrow>a e\<le> x" and A2: "length x = n"
  show "(energy_sup n A) e\<le> x"
    unfolding energy_leq_def
  proof
    show L: "length (energy_sup n A) = length x" using A2 energy_sup_def by simp
    show "\<forall>i<length (energy_sup n A). energy_sup n A ! i \<le> x ! i " 
    proof
      fix i 
      show "i < length (energy_sup n A) \<longrightarrow> energy_sup n A ! i \<le> x ! i "
      proof
        assume "i < length (energy_sup n A)"
        hence "i < length [0..<n]" using L A2 by simp
        from A1 have "\<And>a. a\<in>{v ! i |v. v \<in> A} \<Longrightarrow> a \<le> x ! i"
        proof-
          fix a 
          assume "a\<in>{v ! i |v. v \<in> A} "
          hence "\<exists>v\<in>A. a = v ! i" by auto
          from this obtain v where "v\<in> A" and "a=v !i" by auto
          thus " a \<le> x ! i" using A1 energy_leq_def L \<open>i < length (energy_sup n A)\<close> by simp
        qed

        have "(energy_sup n A) ! i = (map (\<lambda>i. Sup {(v!i)|v. v \<in> A}) [0..<n] ! i) " using energy_sup_def by auto
        also have "... = (\<lambda>i. Sup {(v!i)|v. v \<in> A}) ([0..<n] ! i)" using nth_map \<open>i < length [0..<n]\<close>
          by auto
        also have "... = Sup {v ! i |v. v \<in> A}"
          using \<open>i < length [0..<n]\<close> by auto 
        also have "...\<le> (x ! i) " using \<open>\<And>a. a\<in>{v ! i |v. v \<in> A} \<Longrightarrow> a \<le> x ! i\<close>
          by (meson Sup_least)
        finally show "energy_sup n A ! i \<le> x ! i " .
      qed
    qed
  qed
qed

text\<open>We now observe a version of monotonicity. Afterwards we show that the supremum of the empty set is the zero-vector.\<close>

lemma energy_sup_leq_energy_sup:
  assumes "A \<noteq> {}" and "\<And>a. a\<in> A \<Longrightarrow> \<exists>b\<in> B. energy_leq a b" and 
          "\<And>a. a\<in> A \<Longrightarrow> length a = n"
  shows "energy_leq (energy_sup n A) (energy_sup n B)"
proof-
  have len: "length (energy_sup n B) = n" using energy_sup_def by simp
  have "\<And>a. a\<in> A \<Longrightarrow> energy_leq a (energy_sup n B)" 
  proof-
    fix a
    assume "a\<in> A"
    hence "\<exists>b\<in> B. energy_leq a b" using assms by simp
    from this obtain b where "b \<in> B" and "energy_leq a b" by auto
    hence "energy_leq b (energy_sup n B)" using energy_sup_in energy_leq_def
      by (simp add: \<open>a \<in> A\<close> assms(3))
    thus "energy_leq a (energy_sup n B)" using \<open>energy_leq a b\<close> energy_leq.trans by blast
  qed
  thus ?thesis using len energy_sup_leq by blast
qed

lemma empty_Sup_is_zero:
  assumes "i < n"
  shows "(energy_sup n {}) ! i = 0"
proof-
  have "(energy_sup n {}) ! i = (map (\<lambda>i. Sup {(v!i)|v. v \<in> {}}) [0..<n]) ! i"
    using energy_sup_def by auto
  also have "... = (\<lambda>i. Sup {(v!i)|v. v \<in> {}}) ([0..<n] ! i)" using nth_map assms by simp
  finally show "(energy_sup n {}) ! i = 0"
    by (simp add: bot_enat_def)
qed

end