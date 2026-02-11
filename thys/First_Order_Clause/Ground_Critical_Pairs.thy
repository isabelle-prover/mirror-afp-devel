theory Ground_Critical_Pairs
  imports 
    Generic_Term_Context
    Ground_Term_Rewrite_System
    Parallel_Rewrite
begin

(* TODO: Create generalized version that works with ground and nonground terms *)
text\<open>Adapted from First\_Order\_Rewriting.Critical\_Pairs\<close>

context ground_term_rewrite_system
begin

definition ground_critical_pairs :: "'t rel \<Rightarrow> 't rel" where
  "ground_critical_pairs R = {(c\<langle>r\<^sub>2\<rangle>, r\<^sub>1) | c l r\<^sub>1 r\<^sub>2. (c\<langle>l\<rangle>, r\<^sub>1) \<in> R \<and> (l, r\<^sub>2) \<in> R}"

abbreviation ground_critical_pair_theorem where
  "ground_critical_pair_theorem R \<equiv> 
    WCR (rewrite_in_context R) \<longleftrightarrow> ground_critical_pairs R \<subseteq> (rewrite_in_context R)\<^sup>\<down>"

lemma ground_critical_pairs_fork:
  fixes R :: "'t rel"
  assumes ground_critical_pairs: "(l, r) \<in> ground_critical_pairs R"
  shows "(r, l) \<in> (rewrite_in_context R)\<inverse> O rewrite_in_context R"
proof -

  obtain c t t' where "l = c\<langle>t'\<rangle>" and "(c\<langle>t\<rangle>, r) \<in> R" and "(t, t') \<in> R" 
    using ground_critical_pairs
    unfolding ground_critical_pairs_def
    by auto

  have "(r, c\<langle>t\<rangle>) \<in> (rewrite_in_context R)\<inverse>"
    using \<open>(c\<langle>t\<rangle>, r) \<in> R\<close> subset_rewrite_in_context 
    by blast

  moreover have "(c\<langle>t\<rangle>, l) \<in> rewrite_in_context R"
    using \<open>(t, t') \<in> R\<close> \<open>l = c\<langle>t'\<rangle>\<close> rewrite_in_context_def
    by fast

  ultimately show ?thesis
    by auto
qed

lemma ground_critical_pairs_complete:
  fixes R :: "'t rel"
  assumes 
    ground_critical_pairs: "(l, r) \<in> ground_critical_pairs R" and
    no_join: "(l, r) \<notin> (rewrite_in_context R)\<^sup>\<down>"
  shows "\<not> WCR (rewrite_in_context R)"
  using ground_critical_pairs_fork[OF ground_critical_pairs] no_join
  by auto

definition ground_critical_peaks ::"'t rel \<Rightarrow> ('t \<times> 't \<times> 't) set" where
  "ground_critical_peaks R = { (c\<langle>r'\<rangle>, c\<langle>l\<rangle>, r) | l r r' c. (c\<langle>l\<rangle>, r) \<in> R \<and> (l, r') \<in> R }"

lemma ground_critical_peak_to_pair: 
  assumes "(l, m, r) \<in> ground_critical_peaks R" 
  shows "(l, r) \<in> ground_critical_pairs R" 
  using assms 
  unfolding ground_critical_peaks_def ground_critical_pairs_def 
  by blast

end

locale ground_critical_pairs =
  term_context_interpretation where More = More and is_var = "\<lambda>_. False" +
  parallel_rewrite where Fun = Fun
for        
  More :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 'c \<Rightarrow> 't list \<Rightarrow> 'c"
begin

lemma ground_critical_peaks_main: 
  fixes R :: "'t rel" and  t u s :: 't
  assumes t_u: "(t, u) \<in> rewrite_in_context R" and t_s: "(t, s) \<in> rewrite_in_context R"
  shows 
    "(s, u) \<in> join (rewrite_in_context R) \<or>
      (\<exists>c l m r. s = c\<langle>l\<rangle> \<and> t = c\<langle>m\<rangle> \<and> u = c\<langle>r\<rangle> \<and>
        ((l, m, r) \<in> ground_critical_peaks R \<or> (r, m, l) \<in> ground_critical_peaks R))"
proof -

  let ?R = "rewrite_in_context R"
  let ?CP = "ground_critical_peaks R"

  from t_u obtain c\<^sub>1 l\<^sub>1 r\<^sub>1 where
    l\<^sub>1_r\<^sub>1: "(l\<^sub>1, r\<^sub>1) \<in> R" and 
    t1: "t = c\<^sub>1\<langle>l\<^sub>1\<rangle>" and 
    u: "u = c\<^sub>1\<langle>r\<^sub>1\<rangle>"
    unfolding rewrite_in_context_def
    by auto

  from t_s obtain c\<^sub>2 l\<^sub>2 r\<^sub>2 where 
    l\<^sub>2_r\<^sub>2: "(l\<^sub>2, r\<^sub>2) \<in> R" and 
    t2: "t = c\<^sub>2\<langle>l\<^sub>2\<rangle>" and 
    s: "s = c\<^sub>2\<langle>r\<^sub>2\<rangle>"
    unfolding rewrite_in_context_def
    by auto

  define n where "n = size\<^sub>c c\<^sub>1 + size\<^sub>c c\<^sub>2"

  from t1 t2 u s n_def show ?thesis
  proof (induct n arbitrary: c\<^sub>1 c\<^sub>2 s t u rule: less_induct)
    case (less n c\<^sub>1 c\<^sub>2 s t u)

    show ?case
    proof (cases "c\<^sub>1 = \<box>")
      case Hole: True

      show ?thesis
        using l\<^sub>1_r\<^sub>1 l\<^sub>2_r\<^sub>2 less.prems
        unfolding ground_critical_peaks_def mem_Collect_eq
        by (metis Hole apply_hole)
    next
      case c\<^sub>1_not_hole: False

      then obtain f\<^sub>1 e\<^sub>1 ss\<^sub>1 c\<^sub>1' ts\<^sub>1 where c\<^sub>1: "c\<^sub>1 = More f\<^sub>1 e\<^sub>1 ss\<^sub>1 c\<^sub>1' ts\<^sub>1"
        using context_destruct
        by auto

      show ?thesis
      proof (cases "c\<^sub>2 = \<box>")
        case Hole: True

        show ?thesis
          using l\<^sub>1_r\<^sub>1 l\<^sub>2_r\<^sub>2 less.prems
          unfolding ground_critical_peaks_def mem_Collect_eq
          by (metis Hole apply_hole)
      next
        case c\<^sub>2_not_hole: False

        then obtain f\<^sub>2 e\<^sub>2 ss\<^sub>2 c\<^sub>2' ts\<^sub>2 where c\<^sub>2: "c\<^sub>2 = More f\<^sub>2 e\<^sub>2 ss\<^sub>2 c\<^sub>2' ts\<^sub>2"
          using context_destruct
          by auto

        from less(2-3) c\<^sub>1 c\<^sub>2
        have id: "(More f\<^sub>1 e\<^sub>1 ss\<^sub>1 c\<^sub>1' ts\<^sub>1)\<langle>l\<^sub>1\<rangle> = (More f\<^sub>2 e\<^sub>2 ss\<^sub>2 c\<^sub>2' ts\<^sub>2)\<langle>l\<^sub>2\<rangle>"
          by auto

        then have
          f: "f\<^sub>1 = f\<^sub>2" and
          e: "e\<^sub>1 = e\<^sub>2"
          using term_inject
          by auto

        let ?n\<^sub>1 = "length ss\<^sub>1"
        let ?n\<^sub>2 = "length ss\<^sub>2"

        show ?thesis
        proof (cases "?n\<^sub>1 = ?n\<^sub>2")
          case True

          with id have 
            ss: "ss\<^sub>1 = ss\<^sub>2" and 
            ts: "ts\<^sub>1 = ts\<^sub>2" and
            c': "c\<^sub>1'\<langle>l\<^sub>1\<rangle> = c\<^sub>2'\<langle>l\<^sub>2\<rangle>"
            using term_inject
            by fastforce+

          let ?c = "More f\<^sub>2 e\<^sub>2 ss\<^sub>2 \<box> ts\<^sub>2"

          have c\<^sub>1_eq: "c\<^sub>1 = ?c \<circ>\<^sub>c c\<^sub>1'" 
            unfolding c\<^sub>1 f e ss ts
            by simp

          have c\<^sub>2_eq: "c\<^sub>2 = ?c \<circ>\<^sub>c c\<^sub>2'" 
            unfolding c\<^sub>2 f ss ts  
            by simp

          define m where
            "m = size\<^sub>c c\<^sub>1' + size\<^sub>c c\<^sub>2'"

          have m_less_n: "m < n" 
            unfolding less m_def c\<^sub>1 c\<^sub>2
            using subcontext_smaller interpretation_not_hole
            by (metis add_less_mono subcontext)

          note IH = less(1)[OF m_less_n refl c' refl refl m_def]

          then show ?thesis
          proof (elim disjE)
            assume "(c\<^sub>2'\<langle>r\<^sub>2\<rangle>, c\<^sub>1'\<langle>r\<^sub>1\<rangle>) \<in> ?R\<^sup>\<down>"

            then obtain s' where 
              c\<^sub>1'_s': "(c\<^sub>1'\<langle>r\<^sub>1\<rangle>, s') \<in> ?R\<^sup>*" and
              c\<^sub>2'_s': "(c\<^sub>2'\<langle>r\<^sub>2\<rangle>, s') \<in> ?R\<^sup>*"
              by auto

            have "(c\<^sub>1\<langle>r\<^sub>1\<rangle>, ?c\<langle>s'\<rangle>) \<in> ?R\<^sup>*" 
              using c\<^sub>1'_s' 
              unfolding c\<^sub>1_eq compose_context_iff
              by blast

            moreover have "(c\<^sub>2\<langle>r\<^sub>2\<rangle>, ?c\<langle>s'\<rangle>) \<in> ?R\<^sup>*" 
              using c\<^sub>2'_s' 
              unfolding c\<^sub>2_eq compose_context_iff
              by blast

            ultimately show ?thesis 
              using less 
              by auto
          next
            assume 
              "\<exists>c l m r.
                c\<^sub>2'\<langle>r\<^sub>2\<rangle> = c\<langle>l\<rangle> \<and>
                c\<^sub>1'\<langle>l\<^sub>1\<rangle> = c\<langle>m\<rangle> \<and>
                c\<^sub>1'\<langle>r\<^sub>1\<rangle> = c\<langle>r\<rangle> \<and>
                ((l, m, r) \<in> ?CP \<or> (r, m, l) \<in> ?CP)"

            then show ?thesis
              by (metis c\<^sub>1_eq c\<^sub>2_eq compose_context_iff less.prems(1,3,4))
          qed
        next
          case False

          let ?p\<^sub>1 = "?n\<^sub>1 # hole_position c\<^sub>1'"
          let ?p\<^sub>2 = "?n\<^sub>2 # hole_position c\<^sub>2'"

          let ?one = "c\<^sub>1\<langle>l\<^sub>1\<rangle>\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>"
          let ?two = "c\<^sub>2\<langle>l\<^sub>2\<rangle>\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>"

          have parallel_p\<^sub>1_p\<^sub>2: "?p\<^sub>1 \<bottom> ?p\<^sub>2" 
            using False
            by auto

          have p\<^sub>1: "?p\<^sub>1 \<in> positions c\<^sub>1\<langle>l\<^sub>1\<rangle>"
            unfolding c\<^sub>1
            by auto

          have p\<^sub>2: "?p\<^sub>2 \<in> positions c\<^sub>1\<langle>l\<^sub>1\<rangle>"
            unfolding c\<^sub>1 id
            by auto

          have "(?one, ?one\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>) \<in> rewrite_in_context R" 
          proof(rule parallel_rewrite_in_context[OF parallel_p\<^sub>1_p\<^sub>2 p\<^sub>1 p\<^sub>2 _ l\<^sub>2_r\<^sub>2])

            show "l\<^sub>2 = c\<^sub>1\<langle>l\<^sub>1\<rangle> !\<^sub>t ?p\<^sub>2"
              unfolding c\<^sub>1 id
              by simp
          qed

          then have "(c\<^sub>1\<langle>r\<^sub>1\<rangle>, ?one\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>) \<in> (rewrite_in_context R)\<^sup>*"
            unfolding c\<^sub>1
            by simp

          moreover have "(?two, ?two\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>) \<in> rewrite_in_context R" 
          proof (rule parallel_rewrite_in_context[OF parallel_pos_sym[OF parallel_p\<^sub>1_p\<^sub>2]])

            show "?p\<^sub>1 \<in> positions c\<^sub>2\<langle>l\<^sub>2\<rangle>"
              unfolding c\<^sub>2 id[symmetric]
              by auto
          next

            show "?p\<^sub>2 \<in> positions c\<^sub>2\<langle>l\<^sub>2\<rangle>"
              unfolding c\<^sub>2
              by auto
          next

            show "l\<^sub>1 = c\<^sub>2\<langle>l\<^sub>2\<rangle> !\<^sub>t ?p\<^sub>1"
              unfolding c\<^sub>2 id[symmetric]
              by simp
          next

            show "(l\<^sub>1, r\<^sub>1) \<in> R"
              using l\<^sub>1_r\<^sub>1 .
          qed

          then have "(c\<^sub>2\<langle>r\<^sub>2\<rangle>, ?two\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>) \<in> (rewrite_in_context R)\<^sup>*" 
            unfolding c\<^sub>2 
            by simp

          moreover have "?one\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk> = (c\<^sub>1\<langle>l\<^sub>1\<rangle>\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>)"
            by (rule parallel_replace_at[OF parallel_p\<^sub>1_p\<^sub>2 p\<^sub>1 p\<^sub>2])

          then have "?one\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk> = ?two\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>" 
            unfolding c\<^sub>1 c\<^sub>2 id .

          ultimately show ?thesis
            unfolding less
            by (intro disjI1) auto
        qed
      qed
    qed
  qed
qed

lemma ground_critical_pairs_main: 
  assumes "(s, t\<^sub>1) \<in> rewrite_in_context R" "(s, t\<^sub>2) \<in> rewrite_in_context R"
  shows
    "(t\<^sub>1, t\<^sub>2) \<in> (rewrite_in_context R)\<^sup>\<down> \<or>
       (\<exists>c l r. t\<^sub>1 = c\<langle>l\<rangle> \<and> t\<^sub>2 = c\<langle>r\<rangle> \<and>
         ((l, r) \<in> ground_critical_pairs R \<or> (r, l) \<in> ground_critical_pairs R))"
  using assms ground_critical_peaks_main ground_critical_peak_to_pair
  by metis

lemma ground_critical_pairs:
  assumes ground_critical_pairs:
    "\<And>l r. (l, r) \<in> ground_critical_pairs R \<Longrightarrow> l \<noteq> r \<Longrightarrow>
      \<exists>s. (l, s) \<in> (rewrite_in_context R)\<^sup>* \<and> (r, s) \<in> (rewrite_in_context R)\<^sup>*"
  shows "WCR (rewrite_in_context R)"
proof (intro WCR_onI)

  let ?R = "rewrite_in_context R"
  let ?CP = "ground_critical_pairs R"

  fix s t\<^sub>1 t\<^sub>2

  assume steps: "(s, t\<^sub>1) \<in> ?R" "(s, t\<^sub>2) \<in> ?R"

  let ?p = "\<lambda>s'. (t\<^sub>1, s') \<in> ?R\<^sup>* \<and> (t\<^sub>2, s') \<in> ?R\<^sup>*"

  from ground_critical_pairs_main [OF steps]
  have "\<exists>s'. ?p s'"
    using ground_critical_pairs rewrite_in_context_trancl_add_context
    by (metis joinE rtrancl.rtrancl_refl)
 
  then show "(t\<^sub>1, t\<^sub>2) \<in> ?R\<^sup>\<down>"
    by auto
qed

theorem ground_critical_pair_theorem: "ground_critical_pair_theorem R" (is "?l = ?r")
proof (rule iffI)
  assume ?l

  with ground_critical_pairs_complete show ?r 
    by auto
next
  assume ?r

  with ground_critical_pairs show ?l
    by auto
qed

end

end
