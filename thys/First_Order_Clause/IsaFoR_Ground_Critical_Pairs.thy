theory IsaFoR_Ground_Critical_Pairs
  imports 
    Parallel_Induct
    IsaFoR_Ground_Context
    Ground_Critical_Peaks
begin

(* TODO: Create generalized version that works with ground and nonground terms *)
text\<open>Adapted from First\_Order\_Rewriting.Critical\_Pairs\<close>

type_synonym 'f ground_rewrite_system = "'f gterm rel"

interpretation ground_term_rewrite_system where
  hole = \<box> and apply_context = apply_ground_context and compose_context = "(\<circ>\<^sub>c)"
  by unfold_locales

lemma parallel_rewrite_in_context:
  assumes 
    parallel: "p\<^sub>1 \<bottom> p\<^sub>2" and
    p\<^sub>1_in_t: "p\<^sub>1 \<in> positions\<^sub>G t" and
    p\<^sub>2_in_t: "p\<^sub>2 \<in> positions\<^sub>G t" and
    l\<^sub>2: "l\<^sub>2 = t !\<^sub>t\<^sub>G p\<^sub>2" and
    l\<^sub>2_r\<^sub>2: "(l\<^sub>2, r\<^sub>2) \<in> R" 
  shows "(t\<lbrakk>p\<^sub>1 := v\<rbrakk>, t\<lbrakk>p\<^sub>1 := v\<rbrakk>\<lbrakk>p\<^sub>2 := r\<^sub>2\<rbrakk>) \<in> rewrite_in_context R" (is "(?t\<^sub>1,?t\<^sub>2) \<in> _")
proof (unfold rewrite_in_context_def mem_Collect_eq, intro exI conjI)
  let ?c = "t\<lbrakk>p\<^sub>1 := v\<rbrakk> !\<^sub>c p\<^sub>2"

  show "(?t\<^sub>1, ?t\<^sub>2) = (?c\<langle>l\<^sub>2\<rangle>\<^sub>G, ?c\<langle>r\<^sub>2\<rangle>\<^sub>G)"
    unfolding l\<^sub>2 parallel_replace_at\<^sub>G[OF parallel p\<^sub>1_in_t p\<^sub>2_in_t] gsubt_at_id[OF p\<^sub>2_in_t] ..  
qed (rule l\<^sub>2_r\<^sub>2)

interpretation ground_critical_peaks where
  hole = \<box> and 
  apply_context = apply_ground_context and 
  compose_context = actxt_compose
proof unfold_locales
  fix R :: "'f ground_rewrite_system" and t u s
  assume 
    t_u: "(t, u) \<in> rewrite_in_context R" and
    t_s: "(t, s) \<in> rewrite_in_context R"

  show "(s, u) \<in> join (rewrite_in_context R) \<or>
    (\<exists>c l m r. s = c\<langle>l\<rangle>\<^sub>G \<and> t = c\<langle>m\<rangle>\<^sub>G \<and> u = c\<langle>r\<rangle>\<^sub>G \<and> 
    ((l, m, r) \<in> ground_critical_peaks R \<or> (r, m, l) \<in> ground_critical_peaks R))"
  proof - 
    let ?R = "rewrite_in_context R"
    let ?CP = "ground_critical_peaks R"

    from t_u obtain c\<^sub>1 l\<^sub>1 r\<^sub>1 where
      l\<^sub>1_r\<^sub>1: "(l\<^sub>1, r\<^sub>1) \<in> R" and 
      t1: "t = c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G" and 
      u: "u = c\<^sub>1\<langle>r\<^sub>1\<rangle>\<^sub>G"
      unfolding rewrite_in_context_def
      by auto

    from t_s obtain c\<^sub>2 l\<^sub>2 r\<^sub>2 where 
      l\<^sub>2_r\<^sub>2: "(l\<^sub>2, r\<^sub>2) \<in> R" and 
      t2: "t = c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G" and 
      s: "s = c\<^sub>2\<langle>r\<^sub>2\<rangle>\<^sub>G"
      unfolding rewrite_in_context_def
      by auto

    define n where "n = size c\<^sub>1 + size c\<^sub>2"

    from t1 t2 u s n_def show ?thesis
    proof (induct n arbitrary: c\<^sub>1 c\<^sub>2 s t u rule: less_induct)
      case (less n c\<^sub>1 c\<^sub>2 s t u)

      show ?case
      proof (cases c\<^sub>1)
        case Hole

        show ?thesis
          using l\<^sub>1_r\<^sub>1 l\<^sub>2_r\<^sub>2 less.prems
          unfolding ground_critical_peaks_def mem_Collect_eq
          by (metis Hole intp_actxt.simps(1))        
      next
        case c\<^sub>1: (More f\<^sub>1 ss\<^sub>1 c\<^sub>1' ts\<^sub>1)

        show ?thesis
        proof (cases c\<^sub>2)
          case Hole

          show ?thesis
            using l\<^sub>1_r\<^sub>1 l\<^sub>2_r\<^sub>2 less.prems
            unfolding ground_critical_peaks_def mem_Collect_eq
            by (metis Hole intp_actxt.simps(1))    
        next
          case c\<^sub>2: (More f\<^sub>2 ss\<^sub>2 c\<^sub>2' ts\<^sub>2)

          from less(2-3) c\<^sub>1 c\<^sub>2
          have id: "(More f\<^sub>1 ss\<^sub>1 c\<^sub>1' ts\<^sub>1)\<langle>l\<^sub>1\<rangle>\<^sub>G = (More f\<^sub>2 ss\<^sub>2 c\<^sub>2' ts\<^sub>2)\<langle>l\<^sub>2\<rangle>\<^sub>G"
            by auto

          let ?n\<^sub>1 = "length ss\<^sub>1"
          let ?n\<^sub>2 = "length ss\<^sub>2"

          from id have f: "f\<^sub>1 = f\<^sub>2" 
            by simp

          show ?thesis
          proof (cases "?n\<^sub>1 = ?n\<^sub>2")
            case True

            with id have 
              ss: "ss\<^sub>1 = ss\<^sub>2" and 
              ts: "ts\<^sub>1 = ts\<^sub>2" and
              c': "c\<^sub>1'\<langle>l\<^sub>1\<rangle>\<^sub>G = c\<^sub>2'\<langle>l\<^sub>2\<rangle>\<^sub>G" 
              by auto

            let ?c = "More f\<^sub>2 ss\<^sub>2 \<box> ts\<^sub>2"

            have c\<^sub>1_eq: "c\<^sub>1 = ?c \<circ>\<^sub>c c\<^sub>1'" 
              unfolding c\<^sub>1 f ss ts 
              by simp

            have c\<^sub>2_eq: "c\<^sub>2 = ?c \<circ>\<^sub>c c\<^sub>2'" 
              unfolding c\<^sub>2 f ss ts  
              by simp

            define m where
              "m = size c\<^sub>1' + size c\<^sub>2'"

            have m_less_n: "m < n" 
              unfolding less m_def c\<^sub>1 c\<^sub>2 
              by auto

            note IH = less(1)[OF m_less_n refl c' refl refl m_def]

            then show ?thesis
            proof (elim disjE)
              assume "(c\<^sub>2'\<langle>r\<^sub>2\<rangle>\<^sub>G, c\<^sub>1'\<langle>r\<^sub>1\<rangle>\<^sub>G) \<in> ?R\<^sup>\<down>"

              then obtain s' where 
                c\<^sub>1'_s': "(c\<^sub>1'\<langle>r\<^sub>1\<rangle>\<^sub>G, s') \<in> ?R\<^sup>*" and
                c\<^sub>2'_s': "(c\<^sub>2'\<langle>r\<^sub>2\<rangle>\<^sub>G, s') \<in> ?R\<^sup>*"
                by auto

              have "(c\<^sub>1\<langle>r\<^sub>1\<rangle>\<^sub>G, ?c\<langle>s'\<rangle>\<^sub>G) \<in> ?R\<^sup>*" 
                using c\<^sub>1'_s' 
                unfolding c\<^sub>1_eq intp_actxt_compose
                by blast

              moreover have "(c\<^sub>2\<langle>r\<^sub>2\<rangle>\<^sub>G, ?c\<langle>s'\<rangle>\<^sub>G) \<in> ?R\<^sup>*" 
                using c\<^sub>2'_s' 
                unfolding c\<^sub>2_eq intp_actxt_compose
                by blast

              ultimately show ?thesis 
                using less 
                by auto
            next
              assume 
                "\<exists>c l m r.
                c\<^sub>2'\<langle>r\<^sub>2\<rangle>\<^sub>G = c\<langle>l\<rangle>\<^sub>G \<and>
                c\<^sub>1'\<langle>l\<^sub>1\<rangle>\<^sub>G = c\<langle>m\<rangle>\<^sub>G \<and>
                c\<^sub>1'\<langle>r\<^sub>1\<rangle>\<^sub>G = c\<langle>r\<rangle>\<^sub>G \<and>
                ((l, m, r) \<in> ?CP \<or> (r, m, l) \<in> ?CP)"

              then show ?thesis
                by (metis c\<^sub>1_eq c\<^sub>2_eq intp_actxt_compose less.prems(1,3,4))
            qed
          next
            case False

            let ?p\<^sub>1 = "?n\<^sub>1 # hole_pos c\<^sub>1'"
            let ?p\<^sub>2 = "?n\<^sub>2 # hole_pos c\<^sub>2'"

            let ?one = "c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>"
            let ?two = "c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>"

            have parallel_p\<^sub>1_p\<^sub>2: "?p\<^sub>1 \<bottom> ?p\<^sub>2" 
              using False
              by simp

            have p\<^sub>1: "?p\<^sub>1 \<in> positions\<^sub>G c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G"
              unfolding c\<^sub>1
              by auto

            have p\<^sub>2: "?p\<^sub>2 \<in> positions\<^sub>G c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G"
              unfolding c\<^sub>1 id
              by auto

            have "(?one, ?one\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>) \<in> rewrite_in_context R" 
            proof(rule parallel_rewrite_in_context[OF parallel_p\<^sub>1_p\<^sub>2 p\<^sub>1 p\<^sub>2 _ l\<^sub>2_r\<^sub>2])

              show "l\<^sub>2 = c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G !\<^sub>t\<^sub>G ?p\<^sub>2"
                unfolding c\<^sub>1 id
                by simp
            qed

            then have "(c\<^sub>1\<langle>r\<^sub>1\<rangle>\<^sub>G, ?one\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>) \<in> (rewrite_in_context R)\<^sup>*"
              unfolding c\<^sub>1
              by simp

            moreover have "(?two, ?two\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>) \<in> rewrite_in_context R" 
            proof (rule parallel_rewrite_in_context[OF parallel_pos_sym[OF parallel_p\<^sub>1_p\<^sub>2]])

              show "?p\<^sub>1 \<in> positions\<^sub>G c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G"
                unfolding c\<^sub>2 id[symmetric]
                by auto
            next

              show "?p\<^sub>2 \<in> positions\<^sub>G c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G"
                unfolding c\<^sub>2
                by auto
            next

              show "l\<^sub>1 = c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G !\<^sub>t\<^sub>G ?p\<^sub>1"
                unfolding c\<^sub>2 id[symmetric]
                by simp
            next

              show "(l\<^sub>1, r\<^sub>1) \<in> R"
                using l\<^sub>1_r\<^sub>1 .
            qed

            then have "(c\<^sub>2\<langle>r\<^sub>2\<rangle>\<^sub>G, ?two\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>) \<in> (rewrite_in_context R)\<^sup>*" 
              unfolding c\<^sub>2 
              by simp

            moreover have "?one\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk> = (c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G\<lbrakk>?p\<^sub>2 := r\<^sub>2\<rbrakk>\<lbrakk>?p\<^sub>1 := r\<^sub>1\<rbrakk>)"
              by (rule parallel_replace_at\<^sub>G[OF parallel_p\<^sub>1_p\<^sub>2 p\<^sub>1 p\<^sub>2])

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
qed

end
