theory IsaFoR_Ground_Critical_Pairs
  imports 
    First_Order_Terms.Term_More
    IsaFoR_Ground_Context
begin

(* TODO: Create generalized version that works with ground and nonground terms *)
text\<open>Adapted from First_Order_Rewriting.Critical_Pairs\<close>

(* TODO: *)
no_notation Term_Context.position_par (infixl \<open>\<bottom>\<close> 67)

type_synonym 'f ground_rewrite_system = "'f gterm rel"

interpretation ground_term_rewrite_system where
  hole = \<box> and apply_context = apply_ground_context and compose_context = "(\<circ>\<^sub>c)"
  by unfold_locales

(* TODO: notation + names! *)
lemma gsubt_at_hole [simp]: "gsubt_at c\<langle>t\<rangle>\<^sub>G (hole_pos c) = t"
  by (induction c) auto

lemma hole_pos_gposs [intro]: "hole_pos c \<in> gposs c\<langle>t\<rangle>\<^sub>G"
  by (induction c) auto

fun
  ctxt_of_pos_gterm :: "pos \<Rightarrow> 'f gterm \<Rightarrow> 'f ground_context"
  where
    "ctxt_of_pos_gterm [] t = \<box>" |
    "ctxt_of_pos_gterm (i # ps) (GFun f ts) =
    More f (take i ts) (ctxt_of_pos_gterm ps (ts!i)) (drop (Suc i) ts)"

text\<open>Behaves differently than replace_gterm_at!\<close>
abbreviation (input) "greplace_at t p s \<equiv> (ctxt_of_pos_gterm p t)\<langle>s\<rangle>\<^sub>G"

lemma greplace_at_hole [simp]: "greplace_at c\<langle>t\<rangle>\<^sub>G (hole_pos c) t' = c\<langle>t'\<rangle>\<^sub>G"
  by (induction c) auto

lemma gctxt_gsupt_id: 
  assumes "p \<in> gposs t"  
  shows "(ctxt_of_pos_gterm p t)\<langle>gsubt_at t p\<rangle>\<^sub>G = t"
  using assms 
  by (induction t arbitrary: p) (auto simp: id_take_nth_drop[symmetric])
  
(* TODO: Clean up file *)
lemma parallel_gposs_greplace_at:
  assumes parallel: "p1 \<bottom> p2" and p1: "p1 \<in> gposs t"
  shows "(p2 \<in> gposs (ctxt_of_pos_gterm p1 t)\<langle>t'\<rangle>\<^sub>G) = (p2 \<in> gposs t)"
proof -
  from parallel_remove_prefix[OF parallel]
  obtain p i j q1 q2 where 
    p1_id: "p1 = p @ i # q1" and 
    p2_id: "p2 = p @ j # q2" and
    ij: "i \<noteq> j" 
    by blast

  from p1 show ?thesis unfolding p1_id p2_id
  proof (induct p arbitrary: t)
    case (Cons k p)

    from Cons(2) obtain f ts where t: "t = GFun f ts" and k: "k < length ts" 
      by (cases t, auto)

    note Cons = Cons[unfolded t]

    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"

    from Cons(2) have "?p1 \<in> gposs (ts ! k)" 
      by auto
   
    from Cons(1)[OF this]
    have rec: "(?p2 \<in> gposs (greplace_at (ts ! k) ?p1 t')) = (?p2 \<in> gposs (ts ! k))" .

    from k have min: "min (length ts) k = k" 
      by simp

    show ?case unfolding t using rec min k
      by (auto simp: nth_append)
  next
    case Nil
    then obtain f ts where t: "t = GFun f ts" and i: "i < length ts" 
      by (cases t, auto)

    let ?p1 = "i # q1"
    let ?s1 = "greplace_at (ts ! i) q1 t'"

    have "greplace_at t ?p1 t' = GFun f (ts[i := ?s1])"
      unfolding t upd_conv_take_nth_drop[OF i] 
      by simp

    then show ?case 
      unfolding t
      using ij
      by auto
  qed
qed

lemma parallel_greplace_at_gsubt_at: 
  assumes parallel: "p1 \<bottom> p2" and p1: "p1 \<in> gposs t" and p2: "p2 \<in> gposs t"
  shows "gsubt_at (ctxt_of_pos_gterm p1 t)\<langle>t'\<rangle>\<^sub>G p2 = gsubt_at t p2"
proof -
  from parallel_remove_prefix[OF parallel]

  obtain p i j q1 q2 where p1_id: "p1 = p @ i # q1" and p2_id: "p2 = p @ j # q2"
    and ij: "i \<noteq> j" by blast

  from p1 p2 show ?thesis unfolding p1_id p2_id
  proof (induct p arbitrary: t)
    case (Cons k p)

    from Cons(3) obtain f ts where 
      t: "t = GFun f ts" and k: "k < length ts" 
      by (cases t, auto)
    
    note Cons = Cons[unfolded t]
    
    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"
    
    from Cons(2) Cons(3) have "?p1 \<in> gposs (ts ! k)" "?p2 \<in> gposs (ts ! k)" 
      by auto

    from Cons(1)[OF this] 
    have rec: "gsubt_at (greplace_at (ts ! k) ?p1 t') ?p2 = gsubt_at (ts ! k) ?p2" .

    from k have min: "min (length ts) k = k" 
      by simp

    show ?case unfolding t using rec min k
      by (simp add: nth_append)
  next
    case Nil
    from Nil(2) obtain f ts where 
      t: "t = GFun f ts" and j: "j < length ts"
      by (cases t, auto)
    
    note Nil = Nil[unfolded t]
    
    from Nil have i: "i < length ts" 
      by auto

    let ?p1 = "i # q1"
    let ?p2 = "j # q2"

    let ?s1 = "greplace_at (ts ! i) q1 t'"
    let ?ts1 = "ts[i := ?s1]"

    from j have j': "j < length ?ts1"
      by simp

    have "gsubt_at (greplace_at t ?p1 t') ?p2 = gsubt_at (GFun f ?ts1) ?p2" 
      unfolding t upd_conv_take_nth_drop[OF i] 
      by simp

    also have "... = gsubt_at (ts ! j) q2" using ij 
      by simp

    finally show ?case unfolding t 
      by simp
  qed
qed

lemma parallel_greplace_at:
  fixes p1 :: pos
  assumes parallel: "p1 \<bottom> p2"
    and p1: "p1 \<in> gposs t"
    and p2: "p2 \<in> gposs t"
  shows "greplace_at (greplace_at t p1 s1) p2 s2 = greplace_at (greplace_at t p2 s2) p1 s1"
proof -
  from parallel_remove_prefix[OF parallel]
  obtain p i j q1 q2 where 
    p1_id: "p1 = p @ i # q1" and p2_id: "p2 = p @ j # q2" and ij: "i \<noteq> j"
    by blast

  from p1 p2 show ?thesis unfolding p1_id p2_id
  proof (induct p arbitrary: t)
    case (Cons k p)
    from Cons(3) obtain f ts where 
      t: "t = GFun f ts" and k: "k < length ts" 
      by (cases t, auto)

    note Cons = Cons[unfolded t]

    let ?p1 = "p @ i # q1" let ?p2 = "p @ j # q2"

    from Cons(2) Cons(3) have "?p1 \<in> gposs (ts ! k)" "?p2 \<in> gposs (ts ! k)"
      by auto

    from Cons(1)[OF this]
    have rec: "greplace_at (greplace_at (ts ! k) ?p1 s1) ?p2 s2 =
               greplace_at (greplace_at (ts ! k) ?p2 s2) ?p1 s1" .

    from k have min: "min (length ts) k = k" 
      by simp

    show ?case 
      unfolding t
      using rec min k
      by (simp add: nth_append)
  next
    case Nil

    from Nil(2) obtain f ts where 
      t: "t = GFun f ts" and j: "j < length ts"
      by (cases t, auto)

    note Nil = Nil[unfolded t]

    from Nil have i: "i < length ts" 
      by auto

    let ?p1 = "i # q1"
    let ?p2 = "j # q2"
    let ?s1 = "greplace_at (ts ! i) q1 s1"
    let ?s2 = "greplace_at (ts ! j) q2 s2"
    let ?ts1 = "ts[i := ?s1]"
    let ?ts2 = "ts[j := ?s2]"

    from j have j': "j < length ?ts1" 
      by simp

    from i have i': "i < length ?ts2" 
      by simp

    have "greplace_at (greplace_at t ?p1 s1) ?p2 s2 = greplace_at (GFun f ?ts1) ?p2 s2" 
      unfolding t upd_conv_take_nth_drop[OF i] 
      by simp

    also have "... = GFun f (?ts1[j := ?s2])"
      unfolding upd_conv_take_nth_drop[OF j'] 
      using ij 
      by simp

    also have "... = GFun f (?ts2[i := ?s1])"
      using list_update_swap[OF ij]
      by simp

    also have "... = greplace_at (GFun f ?ts2) ?p1 s1"
      unfolding upd_conv_take_nth_drop[OF i'] 
      using ij 
      by simp

    also have "... = greplace_at (greplace_at t ?p2 s2) ?p1 s1" 
      unfolding t upd_conv_take_nth_drop[OF j] 
      by simp

    finally show ?case by simp
  qed
qed

lemma parallel_rewrite_in_context:
  fixes p1 :: pos
  assumes p12: "p1 \<bottom> p2"
    and p1: "p1 \<in> gposs t"
    and p2: "p2 \<in> gposs t"
    and step2: "gsubt_at t p2 = l2" "(l2,r2) \<in> R" 
  shows "(greplace_at t p1 v, greplace_at (greplace_at t p1 v) p2 r2) \<in> rewrite_in_context R" 
    (is "(?one,?two) \<in> _")
proof -

  let ?c = "(ctxt_of_pos_gterm p2 (ctxt_of_pos_gterm p1 t)\<langle>v\<rangle>\<^sub>G)"

  show ?thesis
    unfolding rewrite_in_context_def mem_Collect_eq
  proof (intro exI conjI)

    show "(?one, ?two) = (?c\<langle>l2\<rangle>\<^sub>G, ?c\<langle>r2\<rangle>\<^sub>G)"
      using gctxt_gsupt_id parallel_gposs_greplace_at parallel_greplace_at_gsubt_at
      by (metis p1 p12 p2 step2(1))
  next

    show "(l2, r2) \<in> R"
      using step2(2) .
  qed
qed

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

            (* TODO: names! *)
            have l2: "gsubt_at c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G ?p\<^sub>2 = l\<^sub>2"
              unfolding c\<^sub>1 id
              by simp

            have p12: "?p\<^sub>1 \<bottom> ?p\<^sub>2" 
              using False 
              by simp

            have p1: "?p\<^sub>1 \<in> gposs c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G" 
              unfolding c\<^sub>1
              by auto

            have p2: "?p\<^sub>2 \<in> gposs c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G"
              unfolding c\<^sub>1 id
              by auto

            let ?one = "greplace_at c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G ?p\<^sub>1 r\<^sub>1"

            have one: "c\<^sub>1\<langle>r\<^sub>1\<rangle>\<^sub>G = ?one"
              unfolding c\<^sub>1
              by simp

            have "(?one, greplace_at ?one ?p\<^sub>2 r\<^sub>2) \<in> rewrite_in_context R"
              using parallel_rewrite_in_context[OF p12 p1 p2 l2 l\<^sub>2_r\<^sub>2]
              by auto

            then have one: "(c\<^sub>1\<langle>r\<^sub>1\<rangle>\<^sub>G, greplace_at ?one ?p\<^sub>2 r\<^sub>2) \<in> (rewrite_in_context R)\<^sup>*"
              unfolding one
              by simp

            have l1: "gsubt_at c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G ?p\<^sub>1 = l\<^sub>1" 
              unfolding c\<^sub>2  id[symmetric]
              by simp

            have p21: "?p\<^sub>2  \<bottom> ?p\<^sub>1" using False 
              by simp

            have p1': "?p\<^sub>1 \<in> gposs (c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G)" 
              unfolding c\<^sub>2 id[symmetric]
              by auto

            have p2': "?p\<^sub>2 \<in> gposs (c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G)" 
              unfolding c\<^sub>2 
              by auto

            let ?two = "greplace_at (c\<^sub>2\<langle>l\<^sub>2\<rangle>\<^sub>G) ?p\<^sub>2 r\<^sub>2"

            have two: "c\<^sub>2\<langle>r\<^sub>2\<rangle>\<^sub>G = ?two"
              unfolding c\<^sub>2 
              by simp

            from parallel_rewrite_in_context[OF p21 p2' p1' l1 l\<^sub>1_r\<^sub>1, of "r\<^sub>2"]
            have "(?two, greplace_at ?two ?p\<^sub>1 r\<^sub>1) \<in> rewrite_in_context R" 
              by auto

            then have two: "(c\<^sub>2\<langle>r\<^sub>2\<rangle>\<^sub>G, greplace_at ?two ?p\<^sub>1 r\<^sub>1) \<in> (rewrite_in_context R)\<^sup>*" 
              unfolding two 
              by simp

            have "greplace_at ?one ?p\<^sub>2 r\<^sub>2 = greplace_at (greplace_at (c\<^sub>1\<langle>l\<^sub>1\<rangle>\<^sub>G) ?p\<^sub>2 r\<^sub>2) ?p\<^sub>1 r\<^sub>1"
              by (rule parallel_greplace_at [OF p12 p1 p2])

            also have "... = greplace_at ?two ?p\<^sub>1 r\<^sub>1" 
              unfolding c\<^sub>1 c\<^sub>2 id ..

            finally have one_two: "greplace_at ?one ?p\<^sub>2 r\<^sub>2 = greplace_at ?two ?p\<^sub>1 r\<^sub>1" .

            show ?thesis
              unfolding less
              by (rule disjI1, insert one one_two two, auto)
          qed
        qed
      qed
    qed
  qed
qed

end
