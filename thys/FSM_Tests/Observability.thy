section \<open>Observability\<close>

text \<open>This theory presents the classical algorithm for transforming FSMs into 
      language-equivalent observable FSMs in analogy to the determinisation of nondeterministic
      finite automata.\<close>


theory Observability
imports FSM 
begin

lemma fPow_Pow : "Pow (fset A) = fset (fset |`| fPow A)" 
proof (induction A)
  case empty
  then show ?case by auto
next
  case (insert x A)

  have "Pow (fset (finsert x A)) = Pow (fset A) \<union> (insert x) ` Pow (fset A)"
    by (simp add: Pow_insert) 
  moreover have "fset (fset |`| fPow (finsert x A)) = fset (fset |`| fPow A) \<union> (insert x) ` fset (fset |`| fPow A)"
  proof -
    have "fset |`| ((fPow A) |\<union>| (finsert x) |`| (fPow A)) = (fset |`| fPow A) |\<union>| (insert x) |`| (fset |`| fPow A)"
      unfolding fimage_funion
      by fastforce
    moreover have "(fPow (finsert x A)) = (fPow A) |\<union>| (finsert x) |`| (fPow A)"
      by (simp add: fPow_finsert)
    ultimately show ?thesis
      by auto 
  qed
  ultimately show ?case 
    using insert.IH by simp
qed

lemma fcard_fsubset: "\<not> fcard (A |-| (B |\<union>| C)) < fcard (A |-| B) \<Longrightarrow> C |\<subseteq>| A \<Longrightarrow> C |\<subseteq>| B"
proof (induction C)
  case empty
  then show ?case by auto
next
  case (insert x C)
  then show ?case
    unfolding  finsert_fsubset funion_finsert_right not_less 
  proof -
    assume a1: "fcard (A |-| B) \<le> fcard (A |-| finsert x (B |\<union>| C))"
    assume "\<lbrakk>fcard (A |-| B) \<le> fcard (A |-| (B |\<union>| C)); C |\<subseteq>| A\<rbrakk> \<Longrightarrow> C |\<subseteq>| B"
    assume a2: "x |\<in>| A \<and> C |\<subseteq>| A"
    have "A |-| (C |\<union>| finsert x B) = A |-| B \<or> \<not> A |-| (C |\<union>| finsert x B) |\<subseteq>| A |-| B"
      using a1 by (metis (no_types) fcard_seteq funion_commute funion_finsert_right)
    then show "x |\<in>| B \<and> C |\<subseteq>| B"
      using a2 by blast
  qed 
qed


lemma make_observable_transitions_qtrans_helper:
  assumes  "qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) A;
                                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                       in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)) nexts)"
shows "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| A \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
proof -
  have "fset qtrans = { (q,x,y,q') | q x y q' . q |\<in>| nexts \<and> q' \<noteq> {||} \<and> fset q' = t_target ` {t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y}}"
  proof -
    have "\<And> q . fset (ffilter (\<lambda>t . t_source t |\<in>| q) A) = Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A)"
      using ffilter.rep_eq assms(1) by auto
    then have "\<And> q . fset (fimage (\<lambda> t . (t_input t, t_output t)) (ffilter (\<lambda>t . t_source t |\<in>| q) A)) = image (\<lambda> t . (t_input t, t_output t)) (Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A))"
      by simp
    then have *:"\<And> q . fset (fimage (\<lambda>(x,y) . (q,x,y, (t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))))) (fimage (\<lambda> t . (t_input t, t_output t)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A)))) 
                  = image (\<lambda>(x,y) . (q,x,y, (t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))))) (image (\<lambda> t . (t_input t, t_output t)) (Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A)))"
      by (metis (no_types, lifting) ffilter.rep_eq fset.set_map)
    
    have **: "\<And> f1 f2 xs ys ys' . (\<And> x . fset (f1 x ys) = (f2 x ys')) \<Longrightarrow> 
          fset (ffUnion (fimage (\<lambda> x . (f1 x ys)) xs)) = (\<Union> x \<in> fset xs . (f2 x ys'))"
      unfolding ffUnion.rep_eq fimage.rep_eq by force


    have "fset (ffUnion (fimage (\<lambda> q . (fimage (\<lambda>(x,y) . (q,x,y, (t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))))) (fimage (\<lambda> t . (t_input t, t_output t)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))) nexts)) 
              = (\<Union> q \<in> fset nexts . image (\<lambda>(x,y) . (q,x,y, (t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))))) (image (\<lambda> t . (t_input t, t_output t)) (Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A))))"
      unfolding ffUnion.rep_eq fimage.rep_eq
      using "*" by force

    also have "\<dots> = { (q,x,y,q') | q x y q' . q |\<in>| nexts \<and> q' \<noteq> {||} \<and> fset q' = t_target ` {t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y}}"
    (is "?A = ?B") proof -
      have "\<And> t . t \<in> ?A \<Longrightarrow> t \<in> ?B"
      proof -
        fix t assume "t \<in> ?A"
        then obtain q where "q \<in> fset nexts"
                      and   "t \<in> image (\<lambda>(x,y) . (q,x,y, (t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))))) (image (\<lambda> t . (t_input t, t_output t)) (Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A)))"
          by blast
        then obtain x y q' where *: "(x,y) \<in> (image (\<lambda> t . (t_input t, t_output t)) (Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A)))"
                           and      "t = (q,x,y,q')"
                           and   **:"q' = (t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A)))))"
          by force

        
        have "q |\<in>| nexts" 
          using \<open>q \<in> fset nexts\<close>
          by simp 
        moreover have "q' \<noteq> {||}"
        proof -
          have ***:"(Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A)) = fset (ffilter (\<lambda>t . t_source t |\<in>| q) (A))"
            by auto
          have "\<exists> t . t |\<in>| (ffilter (\<lambda>t. t_source t |\<in>| q) A) \<and> (t_input t, t_output t) = (x,y)"
            using *
            by (metis (no_types, lifting) "***" image_iff) 
          then show ?thesis unfolding **
            by force 
        qed
        moreover have "fset q' = t_target ` {t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y}"
        proof -
          have "{t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y} = ((Set.filter (\<lambda>t . (t_input t, t_output t) = (x,y)) (fset (ffilter (\<lambda>t . t_source t |\<in>| q) (A)))))"
             by fastforce
          also have "\<dots> = fset ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))"
            by fastforce
          finally have "{t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y} = fset ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))" .
          then show ?thesis
            unfolding **
            by simp  
        qed
        ultimately show "t \<in> ?B"
          unfolding \<open>t = (q,x,y,q')\<close> 
          by blast
      qed
      moreover have "\<And> t . t \<in> ?B \<Longrightarrow> t \<in> ?A" 
      proof -
        fix t assume "t \<in> ?B"
        then obtain q x y q' where "t = (q,x,y,q')" and "(q,x,y,q') \<in> ?B" by force
        then have "q |\<in>| nexts" 
             and  "q' \<noteq> {||}" 
             and  *: "fset q' = t_target ` {t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y}"
          by force+
        then have "fset q' \<noteq> {}"
          by (metis bot_fset.rep_eq fset_inject)

        have "(x,y) \<in> (image (\<lambda> t . (t_input t, t_output t)) (Set.filter (\<lambda>t . t_source t |\<in>| q) (fset A)))"
          using \<open>fset q' \<noteq> {}\<close> unfolding * Set.filter_def by blast
        moreover have "q' = t_target |`| ffilter (\<lambda>t. (t_input t, t_output t) = (x, y)) (ffilter (\<lambda>t. t_source t |\<in>| q) A)"
        proof -
          have "{t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y} = ((Set.filter (\<lambda>t . (t_input t, t_output t) = (x,y)) (fset (ffilter (\<lambda>t . t_source t |\<in>| q) (A)))))"
            by fastforce
          also have "\<dots> = fset ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))"
            by fastforce
          finally have ***:"{t' . t' |\<in>| A \<and> t_source t' |\<in>| q \<and> t_input t' = x \<and> t_output t' = y} = fset ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) (ffilter (\<lambda>t . t_source t |\<in>| q) (A))))" .
          
          show ?thesis
            using * 
            unfolding ***
            by (metis (no_types, lifting) fimage.rep_eq fset_inject)
        qed 
        ultimately show "t \<in> ?A"
          using \<open>q |\<in>| nexts\<close>
          unfolding \<open>t = (q,x,y,q')\<close> 
          by force
      qed
      ultimately show ?thesis
        by (metis (no_types, lifting) Collect_cong Sup_set_def mem_Collect_eq) 
    qed
    finally show ?thesis 
      unfolding assms Let_def by blast
  qed
  then show "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| A \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
    by force
qed




function make_observable_transitions :: "('a,'b,'c) transition fset \<Rightarrow> 'a fset fset \<Rightarrow> 'a fset fset \<Rightarrow> ('a fset \<times> 'b \<times> 'c \<times> 'a fset) fset \<Rightarrow> ('a fset \<times> 'b \<times> 'c \<times> 'a fset) fset" where
  "make_observable_transitions base_trans nexts dones ts = (let
            qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) base_trans;
                                         ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                     in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| (ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts))) ios)) nexts);
            dones' = dones |\<union>| nexts;
            ts' = ts |\<union>| qtrans;
            nexts' = (fimage t_target qtrans) |-| dones' 
          in if nexts' = {||}
            then ts'
            else make_observable_transitions base_trans nexts' dones' ts')"
  by auto
termination 
proof -
  {
    fix base_trans :: "('a,'b,'c) transition fset"
    fix nexts :: "'a fset fset" 
    fix dones :: "'a fset fset" 
    fix ts    :: "('a fset \<times> 'b \<times> 'c \<times> 'a fset) fset"
    fix q x y q'
  
    assume assm1: "\<not> fcard
             (fPow (t_source |`| base_trans |\<union>| t_target |`| base_trans) |-|
              (dones |\<union>| nexts |\<union>|
               t_target |`|
               ffUnion
                ((\<lambda>q. let qts = ffilter (\<lambda>t. t_source t |\<in>| q) base_trans
                       in ((\<lambda>(x, y). (q, x, y, t_target |`| ffilter (\<lambda>t. t_input t = x \<and> t_output t = y) qts)) \<circ> (\<lambda>t. (t_input t, t_output t))) |`|
                          qts) |`|
                 nexts)))
            < fcard (fPow (t_source |`| base_trans |\<union>| t_target |`| base_trans) |-| (dones |\<union>| nexts))"
  
    and assm2: "(q, x, y, q') |\<in>|
         ffUnion
          ((\<lambda>q. let qts = ffilter (\<lambda>t. t_source t |\<in>| q) base_trans
                 in ((\<lambda>(x, y). (q, x, y, t_target |`| ffilter (\<lambda>t. t_input t = x \<and> t_output t = y) qts)) \<circ> (\<lambda>t. (t_input t, t_output t))) |`| qts) |`|
           nexts)"
  
    and assm3: "q' |\<notin>| nexts"
  
  
  
    define qtrans where qtrans_def: "qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) base_trans;
                                             ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                         in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)) nexts)"
    
    have qtrans_prop: "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' | t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
      using make_observable_transitions_qtrans_helper[OF qtrans_def]
      by presburger
  
    have "\<And> t . t |\<in>| qtrans \<Longrightarrow> t_target t |\<in>| fPow (t_target |`| base_trans)"
    proof -
      fix t assume "t |\<in>| qtrans"
      then have *: "fset (t_target t) = t_target ` {t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
        using qtrans_prop by blast
      then have "fset (t_target t) \<subseteq> t_target ` (fset base_trans)"
        by (metis (mono_tags, lifting) imageI image_Collect_subsetI)
      then show "t_target t |\<in>| fPow (t_target |`| base_trans)"
        by (simp add: less_eq_fset.rep_eq) 
    qed
    then have "t_target |`| qtrans |\<subseteq>| (fPow (t_source |`| base_trans |\<union>| t_target |`| base_trans))"
      by fastforce
    moreover have " \<not> fcard (fPow (t_source |`| base_trans |\<union>| t_target |`| base_trans) |-| (dones |\<union>| nexts |\<union>| t_target |`| qtrans))
                  < fcard (fPow (t_source |`| base_trans |\<union>| t_target |`| base_trans) |-| (dones |\<union>| nexts))"
      using assm1 unfolding qtrans_def by force
    ultimately have "t_target |`| qtrans |\<subseteq>| dones |\<union>| nexts" 
      using fcard_fsubset by fastforce
    moreover have "q' |\<in>| t_target |`| qtrans"
      using assm2 unfolding qtrans_def by force
    ultimately have "q' |\<in>| dones"
      using \<open>q' |\<notin>| nexts\<close> by blast
  } note t = this

  show ?thesis
    apply (relation "measure (\<lambda> (base_trans, nexts, dones, ts) . fcard ((fPow (t_source |`| base_trans |\<union>| t_target |`| base_trans)) |-| (dones |\<union>| nexts)))")
    apply auto
    by (erule t)
qed





lemma make_observable_transitions_mono: "ts |\<subseteq>| (make_observable_transitions base_trans nexts dones ts)"
proof (induction rule: make_observable_transitions.induct[of "\<lambda> base_trans nexts dones ts . ts |\<subseteq>| (make_observable_transitions base_trans nexts dones ts)"])
  case (1 base_trans nexts dones ts)

  define qtrans where qtrans_def: "qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) base_trans;
                                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                       in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)) nexts)"
  
  have qtrans_prop: "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' | t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
    using make_observable_transitions_qtrans_helper[OF qtrans_def]
    by presburger

  let ?dones' = "dones |\<union>| nexts"
  let ?ts'    = "ts |\<union>| qtrans"
  let ?nexts' = "(fimage t_target qtrans) |-| ?dones'"

  have res_cases: "make_observable_transitions base_trans nexts dones ts = (if ?nexts' = {||} 
            then ?ts'
            else make_observable_transitions base_trans ?nexts' ?dones' ?ts')"
    unfolding make_observable_transitions.simps[of base_trans nexts dones ts] qtrans_def Let_def by simp

  show ?case proof (cases "?nexts' = {||}")
    case True
    then show ?thesis using res_cases by simp
  next
    case False
    then have "make_observable_transitions base_trans nexts dones ts = make_observable_transitions base_trans ?nexts' ?dones' ?ts'"
      using res_cases by simp
    moreover have "ts |\<union>| qtrans |\<subseteq>| make_observable_transitions base_trans ?nexts' ?dones' ?ts'"
      using "1"[OF qtrans_def _ _ _ False, of ?dones' ?ts'] by blast
    ultimately show ?thesis 
      by blast
  qed
qed



inductive pathlike :: "('state, 'input, 'output) transition fset \<Rightarrow> 'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> bool" 
  where
  nil[intro!] : "pathlike ts q []" |
  cons[intro!] : "t |\<in>| ts \<Longrightarrow> pathlike ts (t_target t) p \<Longrightarrow> pathlike ts (t_source t) (t#p)"

inductive_cases pathlike_nil_elim[elim!]: "pathlike ts q []"
inductive_cases pathlike_cons_elim[elim!]: "pathlike ts q (t#p)"



lemma make_observable_transitions_t_source :
  assumes "\<And> t . t |\<in>| ts \<Longrightarrow> t_source t |\<in>| dones \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
  and     "\<And> q t' . q |\<in>| dones \<Longrightarrow> t' |\<in>| base_trans \<Longrightarrow> t_source t' |\<in>| q \<Longrightarrow> \<exists> t . t |\<in>| ts \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t'"
  and     "t |\<in>| make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts"
  and     "t_source t |\<in>| dones"
shows "t |\<in>| ts"
using assms proof (induction base_trans "(fimage t_target ts) |-| dones" dones ts rule: make_observable_transitions.induct)
  case (1 base_trans dones ts)

  let ?nexts = "(fimage t_target ts) |-| dones"

  define qtrans where qtrans_def: "qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) base_trans;
                                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                       in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)) ?nexts)"
  
  have qtrans_prop: "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| ?nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
    using make_observable_transitions_qtrans_helper[OF qtrans_def]
    by presburger

  let ?dones' = "dones |\<union>| ?nexts"
  let ?ts'    = "ts |\<union>| qtrans"
  let ?nexts' = "(fimage t_target qtrans) |-| ?dones'"

  have res_cases: "make_observable_transitions base_trans ?nexts dones ts = (if ?nexts' = {||} 
            then ?ts'
            else make_observable_transitions base_trans ?nexts' ?dones' ?ts')"
    unfolding make_observable_transitions.simps[of base_trans ?nexts dones ts] qtrans_def Let_def by simp

  show ?case proof (cases "?nexts' = {||}")
    case True

    then have "make_observable_transitions base_trans ?nexts dones ts = ?ts'"
      using res_cases by auto
    then have "t |\<in>| ts |\<union>| qtrans"
      using \<open>t |\<in>| make_observable_transitions base_trans ?nexts dones ts\<close> \<open>t_source t |\<in>| dones\<close> by blast
    then show ?thesis 
      using qtrans_prop "1.prems"(3,4) by blast 
  next
    case False
    then have "make_observable_transitions base_trans ?nexts dones ts = make_observable_transitions base_trans ?nexts' ?dones' ?ts'"
      using res_cases by simp

    have i1: "(\<And>t. t |\<in>| ts |\<union>| qtrans \<Longrightarrow>
                t_source t |\<in>| dones |\<union>| ?nexts \<and>
                t_target t \<noteq> {||} \<and>
                fset (t_target t) =
                t_target `
                {t' . t' |\<in>| base_trans \<and>
                 t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t})"
      using "1.prems"(1) qtrans_prop by blast

    have i3: "t_target |`| qtrans |-| (dones |\<union>| ?nexts) = t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| ?nexts)"
      unfolding "1.prems"(3) by blast 
  
    have i2: "(\<And>q t'.
                  q |\<in>| dones |\<union>| ?nexts \<Longrightarrow>
                  t' |\<in>| base_trans \<Longrightarrow>
                  t_source t' |\<in>| q \<Longrightarrow>
                  \<exists>t. t |\<in>| ts |\<union>| qtrans \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t')"
    proof -
      fix q t' assume "q |\<in>| dones |\<union>| ?nexts"
               and    *:"t' |\<in>| base_trans"
               and    **:"t_source t' |\<in>| q"
  
      then consider (a) "q |\<in>| dones" | (b) "q |\<in>| ?nexts" by blast
      then show "\<exists>t. t |\<in>| ts |\<union>| qtrans \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t'" 
      proof cases
        case a
        then show ?thesis using * **
          using "1.prems"(2) by blast
      next
        case b
  
        let ?tgts = "{t'' . t'' |\<in>| base_trans \<and> t_source t'' |\<in>| q \<and> t_input t'' = t_input t' \<and> t_output t'' = t_output t'}"
        define tgts where tgts: "tgts = Abs_fset (t_target ` ?tgts)"
      
        have "?tgts \<subseteq> fset base_trans"
          by fastforce
        then have "finite (t_target ` ?tgts)"
          by (meson finite_fset finite_imageI finite_subset) 
        then have "fset tgts = (t_target ` ?tgts)"
          unfolding tgts 
          using Abs_fset_inverse
          by blast

        have "?tgts \<noteq> {}"
          using * ** by blast
        then have "t_target ` ?tgts \<noteq> {}"
          by blast
        then have "tgts \<noteq> {||}" 
          using \<open>fset tgts = (t_target ` ?tgts)\<close>
          by force 

        then have "(q, t_input t', t_output t', tgts) |\<in>| qtrans"
          using b 
          unfolding qtrans_prop[of "(q,t_input t',t_output t',tgts)"]
          unfolding fst_conv snd_conv 
          unfolding \<open>fset tgts = (t_target ` ?tgts)\<close>[symmetric]
          by blast
        then show ?thesis
          by auto
      qed
    qed


    have "t |\<in>| make_observable_transitions base_trans ?nexts dones ts \<Longrightarrow> t_source t |\<in>| dones |\<union>| ?nexts \<Longrightarrow> t |\<in>| ts |\<union>| qtrans"
      unfolding \<open>make_observable_transitions base_trans ?nexts dones ts = make_observable_transitions base_trans ?nexts' ?dones' ?ts'\<close>
      using "1.hyps"[OF qtrans_def _ _ _ _ i1 i2] False i3 by force
    then have "t |\<in>| ts |\<union>| qtrans"
      using \<open>t |\<in>| make_observable_transitions base_trans ?nexts dones ts\<close> \<open>t_source t |\<in>| dones\<close> by blast

    then show ?thesis 
      using qtrans_prop "1.prems"(3,4) by blast 
  qed
qed




  



lemma make_observable_transitions_path :
  assumes "\<And> t . t |\<in>| ts \<Longrightarrow> t_source t |\<in>| dones \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' \<in> transitions M . t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
  and     "\<And> q t' . q |\<in>| dones \<Longrightarrow> t' \<in> transitions M \<Longrightarrow> t_source t' |\<in>| q \<Longrightarrow> \<exists> t . t |\<in>| ts \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t'"
  and     "\<And> q . q |\<in>| (fimage t_target ts) |-| dones \<Longrightarrow> q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M)"
  and     "\<And> q . q |\<in>| dones \<Longrightarrow> q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M |\<union>| {|initial M|})"
  and     "{||} |\<notin>| dones"
  and     "q |\<in>| dones"
shows "(\<exists> q' p . q' |\<in>| q \<and> path M q' p \<and> p_io p = io) \<longleftrightarrow> (\<exists> p'. pathlike (make_observable_transitions (ftransitions M) ((fimage t_target ts) |-| dones) dones ts) q p' \<and> p_io p' = io)"

using assms proof (induction "ftransitions M" "(fimage t_target ts) |-| dones" dones ts  arbitrary: q io rule: make_observable_transitions.induct)
  case (1 dones ts q)

  let ?obs = "(make_observable_transitions (ftransitions M) ((fimage t_target ts) |-| dones) dones ts)"
  let ?nexts = "(fimage t_target ts) |-| dones"

  show ?case proof (cases io)
    case Nil

    have scheme: "\<And> q q' X . q' |\<in>| q \<Longrightarrow> q |\<in>| fPow X \<Longrightarrow> q' |\<in>| X"
      by (simp add: fsubsetD)

    obtain q' where "q' |\<in>| q" 
      using \<open>{||} |\<notin>| dones\<close> \<open>q |\<in>| dones\<close>
      by (metis all_not_in_conv bot_fset.rep_eq fset_cong) 
    have "q' |\<in>| t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M |\<union>| {|FSM.initial M|}"
      using scheme[OF \<open>q' |\<in>| q\<close> "1.prems"(4)[OF \<open>q |\<in>| dones\<close>]] .
    then have "q' \<in> states M"
      using ftransitions_source[of q' M]
      using ftransitions_target[of q' M]
      by force
    then have "\<exists> q' p . q' |\<in>| q \<and> path M q' p \<and> p_io p = io" 
      using \<open>q' |\<in>| q\<close> Nil by auto
    moreover have "(\<exists> p'. pathlike ?obs q p' \<and> p_io p' = io)"
      using Nil  by auto
    ultimately show ?thesis 
      by simp
  next
    case (Cons ioT ioP)

    define qtrans where qtrans_def: "qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) (ftransitions M);
                                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                       in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)) ?nexts)"
  
    have qtrans_prop: "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| ?nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| (ftransitions M) \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
      using make_observable_transitions_qtrans_helper[OF qtrans_def]
      by presburger


    let ?dones' = "dones |\<union>| ?nexts"
    let ?ts'    = "ts |\<union>| qtrans"
    let ?nexts' = "(fimage t_target qtrans) |-| ?dones'"
  
    have res_cases: "make_observable_transitions (ftransitions M) ?nexts dones ts = (if ?nexts' = {||} 
              then ?ts'
              else make_observable_transitions (ftransitions M) ?nexts' ?dones' ?ts')"
      unfolding make_observable_transitions.simps[of "ftransitions M" ?nexts dones ts] qtrans_def Let_def by simp


    have i1: "(\<And>t. t |\<in>| ts |\<union>| qtrans \<Longrightarrow>
                  t_source t |\<in>| dones |\<union>| ?nexts \<and>
                  t_target t \<noteq> {||} \<and>
                  fset (t_target t) =
                  t_target `
                  {t' \<in> FSM.transitions M .
                   t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t})"
      using "1.prems"(1) qtrans_prop
      using ftransitions_set[of M]
      by (metis (mono_tags, lifting) Collect_cong funion_iff) 

    have i2: "(\<And>q t'.
                q |\<in>| dones |\<union>| ?nexts \<Longrightarrow>
                t' \<in> FSM.transitions M \<Longrightarrow>
                t_source t' |\<in>| q \<Longrightarrow>
                \<exists>t. t |\<in>| ts |\<union>| qtrans \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t')"
    proof -
      fix q t' assume "q |\<in>| dones |\<union>| ?nexts"
               and    *:"t' \<in> FSM.transitions M"
               and    **:"t_source t' |\<in>| q"
  
      then consider (a) "q |\<in>| dones" | (b) "q |\<in>| ?nexts" by blast
      then show "\<exists>t. t |\<in>| ts |\<union>| qtrans \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t'" 
      proof cases
        case a
        then show ?thesis using "1.prems"(2) * ** by blast
      next
        case b
  
        let ?tgts = "{t'' \<in> FSM.transitions M. t_source t'' |\<in>| q \<and> t_input t'' = t_input t' \<and> t_output t'' = t_output t'}"
        have "?tgts \<noteq> {}"
          using * ** by blast


        let ?tgts = "{t'' . t'' |\<in>| ftransitions M \<and> t_source t'' |\<in>| q \<and> t_input t'' = t_input t' \<and> t_output t'' = t_output t'}"
        define tgts where tgts: "tgts = Abs_fset (t_target ` ?tgts)"

        have "?tgts \<subseteq> transitions M"
          using ftransitions_set[of M]
          by (metis (no_types, lifting) mem_Collect_eq subsetI)   
        then have "finite (t_target ` ?tgts)"
          by (meson finite_imageI finite_subset fsm_transitions_finite)
        then have "fset tgts = (t_target ` ?tgts)"
          unfolding tgts 
          using Abs_fset_inverse
          by blast

        have "?tgts \<noteq> {}"
          using * **
          by (metis (mono_tags, lifting) empty_iff ftransitions_set mem_Collect_eq)
        then have "t_target ` ?tgts \<noteq> {}"
          by blast
        then have "tgts \<noteq> {||}" 
          using \<open>fset tgts = (t_target ` ?tgts)\<close>
          by force 

        then have "(q, t_input t', t_output t', tgts) |\<in>| qtrans"
          using b 
          unfolding qtrans_prop[of "(q,t_input t',t_output t',tgts)"]
          unfolding fst_conv snd_conv 
          unfolding \<open>fset tgts = (t_target ` ?tgts)\<close>[symmetric]
          by blast
        then show ?thesis
          by auto
      qed
    qed

    have i3: "t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones)) = t_target |`| qtrans |-| (dones |\<union>| (t_target |`| ts |-| dones))"
      by blast  
  
    have i4: "(\<And>q. q |\<in>| t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones)) \<Longrightarrow>
                q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M))"
    proof -
      fix q assume "q |\<in>| t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones))"
      then have "q |\<in>| t_target |`| qtrans"
        by auto
      then obtain t where "t |\<in>| qtrans" and "t_target t = q"
        by auto
      then have "fset q = t_target ` {t'. t' |\<in>| ftransitions M \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
        unfolding qtrans_prop by auto
      then have "fset q \<subseteq> t_target ` transitions M"
        by (metis (no_types, lifting) ftransitions_set image_Collect_subsetI image_eqI)
      then show "q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M)"
        by (metis (no_types, lifting) fPowI fset.set_map fset_inject ftransitions_set le_supI2 sup.orderE sup.orderI sup_fset.rep_eq)
    qed
  
    have i5: "(\<And>q. q |\<in>| dones |\<union>| ?nexts \<Longrightarrow> q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M |\<union>| {|initial M|}))"
      using "1.prems"(4,3) qtrans_prop
      by auto
  
    have i7: "{||} |\<notin>| dones |\<union>| ?nexts"
      using "1.prems" by fastforce


    show ?thesis
    proof (cases "?nexts' \<noteq> {||}")
      case False
      then have "?obs = ?ts'" 
        using res_cases by auto

      have "\<And> q io . q |\<in>| ?dones' \<Longrightarrow> q \<noteq> {||} \<Longrightarrow> (\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = io) \<longleftrightarrow> (\<exists>p'. pathlike ?obs q p' \<and> p_io p' = io)"
      proof -
        fix q io assume "q |\<in>| ?dones'" and "q \<noteq> {||}"
        then show "(\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = io) \<longleftrightarrow> (\<exists>p'. pathlike ?obs q p' \<and> p_io p' = io)"
        proof (induction io arbitrary: q)
          case Nil

          have scheme: "\<And> q q' X . q' |\<in>| q \<Longrightarrow> q |\<in>| fPow X \<Longrightarrow> q' |\<in>| X"
            by (simp add: fsubsetD)

          obtain q' where "q' |\<in>| q" 
            using \<open>q \<noteq> {||}\<close> by fastforce 
          have "q' |\<in>| t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M |\<union>| {|FSM.initial M|}"
            using scheme[OF \<open>q' |\<in>| q\<close> i5[OF \<open>q |\<in>| ?dones'\<close>]] .
          then have "q' \<in> states M"
            using ftransitions_source[of q' M]
            using ftransitions_target[of q' M]
            by force
          then have "\<exists> q' p . q' |\<in>| q \<and> path M q' p \<and> p_io p = []" 
            using \<open>q' |\<in>| q\<close> by auto
          moreover have "(\<exists> p'. pathlike ?obs q p' \<and> p_io p' = [])"
            by auto
          ultimately show ?case
            by simp
        next
          case (Cons ioT ioP)

          have "(\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = ioT # ioP) \<Longrightarrow> (\<exists>p'. pathlike ?obs q p' \<and> p_io p' = ioT # ioP)"
          proof -
            assume "\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = ioT # ioP"
            then obtain q' p where "q' |\<in>| q" and "path M q' p" and "p_io p = ioT # ioP"
              by meson
              
            then obtain tM pM where "p = tM # pM"
              by auto
            then have "tM \<in> transitions M" and "t_source tM |\<in>| q"
              using \<open>path M q' p\<close> \<open>q' |\<in>| q\<close> by blast+
            then obtain tP where "tP |\<in>| ts |\<union>| qtrans" 
                       and   "t_source tP = q" 
                       and   "t_input tP = t_input tM" 
                       and   "t_output tP = t_output tM"
              using Cons.prems i2 by blast

            have "path M (t_target tM) pM" and "p_io pM = ioP"
              using \<open>path M q' p\<close> \<open>p_io p = ioT # ioP\<close> unfolding \<open>p = tM # pM\<close> by auto
            moreover have "t_target tM |\<in>| t_target tP"
              using i1[OF \<open>tP |\<in>| ts |\<union>| qtrans\<close>]
              using \<open>p = tM # pM\<close> \<open>path M q' p\<close> \<open>q' |\<in>| q\<close> 
              unfolding \<open>t_input tP = t_input tM\<close> \<open>t_output tP = t_output tM\<close> \<open>t_source tP = q\<close>
              by fastforce 
            ultimately have "\<exists>q' p. q' |\<in>| t_target tP \<and> path M q' p \<and> p_io p = ioP"
              using \<open>p_io pM = ioP\<close> \<open>path M (t_target tM) pM\<close> by blast

            have "t_target tP |\<in>| dones |\<union>| (t_target |`| ts |-| dones)"
              using False \<open>tP |\<in>| ts |\<union>| qtrans\<close> by blast
            moreover have "t_target tP \<noteq> {||}"
              using i1[OF \<open>tP |\<in>| ts |\<union>| qtrans\<close>] by blast
            ultimately obtain pP where "pathlike ?obs (t_target tP) pP" and "p_io pP = ioP"
              using Cons.IH \<open>\<exists>q' p. q' |\<in>| t_target tP \<and> path M q' p \<and> p_io p = ioP\<close> by blast
            then have "pathlike ?obs q (tP#pP)"
              using \<open>t_source tP = q\<close> \<open>tP |\<in>| ts |\<union>| qtrans\<close> \<open>?obs = ?ts'\<close> by auto
            moreover have "p_io (tP#pP) = ioT # ioP"
              using \<open>t_input tP = t_input tM\<close> \<open>t_output tP = t_output tM\<close> \<open>p_io p = ioT # ioP\<close> \<open>p = tM # pM\<close> \<open>p_io pP = ioP\<close> by simp
            ultimately show ?thesis 
              by auto
          qed

          moreover have "(\<exists>p'. pathlike ?obs q p' \<and> p_io p' = ioT # ioP) \<Longrightarrow> (\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = ioT # ioP)"
          proof -
            assume "\<exists>p'. pathlike ?obs q p' \<and> p_io p' = ioT # ioP"
            then obtain p' where "pathlike ?ts' q p'" and "p_io p' = ioT # ioP"
              unfolding \<open>?obs = ?ts'\<close> by meson
            then obtain tP pP where "p' = tP#pP"
              by auto
      
            then have "t_source tP = q" and "tP |\<in>| ?ts'"
              using \<open>pathlike ?ts' q p'\<close> by auto
            
      
            have "pathlike ?ts' (t_target tP) pP" and "p_io pP = ioP"
              using \<open>pathlike ?ts' q p'\<close> \<open>p_io p' = ioT # ioP\<close> \<open>p' = tP#pP\<close> by auto
            then have "\<exists>p'. pathlike ?ts' (t_target tP) p' \<and> p_io p' = ioP"
              by auto
            moreover have "t_target tP |\<in>| dones |\<union>| (t_target |`| ts |-| dones)"
              using False \<open>tP |\<in>| ts |\<union>| qtrans\<close> by blast
            moreover have "t_target tP \<noteq> {||}"
              using i1[OF \<open>tP |\<in>| ts |\<union>| qtrans\<close>] by blast

            ultimately obtain q'' pM where "q'' |\<in>| t_target tP" and "path M q'' pM" and "p_io pM = ioP"
              using Cons.IH unfolding \<open>?obs = ?ts'\<close> by blast
      
            then obtain tM where "t_source tM |\<in>| q" and "tM \<in> transitions M" and "t_input tM = t_input tP" and "t_output tM = t_output tP" and "t_target tM = q''"
              using i1[OF \<open>tP |\<in>| ts |\<union>| qtrans\<close>]
              using \<open>q'' |\<in>| t_target tP\<close>  
              unfolding \<open>t_source tP = q\<close> by force

            have "path M (t_source tM) (tM#pM)"
              using \<open>tM \<in> transitions M\<close> \<open>t_target tM = q''\<close> \<open>path M q'' pM\<close> by auto
            moreover have "p_io (tM#pM) = ioT # ioP"
              using \<open>p_io pM = ioP\<close> \<open>t_input tM = t_input tP\<close> \<open>t_output tM = t_output tP\<close> \<open>p_io p' = ioT # ioP\<close> \<open>p' = tP#pP\<close> by auto
            ultimately show ?thesis 
              using \<open>t_source tM |\<in>| q\<close> by meson 
          qed
          ultimately show ?case
            by meson            
        qed
      qed

      then show ?thesis 
        using \<open>q |\<in>| dones\<close> \<open>{||} |\<notin>| dones\<close> by blast
    next
      case True

      have "make_observable_transitions (ftransitions M) ?nexts' ?dones' ?ts' = make_observable_transitions (ftransitions M) ?nexts dones ts"
      proof (cases "?nexts' = {||}")
        case True
        then have "?obs = ?ts'"
          using qtrans_def by auto 
        moreover have "make_observable_transitions (ftransitions M) ?nexts' ?dones' ?ts' = ?ts'"
          unfolding make_observable_transitions.simps[of "ftransitions M" ?nexts' ?dones' ?ts']
          unfolding True Let_def by auto
        ultimately show ?thesis 
          by blast
      next 
        case False
        then show ?thesis 
          unfolding make_observable_transitions.simps[of "ftransitions M" ?nexts dones ts] qtrans_def Let_def by auto
      qed
  
      then have IStep: "\<And> q io . q |\<in>| ?dones' \<Longrightarrow> 
                          (\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = io) =
                            (\<exists>p'. pathlike (make_observable_transitions (ftransitions M) ?nexts dones ts) q p' \<and> p_io p' = io)"
        using "1.hyps"[OF qtrans_def _ _ _ _ i1 i2 i4 i5 i7] True
        unfolding i3 
        by presburger


      show ?thesis 
        unfolding \<open>io = ioT # ioP\<close> 
      proof
        show "\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = ioT # ioP \<Longrightarrow> \<exists>p'. pathlike ?obs q p' \<and> p_io p' = ioT # ioP"
        proof -
          assume "\<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = ioT # ioP"
          then obtain q' p where "q' |\<in>| q" and "path M q' p" and "p_io p = ioT # ioP"
            by meson
            
          then obtain tM pM where "p = tM # pM"
            by auto
          then have "tM \<in> transitions M" and "t_source tM |\<in>| q"
            using \<open>path M q' p\<close> \<open>q' |\<in>| q\<close> by blast+
    
          
          then obtain tP where "tP |\<in>| ts" 
                     and   "t_source tP = q" 
                     and   "t_input tP = t_input tM" 
                     and   "t_output tP = t_output tM"
            using "1.prems"(2,6) by blast
  
          then have i9: "t_target tP |\<in>| dones |\<union>| ?nexts"
            by simp
  
          have "path M (t_target tM) pM" and "p_io pM = ioP"
            using \<open>path M q' p\<close> \<open>p_io p = ioT # ioP\<close> unfolding \<open>p = tM # pM\<close> by auto
          moreover have "t_target tM |\<in>| t_target tP"
            using "1.prems"(1)[OF \<open>tP |\<in>| ts\<close>] \<open>p = tM # pM\<close> \<open>path M q' p\<close> \<open>q' |\<in>| q\<close>  
            unfolding \<open>t_input tP = t_input tM\<close> \<open>t_output tP = t_output tM\<close> \<open>t_source tP = q\<close>
            by fastforce 
          ultimately have "\<exists>q' p. q' |\<in>| t_target tP \<and> path M q' p \<and> p_io p = ioP"
            using \<open>p_io pM = ioP\<close> \<open>path M (t_target tM) pM\<close> by blast
  
          obtain pP where "pathlike ?obs (t_target tP) pP" and "p_io pP = ioP"
            using \<open>\<exists>q' p. q' |\<in>| t_target tP \<and> path M q' p \<and> p_io p = ioP\<close> unfolding IStep[OF i9] 
            using that by blast
          

          then have "pathlike ?obs q (tP#pP)"
            using \<open>t_source tP = q\<close> \<open>tP |\<in>| ts\<close> make_observable_transitions_mono by blast
          moreover have "p_io (tP#pP) = ioT # ioP"
            using \<open>t_input tP = t_input tM\<close> \<open>t_output tP = t_output tM\<close> \<open>p_io p = ioT # ioP\<close> \<open>p = tM # pM\<close> \<open>p_io pP = ioP\<close> by simp
          ultimately show ?thesis 
            by auto
        qed

        show "\<exists>p'. pathlike ?obs q p' \<and> p_io p' = ioT # ioP \<Longrightarrow> \<exists>q' p. q' |\<in>| q \<and> path M q' p \<and> p_io p = ioT # ioP"
        proof -
          assume "\<exists>p'. pathlike ?obs q p' \<and> p_io p' = ioT # ioP"
          then obtain p' where "pathlike ?obs q p'" and "p_io p' = ioT # ioP"
            by meson
          then obtain tP pP where "p' = tP#pP"
            by auto


          have "\<And> t' . t' |\<in>| ftransitions M = (t' \<in> transitions M)"
            using ftransitions_set
            by metis

          from \<open>p' = tP#pP\<close> have "t_source tP = q" and "tP |\<in>| ?obs"
            using \<open>pathlike ?obs q p'\<close> by auto
          then have "tP |\<in>| ts"
            using "1.prems"(6) make_observable_transitions_t_source[of ts dones "ftransitions M"] "1.prems"(1,2)
            unfolding \<open>\<And> t' . t' |\<in>| ftransitions M = (t' \<in> transitions M)\<close>
            by blast
          then have i9: "t_target tP |\<in>| dones |\<union>| ?nexts"
            by simp           
    
          have "pathlike ?obs (t_target tP) pP" and "p_io pP = ioP"
            using \<open>pathlike ?obs q p'\<close> \<open>p_io p' = ioT # ioP\<close> \<open>p' = tP#pP\<close> by auto
          then have "\<exists>p'. pathlike ?obs (t_target tP) p' \<and> p_io p' = ioP"
            by auto
          then obtain q'' pM where "q'' |\<in>| t_target tP" and "path M q'' pM" and "p_io pM = ioP"
            using IStep[OF i9] by blast

          obtain tM where "t_source tM |\<in>| q" and "tM \<in> transitions M" and "t_input tM = t_input tP" and "t_output tM = t_output tP" and "t_target tM = q''"
            using "1.prems"(1)[OF \<open>tP |\<in>| ts\<close>] \<open>q'' |\<in>| t_target tP\<close> 
            unfolding \<open>t_source tP = q\<close> 
            by force

          have "path M (t_source tM) (tM#pM)"
            using \<open>tM \<in> transitions M\<close> \<open>t_target tM = q''\<close> \<open>path M q'' pM\<close> by auto
          moreover have "p_io (tM#pM) = ioT # ioP"
            using \<open>p_io pM = ioP\<close> \<open>t_input tM = t_input tP\<close> \<open>t_output tM = t_output tP\<close> \<open>p_io p' = ioT # ioP\<close> \<open>p' = tP#pP\<close> by auto
          ultimately show ?thesis 
            using \<open>t_source tM |\<in>| q\<close> by meson 
        qed
      qed
    qed
  qed
qed






fun observable_fset :: "('a,'b,'c) transition fset \<Rightarrow> bool" where
  "observable_fset ts = (\<forall> t1 t2 . t1 |\<in>| ts \<longrightarrow> t2 |\<in>| ts \<longrightarrow> 
                          t_source t1 = t_source t2 \<longrightarrow> t_input t1 = t_input t2 \<longrightarrow> t_output t1 = t_output t2
                            \<longrightarrow> t_target t1 = t_target t2)" 



lemma make_observable_transitions_observable :
  assumes "\<And> t . t |\<in>| ts \<Longrightarrow> t_source t |\<in>| dones \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
  and     "observable_fset ts"
shows "observable_fset (make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts)"
using assms proof (induction base_trans "(fimage t_target ts) |-| dones" dones ts rule: make_observable_transitions.induct)
  case (1 base_trans dones ts)

  let ?nexts = "(fimage t_target ts) |-| dones"

  

  define qtrans where qtrans_def: "qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) base_trans;
                                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                       in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)) ?nexts)"
  
  have qtrans_prop: "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| ?nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
    using make_observable_transitions_qtrans_helper[OF qtrans_def]
    by presburger
   

  let ?dones' = "dones |\<union>| ?nexts"
  let ?ts'    = "ts |\<union>| qtrans"
  let ?nexts' = "(fimage t_target qtrans) |-| ?dones'"

  have "observable_fset qtrans" 
    using qtrans_prop
    unfolding observable_fset.simps
    by (metis (mono_tags, lifting) Collect_cong fset_inject)  
  moreover have "t_source |`| qtrans |\<inter>| t_source |`| ts = {||}"
    using "1.prems"(1) qtrans_prop by force
  ultimately have "observable_fset ?ts'"
    using "1.prems"(2) unfolding observable_fset.simps
    by blast
  

  have res_cases: "make_observable_transitions base_trans ?nexts dones ts = (if ?nexts' = {||} 
            then ?ts'
            else make_observable_transitions base_trans ?nexts' ?dones' ?ts')"
    unfolding make_observable_transitions.simps[of base_trans ?nexts dones ts] qtrans_def Let_def by simp

  show ?case proof (cases "?nexts' = {||}")
    case True
    then have "make_observable_transitions base_trans ?nexts dones ts = ?ts'"
      using res_cases by simp
    then show ?thesis 
      using \<open>observable_fset ?ts'\<close> by simp
  next
    case False
    then have *: "make_observable_transitions base_trans ?nexts dones ts = make_observable_transitions base_trans ?nexts' ?dones' ?ts'"
      using res_cases by simp

    have i1: "(\<And>t. t |\<in>| ts |\<union>| qtrans \<Longrightarrow>
                  t_source t |\<in>| dones |\<union>| ?nexts \<and>
                  t_target t \<noteq> {||} \<and>
                  fset (t_target t) =
                  t_target `
                  {t' . t' |\<in>| base_trans \<and>
                   t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t})"
      using "1.prems"(1) qtrans_prop by blast

    have i3: "t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones)) = t_target |`| qtrans |-| (dones |\<union>| (t_target |`| ts |-| dones))"
      by auto

    have i4: "t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones)) \<noteq> {||}"
      using False by auto

    show ?thesis
      using "1.hyps"[OF qtrans_def _ _ i3 i4 i1 \<open>observable_fset ?ts'\<close>] unfolding * i3 by metis
  qed
qed


lemma make_observable_transitions_transition_props : 
  assumes "\<And> t . t |\<in>| ts \<Longrightarrow> t_source t |\<in>| dones \<and> t_target t |\<in>| dones |\<union>| ((fimage t_target ts) |-| dones) \<and> t_input t |\<in>| t_input |`| base_trans \<and> t_output t |\<in>| t_output |`| base_trans"
  assumes "t |\<in>| make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts"
shows "t_source t |\<in>| dones |\<union>| (t_target |`| (make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts))"  
    and "t_target t |\<in>| dones |\<union>| (t_target |`| (make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts))" 
    and "t_input t |\<in>| t_input |`| base_trans"
    and "t_output t |\<in>| t_output |`| base_trans"  
proof -
  have "t_source t |\<in>| dones |\<union>| (t_target |`| (make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts))
          \<and> t_target t |\<in>| dones |\<union>| (t_target |`| (make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts)) 
          \<and> t_input t |\<in>| t_input |`| base_trans 
          \<and> t_output t |\<in>| t_output |`| base_trans"
    using assms(1,2)
  proof (induction base_trans "((fimage t_target ts) |-| dones)" dones ts rule: make_observable_transitions.induct)
    case (1 base_trans dones ts)

    let ?nexts = "((fimage t_target ts) |-| dones)"

    define qtrans where qtrans_def: "qtrans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) base_trans;
                                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                       in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)) ?nexts)"
  
    have qtrans_prop: "\<And> t . t |\<in>| qtrans \<longleftrightarrow> t_source t |\<in>| ?nexts \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' . t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
      using make_observable_transitions_qtrans_helper[OF qtrans_def]
      by presburger

    let ?dones' = "dones |\<union>| ?nexts"
    let ?ts'    = "ts |\<union>| qtrans"
    let ?nexts' = "(fimage t_target qtrans) |-| ?dones'"

    have res_cases: "make_observable_transitions base_trans ?nexts dones ts = (if ?nexts' = {||} 
              then ?ts'
              else make_observable_transitions base_trans ?nexts' ?dones' ?ts')"
      unfolding make_observable_transitions.simps[of base_trans ?nexts dones ts] qtrans_def Let_def by simp


    have qtrans_trans_prop: "(\<And>t. t |\<in>| qtrans \<Longrightarrow>
                  t_source t |\<in>| dones |\<union>| (t_target |`| ts |-| dones) \<and>
                  t_target t |\<in>| dones |\<union>| (t_target |`| ts |-| dones) |\<union>| (t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones))) \<and>
                  t_input t |\<in>| t_input |`| base_trans \<and> t_output t |\<in>| t_output |`| base_trans)" (is "\<And> t . t |\<in>| qtrans \<Longrightarrow> ?P t")
    proof -
      fix t assume "t |\<in>| qtrans"

      then have "t_source t |\<in>| dones |\<union>| (t_target |`| ts |-| dones)"
        using \<open>t |\<in>| qtrans\<close> unfolding qtrans_prop[of t] by blast
      moreover have "t_target t |\<in>| dones |\<union>| (t_target |`| ts |-| dones) |\<union>| (t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones)))" 
        using \<open>t |\<in>| qtrans\<close> "1.prems"(1) by blast
      moreover have "t_input t |\<in>| t_input |`| base_trans \<and> t_output t |\<in>| t_output |`| base_trans"
      proof -
        obtain t' where "t' \<in> {t'. t' |\<in>| base_trans \<and> t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
          using \<open>t |\<in>| qtrans\<close> unfolding qtrans_prop[of t]
          by (metis (mono_tags, lifting) Collect_empty_eq bot_fset.rep_eq empty_is_image fset_inject mem_Collect_eq) 
        then show ?thesis
          by force
      qed
      ultimately show "?P t" 
        by blast
    qed    
    

    show ?case proof (cases "?nexts' = {||}")
      case True
      then have "t |\<in>| ?ts'"
        using "1.prems"(2) res_cases by force
      then show ?thesis
        using "1.prems"(1) qtrans_trans_prop
        by (metis True fimage_funion funion_fminus_cancel funion_iff res_cases) 
    next
      case False
      then have *: "make_observable_transitions base_trans ?nexts dones ts = make_observable_transitions base_trans ?nexts' ?dones' ?ts'"
        using res_cases by simp

      have i1: "t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones)) = t_target |`| qtrans |-| (dones |\<union>| (t_target |`| ts |-| dones))"
        by blast

      have i2: "t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones)) \<noteq> {||}"
        using False by blast

      have i3: "(\<And>t. t |\<in>| ts |\<union>| qtrans \<Longrightarrow>
                  t_source t |\<in>| dones |\<union>| (t_target |`| ts |-| dones) \<and>
                  t_target t |\<in>| dones |\<union>| (t_target |`| ts |-| dones) |\<union>| (t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones))) \<and>
                  t_input t |\<in>| t_input |`| base_trans \<and> t_output t |\<in>| t_output |`| base_trans)"
        using "1.prems"(1) qtrans_trans_prop by blast

      have i4: "t |\<in>| make_observable_transitions base_trans (t_target |`| (ts |\<union>| qtrans) |-| (dones |\<union>| (t_target |`| ts |-| dones))) (dones |\<union>| (t_target |`| ts |-| dones)) (ts |\<union>| qtrans)"
        using "1.prems"(2) unfolding * i1 by assumption

      show ?thesis
        using "1.hyps"[OF qtrans_def _ _ i1 i2 i3 i4] unfolding  i1 unfolding *[symmetric]
        using make_observable_transitions_mono[of ts base_trans ?nexts dones] by blast
    qed
  qed
  then show "t_source t |\<in>| dones |\<union>| (t_target |`| (make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts))"  
        and "t_target t |\<in>| dones |\<union>| (t_target |`| (make_observable_transitions base_trans ((fimage t_target ts) |-| dones) dones ts))" 
        and "t_input t |\<in>| t_input |`| base_trans"
        and "t_output t |\<in>| t_output |`| base_trans" 
    by blast+
qed





fun make_observable :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> ('a fset,'b,'c) fsm" where
  "make_observable M = (let
      initial_trans = (let qts = ffilter (\<lambda>t . t_source t = initial M) (ftransitions M);
                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                       in fimage (\<lambda>(x,y) . ({|initial M|},x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios);
      nexts = fimage t_target initial_trans |-| {|{|initial M|}|};
      ptransitions = make_observable_transitions (ftransitions M) nexts {|{|initial M|}|} initial_trans;
      pstates = finsert {|initial M|} (t_target |`| ptransitions);
      M' = create_unconnected_fsm_from_fsets {|initial M|} pstates (finputs M) (foutputs M)
  in add_transitions M' (fset ptransitions))"






lemma make_observable_language_observable :
  shows "L (make_observable M) = L M"
    and "observable (make_observable M)"
    and "initial (make_observable M) = {|initial M|}"
    and "inputs (make_observable M) = inputs M"
    and "outputs (make_observable M) = outputs M"
proof -

  define initial_trans where "initial_trans = (let qts = ffilter (\<lambda>t . t_source t = initial M) (ftransitions M);
                                 ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                             in fimage (\<lambda>(x,y) . ({|initial M|},x,y, t_target |`| ((ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts)))) ios)"
  moreover define ptransitions where "ptransitions = make_observable_transitions (ftransitions M) (fimage t_target initial_trans |-| {|{|initial M|}|}) {|{|initial M|}|} initial_trans"
  moreover define pstates where "pstates = finsert {|initial M|} (t_target |`| ptransitions)"
  moreover define M' where "M' = create_unconnected_fsm_from_fsets {|initial M|} pstates (finputs M) (foutputs M)"

  ultimately have "make_observable M = add_transitions M' (fset ptransitions)"
    unfolding make_observable.simps Let_def by blast

  have "{|initial M|} |\<in>| pstates"
    unfolding pstates_def by blast
  have "inputs M' = inputs M"
    unfolding M'_def create_unconnected_fsm_from_fsets_simps(3)[OF \<open>{|initial M|} |\<in>| pstates\<close>, of "finputs M" "foutputs M"]
    using fset_of_list.rep_eq inputs_as_list_set by fastforce 
  have "outputs M' = outputs M"
    unfolding M'_def create_unconnected_fsm_from_fsets_simps(4)[OF \<open>{|initial M|} |\<in>| pstates\<close>, of "finputs M" "foutputs M"]
    using fset_of_list.rep_eq outputs_as_list_set by fastforce 
  have "states M' = fset pstates" and "transitions M' = {}" and "initial M' = {|initial M|}"
     unfolding M'_def create_unconnected_fsm_from_fsets_simps(1,2,5)[OF \<open>{|initial M|} |\<in>| pstates\<close>] by simp+


  have initial_trans_prop: "\<And> t . t |\<in>| initial_trans \<longleftrightarrow> t_source t |\<in>| {|{|FSM.initial M|}|} \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' \<in> transitions M . t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
  proof -
    have *:"\<And> t' . t' |\<in>| ftransitions M = (t' \<in> transitions M)"
            using ftransitions_set
            by metis 
    have **: "initial_trans = ffUnion (fimage (\<lambda> q . (let qts = ffilter (\<lambda>t . t_source t |\<in>| q) (ftransitions M);
                                           ios = fimage (\<lambda> t . (t_input t, t_output t)) qts
                                       in fimage (\<lambda>(x,y) . (q,x,y, t_target |`| (ffilter (\<lambda>t . (t_input t, t_output t) = (x,y)) qts))) ios)) {|{|initial M|}|})"
      unfolding initial_trans_def by auto
    show "\<And> t . t |\<in>| initial_trans \<longleftrightarrow> t_source t |\<in>| {|{|FSM.initial M|}|} \<and> t_target t \<noteq> {||} \<and> fset (t_target t) = t_target ` {t' \<in> transitions M . t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
      unfolding make_observable_transitions_qtrans_helper[OF **] *
      by presburger
  qed

  have well_formed_transitions: "\<And> t . t \<in> (fset ptransitions) \<Longrightarrow> t_source t \<in> states M' \<and> t_input t \<in> inputs M' \<and> t_output t \<in> outputs M' \<and> t_target t \<in> states M'"
    (is "\<And> t .  t \<in> (fset ptransitions) \<Longrightarrow> ?P1 t \<and> ?P2 t \<and> ?P3 t \<and> ?P4 t")
  proof -
    fix t assume "t \<in> (fset ptransitions)"

    then have i2: "t |\<in>| make_observable_transitions (ftransitions M) (fimage t_target initial_trans |-| {|{|initial M|}|}) {|{|initial M|}|} initial_trans"
      using ptransitions_def
      by metis 

    have i1: "(\<And>t. t |\<in>| initial_trans \<Longrightarrow>
          t_source t |\<in>| {|{|FSM.initial M|}|} \<and>
          t_target t |\<in>| {|{|FSM.initial M|}|} |\<union>| (t_target |`| initial_trans |-| {|{|FSM.initial M|}|}) \<and>
          t_input t |\<in>| t_input |`| ftransitions M \<and> t_output t |\<in>| t_output |`| ftransitions M)" (is "\<And> t . t |\<in>| initial_trans \<Longrightarrow> ?P t")
    proof -
      fix t assume *: "t |\<in>| initial_trans"
      then have "t_source t |\<in>| {|{|FSM.initial M|}|}" 
           and  "t_target t \<noteq> {||}" 
           and  "fset (t_target t) = t_target ` {t' \<in> FSM.transitions M. t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}"
        using initial_trans_prop by blast+

      have "t_target t |\<in>| {|{|FSM.initial M|}|} |\<union>| (t_target |`| initial_trans |-| {|{|FSM.initial M|}|})"
        using "*" by blast
        
      moreover have "t_input t |\<in>| t_input |`| ftransitions M \<and> t_output t |\<in>| t_output |`| ftransitions M"
      proof -
        obtain t' where "t' \<in> transitions M" and "t_input t = t_input t'" and "t_output t = t_output t'"
          using \<open>t_target t \<noteq> {||}\<close> \<open>fset (t_target t) = t_target ` {t' \<in> FSM.transitions M. t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t}\<close>
          by (metis (mono_tags, lifting) bot_fset.rep_eq empty_Collect_eq fset_inject image_empty) 

        have "fset (ftransitions M) = transitions M"
          by (simp add: fset_of_list.rep_eq fsm_transitions_finite) 
        then show ?thesis 
          unfolding \<open>t_input t = t_input t'\<close> \<open>t_output t = t_output t'\<close>
          using \<open>t' \<in> transitions M\<close>
          by auto
      qed
        
      ultimately show "?P t" 
        using \<open>t_source t |\<in>| {|{|FSM.initial M|}|}\<close> by blast
    qed 


    have "?P1 t"
      using make_observable_transitions_transition_props(1)[OF i1 i2] unfolding pstates_def ptransitions_def \<open>states M' = fset pstates\<close>
      by (metis finsert_is_funion)
    moreover have "?P2 t" 
    proof-
      have "t_input t |\<in>| t_input |`| ftransitions M"
        using make_observable_transitions_transition_props(3)[OF i1 i2] by blast
      then have "t_input t \<in> t_input ` transitions M"
        using ftransitions_set by (metis (mono_tags, lifting) fset.set_map)
      then show ?thesis
        using finputs_set fsm_transition_input \<open>inputs M' = inputs M\<close> by fastforce 
    qed
    moreover have "?P3 t"
    proof-
      have "t_output t |\<in>| t_output |`| ftransitions M"
        using make_observable_transitions_transition_props(4)[OF i1 i2] by blast
      then have "t_output t \<in> t_output ` transitions M"
        using ftransitions_set by (metis (mono_tags, lifting) fset.set_map)
      then show ?thesis
        using foutputs_set fsm_transition_output \<open>outputs M' = outputs M\<close> by fastforce 
    qed
    moreover have "?P4 t"
      using make_observable_transitions_transition_props(2)[OF i1 i2] unfolding pstates_def ptransitions_def \<open>states M' = fset pstates\<close>
      by (metis finsert_is_funion)
      
    ultimately show "?P1 t \<and> ?P2 t \<and> ?P3 t \<and> ?P4 t"
      by blast
  qed

  have "initial (make_observable M) = {|initial M|}"
   and "states (make_observable M) = fset pstates"
   and "inputs (make_observable M) = inputs M"
   and "outputs (make_observable M) = outputs M"
   and "transitions (make_observable M) = fset ptransitions"
    using add_transitions_simps[OF well_formed_transitions, of "fset ptransitions"] 
    unfolding \<open>make_observable M = add_transitions M' (fset ptransitions)\<close>[symmetric]
              \<open>inputs M' = inputs M\<close> \<open>outputs M' = outputs M\<close> \<open>initial M' = {|initial M|}\<close> \<open>states M' = fset pstates\<close> \<open>transitions M' = {}\<close>
    by blast+

  then show "initial (make_observable M) = {|initial M|}" and "inputs (make_observable M) = inputs M" and "outputs (make_observable M) = outputs M"
    by presburger+


  have i1: "(\<And>t. t |\<in>| initial_trans \<Longrightarrow>
                    t_source t |\<in>| {|{|FSM.initial M|}|} \<and>
                    t_target t \<noteq> {||} \<and>
                    fset (t_target t) = t_target ` {t' \<in> FSM.transitions M. t_source t' |\<in>| t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t})"
    using initial_trans_prop by blast

  have i2: "(\<And>q t'.
                    q |\<in>| {|{|FSM.initial M|}|} \<Longrightarrow>
                    t' \<in> FSM.transitions M \<Longrightarrow> t_source t' |\<in>| q \<Longrightarrow> \<exists>t. t |\<in>| initial_trans \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t')"
  proof -
    fix q t' assume "q |\<in>| {|{|FSM.initial M|}|}" and "t' \<in> FSM.transitions M" and "t_source t' |\<in>| q"
    then have "q = {|FSM.initial M|}" and "t_source t' = initial M" 
      by auto

    define tgt where "tgt =  t_target ` {t'' \<in> FSM.transitions M. t_source t'' |\<in>| {|FSM.initial M|} \<and> t_input t'' = t_input t' \<and> t_output t'' = t_output t'}"
    have "t_target t' \<in> tgt"
      unfolding tgt_def using \<open>t' \<in> FSM.transitions M\<close> \<open>t_source t' = initial M\<close> by auto
    then have "tgt \<noteq> {}"
      by auto

    have "finite tgt"
      using fsm_transitions_finite[of M] unfolding tgt_def by auto
    then have "fset (Abs_fset tgt) = tgt"
      by (simp add: Abs_fset_inverse)
    then have "Abs_fset tgt \<noteq> {||}"
      using \<open>tgt \<noteq> {}\<close> by auto

    let ?t = "({|FSM.initial M|}, t_input t', t_output t', Abs_fset tgt)"
    have "?t |\<in>| initial_trans"
      unfolding initial_trans_prop fst_conv snd_conv \<open>fset (Abs_fset tgt) = tgt\<close>
      unfolding \<open>tgt =  t_target ` {t'' \<in> FSM.transitions M. t_source t'' |\<in>| {|FSM.initial M|} \<and> t_input t'' = t_input t' \<and> t_output t'' = t_output t'}\<close>[symmetric]
      using \<open>Abs_fset tgt \<noteq> {||}\<close> 
      by blast
    then show "\<exists>t. t |\<in>| initial_trans \<and> t_source t = q \<and> t_input t = t_input t' \<and> t_output t = t_output t'"
      using \<open>q = {|FSM.initial M|}\<close> by auto
  qed

  have i3: "(\<And>q. q |\<in>| t_target |`| initial_trans |-| {|{|FSM.initial M|}|} \<Longrightarrow> q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M))"
  proof -
    fix q assume "q |\<in>| t_target |`| initial_trans |-| {|{|FSM.initial M|}|}"
    then obtain t where "t |\<in>| initial_trans" and "t_target t = q"
      by auto

    have "fset q \<subseteq> t_target ` (transitions M)"
      using \<open>t |\<in>| initial_trans\<close>
      unfolding initial_trans_prop \<open>t_target t = q\<close>
      by auto
    then have "q |\<subseteq>| (t_target |`| ftransitions M)"
      using ftransitions_set[of M]
      by (simp add: less_eq_fset.rep_eq) 
    then show "q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M)"
      by auto
  qed

  have i4: "(\<And>q. q |\<in>| {|{|FSM.initial M|}|} \<Longrightarrow> q |\<in>| fPow (t_source |`| ftransitions M |\<union>| t_target |`| ftransitions M |\<union>| {|FSM.initial M|}))"
   and i5: "{||} |\<notin>| {|{|FSM.initial M|}|}"
   and i6: "{|FSM.initial M|} |\<in>| {|{|FSM.initial M|}|}"
    by blast+


  show "L (make_observable M) = L M"
  proof -
    have *: "\<And> p . pathlike ptransitions {|initial M|} p = path (make_observable M) {|initial M|} p"
    proof 
      have "\<And> q p . p \<noteq> [] \<Longrightarrow> pathlike ptransitions q p \<Longrightarrow> path (make_observable M) q p"
      proof -
        fix q p assume "p \<noteq> []" and "pathlike ptransitions q p"
        then show "path (make_observable M) q p"
        proof (induction p arbitrary: q)
          case Nil
          then show ?case by blast
        next
          case (Cons t p)
          then have "t |\<in>| ptransitions" and "pathlike ptransitions (t_target t) p" and "t_source t = q"
            by blast+
    
          have "t \<in> transitions (make_observable M)"
            using \<open>t |\<in>| ptransitions\<close> \<open>transitions (make_observable M) = fset ptransitions\<close>
            by metis
          moreover have "path (make_observable M) (t_target t) p"
            using Cons.IH[OF _ \<open>pathlike ptransitions (t_target t) p\<close>] calculation by blast
          ultimately show ?case 
            using \<open>t_source t = q\<close> by blast
        qed
      qed
      then show "\<And> p . pathlike ptransitions {|initial M|} p \<Longrightarrow> path (make_observable M) {|initial M|} p"
        by (metis \<open>FSM.initial (make_observable M) = {|FSM.initial M|}\<close> fsm_initial path.nil)
      
      show "\<And> q p . path (make_observable M) q p \<Longrightarrow> pathlike ptransitions q p"
      proof -
        fix q p assume "path (make_observable M) q p"
        then show "pathlike ptransitions q p"
        proof (induction p arbitrary: q rule: list.induct)
          case Nil
          then show ?case by blast
        next
          case (Cons t p)
          then have "t \<in> transitions (make_observable M)" and "path (make_observable M) (t_target t) p" and "t_source t = q"
            by blast+
  
          have "t |\<in>| ptransitions"
            using \<open>t \<in> transitions (make_observable M)\<close> \<open>transitions (make_observable M) = fset ptransitions\<close>
            by metis
          then show ?case 
            using Cons.IH[OF \<open>path (make_observable M) (t_target t) p\<close>] \<open>t_source t = q\<close> by blast          
        qed
      qed
    qed
    
    have "\<And> io . (\<exists>q' p. q' |\<in>| {|FSM.initial M|} \<and> path M q' p \<and> p_io p = io) = (\<exists>p'. pathlike ptransitions {|FSM.initial M|} p' \<and> p_io p' = io)"
      using make_observable_transitions_path[OF i1 i2 i3 i4 i5 i6] unfolding ptransitions_def[symmetric] by blast
    then have "\<And> io . (\<exists>p. path M (FSM.initial M) p \<and> p_io p = io) = (\<exists>p' . path (make_observable M) {|initial M|} p' \<and> p_io p' = io)"
      unfolding *
      by (metis (no_types, lifting) fempty_iff finsert_iff) 
    then show ?thesis
      unfolding LS.simps \<open>initial (make_observable M) = {|initial M|}\<close> by (metis (no_types, lifting)) 
  qed


  show "observable (make_observable M)"
  proof -

    have i2: "observable_fset initial_trans"
      unfolding observable_fset.simps 
      unfolding initial_trans_prop
      using fset_inject
      by metis

    have "\<And> t' . t' |\<in>| ftransitions M = (t' \<in> transitions M)"
      using ftransitions_set
      by metis 
    have "observable_fset ptransitions"
      using make_observable_transitions_observable[OF _ i2, of "{| {|initial M|} |}" "ftransitions M"] i1 
      unfolding ptransitions_def \<open>\<And> t' . t' |\<in>| ftransitions M = (t' \<in> transitions M)\<close>
      by blast 
    then show ?thesis
      unfolding observable.simps observable_fset.simps \<open>transitions (make_observable M) = fset ptransitions\<close>
      by metis 
  qed
qed

end