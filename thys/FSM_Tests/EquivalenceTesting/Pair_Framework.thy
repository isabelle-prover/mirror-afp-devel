section \<open>Pair-Framework\<close>

text \<open>This theory defines the Pair-Framework and provides completeness properties.\<close>


theory Pair_Framework
  imports H_Framework 
begin

subsection \<open>Classical H-Condition\<close>

definition satisfies_h_condition :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('b \<times>'c) list set \<Rightarrow> nat \<Rightarrow> bool" where
  "satisfies_h_condition M V T m = (let
      \<Pi> = (V ` reachable_states M);
      n = card (reachable_states M);
      \<X> = \<lambda> q . {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M}; 
      A = \<Pi> \<times> \<Pi>;
      B = \<Pi> \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q};
      C = (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> \<X> q . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>}) 
    in 
      is_state_cover_assignment M V
      \<and> \<Pi> \<subseteq> T
      \<and> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> T
      \<and> (\<forall> (\<alpha>,\<beta>) \<in> A \<union> B \<union> C . \<alpha> \<in> L M \<longrightarrow> 
                                \<beta> \<in> L M \<longrightarrow> 
                                after_initial M \<alpha> \<noteq> after_initial M \<beta> \<longrightarrow> 
                                (\<exists> \<omega> . \<alpha>@\<omega> \<in> T \<and>
                                       \<beta>@\<omega> \<in> T \<and>
                                       distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>)))"

lemma h_condition_satisfies_abstract_h_condition :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
  and     "satisfies_h_condition M V T m"
  and     "(L M \<inter> T = L I \<inter> T)"
shows "satisfies_abstract_h_condition M I V m"
proof -

  define \<Pi> where \<Pi>: "\<Pi> = (V ` reachable_states M)"
  define n where n: "n = size_r M"
  define \<X> where \<X>: "\<X> = (\<lambda> q . {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M})"
  define A where A: "A = \<Pi> \<times> \<Pi>"
  define B where B: "B = \<Pi> \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q}"
  define C where C: "C = (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> \<X> q . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>})"


  have "satisfies_h_condition M V T m = (is_state_cover_assignment M V
    \<and> \<Pi> \<subseteq> T
    \<and> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> T
    \<and> (\<forall> (\<alpha>,\<beta>) \<in> A \<union> B \<union> C . \<alpha> \<in> L M \<longrightarrow> 
                              \<beta> \<in> L M \<longrightarrow> 
                              after_initial M \<alpha> \<noteq> after_initial M \<beta> \<longrightarrow> 
                              (\<exists> \<omega> . \<alpha>@\<omega> \<in> T \<and>
                                     \<beta>@\<omega> \<in> T \<and>
                                     distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>)))"
    unfolding satisfies_h_condition_def Let_def \<Pi> n \<X> A B C  
    by auto

  then have "is_state_cover_assignment M V" 
        and "\<Pi> \<subseteq> T" 
        and "{ (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> T"
        and distinguishing_tests: "\<And> \<alpha> \<beta> . (\<alpha>,\<beta>) \<in> A \<union> B \<union> C \<Longrightarrow> 
                            \<alpha> \<in> L M \<Longrightarrow> 
                            \<beta> \<in> L M \<Longrightarrow> 
                            after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow> 
                            (\<exists> \<omega> . \<alpha>@\<omega> \<in> T \<and>
                                   \<beta>@\<omega> \<in> T \<and>
                                   distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>)"
    using \<open>satisfies_h_condition M V T m\<close> by blast+

  have "\<Pi> \<subseteq> L I" and "\<Pi> \<subseteq> L M"
    using \<open>\<Pi> \<subseteq> T\<close> \<open>\<Pi> = (V ` reachable_states M)\<close> \<open>L M \<inter> T = L I \<inter> T\<close> 
          state_cover_assignment_language[OF \<open>is_state_cover_assignment M V\<close>] by blast+

  have "(\<And> q \<gamma> . q \<in> reachable_states M \<Longrightarrow> length \<gamma> \<le> Suc (m-size_r M) \<Longrightarrow> list.set \<gamma> \<subseteq> inputs M \<times> outputs M  \<Longrightarrow> butlast \<gamma> \<in> LS M q \<Longrightarrow>  (L M \<inter> (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) = L I \<inter> (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})) \<and> (preserves_divergence M I (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))) \<Longrightarrow>
        satisfies_abstract_h_condition M I V m"
    unfolding satisfies_abstract_h_condition_def Let_def 
    by blast
  moreover have "(\<And> q \<gamma> . q \<in> reachable_states M \<Longrightarrow> length \<gamma> \<le> Suc (m-size_r M) \<Longrightarrow> list.set \<gamma> \<subseteq> inputs M \<times> outputs M  \<Longrightarrow> butlast \<gamma> \<in> LS M q \<Longrightarrow>  (L M \<inter> (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) = L I \<inter> (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})) \<and> (preserves_divergence M I (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})))"
  proof -
    fix q \<gamma> 
    assume a1: "q \<in> reachable_states M" 
       and a2: "length \<gamma> \<le> Suc (m-size_r M)" 
       and a3: "list.set \<gamma> \<subseteq> inputs M \<times> outputs M"
       and a4: "butlast \<gamma> \<in> LS M q" 


    have "{V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<subseteq> {V q} \<union> {V q @ \<tau> | \<tau>. \<tau> \<in> \<X> q}"
    proof 
      fix v assume "v \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}"
      then obtain w where "v = V q @ w" and "w \<in> list.set (prefixes \<gamma>)"
        by blast

      show "v \<in> {V q} \<union> {V q @ \<tau> | \<tau>. \<tau> \<in> \<X> q}"
      proof (cases w rule: rev_cases)
        case Nil
        show ?thesis unfolding \<open>v = V q @ w\<close> Nil \<Pi> using a1 by auto
      next
        case (snoc w' xy)

        obtain w'' where "\<gamma> = w'@[xy]@w''"
          using \<open>w \<in> list.set (prefixes \<gamma>)\<close> 
          unfolding prefixes_set snoc by auto

        obtain w''' x y where "\<gamma> = (w'@w''')@[(x,y)]"
        proof (cases w'' rule: rev_cases)
          case Nil
          show ?thesis 
            using that[of "[]" "fst xy" "snd xy"] 
            unfolding \<open>\<gamma> = w'@[xy]@w''\<close> Nil by auto
        next
          case (snoc w''' xy')
          show ?thesis 
            using that[of "[xy]@w'''" "fst xy'" "snd xy'"]
            unfolding \<open>\<gamma> = w'@[xy]@w''\<close> snoc by auto              
        qed
        then have "butlast \<gamma> = w'@w'''"
          using butlast_snoc by metis

        have "w' \<in> LS M q"
          using a4 unfolding \<open>v = V q @ w\<close> \<open>butlast \<gamma> = w'@w'''\<close> 
          using language_prefix by metis
        moreover have "length w' \<le> m - size_r M"
          using a2 unfolding \<open>v = V q @ w\<close> \<open>\<gamma> = (w'@w''')@[(x,y)]\<close> by auto
        moreover have "fst xy \<in> FSM.inputs M \<and> snd xy \<in> FSM.outputs M"
          using a3 unfolding \<open>v = V q @ w\<close> \<open>\<gamma> = w'@[xy]@w''\<close> by auto
        ultimately have "w'@[(fst xy, snd xy)] \<in> \<X> q"
          unfolding snoc \<X> n by blast
        then have "w \<in> \<X> q"
          unfolding snoc by auto
        then show ?thesis
          unfolding \<open>v = V q @ w\<close> using a1 by blast
      qed
    qed


    have "preserves_divergence M I (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
    proof -
      have "\<And> \<alpha> \<beta> . \<alpha> \<in> L M \<Longrightarrow> \<alpha> \<in> (\<Pi> \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<Longrightarrow> \<beta> \<in> L M \<Longrightarrow> \<beta> \<in>  (\<Pi> \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<Longrightarrow>
          \<not> converge M \<alpha> \<beta> \<Longrightarrow> \<not> converge I \<alpha> \<beta>"
      proof -
        fix \<alpha> \<beta> 
        assume "\<alpha> \<in> L M"
           and "\<alpha> \<in> (\<Pi> \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
           and "\<beta> \<in> L M"
           and "\<beta> \<in>  (\<Pi> \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
           and "\<not> converge M \<alpha> \<beta>"
        then have "after_initial M \<alpha> \<noteq> after_initial M \<beta>"
          by auto
        then have "\<alpha> \<noteq> \<beta>"
          by auto

        obtain v w where "{v,w} = {\<alpha>,\<beta>}" and *:"(v \<in> \<Pi> \<and> w \<in> \<Pi>)
                                               \<or> (v \<in> \<Pi> \<and> w \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                                               \<or> (v \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<and> w \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
          using \<open>\<alpha> \<in> (\<Pi> \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})\<close>
                \<open>\<beta> \<in> (\<Pi> \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})\<close>
          by blast

        from * consider "(v \<in> \<Pi> \<and> w \<in> \<Pi>)" |
                        "(v \<in> \<Pi> \<and> w \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})" |
                        "(v \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<and> w \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
          by blast
        then have "(v,w) \<in> A \<union> B \<union> C \<or> (w,v) \<in> A \<union> B \<union> C"
        proof cases
          case 1
          then show ?thesis unfolding A by blast
        next
          case 2
          then show ?thesis
            using \<open>{V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<subseteq> {V q} \<union> {V q @ \<tau> | \<tau>. \<tau> \<in> \<X> q}\<close> a1
            unfolding A B \<Pi>
            by blast
        next
          case 3

          then obtain io io' where "v = V q @ io" and "io \<in> list.set (prefixes \<gamma>)"
                               and "w = V q @ io'" and "io' \<in> list.set (prefixes \<gamma>)"
            by auto
          
          have "v \<noteq> w"
            using \<open>{v,w} = {\<alpha>,\<beta>}\<close> \<open>\<alpha> \<noteq> \<beta>\<close> by force 
          then have "length io \<noteq> length io'" 
            using \<open>io \<in> list.set (prefixes \<gamma>)\<close> \<open>io' \<in> list.set (prefixes \<gamma>)\<close>
            unfolding \<open>v = V q @ io\<close> \<open>w = V q @ io'\<close> prefixes_set 
            by force
          
          have "io \<in> list.set (prefixes io') \<or> io' \<in> list.set (prefixes io)"
            using prefixes_prefixes[OF \<open>io \<in> list.set (prefixes \<gamma>)\<close> \<open>io' \<in> list.set (prefixes \<gamma>)\<close>] .
          then obtain u u' where "{u,u@u'} = {io,io'}"
                             and "u \<in> list.set (prefixes (u@u'))"
            unfolding prefixes_set by auto

          have "(u,u@u') = (io,io') \<or> (u,u@u') = (io',io)"
            using \<open>{u,u@u'} = {io,io'}\<close>
            by (metis empty_iff insert_iff) 

          have "u \<noteq> u@u'"
            using \<open>length io \<noteq> length io'\<close> \<open>{u,u@u'} = {io,io'}\<close> by force
          then have "u@u' \<noteq> []"
            by auto
          moreover have "\<And> w . w \<noteq> [] \<Longrightarrow> w \<in> list.set (prefixes \<gamma>) \<Longrightarrow> w \<in> \<X> q"
            using \<open>{V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<subseteq> {V q} \<union> {V q @ \<tau> | \<tau>. \<tau> \<in> \<X> q}\<close>
            by auto
          moreover have "u@u' \<in> list.set (prefixes \<gamma>)"
            using \<open>(u,u@u') = (io,io') \<or> (u,u@u') = (io',io)\<close> \<open>io \<in> list.set (prefixes \<gamma>)\<close> \<open>io' \<in> list.set (prefixes \<gamma>)\<close> by auto
          ultimately have "u@u' \<in> \<X> q"
            by blast
          then have "(V q @ u, V q @ (u@u')) \<in> C"
            unfolding C
            using a1 \<open>u \<in> list.set (prefixes (u@u'))\<close> by blast
          moreover have "(V q @ u, V q @ (u@u')) \<in> {(v,w), (w,v)}"
            unfolding \<open>v = V q @ io\<close> \<open>w = V q @ io'\<close> 
            using \<open>(u,u@u') = (io,io') \<or> (u,u@u') = (io',io)\<close> by auto
          ultimately show ?thesis
            by blast
        qed
        moreover have "(\<alpha>,\<beta>) = (v,w) \<or> (\<alpha>,\<beta>) = (w,v)"
          using \<open>{v,w} = {\<alpha>,\<beta>}\<close> 
          by (metis empty_iff insert_iff) 
        ultimately consider "(\<alpha>,\<beta>) \<in> A \<union> B \<union> C" | "(\<beta>,\<alpha>) \<in> A \<union> B \<union> C" 
          by blast

        then obtain \<omega> where "\<alpha>@\<omega> \<in> T" and "\<beta>@\<omega> \<in> T" and "distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>"
          using distinguishing_tests[OF _ \<open>\<alpha> \<in> L M\<close> \<open>\<beta> \<in> L M\<close> \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close>]
          using distinguishing_tests[OF _ \<open>\<beta> \<in> L M\<close> \<open>\<alpha> \<in> L M\<close> ] \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close>
          by (metis distinguishes_sym)

        show "\<not> converge I \<alpha> \<beta>"
          using distinguish_diverge[OF assms(1,2) \<open>distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>\<close> \<open>\<alpha>@\<omega> \<in> T\<close> \<open>\<beta>@\<omega> \<in> T\<close> \<open>\<alpha> \<in> L M\<close> \<open>\<beta> \<in> L M\<close> assms(9)] .
      qed
      then show ?thesis
        unfolding preserves_divergence.simps by blast
    qed

    moreover have "(L M \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) = L I \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
    proof -
      have "L M \<inter> \<Pi> = L I \<inter> \<Pi>"
        using \<open>\<Pi> \<subseteq> L I\<close> \<open>\<Pi> \<subseteq> L M\<close> 
        by blast
      moreover have "L M \<inter> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} = L I \<inter> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q}"
        using \<open>{ (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> T\<close> 
        using assms(9)
        by blast
      ultimately have *:"L M \<inter> (\<Pi> \<union> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q}) = L I \<inter> (\<Pi> \<union> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q})"
        by blast
      have **:"(\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<subseteq> \<Pi> \<union> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q}"
        using \<open>{V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<subseteq> {V q} \<union> {V q @ \<tau> | \<tau>. \<tau> \<in> \<X> q}\<close> 
        using a1 unfolding \<Pi> by blast
      
      have scheme: "\<And> A B C D . A \<inter> C = B \<inter> C \<Longrightarrow> D \<subseteq> C \<Longrightarrow> A \<inter> D = B \<inter> D"
        by (metis (no_types, opaque_lifting) Int_absorb1 inf_assoc) 
      show ?thesis 
        using scheme[OF * **] .
    qed

    ultimately show "(L M \<inter> (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) = L I \<inter> (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})) \<and> (preserves_divergence M I (V ` reachable_states M \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
      unfolding \<Pi> by blast
  qed
  ultimately show ?thesis
    by blast
qed

lemma h_condition_completeness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
  and     "satisfies_h_condition M V T m"
shows "(L M = L I) \<longleftrightarrow> (L M \<inter> T = L I \<inter> T)"
proof -
  have "is_state_cover_assignment M V" using assms(8) unfolding satisfies_h_condition_def Let_def by blast
  then show ?thesis
    using h_condition_satisfies_abstract_h_condition[OF assms]
    using abstract_h_condition_completeness[OF assms(1-7)]
    by blast
qed



subsection \<open>Helper Functions\<close>

fun language_up_to_length_with_extensions :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> (('c\<times>'a) list)) \<Rightarrow> 'b list \<Rightarrow> ('b\<times>'c) list list \<Rightarrow> nat \<Rightarrow> ('b \<times>'c) list list" 
  where
  "language_up_to_length_with_extensions q hM iM ex 0 = ex" |
  "language_up_to_length_with_extensions q hM iM ex (Suc k) = 
    ex @ concat (map (\<lambda>x .concat (map (\<lambda>(y,q') . (map (\<lambda>p . (x,y) # p)
                                                (language_up_to_length_with_extensions q' hM iM ex k)))
                            (hM q x))) 
                iM)"

lemma language_up_to_length_with_extensions_set :
  assumes "q \<in> states M"
  shows "List.set (language_up_to_length_with_extensions q (\<lambda> q x . sorted_list_of_set (h M (q,x))) (inputs_as_list M) ex k) 
          = {io@xy | io xy . io \<in> LS M q \<and> length io \<le> k \<and> xy \<in> List.set ex}"
  (is "?S1 q k = ?S2 q k")
proof 
  let ?hM = "(\<lambda> q x . sorted_list_of_set (h M (q,x)))"
  let ?iM = "inputs_as_list M"

  show "?S1 q k \<subseteq> ?S2 q k"
  proof 
    fix io assume "io \<in> ?S1 q k"
    then show "io \<in> ?S2 q k"
      using assms proof (induction k arbitrary: q io)
      case 0
      then obtain xy where "io = []@xy"
                       and "xy \<in> List.set ex"
                       and "[] \<in> LS M q"
        by auto
      then show ?case by force
    next
      case (Suc k)     

      show ?case proof (cases "io \<in> List.set ex")
        case True
        then have "io = []@io"
              and "io \<in> List.set ex"
              and "[] \<in> LS M q"
          using Suc.prems(2) by auto
        then show ?thesis by force
      next
        case False
        then obtain x where "x \<in> List.set ?iM"
                        and *: "io \<in> List.set (concat (map (\<lambda>(y,q') . map (\<lambda>p . (x,y) # p)
                                                                           (language_up_to_length_with_extensions q' ?hM ?iM ex k))
                                                       (?hM q x)))"
          using Suc.prems(1) 
          unfolding language_up_to_length_with_extensions.simps 
          by fastforce
        
        have "x \<in> inputs M"
          using \<open>x \<in> List.set ?iM\<close> inputs_as_list_set by auto
  
        obtain yq' where "(yq') \<in> List.set (?hM q x)"
                     and "io \<in> List.set ((\<lambda>(y,q') . (map (\<lambda>p . (x,y) # p)
                                                      (language_up_to_length_with_extensions q' ?hM ?iM ex k))) yq')"
          using concat_map_elem[OF *] by blast
        moreover obtain y q' where "yq' = (y,q')"
          using prod.exhaust_sel by blast
        ultimately have "(y,q') \<in> List.set (?hM q x)"
                    and "io \<in> List.set ((map (\<lambda>p . (x,y) # p) (language_up_to_length_with_extensions q' ?hM ?iM ex k)))"
          by auto
  
        
        have "(y,q') \<in> h M (q,x)"
          using \<open>(y,q') \<in> List.set (?hM q x)\<close>
          by (metis empty_iff empty_set sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.set_sorted_key_list_of_set)           
        then have "q' \<in> states M" 
              and "y \<in> outputs M"
              and "(q,x,y,q') \<in> transitions M"
          unfolding h_simps using fsm_transition_target fsm_transition_output by auto
  
        obtain p where "io = (x,y) # p"
                   and "p \<in> List.set (language_up_to_length_with_extensions q' ?hM ?iM ex k)"
          using \<open>io \<in> List.set ((map (\<lambda>p . (x,y) # p) (language_up_to_length_with_extensions q' ?hM ?iM ex k)))\<close>
          by force
        then have "p \<in> {io @ xy |io xy. io \<in> LS M q' \<and> length io \<le> k \<and> xy \<in> list.set ex}"
          using Suc.IH[OF _ \<open>q' \<in> states M\<close>] 
          by auto
        then obtain ioP xy where "p = ioP@xy"
                             and "ioP \<in> LS M q'" 
                             and "length ioP \<le> k" 
                             and "xy \<in> list.set ex"
          by blast
  
        have "io = ((x,y)#ioP)@xy"
          using \<open>io = (x,y) # p\<close> \<open>p = ioP@xy\<close> by auto
        moreover have "((x,y)#ioP) \<in> LS M q"
          using LS_prepend_transition[OF \<open>(q,x,y,q') \<in> transitions M\<close>] \<open>ioP \<in> LS M q'\<close>
          by auto
        moreover have "length ((x,y)#ioP) \<le> Suc k"
          using \<open>length ioP \<le> k\<close>
          by simp
        ultimately show ?thesis
          using \<open>xy \<in> list.set ex\<close> by blast
      qed
    qed
  qed
        
  show "?S2 q k \<subseteq> ?S1 q k"
  proof 
    fix io' assume "io' \<in> ?S2 q k"
    then show "io' \<in> ?S1 q k"
      using assms proof (induction k arbitrary: q io')
      case 0
      then show ?case by auto
    next
      case (Suc k)

      then obtain io xy where "io' = io@xy"
                           and "io \<in> LS M q" 
                           and "length io \<le> Suc k" 
                           and "xy \<in> list.set ex"
        by blast

      show ?case proof (cases io)
        case Nil
        then show ?thesis 
          using \<open>io \<in> LS M q\<close> \<open>xy \<in> list.set ex\<close>
          unfolding \<open>io' = io@xy\<close> 
          by auto
      next
        case (Cons a io'')
        
        obtain p where "path M q p" and "p_io p = io"
          using \<open>io \<in> LS M q\<close> by auto
        then obtain t p' where "p = t#p'"
          using Cons
          by blast 

        then have "t \<in> transitions M"
              and "t_source t = q"
              and "path M (t_target t) p'"
          using \<open>path M q p\<close> by auto

        have "a = (t_input t, t_output t)"
         and "p_io p' = io''"
          using \<open>p_io p = io\<close> Cons \<open>p = t#p'\<close> 
          by auto

        have "io'' \<in> LS M (t_target t)" 
          using \<open>p_io p' = io''\<close> \<open>path M (t_target t) p'\<close> by auto
        moreover have "length io'' \<le> k"
          using \<open>length io \<le> Suc k\<close> Cons by auto
        ultimately have "io''@xy \<in> {io @ xy |io xy. io \<in> LS M (t_target t) \<and> length io \<le> k \<and> xy \<in> list.set ex}"
          using \<open>xy \<in> list.set ex\<close> by blast

        moreover define f where f_def: "f = (\<lambda> q . (language_up_to_length_with_extensions q ?hM ?iM ex k))"
        ultimately have "io''@xy \<in> list.set (f (t_target t))"
          using Suc.IH[OF _ fsm_transition_target[OF \<open>t \<in> transitions M\<close>]]
          by auto
        moreover have "(t_output t, t_target t) \<in> list.set (?hM q (t_input t))"
        proof -
          have "(h M (q,t_input t)) \<subseteq> image (snd \<circ> snd) (transitions M)"
            unfolding h_simps by force
          then have "finite (h M (q,t_input t))"
            using fsm_transitions_finite
            using finite_surj by blast 
          moreover have "(t_output t, t_target t) \<in> h M (q,t_input t)"
            using \<open>t \<in> transitions M\<close> \<open>t_source t = q\<close> 
            by auto
          ultimately show ?thesis 
            by simp
        qed
        ultimately have "a#(io''@xy) \<in> list.set (concat (map (\<lambda>(y,q') . (map (\<lambda>p . ((t_input t),y) # p)
                                                (f q')))
                            (?hM q (t_input t))))"
          unfolding \<open>a = (t_input t, t_output t)\<close> 
          by force 
        moreover have "t_input t \<in> list.set ?iM"
          using fsm_transition_input[OF \<open>t \<in> transitions M\<close>] inputs_as_list_set by auto
        ultimately have "a#(io''@xy) \<in> list.set (concat (map (\<lambda>x .concat (map (\<lambda>(y,q') . (map (\<lambda>p . (x,y) # p)
                                                (f q')))
                            (?hM q x))) 
                ?iM))"
          by force
        then have "a#(io''@xy) \<in> ?S1 q (Suc k)"
          unfolding language_up_to_length_with_extensions.simps
          unfolding f_def by force
        then show ?thesis
          unfolding \<open>io' = io@xy\<close> Cons by simp
      qed
    qed
  qed
qed



fun h_extensions :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b \<times>'c) list list" where
  "h_extensions M q k = (let 
    iM = inputs_as_list M;
    ex = map (\<lambda>xy . [xy]) (List.product iM (outputs_as_list M));
    hM = (\<lambda> q x . sorted_list_of_set (h M (q,x)))
  in
    language_up_to_length_with_extensions q hM iM ex k)"


lemma h_extensions_set :
  assumes "q \<in> states M"
shows "List.set (h_extensions M q k) = {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> k \<and> x \<in> inputs M \<and> y \<in> outputs M}"
proof -

  define ex where ex: "ex = map (\<lambda>xy . [xy]) (List.product (inputs_as_list M) (outputs_as_list M))"
  then have "List.set ex = {[xy] | xy . xy \<in> list.set (List.product (inputs_as_list M) (outputs_as_list M))}"
    by auto
  then have *: "List.set ex = {[(x,y)] | x y . x \<in> inputs M \<and> y \<in> outputs M}"
    using inputs_as_list_set[of M] outputs_as_list_set[of M]
    by auto

  have "h_extensions M q k = language_up_to_length_with_extensions q (\<lambda> q x . sorted_list_of_set (h M (q,x))) (inputs_as_list M) ex k"
    unfolding ex h_extensions.simps Let_def 
    by auto
  then have "List.set (h_extensions M q k) = {io @ xy |io xy. io \<in> LS M q \<and> length io \<le> k \<and> xy \<in> list.set ex}"
    using language_up_to_length_with_extensions_set[OF assms] 
    by auto
  then show ?thesis
    unfolding * by blast
qed



fun paths_up_to_length_with_targets :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> (('a,'b,'c) transition list)) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> (('a,'b,'c) path \<times> 'a) list" 
  where
  "paths_up_to_length_with_targets q hM iM 0 = [([],q)]" |
  "paths_up_to_length_with_targets q hM iM (Suc k) = 
    ([],q) # (concat (map (\<lambda>x .concat (map (\<lambda>t . (map (\<lambda>(p,q). (t # p,q))
                                                (paths_up_to_length_with_targets (t_target t) hM iM k)))
                            (hM q x))) 
                iM))"

lemma paths_up_to_length_with_targets_set :
  assumes "q \<in> states M"
  shows "List.set (paths_up_to_length_with_targets q (\<lambda> q x . map (\<lambda>(y,q') . (q,x,y,q')) (sorted_list_of_set (h M (q,x)))) (inputs_as_list M) k) 
          = {(p, target q p) | p . path M q p \<and> length p \<le> k}"
  (is "?S1 q k = ?S2 q k")
proof 
  let ?hM = "(\<lambda> q x . map (\<lambda>(y,q') . (q,x,y,q')) (sorted_list_of_set (h M (q,x))))"
  let ?iM = "inputs_as_list M"

  have hM: "\<And> q x . list.set (?hM q x) = {(q,x,y,q') | y q' . (q,x,y,q') \<in> transitions M}"
  proof -
    fix q x show "list.set (?hM q x) = {(q,x,y,q') | y q' . (q,x,y,q') \<in> transitions M}"
    proof 
      show "list.set (?hM q x) \<subseteq> {(q,x,y,q') | y q' . (q,x,y,q') \<in> transitions M}"
      proof 
        fix t assume "t \<in> list.set (?hM q x)"
        then obtain y q' where "t = (q,x,y,q')" and "(y,q') \<in> list.set (sorted_list_of_set (h M (q,x)))"
          by auto
        then have "(y,q') \<in> h M (q,x)"
          by (metis empty_iff empty_set sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.set_sorted_key_list_of_set)
        then show "t \<in> {(q,x,y,q') | y q' . (q,x,y,q') \<in> transitions M}"
          unfolding h_simps \<open>t = (q,x,y,q')\<close> by blast
      qed

      show "{(q,x,y,q') | y q' . (q,x,y,q') \<in> transitions M} \<subseteq> list.set (?hM q x)"
      proof 
        fix t assume "t \<in> {(q,x,y,q') | y q' . (q,x,y,q') \<in> transitions M}"
        then obtain y q' where "t = (q,x,y,q')" and "(q,x,y,q') \<in> {(q,x,y,q') | y q' . (q,x,y,q') \<in> transitions M}"
          by auto
        then have "(y,q') \<in> h M (q,x)"
          by auto

        have "(h M (q,x)) \<subseteq> image (snd \<circ> snd) (transitions M)"
          unfolding h_simps by force
        then have "finite (h M (q,x))"
          using fsm_transitions_finite
          using finite_surj by blast 
        then have "(y,q') \<in> list.set (sorted_list_of_set (h M (q,x)))"
          using \<open>(y,q') \<in> h M (q,x)\<close> by auto
        then show "t \<in> list.set (?hM q x)"
          unfolding \<open>t = (q,x,y,q')\<close> by auto
      qed
    qed
  qed

  show "?S1 q k \<subseteq> ?S2 q k"
  proof 
    fix pq assume "pq \<in> ?S1 q k"
    then show "pq \<in> ?S2 q k"
    using assms proof (induction k arbitrary: q pq)
      case 0
      then show ?case by force
    next
      case (Suc k)     

      obtain p q' where "pq = (p,q')"
        by fastforce

      show ?case proof (cases p)
        case Nil
        have "q' = q"
          using Suc.prems(1) 
          unfolding \<open>pq = (p,q')\<close> Nil paths_up_to_length_with_targets.simps 
          by force
        then show ?thesis 
          unfolding \<open>pq = (p,q')\<close> Nil using Suc.prems(2) by auto
      next
        case (Cons t p')

        obtain x where "x \<in> list.set ?iM"
                   and *:"(t#p',q') \<in> list.set (concat (map (\<lambda>t . (map (\<lambda>(p,q). (t # p,q))
                                                        (paths_up_to_length_with_targets (t_target t) ?hM ?iM k)))
                                                (?hM q x)))"
          using Suc.prems(1) unfolding \<open>pq = (p,q')\<close> Cons paths_up_to_length_with_targets.simps 
          by fastforce

        have "x \<in> inputs M"
          using \<open>x \<in> List.set ?iM\<close> inputs_as_list_set by auto

        have "t \<in> list.set (?hM q x)"
         and **:"(p',q') \<in> list.set (paths_up_to_length_with_targets (t_target t) ?hM ?iM k)"
          using * by auto

        have "t \<in> transitions M" and "t_source t = q"
          using \<open>t \<in> list.set (?hM q x)\<close> hM by auto

        have "q' = target (t_target t) p'"
         and "path M (t_target t) p'"
         and "length p' \<le> k"
          using Suc.IH[OF ** fsm_transition_target[OF \<open>t \<in> transitions M\<close>]]
          by auto

        have "q' = target q p"
          unfolding Cons using \<open>q' = target (t_target t) p'\<close> by auto
        moreover have "path M q p"
          unfolding Cons using \<open>path M (t_target t) p'\<close> \<open>t \<in> transitions M\<close> \<open>t_source t = q\<close> by auto
        moreover have "length p \<le> Suc k"
          unfolding Cons using \<open>length p' \<le> k\<close> by auto
        ultimately show ?thesis 
          unfolding \<open>pq = (p,q')\<close> by blast
      qed
    qed
  qed     

  show "?S2 q k \<subseteq> ?S1 q k"
  proof 
    fix pq assume "pq \<in> ?S2 q k"

    obtain p q' where "pq = (p,q')"
      by fastforce

    show "pq \<in> ?S1 q k"
    using assms \<open>pq \<in> ?S2 q k\<close> unfolding \<open>pq = (p,q')\<close> proof (induction k arbitrary: q p q')
      case 0
      then show ?case by force
    next
      case (Suc k)  
      then have "q' = target q p"
            and "path M q p"
            and "length p \<le> Suc k"
        by auto

      show ?case proof (cases p)
        case Nil
        then have "q' = q"
          using Suc.prems(2) by auto
        then show ?thesis unfolding Nil by auto
      next
        case (Cons t p')

        then have "q' = target q (t#p')"
            and "path M q (t#p')"
            and "length (t#p') \<le> Suc k"
          using Suc.prems(2)
          by auto 

        have "t \<in> transitions M" and "t_source t = q"
          using \<open>path M q (t#p')\<close> by auto
        then have "t \<in> list.set (?hM q (t_input t))"
          unfolding hM
          by (metis (mono_tags, lifting) mem_Collect_eq prod.exhaust_sel) 

        have "t_input t \<in> list.set ?iM"
          using fsm_transition_input[OF \<open>t \<in> transitions M\<close>] inputs_as_list_set by auto


        have "q' = target (t_target t) p'"
          using \<open>q' = target q (t#p')\<close> by auto
        moreover have "path M (t_target t) p'"
          using \<open>path M q (t#p')\<close> by auto
        moreover have "length p' \<le> k"
          using \<open>length (t#p') \<le> Suc k\<close> by auto
        ultimately have "(p',q') \<in> ?S2 (t_target t) k"
          by blast
        moreover define f where f_def: "f = (\<lambda>q . (paths_up_to_length_with_targets q ?hM ?iM k))"
        ultimately have "(p',q') \<in> list.set (f (t_target t))"
          using Suc.IH[OF fsm_transition_target[OF \<open>t \<in> transitions M\<close>]]
          by blast
        then have **: "(t#p',q') \<in> list.set ((map (\<lambda>(p,q). (t # p,q)) (f (t_target t))))"
          by auto

        have scheme: "\<And> x y ys f . x \<in> list.set (f y) \<Longrightarrow> y \<in> list.set ys \<Longrightarrow> x \<in> list.set (concat (map f ys))"
          by auto

        have "(t#p',q') \<in> list.set (concat (map (\<lambda>t . (map (\<lambda>(p,q). (t # p,q))
                                                (f (t_target t))))
                                          (?hM q (t_input t))))"
          using scheme[of "(t#p',q')" "\<lambda> t. (map (\<lambda>(p,q). (t # p,q)) (f (t_target t)))", OF ** \<open>t \<in> list.set (?hM q (t_input t))\<close>]
          .

        then have "(t#p',q') \<in> list.set (concat
          (map (\<lambda>x. concat
                     (map (\<lambda>t. map (\<lambda>(p, y). (t # p, y))
                                (f (t_target t)))
                       (map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x))))))
            (inputs_as_list M)))"
          using \<open>t_input t \<in> list.set ?iM\<close> by force

        then show ?thesis
          unfolding paths_up_to_length_with_targets.simps f_def Cons by auto
      qed
    qed
  qed
qed



fun pairs_to_distinguish :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a \<Rightarrow> (('a,'b,'c) path \<times> 'a) list) \<Rightarrow> 'a list \<Rightarrow> ((('b \<times> 'c) list \<times> 'a) \<times> (('b \<times> 'c) list \<times> 'a)) list" where
  "pairs_to_distinguish M V \<X>' rstates = (let 
    \<Pi> = map (\<lambda>q . (V q,q)) rstates;
    A = List.product \<Pi> \<Pi>;
    B = List.product \<Pi> (concat (map (\<lambda>q . map (\<lambda> (\<tau>,q') . ((V q)@ p_io \<tau>,q')) (\<X>' q)) rstates));
    C = concat (map (\<lambda>q . concat (map (\<lambda> (\<tau>',q'). map (\<lambda>\<tau>'' . (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q'))) (prefixes \<tau>')) (\<X>' q))) rstates) 
  in 
    filter (\<lambda>((\<alpha>,q'),(\<beta>,q'')) . q' \<noteq> q'') (A@B@C))"

lemma pairs_to_distinguish_elems :
  assumes "observable M"
  and     "is_state_cover_assignment M V"
  and     "list.set rstates = reachable_states M"
  and     "\<And> q p q' . q \<in> reachable_states M \<Longrightarrow> (p,q') \<in> list.set (\<X>' q) \<longleftrightarrow> path M q p \<and> target q p = q' \<and> length p \<le> m-n+1"
  and     "((\<alpha>,q1),(\<beta>,q2)) \<in> list.set (pairs_to_distinguish M V \<X>' rstates)"
  
shows "q1 \<in> states M" and "q2 \<in> states M" and "q1 \<noteq> q2"
  and "\<alpha> \<in> L M" and "\<beta> \<in> L M" and "q1 = after_initial M \<alpha>" and "q2 = after_initial M \<beta>"
proof -

  define \<Pi> where \<Pi>: "\<Pi> = map (\<lambda>q . (V q,q)) rstates"
  moreover define A where A: "A = List.product \<Pi> \<Pi>"
  moreover define B where B: "B = List.product \<Pi> (concat (map (\<lambda>q . map (\<lambda> (\<tau>,q') . ((V q)@ p_io \<tau>,q')) (\<X>' q)) rstates))"
  moreover define C where C: "C = concat (map (\<lambda>q . concat (map (\<lambda> (\<tau>',q'). map (\<lambda>\<tau>'' . (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q'))) (prefixes \<tau>')) (\<X>' q))) rstates)"
  ultimately have pairs_def: "pairs_to_distinguish M V \<X>' rstates = filter (\<lambda>((\<alpha>,q'),(\<beta>,q'')) . q' \<noteq> q'') (A@B@C)"
    unfolding pairs_to_distinguish.simps Let_def by force

  show "q1 \<noteq> q2"
    using assms(5) unfolding pairs_def by auto

  consider "((\<alpha>,q1),(\<beta>,q2)) \<in> list.set A" | "((\<alpha>,q1),(\<beta>,q2)) \<in> list.set B" | "((\<alpha>,q1),(\<beta>,q2)) \<in> list.set C"
    using assms(5) unfolding pairs_def by auto
  then have "q1 \<in> states M \<and> q2 \<in> states M \<and> \<alpha> \<in> L M \<and> \<beta> \<in> L M \<and> q1 = after_initial M \<alpha> \<and> q2 = after_initial M \<beta>"
  proof cases
    case 1
    then have "(\<alpha>,q1) \<in> list.set \<Pi>" and "(\<beta>,q2) \<in> list.set \<Pi>"
      unfolding A by auto
    then show ?thesis unfolding \<Pi> using assms(3)
      using reachable_state_is_state 
      using state_cover_assignment_after[OF assms(1,2)]
      by force
  next
    case 2
    then have "(\<alpha>,q1) \<in> list.set \<Pi>" and "(\<beta>,q2) \<in> list.set (concat (map (\<lambda>q . map (\<lambda> (\<tau>,q') . ((V q)@ p_io \<tau>,q')) (\<X>' q)) rstates))"
      unfolding B by auto
     
    then obtain q where "q \<in> reachable_states M"
                    and "(\<beta>,q2) \<in> list.set (map (\<lambda> (\<tau>,q') . ((V q)@ p_io \<tau>,q')) (\<X>' q))"
      unfolding assms(3)[symmetric] by (meson concat_map_elem)
    then obtain \<tau> where "(\<tau>,q2) \<in> list.set (\<X>' q)" and "\<beta> = (V q)@ p_io \<tau>"
      by force
    then have "path M q \<tau>" and "target q \<tau> = q2" 
      unfolding assms(4)[OF \<open>q \<in> reachable_states M\<close>] by auto
    moreover obtain p where "path M (initial M) p" and "p_io p = V q" and "target (initial M) p = q"
      using state_cover_assignment_after[OF assms(1,2) \<open>q \<in> reachable_states M\<close>]
            after_path[OF assms(1)]
      by auto
    ultimately have "path M (initial M) (p@\<tau>)" and "target (initial M) (p@\<tau>) = q2" and "p_io (p@\<tau>) = \<beta>"
      unfolding \<open>\<beta> = (V q)@ p_io \<tau>\<close> by auto
    then have "q2 = after_initial M \<beta>"
      by (metis (mono_tags, lifting) after_path assms(1))
    moreover have "\<beta> \<in> L M"
      using \<open>path M (initial M) (p@\<tau>)\<close> \<open>p_io (p@\<tau>) = \<beta>\<close>
      by (metis (mono_tags, lifting) language_state_containment) 
    moreover have "q2 \<in> states M"
      by (metis \<open>path M q \<tau>\<close> \<open>target q \<tau> = q2\<close> path_target_is_state)
    moreover have "q1 \<in> states M"
      using \<open>(\<alpha>,q1) \<in> list.set \<Pi>\<close> assms(3) reachable_state_is_state unfolding \<Pi> by fastforce
    moreover have "\<alpha> \<in> L M" and "q1 = after_initial M \<alpha>"
      using \<open>(\<alpha>,q1) \<in> list.set \<Pi>\<close> assms(3) state_cover_assignment_after[OF assms(1,2)] unfolding \<Pi> by auto
    ultimately show ?thesis 
      by blast
  next
    case 3
    then obtain q where "q \<in> reachable_states M"
                    and "((\<alpha>,q1),(\<beta>,q2)) \<in> list.set  (concat (map (\<lambda> (\<tau>',q'). map (\<lambda>\<tau>'' . (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q'))) (prefixes \<tau>')) (\<X>' q)))"
      unfolding assms(3)[symmetric] C by force
    then obtain \<tau>' where "(\<tau>',q2) \<in> list.set (\<X>' q)" and "\<beta> = V q @ p_io \<tau>'"
                     and "((\<alpha>,q1),(\<beta>,q2)) \<in> list.set (map (\<lambda>\<tau>'' . (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q2))) (prefixes \<tau>'))"
      by force
    then obtain \<tau>'' where "\<tau>'' \<in> list.set (prefixes \<tau>')" and "\<alpha> = V q @ p_io \<tau>''"
                      and "((\<alpha>,q1),(\<beta>,q2)) = (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q2))"
      by auto
    then have "q1 = target q \<tau>''"
      by auto

    have "path M q \<tau>'" and "target q \<tau>' = q2"
      using \<open>(\<tau>',q2) \<in> list.set (\<X>' q)\<close> unfolding assms(4)[OF \<open>q \<in> reachable_states M\<close>] by simp+
    then have "path M q \<tau>''"
      using \<open>\<tau>'' \<in> list.set (prefixes \<tau>')\<close>
      using prefixes_set_ob by force 
    then have "q1 \<in> states M"
      using path_target_is_state unfolding \<open>q1 = target q \<tau>''\<close> by force
    moreover have "\<alpha> \<in> L M" 
      unfolding \<open>\<alpha> = V q @ p_io \<tau>''\<close> 
      using state_cover_assignment_after[OF assms(1,2)]
      by (metis (mono_tags, lifting) \<open>path M q \<tau>''\<close> \<open>q \<in> reachable_states M\<close> assms(1) language_state_containment observable_after_language_append)
    moreover have "q1 = after_initial M \<alpha>"
      unfolding \<open>\<alpha> = V q @ p_io \<tau>''\<close> 
      using state_cover_assignment_after[OF assms(1,2) \<open>q \<in> reachable_states M\<close>]
      by (metis (mono_tags, lifting) \<open>\<alpha> = V q @ p_io \<tau>''\<close> \<open>path M q \<tau>''\<close>  \<open>q1 = target q \<tau>''\<close> after_path after_split assms(1) calculation(2))
    moreover have "q2 \<in> states M"
      using \<open>path M q \<tau>'\<close> \<open>target q \<tau>' = q2\<close> path_target_is_state by force
    moreover have "\<beta> \<in> L M"
      by (metis (mono_tags, lifting) \<open>\<alpha> = V q @ p_io \<tau>''\<close> \<open>\<beta> = V q @ p_io \<tau>'\<close> \<open>path M q \<tau>'\<close> \<open>q \<in> reachable_states M\<close> assms(1) assms(2) calculation(2) is_state_cover_assignment_observable_after language_prefix language_state_containment observable_after_language_append)
    moreover have "q2 = after_initial M \<beta>"
      unfolding \<open>\<beta> = V q @ p_io \<tau>'\<close>
      using state_cover_assignment_after[OF assms(1,2) \<open>q \<in> reachable_states M\<close>]
      by (metis (mono_tags, lifting) \<open>\<beta> = V q @ p_io \<tau>'\<close> \<open>path M q \<tau>'\<close> \<open>target q \<tau>' = q2\<close> after_path after_split assms(1) calculation(5))
    ultimately show ?thesis 
      by blast
  qed
  then show "q1 \<in> states M" and "q2 \<in> states M" and "\<alpha> \<in> L M" and "\<beta> \<in> L M" and "q1 = after_initial M \<alpha>" and "q2 = after_initial M \<beta>"
    by auto
qed


lemma pairs_to_distinguish_containment :
  assumes "observable M"
  and     "is_state_cover_assignment M V"
  and     "list.set rstates = reachable_states M"
  and     "\<And> q p q' . q \<in> reachable_states M \<Longrightarrow> (p,q') \<in> list.set (\<X>' q) \<longleftrightarrow> path M q p \<and> target q p = q' \<and> length p \<le> m-n+1"
  and     "(\<alpha>,\<beta>) \<in> (V ` reachable_states M) \<times> (V ` reachable_states M)
                  \<union> (V ` reachable_states M) \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M}}
                  \<union> (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M} . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>})"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M"
  and     "after_initial M \<alpha> \<noteq> after_initial M \<beta>"
shows "((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set (pairs_to_distinguish M V \<X>' rstates)"
proof -

  let ?\<X> = "\<lambda> q . {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M}"

  define \<Pi> where \<Pi>: "\<Pi> = map (\<lambda>q . (V q,q)) rstates"
  moreover define A where A: "A = List.product \<Pi> \<Pi>"
  moreover define B where B: "B =List.product \<Pi> (concat (map (\<lambda>q . map (\<lambda> (\<tau>,q') . ((V q)@ p_io \<tau>,q')) (\<X>' q)) rstates))"
  moreover define C where C: "C = concat (map (\<lambda>q . concat (map (\<lambda> (\<tau>',q'). map (\<lambda>\<tau>'' . (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q'))) (prefixes \<tau>')) (\<X>' q))) rstates)"
  ultimately have pairs_def: "pairs_to_distinguish M V \<X>' rstates = filter (\<lambda>((\<alpha>,q'),(\<beta>,q'')) . q' \<noteq> q'') (A@B@C)"
    unfolding pairs_to_distinguish.simps Let_def by force


  have V_target: "\<And>q . q \<in> reachable_states M \<Longrightarrow> after_initial M (V q) = q"
  proof -
    fix q assume "q \<in> reachable_states M"
    then have "q \<in> io_targets M (V q) (initial M)"
      using assms(2) by auto
    then have "V q \<in> L M"
      unfolding io_targets.simps
      by force 
    
    show "after_initial M (V q) = q"
      by (meson \<open>q \<in> reachable_states M\<close> assms(1) assms(2) is_state_cover_assignment_observable_after)
  qed

  have V_path: "\<And> io q . q \<in> reachable_states M \<Longrightarrow> io \<in> LS M q \<Longrightarrow> \<exists> p . path M q p \<and> p_io p = io \<and> target q p = after_initial M ((V q)@io)"
  proof -
    fix io q assume "q \<in> reachable_states M" and "io \<in> LS M q"
    then have "after_initial M (V q) = q" 
      using V_target by auto
    then have "((V q)@io) \<in> L M"
      using \<open>io \<in> LS M q\<close>
      by (meson \<open>q \<in> reachable_states M\<close> assms(2) is_state_cover_assignment.simps language_io_target_append) 
    then obtain p where "path M (initial M) p" and "p_io p = ((V q)@io)"
      by auto
    moreover have "target (initial M) p \<in> io_targets M ((V q)@io) (initial M)"
      using calculation unfolding io_targets.simps by force
    ultimately have "target (initial M) p = after_initial M ((V q)@io)"
      using observable_io_targets[OF \<open>observable M\<close> \<open>((V q)@io) \<in> L M\<close>] 
      unfolding io_targets.simps
      by (metis (mono_tags, lifting) after_path assms(1)) 

    have "path M (FSM.initial M) (take (length (V q)) p)"
     and "p_io (take (length (V q)) p) = V q"
     and "path M (target (FSM.initial M) (take (length (V q)) p)) (drop (length (V q)) p)"
     and "p_io (drop (length (V q)) p) = io"
      using path_io_split[OF \<open>path M (initial M) p\<close> \<open>p_io p = ((V q)@io)\<close>]
      by auto

    have "target (initial M) p = target (target (FSM.initial M) (take (length (V q)) p)) (drop (length (V q)) p)"
      by (metis append_take_drop_id path_append_target)
    moreover have "(target (FSM.initial M) (take (length (V q)) p)) = q"
      using \<open>p_io (take (length (V q)) p) = V q\<close> \<open>after_initial M (V q) = q\<close>
      using \<open>path M (FSM.initial M) (take (length (V q)) p)\<close> after_path assms(1) by fastforce 
    ultimately have "target q (drop (length (V q)) p) = after_initial M ((V q)@io)"
      using \<open>target (initial M) p = after_initial M ((V q)@io)\<close>
      by presburger
    then show "\<exists> p . path M q p \<and> p_io p = io \<and> target q p = after_initial M ((V q)@io)"
      using \<open>path M (target (FSM.initial M) (take (length (V q)) p)) (drop (length (V q)) p)\<close> \<open>p_io (drop (length (V q)) p) = io\<close>
      unfolding \<open>(target (FSM.initial M) (take (length (V q)) p)) = q\<close>
      by blast
  qed
      


  consider "(\<alpha>,\<beta>) \<in> (V ` reachable_states M) \<times> (V ` reachable_states M)" |
           "(\<alpha>,\<beta>) \<in> (V ` reachable_states M) \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M}}" |
           "(\<alpha>,\<beta>) \<in> (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M} . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>})"
    using assms(5) by blast
  then show ?thesis proof cases
    case 1
    then have "\<alpha> \<in> V ` reachable_states M"
          and "\<beta> \<in> V ` reachable_states M"
      by auto
    
    have "(\<alpha>,after_initial M \<alpha>) \<in> list.set (map (\<lambda>q . (V q,q)) rstates)"
      using \<open>\<alpha> \<in> V ` reachable_states M\<close> V_target assms(3) by force
    moreover have "(\<beta>,after_initial M \<beta>) \<in> list.set (map (\<lambda>q . (V q,q)) rstates)"
      using \<open>\<beta> \<in> V ` reachable_states M\<close> V_target assms(3) by force
    ultimately have "((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set A"
      unfolding \<Pi> A by auto
    then show ?thesis
      using \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close>
      unfolding pairs_def by auto
  next
    case 2
    then have "\<alpha> \<in> V ` reachable_states M"
          and "\<beta> \<in> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M}}"
      by auto

    have "(\<alpha>,after_initial M \<alpha>) \<in> list.set (map (\<lambda>q . (V q,q)) rstates)"
      using \<open>\<alpha> \<in> V ` reachable_states M\<close> V_target assms(3) by force

    obtain q io x y where "\<beta> = (V q) @ (io@[(x,y)])"
                 and "q \<in> reachable_states M"
                 and "length io \<le> m-n"
      using \<open>\<beta> \<in> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M}}\<close>
      by blast

    have "(V q) @ (io@[(x,y)]) \<in> L M"
      using \<open>\<beta> \<in> L M\<close> unfolding \<open>\<beta> = (V q) @ (io@[(x,y)])\<close> by simp


    have "q \<in> io_targets M (V q) (initial M)"
      using \<open>q \<in> reachable_states M\<close> assms(2) by auto 
    then have "io@[(x,y)] \<in> LS M q"
      unfolding \<open>\<beta> = (V q) @ (io@[(x,y)])\<close>
      using observable_io_targets_language[OF \<open>(V q) @ (io@[(x,y)]) \<in> L M\<close> \<open>observable M\<close>]
      by auto
    then obtain p where "path M q p" 
                    and "p_io p = io@[(x,y)]"
                    and "target q p = after_initial M \<beta>"
      using V_path[OF \<open>q \<in> reachable_states M\<close>]
      unfolding \<open>\<beta> = (V q) @ (io@[(x,y)])\<close>
      by blast
    moreover have "length p \<le> m-n+1"
      using calculation \<open>length io \<le> m-n\<close>
      by (metis (no_types, lifting) Suc_le_mono add.commute length_append_singleton length_map plus_1_eq_Suc) 
    ultimately have "(p,after_initial M \<beta>) \<in> list.set (\<X>' q)"
      using assms(4)[OF \<open>q \<in> reachable_states M\<close>] 
      by auto
    then have "(\<beta>,after_initial M \<beta>) \<in> list.set (map (\<lambda> (\<tau>,q') . ((V q)@ p_io \<tau>,q')) (\<X>' q))"
      unfolding \<open>\<beta> = (V q) @ (io@[(x,y)])\<close> using \<open>p_io p = io@[(x,y)]\<close> by force
    moreover have "q \<in> list.set rstates"
      using \<open>q \<in> reachable_states M\<close> assms(3) by auto
    ultimately have "(\<beta>,after_initial M \<beta>) \<in> list.set (concat (map (\<lambda>q . map (\<lambda> (\<tau>,q') . ((V q)@ p_io \<tau>,q')) (\<X>' q)) rstates))"
      by force
    then have "((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set B"
      using \<open>(\<alpha>,after_initial M \<alpha>) \<in> list.set (map (\<lambda>q . (V q,q)) rstates)\<close>
      unfolding B \<Pi> 
      by auto
    then show ?thesis
      using \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close>
      unfolding pairs_def by auto
  next
    case 3
    then obtain q \<tau>' io x y where "q \<in> reachable_states M"
                                and "io \<in> LS M q" 
                                and "length io \<le> m - n" 
                                and "x \<in> FSM.inputs M" 
                                and "y \<in> FSM.outputs M"
                                and "\<alpha> = V q @ \<tau>'" 
                                and "\<tau>' \<in> list.set (prefixes ( io @ [(x, y)]))"
                                and "\<beta> = V q @ io @ [(x, y)]"
      by blast



    have "(V q) @ (io@[(x,y)]) \<in> L M"
      using \<open>\<beta> \<in> L M\<close> unfolding \<open>\<beta> = (V q) @ (io@[(x,y)])\<close> by simp
    

    have "q \<in> io_targets M (V q) (initial M)"
      using \<open>q \<in> reachable_states M\<close> assms(2) by auto 
    then have "io@[(x,y)] \<in> LS M q"
      unfolding \<open>\<beta> = (V q) @ (io@[(x,y)])\<close>
      using observable_io_targets_language[OF \<open>(V q) @ (io@[(x,y)]) \<in> L M\<close> \<open>observable M\<close>]
      by auto
    then obtain p where "path M q p" 
                    and "p_io p = io@[(x,y)]"
                    and "target q p = after_initial M \<beta>"
      using V_path[OF \<open>q \<in> reachable_states M\<close>]
      unfolding \<open>\<beta> = (V q) @ (io@[(x,y)])\<close>
      by blast
    moreover have "length p \<le> m-n+1"
      using calculation \<open>length io \<le> m-n\<close>
      by (metis (no_types, lifting) Suc_le_mono add.commute length_append_singleton length_map plus_1_eq_Suc) 
    ultimately have "(p,after_initial M \<beta>) \<in> list.set (\<X>' q)"
      using assms(4)[OF \<open>q \<in> reachable_states M\<close>] 
      by auto
    
    have "q \<in> list.set rstates"
      using \<open>q \<in> reachable_states M\<close> assms(3) by auto

    let ?\<tau> = "take (length \<tau>') (io@[(x,y)])"
    obtain \<tau>'' where "io @ [(x, y)] = \<tau>' @ \<tau>''"
      using \<open>\<tau>' \<in> list.set (prefixes ( io @ [(x, y)]))\<close>
      using prefixes_set_ob by blast 
    then have "\<tau>' = ?\<tau>"
      by auto
    then have "io@[(x,y)] = \<tau>' @ (drop (length \<tau>') (io@[(x,y)]))"
      by (metis append_take_drop_id)
    then have "p_io p = \<tau>' @ (drop (length \<tau>') (io@[(x,y)]))"
      using \<open>p_io p = io@[(x,y)]\<close>
      by simp
    
    have "path M q (take (length \<tau>') p)"
     and "p_io (take (length \<tau>') p) = \<tau>'"
      using path_io_split(1,2)[OF \<open>path M q p\<close> \<open>p_io p = \<tau>' @ (drop (length \<tau>') (io@[(x,y)]))\<close>]
      by auto
    then have "\<tau>' \<in> LS M q"
      using language_intro by fastforce

    have "(V q) @ \<tau>' \<in> L M"
      using \<open>(V q) @ (io@[(x,y)]) \<in> L M\<close> unfolding \<open>io @ [(x, y)] = \<tau>' @ \<tau>''\<close> 
      using language_prefix[of "V q @ \<tau>'" \<tau>'' M "initial M"] 
      by auto 
      
      
    have "(FSM.after M (FSM.initial M) (V q)) = q"
      using V_target \<open>q \<in> reachable_states M\<close> by blast
    have "target q (take (length \<tau>') p) = after_initial M \<alpha>"
      using observable_after_target[OF \<open>observable M\<close> \<open>(V q) @ \<tau>' \<in> L M\<close> _ \<open>p_io (take (length \<tau>') p) = \<tau>'\<close>] 
      using \<open>path M q (take (length \<tau>') p)\<close>
      unfolding \<open>(FSM.after M (FSM.initial M) (V q)) = q\<close> \<open>\<alpha> = V q @ \<tau>'\<close>
      by auto

    have "p = (take (length \<tau>') p)@(drop (length \<tau>') p)"
      by simp
    then have "(take (length \<tau>') p) \<in> list.set (prefixes p)"
      unfolding prefixes_set
      by (metis (mono_tags, lifting) mem_Collect_eq) 


    have "(((V q)@ p_io (take (length \<tau>') p), target q (take (length \<tau>') p)),((V q)@ p_io p,after_initial M \<beta>)) \<in> list.set ( (\<lambda>(\<tau>', q'). map (\<lambda>\<tau>''. ((V q @ p_io \<tau>'', target q \<tau>''), V q @ p_io \<tau>', q')) (prefixes \<tau>')) (p,after_initial M \<beta>))"
      using \<open>(take (length \<tau>') p) \<in> list.set (prefixes p)\<close>
      by auto
    then have *: "((\<alpha>, after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set ( (\<lambda>(\<tau>', q'). map (\<lambda>\<tau>''. ((V q @ p_io \<tau>'', target q \<tau>''), V q @ p_io \<tau>', q')) (prefixes \<tau>')) (p,after_initial M \<beta>))"
      unfolding \<open>\<alpha> = V q @ \<tau>'\<close> 
                \<open>\<beta> = V q @ io @ [(x, y)]\<close> 
                \<open>target q (take (length \<tau>') p) = after_initial M \<alpha>\<close> 
                \<open>p_io (take (length \<tau>') p) = \<tau>'\<close>
                \<open>p_io p = io@[(x,y)]\<close> .

    have scheme: "\<And> x y ys f . x \<in> list.set (f y) \<Longrightarrow> y \<in> list.set ys \<Longrightarrow> x \<in> list.set (concat (map f ys))"
      by auto


    have **: "((\<alpha>, after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set (concat (map (\<lambda> (\<tau>',q'). map (\<lambda>\<tau>'' . (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q'))) (prefixes \<tau>')) (\<X>' q)))"
      using scheme[of _ "(\<lambda>(\<tau>', q'). map (\<lambda>\<tau>''. ((V q @ p_io \<tau>'', target q \<tau>''), V q @ p_io \<tau>', q')) (prefixes \<tau>'))", OF * \<open>(p,after_initial M \<beta>) \<in> list.set (\<X>' q)\<close>]
      .

    have "((\<alpha>, after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set C"
      unfolding C 
      using scheme[of _ "(\<lambda>q . concat (map (\<lambda> (\<tau>',q'). map (\<lambda>\<tau>'' . (((V q)@ p_io \<tau>'', target q \<tau>''),((V q)@ p_io \<tau>',q'))) (prefixes \<tau>')) (\<X>' q)))", OF ** \<open>q \<in> list.set rstates\<close>]
      .

    then show ?thesis
      using \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close>
      unfolding pairs_def by auto
  qed
qed


subsection \<open>Definition of the Pair-Framework\<close>

definition pair_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                              nat \<Rightarrow>
                              (('a,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow>
                              (('a,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> ((('b \<times> 'c) list \<times> 'a) \<times> (('b \<times> 'c) list \<times> 'a)) list) \<Rightarrow>
                              (('a,'b,'c) fsm \<Rightarrow> (('b \<times> 'c) list \<times> 'a) \<times> ('b \<times> 'c) list \<times> 'a \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> ('b \<times> 'c) prefix_tree) \<Rightarrow>
                              ('b\<times>'c) prefix_tree" 
where
  "pair_framework M m get_initial_test_suite get_pairs get_separating_traces =   
    (let 
      TS = get_initial_test_suite M m;
      D  = get_pairs M m;
      dist_extension = (\<lambda> t ((\<alpha>,q'),(\<beta>,q'')) . let tDist = get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) t
                                                in combine_after (combine_after t \<alpha> tDist) \<beta> tDist)
    in 
      foldl dist_extension TS D)"



lemma pair_framework_completeness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
  and     "is_state_cover_assignment M V"
  and     "{(V q)@io@[(x,y)] | q io x y . q \<in> reachable_states M \<and> io \<in> LS M q \<and> length io \<le> m - size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M} \<subseteq> set (get_initial_test_suite M m)"
  and     "\<And> \<alpha> \<beta> . (\<alpha>,\<beta>) \<in> (V ` reachable_states M) \<times> (V ` reachable_states M)
                      \<union> (V ` reachable_states M) \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M}}
                      \<union> (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M} . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>}) \<Longrightarrow>
                    \<alpha> \<in> L M \<Longrightarrow> \<beta> \<in> L M \<Longrightarrow> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow>
                    ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set (get_pairs M m)"
  and     "\<And> \<alpha> \<beta> t . \<alpha> \<in> L M \<Longrightarrow> \<beta> \<in> L M \<Longrightarrow> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow> \<exists> io \<in> set (get_separating_traces M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) . distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
shows "(L M = L I) \<longleftrightarrow> (L M \<inter> set (pair_framework M m get_initial_test_suite get_pairs get_separating_traces) = L I \<inter> set (pair_framework M m get_initial_test_suite get_pairs get_separating_traces))"
proof (cases "inputs M = {} \<or> outputs M = {}")
  case True (* handle case of empty input or outputs *)
  then consider "inputs M = {}" | "outputs M = {}" by blast
  then show ?thesis proof cases
    case 1
    have "L M = {[]}"
      using "1" language_empty_IO by blast
    moreover have "L I = {[]}"
      by (metis "1" assms(6) language_empty_IO)
    ultimately show ?thesis by blast
  next
    case 2
    have "L M = {[]}"
      using language_io(2)[of _ M "initial M"] unfolding 2
      by (metis (no_types, opaque_lifting) ex_in_conv is_singletonI' is_singleton_the_elem language_contains_empty_sequence set_empty2 singleton_iff surj_pair) 
    moreover have "L I = {[]}"
      using language_io(2)[of _ I "initial I"] unfolding 2 \<open>outputs I = outputs M\<close>
      by (metis (no_types, opaque_lifting) ex_in_conv is_singletonI' is_singleton_the_elem language_contains_empty_sequence set_empty2 singleton_iff surj_pair)
    ultimately show ?thesis by blast
  qed
next
  case False


  define T where T: "T = get_initial_test_suite M m"
  moreover define pairs where pairs: "pairs  = get_pairs M m"
  moreover define distExtension where distExtension: "distExtension = (\<lambda> t ((\<alpha>,q'),(\<beta>,q'')) . let tDist = get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) t
                                                                       in combine_after (combine_after t \<alpha> tDist) \<beta> tDist)"
  ultimately have res_def: "pair_framework M m get_initial_test_suite get_pairs get_separating_traces = foldl distExtension T pairs"
    unfolding pair_framework_def Let_def by auto

  define T' where T': "T' = set (foldl distExtension T pairs)"
  then have T'r: "T' = set (foldr (\<lambda> x y . distExtension y x) (rev pairs) T)"
    by (simp add: foldl_conv_foldr) 

  define \<Pi> where \<Pi>: "\<Pi> = (V ` reachable_states M)"
  define n where n: "n = size_r M"
  define \<X> where \<X>: "\<X> = (\<lambda> q . {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M})"
  define A where A: "A = \<Pi> \<times> \<Pi>"
  define B where B: "B = \<Pi> \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q}"
  define C where C: "C = (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> \<X> q . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>})"
  

  have satisfaction_conditions: "is_state_cover_assignment M V \<Longrightarrow>
    \<Pi> \<subseteq> T' \<Longrightarrow>
    { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> T' \<Longrightarrow>
    (\<And> \<alpha> \<beta> . (\<alpha>,\<beta>) \<in> A \<union> B \<union> C \<Longrightarrow> 
              \<alpha> \<in> L M \<Longrightarrow>
              \<beta> \<in> L M \<Longrightarrow>
              after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow>
              (\<exists> \<omega> . \<alpha>@\<omega> \<in> T' \<and>
                     \<beta>@\<omega> \<in> T' \<and>
                     distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>)) \<Longrightarrow>
    satisfies_h_condition M V T' m"
    unfolding satisfies_h_condition_def Let_def \<Pi> n \<X> A B C  
    by force

  have c1: "is_state_cover_assignment M V"
    using assms(8) .

  have c2: "\<Pi> \<subseteq> T'" and c3: "{ (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> T'"
  proof -
    have "set T \<subseteq> T'"
      unfolding T' 
    proof (induction pairs rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a pairs)

      obtain \<alpha> q' \<beta> q'' where "a = ((\<alpha>,q'),(\<beta>,q''))"
        by (metis prod.collapse) 

      have "foldl distExtension T (pairs @ [a]) = distExtension (foldl distExtension T pairs) a"
        by simp 
      moreover have "\<And> t . set t \<subseteq> set (distExtension t a)" 
      proof -
        fix t
        have "distExtension t a = combine_after (combine_after t \<alpha> (get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) t)) \<beta> (get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) t)"
          unfolding distExtension \<open>a = ((\<alpha>,q'),(\<beta>,q''))\<close> Let_def by auto
        moreover have "\<And> t' . set t \<subseteq> set (combine_after (combine_after t \<alpha> t') \<beta> t')"
          unfolding combine_after_set by blast
        ultimately show "set t \<subseteq> set (distExtension t a)" 
          by simp
      qed
      ultimately show ?case
        using snoc.IH by auto
    qed

    have "\<Pi> \<subseteq> set T"
    proof 
      fix io assume "io \<in> \<Pi>"
      then obtain q where "io = (V q)"
                      and "q \<in> reachable_states M"                      
        unfolding \<Pi>
        by blast

      obtain x y where "x \<in> inputs M" and "y \<in> outputs M" 
        using False by blast
      moreover have "[] \<in> LS M q"
        using reachable_state_is_state[OF \<open>q \<in> reachable_states M\<close>] by auto
      ultimately have "(V q) @ [(x,y)] \<in> set T"
        using assms(9) \<open>q \<in> reachable_states M\<close>
        unfolding T[symmetric] by force
      then show "io \<in> set T"
        unfolding \<Pi>
        using \<open>io = V q\<close> set_prefix by auto 
    qed
    then show "\<Pi> \<subseteq> T'"
      using \<open>set T \<subseteq> T'\<close> by blast


    have "{ (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> set T" 
      using assms(9)
      unfolding \<X> T[symmetric] n[symmetric] by force
    then show "{ (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> T'"
      using \<open>set T \<subseteq> T'\<close> by blast
  qed

  have c4: "(\<And> \<alpha> \<beta> . (\<alpha>,\<beta>) \<in> A \<union> B \<union> C \<Longrightarrow> 
              \<alpha> \<in> L M \<Longrightarrow>
              \<beta> \<in> L M \<Longrightarrow>
              after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow>
              (\<exists> \<omega> . \<alpha>@\<omega> \<in> T' \<and>
                     \<beta>@\<omega> \<in> T' \<and>
                     distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>))"    
  proof -
    fix \<alpha> \<beta> assume "(\<alpha>,\<beta>) \<in> A \<union> B \<union> C"
               and "\<alpha> \<in> L M"
               and "\<beta> \<in> L M"
               and "after_initial M \<alpha> \<noteq> after_initial M \<beta>"


    have "((\<alpha>, FSM.after M (FSM.initial M) \<alpha>), \<beta>, FSM.after M (FSM.initial M) \<beta>) \<in> list.set pairs"
      using \<open>(\<alpha>,\<beta>) \<in> A \<union> B \<union> C\<close>
      unfolding A B C \<Pi> \<X> pairs
      using \<open>\<alpha> \<in> L M\<close> \<open>\<beta> \<in> L M\<close> \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close> assms(10) n by force
    moreover note \<open>\<alpha> \<in> L M\<close> \<open>\<beta> \<in> L M\<close> \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close>
    moreover have "\<And> \<alpha> \<beta> . ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set pairs \<Longrightarrow> \<alpha> \<in> L M \<Longrightarrow> \<beta> \<in> L M \<Longrightarrow> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow> \<exists> io . io \<in> (LS M (after_initial M \<alpha>) - LS M (after_initial M \<beta>)) \<union> (LS M (after_initial M \<beta>) - LS M (after_initial M \<alpha>)) \<and> \<alpha>@io \<in> T' \<and> \<beta>@io \<in> T'"
      unfolding T' proof (induction pairs rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a pairs)

      obtain \<alpha>a q'a \<beta>a q''a where "a = ((\<alpha>a,q'a),(\<beta>a,q''a))"
        by (metis prod.collapse) 

      have "foldl distExtension T (pairs @ [a]) = distExtension (foldl distExtension T pairs) a"
        by simp 
      moreover have "\<And> t . set t \<subseteq> set (distExtension t a)"
      proof -
        fix t
        have "distExtension t a = combine_after (combine_after t \<alpha>a (get_separating_traces M ((\<alpha>a,q'a),(\<beta>a,q''a)) t)) \<beta>a (get_separating_traces M ((\<alpha>a,q'a),(\<beta>a,q''a)) t)"
          unfolding distExtension \<open>a = ((\<alpha>a,q'a),(\<beta>a,q''a))\<close> Let_def by auto
        moreover have "\<And> t' . set t \<subseteq> set (combine_after (combine_after t \<alpha>a t') \<beta>a t')"
          unfolding combine_after_set by blast
        ultimately show "set t \<subseteq> set (distExtension t a)" 
          by simp
      qed
      ultimately have "set (foldl distExtension T pairs) \<subseteq> set (foldl distExtension T (pairs@[a]))"
        by auto

      let ?q' = "after_initial M \<alpha>"
      let ?q'' = "after_initial M \<beta>"

      show ?case proof (cases "a = ((\<alpha>,?q'),(\<beta>,?q''))")
        case True
        then have "foldl distExtension T (pairs @ [a]) = distExtension (foldl distExtension T pairs) ((\<alpha>,?q'),(\<beta>,?q''))"
          by auto 
        also have "\<dots> = combine_after (combine_after (foldl distExtension T pairs) \<alpha> (get_separating_traces M ((\<alpha>, ?q'), (\<beta>, ?q'')) (foldl distExtension T pairs))) \<beta> (get_separating_traces M ((\<alpha>, ?q'), (\<beta>, ?q'')) (foldl distExtension T pairs))"
          using distExtension 
          by (metis (no_types, lifting) case_prod_conv)
        finally have "foldl distExtension T (pairs @ [a]) = combine_after (combine_after (foldl distExtension T pairs) \<alpha> (get_separating_traces M ((\<alpha>, ?q'), (\<beta>, ?q'')) (foldl distExtension T pairs))) \<beta> (get_separating_traces M ((\<alpha>, ?q'), (\<beta>, ?q'')) (foldl distExtension T pairs))"
          .
        moreover define dist where dist: "dist = (get_separating_traces M ((\<alpha>,?q'),(\<beta>,?q'')) (foldl distExtension T pairs))"
        ultimately have *: "foldl distExtension T (pairs @ [a]) = combine_after (combine_after (foldl distExtension T pairs) \<alpha> dist) \<beta> dist"
          by auto

        define ta where "ta = (after (foldl distExtension T pairs) \<alpha>)"
        define tb where "tb = (after (foldl distExtension T pairs) \<beta>)"
        obtain io where "io \<in> set dist \<union> (set ta \<inter> set tb)" and "io \<in> (LS M ?q' - LS M ?q'') \<union> (LS M ?q'' - LS M ?q')"
          using assms(11)[OF snoc.prems(2,3,4), of "(foldl distExtension T pairs)"]
          unfolding dist distinguishes_def ta_def tb_def by blast 
        then consider "io \<in> set dist" | "io \<in> (set ta \<inter> set tb)"
          by blast

        then show ?thesis proof cases
          case 1
          then have "\<alpha>@io \<in> set (foldl distExtension T (pairs @ [a]))" and "\<beta>@io \<in> set (foldl distExtension T (pairs @ [a]))"
            unfolding * using combine_after_set by blast+
          then show ?thesis 
            using \<open>io \<in> (LS M ?q' - LS M ?q'') \<union> (LS M ?q'' - LS M ?q')\<close> by auto
        next
          case 2
          moreover have "io \<noteq> []"
            using \<open>io \<in> (LS M ?q' - LS M ?q'') \<union> (LS M ?q'' - LS M ?q')\<close>
                  after_is_state[OF assms(1) snoc.prems(2)]
                  after_is_state[OF assms(1) snoc.prems(3)]
            by auto
          ultimately have "\<alpha>@io \<in> set (foldl distExtension T pairs)" and "\<beta>@io \<in> set (foldl distExtension T pairs)"
            unfolding ta_def tb_def after_set by blast+
          then show ?thesis
            using \<open>io \<in> (LS M ?q' - LS M ?q'') \<union> (LS M ?q'' - LS M ?q')\<close>
                  \<open>set (foldl distExtension T pairs) \<subseteq> set (foldl distExtension T (pairs @ [a]))\<close>
            by auto
        qed
      next
        case False
        then have "((\<alpha>,?q'),(\<beta>,?q'')) \<in> list.set pairs"
          using snoc.prems(1) by auto

        show ?thesis 
          using snoc.IH[OF \<open>((\<alpha>,?q'),(\<beta>,?q'')) \<in> list.set pairs\<close> snoc.prems(2,3,4)]
                \<open>set (foldl distExtension T pairs) \<subseteq> set (foldl distExtension T (pairs @ [a]))\<close>
          by auto
      qed
    qed
    ultimately show "(\<exists> \<omega> . \<alpha>@\<omega> \<in> T' \<and> \<beta>@\<omega> \<in> T' \<and> distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) \<omega>)"
      unfolding distinguishes_def  by blast
  qed

  have "satisfies_h_condition M V T' m"
    using satisfaction_conditions[OF c1 c2 c3 c4]
    by blast
  then have "satisfies_h_condition M V (set (pair_framework M m get_initial_test_suite get_pairs get_separating_traces)) m"
    unfolding res_def T' .
  then show ?thesis
    using h_condition_completeness[OF assms(1-7)]
    by blast
qed



lemma pair_framework_finiteness :
  assumes "\<And> \<alpha> \<beta> t . \<alpha> \<in> L M \<Longrightarrow> \<beta> \<in> L M \<Longrightarrow> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow> finite_tree (get_separating_traces M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
  and     "finite_tree (get_initial_test_suite M m)"
  and     "\<And> \<alpha> q' \<beta> q'' . ((\<alpha>,q'),(\<beta>,q'')) \<in> list.set (get_pairs M m) \<Longrightarrow> \<alpha> \<in> L M \<and> \<beta> \<in> L M \<and> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<and> q' = after_initial M \<alpha> \<and> q'' = after_initial M \<beta>"
shows "finite_tree (pair_framework M m get_initial_test_suite get_pairs get_separating_traces)"
proof -
  
  define T where T: "T = get_initial_test_suite M m"
  moreover define pairs where pairs: "pairs  = get_pairs M m"
  moreover define distExtension where distExtension: "distExtension = (\<lambda> t ((\<alpha>,q'),(\<beta>,q'')) . let tDist = get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) t
                                                                       in combine_after (combine_after t \<alpha> tDist) \<beta> tDist)"
  ultimately have res_def: "pair_framework M m get_initial_test_suite get_pairs get_separating_traces = foldl distExtension T pairs"
    unfolding pair_framework_def Let_def by auto

  have "\<And> \<alpha> q' \<beta> q'' . ((\<alpha>,q'),(\<beta>,q'')) \<in> list.set pairs \<Longrightarrow> \<alpha> \<in> L M \<and> \<beta> \<in> L M \<and> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<and> q' = after_initial M \<alpha> \<and> q'' = after_initial M \<beta>"
    using assms(3) unfolding pairs by auto
  then show ?thesis
  unfolding res_def proof (induction pairs rule: rev_induct)
    case Nil
    then show ?case 
      using from_list_finite_tree assms(2)
      unfolding T 
      by auto
  next
    case (snoc a pairs)
    then have p1: "\<And> \<alpha> q' \<beta> q'' . ((\<alpha>,q'),(\<beta>,q'')) \<in> list.set pairs \<Longrightarrow> \<alpha> \<in> L M \<and> \<beta> \<in> L M \<and> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<and> q' = after_initial M \<alpha> \<and> q'' = after_initial M \<beta>"
      by (metis butlast_snoc in_set_butlastD)

    obtain \<alpha> q' \<beta> q'' where "a = ((\<alpha>,q'),(\<beta>,q''))"
      by (metis prod.collapse) 
    then have "foldl distExtension T (pairs @ [a]) = distExtension (foldl distExtension T pairs) ((\<alpha>,q'),(\<beta>,q'')) "
      by auto
    also have "\<dots> = combine_after (combine_after (foldl distExtension T pairs) \<alpha> (get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) (foldl distExtension T pairs))) \<beta> (get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) (foldl distExtension T pairs))"
      using distExtension 
      by (metis (no_types, lifting) case_prod_conv)
    finally have "foldl distExtension T (pairs @ [a]) = combine_after (combine_after (foldl distExtension T pairs) \<alpha> (get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) (foldl distExtension T pairs))) \<beta> (get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) (foldl distExtension T pairs))"
      .
    moreover define ta where ta: "ta = (after (foldl distExtension T pairs) \<alpha>)"
    moreover define tb where tb: "tb = (after (foldl distExtension T pairs) \<beta>)"
    moreover define dist where dist: "dist = (get_separating_traces M ((\<alpha>,q'),(\<beta>,q'')) (foldl distExtension T pairs))"
        ultimately have *: "foldl distExtension T (pairs @ [a]) = combine_after (combine_after (foldl distExtension T pairs) \<alpha> dist) \<beta> dist"
          by auto

    have "((\<alpha>,q'),(\<beta>,q'')) \<in> list.set (a#pairs)"
      unfolding \<open>a = ((\<alpha>,q'),(\<beta>,q''))\<close> by auto
    then have "\<alpha> \<in> L M \<and> \<beta> \<in> L M \<and> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<and> q' = after_initial M \<alpha> \<and> q'' = after_initial M \<beta>"
      using snoc.prems
      by auto 
    then have "finite_tree dist"
      using assms(1) unfolding dist by auto
    moreover have "finite_tree (foldl distExtension T pairs)"
      using snoc.IH[OF p1] by auto
    ultimately show ?case
      unfolding * 
      using combine_after_finite_tree by blast
  qed
qed


end 