section \<open>H-Framework\<close>

text \<open>This theory defines the H-Framework and provides completeness properties.\<close>

theory H_Framework
imports Convergence_Graph "../Prefix_Tree" "../State_Cover"
begin


subsection \<open>Abstract H-Condition\<close>

(* assumes that V is a state cover assignment *)
definition satisfies_abstract_h_condition :: "('a,'b,'c) fsm \<Rightarrow> ('e,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> nat \<Rightarrow> bool" where
  "satisfies_abstract_h_condition M1 M2 V m = (\<forall> q \<gamma> . 
    q \<in> reachable_states M1 \<longrightarrow> 
    length \<gamma> \<le> Suc (m-size_r M1) \<longrightarrow> 
    list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1  \<longrightarrow> 
    butlast \<gamma> \<in> LS M1 q \<longrightarrow> 
    (let traces = (V ` reachable_states M1)
                  \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} 
      in (L M1 \<inter> traces = L M2 \<inter> traces)
         \<and> preserves_divergence M1 M2 traces))"



lemma abstract_h_condition_exhaustiveness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
  and     "is_state_cover_assignment M V"
  and     "satisfies_abstract_h_condition M I V m"
shows "L M = L I"
proof (rule ccontr)
  assume "L M \<noteq> L I"

  (* unfold the sufficient condition for easier reference *)

  define \<Pi> where \<Pi>: "\<Pi> = (V ` reachable_states M)"
  define n where n: "n = size_r M"
  define \<X> where \<X>: "\<X> = (\<lambda> q . {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M})"

  have pass_prop: "\<And> q \<gamma> . q \<in> reachable_states M \<Longrightarrow> length \<gamma> \<le> Suc (m-n) \<Longrightarrow> list.set \<gamma> \<subseteq> inputs M \<times> outputs M  \<Longrightarrow> butlast \<gamma> \<in> LS M q \<Longrightarrow>
                    (L M \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                     = L I \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
  and dist_prop: "\<And> q \<gamma> . q \<in> reachable_states M \<Longrightarrow> length \<gamma> \<le> Suc (m-n) \<Longrightarrow> list.set \<gamma> \<subseteq> inputs M \<times> outputs M  \<Longrightarrow> butlast \<gamma> \<in> LS M q \<Longrightarrow>
                     preserves_divergence M I (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
    using \<open>satisfies_abstract_h_condition M I V m\<close> 
    unfolding satisfies_abstract_h_condition_def Let_def \<Pi> n  by blast+

  have pass_prop_\<X> : "\<And> q \<gamma> . q \<in> reachable_states M \<Longrightarrow> \<gamma> \<in> \<X> q \<Longrightarrow>
                           (L M \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                            = L I \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
   and dist_prop_\<X> : "\<And> q \<gamma> . q \<in> reachable_states M \<Longrightarrow> \<gamma> \<in> \<X> q \<Longrightarrow>
                           preserves_divergence M I (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
  proof -
    fix q \<gamma> assume *: "q \<in> reachable_states M" and "\<gamma> \<in> \<X> q"
    then obtain io x y where "\<gamma> = io@[(x,y)]" and "io \<in> LS M q" and "length io \<le> m-n" and "x \<in> inputs M" and "y \<in> outputs M"
      unfolding \<X> by blast

    have **:"length \<gamma> \<le> Suc (m-n)"
      using \<open>\<gamma> = io@[(x,y)]\<close> \<open>length io \<le> m-n\<close> by auto
    have ***:"list.set \<gamma> \<subseteq> inputs M \<times> outputs M"
      using language_io[OF \<open>io \<in> LS M q\<close>] \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close>
      unfolding \<open>\<gamma> = io@[(x,y)]\<close> by auto
    have ****:"butlast \<gamma> \<in> LS M q"
      unfolding \<open>\<gamma> = io@[(x,y)]\<close> using \<open>io \<in> LS M q\<close> by auto
    
    show "(L M \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                            = L I \<inter> (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
      using pass_prop[OF * ** *** ****] .
    show "preserves_divergence M I (\<Pi> \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
      using dist_prop[OF * ** *** ****] .
  qed


  (* obtain minimal trace that
      - extends some sequence of the state cover (which contains the empty sequence), and
      - is contained in either L M or L I *)
 
  have "(L M \<inter> \<Pi>) = (L I \<inter> \<Pi>)"
    using pass_prop[OF reachable_states_initial, of "[]"] language_contains_empty_sequence[of M] by auto
  moreover have "\<Pi> \<subseteq> L M"
    unfolding \<Pi> using state_cover_assignment_after(1)[OF assms(1) \<open>is_state_cover_assignment M V\<close>]
    by blast
  ultimately have "\<Pi> \<subseteq> L I"
    using \<open>\<Pi> = (V ` reachable_states M)\<close> by blast

  obtain \<pi> \<tau>' where "\<pi> \<in> \<Pi>"
                and "\<pi> @ \<tau>' \<in> (L M - L I) \<union> (L I - L M)"
                and "\<And> io q . q \<in> reachable_states M \<Longrightarrow> (V q)@io \<in> (L M - L I) \<union> (L I - L M) \<Longrightarrow> length \<tau>' \<le> length io"
    using \<open>(L M \<inter> \<Pi>) = (L I \<inter> \<Pi>)\<close>
    using minimal_sequence_to_failure_from_state_cover_assignment_ob[OF \<open>L M \<noteq> L I\<close> \<open>is_state_cover_assignment M V\<close>] 
    unfolding \<Pi>
    by blast

  obtain q where "q \<in> reachable_states M" and "\<pi> = V q"
    using \<open>\<pi> \<in> \<Pi>\<close> unfolding \<Pi> by blast
  then have "\<pi> \<in> L M" and "after_initial M \<pi> = q"
    using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M V\<close>]
    by blast+
  

  have \<tau>'_min: "\<And> \<pi>' io . \<pi>' \<in> \<Pi> \<Longrightarrow> \<pi>'@io \<in> (L M - L I) \<union> (L I - L M) \<Longrightarrow> length \<tau>' \<le> length io"
  proof -
    fix \<pi>' io
    assume "\<pi>' \<in> \<Pi>" and "\<pi>'@io \<in> (L M - L I) \<union> (L I - L M)"
    then obtain q where "q \<in> reachable_states M" and "\<pi>' = V q"
      unfolding \<Pi> by blast
    then show "length \<tau>' \<le> length io"
      using \<open>\<And> io q . q \<in> reachable_states M \<Longrightarrow> (V q)@io \<in> (L M - L I) \<union> (L I - L M) \<Longrightarrow> length \<tau>' \<le> length io\<close>
            \<open>\<pi>'@io \<in> (L M - L I) \<union> (L I - L M)\<close> by auto
  qed


  

  obtain \<pi>\<tau> xy \<tau>'' where "\<pi> @ \<tau>' = \<pi>\<tau> @ [xy] @ \<tau>''"
                      and "\<pi>\<tau> \<in> L M \<inter> L I"
                      and "\<pi>\<tau>@[xy] \<in> (L I - L M) \<union> (L M - L I)"
    using minimal_failure_prefix_ob[OF \<open>observable M\<close> \<open>observable I\<close> fsm_initial fsm_initial, of "\<pi> @ \<tau>'"]
    using minimal_failure_prefix_ob[OF \<open>observable I\<close> \<open>observable M\<close> fsm_initial fsm_initial, of "\<pi> @ \<tau>'"]
    using \<open>\<pi> @ \<tau>' \<in> (L M - L I) \<union> (L I - L M)\<close>
    by (metis Int_commute Un_iff)

  moreover obtain x y where "xy = (x,y)"
    using surjective_pairing by blast

  moreover have "\<pi>\<tau> = \<pi> @ butlast \<tau>'"
  proof -
    have "length \<pi>\<tau> \<ge> length \<pi>"
    proof (rule ccontr) 
      assume "\<not> length \<pi> \<le> length \<pi>\<tau>"
      then have "length (\<pi>\<tau>@[xy]) \<le> length \<pi>"
        by auto
      then have "take (length (\<pi>\<tau>@[xy])) \<pi> = \<pi>\<tau>@[xy]"
        using \<open>\<pi> @ \<tau>' = \<pi>\<tau> @ [xy] @ \<tau>''\<close>
        by (metis append_assoc append_eq_append_conv_if) 
      then have "\<pi> = (\<pi>\<tau>@[xy]) @ (drop (length (\<pi>\<tau>@[xy])) \<pi>)"
        by (metis append_take_drop_id)          
      then have "\<pi>\<tau>@[xy] \<in> L M \<inter> L I"
        using \<open>\<pi> \<in> \<Pi>\<close> \<open>\<Pi> \<subseteq> L I\<close> \<open>\<Pi> \<subseteq> L M\<close> 
        using language_prefix[of "(\<pi>\<tau>@[xy])" "drop (length (\<pi>\<tau>@[xy])) \<pi>", of M "initial M"]
        using language_prefix[of "(\<pi>\<tau>@[xy])" "drop (length (\<pi>\<tau>@[xy])) \<pi>", of I "initial I"]
        by auto
      then show "False"
        using \<open>\<pi>\<tau>@[xy] \<in> (L I - L M) \<union> (L M - L I)\<close> by blast
    qed

    then have "\<pi>\<tau> = \<pi> @ (take (length \<pi>\<tau> - length \<pi>) \<tau>')"
      using \<open>\<pi> @ \<tau>' = \<pi>\<tau> @ [xy] @ \<tau>''\<close>
      by (metis dual_order.refl take_all take_append take_le) 
    then have "\<pi> @ ((take (length \<pi>\<tau> - length \<pi>) \<tau>')@[xy]) \<in> (L I - L M) \<union> (L M - L I)"
      using \<open>\<pi>\<tau>@[xy] \<in> (L I - L M) \<union> (L M - L I)\<close>
      by (metis append_assoc)        
    then have "length \<tau>' \<le> Suc (length (take (length \<pi>\<tau> - length \<pi>) \<tau>'))"
      using \<tau>'_min[OF \<open>\<pi> \<in> \<Pi>\<close>]
      by (metis Un_commute length_append_singleton)
    moreover have "length \<tau>' \<ge> Suc (length (take (length \<pi>\<tau> - length \<pi>) \<tau>'))"
      using \<open>\<pi> @ \<tau>' = \<pi>\<tau> @ [xy] @ \<tau>''\<close> \<open>\<pi>\<tau> = \<pi> @ take (length \<pi>\<tau> - length \<pi>) \<tau>'\<close> not_less_eq_eq by fastforce
    ultimately have "length \<tau>' = Suc (length (take (length \<pi>\<tau> - length \<pi>) \<tau>'))"
      by simp
    then show ?thesis
    proof -
      have "\<pi> @ \<tau>' = (\<pi> @ take (length \<pi>\<tau> - length \<pi>) \<tau>') @ [xy] @ \<tau>''"
        using \<open>\<pi> @ \<tau>' = \<pi>\<tau> @ [xy] @ \<tau>''\<close> \<open>\<pi>\<tau> = \<pi> @ take (length \<pi>\<tau> - length \<pi>) \<tau>'\<close> by presburger
      then have "take (length \<pi>\<tau> - length \<pi>) \<tau>' = butlast \<tau>'"
        by (metis (no_types) \<open>length \<tau>' = Suc (length (take (length \<pi>\<tau> - length \<pi>) \<tau>'))\<close> append_assoc append_butlast_last_id append_eq_append_conv diff_Suc_1 length_butlast length_greater_0_conv zero_less_Suc)
      then show ?thesis
        using \<open>\<pi>\<tau> = \<pi> @ take (length \<pi>\<tau> - length \<pi>) \<tau>'\<close> by fastforce
    qed 
  qed

  ultimately have "\<pi> @ (butlast \<tau>') \<in> L M \<inter> L I"
              and "(\<pi> @ (butlast \<tau>'))@[(x,y)] \<in> (L I - L M) \<union> (L M - L I)"
    by auto

  have "\<tau>' = (butlast \<tau>')@[(x,y)]"
    using \<open>\<pi> @ \<tau>' = \<pi>\<tau> @ [xy] @ \<tau>''\<close> \<open>xy = (x,y)\<close> 
    unfolding \<open>\<pi>\<tau> = \<pi> @ butlast \<tau>'\<close>
    by (metis (no_types, opaque_lifting) append_Cons append_butlast_last_id butlast.simps(1) butlast_append last_appendR list.distinct(1) self_append_conv)


  have "x \<in> inputs M" and "y \<in> outputs M"
  proof -
    have *: "(x,y) \<in> list.set ((\<pi> @ (butlast \<tau>'))@[(x,y)])"
      by auto

    show "x \<in> inputs M"
      using \<open>(\<pi> @ (butlast \<tau>'))@[(x,y)] \<in> (L I - L M) \<union> (L M - L I)\<close> 
            language_io(1)[OF _ *, of I]
            language_io(1)[OF _ *, of M]
            \<open>inputs I = inputs M\<close>
      by blast

    show "y \<in> outputs M"
      using \<open>(\<pi> @ (butlast \<tau>'))@[(x,y)] \<in> (L I - L M) \<union> (L M - L I)\<close> 
            language_io(2)[OF _ *, of I]
            language_io(2)[OF _ *, of M]
            \<open>outputs I = outputs M\<close>
      by blast
  qed

  have "\<pi> @ (butlast \<tau>') \<in> L M"
    using  \<open>\<pi> @ (butlast \<tau>') \<in> L M \<inter> L I\<close> by auto
  have "list.set (\<pi> @ \<tau>') \<subseteq> inputs M \<times> outputs M"
    using \<open>\<pi> @ \<tau>' \<in> (L M - L I) \<union> (L I - L M)\<close>
    using language_io[of \<open>\<pi> @ \<tau>'\<close> M "initial M"]
    using language_io[of \<open>\<pi> @ \<tau>'\<close> I "initial I"]
    unfolding assms(6,7) by fast 
  then have "list.set \<tau>' \<subseteq> inputs M \<times> outputs M"
    by auto
  have "list.set (butlast \<tau>') \<subseteq> inputs M \<times> outputs M"
    using language_io[OF \<open>\<pi> @ (butlast \<tau>') \<in> L M\<close>] by force
  have "butlast \<tau>' \<in> LS M q"
    using after_language_iff[OF assms(1) \<open>\<pi> \<in> L M\<close>] \<open>\<pi> @ (butlast \<tau>') \<in> L M\<close>
    unfolding \<open>after_initial M \<pi> = q\<close>
    by blast

  have "length \<tau>' > m - n + 1"
  proof (rule ccontr)
    assume "\<not> m - n + 1 < length \<tau>'"
    then have "length \<tau>' \<le> Suc (m - n)"
      by auto

    have "\<pi> @ \<tau>' \<in> (\<Pi> \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<tau>')})"
      unfolding \<open>\<pi> = V q\<close> using \<open>q \<in> reachable_states M\<close>  unfolding prefixes_set by auto
    then have "L M \<inter> {\<pi> @ \<tau>'} = L I \<inter> {\<pi> @ \<tau>'}"
      using pass_prop[OF \<open>q \<in> reachable_states M\<close> \<open>length \<tau>' \<le> Suc (m - n)\<close> \<open>list.set \<tau>' \<subseteq> inputs M \<times> outputs M\<close> \<open>butlast \<tau>' \<in> LS M q\<close>]
      by blast
    then show False
      using \<open>\<pi> @ \<tau>' \<in> (L M - L I) \<union> (L I - L M)\<close> by blast
  qed



  define \<tau> where \<tau>_def: "\<tau> = (\<lambda>i . take i (butlast \<tau>'))"

  have "\<And> i . i > 0 \<Longrightarrow> i \<le> m - n + 1 \<Longrightarrow> (\<tau> i) \<in> \<X> q"
  proof -
    fix i assume "i > 0" and "i \<le> m - n + 1"
    
    then have "\<tau> i = (butlast (\<tau> i)) @ [last (\<tau> i)]"
      using \<tau>_def \<open>length \<tau>' > m - n + 1\<close>
      by (metis add_less_same_cancel2 append_butlast_last_id length_butlast less_diff_conv list.size(3) not_add_less2 take_eq_Nil) 

    have "length (butlast (\<tau> i)) \<le> m - n" 
      using \<tau>_def \<open>length \<tau>' > m - n + 1\<close> \<open>i \<le> m - n + 1\<close> by auto


    have "q \<in> io_targets M \<pi> (initial M)"
      using \<open>is_state_cover_assignment M V\<close> \<open>q \<in> reachable_states M\<close> \<open>\<pi> = V q\<close>
      by simp 
    then have "(butlast \<tau>') \<in> LS M q"
      using \<open>\<pi> @ (butlast \<tau>') \<in> L M \<inter> L I\<close> 
      using observable_io_targets_language[OF _ \<open>observable M\<close>] 
      by force
    then have "\<tau> i @ (drop i (butlast \<tau>')) \<in> LS M q"
      using \<tau>_def by auto
    then have "\<tau> i \<in> LS M q"
      using language_prefix
      by fastforce 
    then have "butlast (\<tau> i) \<in> LS M q"
      using language_prefix \<open>\<tau> i = (butlast (\<tau> i)) @ [last (\<tau> i)]\<close>
      by metis 

    have "(fst (last (\<tau> i)), snd (last (\<tau> i))) \<in> list.set ((butlast (\<tau> i)) @ [last (\<tau> i)])"
      using \<open>\<tau> i = (butlast (\<tau> i)) @ [last (\<tau> i)]\<close>
      using in_set_conv_decomp by fastforce
    then have "fst (last (\<tau> i)) \<in> inputs M" 
          and "snd (last (\<tau> i)) \<in> outputs M"
      using \<open>\<tau> i \<in> LS M q\<close> \<open>\<tau> i = (butlast (\<tau> i)) @ [last (\<tau> i)]\<close> language_io[of "(butlast (\<tau> i)) @ [last (\<tau> i)]" M q "fst (last (\<tau> i))" "snd (last (\<tau> i))"] 
      by auto
      
    then show "\<tau> i \<in> \<X> q"
      unfolding \<X> 
      using \<open>length (butlast (\<tau> i)) \<le> m - n\<close> \<open>\<tau> i = (butlast (\<tau> i)) @ [last (\<tau> i)]\<close>
            \<open>butlast (\<tau> i) \<in> LS M q\<close>
      by (metis (mono_tags, lifting) mem_Collect_eq surjective_pairing)
  qed

  have "\<And> i . i \<le> m-n+1 \<Longrightarrow> \<pi> @ (\<tau> i) \<in> L M \<inter> L I"
  proof -
    fix i assume "i \<le> m-n+1"

    have "butlast \<tau>' = \<tau> i @ (drop i (butlast \<tau>'))"
      unfolding \<tau>_def by auto
    then have \<open>(\<pi> @ \<tau> i) @ (drop i (butlast \<tau>')) \<in> L M \<inter> L I\<close>
      using \<open>\<pi> @ (butlast \<tau>') \<in> L M \<inter> L I\<close>
      by auto
    then show "\<pi> @ (\<tau> i) \<in> L M \<inter> L I"
      using language_prefix[of "(\<pi> @ \<tau> i)" "(drop i (butlast \<tau>'))", of M "initial M"]
      using language_prefix[of "(\<pi> @ \<tau> i)" "(drop i (butlast \<tau>'))", of I "initial I"]
      by blast
  qed

  have B_diff: "\<Pi> \<inter> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} = {}"
  proof -
    have "\<And> io1 io2 . io1 \<in> \<Pi> \<Longrightarrow> io2 \<in> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} \<Longrightarrow> io1 \<noteq> io2"
    proof (rule ccontr)
      fix io1 io2 assume "io1 \<in> \<Pi>" "io2 \<in> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}" "\<not> io1 \<noteq> io2"

      then obtain i where "io2 = \<pi> @ (\<tau> i)" and "i \<ge> 1" and "i \<le> m - n + 1" and "\<pi> @ (\<tau> i) \<in> \<Pi>"
        by auto
      then have "\<pi> @ (\<tau> i) \<in> L M"
        using \<open>\<And> i . i \<le> m-n+1 \<Longrightarrow> \<pi> @ (\<tau> i) \<in> L M \<inter> L I\<close> by auto
      
      obtain q where "q \<in> reachable_states M" and "V q = \<pi> @ (\<tau> i)"
        using \<open>\<pi> @ (\<tau> i) \<in> \<Pi>\<close> \<Pi>
        by auto 
      moreover have "(\<pi> @ (\<tau> i))@(drop i \<tau>') \<in> (L M - L I) \<union> (L I - L M)"
        using \<tau>_def \<open>\<pi> @ \<tau>' \<in> (L M - L I) \<union> (L I - L M)\<close> \<open>length \<tau>' > m - n + 1\<close> \<open>i \<le> m - n + 1\<close>
        by (metis append_assoc append_take_drop_id le_iff_sup sup.strict_boundedE take_butlast) 
      ultimately have "length \<tau>' \<le> length (drop i \<tau>')"
        using \<open>\<And> io q . q \<in> reachable_states M \<Longrightarrow> (V q)@io \<in> (L M - L I) \<union> (L I - L M) \<Longrightarrow> length \<tau>' \<le> length io\<close>
        by presburger
      then show "False"
        using \<open>length \<tau>' > m - n + 1\<close> \<open>i \<ge> 1\<close>
        by (metis One_nat_def \<open>i \<le> m - n + 1\<close> diff_diff_cancel diff_is_0_eq' le_trans length_drop less_Suc_eq nat_less_le) 
    qed
    then show ?thesis 
      by blast
  qed


  have same_targets_in_I: "\<exists> \<alpha> \<beta> . 
                    \<alpha> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}
                    \<and> \<beta> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}
                    \<and> \<alpha> \<noteq> \<beta> \<and> (after_initial I \<alpha> = after_initial I \<beta>)"
  proof - 
    have "after_initial I ` (\<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}) \<subseteq> states I"
    proof 
      fix q assume "q \<in> after_initial I ` (\<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1})"
      then obtain io where "io \<in> (\<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1})" and "q = after_initial I io"
        by blast
      then have "io \<in> L I"
        using \<open>\<And> i . i \<le> m-n+1 \<Longrightarrow> \<pi> @ (\<tau> i) \<in> L M \<inter> L I\<close> \<open>\<Pi> \<subseteq> L I\<close> by auto
      then show "q \<in> states I"
        unfolding \<open>q = after_initial I io\<close> 
        using observable_after_path[OF \<open>observable I\<close>, of io "initial I"] path_target_is_state[of I "initial I"]
        by metis 
    qed
    then have "card (after_initial I ` (\<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1})) \<le> m"
      using \<open>size I \<le> m\<close> fsm_states_finite[of I] unfolding FSM.size_def
      by (meson card_mono le_trans) 
    moreover have "card (\<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}) = m+1"
    proof -
      have *: "card \<Pi> = n"
        using state_cover_assignment_card[OF \<open>is_state_cover_assignment M V\<close> \<open>observable M\<close>] unfolding \<Pi> n .
      have **: "card ((\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}) = m-n+1"
      proof -
        have "finite ((\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1})"
          by auto
        moreover have "inj_on (\<lambda>i . \<pi> @ (\<tau> i)) {1 .. m-n+1}" 
        proof 
          fix x y assume "x \<in> {1..m - n + 1}" "y \<in> {1..m - n + 1}" "\<pi> @ \<tau> x = \<pi> @ \<tau> y"

          then have "take x \<tau>' = take y \<tau>'"
            unfolding \<tau>_def \<open>length \<tau>' > m - n + 1\<close>
            by (metis (no_types, lifting) \<open>m - n + 1 < length \<tau>'\<close> atLeastAtMost_iff diff_is_0_eq le_trans nat_less_le same_append_eq take_butlast zero_less_diff)
          moreover have "x \<le> length \<tau>'"
            using \<open>x \<in> {1..m - n + 1}\<close> \<open>length \<tau>' > m - n + 1\<close> by auto
          moreover have "y \<le> length \<tau>'"
            using \<open>y \<in> {1..m - n + 1}\<close> \<open>length \<tau>' > m - n + 1\<close> by auto
          ultimately show "x=y"
            by (metis length_take min.absorb2) 
        qed
        moreover have "card {1..m - n + 1} = m - n + 1"
          by auto
        ultimately show ?thesis
          by (simp add: card_image) 
      qed

      have ***: "n + (m - n + 1) = m+1"
        unfolding n using \<open>m \<ge> size_r M\<close> by auto

      have "finite \<Pi>"
        unfolding \<Pi> using fsm_states_finite restrict_to_reachable_states_simps(2)
        by (metis finite_imageI) 
      have "finite ((\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1})"
        by auto
      
      show ?thesis
        using card_Un_disjoint[OF \<open>finite \<Pi>\<close> \<open>finite ((\<lambda>i. \<pi> @ \<tau> i) ` {1..m - n + 1})\<close> \<open>\<Pi> \<inter> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} = {}\<close>]
        unfolding * ** *** .
    qed
    ultimately have *: "card (after_initial I ` (\<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1})) < card (\<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1})"
      by simp
    
    show ?thesis
      using pigeonhole[OF *] unfolding inj_on_def by blast
  qed

  (* covered converging traces in I must also converge in M *)
  have same_targets_in_M: "\<And> \<alpha> \<beta> . 
                    \<alpha> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} \<Longrightarrow>
                    \<beta> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} \<Longrightarrow>
                    \<alpha> \<noteq> \<beta> \<Longrightarrow> 
                    (after_initial I \<alpha> = after_initial I \<beta>) \<Longrightarrow>
                    (after_initial M \<alpha> = after_initial M \<beta>)"
  proof (rule ccontr)
    fix \<alpha> \<beta> assume "\<alpha> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}"
               and "\<beta> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}"
               and "\<alpha> \<noteq> \<beta>"
               and "(after_initial I \<alpha> = after_initial I \<beta>)"
               and "(after_initial M \<alpha> \<noteq> after_initial M \<beta>)"


    have *: "(\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} \<subseteq> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q}"
      using \<open>\<And> i . i > 0 \<Longrightarrow> i \<le> m - n + 1 \<Longrightarrow> (\<tau> i) \<in> \<X> q\<close> \<open>q \<in> reachable_states M\<close> \<open>\<pi> = V q\<close>
      by force

    have "\<alpha> \<in> L M" and "\<beta> \<in> L M" and "\<alpha> \<in> L I" and "\<beta> \<in> L I"
      using \<open>\<alpha> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}\<close> 
            \<open>\<beta> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}\<close>
            \<open>\<And> i . i \<le> m-n+1 \<Longrightarrow> \<pi> @ (\<tau> i) \<in> L M \<inter> L I\<close> 
            \<open>\<Pi> \<subseteq> L M\<close> \<open>\<Pi> \<subseteq> L I\<close> 
      by auto
    then have "\<not> converge M \<alpha> \<beta>" and "converge I \<alpha> \<beta>"
      using \<open>after_initial M \<alpha> \<noteq> after_initial M \<beta>\<close> 
      using \<open>minimal M\<close> 
      using after_is_state[OF assms(1) \<open>\<alpha> \<in> L M\<close>]
      using after_is_state[OF assms(1) \<open>\<beta> \<in> L M\<close>]
      unfolding converge.simps minimal.simps \<open>after_initial I \<alpha> = after_initial I \<beta>\<close> by auto
    then have "\<not> converge M \<beta> \<alpha>" and "converge I \<beta> \<alpha>"
      using converge_sym by blast+

    
    have split_helper: "\<And> (P :: nat \<Rightarrow> nat \<Rightarrow> bool) . (\<exists> i j . P i j \<and> i \<noteq> j) = ((\<exists> i j . P i j \<and> i < j) \<or> (\<exists> i j . P i j \<and> i > j))"
    proof 
      show "\<And> (P :: nat \<Rightarrow> nat \<Rightarrow> bool) . \<exists>i j. P i j \<and> i \<noteq> j \<Longrightarrow> (\<exists>i j. P i j \<and> i < j) \<or> (\<exists>i j. P i j \<and> j < i)" 
      proof -
        fix P :: "nat \<Rightarrow> nat \<Rightarrow> bool" 
        assume "\<exists>i j. P i j \<and> i \<noteq> j"
        then obtain i j where "P i j" and "i \<noteq> j" by auto
        then have "i < j \<or> i > j" by auto
        then show "(\<exists>i j. P i j \<and> i < j) \<or> (\<exists>i j. P i j \<and> j < i)" using \<open>P i j\<close> by auto
      qed
      show "\<And> (P :: nat \<Rightarrow> nat \<Rightarrow> bool) . (\<exists>i j. P i j \<and> i < j) \<or> (\<exists>i j. P i j \<and> j < i) \<Longrightarrow> \<exists>i j. P i j \<and> i \<noteq> j" by auto
    qed
    have split_scheme:"(\<exists> i j . i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> \<alpha> = \<pi> @ (\<tau> i) \<and> \<beta> = \<pi> @ (\<tau> j))
          = ((\<exists> i j . i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> i < j \<and> \<alpha> = \<pi> @ (\<tau> i) \<and> \<beta> = \<pi> @ (\<tau> j))
              \<or> (\<exists> i j . i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> i > j \<and> \<alpha> = \<pi> @ (\<tau> i) \<and> \<beta> = \<pi> @ (\<tau> j)))"
      using \<open>\<alpha> \<noteq> \<beta>\<close>  
      using split_helper[of "\<lambda> i j . i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> \<alpha> = \<pi> @ (\<tau> i) \<and> \<beta> = \<pi> @ (\<tau> j)"]
      by blast

    consider "(\<alpha> \<in> \<Pi> \<and> \<beta> \<in> \<Pi>)" |
             "(\<exists> i . i \<in> {1 .. m-n+1} \<and> \<alpha> \<in> \<Pi> \<and> \<beta> = \<pi> @ (\<tau> i))" |
             "(\<exists> i . i \<in> {1 .. m-n+1} \<and> \<beta> \<in> \<Pi> \<and> \<alpha> = \<pi> @ (\<tau> i))" |
             "(\<exists> i j . i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> i < j \<and> \<alpha> = \<pi> @ (\<tau> i) \<and> \<beta> = \<pi> @ (\<tau> j))" |
             "(\<exists> i j . i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> i > j \<and> \<alpha> = \<pi> @ (\<tau> i) \<and> \<beta> = \<pi> @ (\<tau> j))"
      using \<open>\<alpha> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}\<close>
            \<open>\<beta> \<in> \<Pi> \<union> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}\<close>
      using split_scheme 
      by blast

    then have "\<exists> \<alpha>' \<beta>' . \<alpha>' \<in> L M \<and> \<beta>' \<in> L M \<and> \<not>converge M \<alpha>' \<beta>' \<and> converge I \<alpha>' \<beta>' \<and>
            ( (\<alpha>' \<in> \<Pi> \<and> \<beta>' \<in> \<Pi>) 
              \<or> (\<exists> i . i \<in> {1 .. m-n+1} \<and> \<alpha>' \<in> \<Pi> \<and> \<beta>' = \<pi> @ (\<tau> i))
              \<or> (\<exists> i j . i < j \<and> i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> \<alpha>' = \<pi> @ (\<tau> i) \<and> \<beta>' = \<pi> @ (\<tau> j)))"
      using \<open>\<alpha> \<in> L M\<close> \<open>\<beta> \<in> L M\<close> \<open>\<not> converge M \<alpha> \<beta>\<close> \<open>converge I \<alpha> \<beta>\<close> \<open>\<not> converge M \<beta> \<alpha>\<close> \<open>converge I \<beta> \<alpha>\<close> 
      by metis

    then obtain \<alpha>' \<beta>' where "\<alpha>' \<in> L M" and "\<beta>' \<in> L M" and "\<not>converge M \<alpha>' \<beta>'" and "converge I \<alpha>' \<beta>' "
                        and "(\<alpha>' \<in> \<Pi> \<and> \<beta>' \<in> \<Pi>) 
                              \<or> (\<exists> i . i \<in> {1 .. m-n+1} \<and> \<alpha>' \<in> \<Pi> \<and> \<beta>' = \<pi> @ (\<tau> i))
                              \<or> (\<exists> i j . i < j \<and> i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> \<alpha>' = \<pi> @ (\<tau> i) \<and> \<beta>' = \<pi> @ (\<tau> j))"
      by blast
    then consider "\<alpha>' \<in> \<Pi> \<and> \<beta>' \<in> \<Pi>"
      | "\<exists> i . i \<in> {1 .. m-n+1} \<and> \<alpha>' \<in> \<Pi> \<and> \<beta>' = \<pi> @ (\<tau> i)"
      | "\<exists> i j . i < j \<and> i \<in> {1 .. m-n+1} \<and> j \<in> {1 .. m-n+1} \<and> \<alpha>' = \<pi> @ (\<tau> i) \<and> \<beta>' = \<pi> @ (\<tau> j)"
      by blast

    then show False proof cases
      case 1
      moreover have "preserves_divergence M I \<Pi>"
        using dist_prop[OF reachable_states_initial, of "[]"] language_contains_empty_sequence[of M] by auto
      ultimately show ?thesis 
        using \<open>\<not>converge M \<alpha>' \<beta>'\<close> \<open>converge I \<alpha>' \<beta>'\<close> \<open>\<alpha>' \<in> L M\<close> \<open>\<beta>' \<in> L M\<close>
        unfolding preserves_divergence.simps 
        by blast
    next
      case 2
      then obtain i where "i \<in> {1 .. m-n+1}" and "\<alpha>' \<in> \<Pi>" and "\<beta>' = \<pi> @ (\<tau> i)"
        by blast
      then have "\<tau> i \<in> \<X> q" 
        using \<open>\<And> i . i > 0 \<Longrightarrow> i \<le> m - n + 1 \<Longrightarrow> (\<tau> i) \<in> \<X> q\<close>
        by force 

      have "\<beta>' \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (\<tau> i))}"
        unfolding \<open>\<beta>' = \<pi> @ (\<tau> i)\<close> \<open>\<pi> = V q\<close> prefixes_set by auto 
      then have "\<not>converge I \<alpha>' \<beta>'"
        using \<open>\<alpha>' \<in> \<Pi>\<close> \<open>\<not>converge M \<alpha>' \<beta>'\<close> \<open>\<alpha>' \<in> L M\<close> \<open>\<beta>' \<in> L M\<close>
        using dist_prop_\<X>[OF \<open>q \<in> reachable_states M\<close> \<open>\<tau> i \<in> \<X> q\<close>]
        unfolding preserves_divergence.simps by blast
      then show False
        using \<open>converge I \<alpha>' \<beta>'\<close> by blast
    next
      case 3
      then obtain i j where "i \<in> {1 .. m-n+1}" and "j \<in> {1 .. m-n+1}" and "\<alpha>' = \<pi> @ (\<tau> i)" and "\<beta>' = \<pi> @ (\<tau> j)" and "i < j" by blast
      then have "\<tau> j \<in> \<X> q" 
        using \<open>\<And> i . i > 0 \<Longrightarrow> i \<le> m - n + 1 \<Longrightarrow> (\<tau> i) \<in> \<X> q\<close>
        by force 

      have "(\<tau> i) = take i (\<tau> j)"
        using \<open>i < j\<close> unfolding \<tau>_def
        by simp
      then have "(\<tau> i) \<in> list.set (prefixes (\<tau> j))"
        unfolding prefixes_set
        by (metis (mono_tags) append_take_drop_id mem_Collect_eq)
      then have "\<alpha>' \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (\<tau> j))}"
        unfolding \<open>\<alpha>' = \<pi> @ (\<tau> i)\<close> \<open>\<pi> = V q\<close>
        by simp
      moreover have "\<beta>' \<in> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (\<tau> j))}"
        unfolding \<open>\<beta>' = \<pi> @ (\<tau> j)\<close> \<open>\<pi> = V q\<close> prefixes_set by auto 
      ultimately have "\<not>converge I \<alpha>' \<beta>'"
        using \<open>\<not>converge M \<alpha>' \<beta>'\<close> \<open>\<alpha>' \<in> L M\<close> \<open>\<beta>' \<in> L M\<close>
        using dist_prop_\<X>[OF \<open>q \<in> reachable_states M\<close> \<open>\<tau> j \<in> \<X> q\<close>]
        unfolding preserves_divergence.simps by blast
      then show False
        using \<open>converge I \<alpha>' \<beta>'\<close> by blast
    qed
  qed


  have case_helper: "\<And> A B P . (\<And> x y . P x y = P y x) \<Longrightarrow> 
                                (\<exists> x y . x \<in> A \<union> B \<and> y \<in> A \<union> B \<and> P x y) =
                                          ((\<exists> x y . x \<in> A \<and> y \<in> A \<and> P x y)
                                            \<or> (\<exists> x y . x \<in> A \<and> y \<in> B \<and> P x y)
                                            \<or> (\<exists> x y . x \<in> B \<and> y \<in> B \<and> P x y))"
    by auto
  have *: "(\<And>x y. (x \<noteq> y \<and> FSM.after I (FSM.initial I) x = FSM.after I (FSM.initial I) y) =
          (y \<noteq> x \<and> FSM.after I (FSM.initial I) y = FSM.after I (FSM.initial I) x))"
    by auto
    
  consider (a) "\<exists> \<alpha> \<beta> . \<alpha> \<in> \<Pi> \<and> \<beta> \<in> \<Pi> \<and> \<alpha> \<noteq> \<beta> \<and> (after_initial I \<alpha> = after_initial I \<beta>)" | 
           (b) "\<exists> \<alpha> \<beta> . \<alpha> \<in> \<Pi> \<and> \<beta> \<in> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} \<and> \<alpha> \<noteq> \<beta> \<and> (after_initial I \<alpha> = after_initial I \<beta>)" |
           (c) "\<exists> \<alpha> \<beta> . \<alpha> \<in> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} \<and> \<beta> \<in> (\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1} \<and> \<alpha> \<noteq> \<beta> \<and> (after_initial I \<alpha> = after_initial I \<beta>)" 
    using same_targets_in_I
    unfolding case_helper[of "\<lambda> x y . x \<noteq> y \<and> (after_initial I x = after_initial I y)" \<Pi> "(\<lambda>i . \<pi> @ (\<tau> i)) ` {1 .. m-n+1}", OF *] 
    by blast
  then show "False" proof cases
    case a (* elements of the state cover cannot coincide *)
    then obtain \<alpha> \<beta>  where "\<alpha> \<in> \<Pi>" and "\<beta> \<in> \<Pi>" and "\<alpha> \<noteq> \<beta>" and "(after_initial I \<alpha> = after_initial I \<beta>)" by blast
    then have "(after_initial M \<alpha> = after_initial M \<beta>)"
      using same_targets_in_M by blast

    obtain q1 q2 where "q1 \<in> reachable_states M" and "\<alpha> = V q1"
                   and "q2 \<in> reachable_states M" and "\<beta> = V q2"
      using \<open>\<alpha> \<in> \<Pi>\<close> \<open>\<beta> \<in> \<Pi>\<close> \<open>\<alpha> \<noteq> \<beta>\<close>
      unfolding \<Pi> by blast
    then have "q1 \<noteq> q2"
      using \<open>\<alpha> \<noteq> \<beta>\<close> by auto

    have "\<alpha> \<in> L M" 
      using \<open>\<Pi> \<subseteq> L M\<close> \<open>\<alpha> \<in> \<Pi>\<close> by blast
    have "q1 = after_initial M \<alpha>"
      using \<open>is_state_cover_assignment M V\<close> \<open>q1 \<in> reachable_states M\<close> observable_io_targets[OF \<open>observable M\<close> \<open>\<alpha> \<in> L M\<close>] 
      unfolding is_state_cover_assignment.simps \<open>\<alpha> = V q1\<close>
      by (metis \<open>is_state_cover_assignment M V\<close> assms(1) is_state_cover_assignment_observable_after)

    have "\<beta> \<in> L M" 
      using \<open>\<Pi> \<subseteq> L M\<close> \<open>\<beta> \<in> \<Pi>\<close> by blast
    have "q2 = after_initial M \<beta>"
      using \<open>is_state_cover_assignment M V\<close> \<open>q2 \<in> reachable_states M\<close> observable_io_targets[OF \<open>observable M\<close> \<open>\<beta> \<in> L M\<close>] 
      unfolding is_state_cover_assignment.simps \<open>\<beta> = V q2\<close>
      by (metis \<open>is_state_cover_assignment M V\<close> assms(1) is_state_cover_assignment_observable_after)

    show "False"
      using \<open>q1 \<noteq> q2\<close> \<open>(after_initial M \<alpha> = after_initial M \<beta>)\<close>
      unfolding \<open>q1 = after_initial M \<alpha>\<close> \<open>q2 = after_initial M \<beta>\<close> 
      by simp
  next
    case b (* state cover and \<pi>@(\<tau> i) cannot coincide due to minimality of \<pi>@\<tau>' *)
    then obtain \<alpha> \<beta> where "\<alpha> \<in> \<Pi>"
                      and "\<beta> \<in> (\<lambda>i. \<pi> @ \<tau> i) ` {1..m - n + 1}"
                      and "\<alpha> \<noteq> \<beta>" 
                      and "FSM.after I (FSM.initial I) \<alpha> = FSM.after I (FSM.initial I) \<beta>"
      by blast
    then have "FSM.after M (FSM.initial M) \<alpha> = FSM.after M (FSM.initial M) \<beta>"
      using same_targets_in_M by blast

    obtain i where "\<beta> = \<pi>@(\<tau> i)" and "i \<in> {1..m - n + 1}"
      using \<open>\<beta> \<in> (\<lambda>i. \<pi> @ \<tau> i) ` {1..m - n + 1}\<close> by auto

    have "\<alpha> \<in> L M" and "\<alpha> \<in> L I" 
      using \<open>\<Pi> \<subseteq> L M\<close>  \<open>\<Pi> \<subseteq> L I\<close> \<open>\<alpha> \<in> \<Pi>\<close> by blast+
    have "\<beta> \<in> L M" and "\<beta> \<in> L I" 
      using \<open>\<beta> \<in> (\<lambda>i. \<pi> @ \<tau> i) ` {1..m - n + 1}\<close> \<open>\<And> i . i \<le> m-n+1 \<Longrightarrow> \<pi> @ (\<tau> i) \<in> L M \<inter> L I\<close> 
      by auto

    let ?io = "drop i \<tau>'"

    have "\<tau>' = (\<tau> i) @ ?io"
      using \<open>i \<in> {1..m - n + 1}\<close> \<open>length \<tau>' > m-n+1\<close> 
      unfolding \<tau>_def
      by (metis (no_types, lifting) antisym_conv append_take_drop_id atLeastAtMost_iff less_or_eq_imp_le linorder_neqE_nat order.trans take_butlast)
    then have "\<beta>@?io \<in> (L M - L I) \<union> (L I - L M)"
      using \<open>\<beta> = \<pi>@(\<tau> i)\<close>  \<open>\<pi> @ \<tau>' \<in> (L M - L I) \<union> (L I - L M)\<close>
      by auto
    then have "\<alpha>@?io \<in> (L M - L I) \<union> (L I - L M)"
      using observable_after_eq[OF \<open>observable M\<close> \<open>FSM.after M (FSM.initial M) \<alpha> = FSM.after M (FSM.initial M) \<beta>\<close> \<open>\<alpha> \<in> L M\<close> \<open>\<beta> \<in> L M\<close>]
            observable_after_eq[OF \<open>observable I\<close> \<open>FSM.after I (FSM.initial I) \<alpha> = FSM.after I (FSM.initial I) \<beta>\<close> \<open>\<alpha> \<in> L I\<close> \<open>\<beta> \<in> L I\<close>]
      by blast
    then show "False"
      using \<tau>'_min[OF \<open>\<alpha> \<in> \<Pi>\<close>, of ?io] \<open>length \<tau>' > m - n + 1\<close> \<open>i \<in> {1..m - n + 1}\<close>
      by (metis One_nat_def add_diff_cancel_left' atLeastAtMost_iff diff_diff_cancel diff_is_0_eq' length_drop less_Suc_eq nat_le_linear not_add_less2)
  next
    case c (* \<pi>@(\<tau> i) and \<pi>@(\<tau> j) cannot coincide due to minimality of \<pi>@\<tau>' *)
    then have "\<exists> i j  . i \<noteq> j \<and> i \<in> {1..m - n + 1} \<and> j \<in> {1..m - n + 1} \<and> (after_initial I (\<pi>@(\<tau> i)) = after_initial I (\<pi>@(\<tau> j)))"
      by force
    then have "\<exists> i j  . i < j \<and> i \<in> {1..m - n + 1} \<and> j \<in> {1..m - n + 1} \<and> (after_initial I (\<pi>@(\<tau> i)) = after_initial I (\<pi>@(\<tau> j)))"
      by (metis linorder_neqE_nat)
    then obtain i j  where "i \<in> {1..m - n + 1}"
                       and "j \<in> {1..m - n + 1}"
                       and "i < j"
                       and "FSM.after I (FSM.initial I) (\<pi>@(\<tau> i)) = FSM.after I (FSM.initial I) (\<pi>@(\<tau> j))"
      by force

    have "(\<pi>@(\<tau> i)) \<in> (\<lambda>i. \<pi> @ \<tau> i) ` {1..m - n + 1}" and "(\<pi>@(\<tau> j)) \<in> (\<lambda>i. \<pi> @ \<tau> i) ` {1..m - n + 1}"
      using \<open>i \<in> {1..m - n + 1}\<close> \<open>j \<in> {1..m - n + 1}\<close>
      by auto
    moreover have "(\<pi>@(\<tau> i)) \<noteq> (\<pi>@(\<tau> j))"
    proof -
      have "j \<le> length (butlast \<tau>')"
        using \<open>j \<in> {1..m - n + 1}\<close> \<open>length \<tau>' > m - n + 1\<close> by auto
      moreover have "\<And> xs . j \<le> length xs \<Longrightarrow> i < j \<Longrightarrow> take j xs \<noteq> take i xs"
        by (metis dual_order.strict_implies_not_eq length_take min.absorb2 min_less_iff_conj)
      ultimately show ?thesis
        using \<open>i < j\<close> unfolding \<tau>_def
        by fastforce 
    qed
    ultimately have "FSM.after M (FSM.initial M) (\<pi>@(\<tau> i)) = FSM.after M (FSM.initial M) (\<pi>@(\<tau> j))"
      using \<open>FSM.after I (FSM.initial I) (\<pi>@(\<tau> i)) = FSM.after I (FSM.initial I) (\<pi>@(\<tau> j))\<close>
            same_targets_in_M 
      by blast

    have "(\<pi>@(\<tau> i)) \<in> L M" and "(\<pi>@(\<tau> i)) \<in> L I" and "(\<pi>@(\<tau> j)) \<in> L M" and "(\<pi>@(\<tau> j)) \<in> L I" 
      using \<open>\<And> i . i \<le> m-n+1 \<Longrightarrow> \<pi> @ (\<tau> i) \<in> L M \<inter> L I\<close> \<open>i \<in> {1..m - n + 1}\<close> \<open>j \<in> {1..m - n + 1}\<close> 
      by auto

    let ?io = "drop j \<tau>'"
    have "\<tau>' = (\<tau> j) @ ?io"
      using \<open>j \<in> {1..m - n + 1}\<close> \<open>length \<tau>' > m-n+1\<close> 
      unfolding \<tau>_def
      by (metis (no_types, lifting) antisym_conv append_take_drop_id atLeastAtMost_iff less_or_eq_imp_le linorder_neqE_nat order.trans take_butlast)
    then have "(\<pi>@(\<tau> j))@?io \<in> (L M - L I) \<union> (L I - L M)"
      using \<open>\<pi> @ \<tau>' \<in> (L M - L I) \<union> (L I - L M)\<close>
      by (simp add: \<tau>_def)
    then have "(\<pi>@(\<tau> i))@?io \<in> (L M - L I) \<union> (L I - L M)"
      using observable_after_eq[OF \<open>observable M\<close> \<open>FSM.after M (FSM.initial M) (\<pi>@(\<tau> i)) = FSM.after M (FSM.initial M) (\<pi>@(\<tau> j))\<close> \<open>(\<pi>@(\<tau> i)) \<in> L M\<close> \<open>(\<pi>@(\<tau> j)) \<in> L M\<close>]
            observable_after_eq[OF \<open>observable I\<close> \<open>FSM.after I (FSM.initial I) (\<pi>@(\<tau> i)) = FSM.after I (FSM.initial I) (\<pi>@(\<tau> j))\<close> \<open>(\<pi>@(\<tau> i)) \<in> L I\<close> \<open>(\<pi>@(\<tau> j)) \<in> L I\<close>]
      by blast
    then have "\<pi>@(\<tau> i)@?io \<in> (L M - L I) \<union> (L I - L M)"
      by auto
    moreover have "length \<tau>' > length (\<tau> i @ drop j \<tau>')"
      using \<open>length \<tau>' > m - n + 1\<close> \<open>j \<in> {1..m - n + 1}\<close> \<open>i < j\<close> unfolding \<tau>_def by force
    ultimately show "False"
      using \<tau>'_min[OF \<open>\<pi> \<in> \<Pi>\<close>, of "(\<tau> i) @ ?io"] 
      by simp
  qed
qed



lemma abstract_h_condition_soundness :
  assumes "observable M"
  and     "observable I"
  and     "is_state_cover_assignment M V"
  and     "L M = L I"
shows "satisfies_abstract_h_condition M I V m"
  using assms(3,4) equivalence_preserves_divergence[OF assms(1,2,4)]
  unfolding satisfies_abstract_h_condition_def Let_def by blast
  


lemma abstract_h_condition_completeness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
  and     "is_state_cover_assignment M V"
shows "satisfies_abstract_h_condition M I V m \<longleftrightarrow> (L M = L I)"
  using abstract_h_condition_soundness[OF assms(1,2,8)]
  using abstract_h_condition_exhaustiveness[OF assms]
  by blast


    
subsection \<open>Definition of the Framework\<close>


definition h_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment) \<Rightarrow>                        
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> (('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow>
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> ('a,'b,'c) transition list) \<Rightarrow>                              
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) transition \<Rightarrow>  ('a,'b,'c) transition list \<Rightarrow> ( ('a,'b,'c) transition list \<times> ('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow> 
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> (('b\<times>'c) prefix_tree) \<times> 'd) \<Rightarrow> 
                              (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow>
                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                              nat \<Rightarrow>
                              ('b\<times>'c) prefix_tree" 
  where
  "h_framework M 
               get_state_cover 
               handle_state_cover
               sort_transitions
               handle_unverified_transition
               handle_unverified_io_pair
               cg_initial
               cg_insert
               cg_lookup
               cg_merge
               m
  = (let
      rstates_set = reachable_states M;
      rstates     = reachable_states_as_list M;
      rstates_io  = List.product rstates (List.product (inputs_as_list M) (outputs_as_list M));
      undefined_io_pairs = List.filter (\<lambda> (q,(x,y)) . h_obs M q x y = None) rstates_io;
      V           = get_state_cover M;
      TG1         = handle_state_cover M V cg_initial cg_insert cg_lookup;
      sc_covered_transitions = (\<Union> q \<in> rstates_set . covered_transitions M V (V q));
      unverified_transitions = sort_transitions M V (filter (\<lambda>t . t_source t \<in> rstates_set \<and> t \<notin> sc_covered_transitions) (transitions_as_list M));
      verify_transition = (\<lambda> (X,T,G) t . handle_unverified_transition M V T G cg_insert cg_lookup cg_merge m t X);
      TG2         = snd (foldl verify_transition (unverified_transitions, TG1) unverified_transitions);
      verify_undefined_io_pair = (\<lambda> T (q,(x,y)) . fst (handle_unverified_io_pair M V T (snd TG2) cg_insert cg_lookup q x y))
    in
      foldl verify_undefined_io_pair (fst TG2) undefined_io_pairs)"


subsection \<open>Required Conditions on Procedural Parameters\<close>

definition separates_state_cover :: "(('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> (('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow>
                                  ('a,'b,'c) fsm \<Rightarrow>
                                  ('e,'b,'c) fsm \<Rightarrow>
                                  (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                  bool"
  where 
  "separates_state_cover f M1 M2 cg_initial cg_insert cg_lookup = 
    (\<forall> V .
        (V ` reachable_states M1 \<subseteq> set (fst (f M1 V cg_initial cg_insert cg_lookup)))
        \<and> finite_tree (fst (f M1 V cg_initial cg_insert cg_lookup))
        \<and> (observable M1 \<longrightarrow>
            observable M2 \<longrightarrow>
            minimal M1 \<longrightarrow>
            minimal M2 \<longrightarrow>
            inputs M2 = inputs M1 \<longrightarrow>
            outputs M2 = outputs M1 \<longrightarrow>
            is_state_cover_assignment M1 V \<longrightarrow>
            convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
            convergence_graph_initial_invar M1 M2 cg_lookup cg_initial \<longrightarrow>
            L M1 \<inter> set (fst (f M1 V cg_initial cg_insert cg_lookup)) = L M2 \<inter> set (fst (f M1 V cg_initial cg_insert cg_lookup)) \<longrightarrow>
            (preserves_divergence M1 M2 (V ` reachable_states M1)
            \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (f M1 V cg_initial cg_insert cg_lookup)))))"


definition handles_transition :: "(('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                    ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                    ('b\<times>'c) prefix_tree \<Rightarrow> 
                                    'd \<Rightarrow>
                                    ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                    ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                                    ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                    nat \<Rightarrow>
                                    ('a,'b,'c) transition \<Rightarrow> 
                                    ('a,'b,'c) transition list \<Rightarrow>   
                                    (('a,'b,'c) transition list \<times> ('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow>   
                                  ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                  ('e,'b,'c) fsm \<Rightarrow>
                                  ('a,'b,'c) state_cover_assignment \<Rightarrow>    
                                  ('b\<times>'c) prefix_tree \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                  bool"
  where 
  "handles_transition f M1 M2 V T0 cg_insert cg_lookup cg_merge = 
    (\<forall> T G m t X .
        (set T \<subseteq> set (fst (snd (f M1 V T G cg_insert cg_lookup cg_merge m t X))))
        \<and> (finite_tree T \<longrightarrow> finite_tree (fst (snd (f M1 V T G cg_insert cg_lookup cg_merge m t X))))
        \<and> (observable M1 \<longrightarrow>
            observable M2 \<longrightarrow>
            minimal M1 \<longrightarrow>
            minimal M2 \<longrightarrow>
            size_r M1 \<le> m \<longrightarrow>
            size M2 \<le> m \<longrightarrow>
            inputs M2 = inputs M1 \<longrightarrow>
            outputs M2 = outputs M1 \<longrightarrow>
            is_state_cover_assignment M1 V \<longrightarrow>
            preserves_divergence M1 M2 (V ` reachable_states M1) \<longrightarrow>
            V ` reachable_states M1 \<subseteq> set T \<longrightarrow>
            t \<in> transitions M1 \<longrightarrow>
            t_source t \<in> reachable_states M1 \<longrightarrow>
            ((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t)) \<longrightarrow>  
            convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow>
            convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
            convergence_graph_merge_invar M1 M2 cg_lookup cg_merge \<longrightarrow>
            L M1 \<inter> set (fst (snd (f M1 V T G cg_insert cg_lookup cg_merge m t X))) = L M2 \<inter> set (fst (snd (f M1 V T G cg_insert cg_lookup cg_merge m t X))) \<longrightarrow>
            (set T0 \<subseteq> set T) \<longrightarrow>
            (\<forall> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                    \<longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                          = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                         \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})))   
            \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (f M1 V T G cg_insert cg_lookup cg_merge m t X)))))"


definition handles_io_pair :: "(('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                            ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                            ('b\<times>'c) prefix_tree \<Rightarrow> 
                                            'd \<Rightarrow>
                                            ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                            ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                            'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow>  
                                            (('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow>
                                          ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                          ('e,'b,'c) fsm \<Rightarrow>
                                          ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                          ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>                                     
                                          bool"
  where 
  "handles_io_pair f M1 M2 cg_insert cg_lookup = 
    (\<forall> V T G q x y .
        (set T \<subseteq> set (fst (f M1 V T G cg_insert cg_lookup q x y)))
        \<and> (finite_tree T \<longrightarrow> finite_tree (fst (f M1 V T G cg_insert cg_lookup q x y)))
        \<and> (observable M1 \<longrightarrow>
            observable M2 \<longrightarrow>
            minimal M1 \<longrightarrow>
            minimal M2 \<longrightarrow>
            inputs M2 = inputs M1 \<longrightarrow>
            outputs M2 = outputs M1 \<longrightarrow>
            is_state_cover_assignment M1 V \<longrightarrow>
            L M1 \<inter> (V ` reachable_states M1) = L M2 \<inter> V ` reachable_states M1 \<longrightarrow>
            q \<in> reachable_states M1 \<longrightarrow>
            x \<in> inputs M1 \<longrightarrow> 
            y \<in> outputs M1 \<longrightarrow> 
            convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow>   
            convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
            L M1 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y)) \<longrightarrow>
            ( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} )
            \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (f M1 V T G cg_insert cg_lookup q x y))))"



subsection \<open>Completeness and Finiteness of the Scheme\<close>


lemma unverified_transitions_handle_all_transitions :
  assumes "observable M1"
  and     "is_state_cover_assignment M1 V"
  and     "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
  and     "preserves_divergence M1 M2 (V ` reachable_states M1)"
  and     handles_unverified_transitions: "\<And> t \<gamma> . t \<in> transitions M1 \<Longrightarrow>
                                            t_source t \<in> reachable_states M1 \<Longrightarrow>
                                            length \<gamma> \<le> k \<Longrightarrow> 
                                            list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<Longrightarrow> 
                                            butlast \<gamma> \<in> LS M1 (t_target t) \<Longrightarrow>
                                            (V (t_target t) \<noteq> (V (t_source t))@[(t_input t, t_output t)]) \<Longrightarrow>
                                            ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                                               = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                                             \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
  and     handles_undefined_io_pairs: "\<And> q x y . q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> h_obs M1 q x y = None \<Longrightarrow> L M1 \<inter> {V q @ [(x,y)]} = L M2 \<inter> {V q @ [(x,y)]}"
  and     "t \<in> transitions M1"
  and     "t_source t \<in> reachable_states M1"
  and     "length \<gamma> \<le> k"
  and     "list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1"
  and     "butlast \<gamma> \<in> LS M1 (t_target t)"
shows "(L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
         = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
        \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
proof (cases "V (t_target t) \<noteq> V (t_source t) @ [(t_input t, t_output t)]")
  case True
  then show ?thesis 
    using handles_unverified_transitions[OF assms(7-11)] 
    by blast
next
  case False
  then have "V (t_source t) @ [(t_input t, t_output t)] = V (t_target t)"
    by simp
  have "\<And> \<gamma> . length \<gamma> \<le> k \<Longrightarrow>
             list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<Longrightarrow> 
             butlast \<gamma> \<in> LS M1 (t_target t) \<Longrightarrow>
             L M1 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) =
               L M2 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<and>
             preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
  proof -
    fix \<gamma> assume "length \<gamma> \<le> k" and "list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1" and "butlast \<gamma> \<in> LS M1 (t_target t)"
    then show "L M1 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) =
                 L M2 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<and>
               preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"
      using \<open>t \<in> transitions M1\<close> \<open>t_source t \<in> reachable_states M1\<close> \<open>V (t_source t) @ [(t_input t, t_output t)] = V (t_target t)\<close>
    proof (induction \<gamma> arbitrary: t)
      case Nil
      have "{(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes [])} = {V (t_target t)}"
        unfolding Nil by auto
      then have *: "(V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes [])}) = V ` reachable_states M1"
        using reachable_states_next[OF Nil.prems(5,4)] by blast
      show ?case 
        unfolding *
        using assms(3,4) 
        by blast
    next
      case (Cons xy \<gamma>)
      then obtain x y where "xy = (x,y)" by auto
      then have "x \<in> inputs M1" and "y \<in> outputs M1"
        using Cons.prems(2) by auto

      have "t_target t \<in> reachable_states M1"
        using reachable_states_next[OF Cons.prems(5,4)] by blast
      then have "after_initial M1 (V (t_target t)) = t_target t"
        using \<open>is_state_cover_assignment M1 V\<close> 
        by (metis assms(1) is_state_cover_assignment_observable_after)

      show ?case proof (cases "[xy] \<in> LS M1 (t_target t)")
        case False
        then have "h_obs M1 (t_target t) x y = None"
          using Cons.prems(4,5) \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close> unfolding \<open>xy = (x,y)\<close>
          by (meson assms(1) h_obs_language_single_transition_iff) 
        then have "L M1 \<inter> {V (t_target t) @ [(x, y)]} = L M2 \<inter> {V (t_target t) @ [(x, y)]}"
          using handles_undefined_io_pairs[OF \<open>t_target t \<in> reachable_states M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>] by blast      
        
        have "V (t_target t) @ [(x, y)] \<notin> L M1"
          using False \<open>after_initial M1 (V (t_target t)) = t_target t\<close> 
          unfolding \<open>xy = (x,y)\<close>
          by (metis assms(1) language_prefix observable_after_language_none) 
        then have "preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {V (t_target t) @ [(x, y)]})"
          using assms(4)
          unfolding preserves_divergence.simps
          by blast 

        have "\<gamma> = []"
          using False Cons.prems(3) 
          by (metis (no_types, lifting) LS_single_transition \<open>xy = (x, y)\<close> butlast.simps(2) language_next_transition_ob)
        then have "list.set (prefixes (xy#\<gamma>)) = {[], [(x,y)]}"
          unfolding \<open>xy = (x,y)\<close>
          by force 
        then have "{(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (xy # \<gamma>))} = {V (t_target t), V (t_target t) @ [(x, y)]}"
          unfolding Cons by auto
        then have *:"(V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (xy # \<gamma>))}) = (V ` reachable_states M1 \<union> {V (t_target t) @ [(x, y)]})"
          using reachable_states_next[OF Cons.prems(5,4)] by blast

        

        show ?thesis 
          unfolding *
          using assms(3)
                \<open>L M1 \<inter> {V (t_target t) @ [(x, y)]} = L M2 \<inter> {V (t_target t) @ [(x, y)]}\<close>
                \<open>preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {V (t_target t) @ [(x, y)]})\<close>    
          by blast
      next
        case True

        then obtain t' where "t_source t' = t_target t" and "t_input t' = x" and "t_output t' = y" and "t' \<in> transitions M1"
          unfolding \<open>xy = (x,y)\<close>
          by auto 
        then have "t_target t' \<in> reachable_states M1" and "t_source t' \<in> reachable_states M1"
          using reachable_states_next[OF \<open>t_target t \<in> reachable_states M1\<close>, of t'] \<open>t_target t \<in> reachable_states M1\<close> by auto

        have *: "length \<gamma> \<le> k"
          using Cons.prems(1) by auto
        have **: "list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1"
          using Cons.prems(2) by auto
        have ***: "butlast \<gamma> \<in> LS M1 (t_target t')"
          using Cons.prems(3)
          by (metis True \<open>t' \<in> FSM.transitions M1\<close> \<open>t_input t' = x\<close> \<open>t_output t' = y\<close> \<open>t_source t' = t_target t\<close> \<open>xy = (x, y)\<close> assms(1) butlast.simps(1) butlast.simps(2) observable_language_transition_target)                
        
        have "{(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (xy # \<gamma>))} = {((V (t_source t) @ [(t_input t, t_output t)]) @ [xy]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<union> {V (t_source t) @ [(t_input t, t_output t)]}"
          by (induction \<gamma>; auto) 
        moreover have "{((V (t_source t) @ [(t_input t, t_output t)]) @ [xy]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} = {(V (t_source t') @ [(t_input t', t_output t')]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}"
          unfolding \<open>t_source t' = t_target t\<close> \<open>t_input t' = x\<close> \<open>t_output t' = y\<close> \<open>xy = (x,y)\<close>[symmetric] Cons.prems(6)[symmetric] by simp
        ultimately have "{(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (xy # \<gamma>))} = {(V (t_source t') @ [(t_input t', t_output t')]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} \<union> {V (t_target t)}"
          unfolding Cons by force
        then have ****: "V ` reachable_states M1 \<union> {(V (t_source t') @ [(t_input t', t_output t')]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}
                          = V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes (xy # \<gamma>))}"
          using \<open>t_source t' = t_target t\<close> \<open>t_source t' \<in> reachable_states M1\<close> by force

      

        show ?thesis proof (cases "V (t_source t') @ [(t_input t', t_output t')] = V (t_target t')")
          case True
          show ?thesis
            using Cons.IH[OF * ** *** \<open>t' \<in> transitions M1\<close> \<open>t_source t' \<in> reachable_states M1\<close> True]
            unfolding **** .
        next
          case False
          then show ?thesis
            using handles_unverified_transitions[OF \<open>t' \<in> transitions M1\<close> \<open>t_source t' \<in> reachable_states M1\<close> * ** ***]
            unfolding ****
            by presburger
        qed
      qed
    qed
  qed
  then show ?thesis
    using assms(9-11)
    by blast
qed

lemma abstract_h_condition_by_transition_and_io_pair_coverage :
  assumes "observable M1"
  and     "is_state_cover_assignment M1 V"
  and     "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
  and     "preserves_divergence M1 M2 (V ` reachable_states M1)"
  and     handles_unverified_transitions: "\<And> t \<gamma> . t \<in> transitions M1 \<Longrightarrow>
                                            t_source t \<in> reachable_states M1 \<Longrightarrow>
                                            length \<gamma> \<le> k \<Longrightarrow> 
                                            list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<Longrightarrow> 
                                            butlast \<gamma> \<in> LS M1 (t_target t) \<Longrightarrow>
                                            ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                                               = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                                             \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
  and     handles_undefined_io_pairs: "\<And> q x y . q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> h_obs M1 q x y = None \<Longrightarrow> L M1 \<inter> {V q @ [(x,y)]} = L M2 \<inter> {V q @ [(x,y)]}"  
  and     "q \<in> reachable_states M1"
  and     "length \<gamma> \<le> Suc k"
  and     "list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1"
  and     "butlast \<gamma> \<in> LS M1 q"
shows "(L M1 \<inter> (V ` reachable_states M1 \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
         = L M2 \<inter> (V ` reachable_states M1 \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
        \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"   
proof (cases \<gamma>)
  case Nil 
  show ?thesis 
    using assms(3,4,7) unfolding Nil by auto
next
  case (Cons xy \<gamma>')
  then obtain x y where "xy = (x,y)" using prod.exhaust by metis
  then have "x \<in> inputs M1" and "y \<in> outputs M1"
    using assms(9) Cons by auto

  show ?thesis proof (cases "[xy] \<in> LS M1 q")
    case False
    then have "h_obs M1 q x y = None"
      using assms(7) \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close> unfolding \<open>xy = (x,y)\<close>
      by (meson assms(1) h_obs_language_single_transition_iff) 
    then have "L M1 \<inter> {V q @ [(x,y)]} = L M2 \<inter> {V q @ [(x,y)]}"
      using handles_undefined_io_pairs[OF assms(7) \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>] by blast

    have "V q @ [(x, y)] \<notin> L M1"
      using observable_after_language_none[OF assms(1), of "V q" "initial M1" "[(x,y)]"]
      using state_cover_assignment_after[OF assms(1,2,7)]
      by (metis False \<open>xy = (x, y)\<close>) 
    then have "preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {V q @ [(x, y)]})"
      using assms(4)
      unfolding preserves_divergence.simps
      by blast 


    have "\<gamma>' = []"
      using False assms(10) language_prefix[of "[xy]" \<gamma>' M1 q]
      unfolding Cons 
      by (metis (no_types, lifting) LS_single_transition \<open>xy = (x, y)\<close> butlast.simps(2) language_next_transition_ob)
    then have "\<gamma> = [(x,y)]"
      unfolding Cons \<open>xy = (x,y)\<close> by auto
    then have *: "(V ` reachable_states M1 \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) = V ` reachable_states M1 \<union> {V q @ [(x,y)]}"
      using assms(7) by auto

    show ?thesis
      unfolding *
      using assms(3) \<open>L M1 \<inter> {V q @ [(x,y)]} = L M2 \<inter> {V q @ [(x,y)]}\<close> \<open>preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {V q @ [(x, y)]})\<close>
      by blast
  next
    case True
    moreover have "butlast ((x,y)#\<gamma>') \<in> LS M1 q"
      using assms(10) unfolding Cons \<open>xy = (x,y)\<close> .
    ultimately have "(x,y) # (butlast \<gamma>') \<in> LS M1 q" 
      unfolding  \<open>xy = (x,y)\<close> by (cases \<gamma>'; auto)
    then obtain q' where "h_obs M1 q x y = Some q'" and "butlast \<gamma>' \<in> LS M1 q'"
      using h_obs_language_iff[OF assms(1), of x y "butlast \<gamma>'" q]
      by blast
    then have "(q,x,y,q') \<in> transitions M1"
      unfolding h_obs_Some[OF assms(1)] by blast

    

    have "length \<gamma>' \<le> k"
      using assms(8) unfolding Cons by auto
    have "list.set \<gamma>' \<subseteq> inputs M1 \<times> outputs M1"    
      using assms(9) unfolding Cons by auto
    
    have *:"(L M1 \<inter> (V ` reachable_states M1 \<union> {(V q @ [(x,y)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>')})
         = L M2 \<inter> (V ` reachable_states M1 \<union> {(V q @ [(x,y)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>')}))
        \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {(V q @ [(x,y)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>')})"
      using handles_unverified_transitions[OF \<open>(q,x,y,q') \<in> transitions M1\<close> _ \<open>length \<gamma>' \<le> k\<close> \<open>list.set \<gamma>' \<subseteq> inputs M1 \<times> outputs M1\<close>]
            assms(7) \<open>butlast \<gamma>' \<in> LS M1 q'\<close>
      unfolding fst_conv snd_conv 
      by blast

    have "{V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} = {(V q @ [(x, y)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>')} \<union> {V q}"
      unfolding Cons \<open>xy = (x,y)\<close> by auto 
    then have **: "V ` reachable_states M1 \<union> {V q @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)} 
                    = V ` reachable_states M1 \<union> {(V q @ [(x, y)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>')}"
      using assms(7) by blast

    show ?thesis
      using * unfolding ** .
  qed
qed


lemma abstract_h_condition_by_unverified_transition_and_io_pair_coverage :
  assumes "observable M1"
  and     "is_state_cover_assignment M1 V"
  and     "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
  and     "preserves_divergence M1 M2 (V ` reachable_states M1)"
  and     handles_unverified_transitions: "\<And> t \<gamma> . t \<in> transitions M1 \<Longrightarrow>
                                            t_source t \<in> reachable_states M1 \<Longrightarrow>
                                            length \<gamma> \<le> k \<Longrightarrow> 
                                            list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<Longrightarrow> 
                                            butlast \<gamma> \<in> LS M1 (t_target t) \<Longrightarrow>
                                            (V (t_target t) \<noteq> (V (t_source t))@[(t_input t, t_output t)]) \<Longrightarrow> 
                                            ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                                               = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                                             \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
  and     handles_undefined_io_pairs: "\<And> q x y . q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> h_obs M1 q x y = None \<Longrightarrow> L M1 \<inter> {V q @ [(x,y)]} = L M2 \<inter> {V q @ [(x,y)]}"  
  and     "q \<in> reachable_states M1"
  and     "length \<gamma> \<le> Suc k"
  and     "list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1"
  and     "butlast \<gamma> \<in> LS M1 q"
shows "(L M1 \<inter> (V ` reachable_states M1 \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
         = L M2 \<inter> (V ` reachable_states M1 \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
        \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {V q @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})"   
  using unverified_transitions_handle_all_transitions[OF assms(1-6), of k]
  using abstract_h_condition_by_transition_and_io_pair_coverage[OF assms(1-4) _ assms(6-10)]
  by presburger


lemma h_framework_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  fixes cg_insert :: "('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd)"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
  and     "is_state_cover_assignment M1 (get_state_cover M1)"
  and     "\<And> xs . List.set xs = List.set (sort_transitions M1 (get_state_cover M1) xs)"
  and     "convergence_graph_initial_invar M1 M2 cg_lookup cg_initial"
  and     "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
  and     "convergence_graph_merge_invar M1 M2 cg_lookup cg_merge"
  and     "separates_state_cover handle_state_cover M1 M2 cg_initial cg_insert cg_lookup"
  and     "handles_transition handle_unverified_transition M1 M2 (get_state_cover M1) (fst (handle_state_cover M1 (get_state_cover M1) cg_initial cg_insert cg_lookup)) cg_insert cg_lookup cg_merge"
  and     "handles_io_pair handle_unverified_io_pair M1 M2 cg_insert cg_lookup"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (h_framework M1 get_state_cover handle_state_cover sort_transitions handle_unverified_transition handle_unverified_io_pair cg_initial cg_insert cg_lookup cg_merge m))
                          = (L M2 \<inter> set (h_framework M1 get_state_cover handle_state_cover sort_transitions handle_unverified_transition handle_unverified_io_pair cg_initial cg_insert cg_lookup cg_merge m)))"
  (is "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))")
and "finite_tree (h_framework M1 get_state_cover handle_state_cover sort_transitions handle_unverified_transition handle_unverified_io_pair cg_initial cg_insert cg_lookup cg_merge m)"
proof 
  show "(L M1 = L M2) \<Longrightarrow> ((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"
    by blast


  define rstates where rstates: "rstates = reachable_states_as_list M1"
  define rstates_io where rstates_io: "rstates_io = List.product rstates (List.product (inputs_as_list M1) (outputs_as_list M1))"
  define undefined_io_pairs where undefined_io_pairs: "undefined_io_pairs = List.filter (\<lambda> (q,(x,y)) . h_obs M1 q x y = None) rstates_io"
  define V where V: "V             = get_state_cover M1"
  define n where n: "n             = size_r M1"
  define TG1 where TG1: "TG1 = handle_state_cover M1 V cg_initial cg_insert cg_lookup"

  define sc_covered_transitions where sc_covered_transitions: "sc_covered_transitions = (\<Union> q \<in> reachable_states M1 . covered_transitions M1 V (V q))"
  define unverified_transitions where unverified_transitions: "unverified_transitions = sort_transitions M1 V (filter (\<lambda>t . t_source t \<in> reachable_states M1 \<and> t \<notin> sc_covered_transitions) (transitions_as_list M1))"
  define verify_transition where verify_transition: "verify_transition = (\<lambda> (X,T,G) t . handle_unverified_transition M1 V T G cg_insert cg_lookup cg_merge m t X)"
  define TG2 where TG2: "TG2 = snd (foldl verify_transition (unverified_transitions, TG1) unverified_transitions)"
  define verify_undefined_io_pair where verify_undefined_io_pair: "verify_undefined_io_pair = (\<lambda> T (q,(x,y)) . fst (handle_unverified_io_pair M1 V T (snd TG2) cg_insert cg_lookup q x y))" 
  define T3 where T3: "T3 = foldl verify_undefined_io_pair (fst TG2) undefined_io_pairs"

  have "?TS = T3"
    unfolding rstates rstates_io undefined_io_pairs V TG1 sc_covered_transitions unverified_transitions verify_transition TG2 verify_undefined_io_pair T3
    unfolding h_framework_def Let_def
    by force
  then have "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T3 = L M2 \<inter> set T3"
    by simp

  have "is_state_cover_assignment M1 V"
    unfolding V using assms(9) .

  (* basic properties of T1 and G1 *)

  define T1 where T1: "T1 = fst TG1"
  moreover define G1 where G1: "G1 = snd TG1"
  ultimately have "TG1 = (T1,G1)" 
    by auto 

  have T1_state_cover: "V ` reachable_states M1 \<subseteq> set T1"
  and  T1_finite: "finite_tree T1"
    using \<open>separates_state_cover handle_state_cover M1 M2 cg_initial cg_insert cg_lookup\<close>
    unfolding T1 TG1 separates_state_cover_def
    by blast+
  

  have T1_V_div: "(L M1 \<inter> set T1 = (L M2 \<inter> set T1)) \<Longrightarrow> preserves_divergence M1 M2 (V ` reachable_states M1)"
   and G1_invar: "(L M1 \<inter> set T1 = (L M2 \<inter> set T1)) \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G1" 
    using \<open>separates_state_cover handle_state_cover M1 M2 cg_initial cg_insert cg_lookup\<close>
    unfolding T1 G1 TG1 separates_state_cover_def
    using assms(1-4,7,8) \<open>is_state_cover_assignment M1 V\<close> assms(12,11) 
    by blast+

  

  (* properties of transition filtering and sorting *)

  have sc_covered_transitions_alt_def: "sc_covered_transitions = {t . t \<in> transitions M1 \<and> t_source t \<in> reachable_states M1 \<and> (V (t_target t) = (V (t_source t))@[(t_input t, t_output t)])}"
    (is "?A = ?B")
  proof 
    show "?A \<subseteq> ?B"
    proof 
      fix t assume "t \<in> ?A"
      then obtain q where "t \<in> covered_transitions M1 V (V q)" and "q \<in> reachable_states M1"
        unfolding sc_covered_transitions 
        by blast
      then have "V q \<in> L M1" and "after_initial M1 (V q) = q"
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by blast+

      then obtain p where "path M1 (initial M1) p" and "p_io p = V q"
        by auto
      then have *: "the_elem (paths_for_io M1 (initial M1) (V q)) = p"
        using observable_paths_for_io[OF assms(1) \<open>V q \<in> L M1\<close>]
        unfolding paths_for_io_def
        by (metis (mono_tags, lifting) assms(1) mem_Collect_eq observable_path_unique singletonI the_elem_eq)
      
      have "t \<in> list.set p" and "V (t_source t) @ [(t_input t, t_output t)] = V (t_target t)"
        using \<open>t \<in> covered_transitions M1 V (V q)\<close> 
        unfolding covered_transitions_def Let_def * 
        by auto

      have "t \<in> transitions M1"
        using \<open>t \<in> list.set p\<close> \<open>path M1 (initial M1) p\<close>
        by (meson path_transitions subsetD) 
      moreover have "t_source t \<in> reachable_states M1"
        using reachable_states_path[OF reachable_states_initial \<open>path M1 (initial M1) p\<close> \<open>t \<in> list.set p\<close>] .
      ultimately show "t \<in> ?B"
        using \<open>V (t_source t) @ [(t_input t, t_output t)] = V (t_target t)\<close>
        by auto
    qed

    show "?B \<subseteq> ?A"
    proof 
      fix t assume "t \<in> ?B"
      then have "t \<in> transitions M1" 
                "t_source t \<in> reachable_states M1" 
                "(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)"
        by auto
      then have "t_target t \<in> reachable_states M1"
        using reachable_states_next[of "t_source t" M1 t] 
        by blast
      then have "V (t_target t) \<in> L M1" and "after_initial M1 (V (t_target t)) = (t_target t)"
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by blast+
      then obtain p where "path M1 (initial M1) p" and "p_io p = V (t_target t)"
        by auto
      then have *: "the_elem (paths_for_io M1 (initial M1) (V (t_target t))) = p"
        using observable_paths_for_io[OF assms(1) \<open>V (t_target t) \<in> L M1\<close>]
        unfolding paths_for_io_def
        by (metis (mono_tags, lifting) assms(1) mem_Collect_eq observable_path_unique singletonI the_elem_eq)

      
      have "V (t_source t) \<in> L M1" and "after_initial M1 (V (t_source t)) = (t_source t)"
        using \<open>t_source t \<in> reachable_states M1\<close>
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by blast+
      then obtain p' where "path M1 (initial M1) p'" and "p_io p' = V (t_source t)"
        by auto
      
      have "path M1 (initial M1) (p'@[t])"
        using after_path[OF assms(1) \<open>path M1 (initial M1) p'\<close>] \<open>path M1 (initial M1) p'\<close> \<open>t\<in>transitions M1\<close>
        unfolding \<open>p_io p' = V (t_source t)\<close>
        unfolding \<open>after_initial M1 (V (t_source t)) = (t_source t)\<close>
        by (metis path_append single_transition_path)
      moreover have "p_io (p'@[t]) = p_io p"
        using \<open>p_io p' = V (t_source t)\<close> 
        unfolding \<open>p_io p = V (t_target t)\<close>  \<open>(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)\<close>[symmetric]
        by auto
      ultimately have "p'@[t] = p"
        using observable_path_unique[OF assms(1) _ \<open>path M1 (initial M1) p\<close>]
        by force
      then have "t \<in> list.set p"
        by auto
      then have "t \<in> covered_transitions M1 V (V (t_target t))"
        using \<open>(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)\<close>
        unfolding covered_transitions_def Let_def *
        by auto
      then show "t \<in> ?A"
        using \<open>t_target t \<in> reachable_states M1\<close>
        unfolding sc_covered_transitions 
        by blast
    qed
  qed

  have T1_covered_transitions_conv: "\<And> t . (L M1 \<inter> set T1 = (L M2 \<inter> set T1)) \<Longrightarrow> t \<in> sc_covered_transitions \<Longrightarrow> converge M2 (V (t_target t)) ((V (t_source t))@[(t_input t, t_output t)])"
  proof -
    fix t assume "(L M1 \<inter> set T1 = (L M2 \<inter> set T1))"
                 "t \<in> sc_covered_transitions"

    then have "t \<in> transitions M1" 
              "t_source t \<in> reachable_states M1" 
              "(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)"
      unfolding sc_covered_transitions_alt_def
      by auto
    then have "t_target t \<in> reachable_states M1"
      using reachable_states_next[of "t_source t" M1 t] 
      by blast
    then have "V (t_target t) \<in> L M1"
      using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
      by blast   
    moreover have "V (t_target t) \<in> set T1"
      using T1_state_cover \<open>t_target t \<in> reachable_states M1\<close>
      by blast
    ultimately have "V (t_target t) \<in> L M2"
      using \<open>(L M1 \<inter> set T1 = (L M2 \<inter> set T1))\<close>
      by blast
    then show "converge M2 (V (t_target t)) ((V (t_source t))@[(t_input t, t_output t)])"
      unfolding \<open>(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)\<close>
      by auto
  qed


  have unverified_transitions_alt_def : "list.set unverified_transitions = {t . t \<in> transitions M1 \<and> t_source t \<in> reachable_states M1 \<and> (V (t_target t) \<noteq> (V (t_source t))@[(t_input t, t_output t)])}"
    unfolding unverified_transitions sc_covered_transitions_alt_def V
    unfolding assms(10)[symmetric] 
    using transitions_as_list_set[of M1]
    by auto


  (* remaining properties before the computation of TG2 *)

  have cg_insert_invar : "\<And> G \<gamma> . \<gamma> \<in> L M1 \<Longrightarrow> \<gamma> \<in> L M2 \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup (cg_insert G \<gamma>)"
    using assms(12)
    unfolding convergence_graph_insert_invar_def
    by blast

  have cg_merge_invar : "\<And> G \<gamma> \<gamma>'. convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow> converge M1 \<gamma> \<gamma>' \<Longrightarrow> converge M2 \<gamma> \<gamma>' \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup (cg_merge G \<gamma> \<gamma>')"
    using assms(13)
    unfolding convergence_graph_merge_invar_def
    by blast


  (* properties of the computation of TG2 *)

  define T2 where T2: "T2 = fst TG2"
  define G2 where G2: "G2 = snd TG2"

  (* idea: in each application of verify_transition, a further transition of unverified_transitions
           (q,x,y,q') is covered - that is
            - traces \<alpha>.(x/y), \<beta> are added to the test suite such that
              - \<alpha> converges with V s in both M1 and M2
              - \<beta> converges with V s' in both M1 and M2
              - \<alpha>.(x/y) converges with \<beta> in both M1 and M2 
            - the test suite is added as required to establish this convergence
            - the convergence graph is updated, respecting the lookup-invariants due to convergence (in merge)
  *)

  have "handles_transition handle_unverified_transition M1 M2 V T1 cg_insert cg_lookup cg_merge"
    using assms(15)
    unfolding T1 TG1 V .
  then have verify_transition_retains_testsuite: "\<And> t T G X . set T \<subseteq> set (fst (snd (verify_transition (X,T,G) t)))"
       and  verify_transition_retains_finiteness: "\<And> t T G X . finite_tree T \<Longrightarrow> finite_tree (fst (snd (verify_transition (X,T,G) t)))"
    unfolding verify_transition case_prod_conv handles_transition_def 
    by presburger+


  define handles_unverified_transition 
    where handles_unverified_transition: "handles_unverified_transition  = (\<lambda>t .
                                                (\<forall> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                                                          \<longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                                                                = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                                                               \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))))"


  have verify_transition_cover_prop: "\<And> t T G X . (L M1 \<inter> (set (fst (snd (verify_transition (X,T,G) t)))) = L M2 \<inter> (set (fst (snd (verify_transition (X,T,G) t)))))
                                          \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G
                                          \<Longrightarrow> t \<in> transitions M1
                                          \<Longrightarrow> t_source t \<in> reachable_states M1
                                          \<Longrightarrow> set T1 \<subseteq> set T
                                          \<Longrightarrow> ((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))
                                          \<Longrightarrow> handles_unverified_transition t \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (verify_transition (X,T,G) t)))"
  proof -
    fix t T G X
    assume a1: "(L M1 \<inter> (set (fst (snd (verify_transition (X,T,G) t)))) = L M2 \<inter> (set (fst (snd (verify_transition (X,T,G) t)))))"
    assume a2: "convergence_graph_lookup_invar M1 M2 cg_lookup G"
    assume a3: "t \<in> transitions M1"
    assume a4: "t_source t \<in> reachable_states M1"
    assume a5: "set T1 \<subseteq> set T"
    assume a6: "((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))"

    

    obtain X' T' G' where TG': "(X',T',G') = handle_unverified_transition M1 V T G cg_insert cg_lookup cg_merge m t X"
      using prod.exhaust by metis
    have T':  "T'  = fst (snd (handle_unverified_transition M1 V T G cg_insert cg_lookup cg_merge m t X))"
     and G':  "G'  = snd (snd (handle_unverified_transition M1 V T G cg_insert cg_lookup cg_merge m t X))"
      unfolding TG'[symmetric] by auto

    have "verify_transition (X,T,G) t = (X',T',G')"
      using TG'[symmetric]
      unfolding verify_transition G' Let_def case_prod_conv 
      by force
    then have "set T \<subseteq> set T'"
      using verify_transition_retains_testsuite[of T X G t] unfolding T' 
      by auto
    then have "set T1 \<subseteq> set T'"
      using a5 by blast
    then have "(L M1 \<inter> (set T1) = L M2 \<inter> (set T1))"
      using a1 unfolding \<open>verify_transition (X,T,G) t = (X',T',G')\<close> fst_conv snd_conv
      by blast
    then have *: "preserves_divergence M1 M2 (V ` reachable_states M1)"
      using T1_V_div
      by auto

    have "L M1 \<inter> set T' = L M2 \<inter> set T'"
      using a1 \<open>set T \<subseteq> set T'\<close> unfolding T' \<open>verify_transition (X,T,G) t = (X',T',G')\<close> fst_conv snd_conv
      by blast

    have **: "V ` reachable_states M1 \<subseteq> set T"
      using a5 T1_state_cover by blast

    show "handles_unverified_transition t \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (verify_transition (X,T,G) t)))"
      unfolding \<open>verify_transition (X,T,G) t = (X',T',G')\<close> snd_conv 
      unfolding G'
      using \<open>handles_transition handle_unverified_transition M1 M2 V T1 cg_insert cg_lookup cg_merge\<close>
      unfolding handles_transition_def 

      using assms(1-8) \<open>is_state_cover_assignment M1 V\<close> * ** a3 a4 a2 a6 \<open>convergence_graph_insert_invar M1 M2 cg_lookup cg_insert\<close> \<open>convergence_graph_merge_invar M1 M2 cg_lookup cg_merge\<close> \<open>L M1 \<inter> set T' = L M2 \<inter> set T'\<close> a5
      unfolding T'
      unfolding handles_unverified_transition 
      by blast
  qed

  have verify_transition_foldl_invar_1: "\<And> X ts . list.set ts \<subseteq> list.set unverified_transitions \<Longrightarrow> 
                set T1 \<subseteq> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<and> finite_tree (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
  proof -
    fix X ts assume "list.set ts \<subseteq> list.set unverified_transitions" 
    then show "set T1 \<subseteq> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<and> finite_tree (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
    proof (induction ts rule: rev_induct)
      case Nil
      then show ?case 
        using T1_finite by auto
    next
      case (snoc t ts)
      then have "t \<in> transitions M1" and "t_source t \<in> reachable_states M1"
        unfolding unverified_transitions_alt_def 
        by force+

      have p1: "list.set ts \<subseteq> list.set unverified_transitions"
        using snoc.prems(1) by auto

      have "set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<subseteq> set (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t]))))"
        using verify_transition_retains_testsuite 
        unfolding foldl_append
        unfolding foldl.simps 
        by (metis prod.collapse) 

      have **: "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"  
       and ***: "finite_tree (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
        using snoc.IH[OF p1] 
        by auto          
    
      have "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t]))))"
        using ** verify_transition_retains_testsuite \<open>set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<subseteq> set (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t]))))\<close> 
        by auto 
      moreover have "finite_tree (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t]))))"
        using verify_transition_retains_finiteness[OF ***, of "fst (foldl verify_transition (X, T1, G1) ts)" "snd (snd (foldl verify_transition (X, T1, G1) ts))"] 
        by auto
      ultimately show ?case 
        by simp
    qed
  qed 
  then have T2_invar_1: "set T1 \<subseteq> set T2"
        and T2_finite : "finite_tree T2"
    unfolding TG2 G2 T2 \<open>TG1 = (T1,G1)\<close>
    by auto

  have verify_transition_foldl_invar_2: "\<And> X ts . list.set ts \<subseteq> list.set unverified_transitions \<Longrightarrow> 
                L M1 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<Longrightarrow> 
                convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (foldl verify_transition (X, T1, G1) ts)))"
  proof -
    fix X ts assume "list.set ts \<subseteq> list.set unverified_transitions" 
              and "L M1 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
    then show "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (foldl verify_transition (X, T1, G1) ts)))"
    proof (induction ts rule: rev_induct)
      case Nil
      then show ?case 
        using G1_invar by auto
    next
      case (snoc t ts)
      then have "t \<in> transitions M1" and "t_source t \<in> reachable_states M1"
        unfolding unverified_transitions_alt_def 
        by force+

      have p1: "list.set ts \<subseteq> list.set unverified_transitions"
        using snoc.prems(1) by auto

      have "set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<subseteq> set (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t]))))"
        using verify_transition_retains_testsuite unfolding foldl_append foldl.simps
        by (metis fst_conv prod_eq_iff snd_conv)
      then have p2: "L M1 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
        using snoc.prems(2)
        by blast 

      have *:"convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (foldl verify_transition (X, T1, G1) ts)))"                                                           
        using snoc.IH[OF p1 p2] 
        by auto          

      have **: "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
        using verify_transition_foldl_invar_1[OF p1] by blast

      have ***: "((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))"
        using snoc.prems(1) unfolding unverified_transitions_alt_def by force
    
      have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (verify_transition ((fst (foldl verify_transition (X, T1, G1) ts)), fst (snd (foldl verify_transition (X, T1, G1) ts)), snd (snd (foldl verify_transition (X, T1, G1) ts))) t)))"          
        using verify_transition_cover_prop[OF _ * \<open>t \<in> transitions M1\<close> \<open>t_source t \<in> reachable_states M1\<close> ** ***, of "(fst (foldl verify_transition (X, T1, G1) ts))"] snoc.prems(2)
        unfolding prod.collapse
        by auto
      then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (foldl verify_transition (X, T1, G1) (ts@[t]))))"
        by auto
      moreover have "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t]))))"
        using ** verify_transition_retains_testsuite
        using snoc.prems(1) verify_transition_foldl_invar_1 by blast 
      ultimately show ?case 
        by simp
    qed
  qed 
  then have T2_invar_2: "L M1 \<inter> set T2 = L M2 \<inter> set T2 \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G2"
    unfolding TG2 G2 T2 \<open>TG1 = (T1,G1)\<close> by auto

  have T2_cover: "\<And> t . L M1 \<inter> set T2 = L M2 \<inter> set T2 \<Longrightarrow> t \<in> list.set unverified_transitions \<Longrightarrow> handles_unverified_transition t"
  proof -
    have "\<And> X t ts . t \<in> list.set ts \<Longrightarrow> list.set ts \<subseteq> list.set unverified_transitions \<Longrightarrow> L M1 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<Longrightarrow> handles_unverified_transition t"
    proof -
      fix X t ts
      assume "t \<in> list.set ts" and "list.set ts \<subseteq> list.set unverified_transitions" and "L M1 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"

      then show "handles_unverified_transition t"
      proof (induction ts rule: rev_induct)
        case Nil
        then show ?case by auto
      next
        case (snoc t' ts)

        then have "t \<in> transitions M1" and "t_source t \<in> reachable_states M1"
          unfolding unverified_transitions_alt_def 
          by blast+

        have "t' \<in> transitions M1" and "t_source t' \<in> reachable_states M1"
          using snoc.prems(2)
          unfolding unverified_transitions_alt_def 
          by auto

        have "set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<subseteq> set (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t']))))"
          using verify_transition_retains_testsuite unfolding foldl_append foldl.simps
          by (metis fst_conv prod_eq_iff snd_conv)
        then have "L M1 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
          using snoc.prems(3) 
          by blast

        have *: "L M1 \<inter> Prefix_Tree.set (fst (snd (verify_transition (foldl verify_transition (X, T1, G1) ts) t'))) = L M2 \<inter> Prefix_Tree.set (fst (snd (verify_transition (foldl verify_transition (X, T1, G1) ts) t')))"               
          using snoc.prems(3) by auto

        have **: "V (t_source t') @ [(t_input t', t_output t')] \<noteq> V (t_target t')"
          using snoc.prems(2) unfolding unverified_transitions_alt_def by force

        have "L M1 \<inter> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
          using \<open>set (fst (snd (foldl verify_transition (X, T1, G1) ts))) \<subseteq> set (fst (snd (foldl verify_transition (X, T1, G1) (ts@[t']))))\<close> snoc.prems(3)
          by auto
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (foldl verify_transition (X, T1, G1) ts))) \<and> Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) ts)))"
          using snoc.prems(2) verify_transition_foldl_invar_1[of ts] verify_transition_foldl_invar_2[of ts]
          by auto
        then have covers_t': "handles_unverified_transition t'"
          by (metis "*" "**" \<open>t' \<in> FSM.transitions M1\<close> \<open>t_source t' \<in> reachable_states M1\<close> prod.collapse verify_transition_cover_prop) 

        show ?case proof (cases "t = t'")
          case True
          then show ?thesis 
            using covers_t' by auto
        next
          case False
          then have "t \<in> list.set ts"
            using snoc.prems(1) by auto

          show "handles_unverified_transition t"
            using snoc.IH[OF \<open>t \<in> list.set ts\<close>] snoc.prems(2) \<open>L M1 \<inter> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) ts))) = L M2 \<inter> Prefix_Tree.set (fst (snd (foldl verify_transition (X, T1, G1) ts)))\<close>
            by auto
        qed
      qed
    qed

    then show "\<And> t . L M1 \<inter> set T2 = L M2 \<inter> set T2 \<Longrightarrow> t \<in> list.set unverified_transitions \<Longrightarrow> handles_unverified_transition t"
      unfolding TG2 T2 G2 \<open>TG1 = (T1,G1)\<close>
      by simp
  qed


  (* properties of T3 derived from those of T1 and T2 and the assumption that T3 is passed by M2 *)

  have verify_undefined_io_pair_retains_testsuite: "\<And> qxy T . set T \<subseteq> set (verify_undefined_io_pair T qxy)"
  proof -
    fix qxy :: "('a \<times> 'b \<times> 'c)"
    fix T
    obtain q x y where "qxy = (q,x,y)"
      using prod.exhaust by metis
    show \<open>set T \<subseteq> set (verify_undefined_io_pair T qxy)\<close>
      unfolding \<open>qxy = (q,x,y)\<close>
      using \<open>handles_io_pair handle_unverified_io_pair M1 M2 cg_insert cg_lookup\<close>
      unfolding handles_io_pair_def verify_undefined_io_pair case_prod_conv
      by blast
  qed
  have verify_undefined_io_pair_folding_retains_testsuite: "\<And> qxys T . set T \<subseteq> set (foldl verify_undefined_io_pair T qxys)"
  proof -
    fix qxys T
    show "set T \<subseteq> set (foldl verify_undefined_io_pair T qxys)"
      using verify_undefined_io_pair_retains_testsuite
      by (induction qxys rule: rev_induct; force) 
  qed

  have verify_undefined_io_pair_retains_finiteness: "\<And> qxy T . finite_tree T \<Longrightarrow> finite_tree (verify_undefined_io_pair T qxy)"
  proof -
    fix qxy :: "('a \<times> 'b \<times> 'c)"
    fix T :: "('b\<times>'c) prefix_tree"
    assume "finite_tree T"
    obtain q x y where "qxy = (q,x,y)"
      using prod.exhaust by metis
    show \<open>finite_tree (verify_undefined_io_pair T qxy)\<close>
      unfolding \<open>qxy = (q,x,y)\<close>
      using \<open>handles_io_pair handle_unverified_io_pair M1 M2 cg_insert cg_lookup\<close> \<open>finite_tree T\<close>
      unfolding handles_io_pair_def verify_undefined_io_pair case_prod_conv
      by blast
  qed
  have verify_undefined_io_pair_folding_retains_finiteness: "\<And> qxys T . finite_tree T \<Longrightarrow> finite_tree (foldl verify_undefined_io_pair T qxys)"
  proof -
    fix qxys 
    fix T :: "('b\<times>'c) prefix_tree"
    assume "finite_tree T"
    then show "finite_tree (foldl verify_undefined_io_pair T qxys)"
      using verify_undefined_io_pair_retains_finiteness
      by (induction qxys rule: rev_induct; force) 
  qed

  show "finite_tree ?TS"
    using T2 T2_finite T3 \<open>h_framework M1 get_state_cover handle_state_cover sort_transitions handle_unverified_transition handle_unverified_io_pair cg_initial cg_insert cg_lookup cg_merge m = T3\<close> verify_undefined_io_pair_folding_retains_finiteness 
    by auto


  (* having finished all but one goal, we may finally assume that M2 passes the test suite *)
  assume "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"
  
  have "set T2 \<subseteq> set T3"
    unfolding T3 T2
  proof (induction undefined_io_pairs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    then show ?case 
      using verify_undefined_io_pair_retains_testsuite[of "(foldl verify_undefined_io_pair (fst TG2) xs)" x]
      by force
  qed
  then have passes_T2: "L M1 \<inter> set T2 = L M2 \<inter> set T2"
    using \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (L M1 \<inter> set T3 = L M2 \<inter> set T3)\<close> \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>
    by blast


  have "set T1 \<subseteq> set T3"
  and  G2_invar: "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G2"
    using T2_invar_1 T2_invar_2[OF passes_T2] \<open>set T2 \<subseteq> set T3\<close> 
    by auto
  then have passes_T1: "L M1 \<inter> set T1 = L M2 \<inter> set T1"
    using \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T3 = L M2 \<inter> set T3\<close> \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>
    by blast

  have T3_preserves_divergence : "preserves_divergence M1 M2 (V ` reachable_states M1)"
    using T1_V_div[OF passes_T1] .

  have T3_state_cover : "V ` reachable_states M1 \<subseteq> set T3"
    using T1_state_cover \<open>set T1 \<subseteq> set T3\<close>
    by blast
  then have T3_passes_state_cover : "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
    using T1_state_cover passes_T1 by blast 


  (* properties of T3 w.r.t. undefined io pairs *)

  have rstates_io_set : "list.set rstates_io = {(q,(x,y)) . q \<in> reachable_states M1 \<and> x \<in> inputs M1 \<and> y \<in> outputs M1}"
    unfolding rstates_io rstates 
    using reachable_states_as_list_set[of M1] inputs_as_list_set[of M1] outputs_as_list_set[of M1] 
    by force
  then have undefined_io_pairs_set : "list.set undefined_io_pairs = {(q,(x,y)) . q \<in> reachable_states M1 \<and> x \<in> inputs M1 \<and> y \<in> outputs M1 \<and> h_obs M1 q x y = None}"
    unfolding undefined_io_pairs 
    by auto

  have verify_undefined_io_pair_prop : "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (\<And> q x y T . L M1 \<inter> set (verify_undefined_io_pair T (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair T (q,(x,y))) \<Longrightarrow> 
                                                    q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow>
                                                    V ` reachable_states M1 \<subseteq> set T \<Longrightarrow>
                                                    ( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} ))"
  proof -
    fix q x y T
    assume "L M1 \<inter> set (verify_undefined_io_pair T (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair T (q,(x,y)))"
       and "q \<in> reachable_states M1" and "x \<in> inputs M1" and "y \<in> outputs M1"
       and "V ` reachable_states M1 \<subseteq> set T"
       and "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"

    have " L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
      using T3_state_cover \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> Prefix_Tree.set T3 = L M2 \<inter> Prefix_Tree.set T3\<close> \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> 
      by blast

    have "L M1 \<inter> set (fst (handle_unverified_io_pair M1 V T G2 cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (handle_unverified_io_pair M1 V T G2 cg_insert cg_lookup q x y))"
      using \<open>L M1 \<inter> set (verify_undefined_io_pair T (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair T (q,(x,y)))\<close>
      unfolding verify_undefined_io_pair case_prod_conv combine_set G2
      by blast


    show "( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} )"
      using assms(16)
      unfolding handles_io_pair_def 
      using assms(1-4,7,8) \<open>is_state_cover_assignment M1 V\<close> \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close>
            \<open>q \<in> reachable_states M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>
            G2_invar[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>] \<open>convergence_graph_insert_invar M1 M2 cg_lookup cg_insert\<close>
            \<open>L M1 \<inter> set (fst (handle_unverified_io_pair M1 V T G2 cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (handle_unverified_io_pair M1 V T G2 cg_insert cg_lookup q x y))\<close> 
      by blast
  qed

  have T3_covers_undefined_io_pairs : "(\<And> q x y . q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> h_obs M1 q x y = None \<Longrightarrow>
          ( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} ))" 
  proof -
    fix q x y assume "q \<in> reachable_states M1" and "x \<in> inputs M1" and "y \<in> outputs M1" and "h_obs M1 q x y = None" 

    have "\<And> q x y qxys T . L M1 \<inter> set (foldl verify_undefined_io_pair T qxys) = L M2 \<inter> set (foldl verify_undefined_io_pair T qxys) \<Longrightarrow> (V ` reachable_states M1) \<subseteq> set T \<Longrightarrow> (q,(x,y)) \<in> list.set qxys \<Longrightarrow> list.set qxys \<subseteq> list.set undefined_io_pairs \<Longrightarrow> 
              ( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} )"
      (is "\<And> q x y qxys T . ?P1 qxys T \<Longrightarrow> (V ` reachable_states M1) \<subseteq> set T \<Longrightarrow> (q,(x,y)) \<in> list.set qxys \<Longrightarrow> list.set qxys \<subseteq> list.set undefined_io_pairs \<Longrightarrow> ?P2 q x y qxys T")
    proof -
      fix q x y qxys T
      assume "?P1 qxys T" and "(q,(x,y)) \<in> list.set qxys" and "list.set qxys \<subseteq> list.set undefined_io_pairs" and "(V ` reachable_states M1) \<subseteq> set T"
      then show "?P2 q x y qxys T"
      proof (induction qxys rule: rev_induct)
        case Nil
        then show ?case by auto
      next
        case (snoc a qxys)

        have "set (foldl verify_undefined_io_pair T qxys) \<subseteq> set (foldl verify_undefined_io_pair T (qxys@[a]))"
          using verify_undefined_io_pair_retains_testsuite 
          by auto
        then have *:"L M1 \<inter> Prefix_Tree.set (foldl verify_undefined_io_pair T qxys) = L M2 \<inter> Prefix_Tree.set (foldl verify_undefined_io_pair T qxys)"
          using snoc.prems(1)
          by blast

        have **: "V ` reachable_states M1 \<subseteq> Prefix_Tree.set (foldl verify_undefined_io_pair T qxys)"
          using snoc.prems(4) verify_undefined_io_pair_folding_retains_testsuite
          by blast

        show ?case proof (cases "a = (q,(x,y))")
          case True
          then have ***: "q \<in> reachable_states M1"
            using snoc.prems(3) 
            unfolding undefined_io_pairs_set
            by auto 

          have "x \<in> inputs M1" and "y \<in> outputs M1"
            using snoc.prems(2,3) unfolding undefined_io_pairs_set by auto

          have ****: "L M1 \<inter> set (verify_undefined_io_pair (foldl verify_undefined_io_pair T qxys) (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair (foldl verify_undefined_io_pair T qxys) (q,(x,y)))"
            using snoc.prems(1) unfolding True by auto
            
          show ?thesis
            using verify_undefined_io_pair_prop[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> **** *** \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close> **]
            unfolding True 
            by auto
        next
          case False
          then have "(q, x, y) \<in> list.set qxys" and "list.set qxys \<subseteq> list.set undefined_io_pairs"
            using snoc.prems(2,3) by auto
          then show ?thesis 
            using snoc.IH[OF * _ _  snoc.prems(4)]
            using \<open>set (foldl verify_undefined_io_pair T qxys) \<subseteq> set (foldl verify_undefined_io_pair T (qxys@[a]))\<close>
            by blast
        qed
      qed
    qed
    moreover have "L M1 \<inter> set (foldl verify_undefined_io_pair T2 undefined_io_pairs) = L M2 \<inter> set (foldl verify_undefined_io_pair T2 undefined_io_pairs)"
      using \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T3 = L M2 \<inter> set T3\<close>  \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>
      unfolding T3 T2 .
    moreover have "(V ` reachable_states M1) \<subseteq> set T2"
      using T1_state_cover T2 T2_invar_1 passes_T2 by fastforce
    moreover have "(q,(x,y)) \<in> list.set undefined_io_pairs"
      unfolding undefined_io_pairs_set
      using \<open>q \<in> reachable_states M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close> \<open>h_obs M1 q x y = None\<close>
      by blast
    ultimately show "( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} )"
      unfolding T3 T2 
      by blast
  qed


  have handles_unverified_transitions: " 
            (\<And>t \<gamma>. t \<in> FSM.transitions M1 \<Longrightarrow>
              t_source t \<in> reachable_states M1 \<Longrightarrow>
              length \<gamma> \<le> m-n \<Longrightarrow>
              list.set \<gamma> \<subseteq> FSM.inputs M1 \<times> FSM.outputs M1 \<Longrightarrow>
              butlast \<gamma> \<in> LS M1 (t_target t) \<Longrightarrow>
              V (t_target t) \<noteq> V (t_source t) @ [(t_input t, t_output t)] \<Longrightarrow>
              L M1 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) =
              L M2 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<and>
              preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
    using T2_cover[OF passes_T2]
    unfolding unverified_transitions_alt_def
    unfolding handles_unverified_transition
    unfolding \<open>?TS = T3\<close> n by blast



  have "satisfies_abstract_h_condition M1 M2 V m"
    unfolding satisfies_abstract_h_condition_def Let_def
    using abstract_h_condition_by_unverified_transition_and_io_pair_coverage[where k="m-n",OF assms(1) \<open>is_state_cover_assignment M1 V\<close> T3_passes_state_cover T3_preserves_divergence handles_unverified_transitions T3_covers_undefined_io_pairs]
    unfolding \<open>?TS = T3\<close> n by blast

  then show "L M1 = L M2"
    using abstract_h_condition_completeness[OF assms(1,2,3,6,5,7,8) \<open>is_state_cover_assignment M1 V\<close>]
    by blast  
qed

end