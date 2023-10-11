theory Input_Output_Language_Conformance
  imports "HOL-Library.Sublist"
begin


section \<open>Preliminaries\<close>

type_synonym ('a) alphabet = "'a set"
type_synonym ('x,'y) word = "('x \<times> 'y) list"
type_synonym ('x,'y) language = "('x,'y) word set"
type_synonym ('y) output_relation = "('y set \<times> 'y set) set"



fun is_language :: "'x alphabet \<Rightarrow> 'y alphabet \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "is_language X Y L = (
      \<comment> \<open>nonempty\<close>
      (L \<noteq> {}) \<and>
      (\<forall> \<pi> \<in> L .
        \<comment> \<open>over X and Y\<close>
        (\<forall> xy \<in> set \<pi> . fst xy \<in> X \<and> snd xy \<in> Y) \<and>
        \<comment> \<open>prefix closed\<close>
        (\<forall> \<pi>' . prefix \<pi>' \<pi> \<longrightarrow> \<pi>' \<in> L)))"

lemma language_contains_nil : 
  assumes "is_language X Y L"
shows "[] \<in> L"
  using assms by auto

lemma language_intersection_is_language : 
  assumes "is_language X Y L1" 
  and     "is_language X Y L2"
shows "is_language X Y (L1 \<inter> L2)" 
  using assms 
  using language_contains_nil[OF assms(1)] language_contains_nil[OF assms(2)]
  unfolding is_language.simps
  by (metis IntD1 IntD2 IntI disjoint_iff) 
  


fun language_for_state :: "('x,'y) language \<Rightarrow> ('x,'y) word \<Rightarrow> ('x,'y) language" where
  "language_for_state L \<pi> = {\<tau> . \<pi>@\<tau> \<in> L}" 

notation language_for_state ("\<L>[_,_]")

lemma language_for_state_is_language :
  assumes "is_language X Y L"
  and     "\<pi> \<in> L"
shows "is_language X Y \<L>[L,\<pi>]"
proof -
  have "\<And> \<tau> . \<tau> \<in> \<L>[L,\<pi>] \<Longrightarrow> (\<forall> xy \<in> set \<tau> . fst xy \<in> X \<and> snd xy \<in> Y) \<and> (\<forall> \<tau>' . prefix \<tau>' \<tau> \<longrightarrow> \<tau>' \<in> \<L>[L,\<pi>])"
  proof -
    fix \<tau> assume "\<tau> \<in> \<L>[L,\<pi>]"
    then have "\<pi>@\<tau> \<in> L" by auto
    then have "\<And> xy . xy \<in> set (\<pi>@\<tau>) \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> Y"
          and "\<And> \<pi>' . prefix \<pi>' (\<pi>@\<tau>) \<Longrightarrow> \<pi>' \<in> L"
      using assms(1) by auto
    
    have "\<And> xy . xy \<in> set \<tau> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> Y"
      using \<open>\<And> xy . xy \<in> set (\<pi>@\<tau>) \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> Y\<close> by auto
    moreover have "\<And> \<tau>' . prefix \<tau>' \<tau> \<Longrightarrow> \<tau>' \<in> \<L>[L,\<pi>]"
      by (simp add: \<open>\<And>\<pi>'. prefix \<pi>' (\<pi> @ \<tau>) \<Longrightarrow> \<pi>' \<in> L\<close>)
    ultimately show "(\<forall> xy \<in> set \<tau> . fst xy \<in> X \<and> snd xy \<in> Y) \<and> (\<forall> \<tau>' . prefix \<tau>' \<tau> \<longrightarrow> \<tau>' \<in> \<L>[L,\<pi>])"
      by simp
  qed
  moreover have "\<L>[L,\<pi>] \<noteq> {}"
    using assms(2)
    by (metis (no_types, lifting) append.right_neutral empty_Collect_eq language_for_state.simps) 
  ultimately show ?thesis
    by simp
qed


lemma language_of_state_empty_iff : 
  assumes "is_language X Y L"
shows "(\<L>[L,\<pi>] = {}) \<longleftrightarrow> (\<pi> \<notin> L)" 
  using assms unfolding is_language.simps language_for_state.simps
  by (metis Collect_empty_eq append.right_neutral prefixI)



fun are_equivalent_for_language :: "('x,'y) language \<Rightarrow> ('x,'y) word \<Rightarrow> ('x,'y) word \<Rightarrow> bool" where
  "are_equivalent_for_language L \<alpha> \<beta> = (\<L>[L,\<alpha>] = \<L>[L,\<beta>])"


abbreviation(input) "input_projection \<pi> \<equiv> map fst \<pi>"
abbreviation(input) "output_projection \<pi> \<equiv> map snd \<pi>"
notation input_projection ("[_]\<^sub>I")
notation output_projection ("[_]\<^sub>O")


fun is_executable :: "('x,'y) language \<Rightarrow> ('x,'y) word \<Rightarrow> 'x list \<Rightarrow> bool" where
  "is_executable L \<pi> xs = (\<exists> \<tau> \<in> \<L>[L,\<pi>] . [\<tau>]\<^sub>I = xs)"

fun executable_sequences :: "('x,'y) language \<Rightarrow> ('x,'y) word \<Rightarrow> 'x list set" where 
  "executable_sequences L \<pi> = {xs . is_executable L \<pi> xs}"

fun executable_inputs :: "('x,'y) language \<Rightarrow> ('x,'y) word \<Rightarrow> 'x set" where 
  "executable_inputs L \<pi> = {x . is_executable L \<pi> [x]}"

notation executable_inputs ("exec[_,_]")


lemma executable_sequences_alt_def : "executable_sequences L \<pi> = {xs . \<exists> ys . length ys = length xs \<and> zip xs ys \<in> \<L>[L,\<pi>]}"
proof -
  have *:"\<And> A xs . (\<exists>\<tau>\<in>A. map fst \<tau> = xs) = (\<exists>ys. length ys = length xs \<and> zip xs ys \<in> A)"
    by (metis length_map map_fst_zip zip_map_fst_snd)

  show ?thesis
    unfolding executable_sequences.simps is_executable.simps
    unfolding * 
    by simp
qed

lemma executable_inputs_alt_def : "executable_inputs L \<pi> = {x . \<exists> y . [(x,y)] \<in> \<L>[L,\<pi>]}" 
proof -
  have *:"\<And> A xs . (\<exists>\<tau>\<in>A. map fst \<tau> = xs) = (\<exists>ys. length ys = length xs \<and> zip xs ys \<in> A)"
    by (metis length_map map_fst_zip zip_map_fst_snd)

  have **: "\<And> A x . (\<exists>ys. length ys = length [x] \<and> zip [x] ys \<in> A) = (\<exists> y . [(x,y)] \<in> A)"
    by (metis length_Suc_conv length_map zip_Cons_Cons zip_Nil) 

  show ?thesis
    unfolding executable_inputs.simps is_executable.simps 
    unfolding * 
    unfolding **
    by fastforce 
qed

lemma executable_inputs_in_alphabet : 
  assumes "is_language X Y L"
  and     "x \<in> exec[L,\<pi>]"
shows "x \<in> X" 
  using assms unfolding executable_inputs_alt_def by auto


fun output_sequences :: "('x,'y) language \<Rightarrow> ('x,'y) word \<Rightarrow> 'x list \<Rightarrow> 'y list set" where 
  "output_sequences L \<pi> xs = output_projection ` {\<tau> \<in> \<L>[L,\<pi>] . [\<tau>]\<^sub>I = xs}"

lemma prefix_closure_no_member :
  assumes "is_language X Y L"
  and     "\<pi> \<notin> L"
shows "\<pi>@\<tau> \<notin> L"
  by (meson assms(1) assms(2) is_language.elims(2) prefixI)


lemma output_sequences_empty_iff :
  assumes "is_language X Y L"
shows  "(output_sequences L \<pi> xs = {}) = ((\<pi> \<notin> L) \<or> (\<not> is_executable L \<pi> xs))"  
  unfolding output_sequences.simps is_executable.simps language_for_state.simps
  using Collect_empty_eq assms image_empty mem_Collect_eq prefix_closure_no_member by auto



fun outputs :: "('x,'y) language \<Rightarrow> ('x,'y) word \<Rightarrow> 'x \<Rightarrow> 'y set" where 
  "outputs L \<pi> x = {y . [(x,y)] \<in> \<L>[L,\<pi>]}"

notation outputs ("out[_,_,_]")

lemma outputs_in_alphabet :
  assumes "is_language X Y L"
shows "out[L,\<pi>,x] \<subseteq> Y"
  using assms by auto

lemma outputs_executable : "(out[L,\<pi>,x] = {}) \<longleftrightarrow> (x \<notin> exec[L,\<pi>])"
  by auto



fun is_completely_specified_for :: "'x set \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "is_completely_specified_for X L = (\<forall> \<pi> \<in> L . \<forall> x \<in> X . out[L,\<pi>,x] \<noteq> {})"


lemma prefix_executable : 
  assumes "is_language X Y L"
  and     "\<pi> \<in> L"
  and     "i < length \<pi>"
shows "fst (\<pi> ! i) \<in> exec[L,take i \<pi>]"
proof - 
  define \<pi>' where "\<pi>' = take i \<pi>"
  moreover define \<pi>'' where "\<pi>'' = drop (Suc i) \<pi>"
  moreover define xy where "xy = \<pi> ! i" 
  ultimately have "\<pi> = \<pi>'@[xy]@\<pi>''"
    by (simp add: Cons_nth_drop_Suc assms(3))
  then have "\<pi>'@[xy] \<in> L"
    using assms(1,2) by auto
  then show ?thesis
    unfolding \<pi>'_def xy_def 
    unfolding executable_inputs_alt_def language_for_state.simps
    by (metis (mono_tags, lifting) CollectI eq_fst_iff) 
qed


section \<open>Conformance Relations\<close>

definition language_equivalence :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "language_equivalence L1 L2 = (L1 = L2)"

definition language_inclusion :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "language_inclusion L1 L2 = (L1 \<subseteq> L2)"

abbreviation(input) "reduction L1 L2 \<equiv> language_inclusion L1 L2"

definition quasi_equivalence :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "quasi_equivalence L1 L2 = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> exec[L2,\<pi>] . out[L1,\<pi>,x] = out[L2,\<pi>,x])"

definition quasi_reduction :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "quasi_reduction L1 L2 = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> exec[L2,\<pi>] . (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]))"

definition strong_reduction :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "strong_reduction L1 L2 = (quasi_reduction L1 L2 \<and> (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x . out[L2,\<pi>,x] = {} \<longrightarrow> out[L1,\<pi>,x] = {}))"

definition semi_equivalence :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "semi_equivalence L1 L2 = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> exec[L2,\<pi>] . 
      (out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]) \<and>
      (\<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))"

definition semi_reduction :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "semi_reduction L1 L2 = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> exec[L2,\<pi>] . 
      (out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]) \<and>
      (\<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))"

definition strong_semi_equivalence :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "strong_semi_equivalence L1 L2 = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x . 
      (x \<in> exec[L2,\<pi>] \<longrightarrow> ((out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]) \<and> (\<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))) \<and>
      (x \<notin> exec[L2,\<pi>] \<longrightarrow> out[L1,\<pi>,x] = {}))"

definition strong_semi_reduction :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where 
  "strong_semi_reduction L1 L2 = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x . 
      (x \<in> exec[L2,\<pi>] \<longrightarrow> (out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x] \<and> (\<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))) \<and>
      (x \<notin> exec[L2,\<pi>] \<longrightarrow> out[L1,\<pi>,x] = {}))"



section \<open>Unifying Characterisations\<close>


subsection \<open>$\preceq$ Conformance\<close>

fun type_1_conforms :: "('x,'y) language \<Rightarrow> 'x alphabet \<Rightarrow> 'y output_relation \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where
  "type_1_conforms L1 X H L2 = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> X . (out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> H)"

notation type_1_conforms ("_ \<preceq>[_,_] _")

fun equiv :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "equiv Y = {(A,A) | A . A \<subseteq> Y}"

fun red :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "red Y = {(A,B) | A B . A \<subseteq> B \<and> B \<subseteq> Y}"

fun quasieq :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "quasieq Y = {(A,A) | A . A \<subseteq> Y} \<union> {(A,{}) | A . A \<subseteq> Y}"

fun quasired :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "quasired Y = {(A,B) | A B . A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> Y} \<union> {(C,{}) | C . C \<subseteq> Y}"

fun strongred :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "strongred Y = {(A,B) | A B . A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> Y} \<union> {({},{})}"



lemma red_type_1 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "reduction L1 L2 \<longleftrightarrow> (L1 \<preceq>[X,red Y] L2)"
unfolding language_inclusion_def proof 
  show "L1 \<subseteq> L2 \<Longrightarrow> L1 \<preceq>[X,red Y] L2"
    using outputs_in_alphabet[OF assms(2)]  
    unfolding type_1_conforms.simps red.simps
    by auto

  show "L1 \<preceq>[X,red Y] L2 \<Longrightarrow> L1 \<subseteq> L2" 
  proof 
    fix \<pi> assume "\<pi> \<in> L1" and "L1 \<preceq>[X,red Y] L2" 

    then show "\<pi> \<in> L2" proof (induction \<pi> rule: rev_induct)
      case Nil
      then show ?case using assms(2) by auto
    next
      case (snoc xy \<pi>)
      then have "\<pi> \<in> L1" and "\<pi> \<in> L1 \<inter> L2"
        using assms(1) by auto
      
      obtain x y where "xy = (x,y)"
        by fastforce 
      then have "y \<in> out[L1,\<pi>,x]" 
        using snoc.prems(1)
        by simp 
      moreover have "x \<in> X" and "y \<in> Y"
        using snoc.prems(1) assms(1) unfolding \<open>xy = (x,y)\<close> by auto
      ultimately have "y \<in> out[L2,\<pi>,x]"
        using snoc.prems(2) \<open>\<pi> \<in> L1 \<inter> L2\<close>
        unfolding type_1_conforms.simps
        by fastforce
      then show ?case
        using \<open>xy = (x, y)\<close> by auto 
    qed
  qed
qed


lemma equiv_by_reduction : "(L1 \<preceq>[X,equiv Y] L2) \<longleftrightarrow> ((L1 \<preceq>[X,red Y] L2) \<and> (L2 \<preceq>[X,red Y] L1))"
  by fastforce 

lemma equiv_type_1 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(L1 = L2) \<longleftrightarrow> (L1 \<preceq>[X,equiv Y] L2)"
  unfolding equiv_by_reduction
  unfolding red_type_1[OF assms(1,2), symmetric] 
  unfolding red_type_1[OF assms(2,1), symmetric]
  unfolding language_inclusion_def
  by blast


lemma quasired_type_1 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "quasi_reduction L1 L2 \<longleftrightarrow> (L1 \<preceq>[X,quasired Y] L2)"
proof 
  have "\<And> \<pi> x . quasi_reduction L1 L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> quasired Y"
  proof - 
    fix \<pi> x assume "quasi_reduction L1 L2" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> X"

    show "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> quasired Y" 
    proof (cases "x \<in> exec[L2,\<pi>]")
      case False
      then show ?thesis
        by (metis (mono_tags, lifting) CollectI UnCI assms(1) outputs_executable outputs_in_alphabet quasired.elims)
    next
      case True
      then obtain y where "y \<in> out[L2,\<pi>,x]" by auto
      then have "out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]" and "out[L1,\<pi>,x] \<noteq> {}"
        using \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>x \<in> X\<close> \<open>quasi_reduction L1 L2\<close>
        unfolding quasi_reduction_def by force+
      moreover have "out[L2,\<pi>,x] \<subseteq> Y"
        by (meson assms(2) outputs_in_alphabet) 
      ultimately show ?thesis
        unfolding quasired.simps by blast 
    qed
  qed
  then show "quasi_reduction L1 L2 \<Longrightarrow> (L1 \<preceq>[X,quasired Y] L2)"
    by auto


  have "\<And> \<pi> x . L1 \<preceq>[X,quasired Y] L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]"
   and "\<And> \<pi> x . L1 \<preceq>[X,quasired Y] L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] \<noteq> {}"
  proof -
    fix \<pi> x assume "L1 \<preceq>[X,quasired Y] L2" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
    then have "x \<in> X"
      using executable_inputs_in_alphabet[OF assms(2)] by auto 

    have "out[L2,\<pi>,x] \<noteq> {}"
      using \<open>x \<in> exec[L2,\<pi>]\<close>
      by (meson outputs_executable) 
    moreover have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> quasired Y"
      by (meson \<open>L1 \<preceq>[X,quasired Y] L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>x \<in> X\<close> type_1_conforms.elims(2))
    ultimately show "out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]"
                and "out[L1,\<pi>,x] \<noteq> {}"
      unfolding quasired.simps 
      by blast+
  qed 
  then show "L1 \<preceq>[X,quasired Y] L2 \<Longrightarrow> quasi_reduction L1 L2"
    by (meson quasi_reduction_def) 
qed


lemma quasieq_type_1 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "quasi_equivalence L1 L2 \<longleftrightarrow> (L1 \<preceq>[X,quasieq Y] L2)" 
proof     
  have "\<And> \<pi> x . quasi_equivalence L1 L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> quasieq Y"
  proof - 
    fix \<pi> x assume "quasi_equivalence L1 L2" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> X"

    show "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> quasieq Y" 
    proof (cases "x \<in> exec[L2,\<pi>]")
      case False
      then show ?thesis
        by (metis (mono_tags, lifting) CollectI UnCI assms(1) outputs_executable outputs_in_alphabet quasieq.simps)
    next
      case True
      then show ?thesis
        by (metis (mono_tags, lifting) CollectI UnCI \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>quasi_equivalence L1 L2\<close> assms(1) outputs_in_alphabet quasi_equivalence_def quasieq.simps) 
    qed
  qed    
  then show "quasi_equivalence L1 L2 \<Longrightarrow> (L1 \<preceq>[X,quasieq Y] L2)"
    by auto


  have "\<And> \<pi> x . L1 \<preceq>[X,quasieq Y] L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = out[L2,\<pi>,x]"
  proof -
    fix \<pi> x assume "L1 \<preceq>[X,quasieq Y] L2" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
    then have "x \<in> X"
      using executable_inputs_in_alphabet[OF assms(2)] by auto 

    have "out[L2,\<pi>,x] \<noteq> {}"
      using \<open>x \<in> exec[L2,\<pi>]\<close>
      by (meson outputs_executable) 
    moreover have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> quasieq Y"
      by (meson \<open>L1 \<preceq>[X,quasieq Y] L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>x \<in> X\<close> type_1_conforms.elims(2))
    ultimately show "out[L1,\<pi>,x] = out[L2,\<pi>,x]"
      unfolding quasieq.simps 
      by blast
  qed 
  then show "L1 \<preceq>[X,quasieq Y] L2 \<Longrightarrow> quasi_equivalence L1 L2"
    by (meson quasi_equivalence_def) 
qed


lemma strongred_type_1 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "strong_reduction L1 L2 \<longleftrightarrow> (L1 \<preceq>[X,strongred Y] L2)"
proof 
  have "\<And> \<pi> x . strong_reduction L1 L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> strongred Y"
  proof - 
    fix \<pi> x assume "strong_reduction L1 L2" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> X"

    have "out[L2,\<pi>,x] \<subseteq> Y"
      using outputs_in_alphabet[OF assms(2)] .

    show "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> strongred Y" 
    proof (cases "x \<in> exec[L2,\<pi>]")
      case False
      then have "out[L2,\<pi>,x] = {}"
        using outputs_executable by force
      then have "out[L1,\<pi>,x] = {}"
        using \<open>strong_reduction L1 L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close>  
        unfolding strong_reduction_def by blast
      then show ?thesis
        using \<open>out[L2,\<pi>,x] = {}\<close> by auto 
    next
      case True
      then have "out[L1,\<pi>,x] \<noteq> {}" 
        using \<open>strong_reduction L1 L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close>  
        unfolding strong_reduction_def
        by (meson quasi_reduction_def)
      moreover have "out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]"
        by (meson True \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>strong_reduction L1 L2\<close> quasi_reduction_def strong_reduction_def)
      ultimately show ?thesis 
        unfolding strongred.simps 
        using outputs_executable outputs_in_alphabet[OF assms(2)]
        by force
    qed
  qed
  then show "strong_reduction L1 L2 \<Longrightarrow> (L1 \<preceq>[X,strongred Y] L2)"
    by auto


  have "\<And> \<pi> x . L1 \<preceq>[X,strongred Y] L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] \<noteq> {}"
   and "\<And> \<pi> x . L1 \<preceq>[X,strongred Y] L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]"
  proof -
    fix \<pi> x y assume "L1 \<preceq>[X,strongred Y] L2" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
    then have "x \<in> X"
      using executable_inputs_in_alphabet[OF assms(2)] by auto 

    have "out[L2,\<pi>,x] \<noteq> {}"
      using \<open>x \<in> exec[L2,\<pi>]\<close>
      by (meson outputs_executable) 
    moreover have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> strongred Y"
      by (meson \<open>L1 \<preceq>[X,strongred Y] L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>x \<in> X\<close> type_1_conforms.elims(2))
    ultimately show "out[L1,\<pi>,x] \<noteq> {}" and "out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]"
      unfolding strongred.simps 
      by blast+
  qed 
  moreover have "\<And> \<pi> x . L1 \<preceq>[X,strongred Y] L2 \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> out[L2,\<pi>,x] = {} \<Longrightarrow> out[L1,\<pi>,x] = {}"
  proof -
    fix \<pi> x assume "L1 \<preceq>[X,strongred Y] L2" and "\<pi> \<in> L1 \<inter> L2" and "out[L2,\<pi>,x] = {}"

    show "out[L1,\<pi>,x] = {}" 
    proof (rule ccontr)
      assume "out[L1,\<pi>,x] \<noteq> {}"
      then have "x \<in> X"
        by (meson assms(1) executable_inputs_in_alphabet outputs_executable) 
      then have "out[L2,\<pi>,x] \<noteq> {}"
        using \<open>L1 \<preceq>[X,strongred Y] L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>out[L1,\<pi>,x] \<noteq> {}\<close> by fastforce 
      then show False 
        using \<open>out[L2,\<pi>,x] = {}\<close> by simp
    qed
  qed
  ultimately show "L1 \<preceq>[X,strongred Y] L2 \<Longrightarrow> strong_reduction L1 L2" 
    unfolding strong_reduction_def quasi_reduction_def by blast
qed


subsection \<open>$\le$ Conformance\<close>

fun type_2_conforms :: "('x,'y) language \<Rightarrow> 'x alphabet \<Rightarrow> 'y output_relation \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where
  "type_2_conforms L1 X H L2 = (
      (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> X . (out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> H) \<and>
      (\<forall> \<pi> \<in> L1 \<inter> L2 . exec[L2,\<pi>] \<noteq> {} \<longrightarrow> (\<exists> x . out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {})))"

notation type_2_conforms ("_ \<le>[_,_] _")

fun semieq :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "semieq Y = {(A,A) | A . A \<subseteq> Y} \<union> {({},A) | A . A \<subseteq> Y} \<union> {(A,{}) | A . A \<subseteq> Y}"

fun semired :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "semired Y = {(A,B) | A B . A \<subseteq> B \<and> B \<subseteq> Y} \<union> {(C,{}) | C . C \<subseteq> Y}"

fun strongsemieq :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "strongsemieq Y = {(A,A) | A . A \<subseteq> Y} \<union> {({},A) | A . A \<subseteq> Y}"

fun strongsemired :: "'y alphabet \<Rightarrow> 'y output_relation" where 
  "strongsemired Y = {(A,B) | A B . A \<subseteq> B \<and> B \<subseteq> Y}"

lemma strongsemieq_alt_def : "strongsemieq Y = semieq Y \<inter> red Y" 
  by auto

lemma strongsemired_alt_def : "strongsemired Y = red Y" 
  by auto


lemma semired_type_2 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(semi_reduction L1 L2) \<longleftrightarrow> (L1 \<le>[X, semired Y] L2)"
proof 
  show "semi_reduction L1 L2 \<Longrightarrow> L1 \<le>[X, semired Y] L2"
  proof -
    assume "semi_reduction L1 L2"
    then have p1: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> (out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])"
         and  p2: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}"
      unfolding semi_reduction_def by blast+

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> semired Y"
      by (metis (mono_tags, lifting) CollectI UnCI assms(1) assms(2) outputs_executable outputs_in_alphabet p1 semired.simps)
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists>x. out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      using p2 by fastforce
    ultimately show "L1 \<le>[X, semired Y] L2"
      by auto
  qed

  show "L1 \<le>[X,semired Y] L2 \<Longrightarrow> semi_reduction L1 L2"
  proof -
    assume "L1 \<le>[X,semired Y] L2" 
    then have p1 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> semired Y"
         and  p2 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists> x . out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      by auto

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> (out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])" 
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
      then have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> semired Y"
        using p1 executable_inputs_in_alphabet[OF assms(2)] by auto
      moreover have "out[L2,\<pi>,x] \<noteq> {}"
        using \<open>x \<in> exec[L2,\<pi>]\<close> by auto
      ultimately show "(out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])" 
        unfolding semired.simps by blast
    qed
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}" 
      using p2 by blast 
    ultimately show ?thesis
      unfolding semi_reduction_def by blast
  qed
qed


lemma semieq_type_2 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(semi_equivalence L1 L2) \<longleftrightarrow> (L1 \<le>[X, semieq Y] L2)"
proof 
  show "semi_equivalence L1 L2 \<Longrightarrow> L1 \<le>[X, semieq Y] L2"
  proof -
    assume "semi_equivalence L1 L2"
    then have p1: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]"
         and  p2: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}"
      unfolding semi_equivalence_def by blast+

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> semieq Y"
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<in> X"
      show "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> semieq Y"
      proof (cases "x \<in> exec[L2,\<pi>]")
        case True
        then have "out[L2,\<pi>,x] \<noteq> {}" by auto
        then show ?thesis 
          using p1[OF \<open>\<pi> \<in> L1 \<inter> L2\<close> True]  
          using outputs_in_alphabet[OF assms(2)]
          unfolding semieq.simps
          by fastforce 
      next
        case False
        then show ?thesis
          by (metis (mono_tags, lifting) CollectI UnI2 assms(1) outputs_executable outputs_in_alphabet semieq.elims)
      qed
    qed
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists>x. out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      using p2 by fastforce
    ultimately show "L1 \<le>[X, semieq Y] L2"
      by auto
  qed

  show "L1 \<le>[X,semieq Y] L2 \<Longrightarrow> semi_equivalence L1 L2"
  proof -
    assume "L1 \<le>[X,semieq Y] L2" 
    then have p1 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> semieq Y"
         and  p2 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists> x . out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      by auto

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]" 
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
      then have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> semieq Y"
        using p1 executable_inputs_in_alphabet[OF assms(2)] by auto
      moreover have "out[L2,\<pi>,x] \<noteq> {}"
        using \<open>x \<in> exec[L2,\<pi>]\<close> by auto
      ultimately show "out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]" 
        unfolding semieq.simps
        by blast
    qed
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}" 
      using p2 by blast 
    ultimately show ?thesis
      unfolding semi_equivalence_def by blast
  qed
qed


lemma strongsemired_type_2 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(strong_semi_reduction L1 L2) \<longleftrightarrow> (L1 \<le>[X, strongsemired Y] L2)"
proof 
  show "strong_semi_reduction L1 L2 \<Longrightarrow> L1 \<le>[X, strongsemired Y] L2"
  proof -
    assume "strong_semi_reduction L1 L2"
    then have p1: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> (out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])"
         and  p2: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}"
         and  p3: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<notin> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {}"
      unfolding strong_semi_reduction_def by blast+

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> strongsemired Y"
      unfolding strongsemired.simps
      by (metis (mono_tags, lifting) CollectI assms(2) outputs_executable outputs_in_alphabet p1 p3 set_eq_subset)
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists>x. out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      using p2 by fastforce
    ultimately show "L1 \<le>[X, strongsemired Y] L2"
      by auto
  qed

  show "L1 \<le>[X,strongsemired Y] L2 \<Longrightarrow> strong_semi_reduction L1 L2"
  proof -
    assume "L1 \<le>[X,strongsemired Y] L2" 
    then have p1 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> strongsemired Y"
         and  p2 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists> x . out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      by auto

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> (out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])" 
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
      then have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> semired Y"
        using p1 executable_inputs_in_alphabet[OF assms(2)] by auto
      moreover have "out[L2,\<pi>,x] \<noteq> {}"
        using \<open>x \<in> exec[L2,\<pi>]\<close> by auto
      ultimately show "(out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])" 
        unfolding semired.simps by blast
    qed
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}" 
      using p2 by blast 
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<notin> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {}"
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<notin> exec[L2,\<pi>]"
      
      have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> strongsemired Y"
      proof (cases "x \<in> exec[L1,\<pi>]")
        case True
        then show ?thesis
          by (meson \<open>\<pi> \<in> L1 \<inter> L2\<close> assms(1) executable_inputs_in_alphabet p1) 
      next
        case False 
        then show ?thesis
          using \<open>x \<notin> exec[L2,\<pi>]\<close> by fastforce 
      qed 
      moreover have "out[L2,\<pi>,x] = {}"
        using \<open>x \<notin> exec[L2,\<pi>]\<close> by auto
      ultimately show "out[L1,\<pi>,x] = {}" 
        unfolding strongsemired.simps
        by blast 
    qed
    ultimately show ?thesis
      unfolding strong_semi_reduction_def by blast
  qed
qed


lemma strongsemieq_type_2 : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(strong_semi_equivalence L1 L2) \<longleftrightarrow> (L1 \<le>[X, strongsemieq Y] L2)"
proof 
  show "strong_semi_equivalence L1 L2 \<Longrightarrow> L1 \<le>[X, strongsemieq Y] L2"
  proof -
    assume "strong_semi_equivalence L1 L2"
    then have p1: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]"
         and  p2: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}"
         and  p3: "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<notin> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {}"
      unfolding strong_semi_equivalence_def by blast+

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> strongsemieq Y"
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<in> X"
      show "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> strongsemieq Y"
      proof (cases "x \<in> exec[L2,\<pi>]")
        case True
        then have "out[L2,\<pi>,x] \<noteq> {}" by auto
        then show ?thesis 
          using p1[OF \<open>\<pi> \<in> L1 \<inter> L2\<close> True]  
          using outputs_in_alphabet[OF assms(2)]
          by fastforce 
      next
        case False
        then show ?thesis
          using \<open>\<pi> \<in> L1 \<inter> L2\<close> p3 by fastforce
      qed
    qed
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists>x. out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      using p2 by fastforce
    ultimately show "L1 \<le>[X, strongsemieq Y] L2"
      by auto
  qed

  show "L1 \<le>[X,strongsemieq Y] L2 \<Longrightarrow> strong_semi_equivalence L1 L2"
  proof -
    assume "L1 \<le>[X,strongsemieq Y] L2" 
    then have p1 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> strongsemieq Y"
         and  p2 : "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists> x . out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
      by auto

    have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]" 
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
      then have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> semieq Y"
        using p1 executable_inputs_in_alphabet[OF assms(2)] by auto
      moreover have "out[L2,\<pi>,x] \<noteq> {}"
        using \<open>x \<in> exec[L2,\<pi>]\<close> by auto
      ultimately show "out[L1,\<pi>,x] = {} \<or> out[L1,\<pi>,x] = out[L2,\<pi>,x]" 
        unfolding semieq.simps
        by blast
    qed
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> \<exists> x' . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}" 
      using p2 by blast 
    moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<notin> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = {}"
    proof -
      fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<notin> exec[L2,\<pi>]"
      
      have "(out[L1,\<pi>,x],out[L2,\<pi>,x]) \<in> strongsemieq Y"
      proof (cases "x \<in> exec[L1,\<pi>]")
        case True
        then show ?thesis
          by (meson \<open>\<pi> \<in> L1 \<inter> L2\<close> assms(1) executable_inputs_in_alphabet p1) 
      next
        case False 
        then show ?thesis
          using \<open>x \<notin> exec[L2,\<pi>]\<close> by fastforce 
      qed 
      moreover have "out[L2,\<pi>,x] = {}"
        using \<open>x \<notin> exec[L2,\<pi>]\<close> by auto
      ultimately show "out[L1,\<pi>,x] = {}" 
        unfolding strongsemieq.simps
        by blast 
    qed
    ultimately show ?thesis
      unfolding strong_semi_equivalence_def by blast
  qed
qed


section \<open>Comparing Conformance Relations\<close>

lemma type_1_subset :
  assumes "L1 \<preceq>[X,H1] L2"
  and     "H1 \<subseteq> H2"
shows "L1 \<preceq>[X,H2] L2"
  using assms by auto 

lemma type_1_subsets : 
shows "equiv Y \<subseteq> strongred Y"
  and "equiv Y \<subseteq> quasieq Y"
  and "strongred Y \<subseteq> red Y"
  and "strongred Y \<subseteq> quasired Y"
  and "quasieq Y \<subseteq> quasired Y" 
  by auto

lemma type_1_implications : 
shows "L1 \<preceq>[X, equiv Y] L2 \<Longrightarrow> L1 \<preceq>[X, strongred Y] L2" 
  and "L1 \<preceq>[X, equiv Y] L2 \<Longrightarrow> L1 \<preceq>[X, red Y] L2"
  and "L1 \<preceq>[X, equiv Y] L2 \<Longrightarrow> L1 \<preceq>[X, quasired Y] L2"
  and "L1 \<preceq>[X, equiv Y] L2 \<Longrightarrow> L1 \<preceq>[X, quasieq Y] L2"
  and "L1 \<preceq>[X, strongred Y] L2 \<Longrightarrow> L1 \<preceq>[X, red Y] L2" 
  and "L1 \<preceq>[X, strongred Y] L2 \<Longrightarrow> L1 \<preceq>[X, quasired Y] L2" 
  and "L1 \<preceq>[X, quasieq Y] L2 \<Longrightarrow> L1 \<preceq>[X, quasired Y] L2" 
  using type_1_subset[OF _ type_1_subsets(4), of L1 X Y L2] 
  using type_1_subset[OF _ type_1_subsets(5), of L1 X Y L2] 
  by auto


lemma type_2_subset :
  assumes "L1 \<le>[X,H1] L2"
  and     "H1 \<subseteq> H2"
shows "L1 \<le>[X,H2] L2"
  using assms by auto 

lemma type_2_subsets : 
shows "strongsemieq Y \<subseteq> strongsemired Y"
  and "strongsemieq Y \<subseteq> semieq Y"
  and "semieq Y \<subseteq> semired Y"
  and "strongsemired Y \<subseteq> semired Y"
  and "strongsemired Y \<subseteq> red Y"
  by auto

lemma type_2_implications : 
shows "L1 \<le>[X, strongsemieq Y] L2 \<Longrightarrow> L1 \<le>[X, strongsemired Y] L2" 
  and "L1 \<le>[X, strongsemieq Y] L2 \<Longrightarrow> L1 \<le>[X, semieq Y] L2"
  and "L1 \<le>[X, strongsemieq Y] L2 \<Longrightarrow> L1 \<le>[X, semired Y] L2"
  and "L1 \<le>[X, strongsemired Y] L2 \<Longrightarrow> L1 \<le>[X, semired Y] L2"
  and "L1 \<le>[X, semieq Y] L2 \<Longrightarrow> L1 \<le>[X, semired Y] L2"
  by auto


lemma type_1_conformance_to_type_2 :
  assumes "is_language X Y L2"
  and     "L1 \<preceq>[X,H1] L2"
  and     "H1 \<subseteq> H2"
  and     "\<And> A B . (A,B) \<in> H1 \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A \<inter> B \<noteq> {}"
shows "L1 \<le>[X,H2] L2"
proof -
  have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H2"
    using assms(2,3) by auto
  moreover have "\<And> \<pi> . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> \<exists>x. out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}"
  proof -
    fix \<pi> assume "\<pi> \<in> L1 \<inter> L2" and "exec[L2,\<pi>] \<noteq> {}"
    then obtain x where "x \<in> exec[L2,\<pi>]"
      by blast
    then have "x \<in> X"
      by (meson assms(1) executable_inputs_in_alphabet)
    then have "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H1"
      using \<open>\<pi> \<in> L1 \<inter> L2\<close> assms(2) by auto
    moreover have "out[L2,\<pi>,x] \<noteq> {}"
      by (meson \<open>x \<in> exec[L2,\<pi>]\<close> outputs_executable) 
    ultimately have "out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}" 
      using assms(4) by blast 
    then show "\<exists>x. out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}" 
      by blast
  qed
  ultimately show ?thesis 
    by auto
qed

lemma type_1_and_2_mixed_implications : 
  assumes "is_language X Y L2"
shows "L1 \<le>[X, strongsemieq Y] L2 \<Longrightarrow> L1 \<preceq>[X, red Y] L2"
  and "L1 \<le>[X, strongsemired Y] L2 \<Longrightarrow> L1 \<preceq>[X, red Y] L2"
  and "L1 \<preceq>[X, quasieq Y] L2 \<Longrightarrow> L1 \<le>[X, semieq Y] L2"
  and "L1 \<preceq>[X, quasired Y] L2 \<Longrightarrow> L1 \<le>[X, semired Y] L2"
  and "L1 \<preceq>[X, equiv Y] L2 \<Longrightarrow> L1 \<le>[X, strongsemieq Y] L2"
  and "L1 \<preceq>[X, strongred Y] L2 \<Longrightarrow> L1 \<le>[X, strongsemired Y] L2"
proof -

  show "L1 \<le>[X, strongsemieq Y] L2 \<Longrightarrow> L1 \<preceq>[X, red Y] L2"
   and "L1 \<le>[X, strongsemired Y] L2 \<Longrightarrow> L1 \<preceq>[X, red Y] L2"
    by auto

  have "\<And> A B . (A,B) \<in> quasieq Y \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A \<inter> B \<noteq> {}"
    by auto
  moreover have "quasieq Y \<subseteq> semieq Y"
    by auto    
  ultimately show "L1 \<preceq>[X, quasieq Y] L2 \<Longrightarrow> L1 \<le>[X, semieq Y] L2"
    using type_1_conformance_to_type_2[OF assms] by blast

  have "\<And> A B . (A,B) \<in> quasired Y \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A \<inter> B \<noteq> {}"
    by auto
  moreover have "quasired Y \<subseteq> semired Y"
    unfolding quasired.simps semired.simps by blast
  ultimately show "L1 \<preceq>[X, quasired Y] L2 \<Longrightarrow> L1 \<le>[X, semired Y] L2"
    using type_1_conformance_to_type_2[OF assms] by blast

  have "\<And> A B . (A,B) \<in> equiv Y \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A \<inter> B \<noteq> {}"
    by auto
  moreover have "equiv Y \<subseteq> strongsemieq Y"
    unfolding equiv.simps strongsemieq.simps by blast
  ultimately show "L1 \<preceq>[X, equiv Y] L2 \<Longrightarrow> L1 \<le>[X, strongsemieq Y] L2"
    using type_1_conformance_to_type_2[OF assms] by blast

  have "\<And> A B . (A,B) \<in> strongred Y \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A \<inter> B \<noteq> {}"
    by auto
  moreover have "strongred Y \<subseteq> strongsemired Y"
    unfolding strongred.simps strongsemired.simps by blast
  ultimately show "L1 \<preceq>[X, strongred Y] L2 \<Longrightarrow> L1 \<le>[X, strongsemired Y] L2"
    using type_1_conformance_to_type_2[OF assms] by blast
qed


subsection \<open>Completely Specified Languages\<close>

definition partiality_component :: "'y set \<Rightarrow> 'y output_relation" where
  "partiality_component Y = {(A,{}) | A . A \<subseteq> Y} \<union> {({},A) | A . A \<subseteq> Y}"

abbreviation(input) "\<Pi> Y \<equiv> partiality_component Y"


lemma conformance_without_partiality : 
shows "strongsemieq Y - \<Pi> Y = semieq Y - \<Pi> Y"
  and "semieq Y - \<Pi> Y = equiv Y - \<Pi> Y"
  and "strongsemired Y - \<Pi> Y = semired Y - \<Pi> Y"
  and "semired Y - \<Pi> Y = red Y - \<Pi> Y"
  unfolding partiality_component_def  
  by fastforce+


section \<open>Conformance Testing\<close>

type_synonym ('x,'y) state_cover = "('x,'y) language"
type_synonym ('x,'y) transition_cover = "('x,'y) state_cover \<times> 'x set"

fun is_state_cover :: "('x,'y) language \<Rightarrow> ('x,'y) language \<Rightarrow> ('x,'y) state_cover \<Rightarrow> bool" where
  "is_state_cover L1 L2 V = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<exists> \<alpha> \<in> V . \<L>[L1,\<pi>] = \<L>[L1,\<alpha>] \<and> \<L>[L2,\<pi>] = \<L>[L2,\<alpha>])"



lemma state_cover_subset : 
assumes "is_language X Y L1" 
    and "is_language X Y L2"
    and "is_state_cover L1 L2 V"
    and "\<pi> \<in> L1 \<inter> L2"
obtains \<alpha> where "\<alpha> \<in> V"
            and "\<alpha> \<in> L1 \<inter> L2"
            and "\<L>[L1,\<pi>] = \<L>[L1,\<alpha>]"
            and "\<L>[L2,\<pi>] = \<L>[L2,\<alpha>]"
proof -
  obtain \<alpha> where "\<alpha> \<in> V"
             and "\<L>[L1,\<pi>] = \<L>[L1,\<alpha>]"
             and "\<L>[L2,\<pi>] = \<L>[L2,\<alpha>]"
    using assms
    by (meson is_state_cover.elims(2)) 
  moreover have "\<L>[L1,\<pi>] \<noteq> {}" and "\<L>[L2,\<pi>] \<noteq> {}"
    by (metis Collect_empty_eq_bot Int_iff append.right_neutral assms(4) empty_def language_for_state.elims)+
  ultimately have "\<alpha> \<in> L1 \<inter> L2"
    using language_of_state_empty_iff[OF assms(1)] language_of_state_empty_iff[OF assms(2)]
    by blast
  then show ?thesis using that[OF \<open>\<alpha> \<in> V\<close> _ \<open>\<L>[L1,\<pi>] = \<L>[L1,\<alpha>]\<close> \<open>\<L>[L2,\<pi>] = \<L>[L2,\<alpha>]\<close>] 
    by blast
qed
  

theorem sufficient_condition_for_type_1_conformance : 
  assumes "is_language X Y L1" 
  and     "is_language X Y L2"
  and     "is_state_cover L1 L2 V"
shows "(L1 \<preceq>[X,H] L2) \<longleftrightarrow> (\<forall> \<pi> \<in> V . \<forall> x \<in> X . \<pi> \<in> L1 \<inter> L2 \<longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H)"
proof 
  show "(L1 \<preceq>[X,H] L2) \<Longrightarrow> (\<forall> \<pi> \<in> V . \<forall> x \<in> X . \<pi> \<in> L1 \<inter> L2 \<longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H)"
    by auto

  have "(\<And> \<pi> x . \<pi> \<in> V \<Longrightarrow> x \<in> X \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H) \<Longrightarrow> (\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H)"
  proof -
    fix \<pi> x assume "(\<And> \<pi> x . \<pi> \<in> V \<Longrightarrow> x \<in> X \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H)"
               and "\<pi> \<in> L1 \<inter> L2"
               and "x \<in> X" 

    obtain \<alpha> where "\<alpha> \<in> V" and "\<alpha> \<in> L1 \<inter> L2" and "\<L>[L1,\<pi>] = \<L>[L1,\<alpha>]" and "\<L>[L2,\<pi>] = \<L>[L2,\<alpha>]" 
      using state_cover_subset[OF assms \<open>\<pi> \<in> L1 \<inter> L2\<close>] by auto
    then have "out[L1,\<pi>,x] = out[L1,\<alpha>,x]" and "out[L2,\<pi>,x] = out[L2,\<alpha>,x]" 
      by force+
    moreover have "(out[L1,\<alpha>,x], out[L2,\<alpha>,x]) \<in> H"
      using \<open>(\<And> \<pi> x . \<pi> \<in> V \<Longrightarrow> x \<in> X \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H)\<close> \<open>\<alpha> \<in> V\<close> \<open>x \<in> X\<close> \<open>\<alpha> \<in> L1 \<inter> L2\<close>
      by blast
    ultimately show "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H" 
      by simp
  qed
  then show "\<forall>\<pi>\<in>V. \<forall>x\<in>X. \<pi> \<in> L1 \<inter> L2 \<longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<Longrightarrow> L1 \<preceq>[X,H] L2" 
    by auto
qed

theorem sufficient_condition_for_type_2_conformance : 
  assumes "is_language X Y L1" 
  and     "is_language X Y L2"
  and     "is_state_cover L1 L2 V"
shows "(L1 \<le>[X,H] L2) \<longleftrightarrow> (\<forall> \<pi> \<in> V . \<forall> x \<in> X . \<pi> \<in> L1 \<inter> L2 \<longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {})))"
proof 

  have "\<And> \<pi> x . (L1 \<le>[X,H] L2) \<Longrightarrow> \<pi> \<in> V \<Longrightarrow> x \<in> X \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))"
  proof -
    fix \<pi> x assume "L1 \<le>[X,H] L2" and "\<pi> \<in> V" and "x \<in> X" and "\<pi> \<in> L1 \<inter> L2"

    have "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H"
      using \<open>L1 \<le>[X,H] L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close> \<open>x \<in> X\<close> by force 
    moreover have "out[L2,\<pi>,x] \<noteq> {} \<Longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {})"
      by (metis (no_types, lifting) \<open>L1 \<le>[X,H] L2\<close> \<open>\<pi> \<in> L1 \<inter> L2\<close> assms(2) empty_iff executable_inputs_in_alphabet inf_bot_right outputs_executable type_2_conforms.elims(2))  
    ultimately show "(out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))"
      by blast
  qed
  then show "(L1 \<le>[X,H] L2) \<Longrightarrow> (\<forall> \<pi> \<in> V . \<forall> x \<in> X . \<pi> \<in> L1 \<inter> L2 \<longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {})))"
    by auto

  have "(\<And> \<pi> x . \<pi> \<in> V \<Longrightarrow> x \<in> X \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))) \<Longrightarrow> (\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H)"
    by (meson assms(1) assms(2) assms(3) sufficient_condition_for_type_1_conformance type_1_conforms.elims(2)) 
  moreover have "(\<And> \<pi> x . \<pi> \<in> V \<Longrightarrow> x \<in> X \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))) \<Longrightarrow> (\<And> \<pi> . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> exec[L2,\<pi>] \<noteq> {} \<Longrightarrow> (\<exists> x . out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {}))"
  proof -
    fix \<pi> assume "\<pi> \<in> L1 \<inter> L2" 
             and "exec[L2,\<pi>] \<noteq> {}" 
             and *: "(\<And> \<pi> x . \<pi> \<in> V \<Longrightarrow> x \<in> X \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {})))"
 
    then obtain x where "x \<in> X" and "out[L2,\<pi>,x] \<noteq> {}"
      by (metis all_not_in_conv assms(2) executable_inputs_in_alphabet outputs_executable)

    moreover obtain \<alpha> where "\<alpha> \<in> V"
                        and "\<alpha> \<in> L1 \<inter> L2"
                        and "\<L>[L1,\<pi>] = \<L>[L1,\<alpha>]"
                        and "\<L>[L2,\<pi>] = \<L>[L2,\<alpha>]"
      using state_cover_subset[OF assms \<open>\<pi> \<in> L1 \<inter> L2\<close>] by blast
    ultimately show "(\<exists> x . out[L1,\<pi>,x] \<inter> out[L2,\<pi>,x] \<noteq> {})"
      using *
      by (metis outputs.elims) 
  qed
  ultimately show "(\<forall> \<pi> \<in> V . \<forall> x \<in> X . \<pi> \<in> L1 \<inter> L2 \<longrightarrow> (out[L1,\<pi>,x], out[L2,\<pi>,x]) \<in> H \<and> (out[L2,\<pi>,x] \<noteq> {} \<longrightarrow> (\<exists> x' \<in> X . out[L1,\<pi>,x'] \<inter> out[L2,\<pi>,x'] \<noteq> {}))) \<Longrightarrow> (L1 \<le>[X,H] L2)"
    by auto
qed


lemma intersections_card_helper : 
  assumes "finite X" 
  and     "finite Y" 
shows "card {A \<inter> B | A B . A \<in> X \<and> B \<in> Y} \<le> card X * card Y"
proof -
  have "{A \<inter> B | A B . A \<in> X \<and> B \<in> Y} = (\<lambda> (A,B) . A \<inter> B) ` (X \<times> Y)"
    by auto
  then have "card {A \<inter> B | A B . A \<in> X \<and> B \<in> Y} \<le> card (X \<times> Y)"
    by (metis (no_types, lifting) assms(1) assms(2) card_image_le finite_SigmaI) 
  then show ?thesis
    by (simp add: card_cartesian_product) 
qed


lemma prefix_length_take : 
  "(prefix xs ys \<and> length xs \<le> k) \<longleftrightarrow> (prefix xs (take k ys))"
proof 
  show "prefix xs ys \<and> length xs \<le> k \<Longrightarrow> prefix xs (take k ys)"
    using prefix_length_prefix take_is_prefix by fastforce 
  show "prefix xs (take k ys) \<Longrightarrow> prefix xs ys \<and> length xs \<le> k"
    by (metis le_trans length_take min.cobounded2 prefix_length_le prefix_order.order_trans take_is_prefix) 
qed


lemma brute_force_state_cover : 
  assumes "is_language X Y L1"
      and "is_language X Y L2"
      and "finite {\<L>[L1,\<pi>] | \<pi> . \<pi> \<in> L1}"
      and "finite {\<L>[L2,\<pi>] | \<pi> . \<pi> \<in> L2}"
      and "card {\<L>[L1,\<pi>] | \<pi> . \<pi> \<in> L1} \<le> n"
      and "card {\<L>[L2,\<pi>] | \<pi> . \<pi> \<in> L2} \<le> m" 
    shows "is_state_cover L1 L2 {\<alpha> . length \<alpha> \<le> m * n - 1 \<and> (\<forall> xy \<in> set \<alpha> . fst xy \<in> X \<and> snd xy \<in> Y)}" 
proof (rule ccontr)
  let ?V = "{\<alpha>. length \<alpha> \<le> m * n - 1 \<and> (\<forall>xy\<in>set \<alpha>. fst xy \<in> X \<and> snd xy \<in> Y)}"
  assume "\<not> is_state_cover L1 L2 ?V"


  (* there is a trace of minimal length that is not covered *)

  define is_covered where "is_covered = (\<lambda> \<pi> . \<exists> \<alpha> \<in> ?V . \<L>[L1,\<pi>] = \<L>[L1,\<alpha>] \<and> \<L>[L2,\<pi>] = \<L>[L2,\<alpha>])"
  define missing_traces where "missing_traces = {\<tau> . \<tau> \<in> L1 \<inter> L2 \<and> \<not>is_covered \<tau>}"  
  define \<tau> where "\<tau> = arg_min length (\<lambda> \<pi> . \<pi> \<in> missing_traces)"

  have "missing_traces \<noteq> {}" 
    using \<open>\<not> is_state_cover L1 L2 ?V\<close>
    using is_covered_def missing_traces_def by fastforce 
  then have "\<tau> \<in> missing_traces" 
            "\<And> \<tau>' . \<tau>' \<in> missing_traces \<Longrightarrow> length \<tau> \<le> length \<tau>'" 
    using arg_min_nat_lemma[where P="(\<lambda> \<pi> . \<pi> \<in> missing_traces)" and m=length] 
    unfolding \<tau>_def[symmetric] by blast+
  then have \<tau>_props: "\<tau> \<in> L1 \<inter> L2"
                     "\<And> \<alpha> . \<alpha> \<in> ?V \<Longrightarrow> \<not>(\<L>[L1,\<tau>] = \<L>[L1,\<alpha>] \<and> \<L>[L2,\<tau>] = \<L>[L2,\<alpha>])"
    unfolding missing_traces_def is_covered_def by blast+
        
  
  (* this length is at least m*n, as otherwise it would be contained in the brute force state cover *)

  have "\<And> xy . xy \<in> set \<tau> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> Y"
    using \<open>\<tau> \<in> L1 \<inter> L2\<close> assms(1) by auto
  moreover have "\<tau> \<notin> ?V"
    using \<tau>_props(2) by blast 
  ultimately have "length \<tau> > m*n-1"
    by simp 


  (* at the same time, L1 \<times> L2 has at most m*n 'states' *)

  let ?L12 = "{\<L>[L1,\<pi>] | \<pi> . \<pi> \<in> L1} \<times> {\<L>[L2,\<pi>] | \<pi> . \<pi> \<in> L2}"

  have "finite ?L12"
    using assms(3,4)
    by blast 

  have "card ?L12 \<le> m*n"
    using assms(3,4,5,6)
    by (metis (no_types, lifting) Sigma_cong card_cartesian_product mult.commute mult_le_mono) 


  (* thus, the m*n many prefixes of \<tau> of length up to m*n-1 may visit at most m*n states *)

  let ?visited_states = "{(\<L>[L1,\<tau>'],\<L>[L2,\<tau>']) | \<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1}"

  have "\<And> \<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<Longrightarrow> \<tau>' \<in> L1 \<inter> L2"
    by (meson \<tau>_props(1) assms(1) assms(2) in_set_prefixes is_language.elims(2) language_intersection_is_language)
  then have "?visited_states \<subseteq> ?L12"
    by blast
  then have "card ?visited_states \<le> m * n"
    using \<open>finite ?L12\<close> \<open>card ?L12 \<le> m * n\<close>
    by (meson card_mono dual_order.trans) 


  (* due to the minimality of \<tau>, all prefixes of it must reach distinct states *)

  have no_index_loop : "\<And> i j . i < j \<Longrightarrow> j \<le> length \<tau> \<Longrightarrow> \<L>[L1, take i \<tau>] \<noteq> \<L>[L1, take j \<tau>] \<or> \<L>[L2, take i \<tau>] \<noteq> \<L>[L2, take j \<tau>]"
  proof (rule ccontr)
    fix i j 
    assume "i < j" and "j \<le> length \<tau>" and "\<not> (\<L>[L1,take i \<tau>] \<noteq> \<L>[L1,take j \<tau>] \<or> \<L>[L2,take i \<tau>] \<noteq> \<L>[L2,take j \<tau>])"
    then have "\<L>[L1,take i \<tau>] = \<L>[L1,take j \<tau>]" and "\<L>[L2,take i \<tau>] = \<L>[L2,take j \<tau>]"
      by auto

    have "{\<tau>'. \<tau> @ \<tau>' \<in> L1} = {\<tau>'. take j \<tau> @ drop j \<tau> @ \<tau>' \<in> L1}"
      by (metis append.assoc append_take_drop_id)
    have "{\<tau>'. \<tau> @ \<tau>' \<in> L2} = {\<tau>'. take j \<tau> @ drop j \<tau> @ \<tau>' \<in> L2}"
      by (metis append.assoc append_take_drop_id)

    have "\<L>[L1,take i \<tau> @ drop j \<tau>] = \<L>[L1,\<tau>]"
      using \<open>\<L>[L1,take i \<tau>] = \<L>[L1,take j \<tau>]\<close> 
      unfolding language_for_state.simps 
      unfolding \<open>{\<tau>'. \<tau> @ \<tau>' \<in> L1} = {\<tau>'. take j \<tau> @ drop j \<tau> @ \<tau>' \<in> L1}\<close> append.assoc by blast
    moreover have "\<L>[L2,take i \<tau> @ drop j \<tau>] = \<L>[L2,\<tau>]"
      using \<open>\<L>[L2,take i \<tau>] = \<L>[L2,take j \<tau>]\<close> 
      unfolding language_for_state.simps 
      unfolding \<open>{\<tau>'. \<tau> @ \<tau>' \<in> L2} = {\<tau>'. take j \<tau> @ drop j \<tau> @ \<tau>' \<in> L2}\<close> append.assoc by blast
    
    have "(take i \<tau> @ drop j \<tau>) \<in> missing_traces"
    proof (rule ccontr)
      assume "take i \<tau> @ drop j \<tau> \<notin> missing_traces" 
      moreover have "take i \<tau> @ drop j \<tau> \<in> L1 \<inter> L2"
        by (metis IntD1 IntD2 IntI \<open>\<L>[L1,take i \<tau>] = \<L>[L1,take j \<tau>]\<close> \<open>\<L>[L2,take i \<tau>] = \<L>[L2,take j \<tau>]\<close> \<tau>_props(1) append_take_drop_id language_for_state.elims mem_Collect_eq)
      ultimately obtain \<alpha> where "length \<alpha> \<le> m * n - 1" 
                                "(\<forall>xy\<in>set \<alpha>. fst xy \<in> X \<and> snd xy \<in> Y)"
                                "\<L>[L1,take i \<tau> @ drop j \<tau>] = \<L>[L1,\<alpha>]" 
                                "\<L>[L2,take i \<tau> @ drop j \<tau>] = \<L>[L2,\<alpha>]"
        unfolding missing_traces_def is_covered_def 
        by blast
      then have "\<tau> \<notin> missing_traces" 
        unfolding missing_traces_def is_covered_def 
        using \<open>\<tau> \<in> L1 \<inter> L2\<close>
        unfolding \<open>\<L>[L1,take i \<tau> @ drop j \<tau>] = \<L>[L1,\<tau>]\<close>
        unfolding \<open>\<L>[L2,take i \<tau> @ drop j \<tau>] = \<L>[L2,\<tau>]\<close> 
        by blast
      then show False
        using \<open>\<tau> \<in> missing_traces\<close> by simp
    qed
    moreover have "length (take i \<tau> @ drop j \<tau>) < length \<tau>" 
      using \<open>i < j\<close> \<open>j \<le> length \<tau>\<close> 
      by (induction \<tau> arbitrary: i j; auto)
    ultimately show False
      using \<open>\<And> \<tau>' . \<tau>' \<in> missing_traces \<Longrightarrow> length \<tau> \<le> length \<tau>'\<close>
      using leD by blast 
  qed
  
  have no_prefix_loop : "\<And> \<tau>' \<tau>'' . \<tau>' \<in> set (prefixes \<tau>) \<Longrightarrow> \<tau>'' \<in> set (prefixes \<tau>) \<Longrightarrow> \<tau>' \<noteq> \<tau>'' \<Longrightarrow> (\<L>[L1,\<tau>'],\<L>[L2,\<tau>']) \<noteq> (\<L>[L1,\<tau>''],\<L>[L2,\<tau>''])"
  proof -
    fix \<tau>' \<tau>'' assume "\<tau>' \<in> set (prefixes \<tau>)" and "\<tau>'' \<in> set (prefixes \<tau>)" and "\<tau>' \<noteq> \<tau>''" 

    obtain i where "\<tau>' = take i \<tau>" and "i \<le> length \<tau>"
      using \<open>\<tau>' \<in> set (prefixes \<tau>)\<close>
      by (metis append_eq_conv_conj in_set_prefixes linorder_linear prefix_def take_all_iff) 

    obtain j where "\<tau>'' = take j \<tau>" and "j \<le> length \<tau>"
      using \<open>\<tau>'' \<in> set (prefixes \<tau>)\<close>
      by (metis append_eq_conv_conj in_set_prefixes linorder_linear prefix_def take_all_iff)

    have "i \<noteq> j"
      using \<open>\<tau>' = take i \<tau>\<close> \<open>\<tau>' \<noteq> \<tau>''\<close> \<open>\<tau>'' = take j \<tau>\<close> by blast
    then consider (a) "i < j" | (b) "j < i"
      using nat_neq_iff by blast 
    then show "(\<L>[L1,\<tau>'],\<L>[L2,\<tau>']) \<noteq> (\<L>[L1,\<tau>''],\<L>[L2,\<tau>''])" 
      using no_index_loop
      using \<open>j \<le> length \<tau>\<close> \<open>i \<le> length \<tau>\<close>
      unfolding \<open>\<tau>' = take i \<tau>\<close> \<open>\<tau>'' = take j \<tau>\<close> 
      by (cases; blast)
  qed
  then have "inj_on (\<lambda> \<tau>' . (\<L>[L1,\<tau>'], \<L>[L2,\<tau>'])) {\<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1}" 
    using inj_onI
    by (metis (mono_tags, lifting) mem_Collect_eq) 
  then have "card ((\<lambda> \<tau>' . (\<L>[L1,\<tau>'], \<L>[L2,\<tau>'])) ` {\<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1}) = card {\<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1}"
    using card_image by blast
  moreover have "?visited_states = (\<lambda> \<tau>' . (\<L>[L1,\<tau>'], \<L>[L2,\<tau>'])) ` {\<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1}"
    by auto
  ultimately have "card ?visited_states = card {\<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1}" 
    by simp  
  moreover have "card {\<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1} = m*n" 
  proof -
    have "{\<tau>' . \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1} = set (prefixes (take (m*n-1) \<tau>))"
      unfolding in_set_prefixes prefix_length_take 
      by auto
    moreover have "length (take (m*n-1) \<tau>) = m*n-1"
      using \<open>length \<tau> > m*n-1\<close> by auto
    ultimately show ?thesis 
      using length_prefixes distinct_prefixes
      by (metis \<open>card {(\<L>[L1,\<tau>'], \<L>[L2,\<tau>']) |\<tau>'. \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1} = card {\<tau>' \<in> set (prefixes \<tau>). length \<tau>' \<le> m * n - 1}\<close> \<open>card {(\<L>[L1,\<tau>'], \<L>[L2,\<tau>']) |\<tau>'. \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1} \<le> m * n\<close> distinct_card less_diff_conv not_less_iff_gr_or_eq order_le_less) 
  qed
  
  
  (* that is, the m*n many prefixes of \<tau> of length up to m*n-1 must visit all m*n states *)

  ultimately have "card ?visited_states = m*n"
    by simp
  then have "?visited_states = ?L12"
    by (metis (no_types, lifting) \<open>card ({\<L>[L1,\<pi>] |\<pi>. \<pi> \<in> L1} \<times> {\<L>[L2,\<pi>] |\<pi>. \<pi> \<in> L2}) \<le> m * n\<close> \<open>finite ({\<L>[L1,\<pi>] |\<pi>. \<pi> \<in> L1} \<times> {\<L>[L2,\<pi>] |\<pi>. \<pi> \<in> L2})\<close> \<open>{(\<L>[L1,\<tau>'], \<L>[L2,\<tau>']) |\<tau>'. \<tau>' \<in> set (prefixes \<tau>) \<and> length \<tau>' \<le> m * n - 1} \<subseteq> {\<L>[L1,\<pi>] |\<pi>. \<pi> \<in> L1} \<times> {\<L>[L2,\<pi>] |\<pi>. \<pi> \<in> L2}\<close> card_seteq) 
    

  (* so that the state reached by \<tau> itself must at the same time be visited and not visited *)

  have "(\<L>[L1,\<tau>], \<L>[L2,\<tau>]) \<in> ?L12"
    using \<open>\<tau> \<in> L1 \<inter> L2\<close>
    by blast 
  moreover have "(\<L>[L1,\<tau>], \<L>[L2,\<tau>]) \<notin> ?visited_states" 
  proof 
    assume "(\<L>[L1,\<tau>], \<L>[L2,\<tau>]) \<in> ?visited_states"
    then obtain \<tau>' where "(\<L>[L1,\<tau>], \<L>[L2,\<tau>]) = (\<L>[L1,\<tau>'],\<L>[L2,\<tau>'])" 
                     and "\<tau>' \<in> set (prefixes \<tau>)" 
                     and "length \<tau>' \<le> m * n - 1"
      by blast

    then have "\<tau> \<noteq> \<tau>'"
      using \<open>length \<tau> > m*n-1\<close> by auto
    
    show False
      using \<open>(\<L>[L1,\<tau>], \<L>[L2,\<tau>]) = (\<L>[L1,\<tau>'],\<L>[L2,\<tau>'])\<close> 
      using no_prefix_loop[OF _ \<open>\<tau>' \<in> set (prefixes \<tau>)\<close> \<open>\<tau> \<noteq> \<tau>'\<close>] 
      by simp
  qed
  ultimately show False
    unfolding \<open>?visited_states = ?L12\<close> 
    by blast
qed


section \<open>Reductions Between Relations\<close>

subsection \<open>Quasi-Equivalence via Quasi-Reduction and Absences\<close>

fun absence_completion :: "'x alphabet \<Rightarrow> 'y alphabet \<Rightarrow> ('x,'y) language \<Rightarrow> ('x, 'y \<times> bool) language" where 
  "absence_completion X Y L = 
    ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L)
    \<union> {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"

lemma absence_completion_is_language : 
  assumes "is_language X Y L"
shows "is_language X (Y \<times> UNIV) (absence_completion X Y L)" 
proof -       
  let ?L = "(absence_completion X Y L)" 
  have "[] \<in> ?L" 
    using language_contains_nil[OF assms] by auto

  have "?L \<noteq> {}"
    using language_contains_nil[OF assms] by auto
  moreover have "\<And> \<gamma> xy . \<gamma> \<in> ?L \<Longrightarrow> xy \<in> set \<gamma> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> (Y \<times> UNIV)"
            and "\<And> \<gamma> \<gamma>' . \<gamma> \<in> ?L \<Longrightarrow> prefix \<gamma>' \<gamma> \<Longrightarrow> \<gamma>' \<in> ?L"
  proof -
    fix \<gamma> xy \<gamma>' assume "\<gamma> \<in> ?L" 
    then consider (a) "\<gamma> \<in> ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L)" | 
                  (b) "\<gamma> \<in> {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"
      unfolding absence_completion.simps by blast
    then have "(xy \<in> set \<gamma> \<longrightarrow> fst xy \<in> X \<and> snd xy \<in> (Y \<times> UNIV)) \<and> (prefix \<gamma>' \<gamma> \<longrightarrow> \<gamma>' \<in> ?L)"
    proof cases
      case a
      then obtain \<pi> where *:"\<gamma> = map (\<lambda>(x,y) . (x,(y,True))) \<pi>" and "\<pi> \<in> L"
        by auto
      then have p1: "\<And> xy . xy \<in> set \<pi> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> Y"
            and p2: "\<And> \<pi>' . prefix \<pi>' \<pi> \<Longrightarrow> \<pi>' \<in> L"
        using assms by auto

      have "xy \<in> set \<gamma> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> (Y \<times> UNIV)"
      proof -
        assume "xy \<in> set \<gamma>"
        then have "(fst xy, fst (snd xy)) \<in> set \<pi>" and "snd (snd xy) = True"
          unfolding * by auto
        then show "fst xy \<in> X \<and> snd xy \<in> (Y \<times> UNIV)"
          by (metis p1 SigmaI UNIV_I fst_conv prod.collapse snd_conv)  
      qed
      moreover have "prefix \<gamma>' \<gamma> \<Longrightarrow> \<gamma>' \<in> ?L" 
      proof -
        assume "prefix \<gamma>' \<gamma>" 
        then obtain i where "\<gamma>' = take i \<gamma>"
          by (metis append_eq_conv_conj prefix_def) 
        then have "\<gamma>' = map (\<lambda>(x,y) . (x,(y,True))) (take i \<pi>)"
          unfolding * using take_map by blast 
        moreover have "take i \<pi> \<in> L"
          using p2 \<open>\<pi> \<in> L\<close> take_is_prefix by blast 
        ultimately have "\<gamma>' \<in> ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L)"
          by simp
        then show "\<gamma>' \<in> ?L" 
          by auto
      qed
      ultimately show ?thesis by blast
    next
      case b
      then obtain \<pi> x y \<tau> where *: "\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau>"
                            and "\<pi> \<in> L" 
                            and "out[L,\<pi>,x] \<noteq> {}" 
                            and "y \<in> Y" 
                            and "y \<notin> out[L,\<pi>,x]" 
                            and "(\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)"
        by blast
      then have p1: "\<And> xy . xy \<in> set \<pi> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> Y"
            and p2: "\<And> \<pi>' . prefix \<pi>' \<pi> \<Longrightarrow> \<pi>' \<in> L"
        using assms by auto

      have "x \<in> X"
        using \<open>out[L,\<pi>,x] \<noteq> {}\<close> assms
        by (meson executable_inputs_in_alphabet outputs_executable) 

      have "xy \<in> set \<gamma> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> (Y \<times> UNIV)"
      proof -
        assume "xy \<in> set \<gamma>" 
        then consider (b1) "xy \<in> set (map (\<lambda>(x,y) . (x,(y,True))) \<pi>)" | 
                      (b2) "xy = (x,(y,False))" | 
                      (b3) "xy \<in> set \<tau>" 
          unfolding * by force
        then show ?thesis proof cases
          case b1
          then have "(fst xy, fst (snd xy)) \<in> set \<pi>" and "snd (snd xy) = True"
            unfolding * by auto
          then show "fst xy \<in> X \<and> snd xy \<in> (Y \<times> UNIV)"
            by (metis p1 SigmaI UNIV_I fst_conv prod.collapse snd_conv)
        next
          case b2
          then show ?thesis 
            using \<open>x \<in> X\<close> \<open>y \<in> Y\<close> by simp
        next
          case b3
          then show ?thesis 
            using \<open>(\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)\<close> by force
        qed
      qed
      moreover have "prefix \<gamma>' \<gamma> \<Longrightarrow> \<gamma>' \<in> ?L" 
      proof -
        assume "prefix \<gamma>' \<gamma>" 
        then obtain i where "\<gamma>' = take i \<gamma>"
          by (metis append_eq_conv_conj prefix_def)
        then consider (b1) "i \<le> length \<pi>" | 
                      (b2) "i > length \<pi>"
          by linarith
        then show "\<gamma>' \<in> ?L" proof cases
          case b1 
          then have "i \<le> length (map (\<lambda>(x, y). (x, y, True)) \<pi>)" 
            by auto
          then have "\<gamma>' = map (\<lambda>(x,y) . (x,(y,True))) (take i \<pi>)"
            unfolding * \<open>\<gamma>' = take i \<gamma>\<close>
            by (simp add: take_map) 
          moreover have "take i \<pi> \<in> L"
            using p2 \<open>\<pi> \<in> L\<close> take_is_prefix by blast 
          ultimately have "\<gamma>' \<in> ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L)"
            by simp
          then show "\<gamma>' \<in> ?L" 
            by auto
        next
          case b2 
          then have "i > length (map (\<lambda>(x, y). (x, y, True)) \<pi>)" 
            by auto

          have "\<And> k xs ys . k > length xs \<Longrightarrow> take k (xs@ys) = xs@(take (k - length xs) ys)"
            by simp 
          have take_helper: "\<And> k xs y zs . k > length xs \<Longrightarrow> take k (xs@[y]@zs) = xs@[y]@(take (k - length xs - 1) zs)"
            by (metis One_nat_def Suc_pred \<open>\<And>ys xs k. length xs < k \<Longrightarrow> take k (xs @ ys) = xs @ take (k - length xs) ys\<close> append_Cons append_Nil take_Suc_Cons zero_less_diff) 
          
          have **: "\<gamma>' = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@(take (i - length \<pi> - 1) \<tau>)"
            unfolding * \<open>\<gamma>' = take i \<gamma>\<close>
            using take_helper[OF \<open>i > length (map (\<lambda>(x, y). (x, y, True)) \<pi>)\<close>] by simp
          
          have "(\<forall> (x,(y,a)) \<in> set (take (i - length \<pi> - 1) \<tau>) . x \<in> X \<and> y \<in> Y)"
            using \<open>(\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)\<close>
            by (meson in_set_takeD) 
          then show ?thesis 
            unfolding ** absence_completion.simps
            using \<open>\<pi> \<in> L\<close> \<open>out[L,\<pi>,x] \<noteq> {}\<close> \<open>y \<in> Y\<close> \<open>y \<notin> out[L,\<pi>,x]\<close>
            by blast
        qed
      qed
      ultimately show ?thesis by simp
    qed
    then show "xy \<in> set \<gamma> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> (Y \<times> UNIV)"
          and "prefix \<gamma>' \<gamma> \<Longrightarrow> \<gamma>' \<in> ?L"
      by blast+
  qed
  ultimately show ?thesis
    unfolding is_language.simps by blast
qed

lemma absence_completion_inclusion_R : 
  assumes "is_language X Y L"
  and     "\<pi> \<in> absence_completion X Y L"
shows "(map (\<lambda>(x,y,a) . (x,y)) \<pi> \<in> L) \<longleftrightarrow> (\<forall> (x,y,a) \<in> set \<pi> . a = True)" 
proof -
  define L'a where "L'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L)"
  define L'b where "L'b = {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"
  

  have "\<And> \<pi> xya . \<pi> \<in> L'a \<Longrightarrow> xya \<in> set \<pi> \<Longrightarrow> snd (snd xya) = True" 
    unfolding L'a_def by auto
  moreover have "\<And> \<pi> . \<pi> \<in> L'b \<Longrightarrow> \<exists> xya \<in> set \<pi> . snd (snd xya) = False" 
    unfolding L'b_def by auto
  moreover have "\<pi> \<in> L'a \<union> L'b"
    using assms(2) unfolding absence_completion.simps L'a_def L'b_def .
  ultimately have "(\<forall> (x,y,a) \<in> set \<pi> . a = True) = (\<pi> \<in> L'a)" 
    by fastforce

  show ?thesis proof (cases "(\<forall> (x,y,a) \<in> set \<pi> . a = True)")
    case True 
    then obtain \<tau> where "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<tau>"
                    and "\<tau> \<in> L"
      unfolding \<open>(\<forall> (x,y,a) \<in> set \<pi> . a = True) = (\<pi> \<in> L'a)\<close> L'a_def
      by blast
    
    have "map (\<lambda>(x, y, a). (x, y)) \<pi> = \<tau>"
      unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<tau>\<close>
      by (induction \<tau>; auto)
    show ?thesis 
      using True \<open>\<tau> \<in> L\<close>
      unfolding \<open>(\<forall> (x,y,a) \<in> set \<pi> . a = True) = (\<pi> \<in> L'a)\<close> L'a_def
      unfolding \<open>map (\<lambda>(x, y, a). (x, y)) \<pi> = \<tau>\<close>
      unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<tau>\<close> 
      by blast
  next
    case False 
    then have "\<pi> \<in> L'b" 
      using \<open>(\<forall> (x,y,a) \<in> set \<pi> . a = True) = (\<pi> \<in> L'a)\<close> \<open>\<pi> \<in> L'a \<union> L'b\<close> by blast
    then obtain \<tau> x y \<tau>' where "\<pi> = (map (\<lambda>(x,y) . (x,(y,True))) \<tau>)@[(x,(y,False))]@\<tau>'"
                           and "\<tau> \<in> L" 
                           and "out[L,\<tau>,x] \<noteq> {}"
                           and "y \<in> Y" 
                           and "y \<notin> out[L,\<tau>,x]" 
                           and "(\<forall> (x,(y,a)) \<in> set \<tau>' . x \<in> X \<and> y \<in> Y)"
      unfolding L'b_def by blast
    then have "\<tau>@[(x,y)] \<notin> L"
      by fastforce 
    then have "\<tau>@[(x,y)]@(map (\<lambda>(x, y, a). (x, y)) \<tau>') \<notin> L"
      using assms(1)
      by (metis append.assoc prefix_closure_no_member) 
    moreover have "map (\<lambda>(x, y, a). (x, y)) \<pi> = \<tau>@[(x,y)]@(map (\<lambda>(x, y, a). (x, y)) \<tau>')" 
      unfolding \<open>\<pi> = (map (\<lambda>(x,y) . (x,(y,True))) \<tau>)@[(x,(y,False))]@\<tau>'\<close> 
      by (induction \<tau>; auto)
    ultimately have "map (\<lambda>(x, y, a). (x, y)) \<pi> \<notin> L"
      by simp
    then show ?thesis
      using False by blast
  qed
qed

lemma absence_completion_inclusion_L : 
  "(\<pi> \<in> L) \<longleftrightarrow> (map (\<lambda>(x,y) . (x,y,True)) \<pi> \<in> absence_completion X Y L)" 
proof -

  let ?L = "absence_completion X Y L"
  define L'a where "L'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L)"
  define L'b where "L'b = {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"
  have "?L = L'a \<union> L'b" 
    unfolding L'a_def L'b_def absence_completion.simps by blast

  have "\<And> \<pi> . \<pi> \<in> L'b \<Longrightarrow> \<exists> xya \<in> set \<pi> . snd (snd xya) = False" 
    unfolding L'b_def by auto
  then have "(map (\<lambda>(x,y) . (x,y,True)) \<pi> \<in> ?L) = (map (\<lambda>(x,y) . (x,y,True)) \<pi> \<in> L'a)"
    unfolding \<open>?L = L'a \<union> L'b\<close>
    by fastforce 

  have "inj (\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>)"
    by (simp add: inj_def) 
  then show ?thesis 
    unfolding \<open>(map (\<lambda>(x,y) . (x,y,True)) \<pi> \<in> ?L) = (map (\<lambda>(x,y) . (x,y,True)) \<pi> \<in> L'a)\<close>
    unfolding L'a_def
    by (simp add: image_iff inj_def) 
qed


fun is_present :: "('x,'y \<times> bool) word \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where
  "is_present \<pi> L = (\<pi> \<in> map (\<lambda>(x, y). (x, y, True)) ` L)"

lemma is_present_rev :
  assumes "is_present \<pi> L" 
shows "map (\<lambda>(x, y, a). (x, y)) \<pi> \<in> L"
proof -
  obtain \<pi>' where "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'" and "\<pi>' \<in> L"
    using assms by auto
  moreover have "map (\<lambda>(x, y, a). (x, y)) (map (\<lambda>(x, y). (x, y, True)) \<pi>') = \<pi>'"
    by (induction \<pi>'; auto)
  ultimately show ?thesis
    by force
qed



lemma absence_completion_out : 
  assumes "is_language X Y L"
  and     "x \<in> X"
  and     "\<pi> \<in> absence_completion X Y L"
shows "is_present \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {} \<Longrightarrow> out[absence_completion X Y L, \<pi>, x] = {(y,True) | y . y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]} \<union> {(y,False) | y . y \<in> Y \<and> y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
and   "is_present \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] = {} \<Longrightarrow> out[absence_completion X Y L, \<pi>, x] = {}"
and   "\<not> is_present \<pi> L \<Longrightarrow> out[absence_completion X Y L, \<pi>, x] = Y \<times> UNIV"
proof -

  let ?L = "absence_completion X Y L"
  define L'a where "L'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L)"
  define L'b where "L'b = {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"
  have "?L = L'a \<union> L'b" 
    unfolding L'a_def L'b_def absence_completion.simps by blast
  then have "out[?L, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}"
    unfolding outputs.simps language_for_state.simps by blast

  show "is_present \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {} \<Longrightarrow> out[?L, \<pi>, x] = {(y,True) | y . y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]} \<union> {(y,False) | y . y \<in> Y \<and> y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
  proof - 
    assume "is_present \<pi> L" and "out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {}"
    then have "map (\<lambda>(x, y, a). (x, y)) \<pi> \<in> L" 
      using assms(1) by auto 

    have "{y. \<pi> @ [(x, y)] \<in> L'a} = {(y,True) | y . y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}" 
    proof 
      show "{y. \<pi> @ [(x, y)] \<in> L'a} \<subseteq> {(y, True) |y. y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
      proof 
        fix ya assume "ya \<in> {y. \<pi> @ [(x, y)] \<in> L'a}"
        then have "\<pi> @ [(x, ya)] \<in> map (\<lambda>(x, y). (x, y, True)) ` L"
          unfolding L'a_def by blast
        then obtain \<gamma> where "\<gamma> \<in> L" and "\<pi> @ [(x, ya)] = map (\<lambda>(x, y). (x, y, True)) \<gamma>"
          by blast
        then have "length (\<pi> @ [(x, ya)]) = length \<gamma>"
          by auto
        then obtain \<gamma>' xy where "\<gamma> = \<gamma>'@[xy]"
          by (metis add.right_neutral dual_order.strict_iff_not length_append_singleton less_add_Suc2 rev_exhaust take0 take_all_iff)
        then have "(x,ya) = (\<lambda>(x, y). (x, y, True)) xy"
          using \<open>\<pi> @ [(x, ya)] = map (\<lambda>(x, y). (x, y, True)) \<gamma>\<close> unfolding \<open>\<gamma> = \<gamma>'@[xy]\<close> by auto
        then have "ya = (snd xy, True)" and "xy = (x,snd xy)"
          by (simp add: split_beta)+
        moreover define y where "y = snd xy"
        ultimately have "ya = (y, True)" and "xy = (x,y)"
          by auto

        have "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<gamma>'"
          using \<open>\<pi> @ [(x, ya)] = map (\<lambda>(x, y). (x, y, True)) \<gamma>\<close> unfolding \<open>\<gamma> = \<gamma>'@[xy]\<close> by auto
        then have "map (\<lambda>(x, y, a). (x, y)) \<pi> = \<gamma>'" 
          by (induction \<pi> arbitrary: \<gamma>'; auto)
          
        have "[(x, y)] \<in> {\<tau>. map (\<lambda>(x, y, a). (x, y)) \<pi> @ \<tau> \<in> L}"
          using \<open>\<gamma> \<in> L\<close> 
          unfolding \<open>\<gamma> = \<gamma>'@[xy]\<close> \<open>ya = (y, True)\<close> \<open>xy = (x,y)\<close> 
          unfolding \<open>map (\<lambda>(x, y, a). (x, y)) \<pi> = \<gamma>'\<close> 
          by auto
        then show "ya \<in> {(y, True) |y. y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
          unfolding \<open>ya = (snd xy, True)\<close> outputs.simps language_for_state.simps 
          unfolding \<open>ya = (y, True)\<close> \<open>xy = (x,y)\<close> \<open>map (\<lambda>(x, y, a). (x, y)) \<pi> = \<gamma>'\<close> 
          by auto
      qed
      show "{(y, True) |y. y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]} \<subseteq> {y. \<pi> @ [(x, y)] \<in> L'a}" 
      proof 
        fix ya assume "ya \<in> {(y, True) |y. y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
        then obtain y where "ya = (y,True)" and "y \<in> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]"
          by blast
        then have "[(x, y)] \<in> {\<tau>. map (\<lambda>(x, y, a). (x, y)) \<pi> @ \<tau> \<in> L}"
          unfolding outputs.simps language_for_state.simps by auto
        then have "(map (\<lambda>(x, y, a). (x, y)) \<pi>) @ [(x,y)] \<in> L"
          by auto
        moreover have "map (\<lambda>(x, y). (x, y, True)) ((map (\<lambda>(x, y, a). (x, y)) \<pi>) @ [(x,y)]) = \<pi> @ [(x, (y, True))]"
          using \<open>is_present \<pi> L\<close> unfolding is_present.simps 
          by (induction \<pi> arbitrary: x y; auto)
        ultimately have "\<pi> @ [(x, (y, True))] \<in> L'a" 
          unfolding L'a_def
          by force 
        then show "ya \<in> {y. \<pi> @ [(x, y)] \<in> L'a}"
          unfolding \<open>ya = (y,True)\<close>
          by blast
      qed
    qed
    moreover have "{y. \<pi> @ [(x, y)] \<in> L'b} = {(y,False) | y . y \<in> Y \<and> y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
    proof 
      show "{y. \<pi> @ [(x, y)] \<in> L'b} \<subseteq> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
      proof 
        fix ya assume "ya \<in> {y. \<pi> @ [(x, y)] \<in> L'b}"
        then have "\<pi> @ [(x,ya)] \<in> L'b"
          by auto
        then obtain \<pi>' x' y' \<tau> where "\<pi> @ [(x,ya)]  = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ \<tau>"
                                 and "\<pi>' \<in> L" 
                                 and "out[L,\<pi>',x'] \<noteq> {}" 
                                 and "y' \<in> Y" 
                                 and "y' \<notin> out[L,\<pi>',x']" 
                                 and "(\<forall>(x, y, a)\<in>set \<tau>. x \<in> X \<and> y \<in> Y)"
          unfolding L'b_def by blast

        obtain \<pi>'' where "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>''" and "\<pi>'' \<in> L"
          using \<open>is_present \<pi> L\<close> by auto
        then have "\<And> xya . xya \<in> set \<pi> \<Longrightarrow> snd (snd xya) = True"
          by (induction \<pi>; auto) 

        have "\<tau> = []"
        proof (rule ccontr)
          assume "\<tau> \<noteq> []"
          then obtain \<tau>' xyz where "\<tau> = \<tau>'@[xyz]"
            by (metis append_butlast_last_id)
          then have "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ \<tau>'"
            using \<open>\<pi> @ [(x,ya)]  = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ \<tau>\<close>
            by auto
          then have "(x', y', False) \<in> set \<pi>"
            by auto
          then show False 
            using \<open>\<And> xya . xya \<in> set \<pi> \<Longrightarrow> snd (snd xya) = True\<close> by force
        qed
        then have "x' = x" and "ya = (y', False)" and "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'"
          using \<open>\<pi> @ [(x,ya)]  = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ \<tau>\<close>
          by auto

        have *: "map (\<lambda>(x, y, a). (x, y)) (map (\<lambda>(x, y). (x, y, True)) \<pi>') = \<pi>'"
          by (induction \<pi>'; auto)

        have "y' \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]"
          using \<open>y' \<notin> out[L,\<pi>',x']\<close> 
          unfolding outputs.simps language_for_state.simps 
          unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close> \<open>x' = x\<close>
          unfolding * .
        then show "ya \<in> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}" 
          using \<open>y' \<in> Y\<close>
          unfolding \<open>ya = (y', False)\<close> by auto
      qed

      show "{(y, False) |y. y \<in> Y \<and> y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]} \<subseteq> {y. \<pi> @ [(x, y)] \<in> L'b}"
      proof 
        fix ya assume "ya \<in> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]}"
        then obtain y where "ya = (y,False)"
                        and "y \<in> Y"
                        and "y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]"
          by blast

        obtain \<pi>' where "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'" and "\<pi>' \<in> L"
          using \<open>is_present \<pi> L\<close> by auto
        have *: "map (\<lambda>(x, y, a). (x, y)) (map (\<lambda>(x, y). (x, y, True)) \<pi>') = \<pi>'"
          by (induction \<pi>'; auto)
        have "out[L,\<pi>',x] \<noteq> {}" 
          using \<open>out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {}\<close> 
          unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close> * .
        have "y \<notin> out[L,\<pi>',x]"
          using \<open>y \<notin> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]\<close>
          unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close> * .

        have "\<pi>@[(x,ya)] = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x, y, False)]"
          unfolding \<open>ya = (y,False)\<close> \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close>
          by auto
        then show "ya \<in> {y. \<pi> @ [(x, y)] \<in> L'b}"
          unfolding L'b_def 
          using \<open>\<pi>' \<in> L\<close> \<open>out[L,\<pi>',x] \<noteq> {}\<close> \<open>y \<in> Y\<close> \<open>y \<notin> out[L,\<pi>',x]\<close> 
          by force
      qed
    qed
    ultimately show ?thesis
      unfolding \<open>out[?L, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> 
      by blast
  qed


  show "is_present \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] = {} \<Longrightarrow> out[absence_completion X Y L, \<pi>, x] = {}"
  proof - 
    assume "is_present \<pi> L" and "out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] = {}"

    obtain \<pi>' where "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'" and "\<pi>' \<in> L"
      using \<open>is_present \<pi> L\<close> by auto
    have *: "map (\<lambda>(x, y, a). (x, y)) (map (\<lambda>(x, y). (x, y, True)) \<pi>') = \<pi>'"
      by (induction \<pi>'; auto)
    then have "map (\<lambda>(x, y, a). (x, y)) \<pi> = \<pi>'"
      using \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close> by blast 

    have "{y. \<pi> @ [(x, y)] \<in> L'a} = {}" 
    proof -
      have "\<nexists> y . \<pi> @ [(x, y)] \<in> L'a"
      proof 
        assume "\<exists>y. \<pi> @ [(x, y)] \<in> L'a"
        then obtain ya where "\<pi> @ [(x, ya)] \<in> L'a" 
          by blast        
        then obtain \<pi>'' where "\<pi>'' \<in> L" and "map (\<lambda>(x, y). (x, y, True)) \<pi>'' = \<pi> @ [(x, ya)]"
          unfolding L'a_def by force
        then have "(x,ya) = (\<lambda>(x, y). (x, y, True)) (last \<pi>'')"
          by (metis (mono_tags, lifting) append_is_Nil_conv last_map last_snoc list.map_disc_iff not_Cons_self2) 
        then obtain y where "ya = (y,True)"
          by (simp add: split_beta)
  
        have "map (\<lambda>(x, y). (x, y, True)) \<pi>'' = map (\<lambda>(x, y). (x, y, True)) (\<pi>' @ [(x, y)])"
          using \<open>map (\<lambda>(x, y). (x, y, True)) \<pi>'' = \<pi> @ [(x, ya)]\<close>
          unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close> \<open>ya = (y,True)\<close> by auto
        moreover have "inj (\<lambda>(x, y). (x, y, True))"
          by (simp add: inj_def) 
        ultimately have "\<pi>'' = \<pi>' @ [(x,y)]"
          using inj_map_eq_map by blast
  
        show False
          using \<open>\<pi>'' \<in> L\<close> \<open>out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] = {}\<close>
          unfolding \<open>map (\<lambda>(x, y, a). (x, y)) \<pi> = \<pi>'\<close> \<open>\<pi>'' = \<pi>' @ [(x,y)]\<close>
          by simp 
      qed
      then show ?thesis 
        by blast
    qed 
    moreover have "{y. \<pi> @ [(x, y)] \<in> L'b} = {}"  
    proof -
      have "\<nexists> y . \<pi> @ [(x, y)] \<in> L'b"
      proof 
        assume "\<exists>y. \<pi> @ [(x, y)] \<in> L'b"
        then obtain ya where "\<pi> @ [(x, ya)] \<in> L'b" 
          by blast    
        then obtain \<pi>'' x' y' \<tau> where "\<pi> @ [(x,ya)]  = map (\<lambda>(x, y). (x, y, True)) \<pi>'' @ [(x', y', False)] @ \<tau>"
                                  and "\<pi>'' \<in> L" 
                                  and "out[L,\<pi>'',x'] \<noteq> {}" 
                                  and "y' \<in> Y" 
                                  and "y' \<notin> out[L,\<pi>'',x']" 
                                  and "(\<forall>(x, y, a)\<in>set \<tau>. x \<in> X \<and> y \<in> Y)"
          unfolding L'b_def by blast

        have "\<And> xya . xya \<in> set \<pi> \<Longrightarrow> snd (snd xya) = True"
          using \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close>
          by (induction \<pi>; auto) 

        have "\<tau> = []"
        proof (rule ccontr)
          assume "\<tau> \<noteq> []"
          then obtain \<tau>' xyz where "\<tau> = \<tau>'@[xyz]"
            by (metis append_butlast_last_id)
          then have "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'' @ [(x', y', False)] @ \<tau>'"
            using \<open>\<pi> @ [(x,ya)]  = map (\<lambda>(x, y). (x, y, True)) \<pi>'' @ [(x', y', False)] @ \<tau>\<close>
            by auto
          then have "(x', y', False) \<in> set \<pi>"
            by auto
          then show False 
            using \<open>\<And> xya . xya \<in> set \<pi> \<Longrightarrow> snd (snd xya) = True\<close> by force
        qed
        then have "x' = x" and "ya = (y', False)" and "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>''"
          using \<open>\<pi> @ [(x,ya)]  = map (\<lambda>(x, y). (x, y, True)) \<pi>'' @ [(x', y', False)] @ \<tau>\<close>
          by auto
        moreover have "inj (\<lambda>(x, y). (x, y, True))"
          by (simp add: inj_def) 
        ultimately have "\<pi>'' = \<pi>'"
          unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>'\<close>
          using map_injective by blast
        then show False 
          using \<open>out[L,\<pi>'',x'] \<noteq> {}\<close> \<open>out[L,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] = {}\<close>
          unfolding \<open>map (\<lambda>(x, y, a). (x, y)) \<pi> = \<pi>'\<close> \<open>x' = x\<close>
          by blast
      qed
      then show ?thesis 
        by blast
    qed
    ultimately show ?thesis
      unfolding \<open>out[?L, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> 
      by blast
  qed

  show "\<not> is_present \<pi> L \<Longrightarrow> out[absence_completion X Y L,\<pi>,x] = Y \<times> UNIV" 
  proof 

    show "out[absence_completion X Y L,\<pi>,x] \<subseteq> Y \<times> UNIV"
      using absence_completion_is_language[OF assms(1)]
      by (meson outputs_in_alphabet)



    assume "\<not> is_present \<pi> L" 
    then have "\<pi> \<notin> L'a"
      unfolding L'a_def by auto
    then have "\<pi> \<in> L'b" 
      using \<open>\<pi> \<in> ?L\<close> \<open>?L = L'a \<union> L'b\<close> by blast
    then obtain \<pi>' x' y' \<tau> where "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ \<tau>"
                             and "\<pi>' \<in> L" 
                             and "out[L,\<pi>',x'] \<noteq> {}" 
                             and "y' \<in> Y" 
                             and "y' \<notin> out[L,\<pi>',x']" 
                             and "(\<forall>(x, y, a)\<in>set \<tau>. x \<in> X \<and> y \<in> Y)"
      unfolding L'b_def by blast

    show "Y \<times> UNIV \<subseteq> out[absence_completion X Y L,\<pi>,x]"
    proof 
      fix ya assume "ya \<in> Y \<times> (UNIV :: bool set)"

      have "\<pi>@[(x,ya)] = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ (\<tau> @ [(x,ya)])"
        using \<open>\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ \<tau>\<close>
        by auto
      moreover have \<open>(\<forall>(x, y, a)\<in>set (\<tau> @ [(x,ya)]) . x \<in> X \<and> y \<in> Y)\<close>
        using \<open>(\<forall>(x, y, a)\<in>set \<tau>. x \<in> X \<and> y \<in> Y)\<close> \<open>x \<in> X\<close> \<open>ya \<in> Y \<times> (UNIV :: bool set)\<close>
        by auto
      ultimately have "\<pi>@[(x,ya)] \<in> L'b"
        unfolding L'b_def
        using \<open>\<pi>' \<in> L\<close> \<open>out[L,\<pi>',x'] \<noteq> {}\<close> \<open>y' \<in> Y\<close> \<open>y' \<notin> out[L,\<pi>',x']\<close>
        by blast
      then show "ya \<in> out[?L,\<pi>,x]"
        unfolding \<open>out[?L, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> 
        by blast
    qed
  qed
qed

    

theorem quasieq_via_quasired : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(L1 \<preceq>[X,quasieq Y] L2) \<longleftrightarrow> ((absence_completion X Y L1) \<preceq>[X, quasired (Y \<times> UNIV)] (absence_completion X Y L2))"
proof 

  define L1' where "L1' = absence_completion X Y L1"
  define L2' where "L2' = absence_completion X Y L2"

  define L1'a where "L1'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L1)"
  define L1'b where "L1'b = {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L1 \<and> out[L1,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L1,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"
  define L2'a where "L2'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` L2)"
  define L2'b where "L2'b = {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L2 \<and> out[L2,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L2,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"

  

  have "\<And> \<pi> xya . \<pi> \<in> L1'a \<Longrightarrow> xya \<in> set \<pi> \<Longrightarrow> snd (snd xya) = True" 
    unfolding L1'a_def by auto
  moreover have "\<And> \<pi> xya . \<pi> \<in> L2'a \<Longrightarrow> xya \<in> set \<pi> \<Longrightarrow> snd (snd xya) = True" 
    unfolding L2'a_def by auto
  moreover have "\<And> \<pi> . \<pi> \<in> L1'b \<Longrightarrow> \<exists> xya \<in> set \<pi> . snd (snd xya) = False" 
    unfolding L1'b_def by auto
  moreover have "\<And> \<pi> . \<pi> \<in> L2'b \<Longrightarrow> \<exists> xya \<in> set \<pi> . snd (snd xya) = False" 
    unfolding L2'b_def by auto
  ultimately have "L1'a \<inter> L2'b = {}" and "L1'b \<inter> L2'a = {}"
    by blast+
  moreover have "L1' = L1'a \<union> L1'b" 
    unfolding L1'_def L1'a_def L1'b_def by auto
  moreover have "L2' = L2'a \<union> L2'b" 
    unfolding L2'_def L2'a_def L2'b_def by auto
  ultimately have "L1' \<inter> L2' = (L1'a \<inter> L2'a) \<union> (L1'b \<inter> L2'b)"
    by blast

  have "inj (\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>)"
    by (simp add: inj_def) 
  then have "L1'a \<inter> L2'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` (L1 \<inter> L2))" 
    unfolding L1'a_def L2'a_def
    using image_Int by blast 

  have intersection_b: "L1'b \<inter> L2'b = {(map (\<lambda>(x,y) . (x,(y,True))) \<pi>)@[(x,(y,False))]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L1 \<inter> L2 \<and> out[L1,\<pi>,x] \<noteq> {} \<and> out[L2,\<pi>,x] \<noteq> {} \<and> y \<in> Y \<and> y \<notin> out[L1,\<pi>,x] \<and> y \<notin> out[L2,\<pi>,x] \<and> (\<forall> (x,(y,a)) \<in> set \<tau> . x \<in> X \<and> y \<in> Y)}"
    (is "L1'b \<inter> L2'b = ?L12'b")
  proof 
    show "?L12'b \<subseteq> L1'b \<inter> L2'b" 
      unfolding L1'b_def L2'b_def by blast
    show "L1'b \<inter> L2'b \<subseteq> ?L12'b" 
    proof 
      fix \<gamma> assume "\<gamma> \<in> L1'b \<inter> L2'b"
      
      obtain \<pi>1 x1 y1 \<tau>1 where "\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>1)@[(x1,(y1,False))]@\<tau>1" 
                           and "\<pi>1 \<in> L1" 
                           and "out[L1,\<pi>1,x1] \<noteq> {}" 
                           and "y1 \<in> Y" 
                           and "y1 \<notin> out[L1,\<pi>1,x1]" 
                           and "(\<forall> (x,(y,a)) \<in> set \<tau>1 . x \<in> X \<and> y \<in> Y)"
        using \<open>\<gamma> \<in> L1'b \<inter> L2'b\<close> unfolding L1'b_def by blast

      obtain \<pi>2 x2 y2 \<tau>2 where "\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2)@[(x2,(y2,False))]@\<tau>2" 
                           and "\<pi>2 \<in> L2" 
                           and "out[L2,\<pi>2,x2] \<noteq> {}" 
                           and "y2 \<in> Y" 
                           and "y2 \<notin> out[L2,\<pi>2,x2]" 
                           and "(\<forall> (x,(y,a)) \<in> set \<tau>2 . x \<in> X \<and> y \<in> Y)"
        using \<open>\<gamma> \<in> L1'b \<inter> L2'b\<close> unfolding L2'b_def by blast

      have "\<And> i . i < length \<pi>1 \<Longrightarrow> snd (snd (\<gamma> ! i)) = True" 
      proof - 
        fix i assume "i < length \<pi>1" 
        then have "i < length (map (\<lambda>(x,y) . (x,(y,True))) \<pi>1)" by auto 
        then have "\<gamma> ! i = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>1) ! i" 
          unfolding \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>1)@[(x1,(y1,False))]@\<tau>1\<close>
          by (simp add: nth_append) 
        also have "\<dots> = (\<lambda>(x,y) . (x,(y,True))) (\<pi>1 ! i)"
          using \<open>i < length \<pi>1\<close> nth_map by blast 
        finally show "snd (snd (\<gamma> ! i)) = True"
          by (metis (no_types, lifting) case_prod_conv old.prod.exhaust snd_conv) 
      qed
      have "\<gamma> ! length \<pi>1 = (x1,(y1,False))"
        unfolding \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>1)@[(x1,(y1,False))]@\<tau>1\<close>
        by (metis append_Cons length_map nth_append_length)
      have "\<And> i . i < length \<pi>2 \<Longrightarrow> snd (snd (\<gamma> ! i)) = True" 
      proof - 
        fix i assume "i < length \<pi>2" 
        then have "i < length (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2)" by auto 
        then have "\<gamma> ! i = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2) ! i" 
          unfolding \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2)@[(x2,(y2,False))]@\<tau>2\<close>
          by (simp add: nth_append) 
        also have "\<dots> = (\<lambda>(x,y) . (x,(y,True))) (\<pi>2 ! i)"
          using \<open>i < length \<pi>2\<close> nth_map by blast 
        finally show "snd (snd (\<gamma> ! i)) = True"
          by (metis (no_types, lifting) case_prod_conv old.prod.exhaust snd_conv) 
      qed
      have "\<gamma> ! length \<pi>2 = (x2,(y2,False))"
        unfolding \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2)@[(x2,(y2,False))]@\<tau>2\<close>
        by (metis append_Cons length_map nth_append_length)

      have "length \<pi>1 = length \<pi>2"
        by (metis \<open>\<And>i. i < length \<pi>1 \<Longrightarrow> snd (snd (\<gamma> ! i)) = True\<close> \<open>\<And>i. i < length \<pi>2 \<Longrightarrow> snd (snd (\<gamma> ! i)) = True\<close> \<open>\<gamma> ! length \<pi>1 = (x1, y1, False)\<close> \<open>\<gamma> ! length \<pi>2 = (x2, y2, False)\<close> not_less_iff_gr_or_eq snd_conv) 
      then have "\<pi>1 = \<pi>2"  
        using \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>1)@[(x1,(y1,False))]@\<tau>1\<close> \<open>inj (\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>)\<close>
        unfolding \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2)@[(x2,(y2,False))]@\<tau>2\<close>
        using map_injective by fastforce 
      then have "[(x1,(y1,False))]@\<tau>1 = [(x2,(y2,False))]@\<tau>2"
        using \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>1)@[(x1,(y1,False))]@\<tau>1\<close>
        unfolding \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2)@[(x2,(y2,False))]@\<tau>2\<close>
        by force
      then have "x1 = x2" and "y1 = y2" and "\<tau>1 = \<tau>2"
        by auto

      show "\<gamma> \<in> ?L12'b"
        using \<open>\<pi>1 \<in> L1\<close> \<open>out[L1,\<pi>1,x1] \<noteq> {}\<close> \<open>y1 \<in> Y\<close> \<open>y1 \<notin> out[L1,\<pi>1,x1]\<close> \<open>(\<forall> (x,(y,a)) \<in> set \<tau>1 . x \<in> X \<and> y \<in> Y)\<close>
        using \<open>\<pi>2 \<in> L2\<close> \<open>out[L2,\<pi>2,x2] \<noteq> {}\<close> \<open>y2 \<in> Y\<close> \<open>y2 \<notin> out[L2,\<pi>2,x2]\<close> \<open>(\<forall> (x,(y,a)) \<in> set \<tau>2 . x \<in> X \<and> y \<in> Y)\<close> 
        unfolding \<open>\<pi>1 = \<pi>2\<close> \<open>x1 = x2\<close> \<open>y1 = y2\<close> \<open>\<tau>1 = \<tau>2\<close> \<open>\<gamma> = (map (\<lambda>(x,y) . (x,(y,True))) \<pi>2)@[(x2,(y2,False))]@\<tau>2\<close>
        by blast
    qed
  qed
  

  have "is_language X (Y \<times> UNIV) L1'"
    using absence_completion_is_language[OF assms(1)] unfolding L1'_def .
  have "is_language X (Y \<times> UNIV) L2'"
    using absence_completion_is_language[OF assms(2)] unfolding L2'_def .

  have "(L1 \<preceq>[X,quasieq Y] L2) = quasi_equivalence L1 L2"
    using quasieq_type_1[OF assms] by blast

  have "(L1' \<preceq>[X,quasired (Y \<times> UNIV)] L2') = quasi_reduction L1' L2'"
    using quasired_type_1[OF \<open>is_language X (Y \<times> UNIV) L1'\<close> \<open>is_language X (Y \<times> UNIV) L2'\<close>] by blast

  have "\<And> \<pi> x . quasi_equivalence L1 L2 \<Longrightarrow> \<pi> \<in> L1' \<inter> L2' \<Longrightarrow> x \<in> exec[L2',\<pi>] \<Longrightarrow> (out[L1',\<pi>,x] \<noteq> {} \<and> out[L1',\<pi>,x] \<subseteq> out[L2',\<pi>,x])"
  proof -
    fix \<pi> x assume "quasi_equivalence L1 L2" and "\<pi> \<in> L1' \<inter> L2'" and "x \<in> exec[L2',\<pi>]"

    have "x \<in> X"
      using \<open>x \<in> exec[L2',\<pi>]\<close> absence_completion_is_language[OF assms(2)]
      by (metis L2'_def executable_inputs_in_alphabet)
    have "\<pi> \<in> absence_completion X Y L1" and "\<pi> \<in> absence_completion X Y L2"
      using \<open>\<pi> \<in> L1' \<inter> L2'\<close> unfolding L1'_def L2'_def by blast+

    consider (a) "\<pi> \<in> L1'a \<inter> L2'a" | (b) "\<pi> \<in> (L1'b \<inter> L2'b) - (L1'a \<inter> L2'a)"
      using \<open>\<pi> \<in> L1' \<inter> L2'\<close> \<open>L1' \<inter> L2' = (L1'a \<inter> L2'a) \<union> (L1'b \<inter> L2'b)\<close> by blast
    then show "(out[L1',\<pi>,x] \<noteq> {} \<and> out[L1',\<pi>,x] \<subseteq> out[L2',\<pi>,x])"
    proof cases
      case a
      then obtain \<tau> where "\<tau> \<in> L1 \<inter> L2"
                      and "\<pi> = map (\<lambda>(x,y) . (x,(y,True))) \<tau>"
        using \<open>L1'a \<inter> L2'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,(y,True))) \<pi>) ` (L1 \<inter> L2))\<close> by blast
      
      have "map (\<lambda>(x, y, a). (x, y)) \<pi> = \<tau>"
        unfolding \<open>\<pi> = map (\<lambda>(x,y) . (x,(y,True))) \<tau>\<close> by (induction \<tau>; auto)

      have "is_present \<pi> L1" and "is_present \<pi> L2"
        using \<open>\<tau> \<in> L1 \<inter> L2\<close> unfolding \<open>\<pi> = map (\<lambda>(x,y) . (x,(y,True))) \<tau>\<close> by auto

      have "out[L2,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {}"
        using \<open>x \<in> exec[L2',\<pi>]\<close>
        using absence_completion_out(2)[OF assms(2) \<open>x \<in> X\<close> \<open>\<pi> \<in> absence_completion X Y L2\<close> \<open>is_present \<pi> L2\<close>]
        unfolding L2'_def[symmetric]
        by (meson outputs_executable)  
      then have "x \<in> exec[L2,map (\<lambda>(x, y, a). (x, y)) \<pi>]"
        by auto
      then have "out[L1,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {}" and "out[L1,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] = out[L2,map (\<lambda>(x, y, a). (x, y)) \<pi>,x]"
        using \<open>quasi_equivalence L1 L2\<close> \<open>\<tau> \<in> L1 \<inter> L2\<close>
        unfolding quasi_equivalence_def \<open>map (\<lambda>(x, y, a). (x, y)) \<pi> = \<tau>\<close> by force+
      
      have "out[L1',\<pi>,x] = out[L2',\<pi>,x]"
        unfolding L1'_def L2'_def 
        unfolding absence_completion_out(1)[OF assms(2) \<open>x \<in> X\<close> \<open>\<pi> \<in> absence_completion X Y L2\<close> \<open>is_present \<pi> L2\<close> \<open>out[L2,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {}\<close>]
        unfolding absence_completion_out(1)[OF assms(1) \<open>x \<in> X\<close> \<open>\<pi> \<in> absence_completion X Y L1\<close> \<open>is_present \<pi> L1\<close> \<open>out[L1,map (\<lambda>(x, y, a). (x, y)) \<pi>,x] \<noteq> {}\<close>]
        using \<open>quasi_equivalence L1 L2\<close> \<open>\<tau> \<in> L1 \<inter> L2\<close> \<open>x \<in> exec[L2,map (\<lambda>(x, y, a). (x, y)) \<pi>]\<close>
        unfolding quasi_equivalence_def 
        unfolding \<open>map (\<lambda>(x, y, a). (x, y)) \<pi> = \<tau>\<close>
        by blast
      then show ?thesis
        by (metis \<open>x \<in> exec[L2',\<pi>]\<close> dual_order.refl outputs_executable) 
    next
      case b

      then obtain \<pi>' x' y' \<tau>' where "\<pi> = map (\<lambda>(x, y). (x, y, True)) \<pi>' @ [(x', y', False)] @ \<tau>'"
                                and "\<pi>' \<in> L1 \<inter> L2"
                                and "out[L1,\<pi>',x'] \<noteq> {}"
                                and "out[L2,\<pi>',x'] \<noteq> {}" 
                                and "y' \<in> Y" 
                                and "y' \<notin> out[L1,\<pi>',x']" 
                                and "y' \<notin> out[L2,\<pi>',x']" 
                                and "(\<forall>(x, y, a)\<in>set \<tau>'. x \<in> X \<and> y \<in> Y)"
        unfolding intersection_b 
        by blast

      have "\<not> is_present \<pi> L1"
        using \<open>L1'a \<equiv> map (\<lambda>(x, y). (x, y, True)) ` L1\<close> \<open>L1'a \<inter> L2'b = {}\<close> b by auto

      have "\<not> is_present \<pi> L2"
        using \<open>L2'a \<equiv> map (\<lambda>(x, y). (x, y, True)) ` L2\<close> \<open>L1'b \<inter> L2'a = {}\<close> b by auto

      show ?thesis 
        unfolding L1'_def L2'_def
        unfolding absence_completion_out(3)[OF assms(1) \<open>x \<in> X\<close> \<open>\<pi> \<in> absence_completion X Y L1\<close> \<open>\<not> is_present \<pi> L1\<close>]
        unfolding absence_completion_out(3)[OF assms(2) \<open>x \<in> X\<close> \<open>\<pi> \<in> absence_completion X Y L2\<close> \<open>\<not> is_present \<pi> L2\<close>]
        using \<open>y' \<in> Y\<close>
        by blast
    qed
  qed
  then show "L1 \<preceq>[X,quasieq Y] L2 \<Longrightarrow> (absence_completion X Y L1) \<preceq>[X,quasired (Y \<times> UNIV)] (absence_completion X Y L2)"
    unfolding L1'_def[symmetric] L2'_def[symmetric] 
    unfolding \<open>(L1' \<preceq>[X,quasired (Y \<times> UNIV)] L2') = quasi_reduction L1' L2'\<close>
    unfolding \<open>(L1 \<preceq>[X,quasieq Y] L2) = quasi_equivalence L1 L2\<close>
    unfolding quasi_reduction_def 
    by blast


  have "\<And> \<pi> x . quasi_reduction L1' L2' \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> exec[L2,\<pi>] \<Longrightarrow> out[L1,\<pi>,x] = out[L2,\<pi>,x]"
  proof -
    fix \<pi> x assume "quasi_reduction L1' L2'" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> exec[L2,\<pi>]"
    then have "x \<in> X"
      by (meson assms(2) executable_inputs_in_alphabet)

    let ?\<pi> = "map (\<lambda>(x, y). (x, y, True)) \<pi>"
    have "map (\<lambda>(x, y, a). (x, y)) ?\<pi> = \<pi>"
      by (induction \<pi>; auto)
    then have "out[L2,map (\<lambda>(x, y, a). (x, y)) ?\<pi>,x] \<noteq> {}"
      using \<open>x \<in> exec[L2,\<pi>]\<close> by auto

    have "is_present ?\<pi> L1" and "is_present ?\<pi> L2" 
      using \<open>\<pi> \<in> L1 \<inter> L2\<close> by auto

    have "?\<pi> \<in> L1'a \<inter> L2'a"
      using L1'a_def \<open>L2'a \<equiv> map (\<lambda>(x, y). (x, y, True)) ` L2\<close> \<open>is_present (map (\<lambda>(x, y). (x, y, True)) \<pi>) L1\<close> \<open>is_present (map (\<lambda>(x, y). (x, y, True)) \<pi>) L2\<close> by auto 
    then have "?\<pi> \<in> absence_completion X Y L1" and "?\<pi> \<in> absence_completion X Y L2" and "?\<pi> \<in> L1' \<inter> L2'"
      unfolding L1'_def[symmetric] L2'_def[symmetric]
      unfolding \<open>L1' = L1'a \<union> L1'b\<close> \<open>L2' = L2'a \<union> L2'b\<close>
      by blast+
    
    have "out[L2',?\<pi>,x] = {(y, True) |y. y \<in> out[L2,\<pi>,x]} \<union> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L2,\<pi>,x]}"    
      using absence_completion_out(1)[OF assms(2) \<open>x \<in> X\<close> \<open>?\<pi> \<in> absence_completion X Y L2\<close> \<open>is_present ?\<pi> L2\<close> \<open>out[L2,map (\<lambda>(x, y, a). (x, y)) ?\<pi>,x] \<noteq> {}\<close>]
      unfolding L2'_def[symmetric] \<open>map (\<lambda>(x, y, a). (x, y)) ?\<pi> = \<pi>\<close> .
    then have "x \<in> exec[L2',?\<pi>]"
      using \<open>x \<in> exec[L2,\<pi>]\<close> by fastforce  
    then have "out[L1',?\<pi>,x] \<noteq> {}" and "out[L1',?\<pi>,x] \<subseteq> out[L2',?\<pi>,x]"
      using \<open>quasi_reduction L1' L2'\<close> \<open>?\<pi> \<in> L1' \<inter> L2'\<close>
      unfolding quasi_reduction_def 
      by blast+

    have "out[L1,\<pi>,x] \<noteq> {}"
      by (metis L1'_def \<open>is_present (map (\<lambda>(x, y). (x, y, True)) \<pi>) L1\<close> \<open>map (\<lambda>(x, y). (x, y, True)) \<pi> \<in> absence_completion X Y L1\<close> \<open>map (\<lambda>(x, y, a). (x, y)) (map (\<lambda>(x, y). (x, y, True)) \<pi>) = \<pi>\<close> \<open>out[L1',map (\<lambda>(x, y). (x, y, True)) \<pi>,x] \<noteq> {}\<close> \<open>x \<in> X\<close> absence_completion_out(2) assms(1)) 
    then have "out[L1',?\<pi>,x] = {(y, True) |y. y \<in> out[L1,\<pi>,x]} \<union> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L1,\<pi>,x]}"    
      using absence_completion_out(1)[OF assms(1) \<open>x \<in> X\<close> \<open>?\<pi> \<in> absence_completion X Y L1\<close> \<open>is_present ?\<pi> L1\<close>]
      unfolding L1'_def[symmetric] \<open>map (\<lambda>(x, y, a). (x, y)) ?\<pi> = \<pi>\<close>
      by blast

    have "out[L1,\<pi>,x] \<subseteq> Y" and "out[L2,\<pi>,x] \<subseteq> Y"
      by (meson assms(1,2) outputs_in_alphabet)+ 

    have "\<And> y . y \<in> out[L1,\<pi>,x] \<Longrightarrow> y \<in> out[L2,\<pi>,x]"
    proof -
      fix y assume "y \<in> out[L1,\<pi>,x]"
      then have "(y, True) \<in> out[L1',?\<pi>,x]" 
        unfolding \<open>out[L1',?\<pi>,x] = {(y, True) |y. y \<in> out[L1,\<pi>,x]} \<union> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L1,\<pi>,x]}\<close> by blast
      then have "(y, True) \<in> out[L2',?\<pi>,x]"
        using \<open>out[L1',?\<pi>,x] \<subseteq> out[L2',?\<pi>,x]\<close> by blast
      then show "y \<in> out[L2,\<pi>,x]" 
        unfolding \<open>out[L2',?\<pi>,x] = {(y, True) |y. y \<in> out[L2,\<pi>,x]} \<union> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L2,\<pi>,x]}\<close>
        by fastforce 
    qed
    moreover have "\<And> y . y \<in> out[L2,\<pi>,x] \<Longrightarrow> y \<in> out[L1,\<pi>,x]"
    proof -
      fix y assume "y \<in> out[L2,\<pi>,x]"
      then have "(y, True) \<in> out[L2',?\<pi>,x]" and "(y, False) \<notin> out[L2',?\<pi>,x]"
        unfolding \<open>out[L2',?\<pi>,x] = {(y, True) |y. y \<in> out[L2,\<pi>,x]} \<union> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L2,\<pi>,x]}\<close> by blast+
      moreover have "(y, True) \<in> out[L1',?\<pi>,x] \<or> (y, False) \<in> out[L1',?\<pi>,x]"  
        unfolding \<open>out[L1',?\<pi>,x] = {(y, True) |y. y \<in> out[L1,\<pi>,x]} \<union> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L1,\<pi>,x]}\<close>
        using \<open>out[L2,\<pi>,x] \<subseteq> Y\<close> \<open>y \<in> out[L2,\<pi>,x]\<close> by auto 
      ultimately have "(y, True) \<in> out[L1',?\<pi>,x]"
        using \<open>out[L1',?\<pi>,x] \<subseteq> out[L2',?\<pi>,x]\<close> by blast
      then show "y \<in> out[L1,\<pi>,x]" 
        unfolding \<open>out[L1',?\<pi>,x] = {(y, True) |y. y \<in> out[L1,\<pi>,x]} \<union> {(y, False) |y. y \<in> Y \<and> y \<notin> out[L1,\<pi>,x]}\<close>
        by fastforce 
    qed
    ultimately show "out[L1,\<pi>,x] = out[L2,\<pi>,x]"
      by blast
  qed
  then show "(absence_completion X Y L1) \<preceq>[X,quasired (Y \<times> UNIV)] (absence_completion X Y L2) \<Longrightarrow> L1 \<preceq>[X,quasieq Y] L2"
    unfolding L1'_def[symmetric] L2'_def[symmetric]  
    unfolding \<open>(L1' \<preceq>[X,quasired (Y \<times> UNIV)] L2') = quasi_reduction L1' L2'\<close>
    unfolding \<open>(L1 \<preceq>[X,quasieq Y] L2) = quasi_equivalence L1 L2\<close>
    unfolding quasi_reduction_def quasi_equivalence_def 
    by blast
qed




subsection \<open>Quasi-Reduction via Reduction and explicit Undefined Behaviour\<close>

fun bottom_completion :: "'x alphabet \<Rightarrow> 'y alphabet \<Rightarrow> ('x,'y) language \<Rightarrow> ('x, 'y option) language" where 
  "bottom_completion X Y L = 
    ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,Some y)) \<pi>) ` L)
    \<union> {(map (\<lambda>(x,y) . (x,Some y)) \<pi>)@[(x,y)]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] = {} \<and> x \<in> X \<and> (y = None \<or> y \<in> Some ` Y) \<and> (\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))}"

lemma bottom_completion_is_language :
  assumes "is_language X Y L"
shows "is_language X ({None} \<union> Some ` Y) (bottom_completion X Y L)"
proof -
  let ?L = "bottom_completion X Y L"

  have "?L \<noteq> {}"
    using language_contains_nil[OF assms] by auto
  moreover have "\<And> \<pi> . \<pi> \<in> ?L \<Longrightarrow> (\<forall> xy \<in> set \<pi> . fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y)) \<and> (\<forall> \<pi>' . prefix \<pi>' \<pi> \<longrightarrow> \<pi>' \<in> ?L)"
  proof -
    fix \<pi> assume "\<pi> \<in> ?L"
    then consider (a) "\<pi> \<in> ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,Some y)) \<pi>) ` L)" | 
                  (b) "\<pi> \<in> {(map (\<lambda>(x,y) . (x,Some y)) \<pi>)@[(x,y)]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] = {} \<and> x \<in> X \<and> (y = None \<or> y \<in> Some ` Y) \<and> (\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))}"
      unfolding bottom_completion.simps by blast
    then show "(\<forall> xy \<in> set \<pi> . fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y)) \<and> (\<forall> \<pi>' . prefix \<pi>' \<pi> \<longrightarrow> \<pi>' \<in> ?L)" 
    proof cases
      case a
      then obtain \<pi>' where "\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'" and "\<pi>' \<in> L"
        by auto
      then have "(\<forall> xy \<in> set \<pi>' . fst xy \<in> X \<and> snd xy \<in> Y)"
            and "(\<forall> \<pi>'' . prefix \<pi>'' \<pi>' \<longrightarrow> \<pi>'' \<in> L)"
        using assms by auto

      
      have "(\<forall> \<pi>' . prefix \<pi>' \<pi> \<longrightarrow> \<pi>' \<in> ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,Some y)) \<pi>) ` L))" 
        using \<open>(\<forall> \<pi>'' . prefix \<pi>'' \<pi>' \<longrightarrow> \<pi>'' \<in> L)\<close> unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close>
        using prefix_map_rightE by force
      then have "(\<forall> \<pi>' . prefix \<pi>' \<pi> \<longrightarrow> \<pi>' \<in> ?L)" 
        by auto
      moreover have "(\<forall> xy \<in> set \<pi> . fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y))"
        using \<open>(\<forall> xy \<in> set \<pi>' . fst xy \<in> X \<and> snd xy \<in> Y)\<close> unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close> 
        by (induction \<pi>'; auto)
      ultimately show ?thesis
        by blast
    next
      case b
      then obtain \<pi>' x y \<tau> where "\<pi> = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x,y)]@\<tau>"    
                             and "\<pi>' \<in> L" 
                             and "out[L,\<pi>',x] = {}" 
                             and "x \<in> X" 
                             and "(y = None \<or> y \<in> Some ` Y)" 
                             and "(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
        by blast
      then have "(\<forall> xy \<in> set \<pi>' . fst xy \<in> X \<and> snd xy \<in> Y)"
            and "(\<forall> \<pi>'' . prefix \<pi>'' \<pi>' \<longrightarrow> \<pi>'' \<in> L)"
        using assms by auto

      have "(\<forall> xy \<in> set (map (\<lambda>(x,y) . (x,Some y)) \<pi>') . fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y))"
        using \<open>(\<forall> xy \<in> set \<pi>' . fst xy \<in> X \<and> snd xy \<in> Y)\<close> 
        by (induction \<pi>'; auto)
      moreover have "set \<pi> = set (map (\<lambda>(x,y) . (x,Some y)) \<pi>') \<union> {(x,y)} \<union> set \<tau>"
        unfolding \<open>\<pi> = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x,y)]@\<tau>\<close> 
        by simp
      ultimately have "(\<forall> xy \<in> set \<pi> . fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y))"
        using \<open>x \<in> X\<close> \<open>(y = None \<or> y \<in> Some ` Y)\<close> \<open>(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))\<close>
        by auto
      moreover have "\<And> \<pi>'' . prefix \<pi>'' \<pi> \<Longrightarrow> \<pi>'' \<in> ?L"
      proof -
        fix \<pi>'' assume "prefix \<pi>'' \<pi>" 
        then obtain i where "\<pi>'' = take i \<pi>"
          by (metis append_eq_conv_conj prefix_def)
        then consider (b1) "i \<le> length \<pi>'" | 
                      (b2) "i > length \<pi>'"
          by linarith
        then show "\<pi>'' \<in> ?L" proof cases
          case b1 
          then have "i \<le> length (map (\<lambda>(x,y) . (x,Some y)) \<pi>')" 
            by auto
          then have "\<pi>'' = map (\<lambda>(x,y) . (x,Some y)) (take i \<pi>')"
            unfolding \<open>\<pi>'' = take i \<pi>\<close>
            using \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>' @ [(x, y)] @ \<tau>\<close> take_map by fastforce 
          moreover have "take i \<pi>' \<in> L"
            using \<open>\<pi>' \<in> L\<close> take_is_prefix
            using \<open>\<forall>\<pi>''. prefix \<pi>'' \<pi>' \<longrightarrow> \<pi>'' \<in> L\<close> by blast 
          ultimately have "\<pi>'' \<in> ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,Some y)) \<pi>) ` L)"
            by simp
          then show "\<pi>'' \<in> ?L" 
            by auto
        next
          case b2 
          then have "i > length (map (\<lambda>(x,y) . (x,Some y)) \<pi>')" 
            by auto

          have "\<And> k xs ys . k > length xs \<Longrightarrow> take k (xs@ys) = xs@(take (k - length xs) ys)"
            by simp 
          have take_helper: "\<And> k xs y zs . k > length xs \<Longrightarrow> take k (xs@[y]@zs) = xs@[y]@(take (k - length xs - 1) zs)"
            by (metis One_nat_def Suc_pred \<open>\<And>ys xs k. length xs < k \<Longrightarrow> take k (xs @ ys) = xs @ take (k - length xs) ys\<close> append_Cons append_Nil take_Suc_Cons zero_less_diff) 
          
          have **: "\<pi>'' = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x,y)]@(take (i - length \<pi>' - 1) \<tau>)"
            unfolding \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>' @ [(x, y)] @ \<tau>\<close>  \<open>\<pi>'' = take i \<pi>\<close>
            using take_helper[OF \<open>i > length (map (\<lambda>(x,y) . (x,Some y)) \<pi>')\<close>] by simp
          
          have "(\<forall> (x,y) \<in> set (take (i - length \<pi>' - 1) \<tau>) . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
            using \<open>(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))\<close>
            by (meson in_set_takeD) 
          then show ?thesis
            unfolding ** bottom_completion.simps
            using \<open>\<pi>' \<in> L\<close> \<open>out[L,\<pi>',x] = {}\<close> \<open>x \<in> X\<close> \<open>(y = None \<or> y \<in> Some ` Y)\<close>
            by blast
        qed
      qed
      ultimately show ?thesis by auto
    qed 
  qed
  ultimately show ?thesis 
    unfolding is_language.simps by blast
qed




fun is_not_undefined :: "('x,'y option) word \<Rightarrow> ('x,'y) language \<Rightarrow> bool" where
  "is_not_undefined \<pi> L = (\<pi> \<in> map (\<lambda>(x, y). (x, Some y)) ` L)"

lemma bottom_id : "map (\<lambda>(x,y) . (x, the y)) (map (\<lambda>(x, y). (x, Some y)) \<pi>) = \<pi>"
  by (induction \<pi>; auto) 



fun maximum_prefix_with_property :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "maximum_prefix_with_property P xs = (last (filter P (prefixes xs)))"

lemma maximum_prefix_with_property_props : 
  assumes "\<exists> ys \<in> set (prefixes xs) . P ys"
shows "P (maximum_prefix_with_property P xs)"
  and "(maximum_prefix_with_property P xs) \<in> set (prefixes xs)"
  and "\<And> ys . prefix ys xs \<Longrightarrow> P ys \<Longrightarrow> length ys \<le> length (maximum_prefix_with_property P xs)"
proof -

  have "P (maximum_prefix_with_property P xs) \<and>
        (maximum_prefix_with_property P xs) \<in> set (prefixes xs) \<and>
        (\<forall> ys . prefix ys xs \<longrightarrow> P ys \<longrightarrow> length ys \<le> length (maximum_prefix_with_property P xs))"
    using assms 
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    have "prefixes (xs @ [x]) = (prefixes xs)@[xs @ [x]]"
      by simp

    show ?case proof (cases "P (xs@[x])")
      case True      
      then have "maximum_prefix_with_property P (xs @ [x]) = (xs @ [x])"
        unfolding maximum_prefix_with_property.simps \<open>prefixes (xs @ [x]) = (prefixes xs)@[xs @ [x]]\<close> 
        by auto        
      show ?thesis 
        using True
        unfolding \<open>maximum_prefix_with_property P (xs @ [x]) = (xs@[x])\<close> 
        using in_set_prefixes prefix_length_le by blast
    next
      case False 
      then have "maximum_prefix_with_property P (xs@[x]) = maximum_prefix_with_property P xs" 
        unfolding maximum_prefix_with_property.simps \<open>prefixes (xs @ [x]) = (prefixes xs)@[xs @ [x]]\<close>
        by auto

      have "\<exists>a\<in>set (prefixes xs). P a" 
        using snoc.prems False unfolding \<open>prefixes (xs @ [x]) = (prefixes xs)@[xs @ [x]]\<close> by auto

      show ?thesis
        using snoc.IH[OF \<open>\<exists>a\<in>set (prefixes xs). P a\<close>] False
        unfolding \<open>maximum_prefix_with_property P (xs@[x]) = maximum_prefix_with_property P xs\<close>
        unfolding \<open>prefixes (xs @ [x]) = (prefixes xs)@[xs @ [x]]\<close> by auto
    qed
  qed
  then show "P (maximum_prefix_with_property P xs)"
        and "(maximum_prefix_with_property P xs) \<in> set (prefixes xs)"
        and "\<And> ys . prefix ys xs \<Longrightarrow> P ys \<Longrightarrow> length ys \<le> length (maximum_prefix_with_property P xs)" 
    by blast+
qed


lemma bottom_completion_out : 
  assumes "is_language X Y L"
  and     "x \<in> X"
  and     "\<pi> \<in> bottom_completion X Y L"
shows "is_not_undefined \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<Longrightarrow> out[bottom_completion X Y L, \<pi>, x] = Some ` out[L, map (\<lambda>(x,y) . (x, the y)) \<pi>, x]"
and   "is_not_undefined \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] = {} \<Longrightarrow> out[bottom_completion X Y L, \<pi>, x] = {None} \<union> Some ` Y"
and   "\<not> is_not_undefined \<pi> L \<Longrightarrow> out[bottom_completion X Y L, \<pi>, x] = {None} \<union> Some ` Y"
proof -

  let ?L = "bottom_completion X Y L"
  define L'a where "L'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,Some y)) \<pi>) ` L)"
  define L'b where "L'b = {(map (\<lambda>(x,y) . (x,Some y)) \<pi>)@[(x,y)]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L \<and> out[L,\<pi>,x] = {} \<and> x \<in> X \<and> (y = None \<or> y \<in> Some ` Y) \<and> (\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))}"
  have "?L = L'a \<union> L'b" 
    unfolding L'a_def L'b_def bottom_completion.simps by blast
  then have "out[?L, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}"
    unfolding outputs.simps language_for_state.simps by blast

  have "is_language X ({None} \<union> Some ` Y) ?L"
    using bottom_completion_is_language[OF assms(1)] .
  
  show "is_not_undefined \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<Longrightarrow> out[bottom_completion X Y L, \<pi>, x] = Some ` out[L, map (\<lambda>(x,y) . (x, the y)) \<pi>, x]"
   and "is_not_undefined \<pi> L \<Longrightarrow> out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] = {} \<Longrightarrow> out[bottom_completion X Y L, \<pi>, x] = {None} \<union> Some ` Y"
  proof -
    assume "is_not_undefined \<pi> L"
    then obtain \<pi>' where "\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'" and "\<pi>' \<in> L"
      by auto
    then have "map (\<lambda>(x, y). (x, the y)) \<pi> = \<pi>'"
      using bottom_id by auto


    have "{y. \<pi> @ [(x, y)] \<in> L'a} = Some ` out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x]"
    proof 
      show "{y. \<pi> @ [(x, y)] \<in> L'a} \<subseteq> Some ` out[L,map (\<lambda>(x, y). (x, the y)) \<pi>,x]"
      proof 
        fix y assume "y \<in> {y. \<pi> @ [(x, y)] \<in> L'a}"
        then have "\<pi> @ [(x, y)] \<in> L'a" by auto
        then obtain \<pi>' where "\<pi> @ [(x, y)] = map (\<lambda>(x,y) . (x,Some y)) \<pi>'" and "\<pi>' \<in> L" 
          unfolding L'a_def by blast
        then have "length (\<pi> @ [(x, y)]) = length \<pi>'"
          by auto
        then obtain \<gamma>' xy where "\<pi>' = \<gamma>'@[xy]"
          by (metis add.right_neutral dual_order.strict_iff_not length_append_singleton less_add_Suc2 rev_exhaust take0 take_all_iff)
        then have "(x,y) = (\<lambda>(x, y). (x, Some y)) xy"
          using \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close> unfolding \<open>\<pi>' = \<gamma>'@[xy]\<close> by auto
        then have "y = Some (snd xy)" and "xy = (x,snd xy)"
          by (simp add: split_beta)+
        moreover define y' where "y' = snd xy"
        ultimately have "y = Some y'" and "xy = (x,y')"
          by auto

        have "map (\<lambda>(x, y). (x, the y)) \<pi> = \<gamma>'"
          using \<open>\<pi> @ [(x, y)] = map (\<lambda>(x,y) . (x,Some y)) \<pi>'\<close> unfolding \<open>\<pi>' = \<gamma>'@[xy]\<close>
          using bottom_id by auto 

        have "y' \<in> out[L,map (\<lambda>(x, y). (x, the y)) \<pi>,x]"
          using \<open>\<pi>' \<in> L\<close>
          unfolding \<open>map (\<lambda>(x, y). (x, the y)) \<pi> = \<gamma>'\<close> \<open>\<pi>' = \<gamma>'@[xy]\<close> \<open>xy = (x,y')\<close> by auto
        then show "y \<in> Some ` out[L,map (\<lambda>(x, y). (x, the y)) \<pi>,x]"
          unfolding \<open>y = Some y'\<close> by blast
      qed
      show "Some ` out[L,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<subseteq> {y. \<pi> @ [(x, y)] \<in> L'a}"
      proof 
        fix y assume "y \<in> Some ` out[L,map (\<lambda>(x, y). (x, the y)) \<pi>,x]"
        then obtain y' where "y = Some y'" and "y' \<in> out[L,map (\<lambda>(x, y). (x, the y)) \<pi>,x]"
          by blast
        then have "\<pi>'@[(x,y')] \<in> L"
          unfolding \<open>map (\<lambda>(x, y). (x, the y)) \<pi> = \<pi>'\<close> by auto
        then show "y \<in> {y. \<pi> @ [(x, y)] \<in> L'a}"
          unfolding L'a_def \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close>
          using \<open>y = Some y'\<close> image_iff by fastforce
      qed
    qed



    show "out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<Longrightarrow> out[bottom_completion X Y L, \<pi>, x] = Some ` out[L, map (\<lambda>(x,y) . (x, the y)) \<pi>, x]"
    proof -
      assume "out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {}"
      then obtain ya where "\<pi>'@[(x,ya)] \<in> L"
        using \<open>\<pi>' \<in> L\<close> unfolding \<open>map (\<lambda>(x,y) . (x, the y)) \<pi> = \<pi>'\<close> by auto

      
      have "{y. \<pi> @ [(x, y)] \<in> L'b} = {}"
      proof (rule ccontr)
        assume "{y. \<pi> @ [(x, y)] \<in> L'b} \<noteq> {}"
        then obtain y where "\<pi> @ [(x, y)] \<in> L'b" by blast
        then obtain \<pi>'' x' y' \<tau> where "\<pi> @ [(x, y)] = (map (\<lambda>(x,y) . (x,Some y)) \<pi>'')@[(x',y')]@\<tau>"    
                                  and "\<pi>'' \<in> L" 
                                  and "out[L,\<pi>'',x'] = {}" 
                                  and "x' \<in> X" 
                                  and "(y' = None \<or> y' \<in> Some ` Y)" 
                                  and "(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
          unfolding L'b_def 
          by blast

        have "\<And> y'' . \<pi>''@[(x',y'')] \<notin> L"
          using \<open>\<pi>'' \<in> L\<close> \<open>out[L,\<pi>'',x'] = {}\<close> 
          unfolding outputs.simps language_for_state.simps by force        

        have "length \<pi>' = length \<pi>''"
        proof -
          have "length \<pi>' = length \<pi>"
            using \<open>map (\<lambda>(x, y). (x, the y)) \<pi> = \<pi>'\<close> length_map by blast 

          have "\<not> length \<pi>' < length \<pi>''"
          proof 
            assume "length \<pi>' < length \<pi>''"
            then have "length \<pi>'' = Suc (length \<pi>')"
              by (metis (no_types, lifting) One_nat_def \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>'' @ [(x', y')] @ \<tau>\<close> \<open>length \<pi>' = length \<pi>\<close> add_diff_cancel_left' length_append length_append_singleton length_map list.size(3) not_less_eq plus_1_eq_Suc zero_less_Suc zero_less_diff)
            then have "length \<pi>'' > length \<pi>"
              by (simp add: \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close>) 
            then show False
              by (metis (no_types, lifting) One_nat_def \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>'' @ [(x', y')] @ \<tau>\<close> length_Cons length_append length_append_singleton length_map less_add_same_cancel1 list.size(3) not_less_eq plus_1_eq_Suc zero_less_Suc) 
          qed
          moreover have "\<not> length \<pi>'' < length \<pi>'"
          proof 
            assume "length \<pi>'' < length \<pi>'"
            then have "prefix ((map (\<lambda>(x,y) . (x,Some y)) \<pi>'')@[(x',y')]) (map (\<lambda>(x,y) . (x,Some y)) \<pi>')"
              by (metis (no_types, lifting) \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close> \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>'' @ [(x', y')] @ \<tau>\<close> append.assoc length_append_singleton length_map linorder_not_le not_less_eq prefixI prefix_length_prefix) 
            then have "prefix \<pi>'' \<pi>'"
              by (metis append_prefixD bottom_id map_mono_prefix) 
            then have "take (length \<pi>'') \<pi>' = \<pi>''"
              by (metis append_eq_conv_conj prefix_def) 

            have "(x',y') = (((map (\<lambda>(x,y) . (x,Some y)) \<pi>'')@[(x',y')])) ! (length \<pi>'')"
              by (induction \<pi>'' arbitrary: x' y'; auto)
            then have "(x',y') = (map (\<lambda>(x,y) . (x,Some y)) \<pi>') ! (length \<pi>'')"
              by (metis (no_types, lifting) \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close> \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>'' @ [(x', y')] @ \<tau>\<close> \<open>length \<pi>'' < length \<pi>'\<close> append_Cons length_map nth_append nth_append_length) 
            then have "fst (\<pi>' ! (length \<pi>'')) = x'"
              by (simp add: \<open>length \<pi>'' < length \<pi>'\<close> split_beta) 

            have "out[L, take (length \<pi>'') \<pi>', fst (\<pi>' ! (length \<pi>''))] = {}"
              unfolding \<open>take (length \<pi>'') \<pi>' = \<pi>''\<close> \<open>fst (\<pi>' ! (length \<pi>'')) = x'\<close> 
              using \<open>out[L,\<pi>'',x'] = {}\<close> .
            moreover have "\<And> i . i < length \<pi>' \<Longrightarrow> out[L, take i \<pi>', fst (\<pi>' ! i)] \<noteq> {}"
              using prefix_executable[OF assms(1) \<open>\<pi>' \<in> L\<close>]
              by (meson outputs_executable) 
            ultimately show False 
              using \<open>length \<pi>'' < length \<pi>'\<close> by blast
          qed
          ultimately show ?thesis
            by simp
        qed
        then have "\<pi>'' = \<pi>'"
          by (metis \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>'' @ [(x', y')] @ \<tau>\<close> \<open>map (\<lambda>(x, y). (x, the y)) \<pi> = \<pi>'\<close> append_eq_append_conv bottom_id length_map) 

        show False
          using \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>'' @ [(x', y')] @ \<tau>\<close> \<open>\<pi>'' = \<pi>'\<close> \<open>map (\<lambda>(x, y). (x, the y)) \<pi> = \<pi>'\<close> \<open>out[L,\<pi>'',x'] = {}\<close> \<open>out[L,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<noteq> {}\<close> 
          by force 
      qed
      then show ?thesis
        using \<open>out[bottom_completion X Y L,\<pi>,x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> 
        using \<open>{y. \<pi> @ [(x, y)] \<in> L'a} = Some ` out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x]\<close>
        by force 
    qed

    
    show "out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] = {} \<Longrightarrow> out[bottom_completion X Y L, \<pi>, x] = {None} \<union> Some ` Y"
    proof -
      assume "out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] = {}" 
      then have "{y. \<pi> @ [(x, y)] \<in> L'a} = {}"
        unfolding \<open>{y. \<pi> @ [(x, y)] \<in> L'a} = Some ` out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x]\<close> by blast
      moreover have "{y. \<pi> @ [(x, y)] \<in> L'b} = {None} \<union> Some ` Y"
      proof 
        show "{y. \<pi> @ [(x, y)] \<in> L'b} \<subseteq> {None} \<union> Some ` Y"
        proof 
          fix y assume "y \<in> {y. \<pi> @ [(x, y)] \<in> L'b}"
          then have "\<pi> @ [(x, y)] \<in> L'b" by blast
          then obtain \<pi>'' x' y' \<tau> where "\<pi> @ [(x, y)] = (map (\<lambda>(x,y) . (x,Some y)) \<pi>'')@[(x',y')]@\<tau>"    
                                    and "\<pi>'' \<in> L" 
                                    and "out[L,\<pi>'',x'] = {}" 
                                    and "x' \<in> X" 
                                    and "(y' = None \<or> y' \<in> Some ` Y)" 
                                    and "(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
            unfolding L'b_def 
            by blast
  
          show "y \<in> {None} \<union> Some ` Y"
            by (metis (no_types, lifting) Un_insert_right \<open>out[bottom_completion X Y L,\<pi>,x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> \<open>y \<in> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> assms(1) bottom_completion_is_language insert_subset mk_disjoint_insert outputs_in_alphabet) 
        qed
        show "{None} \<union> Some ` Y \<subseteq> {y. \<pi> @ [(x, y)] \<in> L'b}"
        proof 
          fix y assume "y \<in> {None} \<union> Some ` Y" 

          have "\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>' @ [(x, y)] @ []"
            by (simp add: \<open>\<pi> = map (\<lambda>(x, y). (x, Some y)) \<pi>'\<close>)
          moreover note \<open>\<pi>' \<in> L\<close>
          moreover have "out[L,\<pi>',x] = {}" 
            using \<open>out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] = {}\<close> unfolding \<open>map (\<lambda>(x,y) . (x, the y)) \<pi> = \<pi>'\<close> .
          moreover note \<open>x \<in> X\<close>
          moreover have "(y = None \<or> y \<in> Some ` Y)"
            using \<open>y \<in> {None} \<union> Some ` Y\<close> by blast
          moreover have "(\<forall>(x, y)\<in>set []. x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
            by simp
          ultimately show "y \<in> {y. \<pi> @ [(x, y)] \<in> L'b}"
            unfolding L'b_def by blast
        qed
      qed
      ultimately show ?thesis
        using \<open>out[bottom_completion X Y L,\<pi>,x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> 
        using \<open>{y. \<pi> @ [(x, y)] \<in> L'a} = Some ` out[L,map (\<lambda>(x,y) . (x, the y)) \<pi>,x]\<close>
        by force 
    qed
  qed

  show "\<not> is_not_undefined \<pi> L \<Longrightarrow> out[bottom_completion X Y L,\<pi>,x] = {None} \<union> Some ` Y" 
  proof -
    assume "\<not> is_not_undefined \<pi> L" 
    then have "\<pi> \<notin> L'a" 
      unfolding L'a_def by auto 

    have "{y. \<pi> @ [(x, y)] \<in> L'a} = {}"
    proof (rule ccontr)
      assume "{y. \<pi> @ [(x, y)] \<in> L'a} \<noteq> {}"
      then obtain y where "\<pi> @ [(x, y)] \<in> L'a" by blast
      then obtain \<gamma> where "\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<gamma>" and "\<gamma> \<in> L" 
        unfolding L'a_def by blast
      then have "\<pi> = map (\<lambda>(x, y). (x, Some y)) (butlast \<gamma>)"
        by (metis (mono_tags, lifting) butlast_snoc map_butlast) 
      moreover have "butlast \<gamma> \<in> L"
        using \<open>\<gamma> \<in> L\<close> assms(1)
        by (simp add: prefixeq_butlast) 
      ultimately show False
        using \<open>\<pi> \<notin> L'a\<close>
        using L'a_def by blast
    qed 
    then have "out[?L, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L'b}"
      using \<open>out[bottom_completion X Y L,\<pi>,x] = {y. \<pi> @ [(x, y)] \<in> L'a} \<union> {y. \<pi> @ [(x, y)] \<in> L'b}\<close> by blast 
    also have "\<dots> = {None} \<union> Some ` Y" 
    proof 
      show "{y. \<pi> @ [(x, y)] \<in> L'b} \<subseteq> {None} \<union> Some ` Y"
      proof 
        fix y assume "y \<in> {y. \<pi> @ [(x, y)] \<in> L'b}"
        then obtain \<pi>' x' y' \<tau> where "\<pi> @ [(x, y)] = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x',y')]@\<tau>"    
                                 and "\<pi>' \<in> L" 
                                 and "out[L,\<pi>',x'] = {}" 
                                 and "x' \<in> X" 
                                 and "(y' = None \<or> y' \<in> Some ` Y)" 
                                 and "(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
          unfolding L'b_def 
          by blast

        have "(x,y) \<in> set ([(x',y')]@\<tau>)"
          by (metis \<open>\<pi> @ [(x, y)] = map (\<lambda>(x, y). (x, Some y)) \<pi>' @ [(x', y')] @ \<tau>\<close> append_is_Nil_conv last_appendR last_in_set last_snoc length_Cons list.size(3) nat.simps(3))
        then show "y \<in> {None} \<union> Some ` Y"
          using \<open>(y' = None \<or> y' \<in> Some ` Y)\<close> \<open>(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))\<close> by auto
      qed
      show "{None} \<union> Some ` Y \<subseteq> {y. \<pi> @ [(x, y)] \<in> L'b}" 
      proof 
        fix y assume "y \<in> {None} \<union> Some ` Y" 

        have "\<pi> \<in> L'b"
          using \<open>\<pi> \<notin> L'a\<close> \<open>?L = L'a \<union> L'b\<close> assms(3) by fastforce
        then obtain \<pi>' x' y' \<tau> where "\<pi> = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x',y')]@\<tau>"    
                                 and "\<pi>' \<in> L" 
                                 and "out[L,\<pi>',x'] = {}" 
                                 and "x' \<in> X" 
                                 and "(y' = None \<or> y' \<in> Some ` Y)" 
                                 and "(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
          unfolding L'b_def 
          by blast

        have "\<pi> @ [(x,y)] = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x',y')]@(\<tau>@[(x,y)])"
          unfolding \<open>\<pi> = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x',y')]@\<tau>\<close> by auto
        moreover note \<open>\<pi>' \<in> L\<close> and \<open>out[L,\<pi>',x'] = {}\<close> and \<open>x' \<in> X\<close> and \<open>(y' = None \<or> y' \<in> Some ` Y)\<close>
        moreover have "(\<forall> (x,y) \<in> set (\<tau>@[(x,y)]) . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
          using \<open>\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y)\<close> \<open>y \<in> {None} \<union> Some ` Y\<close> \<open>x \<in> X\<close>
          by auto
        ultimately show "y \<in> {y. \<pi> @ [(x, y)] \<in> L'b}" 
          unfolding L'b_def by blast
      qed
    qed
    finally show "out[?L,\<pi>,x] = {None} \<union> Some ` Y" .
  qed
qed



theorem quasired_via_red : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(L1 \<preceq>[X,quasired Y] L2) \<longleftrightarrow> ((bottom_completion X Y L1) \<preceq>[X, red ({None} \<union> Some ` Y)] (bottom_completion X Y L2))" 
proof -

  define L1' where "L1' = bottom_completion X Y L1"
  define L2' where "L2' = bottom_completion X Y L2"

  define L1'a where "L1'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,Some y)) \<pi>) ` L1)"
  define L1'b where "L1'b = {(map (\<lambda>(x,y) . (x,Some y)) \<pi>)@[(x,y)]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L1 \<and> out[L1,\<pi>,x] = {} \<and> x \<in> X \<and> (y = None \<or> y \<in> Some ` Y) \<and> (\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))}"
  define L2'a where "L2'a = ((\<lambda> \<pi> . map (\<lambda>(x,y) . (x,Some y)) \<pi>) ` L2)"
  define L2'b where "L2'b = {(map (\<lambda>(x,y) . (x,Some y)) \<pi>)@[(x,y)]@\<tau> | \<pi> x y \<tau> . \<pi> \<in> L2 \<and> out[L2,\<pi>,x] = {} \<and> x \<in> X \<and> (y = None \<or> y \<in> Some ` Y) \<and> (\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))}"

  let ?L1 = "bottom_completion X Y L1"
  
  have "?L1 = L1'a \<union> L1'b" 
    unfolding L1'a_def L1'b_def bottom_completion.simps by blast
  then have "\<And> \<pi> x . out[?L1, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L1'a} \<union> {y. \<pi> @ [(x, y)] \<in> L1'b}"
    unfolding outputs.simps language_for_state.simps by blast

  let ?L2 = "bottom_completion X Y L2"
  
  have "?L2 = L2'a \<union> L2'b" 
    unfolding L2'a_def L2'b_def bottom_completion.simps by blast
  then have "\<And> \<pi> x . out[?L2, \<pi>, x] = {y. \<pi> @ [(x, y)] \<in> L2'a} \<union> {y. \<pi> @ [(x, y)] \<in> L2'b}"
    unfolding outputs.simps language_for_state.simps by blast

  have "is_language X ({None} \<union> Some ` Y) ?L1"
    using bottom_completion_is_language[OF assms(1)] .
  have "is_language X ({None} \<union> Some ` Y) ?L2"
    using bottom_completion_is_language[OF assms(2)] .
  then have "\<And> \<pi> x . out[bottom_completion X Y L2,\<pi>,x] \<subseteq> {None} \<union> Some ` Y"
    by (meson outputs_in_alphabet) 

  have "(?L1 \<preceq>[X, red ({None} \<union> Some ` Y)] ?L2) = (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x])"
    unfolding type_1_conforms.simps red.simps 
    using \<open>\<And> \<pi> x . out[bottom_completion X Y L2,\<pi>,x] \<subseteq> {None} \<union> Some ` Y\<close> by force
  also have "\<dots> = (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . (out[?L2,\<pi>,x] = {None} \<union> Some ` Y \<or> (out[?L1,\<pi>,x] \<noteq> {} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x])))"
    by (metis (no_types, lifting) IntD1 \<open>is_language X ({None} \<union> Some ` Y) (bottom_completion X Y L1)\<close> \<open>is_language X ({None} \<union> Some ` Y) (bottom_completion X Y L2)\<close> assms(1) bottom_completion_out(1) bottom_completion_out(2) bottom_completion_out(3) image_is_empty outputs_in_alphabet subset_antisym)
  also have "\<dots> = (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . (out[?L2,\<pi>,x] = {None} \<union> Some ` Y \<or> (is_not_undefined \<pi> L1 \<and> is_not_undefined \<pi> L2 \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<subseteq> out[L2,map (\<lambda>(x,y) . (x, the y)) \<pi>,x])))"
  proof -
    have "\<And> \<pi> x . \<pi> \<in> ?L1 \<inter> ?L2 \<Longrightarrow> x \<in> X \<Longrightarrow> out[?L2,\<pi>,x] \<noteq> {None} \<union> Some ` Y \<Longrightarrow> 
              (out[?L1,\<pi>,x] \<noteq> {} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x]) = (is_not_undefined \<pi> L1 \<and> is_not_undefined \<pi> L2 \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<subseteq> out[L2,map (\<lambda>(x,y) . (x, the y)) \<pi>,x])"
    proof -
      fix \<pi> x assume "\<pi> \<in> ?L1 \<inter> ?L2" and "x \<in> X" and "out[?L2,\<pi>,x] \<noteq> {None} \<union> Some ` Y"
      then have "\<pi> \<in> ?L1" and "\<pi> \<in> ?L2" by blast+

      have "is_not_undefined \<pi> L2"
        using bottom_completion_out[OF assms(2) \<open>x \<in> X\<close> \<open>\<pi> \<in> ?L2\<close>]
        using \<open>out[bottom_completion X Y L2,\<pi>,x] \<noteq> {None} \<union> Some ` Y\<close> by fastforce 
      have "out[L2,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<noteq> {}"
        using bottom_completion_out(1,2)[OF assms(2) \<open>x \<in> X\<close> \<open>\<pi> \<in> ?L2\<close>]
        using \<open>is_not_undefined \<pi> L2\<close> \<open>out[bottom_completion X Y L2,\<pi>,x] \<noteq> {None} \<union> Some ` Y\<close> by blast 

      show "(out[?L1,\<pi>,x] \<noteq> {} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x]) = (is_not_undefined \<pi> L1 \<and> is_not_undefined \<pi> L2 \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<subseteq> out[L2,map (\<lambda>(x,y) . (x, the y)) \<pi>,x])"
      proof (cases "is_not_undefined \<pi> L1")
        case False 
        then have "out[?L1,\<pi>,x] = {None} \<union> Some ` Y"
          by (meson IntD1 \<open>\<pi> \<in> bottom_completion X Y L1 \<inter> bottom_completion X Y L2\<close> \<open>x \<in> X\<close> assms(1) bottom_completion_out(3)) 
        then have "\<not> (out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x])"
          by (metis \<open>is_language X ({None} \<union> Some ` Y) (bottom_completion X Y L2)\<close> \<open>out[bottom_completion X Y L2,\<pi>,x] \<noteq> {None} \<union> Some ` Y\<close> outputs_in_alphabet subset_antisym) 
        then show ?thesis
          using False by presburger 
      next
        case True

        have "(out[?L1,\<pi>,x] \<noteq> {} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x]) = (out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<subseteq> out[L2,map (\<lambda>(x,y) . (x, the y)) \<pi>,x])" 
        proof (cases "out[L1,map (\<lambda>(x, y). (x, the y)) \<pi>,x] = {}")
          case True

          have "\<not> (out[?L1,\<pi>,x] \<noteq> {} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x])"
            unfolding bottom_completion_out(2)[OF assms(1) \<open>x \<in> X\<close> \<open>\<pi> \<in> ?L1\<close> \<open>is_not_undefined \<pi> L1\<close> True]
            by (meson \<open>\<And>x \<pi>. out[bottom_completion X Y L2,\<pi>,x] \<subseteq> {None} \<union> Some ` Y\<close> \<open>out[bottom_completion X Y L2,\<pi>,x] \<noteq> {None} \<union> Some ` Y\<close> subset_antisym) 
          moreover have "\<not> (out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x,y) . (x, the y)) \<pi>,x] \<subseteq> out[L2,map (\<lambda>(x,y) . (x, the y)) \<pi>,x])"
            using True by simp
          ultimately show ?thesis by blast
        next
          case False
          show ?thesis 
            unfolding bottom_completion_out(1)[OF assms(1) \<open>x \<in> X\<close> \<open>\<pi> \<in> ?L1\<close> \<open>is_not_undefined \<pi> L1\<close> False]
            unfolding bottom_completion_out(1)[OF assms(2) \<open>x \<in> X\<close> \<open>\<pi> \<in> ?L2\<close> \<open>is_not_undefined \<pi> L2\<close> \<open>out[L2,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<noteq> {}\<close>]
            by blast
        qed
        then show ?thesis
          using \<open>is_not_undefined \<pi> L1\<close> \<open>is_not_undefined \<pi> L2\<close> 
          by blast
      qed
    qed
    then show ?thesis
      by meson
  qed
  also have "\<dots> = ( (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . \<not> is_not_undefined \<pi> L1 \<longrightarrow> is_not_undefined \<pi> L2 \<longrightarrow> out[?L2,\<pi>,x] = {None} \<union> Some ` Y) 
                  \<and> (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> X . out[L2,\<pi>,x] = {} \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])))" 
    (is "?A = ?B")
  proof 
    show "?A \<Longrightarrow> ?B"  
    proof  -
      assume ?A

      have "\<And> \<pi> x . \<pi> \<in> ?L1 \<inter> ?L2 \<Longrightarrow> x \<in> X \<Longrightarrow> \<not> is_not_undefined \<pi> L1 \<Longrightarrow> is_not_undefined \<pi> L2 \<Longrightarrow> out[?L2,\<pi>,x] = {None} \<union> Some ` Y"
        using \<open>?A\<close> by blast
      moreover have "\<And> \<pi> x . \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> out[L2,\<pi>,x] = {} \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])"
      proof -
        fix \<pi> x assume "\<pi> \<in> L1 \<inter> L2" and "x \<in> X" 

        let ?\<pi> = "map (\<lambda>(x, y). (x, Some y)) \<pi>" 

        have "is_not_undefined ?\<pi> L1" and "is_not_undefined ?\<pi> L2" 
          using \<open>\<pi> \<in> L1 \<inter> L2\<close> by auto
        then have "?\<pi> \<in> ?L1" and "?\<pi> \<in> ?L2"
          by auto 

        show "out[L2,\<pi>,x] = {} \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])"
        proof (cases "out[L2,\<pi>,x] = {}")
          case True
          then show ?thesis by auto
        next
          case False
          then have "out[bottom_completion X Y L2,?\<pi>,x] \<noteq> {None} \<union> Some ` Y" 
            using bottom_completion_out(1)[OF assms(2) \<open>x \<in> X\<close> \<open>?\<pi> \<in> ?L2\<close> \<open>is_not_undefined ?\<pi> L2\<close>]
            unfolding bottom_id
            by force
          then have "out[L1,map (\<lambda>(x, y). (x, the y)) ?\<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x, y). (x, the y)) ?\<pi>,x] \<subseteq> out[L2,map (\<lambda>(x, y). (x, the y)) ?\<pi>,x]"
            using \<open>?A\<close> 
            using \<open>?\<pi> \<in> ?L1\<close> \<open>?\<pi> \<in> ?L2\<close> \<open>x \<in> X\<close> 
            by blast
          then show "out[L2,\<pi>,x] = {} \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])"
            unfolding bottom_id by blast
        qed
      qed
      ultimately show ?B
        by meson
    qed
    show "?B \<Longrightarrow> ?A" 
    proof -
      assume "?B" 

      have "\<And> \<pi> x . \<pi> \<in> ?L1 \<inter> ?L2 \<Longrightarrow> x \<in> X \<Longrightarrow> out[?L2,\<pi>,x] = {None} \<union> Some ` Y \<or> is_not_undefined \<pi> L1 \<and> is_not_undefined \<pi> L2 \<and> out[L1,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<subseteq> out[L2,map (\<lambda>(x, y). (x, the y)) \<pi>,x]" 
      proof -
        fix \<pi> x assume "\<pi> \<in> ?L1 \<inter> ?L2" and "x \<in> X"
        then have "\<pi> \<in> ?L1" and "\<pi> \<in> ?L2" by auto

        show "out[?L2,\<pi>,x] = {None} \<union> Some ` Y \<or> is_not_undefined \<pi> L1 \<and> is_not_undefined \<pi> L2 \<and> out[L1,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<noteq> {} \<and> out[L1,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<subseteq> out[L2,map (\<lambda>(x, y). (x, the y)) \<pi>,x]"
        proof (cases "out[?L2,\<pi>,x] = {None} \<union> Some ` Y")
          case True
          then show ?thesis by blast
        next
          case False
          
          let ?\<pi> = "map (\<lambda>(x, y). (x, the y)) \<pi>"
          
          have "is_not_undefined \<pi> L2"
            using False \<open>(\<forall>\<pi> \<in>bottom_completion X Y L1 \<inter> bottom_completion X Y L2. \<forall>x\<in>X. \<not> is_not_undefined \<pi> L1 \<longrightarrow> is_not_undefined \<pi> L2 \<longrightarrow> out[bottom_completion X Y L2,\<pi>,x] = {None} \<union> Some ` Y) \<and> (\<forall>\<pi>\<in>L1 \<inter> L2. \<forall>x\<in>X. out[L2,\<pi>,x] = {} \<or> out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])\<close> \<open>\<pi> \<in> bottom_completion X Y L1 \<inter> bottom_completion X Y L2\<close> \<open>x \<in> X\<close>
            by (meson \<open>\<pi> \<in> bottom_completion X Y L2\<close> assms(2) bottom_completion_out(3))
          then have "?\<pi> \<in> L2" 
            using bottom_id
            by (metis (mono_tags, lifting) imageE is_not_undefined.elims(2)) 

          have "is_not_undefined \<pi> L1"
            using False \<open>(\<forall>\<pi> \<in>bottom_completion X Y L1 \<inter> bottom_completion X Y L2. \<forall>x\<in>X. \<not> is_not_undefined \<pi> L1 \<longrightarrow> is_not_undefined \<pi> L2 \<longrightarrow> out[bottom_completion X Y L2,\<pi>,x] = {None} \<union> Some ` Y) \<and> (\<forall>\<pi>\<in>L1 \<inter> L2. \<forall>x\<in>X. out[L2,\<pi>,x] = {} \<or> out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])\<close> \<open>\<pi> \<in> bottom_completion X Y L1 \<inter> bottom_completion X Y L2\<close> \<open>x \<in> X\<close>
            using \<open>is_not_undefined \<pi> L2\<close> by blast
          then have "?\<pi> \<in> L1" 
            using bottom_id
            by (metis (mono_tags, lifting) imageE is_not_undefined.elims(2))

          have "out[L2,?\<pi>,x] \<noteq> {}"
            using False bottom_completion_out(2)[OF assms(2) \<open>x \<in> X\<close> \<open>\<pi> \<in> ?L2\<close> \<open>is_not_undefined \<pi> L2\<close>] 
            by blast
          then have "out[L1,?\<pi>,x] \<noteq> {}" and "out[L1,?\<pi>,x] \<subseteq> out[L2,?\<pi>,x]"
            using \<open>?B\<close> \<open>?\<pi> \<in> L1\<close> \<open>?\<pi> \<in> L2\<close> \<open>x \<in> X\<close>
            by (meson IntI)+ 
          then show ?thesis 
            using \<open>is_not_undefined \<pi> L1\<close> \<open>is_not_undefined \<pi> L2\<close>
            by blast
        qed 
      qed
      then show ?A
        by blast
    qed
  qed
  also have "\<dots> = ( (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . \<not> is_not_undefined \<pi> L1 \<longrightarrow> is_not_undefined \<pi> L2 \<longrightarrow> out[L2,map (\<lambda>(x, y). (x, the y)) \<pi>,x] = {}) 
                  \<and> (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> X . out[L2,\<pi>,x] = {} \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])))" 
    (is "(?A \<and> ?B) = (?C \<and> ?B)")
  proof -
    have "?A = ?C"
      by (metis IntD2 None_notin_image_Some UnCI assms(2) bottom_completion_out(1) bottom_completion_out(2) insertCI) 
    then show ?thesis by meson
  qed
  also have "\<dots> = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> X . out[L2,\<pi>,x] = {} \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]))" 
    (is "(?A \<and> ?B) = ?B")
  proof -
    have "?B \<Longrightarrow> ?A" 
    proof -
      assume "?B"


      have "\<And> \<pi> x . \<pi> \<in> ?L1 \<inter> ?L2 \<Longrightarrow> x \<in> X \<Longrightarrow> \<not> is_not_undefined \<pi> L1 \<Longrightarrow> is_not_undefined \<pi> L2 \<Longrightarrow> out[L2,map (\<lambda>(x, y). (x, the y)) \<pi>,x] = {}" 
      proof (rule ccontr)
        fix \<pi> x assume "\<pi> \<in> ?L1 \<inter> ?L2" and "x \<in> X" and "\<not> is_not_undefined \<pi> L1"  and "is_not_undefined \<pi> L2" 
                   and "out[L2,map (\<lambda>(x, y). (x, the y)) \<pi>,x] \<noteq> {}"

        let ?\<pi> = "map (\<lambda>(x, y). (x, the y)) \<pi>"
        have "?\<pi> \<in> L2"
          by (metis (mono_tags, lifting) \<open>is_not_undefined \<pi> L2\<close> bottom_id image_iff is_not_undefined.elims(2)) 

        have "\<pi> \<in> ?L1"
          using \<open>\<pi> \<in> ?L1 \<inter> ?L2\<close> by auto
        moreover have "\<pi> \<notin> L1'a"
          unfolding L1'a_def using \<open>\<not> is_not_undefined \<pi> L1\<close> by auto 
        ultimately have "\<pi> \<in> L1'b"
          unfolding \<open>?L1 = L1'a \<union> L1'b\<close> by blast
        then obtain \<pi>' x' y' \<tau> where "\<pi> = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x',y')]@\<tau>"    
                                 and "\<pi>' \<in> L1" 
                                 and "out[L1,\<pi>',x'] = {}" 
                                 and "x' \<in> X" 
                                 and "(y' = None \<or> y' \<in> Some ` Y)" 
                                 and "(\<forall> (x,y) \<in> set \<tau> . x \<in> X \<and> (y = None \<or> y \<in> Some ` Y))"
          unfolding L1'b_def 
          by blast

        have "?\<pi> = (\<pi>'@[(x', the y')]) @ (map (\<lambda>(x, y). (x, the y)) \<tau>)"
          unfolding \<open>\<pi> = (map (\<lambda>(x,y) . (x,Some y)) \<pi>')@[(x',y')]@\<tau>\<close> 
          using bottom_id by (induction \<pi>' arbitrary: x' y' \<tau>; auto)
        then have "\<pi>'@[(x', the y')] \<in> L2" and "\<pi>' \<in> L2"
          using \<open>?\<pi> \<in> L2\<close>
          by (metis assms(2) prefix_closure_no_member)+
        then have "out[L2,\<pi>',x'] \<noteq> {}"
          by fastforce

        show False
          using \<open>?B\<close> \<open>\<pi>' \<in> L1\<close> \<open>\<pi>' \<in> L2\<close> \<open>x' \<in> X\<close> \<open>out[L2,\<pi>',x'] \<noteq> {}\<close> \<open>out[L1,\<pi>',x'] = {}\<close>
          by blast
      qed
      then show ?A
        by blast
    qed
    then show ?thesis by meson
  qed
  also have "\<dots> = (L1 \<preceq>[X,quasired Y] L2)"     
    unfolding quasired_type_1[OF assms, symmetric] quasi_reduction_def
    by (meson assms(2) executable_inputs_in_alphabet outputs_executable) 
  finally show ?thesis 
    by meson
qed


subsection \<open>Strong Reduction via Reduction and Undefinedness Outputs\<close>

fun non_bottom_shortening :: "('x,'y option) word \<Rightarrow> ('x,'y option) word" where
  "non_bottom_shortening \<pi> = filter (\<lambda> (x,y) . y \<noteq> None) \<pi>"

fun non_bottom_projection :: "('x,'y option) word \<Rightarrow> ('x,'y) word" where
  "non_bottom_projection \<pi> = map (\<lambda>(x,y) . (x,the y)) (non_bottom_shortening \<pi>)" 

lemma non_bottom_projection_split: "non_bottom_projection (\<pi>'@\<pi>'') = (non_bottom_projection \<pi>')@(non_bottom_projection \<pi>'')"
  by (induction \<pi>' arbitrary: \<pi>''; auto)

lemma non_bottom_projection_id : "non_bottom_projection (map (\<lambda>(x,y) . (x,Some y)) \<pi>) = \<pi>"
  by (induction \<pi>; auto)


fun undefinedness_completion :: "'x alphabet \<Rightarrow> ('x,'y) language \<Rightarrow> ('x, 'y option) language" where 
  "undefinedness_completion X L = 
    {\<pi> . non_bottom_projection \<pi> \<in> L \<and> (\<forall> \<pi>' x \<pi>'' . \<pi> = \<pi>' @ [(x,None)] @ \<pi>'' \<longrightarrow> x \<in> X \<and> out[L, non_bottom_projection \<pi>', x] = {})}"

lemma undefinedness_completion_is_language :
  assumes "is_language X Y L"
shows "is_language X ({None} \<union> Some ` Y) (undefinedness_completion X L)"
proof -
  let ?L = "undefinedness_completion X L"

  have "[] \<in> L"
    using language_contains_nil[OF assms] .
  moreover have "non_bottom_projection [] = []" 
    by auto
  ultimately have "[] \<in> ?L"
    by simp 
  then have "?L \<noteq> {}"
    by blast
  moreover have "\<And> \<pi> . \<pi> \<in> ?L \<Longrightarrow> (\<And> xy . xy \<in> set \<pi> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y))"
            and "\<And> \<pi> . \<pi> \<in> ?L \<Longrightarrow> (\<And> \<pi>' . prefix \<pi>' \<pi> \<Longrightarrow> \<pi>' \<in> ?L)"
  proof -
    fix \<pi> assume "\<pi> \<in> ?L"
    then have p1: "non_bottom_projection \<pi> \<in> L" 
          and p2: "\<And> \<pi>' x \<pi>'' . \<pi> = \<pi>' @ [(x,None)] @ \<pi>'' \<Longrightarrow> x \<in> X \<and> out[L, non_bottom_projection \<pi>', x] = {}"
      by auto

    show "\<And> xy . xy \<in> set \<pi> \<Longrightarrow> fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y)"
    proof -
      fix xy assume "xy \<in> set \<pi>"
      then obtain \<pi>' x y \<pi>'' where "xy = (x,y)" and "\<pi> = \<pi>' @ [(x,y)] @ \<pi>''"
        by (metis append_Cons append_Nil old.prod.exhaust split_list)  
      

      show "fst xy \<in> X \<and> snd xy \<in> ({None} \<union> Some ` Y)" 
      proof (cases "snd xy")
        case None
        then show ?thesis 
          unfolding \<open>xy = (x,y)\<close> snd_conv
          using p2 \<open>\<pi> = \<pi>' @ [(x,y)] @ \<pi>''\<close>
          by simp 
      next
        case (Some y')
        then have "y = Some y'"
          unfolding \<open>xy = (x,y)\<close> by auto
        have "(x,y') \<in> set (non_bottom_projection \<pi>)"
          unfolding \<open>\<pi> = \<pi>' @ [(x,y)] @ \<pi>''\<close> \<open>y = Some y'\<close>
          by auto
        then show ?thesis 
          unfolding \<open>xy = (x,y)\<close> snd_conv \<open>y = Some y'\<close> fst_conv
          using p1 assms
          unfolding is_language.simps by fastforce
      qed 
    qed

    show "\<And> \<pi>' . prefix \<pi>' \<pi> \<Longrightarrow> \<pi>' \<in> ?L" 
    proof -
      fix \<pi>' assume "prefix \<pi>' \<pi>"
      then obtain \<pi>'' where "\<pi> = \<pi>'@\<pi>''"
        using prefixE by blast

      have "non_bottom_projection \<pi> = (non_bottom_projection \<pi>')@(non_bottom_projection \<pi>'')"
        unfolding \<open>\<pi> = \<pi>'@\<pi>''\<close>
        using non_bottom_projection_split .
      then have "non_bottom_projection \<pi>' \<in> L"
        by (metis assms p1 prefix_closure_no_member) 
      moreover have "\<And> \<pi>''' x \<pi>'''' . \<pi>' = \<pi>''' @ [(x,None)] @ \<pi>'''' \<Longrightarrow> x \<in> X \<and> out[L, non_bottom_projection \<pi>''', x] = {}"
        using p2 unfolding \<open>\<pi> = \<pi>'@\<pi>''\<close>
        by (metis append.assoc) 
      ultimately show "\<pi>' \<in> ?L"
        by fastforce 
    qed
  qed 
  ultimately show ?thesis
    by (meson is_language.elims(3)) 
qed


lemma undefinedness_completion_inclusion :
  assumes "\<pi> \<in> L" 
shows "map (\<lambda>(x,y) . (x,Some y)) \<pi> \<in> undefinedness_completion X L"
proof -
  let ?\<pi> = "map (\<lambda>(x,y) . (x,Some y)) \<pi>"

  have "\<And> a . (a,None) \<notin> set ?\<pi>"
    by (induction \<pi>; auto)
  then have "\<forall> \<pi>' x \<pi>'' . ?\<pi> = \<pi>' @ [(x,None)] @ \<pi>'' \<longrightarrow> x \<in> X \<and> out[L, non_bottom_projection \<pi>', x] = {}"
    by (metis Cons_eq_appendI in_set_conv_decomp) 
  moreover have "non_bottom_projection ?\<pi> \<in> L"
    using \<open>\<pi> \<in> L\<close> unfolding non_bottom_projection_id .
  ultimately show ?thesis 
    by auto 
qed


lemma undefinedness_completion_out_shortening :
  assumes "is_language X Y L"
  and     "\<pi> \<in> undefinedness_completion X L" 
  and     "x \<in> X" 
shows "out[undefinedness_completion X L, \<pi>, x] = out[undefinedness_completion X L, non_bottom_shortening \<pi>, x]" 
using assms(2,3) proof (induction "length \<pi>" arbitrary: \<pi> x rule: less_induct)
  case less

  let ?L = "undefinedness_completion X L"

  show ?case proof (cases \<pi> rule: rev_cases)
    case Nil
    then show ?thesis by auto
  next
    case (snoc \<pi>' xy) 

    then obtain x' y' where "xy = (x',y')" by fastforce
  
    have "x' \<in> X"
      using snoc less.prems(1) unfolding \<open>xy = (x',y')\<close>
      using undefinedness_completion_is_language[OF assms(1)]
      by (metis fst_conv is_language.elims(2) last_in_set snoc_eq_iff_butlast) 
  
    have "\<pi>' \<in> ?L"
      using snoc less.prems(1) 
      using undefinedness_completion_is_language[OF assms(1)]
      using prefix_closure_no_member by blast 

    show ?thesis proof (cases y')
      case None

      then have "non_bottom_shortening \<pi> = non_bottom_shortening \<pi>'" 
        unfolding \<open>xy = (x',y')\<close> snoc by auto
      then have "out[?L, non_bottom_shortening \<pi>, x] = out[?L, non_bottom_shortening \<pi>', x]"
        by simp
      also have "\<dots> = out[?L, \<pi>', x]"
        using less.hyps[OF _ \<open>\<pi>' \<in> ?L\<close> \<open>x \<in> X\<close>] unfolding snoc
        by (metis Suc_lessD length_append_singleton not_less_eq)
      also have "\<dots> = out[?L, \<pi>, x]" 
      proof 

        show "out[?L, \<pi>', x] \<subseteq> out[?L, \<pi>, x]"
        proof 
          fix y assume "y \<in> out[?L, \<pi>', x]"
          then have "\<pi>'@[(x,y)] \<in> ?L"
            by auto
          then have p1: "non_bottom_projection (\<pi>'@[(x,y)]) \<in> L" 
                and p2: "\<And> \<gamma>' a \<gamma>'' . \<pi>'@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}" 
            by auto

          have "non_bottom_projection (\<pi>@[(x,y)]) = non_bottom_projection (\<pi>'@[(x,y)])"
            unfolding snoc \<open>xy = (x',y')\<close> None by auto
          then have "non_bottom_projection (\<pi>@[(x,y)]) \<in> L"
            using p1 by simp
          moreover have "\<And> \<gamma>' a \<gamma>'' . \<pi>@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}"
          proof -
            fix \<gamma>' a \<gamma>'' assume "\<pi>@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''"
            then have "\<pi>'@[(x',None)]@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''"
              unfolding snoc \<open>xy = (x',y')\<close> None by auto

            show "a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}" 
            proof (cases \<gamma>'' rule: rev_cases)
              case Nil
              then show ?thesis
                using \<open>\<pi> @ [(x, y)] = \<gamma>' @ [(a, None)] @ \<gamma>''\<close> \<open>non_bottom_shortening \<pi> = non_bottom_shortening \<pi>'\<close> p2 by auto 
            next
              case (snoc \<gamma>''' xy')
              then show ?thesis
                using \<open>\<pi> @ [(x, y)] = \<gamma>' @ [(a, None)] @ \<gamma>''\<close> less.prems(1) by force 
            qed 
          qed
          ultimately show "y \<in> out[?L, \<pi>, x]"
            by auto
        qed

        show "out[?L, \<pi>, x] \<subseteq> out[?L, \<pi>', x]" 
        proof 
          fix y assume "y \<in> out[?L, \<pi>, x]"
          then have "\<pi>'@[(x',None)]@[(x,y)] \<in> ?L"
            unfolding snoc \<open>xy = (x',y')\<close> None
            by auto
          then have p1: "non_bottom_projection (\<pi>'@[(x',None)]@[(x,y)]) \<in> L" 
                and p2: "\<And> \<gamma>' a \<gamma>'' . \<pi>'@[(x',None)]@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}" 
            by auto

          have "non_bottom_projection (\<pi>'@[(x',None)]@[(x,y)]) = non_bottom_projection (\<pi>'@[(x,y)])"
            by auto
          then have "non_bottom_projection (\<pi>'@[(x,y)]) \<in> L"
            using p1 by auto
          moreover have "\<And> \<gamma>' a \<gamma>'' . \<pi>'@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}"
          proof -
            fix \<gamma>' a \<gamma>'' assume "\<pi>'@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''"

            show "a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}"
            proof (cases \<gamma>'' rule: rev_cases)
              case Nil 
              then show ?thesis
                by (metis None \<open>\<pi>' @ [(x, y)] = \<gamma>' @ [(a, None)] @ \<gamma>''\<close> \<open>non_bottom_shortening \<pi> = non_bottom_shortening \<pi>'\<close> \<open>xy = (x', y')\<close> append.assoc append.right_neutral append1_eq_conv non_bottom_projection.simps p2 snoc) 
            next
              case (snoc \<gamma>''' xy')
              then show ?thesis
                using \<open>\<pi>' @ [(x, y)] = \<gamma>' @ [(a, None)] @ \<gamma>''\<close> \<open>\<pi>' \<in> undefinedness_completion X L\<close> by force                 
            qed
          qed
          ultimately show "y \<in> out[?L, \<pi>', x]" 
            by auto 
        qed
      qed
      finally show ?thesis 
        by blast
    next
      case (Some y'')
      
      have "non_bottom_shortening \<pi> = (non_bottom_shortening \<pi>')@[(x',Some y'')]"
        unfolding snoc \<open>xy = (x',y')\<close> Some by auto
      then have "non_bottom_projection \<pi> = (non_bottom_projection \<pi>')@[(x',y'')]"
        by auto

      have "\<pi>' @ [(x', Some y'')] \<in> ?L" 
        using less.prems(1) unfolding snoc \<open>xy = (x',y')\<close> Some .
      then have "Some y'' \<in> out[?L,\<pi>',x']"
        by auto
      moreover have "out[?L,\<pi>',x'] = out[?L,non_bottom_shortening \<pi>',x']"
        using less.hyps[OF _ \<open>\<pi>' \<in> ?L\<close> \<open>x' \<in> X\<close>]
        unfolding snoc \<open>xy = (x',y')\<close> Some
        by (metis length_append_singleton lessI)
      ultimately have "Some y'' \<in> out[?L,non_bottom_shortening \<pi>',x']"
        by blast


      show ?thesis 
      proof 
        show "out[?L,\<pi>,x] \<subseteq> out[?L,non_bottom_shortening \<pi>,x]"
        proof 
          fix y assume "y \<in> out[?L,\<pi>,x]" 
          then have "\<pi>'@[(x',Some y'')]@[(x,y)] \<in> ?L"
            unfolding snoc \<open>xy = (x',y')\<close> Some by auto
          then have p1: "non_bottom_projection (\<pi>'@[(x',Some y'')]@[(x,y)]) \<in> L" 
                and p2: "\<And> \<gamma>' a \<gamma>'' . \<pi>'@[(x',Some y'')]@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}" 
            by auto

          have "non_bottom_projection ((non_bottom_shortening \<pi>)@[(x,y)]) = non_bottom_projection (\<pi>'@[(x',Some y'')]@[(x,y)])"
            unfolding \<open>non_bottom_shortening \<pi> = (non_bottom_shortening \<pi>')@[(x',Some y'')]\<close>
            by auto
          then have "non_bottom_projection ((non_bottom_shortening \<pi>)@[(x,y)]) \<in> L"
            using p1 by simp
          moreover have "\<And> \<gamma>' a \<gamma>'' . (non_bottom_shortening \<pi>)@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}"
          proof -
            fix \<gamma>' a \<gamma>'' assume "(non_bottom_shortening \<pi>)@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''" 
            moreover have "(a, None) \<notin> set (non_bottom_shortening \<pi>)"
              by (induction \<pi>; auto)
            moreover have "\<And> xs a ys b zs . xs@[a] = ys@[b]@zs \<Longrightarrow> b \<notin> set xs \<Longrightarrow> zs = []" 
              by (metis append_Cons append_Nil butlast.simps(2) butlast_snoc in_set_butlast_appendI list.distinct(1) list.sel(1) list.set_sel(1))
            ultimately have "\<gamma>'' = []"
              by fastforce 
            then have "\<gamma>' = non_bottom_shortening \<pi>"
                  and "x = a"
                  and "y = None"
              using \<open>(non_bottom_shortening \<pi>)@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''\<close>
              by auto


            show "a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}"  
              using \<open>x \<in> X\<close> unfolding \<open>x = a\<close> 
              unfolding \<open>\<gamma>' = non_bottom_shortening \<pi>\<close>
              by (metis (no_types, lifting) \<open>non_bottom_projection (non_bottom_shortening \<pi> @ [(x, y)]) = non_bottom_projection (\<pi>' @ [(x', Some y'')] @ [(x, y)])\<close> \<open>x = a\<close> \<open>y = None\<close> append.assoc append.right_neutral append_same_eq non_bottom_projection_split p2)  
          qed
          ultimately show "y \<in> out[?L,non_bottom_shortening \<pi>,x]"
            by auto
        qed

        show "out[?L,non_bottom_shortening \<pi>,x] \<subseteq> out[?L,\<pi>,x]" 
        proof 
          fix y assume "y \<in> out[?L,non_bottom_shortening \<pi>,x]" 
          then have "(non_bottom_shortening \<pi>')@[(x',Some y'')]@[(x,y)] \<in> ?L"
            unfolding snoc \<open>xy = (x',y')\<close> Some by auto
          then have p1: "non_bottom_projection ((non_bottom_shortening \<pi>')@[(x',Some y'')]@[(x,y)]) \<in> L" 
                and p2: "\<And> \<gamma>' a \<gamma>'' . (non_bottom_shortening \<pi>')@[(x',Some y'')]@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}" 
            by auto

          have "non_bottom_projection ((non_bottom_shortening \<pi>')@[(x',Some y'')]@[(x,y)]) = non_bottom_projection (\<pi>@[(x,y)])"
            unfolding snoc \<open>xy = (x',y')\<close> Some by auto
          then have "non_bottom_projection (\<pi>@[(x,y)]) \<in> L"
            using p1 by presburger 
          moreover have "\<And> \<gamma>' a \<gamma>'' . \<pi>@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>'' \<Longrightarrow> a \<in> X \<and> out[L, non_bottom_projection \<gamma>', a] = {}"
          proof 
            fix \<gamma>' a \<gamma>'' assume "\<pi>@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''" 
            then have "(a,None) \<in> set (\<pi>@[(x,y)])"
              by auto
            then consider "(a,None) \<in> set \<pi>" | "(a,None) = (x,y)"
              by auto              
            then show "a \<in> X"
              by (metis assms(1) fst_conv is_language.elims(2) less.prems(1) less.prems(2) undefinedness_completion_is_language) 

            show "out[L,non_bottom_projection \<gamma>',a] = {}" 
            proof (cases \<gamma>'' rule: rev_cases)
              case Nil
              then have "\<pi> = \<gamma>'" and "x = a" and "y = None"
                using \<open>\<pi>@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''\<close> by auto 
              then show ?thesis
                by (metis (no_types, opaque_lifting) \<open>non_bottom_projection (non_bottom_shortening \<pi>' @ [(x', Some y'')] @ [(x, y)]) = non_bottom_projection (\<pi> @ [(x, y)])\<close> \<open>non_bottom_shortening \<pi> = non_bottom_shortening \<pi>' @ [(x', Some y'')]\<close> append.assoc append_Cons append_Nil append_same_eq non_bottom_projection_split p2)   
            next
              case (snoc \<gamma>''' xy')
              then have "\<pi> = \<gamma>' @ [(a, None)] @ \<gamma>'''"
                using \<open>\<pi>@[(x,y)] = \<gamma>' @ [(a,None)] @ \<gamma>''\<close> by auto

              have "\<gamma>' @ [(a, None)] \<in> ?L"
                using less.prems(1) unfolding \<open>\<pi> = \<gamma>' @ [(a, None)] @ \<gamma>'''\<close> 
                using undefinedness_completion_is_language[OF assms(1)]
                by (metis append_assoc prefix_closure_no_member)
              then show "out[L, non_bottom_projection \<gamma>', a] = {}"
                by auto
            qed
          qed
          ultimately show "y \<in> out[?L,\<pi>,x]"
            by auto
        qed
      qed
    qed
  qed
qed



lemma undefinedness_completion_out_projection_not_empty :
  assumes "is_language X Y L"
  and     "\<pi> \<in> undefinedness_completion X L" 
  and     "x \<in> X" 
  and     "out[L, non_bottom_projection \<pi>, x] \<noteq> {}"
shows "out[undefinedness_completion X L, non_bottom_shortening \<pi>, x] = Some ` out[L, non_bottom_projection \<pi>, x]" 
proof 
  
  let ?L = "undefinedness_completion X L"

  have "\<pi>@[(x,None)] \<notin> ?L" 
    using assms(4) by auto
  then have "None \<notin> out[?L,\<pi>,x]"
    by auto
  then have "None \<notin> out[?L,non_bottom_shortening \<pi>,x]"
    using undefinedness_completion_out_shortening[OF assms(1,2,3)] by blast
  then have "(non_bottom_shortening \<pi>)@[(x,None)] \<notin> ?L"
    by auto

  show "out[?L, non_bottom_shortening \<pi>, x] \<subseteq> Some ` out[L, non_bottom_projection \<pi>, x]" 
  proof 
    fix y assume "y \<in> out[?L, non_bottom_shortening \<pi>, x]"
    then have "(non_bottom_shortening \<pi>) @ [(x,y)] \<in> ?L" by auto
    then have "y \<noteq> None" 
      using \<open>(non_bottom_shortening \<pi>)@[(x,None)] \<notin> ?L\<close>
      by meson 
    then obtain y' where "y = Some y'"
      by auto 

    have "non_bottom_projection ((non_bottom_shortening \<pi>) @ [(x,y)]) = (non_bottom_projection \<pi>) @ [(x,y')]"
      unfolding \<open>y = Some y'\<close> 
      by (induction \<pi>; auto)
    then have "(non_bottom_projection \<pi>) @ [(x,y')] \<in> L"
      using \<open>(non_bottom_shortening \<pi>) @ [(x,y)] \<in> ?L\<close> unfolding \<open>y = Some y'\<close> 
      by auto
    then show "y \<in> Some ` out[L, non_bottom_projection \<pi>, x]" 
      unfolding \<open>y = Some y'\<close> by auto
  qed

  show "Some ` out[L,non_bottom_projection \<pi>,x] \<subseteq> out[?L,non_bottom_shortening \<pi>,x]" 
  proof 
    fix y assume "y \<in> Some ` out[L,non_bottom_projection \<pi>,x]"
    then obtain y' where "y = Some y'" and "y' \<in> out[L,non_bottom_projection \<pi>,x]"
      by auto
    then have "(non_bottom_projection \<pi>) @ [(x,y')] \<in> L"
      by auto
    moreover have "non_bottom_projection ((non_bottom_shortening \<pi>) @ [(x,y)]) = (non_bottom_projection \<pi>) @ [(x,y')]"
      unfolding \<open>y = Some y'\<close> 
      by (induction \<pi>; auto)
    ultimately have "non_bottom_projection ((non_bottom_shortening \<pi>) @ [(x,y)]) \<in> L"
      unfolding \<open>y = Some y'\<close>  
      by auto
    moreover have "\<And> \<pi>' x' \<pi>'' . ((non_bottom_shortening \<pi>) @ [(x,y)]) = \<pi>' @ [(x',None)] @ \<pi>'' \<Longrightarrow> x' \<in> X \<and> out[L, non_bottom_projection \<pi>', x'] = {}"
    proof -
      fix \<pi>' x' \<pi>'' assume "((non_bottom_shortening \<pi>) @ [(x,y)]) = \<pi>' @ [(x',None)] @ \<pi>''"
      then have "(x',None) \<in> set (non_bottom_shortening \<pi>)"
        by (metis \<open>y = Some y'\<close> append_Cons in_set_conv_decomp old.prod.inject option.distinct(1) rotate1.simps(2) set_ConsD set_rotate1) 
      then have False 
        by (induction \<pi>; auto)
      then show "x' \<in> X \<and> out[L, non_bottom_projection \<pi>', x'] = {}"
        by blast
    qed
    ultimately show "y \<in> out[?L,non_bottom_shortening \<pi>,x]"
      by auto
  qed
qed


lemma undefinedness_completion_out_projection_empty :
  assumes "is_language X Y L"
  and     "\<pi> \<in> undefinedness_completion X L" 
  and     "x \<in> X" 
  and     "out[L, non_bottom_projection \<pi>, x] = {}"
shows "out[undefinedness_completion X L, non_bottom_shortening \<pi>, x] = {None}" 
proof 
  
  let ?L = "undefinedness_completion X L"

  have p1: "non_bottom_projection \<pi> \<in> L" 
   and p2: "\<And> \<pi>' x \<pi>'' . \<pi> = \<pi>' @ [(x,None)] @ \<pi>'' \<Longrightarrow> x \<in> X \<and> out[L, non_bottom_projection \<pi>', x] = {}"
    using assms(2) by auto

  have "non_bottom_projection (\<pi>@[(x,None)]) \<in> L"
    using p1 by auto
  moreover have "\<And> \<pi>' x' \<pi>'' . \<pi>@[(x,None)] = \<pi>' @ [(x',None)] @ \<pi>'' \<Longrightarrow> x' \<in> X \<and> out[L, non_bottom_projection \<pi>', x'] = {}"
  proof -
    fix \<pi>' x' \<pi>'' assume "\<pi>@[(x,None)] = \<pi>' @ [(x',None)] @ \<pi>''"
    show "x' \<in> X \<and> out[L, non_bottom_projection \<pi>', x'] = {}"
    proof (cases \<pi>'' rule: rev_cases)
      case Nil
      then show ?thesis
        using \<open>\<pi> @ [(x, None)] = \<pi>' @ [(x', None)] @ \<pi>''\<close> assms(3) assms(4) by auto
    next
      case (snoc ys y)
      then show ?thesis
        using \<open>\<pi> @ [(x, None)] = \<pi>' @ [(x', None)] @ \<pi>''\<close> p2 by auto
    qed 
  qed
  ultimately have "\<pi>@[(x,None)] \<in> ?L"
    by auto
  then show "{None} \<subseteq> out[?L,non_bottom_shortening \<pi>,x]"
    unfolding undefinedness_completion_out_shortening[OF assms(1,2,3), symmetric] 
    by auto

  show "out[?L,non_bottom_shortening \<pi>,x] \<subseteq> {None}" 
  proof (rule ccontr) 
    assume "\<not> out[?L,non_bottom_shortening \<pi>,x] \<subseteq> {None}"    
    then obtain y where "y \<in> out[?L,non_bottom_shortening \<pi>,x]"  and "y \<noteq> None"
      by blast 
    then obtain y' where "y = Some y'"
      by auto

    have "\<pi>@[(x,Some y')] \<in> ?L" 
      using \<open>y \<in> out[?L,non_bottom_shortening \<pi>,x]\<close>
      unfolding \<open>y = Some y'\<close>
      unfolding undefinedness_completion_out_shortening[OF assms(1,2,3), symmetric] 
      by auto
    then have "(non_bottom_projection \<pi>)@[(x,y')] \<in> L"
      by auto
    then show False
      using assms(4) by auto
  qed
qed


theorem strongred_via_red : 
  assumes "is_language X Y L1"
  and     "is_language X Y L2"
shows "(L1 \<preceq>[X,strongred Y] L2) \<longleftrightarrow> ((undefinedness_completion X L1) \<preceq>[X, red ({None} \<union> Some ` Y)] (undefinedness_completion X L2))" 
proof -

  let ?L1 = "undefinedness_completion X L1"
  let ?L2 = "undefinedness_completion X L2"

  have "(L1 \<preceq>[X,strongred Y] L2) = (\<forall> \<pi> \<in> L1 \<inter> L2 . \<forall> x \<in> X . (out[L1,\<pi>,x] = {} \<and> out[L2,\<pi>,x] = {}) \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x]))"
    (is "?A = ?B")
  proof 
    show "?A \<Longrightarrow> ?B" 
      unfolding strongred_type_1[OF assms, symmetric] strong_reduction_def quasi_reduction_def
      by (metis outputs_executable)
    show "?B \<Longrightarrow> ?A" 
      unfolding strongred_type_1[OF assms, symmetric] strong_reduction_def quasi_reduction_def
      by (metis assms(1) assms(2) executable_inputs_in_alphabet outputs_executable subset_empty)
  qed
  also have "\<dots> = (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . (out[L1,non_bottom_projection \<pi>,x] = {} \<and> out[L2,non_bottom_projection \<pi>,x] = {}) \<or> (out[L1,non_bottom_projection \<pi>,x] \<noteq> {} \<and> out[L1,non_bottom_projection \<pi>,x] \<subseteq> out[L2,non_bottom_projection \<pi>,x]))"
    (is "?A = ?B")
  proof 
    have "\<And> \<pi> x . ?A \<Longrightarrow> \<pi> \<in> ?L1 \<inter> ?L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,non_bottom_projection \<pi>,x] = {} \<and> out[L2,non_bottom_projection \<pi>,x] = {}) \<or> (out[L1,non_bottom_projection \<pi>,x] \<noteq> {} \<and> out[L1,non_bottom_projection \<pi>,x] \<subseteq> out[L2,non_bottom_projection \<pi>,x])"
    proof -
      fix \<pi> x assume "?A" and "\<pi> \<in> ?L1 \<inter> ?L2" and "x \<in> X"

      let ?\<pi> = "non_bottom_projection \<pi>"

      have "?\<pi> \<in> L1"
       and "?\<pi> \<in> L2"
        using \<open>\<pi> \<in> ?L1 \<inter> ?L2\<close> by auto
      then show "(out[L1,?\<pi>,x] = {} \<and> out[L2,?\<pi>,x] = {}) \<or> (out[L1,?\<pi>,x] \<noteq> {} \<and> out[L1,?\<pi>,x] \<subseteq> out[L2,?\<pi>,x])"
        using \<open>?A\<close> \<open>x \<in> X\<close> by blast
    qed
    then show "?A \<Longrightarrow> ?B" 
      by blast

    have "\<And> \<pi> x . ?B \<Longrightarrow> \<pi> \<in> L1 \<inter> L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,\<pi>,x] = {} \<and> out[L2,\<pi>,x] = {}) \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])"
    proof -
      fix \<pi> x assume "?B" and "\<pi> \<in> L1 \<inter> L2" and "x \<in> X"

      let ?\<pi> = "map (\<lambda>(x,y) . (x,Some y)) \<pi>"

      have "?\<pi> \<in> ?L1" and "?\<pi> \<in> ?L2" 
        using \<open>\<pi> \<in> L1 \<inter> L2\<close> undefinedness_completion_inclusion by blast+
      then have "(out[L1,non_bottom_projection ?\<pi>,x] = {} \<and> out[L2,non_bottom_projection ?\<pi>,x] = {}) \<or> (out[L1,non_bottom_projection ?\<pi>,x] \<noteq> {} \<and> out[L1,non_bottom_projection ?\<pi>,x] \<subseteq> out[L2,non_bottom_projection ?\<pi>,x])"
        using \<open>?B\<close> \<open>x \<in> X\<close> by blast 
      then show "(out[L1,\<pi>,x] = {} \<and> out[L2,\<pi>,x] = {}) \<or> (out[L1,\<pi>,x] \<noteq> {} \<and> out[L1,\<pi>,x] \<subseteq> out[L2,\<pi>,x])"
        unfolding non_bottom_projection_id .
    qed
    then show "?B \<Longrightarrow> ?A"
      by blast
  qed
  also have "\<dots> = (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . (out[?L1,\<pi>,x] = {None} \<and> out[?L2,\<pi>,x] = {None}) \<or> (out[?L1,\<pi>,x] \<noteq> {None} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x]))"
  proof -
    have "\<And> \<pi> x . \<pi> \<in> ?L1 \<inter> ?L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,non_bottom_projection \<pi>,x] = {} \<and> out[L2,non_bottom_projection \<pi>,x] = {}) = (out[?L1,\<pi>,x] = {None} \<and> out[?L2,\<pi>,x] = {None})"
      by (metis IntD1 IntD2 None_notin_image_Some assms(1) assms(2) insertCI undefinedness_completion_out_projection_empty undefinedness_completion_out_projection_not_empty undefinedness_completion_out_shortening)
    moreover have "\<And> \<pi> x . \<pi> \<in> ?L1 \<inter> ?L2 \<Longrightarrow> x \<in> X \<Longrightarrow> (out[L1,non_bottom_projection \<pi>,x] \<noteq> {} \<and> out[L1,non_bottom_projection \<pi>,x] \<subseteq> out[L2,non_bottom_projection \<pi>,x]) = (out[?L1,\<pi>,x] \<noteq> {None} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x])"
    proof - 
      fix \<pi> x assume "\<pi> \<in> ?L1 \<inter> ?L2" and "x \<in> X" 
      then have "\<pi> \<in> ?L1" and "\<pi> \<in> ?L2" by auto

      have "(out[L1,non_bottom_projection \<pi>,x] \<noteq> {}) = (out[?L1,\<pi>,x] \<noteq> {None})"
        by (metis None_notin_image_Some \<open>\<pi> \<in> undefinedness_completion X L1\<close> \<open>x \<in> X\<close> assms(1) singletonI undefinedness_completion_out_projection_empty undefinedness_completion_out_projection_not_empty undefinedness_completion_out_shortening)


      show "(out[L1,non_bottom_projection \<pi>,x] \<noteq> {} \<and> out[L1,non_bottom_projection \<pi>,x] \<subseteq> out[L2,non_bottom_projection \<pi>,x]) = (out[?L1,\<pi>,x] \<noteq> {None} \<and> out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x])"
      proof (cases "out[L1,non_bottom_projection \<pi>,x] \<noteq> {}")
        case False
        then show ?thesis using \<open>(out[L1,non_bottom_projection \<pi>,x] \<noteq> {}) = (out[?L1,\<pi>,x] \<noteq> {None})\<close> by blast
      next
        case True
        have "out[undefinedness_completion X L1,\<pi>,x] = Some ` out[L1,non_bottom_projection \<pi>,x]"
          using undefinedness_completion_out_projection_not_empty[OF assms(1) \<open>\<pi> \<in> ?L1\<close> \<open>x \<in> X\<close> True]
          unfolding undefinedness_completion_out_shortening[OF assms(1) \<open>\<pi> \<in> ?L1\<close> \<open>x \<in> X\<close>,symmetric] .

        
        show ?thesis proof (cases "out[L2,non_bottom_projection \<pi>,x] = {}")
          case True
          then show ?thesis
            by (metis \<open>(out[L1,non_bottom_projection \<pi>,x] \<noteq> {}) = (out[undefinedness_completion X L1,\<pi>,x] \<noteq> {None})\<close> \<open>\<pi> \<in> undefinedness_completion X L2\<close> \<open>out[undefinedness_completion X L1,\<pi>,x] = Some ` out[L1,non_bottom_projection \<pi>,x]\<close> \<open>x \<in> X\<close> assms(2) image_is_empty subset_empty subset_singletonD undefinedness_completion_out_projection_empty undefinedness_completion_out_shortening)   
        next
          case False

          have "out[undefinedness_completion X L2,\<pi>,x] = Some ` out[L2,non_bottom_projection \<pi>,x]"
            using undefinedness_completion_out_projection_not_empty[OF assms(2) \<open>\<pi> \<in> ?L2\<close> \<open>x \<in> X\<close> False]
            unfolding undefinedness_completion_out_shortening[OF assms(2) \<open>\<pi> \<in> ?L2\<close> \<open>x \<in> X\<close>,symmetric] .

          show ?thesis 
            unfolding \<open>out[undefinedness_completion X L1,\<pi>,x] = Some ` out[L1,non_bottom_projection \<pi>,x]\<close> 
            unfolding \<open>out[undefinedness_completion X L2,\<pi>,x] = Some ` out[L2,non_bottom_projection \<pi>,x]\<close>
            by (metis \<open>(out[L1,non_bottom_projection \<pi>,x] \<noteq> {}) = (out[undefinedness_completion X L1,\<pi>,x] \<noteq> {None})\<close> \<open>out[undefinedness_completion X L1,\<pi>,x] = Some ` out[L1,non_bottom_projection \<pi>,x]\<close> subset_image_iff these_image_Some_eq)            
        qed 
      qed 
    qed
    ultimately show ?thesis
      by meson
  qed
  also have "\<dots> = (\<forall> \<pi> \<in> ?L1 \<inter> ?L2 . \<forall> x \<in> X . out[?L1,\<pi>,x] \<subseteq> out[?L2,\<pi>,x])" 
    (is "?A = ?B")
  proof
    show "?A \<Longrightarrow> ?B"
      by blast 
    show "?B \<Longrightarrow> ?A"
      by (metis IntD2 None_notin_image_Some assms(2) insert_subset undefinedness_completion_out_projection_empty undefinedness_completion_out_projection_not_empty undefinedness_completion_out_shortening) 
  qed
  also have "\<dots> = (?L1 \<preceq>[X, red ({None} \<union> Some ` Y)] ?L2)"
    unfolding type_1_conforms.simps red.simps
    using outputs_in_alphabet[OF undefinedness_completion_is_language[OF assms(2)]]
    by force
  finally show ?thesis .
qed


end 