theory Untyped_Calculus
  imports Nonground_Typing_Generic
begin

abbreviation remove_types :: "('a, 'v, 'ty) typed_clause inference \<Rightarrow> 'a clause inference" where
  "remove_types \<iota> \<equiv> Infer (map snd (prems_of \<iota>)) (snd (concl_of \<iota>))"

abbreviation empty_typed :: "'C \<Rightarrow> (('v \<Rightarrow> unit) \<times> 'C)" where
  "empty_typed C \<equiv> ((\<lambda>_. ()), C)"

abbreviation empty_typed_inference :: "'C inference \<Rightarrow> (('v \<Rightarrow> unit) \<times> 'C) inference" where
  "empty_typed_inference \<iota> \<equiv> Infer (map empty_typed (prems_of \<iota>)) (empty_typed (concl_of \<iota>))"

lemma comp_empty_typed_snd [simp]: "empty_typed \<circ> snd = id"
  by fastforce

lemma empty_typed_snd [simp]: "empty_typed (snd C) = C"
  by (cases C) auto

lemma remove_types [simp]:
  "\<And>inference. remove_types ` { Infer [(\<V>, D)] (\<V>', C) |\<V> D \<V>' C. inference D C} = 
               { Infer [D] C | D C. inference D C}"
  "\<And>inference. 
      remove_types ` { Infer [(\<V>, D), (\<V>', E)] (\<V>'', C) |\<V> D \<V>' E \<V>'' C. inference D E C} = 
      { Infer [D, E] C | D E C. inference D E C}"
  by force+

lemma \<V>_all_same [simp]:
  fixes \<V> :: "'v \<Rightarrow> unit"
  shows "\<V> = (\<lambda>_. ())"
  by auto

lemma all_infinite_variables_per_type [intro]:
  fixes \<V> :: "'v :: infinite \<Rightarrow> unit"
  shows "infinite_variables_per_type_on X \<V>"
  unfolding infinite_variables_per_type_on_def
  using infinite_UNIV
  by auto

locale untyped_consequence_relation = 
  typed: consequence_relation where Bot = typed_bottom and entails = typed_entails
for 
  typed_bottom :: "('a, 'v, unit) typed_clause set" ("\<bottom>\<^sub>\<tau>") and 
  typed_entails (infix \<open>\<Turnstile>\<^sub>\<tau>\<close> 50) +
fixes 
  bottom ("\<bottom>\<^sub>N") and 
  entails (infix \<open>\<Turnstile>\<close> 50)
defines 
  "bottom \<equiv> snd ` typed_bottom" and
  "\<And>N N'. entails N N' \<equiv> empty_typed ` N \<Turnstile>\<^sub>\<tau> empty_typed ` N'"
begin

sublocale consequence_relation where Bot = "\<bottom>\<^sub>N"
proof unfold_locales
  show "\<bottom>\<^sub>N \<noteq> {}"
    by (simp add: typed.bot_not_empty bottom_def)
next
  fix B N
  assume "B \<in> \<bottom>\<^sub>N"

  then show "{B} \<Turnstile> N"
    using typed.bot_entails_all
    unfolding entails_def bottom_def
    by fastforce
next
  fix N N' :: "'a clause set"
  assume "N \<subseteq> N'" 

  then show "N' \<Turnstile> N"
    using typed.subset_entailed
    unfolding entails_def
    by (simp add: image_mono)
next
  fix N N' :: "'a clause set"
  assume "\<forall>C\<in>N'. N \<Turnstile> {C}"

  then have "\<forall>C\<in> empty_typed ` N'. empty_typed ` N  \<Turnstile>\<^sub>\<tau> {C} "
    unfolding entails_def
    by auto

  then show "N \<Turnstile> N'"
    unfolding entails_def
    by (rule typed.all_formulas_entailed)
next
  fix N\<^sub>1 N\<^sub>2 N\<^sub>3 :: "'a clause set"
  assume "N\<^sub>1 \<Turnstile> N\<^sub>2" "N\<^sub>2 \<Turnstile> N\<^sub>3"

  then show "N\<^sub>1 \<Turnstile> N\<^sub>3"
    unfolding entails_def
    by (rule typed.entails_trans)
qed

end

locale untyped_inference_system =
  typed: inference_system where Inf = typed_inferences
for typed_inferences :: "('a, 'v, unit) typed_clause inference set" +
fixes inferences 
defines "inferences \<equiv> remove_types ` typed_inferences"
begin

sublocale inference_system inferences .

end

locale untyped_sound_inference_system = 
  untyped_inference_system + 
  untyped_consequence_relation +
  typed: sound_inference_system where
  Inf = typed_inferences and Bot = typed_bottom and entails = typed_entails
begin

sublocale sound_inference_system where Inf = inferences and Bot = "\<bottom>\<^sub>N"
proof unfold_locales
  fix \<iota>
  assume "\<iota> \<in> inferences"

  then have "empty_typed_inference \<iota> \<in> typed_inferences"
    unfolding inferences_def
    by auto

  then have "set (prems_of (empty_typed_inference \<iota>)) \<Turnstile>\<^sub>\<tau> {concl_of (empty_typed_inference \<iota>)}"
    by (rule typed.sound)

  then show "set (prems_of \<iota>) \<Turnstile> {concl_of \<iota>}"
    unfolding entails_def
    by auto
qed

end

locale untyped_calculus = 
  typed: calculus where
  Inf = typed_inferences and Bot = typed_bottom and entails = typed_entails and
  Red_I = typed_Red_I and Red_F = typed_Red_F +
  untyped_consequence_relation +
  untyped_inference_system
for 
  typed_Red_I and
  typed_Red_F :: "('a, 'v, unit) typed_clause set \<Rightarrow> ('a, 'v, unit) typed_clause set" +
fixes
  Red_I and
  Red_F
defines
  "\<And>N. Red_F N \<equiv> snd ` typed_Red_F (empty_typed ` N)" and
  "\<And>N. Red_I N \<equiv> remove_types ` typed_Red_I (empty_typed ` N)"
begin

sublocale calculus where Inf = inferences and Bot = "\<bottom>\<^sub>N"
proof unfold_locales
  fix N 
  show "Red_I N \<subseteq> inferences"
    unfolding inferences_def Red_I_def
    using typed.Red_I_to_Inf
    by auto
next
  fix B N
  assume "B \<in> \<bottom>\<^sub>N" "N \<Turnstile> {B}"

  moreover have 
    "empty_typed ` N - typed_Red_F (empty_typed ` N) =
     empty_typed ` (N - snd ` typed_Red_F (empty_typed ` N))"
  proof (intro equalityI subsetI)
    fix C
    assume "C \<in> empty_typed ` N - typed_Red_F (empty_typed ` N)"

    then show "C \<in> empty_typed ` (N - snd ` typed_Red_F (empty_typed ` N))"
      by (smt (verit, del_insts) Diff_iff image_iff empty_typed_snd)
  next
    fix C :: "('a, 'v, unit) typed_clause"
    assume "C \<in> empty_typed ` (N - snd ` typed_Red_F (empty_typed ` N))"

    then show "C \<in> empty_typed ` N - typed_Red_F (empty_typed ` N)"
      by force
  qed

  ultimately show "N - Red_F N \<Turnstile> {B}"
    using typed.Red_F_Bot
    unfolding Red_F_def bottom_def entails_def
    by (metis (no_types, lifting) ext imageE image_empty image_insert empty_typed_snd)
next
  fix N N' :: "'a clause set"
  assume "N \<subseteq> N'"

  then show "Red_F N \<subseteq> Red_F N'"
    unfolding Red_F_def
    using typed.Red_F_of_subset
    by (meson image_mono)
next
  fix N N' :: "'a clause set"
  assume "N \<subseteq> N'"

  then show "Red_I N \<subseteq> Red_I N'"
    unfolding Red_I_def
    using typed.Red_I_of_subset
    by (meson subset_image_iff)
next
  fix N N' :: "'a clause set"
  assume "N' \<subseteq> Red_F N"

  then have  "typed_Red_F (empty_typed ` N) \<subseteq> typed_Red_F (empty_typed ` N - empty_typed ` N')"
    using typed.Red_F_of_Red_F_subset
    unfolding Red_F_def
    by (smt (verit, best) image_iff empty_typed_snd subset_iff)

  then show "Red_F N \<subseteq> Red_F (N - N')"
    unfolding Red_F_def
    by (metis (no_types, lifting) Diff_subset image_Un image_diff_subset subset_Un_eq 
        subset_antisym typed.Red_F_of_subset)
next
  fix N N' :: "'a clause set"
  assume "N' \<subseteq> Red_F N"

  then show "Red_I N \<subseteq> Red_I (N - N')"
    unfolding Red_I_def Red_F_def
    using typed.Red_I_of_Red_F_subset
    by (smt (verit, del_insts) imageE image_Un image_diff_subset empty_typed_snd subset_Un_eq subset_iff
        typed.Red_I_of_subset)
next
  fix \<iota> N
  assume "\<iota> \<in> inferences" "concl_of \<iota> \<in> N"
  then show "\<iota> \<in> Red_I N"
    unfolding inferences_def Red_I_def
    using typed.Red_I_of_Inf_to_N
    by (smt (verit) inference.exhaust_sel inference.inject image_iff empty_typed_snd)
qed

end

locale untyped_complete_calculus = 
  untyped_calculus + 
  typed: statically_complete_calculus where
  Inf = typed_inferences and Bot = typed_bottom and entails = typed_entails and
  Red_I = typed_Red_I and Red_F = typed_Red_F
begin

sublocale statically_complete_calculus where Inf = inferences and Bot = "\<bottom>\<^sub>N"
proof unfold_locales
  fix B N
  assume bottom: "B \<in> \<bottom>\<^sub>N" and entails: "N \<Turnstile> {B}" and saturated: "saturated N" 

  have "empty_typed B \<in> \<bottom>\<^sub>\<tau>" 
    using bottom
    unfolding bottom_def image_iff
    by (metis empty_typed_snd)

  moreover have "empty_typed ` N \<Turnstile>\<^sub>\<tau> {empty_typed B}"
    using entails
    unfolding entails_def
    by simp

  moreover have "typed.Inf_from (empty_typed ` N) = empty_typed_inference ` Inf_from N"
    unfolding typed.Inf_from_def Inf_from_def 
    unfolding inferences_def
    by force

  then have "typed.saturated (empty_typed ` N)"
    using saturated
    unfolding typed.saturated_def saturated_def Red_I_def
    by auto

  ultimately show "\<exists>B'\<in>\<bottom>\<^sub>N. B' \<in> N"
    using typed.statically_complete
    unfolding bottom_def
    by force
qed

end

end
