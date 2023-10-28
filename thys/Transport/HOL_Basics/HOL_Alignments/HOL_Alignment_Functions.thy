\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Definitions from HOL.Main\<close>
theory HOL_Alignment_Functions
  imports
    HOL_Alignment_Binary_Relations
    HOL_Syntax_Bundles_Functions
    LFunctions
begin

unbundle no_HOL_function_syntax

named_theorems HOL_fun_alignment

paragraph \<open>Functions\<close>

subparagraph \<open>Bijection\<close>

overloading
  bijection_on_set \<equiv> "bijection_on :: 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "bijection_on_set (S :: 'a set) (S' :: 'b set) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv>
    bijection_on (mem_of S) (mem_of S')"
end

lemma bijection_on_set_eq_bijection_on_pred [simp]:
  "(bijection_on (S :: 'a set) (S' :: 'b set) :: ('a \<Rightarrow> 'b) \<Rightarrow> _) =
    bijection_on (mem_of S) (mem_of S')"
  unfolding bijection_on_set_def by simp

lemma bijection_on_set_iff_bijection_on_pred [iff]:
  "bijection_on (S :: 'a set) (S' :: 'b set) (f :: 'a \<Rightarrow> 'b) g \<longleftrightarrow>
    bijection_on (mem_of S) (mem_of S') f g"
  by simp

lemma bij_betw_bijection_onE:
  assumes "bij_betw f S S'"
  obtains g where "bijection_on S S' f g"
proof
  let ?g = "the_inv_into S f"
  from assms bij_betw_the_inv_into have "bij_betw ?g S' S" by blast
  with assms show "bijection_on S S' f ?g"
    by (auto intro!: bijection_onI
      dest: bij_betw_apply bij_betw_imp_inj_on the_inv_into_f_f
      simp: f_the_inv_into_f_bij_betw)
qed

lemma bij_betw_if_bijection_on:
  assumes "bijection_on S S' f g"
  shows "bij_betw f S S'"
  using assms by (intro bij_betw_byWitness[where ?f'=g])
  (auto elim: bijection_onE dest: inverse_onD)

corollary bij_betw_iff_ex_bijection_on [HOL_fun_alignment]:
  "bij_betw f S S' \<longleftrightarrow> (\<exists>g. bijection_on S S' f g)"
  by (intro iffI)
  (auto elim!: bij_betw_bijection_onE intro: bij_betw_if_bijection_on)


subparagraph \<open>Injective\<close>

overloading
  injective_on_set \<equiv> "injective_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "injective_on_set (S :: 'a set) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv>
    injective_on (mem_of S)"
end

lemma injective_on_set_eq_injective_on_pred [simp]:
  "(injective_on (S :: 'a set) :: ('a \<Rightarrow> 'b) \<Rightarrow> _) = injective_on (mem_of S)"
  unfolding injective_on_set_def by simp

lemma injective_on_set_iff_injective_on_pred [iff]:
  "injective_on (S :: 'a set) (f :: 'a \<Rightarrow> 'b) \<longleftrightarrow> injective_on (mem_of S) f"
  by simp

lemma inj_on_iff_injective_on [HOL_fun_alignment]: "inj_on f P \<longleftrightarrow> injective_on P f"
  by (auto intro: inj_onI dest: inj_onD injective_onD)

lemma inj_eq_injective [HOL_fun_alignment]: "inj = injective"
  by (auto intro: injI dest: injD injectiveD)


subparagraph \<open>Inverse\<close>

overloading
  inverse_on_set \<equiv> "inverse_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inverse_on_set (S :: 'a set) :: ('a \<Rightarrow> 'b) \<Rightarrow> _ \<equiv>
    inverse_on (mem_of S)"
end

lemma inverse_on_set_eq_inverse_on_pred [simp]:
  "(inverse_on (S :: 'a set) :: ('a \<Rightarrow> 'b) \<Rightarrow> _) = inverse_on (mem_of S)"
  unfolding inverse_on_set_def by simp

lemma inverse_on_set_iff_inverse_on_pred [iff]:
  "inverse_on (S :: 'a set) (f :: 'a \<Rightarrow> 'b) g \<longleftrightarrow> inverse_on (mem_of S) f g"
  by simp


subparagraph \<open>Monotone\<close>

lemma monotone_on_eq_mono_wrt_rel_restrict_left_right [HOL_fun_alignment]:
  "monotone_on S R = mono_wrt_rel (R\<restriction>\<^bsub>S\<^esub>\<upharpoonleft>\<^bsub>S\<^esub>)"
  unfolding restrict_right_eq
  by (intro ext) (blast intro: monotone_onI dest: monotone_onD)

lemma monotone_eq_mono_wrt_rel [HOL_fun_alignment]: "monotone = mono_wrt_rel"
  by (intro ext) (auto intro: monotoneI dest: monotoneD)

lemma pred_fun_eq_mono_wrt_pred [HOL_fun_alignment]: "pred_fun = mono_wrt_pred"
  by (intro ext) auto

lemma Fun_mono_eq_mono [HOL_fun_alignment]: "Fun.mono = mono"
  by (intro ext) (auto intro: Fun.mono_onI dest: Fun.monoD)

lemma Fun_antimono_eq_antimono [HOL_fun_alignment]: "Fun.antimono = antimono"
  by (intro ext) (auto intro: monotoneI dest: monotoneD)


subparagraph \<open>Surjective\<close>

overloading
  surjective_at_set \<equiv> "surjective_at :: 'a set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "surjective_at_set (S :: 'a set) :: ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv>
    surjective_at (mem_of S)"
end

lemma surjective_at_set_eq_surjective_at_pred [simp]:
  "(surjective_at (S :: 'a set) :: ('b \<Rightarrow> 'a) \<Rightarrow> _) = surjective_at (mem_of S)"
  unfolding surjective_at_set_def by simp

lemma surjective_at_set_iff_surjective_at_pred [iff]:
  "surjective_at (S :: 'a set) (f :: 'b \<Rightarrow> 'a) \<longleftrightarrow> surjective_at (mem_of S) f"
  by simp

lemma surj_eq_surjective [HOL_fun_alignment]: "surj = surjective"
  by (intro ext) (fast intro: surjI dest: surjD elim: surjectiveE)


paragraph \<open>Functions\<close>

lemma Fun_id_eq_id [HOL_fun_alignment]: "Fun.id = Functions_Base.id"
  by (intro ext) simp

lemma Fun_comp_eq_comp [HOL_fun_alignment]: "Fun.comp = Functions_Base.comp"
  by (intro ext) simp

lemma map_fun_eq_fun_map [HOL_fun_alignment]: "map_fun = fun_map"
  by (intro ext) simp


paragraph \<open>Relators\<close>

lemma rel_fun_eq_Fun_Rel_rel [HOL_fun_alignment]: "rel_fun = Fun_Rel_rel"
  by (intro ext) (auto dest: rel_funD)



end