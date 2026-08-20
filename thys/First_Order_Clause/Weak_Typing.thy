theory Weak_Typing
  imports Typing 
begin

locale weakly_welltyped = typing where welltyped = welltyped
for
  welltyped :: "'expr \<Rightarrow> 'ty \<Rightarrow> bool" and
  weakly_welltyped :: "'expr \<Rightarrow> bool" +
assumes
  weakly_welltyped_if_welltyped [intro]: "\<And>expr. \<exists>\<tau>. welltyped expr \<tau> \<Longrightarrow> weakly_welltyped expr"
  
locale weakly_welltyped_base = typing_lifting
begin

definition weakly_welltyped where
  "weakly_welltyped expr \<equiv>
    \<forall>\<tau>. \<forall>sub \<in> to_set expr. \<forall>sub' \<in> to_set expr. sub_welltyped sub \<tau> \<longleftrightarrow> sub_welltyped sub' \<tau>"

lemma all_sub_not_welltyped:
  assumes "\<not>is_welltyped expr" "weakly_welltyped expr"
  shows "\<forall>sub \<in> to_set expr. \<forall>\<tau>. \<not>sub_welltyped sub \<tau>"
  using assms
  unfolding is_welltyped_def weakly_welltyped_def
  by blast

sublocale weakly_welltyped where weakly_welltyped = weakly_welltyped and welltyped = welltyped
proof unfold_locales 
  fix expr
  assume "\<exists>\<tau>. welltyped expr \<tau>"

  then show "weakly_welltyped expr"
    using is_welltyped_def weakly_welltyped_def
    by auto
qed

end

locale weakly_welltyped_lifting =
  sub: weakly_welltyped where
  weakly_welltyped = sub_weakly_welltyped and welltyped = sub_welltyped +
  typing_lifting where to_set = to_set
for 
  to_set :: "'expr \<Rightarrow> 'sub set" and
  sub_weakly_welltyped 
begin

definition weakly_welltyped :: "'expr \<Rightarrow> bool" where
  "weakly_welltyped expr \<equiv> \<forall>sub \<in> to_set expr. sub_weakly_welltyped sub"

sublocale weakly_welltyped where
  weakly_welltyped = weakly_welltyped and welltyped = welltyped
proof unfold_locales
  fix expr

  show "\<exists>\<tau>. welltyped expr \<tau> \<Longrightarrow> weakly_welltyped expr"
    using sub.weakly_welltyped_if_welltyped
    unfolding is_welltyped_def weakly_welltyped_def
    by auto
qed

(*
TODO: 
lemma ex_sub_not_welltyped:
  "\<not>is_welltyped expr \<Longrightarrow> weakly_welltyped expr \<Longrightarrow> \<exists>sub \<in> to_set expr. \<not>sub.is_welltyped sub"
  using is_welltyped_def
  by simp*)

end

end
