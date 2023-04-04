section \<open>State Model\<close>

subsection \<open>Partial Heaps\<close>

theory PartialMap
  imports Main
begin

type_synonym ('a, 'b) map = "'a \<rightharpoonup> 'b"

fun compatible_options :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "compatible_options f (Some a) (Some b) \<longleftrightarrow> f a b"
| "compatible_options _ _ _ \<longleftrightarrow> True"

fun merge_option :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b option \<Rightarrow> 'b option \<Rightarrow> 'b option" where
  "merge_option _ None None = None"
| "merge_option _ (Some a) None = Some a"
| "merge_option _ None (Some b) = Some b"
| "merge_option f (Some a) (Some b) = Some (f a b)"

definition merge_options :: "('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('b, 'c) map \<Rightarrow> ('b, 'c) map \<Rightarrow> ('b, 'c) map" where
  "merge_options f a b p = merge_option f (a p) (b p)"

definition compatible_maps :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map \<Rightarrow> bool" where
  "compatible_maps f h1 h2 \<longleftrightarrow> (\<forall>hl. compatible_options f (h1 hl) (h2 hl))"

lemma compatible_mapsI:
  assumes "\<And>x a b. h1 x = Some a \<and> h2 x = Some b \<Longrightarrow> f a b"
  shows "compatible_maps f h1 h2"
  by (metis assms compatible_maps_def compatible_options.elims(3))

definition map_included :: "('a, 'b) map \<Rightarrow> ('a, 'b) map \<Rightarrow> bool" where
  "map_included h1 h2 \<longleftrightarrow> (\<forall>x. h1 x \<noteq> None \<longrightarrow> h1 x = h2 x)"

lemma map_includedI:
  assumes "\<And>x r. h1 x = Some r \<Longrightarrow> h2 x = Some r"
  shows "map_included h1 h2"
  by (metis assms map_included_def option.exhaust)

lemma compatible_maps_empty:
  "compatible_maps f h (Map.empty)"
  by (simp add: compatible_maps_def)

lemma compatible_maps_comm:
  "compatible_maps (=) h1 h2 \<longleftrightarrow> compatible_maps (=) h2 h1"
proof -
  have "\<And>a b. compatible_maps (=) a b \<Longrightarrow> compatible_maps (=) b a"
    by (metis (mono_tags, lifting) compatible_mapsI compatible_maps_def compatible_options.simps(1))
  then show ?thesis
    by auto
qed

lemma add_heaps_asso:
  "(h1 ++ h2) ++ h3 = h1 ++ (h2 ++ h3)"
  by auto

lemma compatible_maps_same:
  assumes "compatible_maps (=) ha hb"
      and "ha x = Some y"
    shows "(ha ++ hb) x = Some y"
proof (cases "hb x")
  case None
  then show ?thesis 
    by (simp add: assms(2) map_add_Some_iff)
next
  case (Some a)
  then show ?thesis
    by (metis (mono_tags) assms(1) assms(2) compatible_maps_def compatible_options.simps(1) map_add_def option.simps(5))
qed

lemma compatible_maps_refl:
  "compatible_maps (=) h h"
  using compatible_maps_def compatible_options.elims(3) by fastforce

lemma map_invo:
  "h ++ h = h"
  by (simp add: map_add_subsumed2)

lemma included_then_compatible_maps:
  assumes "map_included h1 h"
      and "map_included h2 h"
    shows "compatible_maps (=) h1 h2"
proof (rule compatible_mapsI)
  fix x a b assume "h1 x = Some a \<and> h2 x = Some b"
  show "a = b"
    by (metis \<open>h1 x = Some a \<and> h2 x = Some b\<close> assms(1) assms(2) map_included_def option.inject option.simps(3))
qed

lemma commut_charact:
  assumes "compatible_maps (=) h1 h2"
  shows "h1 ++ h2 = h2 ++ h1"
proof (rule ext)
  fix x
  show "(h1 ++ h2) x = (h2 ++ h1) x"
  proof (cases "h1 x")
    case None
    then show ?thesis
      by (simp add: domIff map_add_dom_app_simps(2) map_add_dom_app_simps(3))
  next
    case (Some a)
    then show ?thesis
      by (simp add: assms compatible_maps_same)
  qed
qed

end
