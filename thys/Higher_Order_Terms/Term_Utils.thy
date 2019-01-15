theory Term_Utils
imports
  "HOL-Library.Finite_Map"
  "HOL-Library.Monad_Syntax"
  "HOL-Library.State_Monad"
begin

lemma option_bindE:
  assumes "x \<bind> f = Some a"
  obtains x' where "x = Some x'"  "f x' = Some a"
using assms
by (cases x) auto

lemma rel_option_bind[intro]:
  assumes "rel_option R x y" "\<And>a b. R a b \<Longrightarrow> rel_option R (f a) (g b)"
  shows "rel_option R (x \<bind> f) (y \<bind> g)"
using assms(1) proof (cases rule: option.rel_cases)
  case None
  thus ?thesis
    by simp
next
  case (Some a b)
  thus ?thesis
    using assms(2) by simp
qed

lemma list_split:
  assumes "n < length xs"
  obtains xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1 @ xs\<^sub>2" "n = length xs\<^sub>2" "0 < length xs\<^sub>1"
proof
  let ?xs\<^sub>1 = "take (length xs - n) xs"
  let ?xs\<^sub>2 = "drop (length xs - n) xs"

  show "xs = ?xs\<^sub>1 @ ?xs\<^sub>2"
    by simp
  show "n = length ?xs\<^sub>2" "0 < length ?xs\<^sub>1"
    using assms by auto
qed

context
  includes fset.lifting
begin

lemma ffUnion_alt_def: "x |\<in>| ffUnion A \<longleftrightarrow> fBex A (\<lambda>X. x |\<in>| X)"
by transfer blast

lemma funion_image_bind_eq: "ffUnion (f |`| M) = fbind M f"
by transfer auto

lemma fbind_funion: "fbind (M |\<union>| N) f = fbind M f |\<union>| fbind N f"
by transfer' auto

lemma ffUnion_least: "fBall A (\<lambda>X. X |\<subseteq>| C) \<Longrightarrow> ffUnion A |\<subseteq>| C"
by transfer blast

lemma fbind_iff: "x |\<in>| fbind S f \<longleftrightarrow> (\<exists>s. x |\<in>| f s \<and> s |\<in>| S)"
  by transfer' auto

lemma fBall_pred_weaken: "(\<And>x. x |\<in>| M \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> fBall M P \<Longrightarrow> fBall M Q"
by auto

end

lemma fmmap_fmupd[simp]:
  "fmmap f (fmupd k v m) = fmupd k (f v) (fmmap f m)"
apply (rule fmap_ext)
by auto

definition fmlookup_default :: "('a, 'b) fmap \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"fmlookup_default m f x = (case fmlookup m x of None \<Rightarrow> f x | Some b \<Rightarrow> b)"

(* FIXME everything below, remove after merge to afp-devel *)

lemma run_state_bind[simp]:
  "run_state (bind x f) s = (case run_state x s of (a, s') \<Rightarrow> run_state (f a) s')"
unfolding State_Monad.bind_def by auto

context
  includes fmap.lifting fset.lifting
begin

lift_definition fmimage :: "('a, 'b) fmap \<Rightarrow> 'a fset \<Rightarrow> 'b fset" is "\<lambda>m S. {b|a b. m a = Some b \<and> a \<in> S}"
subgoal for m S
  apply (rule finite_subset[where B = "ran m"])
  apply (auto simp: ran_def)[]
  by (rule finite_ran)
done

lemma fmimage_alt_def: "fmimage m S = fmran (fmrestrict_fset S m)"
by transfer' (auto simp: ran_def map_restrict_set_def map_filter_def)

lemma fmimage_empty[simp]: "fmimage m fempty = fempty"
by transfer' auto

lemma fmimage_subset_ran[simp]: "fmimage m S |\<subseteq>| fmran m"
by transfer' (auto simp: ran_def)

lemma fmimage_dom[simp]: "fmimage m (fmdom m) = fmran m"
by transfer' (auto simp: ran_def)

lemma fmimage_inter: "fmimage m (A |\<inter>| B) |\<subseteq>| fmimage m A |\<inter>| fmimage m B"
by transfer' auto

lemma fimage_inter_dom[simp]:
  "fmimage m (fmdom m |\<inter>| A) = fmimage m A"
  "fmimage m (A |\<inter>| fmdom m) = fmimage m A"
by (transfer'; auto)+

lemma fmimage_union[simp]: "fmimage m (A |\<union>| B) = fmimage m A |\<union>| fmimage m B"
by transfer' auto

lemma fmimage_Union[simp]: "fmimage m (ffUnion A) = ffUnion (fmimage m |`| A)"
by transfer' auto

lemma fmimage_filter[simp]: "fmimage (fmfilter P m) A = fmimage m (ffilter P A)"
by transfer' (auto simp: map_filter_def)

lemma fmimage_drop[simp]: "fmimage (fmdrop a m) A = fmimage m (A - {|a|})"
by transfer' (auto simp: map_filter_def map_drop_def)

lemma fmimage_drop_fset[simp]: "fmimage (fmdrop_fset B m) A = fmimage m (A - B)"
by transfer' (auto simp: map_filter_def map_drop_set_def)

lemma fmimage_restrict_fset[simp]: "fmimage (fmrestrict_fset B m) A = fmimage m (A |\<inter>| B)"
by transfer' (auto simp: map_filter_def map_restrict_set_def)

lemma fmfilter_ran[simp]: "fmran (fmfilter P m) = fmimage m (ffilter P (fmdom m))"
by transfer' (auto simp: ran_def map_filter_def)

lemma fmran_drop[simp]: "fmran (fmdrop a m) = fmimage m (fmdom m - {|a|})"
by transfer' (auto simp: ran_def map_drop_def map_filter_def)

lemma fmran_drop_fset[simp]: "fmran (fmdrop_fset A m) = fmimage m (fmdom m - A)"
by transfer' (auto simp: ran_def map_drop_set_def map_filter_def)

lemma fmran_restrict_fset: "fmran (fmrestrict_fset A m) = fmimage m (fmdom m |\<inter>| A)"
by transfer' (auto simp: ran_def map_restrict_set_def map_filter_def)

lemma fmlookup_image_iff: "y |\<in>| fmimage m A \<longleftrightarrow> (\<exists>x. fmlookup m x = Some y \<and> x |\<in>| A)"
by transfer' (auto simp: ran_def)

lemma fmimageI: "fmlookup m x = Some y \<Longrightarrow> x |\<in>| A \<Longrightarrow> y |\<in>| fmimage m A"
by (auto simp: fmlookup_image_iff)

lemma fmimageE[elim]:
  assumes "y |\<in>| fmimage m A"
  obtains x where "fmlookup m x = Some y" "x |\<in>| A"
using assms by (auto simp: fmlookup_image_iff)

lemma fmpred_mono_strong:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  shows "fmpred P m \<Longrightarrow> fmpred Q m"
  using assms unfolding fmpred_iff by auto

lemma fmdrop_idem[simp]: "fmdrop a (fmdrop a m) = fmdrop a m"
unfolding fmfilter_alt_defs by auto

end

end
