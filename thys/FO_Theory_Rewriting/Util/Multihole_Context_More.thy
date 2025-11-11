(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2016)
Author:  Martin Avanzini <martin.avanzini@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Preliminaries\<close>
subsection \<open>More Results on Multihole Contexts\<close>

theory Multihole_Context_More
imports 
  Utils
  First_Order_Rewriting.Multihole_Context
begin

unbundle lattice_syntax

fun hole_poss_list :: "('f, 'v) mctxt \<Rightarrow> pos list" where
  "hole_poss_list (MVar x) = []" |
  "hole_poss_list MHole = [[]]" |
  "hole_poss_list (MFun f cs) = concat (poss_args hole_poss_list cs)"


lemma hole_poss_list_length:
  "length (hole_poss_list D) = num_holes D"
  by (induct D) (auto simp: length_concat intro!: nth_sum_listI)

lemma unfill_holles_hole_poss_list_length:
  assumes "C \<le> mctxt_of_term t"
  shows "length (unfill_holes C t) = length (hole_poss_list C)" using assms
proof (induct C arbitrary: t)
  case (MVar x)
  then have [simp]: "t = Var x" by (cases t) (auto dest: less_eq_mctxt_MVarE1)
  show ?case by simp
next
  case (MFun f ts) then show ?case
    by (cases t) (auto simp: length_concat comp_def
      elim!: less_eq_mctxt_MFunE1 less_eq_mctxt_MVarE1 intro!: nth_sum_listI)
qed auto

lemma unfill_holes_to_subst_at_hole_poss:
  assumes "C \<le> mctxt_of_term t"
  shows "unfill_holes C t = map ((|_) t) (hole_poss_list C)" using assms
proof (induct C arbitrary: t)
  case (MVar x)
  then show ?case by (cases t) (auto elim: less_eq_mctxt_MVarE1)
next
  case (MFun f ts)
  from MFun(2) obtain ss where [simp]: "t = Fun f ss" and l: "length ts = length ss"
    by (cases t) (auto elim: less_eq_mctxt_MFunE1)
  let ?ts = "map (\<lambda>i. unfill_holes (ts ! i) (ss ! i)) [0..<length ts]"
  let ?ss = "map (\<lambda> x. map ((|_) (Fun f ss)) (case x of (x, y) \<Rightarrow> map ((#) x) (hole_poss_list y))) (zip [0..<length ts] ts)"
  have eq_l [simp]: "length (concat ?ts) = length (concat ?ss)" using MFun
    by (auto simp: length_concat comp_def elim!: less_eq_mctxt_MFunE1 split!: prod.splits intro!: nth_sum_listI)
  {fix i assume ass: "i < length (concat ?ts)"
    then have lss: "i < length (concat ?ss)" by auto
    obtain m n where [simp]: "concat_index_split (0, i) ?ts = (m, n)" by fastforce
    then have [simp]: "concat_index_split (0, i) ?ss = (m, n)" using concat_index_split_unique[OF ass, of ?ss 0] MFun(2)
      by (auto simp: unfill_holles_hole_poss_list_length[of "ts ! i" "ss ! i" for i]
       simp del: length_unfill_holes elim!: less_eq_mctxt_MFunE1)
    from concat_index_split_less_length_concat(2-)[OF ass ] concat_index_split_less_length_concat(2-)[OF lss]
    have "concat ?ts ! i = concat ?ss! i" using MFun(1)[OF nth_mem, of m "ss ! m"] MFun(2)
      by (auto elim!: less_eq_mctxt_MFunE1)} note nth = this
  show ?case using MFun
    by (auto simp: comp_def map_concat length_concat
        elim!: less_eq_mctxt_MFunE1 split!: prod.splits
        intro!: nth_equalityI nth_sum_listI nth)
qed auto

lemma hole_poss_split_var_poss_list_length [simp]:
  "length (hole_poss_list (fst (split_vars t))) = length (var_poss_list t)"
  by (induct t)(auto simp: length_concat comp_def intro!: nth_sum_listI)

lemma hole_poss_split_vars_var_poss_list:
  "hole_poss_list (fst (split_vars t)) = var_poss_list t"
proof (induct t)
  case (Fun f ts)
  let ?ts = "poss_args hole_poss_list (map (fst \<circ> split_vars) ts)"
  let ?ss = "poss_args var_poss_list ts"
  have len: "length (concat ?ts) = length (concat ?ss)" "length ?ts = length ?ss"
    "\<forall> i < length ?ts. length (?ts ! i) = length (?ss ! i)" by (auto intro: eq_length_concat_nth)
  {fix i assume ass: "i < length (concat ?ts)"
    then have lss: "i < length (concat ?ss)" using len by auto
    obtain m n where int: "concat_index_split (0, i) ?ts = (m, n)" by fastforce
    then have [simp]: "concat_index_split (0, i) ?ss = (m, n)" using concat_index_split_unique[OF ass len(2-)] by auto
    from concat_index_split_less_length_concat(2-)[OF ass int] concat_index_split_less_length_concat(2-)[OF lss]
    have "concat ?ts ! i = concat ?ss! i" using Fun[OF nth_mem, of m] by auto}
  then show ?case using len by (auto intro: nth_equalityI)
qed auto

end
