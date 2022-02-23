theory MDL
  imports Interval Trace
begin

section \<open>Formulas and Satisfiability\<close>

declare [[typedef_overloaded]]

datatype ('a, 't :: timestamp) formula = Bool bool | Atom 'a | Neg "('a, 't) formula" |
  Bin "bool \<Rightarrow> bool \<Rightarrow> bool" "('a, 't) formula" "('a, 't) formula" |
  Prev "'t \<I>" "('a, 't) formula" | Next "'t \<I>" "('a, 't) formula" |
  Since "('a, 't) formula" "'t \<I>" "('a, 't) formula" |
  Until "('a, 't) formula" "'t \<I>" "('a, 't) formula" |
  MatchP "'t \<I>" "('a, 't) regex" | MatchF "'t \<I>" "('a, 't) regex"
  and ('a, 't) regex = Lookahead "('a, 't) formula" | Symbol "('a, 't) formula" |
  Plus "('a, 't) regex" "('a, 't) regex" | Times "('a, 't) regex" "('a, 't) regex" |
  Star "('a, 't) regex"

fun eps :: "('a, 't :: timestamp) regex \<Rightarrow> bool" where
  "eps (Lookahead phi) = True"
| "eps (Symbol phi) = False"
| "eps (Plus r s) = (eps r \<or> eps s)"
| "eps (Times r s) = (eps r \<and> eps s)"
| "eps (Star r) = True"

fun atms :: "('a, 't :: timestamp) regex \<Rightarrow> ('a, 't) formula set" where
  "atms (Lookahead phi) = {phi}"
| "atms (Symbol phi) = {phi}"
| "atms (Plus r s) = atms r \<union> atms s"
| "atms (Times r s) = atms r \<union> atms s"
| "atms (Star r) = atms r"

lemma size_atms[termination_simp]: "phi \<in> atms r \<Longrightarrow> size phi < size r"
  by (induction r) auto

fun wf_fmla :: "('a, 't :: timestamp) formula \<Rightarrow> bool"
  and wf_regex :: "('a, 't) regex \<Rightarrow> bool" where
  "wf_fmla (Bool b) = True"
| "wf_fmla (Atom a) = True"
| "wf_fmla (Neg phi) = wf_fmla phi"
| "wf_fmla (Bin f phi psi) = (wf_fmla phi \<and> wf_fmla psi)"
| "wf_fmla (Prev I phi) = wf_fmla phi"
| "wf_fmla (Next I phi) = wf_fmla phi"
| "wf_fmla (Since phi I psi) = (wf_fmla phi \<and> wf_fmla psi)"
| "wf_fmla (Until phi I psi) = (wf_fmla phi \<and> wf_fmla psi)"
| "wf_fmla (MatchP I r) = (wf_regex r \<and> (\<forall>phi \<in> atms r. wf_fmla phi))"
| "wf_fmla (MatchF I r) = (wf_regex r \<and> (\<forall>phi \<in> atms r. wf_fmla phi))"
| "wf_regex (Lookahead phi) = False"
| "wf_regex (Symbol phi) = wf_fmla phi"
| "wf_regex (Plus r s) = (wf_regex r \<and> wf_regex s)"
| "wf_regex (Times r s) = (wf_regex s \<and> (\<not>eps s \<or> wf_regex r))"
| "wf_regex (Star r) = wf_regex r"

fun progress :: "('a, 't :: timestamp) formula \<Rightarrow> 't list \<Rightarrow> nat" where
  "progress (Bool b) ts = length ts"
| "progress (Atom a) ts = length ts"
| "progress (Neg phi) ts = progress phi ts"
| "progress (Bin f phi psi) ts = min (progress phi ts) (progress psi ts)"
| "progress (Prev I phi) ts = min (length ts) (Suc (progress phi ts))"
| "progress (Next I phi) ts = (case progress phi ts of 0 \<Rightarrow> 0 | Suc k \<Rightarrow> k)"
| "progress (Since phi I psi) ts = min (progress phi ts) (progress psi ts)"
| "progress (Until phi I psi) ts = (if length ts = 0 then 0 else
  (let k = min (length ts - 1) (min (progress phi ts) (progress psi ts)) in
   Min {j. 0 \<le> j \<and> j \<le> k \<and> memR (ts ! j) (ts ! k) I}))"
| "progress (MatchP I r) ts = Min ((\<lambda>f. progress f ts) ` atms r)"
| "progress (MatchF I r) ts = (if length ts = 0 then 0 else
  (let k = min (length ts - 1) (Min ((\<lambda>f. progress f ts) ` atms r)) in
   Min {j. 0 \<le> j \<and> j \<le> k \<and> memR (ts ! j) (ts ! k) I}))"

fun bounded_future_fmla :: "('a, 't :: timestamp) formula \<Rightarrow> bool"
  and bounded_future_regex :: "('a, 't) regex \<Rightarrow> bool" where
  "bounded_future_fmla (Bool b) \<longleftrightarrow> True"
| "bounded_future_fmla (Atom a) \<longleftrightarrow> True"
| "bounded_future_fmla (Neg phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_fmla (Bin f phi psi) \<longleftrightarrow> bounded_future_fmla phi \<and> bounded_future_fmla psi"
| "bounded_future_fmla (Prev I phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_fmla (Next I phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_fmla (Since phi I psi) \<longleftrightarrow> bounded_future_fmla phi \<and> bounded_future_fmla psi"
| "bounded_future_fmla (Until phi I psi) \<longleftrightarrow> bounded_future_fmla phi \<and> bounded_future_fmla psi \<and> right I \<in> tfin"
| "bounded_future_fmla (MatchP I r) \<longleftrightarrow> bounded_future_regex r"
| "bounded_future_fmla (MatchF I r) \<longleftrightarrow> bounded_future_regex r \<and> right I \<in> tfin"
| "bounded_future_regex (Lookahead phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_regex (Symbol phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_regex (Plus r s) \<longleftrightarrow> bounded_future_regex r \<and> bounded_future_regex s"
| "bounded_future_regex (Times r s) \<longleftrightarrow> bounded_future_regex r \<and> bounded_future_regex s"
| "bounded_future_regex (Star r) \<longleftrightarrow> bounded_future_regex r"

lemmas regex_induct[case_names Lookahead Symbol Plus Times Star, induct type: regex] =
  regex.induct[of "\<lambda>_. True", simplified]

definition "Once I \<phi> \<equiv> Since (Bool True) I \<phi>"
definition "Historically I \<phi> \<equiv> Neg (Once I (Neg \<phi>))"
definition "Eventually I \<phi> \<equiv> Until (Bool True) I \<phi>"
definition "Always I \<phi> \<equiv> Neg (Eventually I (Neg \<phi>))"

fun rderive :: "('a, 't :: timestamp) regex \<Rightarrow> ('a, 't) regex" where
  "rderive (Lookahead phi) = Lookahead (Bool False)"
| "rderive (Symbol phi) = Lookahead phi"
| "rderive (Plus r s) = Plus (rderive r) (rderive s)"
| "rderive (Times r s) = (if eps s then Plus (rderive r) (Times r (rderive s)) else Times r (rderive s))"
| "rderive (Star r) = Times (Star r) (rderive r)"

lemma atms_rderive: "phi \<in> atms (rderive r) \<Longrightarrow> phi \<in> atms r \<or> phi = Bool False"
  by (induction r) (auto split: if_splits)

lemma size_formula_positive: "size (phi :: ('a, 't :: timestamp) formula) > 0"
  by (induction phi) auto

lemma size_regex_positive: "size (r :: ('a, 't :: timestamp) regex) > Suc 0"
  by (induction r) (auto intro: size_formula_positive)

lemma size_rderive[termination_simp]: "phi \<in> atms (rderive r) \<Longrightarrow> size phi < size r"
  by (drule atms_rderive) (auto intro: size_atms size_regex_positive)

locale MDL =
  fixes \<sigma> :: "('a, 't :: timestamp) trace"
begin

fun sat :: "('a, 't) formula \<Rightarrow> nat \<Rightarrow> bool"
  and match :: "('a, 't) regex \<Rightarrow> (nat \<times> nat) set" where
  "sat (Bool b) i = b"
| "sat (Atom a) i = (a \<in> \<Gamma> \<sigma> i)"
| "sat (Neg \<phi>) i = (\<not> sat \<phi> i)"
| "sat (Bin f \<phi> \<psi>) i = (f (sat \<phi> i) (sat \<psi> i))"
| "sat (Prev I \<phi>) i = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> sat \<phi> j)"
| "sat (Next I \<phi>) i = (mem (\<tau> \<sigma> i) (\<tau> \<sigma> (Suc i)) I \<and> sat \<phi> (Suc i))"
| "sat (Since \<phi> I \<psi>) i = (\<exists>j\<le>i. mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> sat \<psi> j \<and> (\<forall>k \<in> {j<..i}. sat \<phi> k))"
| "sat (Until \<phi> I \<psi>) i = (\<exists>j\<ge>i. mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I \<and> sat \<psi> j \<and> (\<forall>k \<in> {i..<j}. sat \<phi> k))"
| "sat (MatchP I r) i = (\<exists>j\<le>i. mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> (j, Suc i) \<in> match r)"
| "sat (MatchF I r) i = (\<exists>j\<ge>i. mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I \<and> (i, Suc j) \<in> match r)"
| "match (Lookahead \<phi>) = {(i, i) | i. sat \<phi> i}"
| "match (Symbol \<phi>) = {(i, Suc i) | i. sat \<phi> i}"
| "match (Plus r s) = match r \<union> match s"
| "match (Times r s) = match r O match s"
| "match (Star r) = rtrancl (match r)"

lemma "sat (Prev I (Bool False)) i \<longleftrightarrow> sat (Bool False) i"
  "sat (Next I (Bool False)) i \<longleftrightarrow> sat (Bool False) i"
  "sat (Since \<phi> I (Bool False)) i \<longleftrightarrow> sat (Bool False) i"
  "sat (Until \<phi> I (Bool False)) i \<longleftrightarrow> sat (Bool False) i"
  apply (auto split: nat.splits)
  done

lemma prev_rewrite: "sat (Prev I \<phi>) i \<longleftrightarrow> sat (MatchP I (Times (Symbol \<phi>) (Symbol (Bool True)))) i"
  apply (auto split: nat.splits)
  subgoal for j
    by (fastforce intro: exI[of _ j])
  done

lemma next_rewrite: "sat (Next I \<phi>) i \<longleftrightarrow> sat (MatchF I (Times (Symbol (Bool True)) (Symbol \<phi>))) i"
  by (fastforce intro: exI[of _ "Suc i"])

lemma trancl_Base: "{(i, Suc i) |i. P i}\<^sup>* = {(i, j). i \<le> j \<and> (\<forall>k\<in>{i..<j}. P k)}"
proof -
  have "(x, y) \<in> {(i, j). i \<le> j \<and> (\<forall>k\<in>{i..<j}. P k)}"
    if "(x, y) \<in> {(i, Suc i) |i. P i}\<^sup>*" for x y
    using that by (induct rule: rtrancl_induct) (auto simp: less_Suc_eq)
  moreover have "(x, y) \<in> {(i, Suc i) |i. P i}\<^sup>*"
    if "(x, y) \<in> {(i, j). i \<le> j \<and> (\<forall>k\<in>{i..<j}. P k)}" for x y
    using that unfolding mem_Collect_eq prod.case Ball_def
    by (induct y arbitrary: x)
       (auto 0 3 simp: le_Suc_eq intro: rtrancl_into_rtrancl[rotated])
  ultimately show ?thesis by blast
qed

lemma Ball_atLeastLessThan_reindex:
  "(\<forall>k\<in>{j..<i}. P (Suc k)) = (\<forall>k \<in> {j<..i}. P k)"
  by (auto simp: less_eq_Suc_le less_eq_nat.simps split: nat.splits)

lemma since_rewrite: "sat (Since \<phi> I \<psi>) i \<longleftrightarrow> sat (MatchP I (Times (Symbol \<psi>) (Star (Symbol \<phi>)))) i"
proof (rule iffI)
  assume "sat (Since \<phi> I \<psi>) i"
  then obtain j where j_def: "j \<le> i" "mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I" "sat \<psi> j"
    "\<forall>k \<in> {j..<i}. sat \<phi> (Suc k)"
    by auto
  have "k \<in> {Suc j..<Suc i} \<Longrightarrow> (k, Suc k) \<in> match (Symbol \<phi>)" for k
    using j_def(4)
    by (cases k) auto
  then have "(Suc j, Suc i) \<in> (match (Symbol \<phi>))\<^sup>*"
    using j_def(1) trancl_Base
    by auto
  then show "sat (MatchP I (Times (Symbol \<psi>) (Star (Symbol \<phi>)))) i"
    using j_def(1,2,3)
    by auto
next
  assume "sat (MatchP I (Times (Symbol \<psi>) (Star (Symbol \<phi>)))) i"
  then obtain j where j_def: "j \<le> i" "mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I" "(Suc j, Suc i) \<in> (match (Symbol \<phi>))\<^sup>*" "sat \<psi> j"
    by auto
  have "\<And>k. k \<in> {Suc j..<Suc i} \<Longrightarrow> (k, Suc k) \<in> match (Symbol \<phi>)"
    using j_def(3) trancl_Base[of "\<lambda>k. (k, Suc k) \<in> match (Symbol \<phi>)"]
    by simp
  then have "\<forall>k \<in> {j..<i}. sat \<phi> (Suc k)"
    by auto
  then show "sat (Since \<phi> I \<psi>) i"
    using j_def(1,2,4) Ball_atLeastLessThan_reindex[of j i "sat \<phi>"]
    by auto
qed

lemma until_rewrite: "sat (Until \<phi> I \<psi>) i \<longleftrightarrow> sat (MatchF I (Times (Star (Symbol \<phi>)) (Symbol \<psi>))) i"
proof (rule iffI)
  assume "sat (Until \<phi> I \<psi>) i"
  then obtain j where j_def: "j \<ge> i" "mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I" "sat \<psi> j"
    "\<forall>k \<in> {i..<j}. sat \<phi> k"
    by auto
  have "k \<in> {i..<j} \<Longrightarrow> (k, Suc k) \<in> match (Symbol \<phi>)" for k
    using j_def(4)
    by auto
  then have "(i, j) \<in> (match (Symbol \<phi>))\<^sup>*"
    using j_def(1) trancl_Base
    by simp
  then show "sat (MatchF I (Times (Star (Symbol \<phi>)) (Symbol \<psi>))) i"
    using j_def(1,2,3)
    by auto
next
  assume "sat (MatchF I (Times (Star (Symbol \<phi>)) (Symbol \<psi>))) i"
  then obtain j where j_def: "j \<ge> i" "mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I" "(i, j) \<in> (match (Symbol \<phi>))\<^sup>*" "sat \<psi> j"
    by auto
  have "\<And>k. k \<in> {i..<j} \<Longrightarrow> (k, Suc k) \<in> match (Symbol \<phi>)"
    using j_def(3) trancl_Base[of "\<lambda>k. (k, Suc k) \<in> match (Symbol \<phi>)"]
    by auto
  then have "\<forall>k \<in> {i..<j}. sat \<phi> k"
    by simp
  then show "sat (Until \<phi> I \<psi>) i"
    using j_def(1,2,4)
    by auto
qed

lemma match_le: "(i, j) \<in> match r \<Longrightarrow> i \<le> j"
proof (induction r arbitrary: i j)
  case (Times r s)
  then show ?case using order.trans by fastforce
next
  case (Star r)
  from Star.prems show ?case
    unfolding match.simps
    by (induct i j rule: rtrancl.induct) (force dest: Star.IH)+
qed auto

lemma match_Times: "(i, i + n) \<in> match (Times r s) \<longleftrightarrow>
  (\<exists>k \<le> n. (i, i + k) \<in> match r \<and> (i + k, i + n) \<in> match s)"
  using match_le by auto (metis le_iff_add nat_add_left_cancel_le)

lemma rtrancl_unfold: "(x, z) \<in> rtrancl R \<Longrightarrow>
  x = z \<or> (\<exists>y. (x, y) \<in> R \<and> x \<noteq> y \<and> (y, z) \<in> rtrancl R)"
  by (induction x z rule: rtrancl.induct) auto

lemma rtrancl_unfold': "(x, z) \<in> rtrancl R \<Longrightarrow>
  x = z \<or> (\<exists>y. (x, y) \<in> rtrancl R \<and> y \<noteq> z \<and> (y, z) \<in> R)"
  by (induction x z rule: rtrancl.induct) auto

lemma match_Star: "(i, i + Suc n) \<in> match (Star r) \<longleftrightarrow>
  (\<exists>k \<le> n. (i, i + 1 + k) \<in> match r \<and> (i + 1 + k, i + Suc n) \<in> match (Star r))"
proof (rule iffI)
  assume assms: "(i, i + Suc n) \<in> match (Star r)"
  obtain k where k_def: "(i, k) \<in> local.match r" "i \<le> k" "i \<noteq> k"
    "(k, i + Suc n) \<in> (local.match r)\<^sup>*"
    using rtrancl_unfold[OF assms[unfolded match.simps]] match_le by auto
  from k_def(4) have "(k, i + Suc n) \<in> match (Star r)"
    unfolding match.simps by simp
  then have k_le: "k \<le> i + Suc n"
    using match_le by blast
  from k_def(2,3) obtain k' where k'_def: "k = i + Suc k'"
    by (metis Suc_diff_Suc le_add_diff_inverse le_neq_implies_less)
  show "\<exists>k \<le> n. (i, i + 1 + k) \<in> match r \<and> (i + 1 + k, i + Suc n) \<in> match (Star r)"
    using k_def k_le unfolding k'_def by auto
next
  assume assms: "\<exists>k \<le> n. (i, i + 1 + k) \<in> match r \<and>
    (i + 1 + k, i + Suc n) \<in> match (Star r)"
  then show "(i, i + Suc n) \<in> match (Star r)"
    by (induction n) auto
qed

lemma match_refl_eps: "(i, i) \<in> match r \<Longrightarrow> eps r"
proof (induction r)
  case (Times r s)
  then show ?case
    using match_Times[where ?i=i and ?n=0]
    by auto
qed auto

lemma wf_regex_eps_match: "wf_regex r \<Longrightarrow> eps r \<Longrightarrow> (i, i) \<in> match r"
  by (induction r arbitrary: i) auto

lemma match_Star_unfold: "i < j \<Longrightarrow> (i, j) \<in> match (Star r) \<Longrightarrow> \<exists>k \<in> {i..<j}. (i, k) \<in> match (Star r) \<and> (k, j) \<in> match r"
  using rtrancl_unfold'[of i j "match r"] match_le[of _ j r] match_le[of i _ "Star r"]
  by auto (meson atLeastLessThan_iff order_le_less)

lemma match_rderive: "wf_regex r \<Longrightarrow> i \<le> j \<Longrightarrow> (i, Suc j) \<in> match r \<longleftrightarrow> (i, j) \<in> match (rderive r)"
proof (induction r arbitrary: i j)
  case (Times r1 r2)
  then show ?case
    using match_refl_eps[of "Suc j" r2] match_le[of _ "Suc j" r2]
    apply (auto)
          apply (metis le_Suc_eq relcomp.simps)
         apply (meson match_le relcomp.simps)
        apply (metis le_SucE relcomp.simps)
       apply (meson relcomp.relcompI wf_regex_eps_match)
      apply (meson match_le relcomp.simps)
     apply (metis le_SucE relcomp.simps)
    apply (meson match_le relcomp.simps)
    done
next
  case (Star r)
  then show ?case
    using match_Star_unfold[of i "Suc j" r]
    by auto (meson match_le rtrancl.simps)
qed auto

end

lemma atms_nonempty: "atms r \<noteq> {}"
  by (induction r) auto

lemma atms_finite: "finite (atms r)"
  by (induction r) auto

lemma progress_le_ts:
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> t \<in> tfin"
  shows "progress phi ts \<le> length ts"
  using assms
proof (induction phi ts rule: progress.induct)
  case (8 phi I psi ts)
  have "ts \<noteq> [] \<Longrightarrow> Min {j. j \<le> min (length ts - Suc 0) (min (progress phi ts) (progress psi ts)) \<and>
    memR (ts ! j) (ts ! min (length ts - Suc 0) (min (progress phi ts) (progress psi ts))) I}
    \<le> length ts"
    apply (rule le_trans[OF Min_le[where ?x="min (length ts - Suc 0) (min (progress phi ts) (progress psi ts))"]])
      apply (auto simp: in_set_conv_nth intro!: memR_tfin_refl 8(3))
    apply (metis One_nat_def diff_less length_greater_0_conv less_numeral_extra(1) min.commute min.strict_coboundedI2)
    done
  then show ?case
    by auto
next
  case (9 I r ts)
  then show ?case
    using atms_nonempty[of r] atms_finite[of r]
    by auto (meson Min_le dual_order.trans finite_imageI image_iff)
next
  case (10 I r ts)
  have "ts \<noteq> [] \<Longrightarrow> Min {j. j \<le> min (length ts - Suc 0) (MIN f\<in>atms r. progress f ts) \<and>
    memR (ts ! j) (ts ! min (length ts - Suc 0) (MIN f\<in>atms r. progress f ts)) I}
    \<le> length ts"
    apply (rule le_trans[OF Min_le[where ?x="min (length ts - Suc 0) (Min ((\<lambda>f. progress f ts) ` atms r))"]])
      apply (auto simp: in_set_conv_nth intro!: memR_tfin_refl 10(2))
    apply (metis One_nat_def diff_less length_greater_0_conv less_numeral_extra(1) min.commute min.strict_coboundedI2)
    done
  then show ?case
    by auto
qed (auto split: nat.splits)

end