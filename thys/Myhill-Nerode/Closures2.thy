theory Closures2
imports 
  Closures
  "~~/src/HOL/Proofs/Extraction/Higman" 
begin

section {* Closure under @{text SUBSEQ} and @{text SUPSEQ} *}

(* compatibility with Higman theory by Stefan Berghofer *)
notation
  emb ("_ \<preceq> _")

declare  emb0 [intro]
declare  emb1 [intro]
declare  emb2 [intro]

lemma letter_UNIV:
  shows "UNIV = {A, B::letter}"
apply(auto)
apply(case_tac x)
apply(auto)
done

instance letter :: finite
apply(default)
apply(simp add: letter_UNIV)
done

hide_const A
hide_const B
hide_const R

(* definition of the embedding relation 
inductive 
  emb :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<preceq> _")
where
   emb0 [intro]: "emb [] y"
 | emb1 [intro]: "emb x y \<Longrightarrow> emb x (c # y)"
 | emb2 [intro]: "emb x y \<Longrightarrow> emb (c # x) (c # y)"
*)

text {* Properties about the embedding relation *}

lemma emb_refl [intro]:
  shows "x \<preceq> x"
by (induct x) (auto)

lemma emb_right [intro]:
  assumes a: "x \<preceq> y"
  shows "x \<preceq> y @ y'"
using a 
by (induct arbitrary: y') (auto)

lemma emb_left [intro]:
  assumes a: "x \<preceq> y"
  shows "x \<preceq> y' @ y"
using a by (induct y') (auto)

lemma emb_appendI [intro]:
  assumes a: "x \<preceq> x'"
  and     b: "y \<preceq> y'"
  shows "x @ y \<preceq> x' @ y'"
using a b by (induct) (auto)

lemma emb_cons_leftD:
  assumes "a # x \<preceq> y"
  shows "\<exists>y1 y2. y = y1 @ [a] @ y2 \<and> x \<preceq> y2"
using assms
apply(induct x\<equiv>"a # x" y\<equiv>"y" arbitrary: a x y)
apply(auto)
apply(metis append_Cons)
done

lemma emb_append_leftD:
  assumes "x1 @ x2 \<preceq> y"
  shows "\<exists>y1 y2. y = y1 @ y2 \<and> x1 \<preceq> y1 \<and> x2 \<preceq> y2"
using assms
apply(induct x1 arbitrary: x2 y)
apply(auto)
apply(drule emb_cons_leftD)
apply(auto)
apply(drule_tac x="x2" in meta_spec)
apply(drule_tac x="y2" in meta_spec)
apply(auto)
apply(rule_tac x="y1 @ (a # y1a)" in exI)
apply(rule_tac x="y2a" in exI)
apply(auto)
done

lemma emb_trans:
  assumes a: "x1 \<preceq> x2"
  and     b: "x2 \<preceq> x3"
  shows "x1 \<preceq> x3"
using a b
apply(induct arbitrary: x3)
apply(metis emb0)
apply(metis emb_cons_leftD emb_left)
apply(drule_tac emb_cons_leftD)
apply(auto)
done

lemma emb_strict_length:
  assumes a: "x \<preceq> y" "x \<noteq> y" 
  shows "length x < length y"
using a
by (induct) (auto simp add: less_Suc_eq)

lemma emb_antisym:
  assumes a: "x \<preceq> y" "y \<preceq> x" 
  shows "x = y"
using a emb_strict_length
by (metis not_less_iff_gr_or_eq)

lemma emb_wf:
  shows "wf {(x, y). x \<preceq> y \<and> x \<noteq> y}"
proof -
  have "wf (measure length)" by simp
  moreover
  have "{(x, y). x \<preceq> y \<and> x \<noteq> y} \<subseteq> measure length"
    unfolding measure_def by (auto simp add: emb_strict_length)
  ultimately 
  show "wf {(x, y). x \<preceq> y \<and> x \<noteq> y}" by (rule wf_subset)
qed

subsection {* Sub- and Supersequences *}

definition
 "SUBSEQ A \<equiv> {x. \<exists>y \<in> A. x \<preceq> y}"

definition
 "SUPSEQ A \<equiv> {x. \<exists>y \<in> A. y \<preceq> x}"

lemma SUPSEQ_simps [simp]:
  shows "SUPSEQ {} = {}"
  and   "SUPSEQ {[]} = UNIV"
unfolding SUPSEQ_def by auto

lemma SUPSEQ_atom [simp]:
  shows "SUPSEQ {[c]} = UNIV \<cdot> {[c]} \<cdot> UNIV"
unfolding SUPSEQ_def conc_def
by (auto) (metis append_Cons emb_cons_leftD)

lemma SUPSEQ_union [simp]:
  shows "SUPSEQ (A \<union> B) = SUPSEQ A \<union> SUPSEQ B"
unfolding SUPSEQ_def by auto

lemma SUPSEQ_conc [simp]:
  shows "SUPSEQ (A \<cdot> B) = SUPSEQ A \<cdot> SUPSEQ B"
unfolding SUPSEQ_def conc_def
by (auto) (metis emb_append_leftD)

lemma SUPSEQ_star [simp]:
  shows "SUPSEQ (A\<star>) = UNIV"
apply(subst star_unfold_left)
apply(simp only: SUPSEQ_union) 
apply(simp)
done

subsection {* Regular expression that recognises every character *}

definition
  Allreg :: "'a::finite rexp"
where
  "Allreg \<equiv> \<Uplus>(Atom ` UNIV)"

lemma Allreg_lang [simp]:
  shows "lang Allreg = (\<Union>a. {[a]})"
unfolding Allreg_def by auto

lemma [simp]:
  shows "(\<Union>a. {[a]})\<star> = UNIV"
apply(auto)
apply(induct_tac x rule: list.induct)
apply(auto)
apply(subgoal_tac "[a] @ list \<in> (\<Union>a. {[a]})\<star>")
apply(simp)
apply(rule append_in_starI)
apply(auto)
done

lemma Star_Allreg_lang [simp]:
  shows "lang (Star Allreg) = UNIV"
by simp

fun 
  UP :: "'a::finite rexp \<Rightarrow> 'a rexp"
where
  "UP (Zero) = Zero"
| "UP (One) = Star Allreg"
| "UP (Atom c) = Times (Star Allreg) (Times (Atom c) (Star Allreg))"   
| "UP (Plus r1 r2) = Plus (UP r1) (UP r2)"
| "UP (Times r1 r2) = Times (UP r1) (UP r2)"
| "UP (Star r) = Star Allreg"

lemma lang_UP:
  fixes r::"letter rexp"
  shows "lang (UP r) = SUPSEQ (lang r)"
by (induct r) (simp_all)

lemma regular_SUPSEQ: 
  fixes A::"letter lang"
  assumes "regular A"
  shows "regular (SUPSEQ A)"
proof -
  from assms obtain r::"letter rexp" where "lang r = A" by auto
  then have "lang (UP r) = SUPSEQ A" by (simp add: lang_UP)
  then show "regular (SUPSEQ A)" by auto
qed

lemma SUPSEQ_subset:
  shows "A \<subseteq> SUPSEQ A"
unfolding SUPSEQ_def by auto

lemma SUBSEQ_complement:
  shows "- (SUBSEQ A) = SUPSEQ (- (SUBSEQ A))"
proof -
  have "- (SUBSEQ A) \<subseteq> SUPSEQ (- (SUBSEQ A))"
    by (rule SUPSEQ_subset)
  moreover 
  have "SUPSEQ (- (SUBSEQ A)) \<subseteq> - (SUBSEQ A)"
  proof (rule ccontr)
    assume "\<not> (SUPSEQ (- (SUBSEQ A)) \<subseteq> - (SUBSEQ A))"
    then obtain x where 
       a: "x \<in> SUPSEQ (- (SUBSEQ A))" and 
       b: "x \<notin> - (SUBSEQ A)" by auto

    from a obtain y where c: "y \<in> - (SUBSEQ A)" and d: "y \<preceq> x"
      by (auto simp add: SUPSEQ_def)

    from b have "x \<in> SUBSEQ A" by simp
    then obtain x' where f: "x' \<in> A" and e: "x \<preceq> x'"
      by (auto simp add: SUBSEQ_def)
    
    from d e have "y \<preceq> x'" by (rule emb_trans)
    then have "y \<in> SUBSEQ A" using f
      by (auto simp add: SUBSEQ_def)
    with c show "False" by simp
  qed
  ultimately show "- (SUBSEQ A) = SUPSEQ (- (SUBSEQ A))" by simp
qed

lemma Higman_antichains:
  assumes a: "\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y \<longrightarrow> \<not>(x \<preceq> y) \<and> \<not>(y \<preceq> x)"
  shows "finite A"
proof (rule ccontr)
  assume "infinite A"
  then obtain f::"nat \<Rightarrow> letter list" where b: "inj f" and c: "range f \<subseteq> A"
    by (auto simp add: infinite_iff_countable_subset)
  from higman_idx obtain i j where d: "i < j" and e: "f i \<preceq> f j" by blast
  have "f i \<noteq> f j" using b d by (auto simp add: inj_on_def)
  moreover
  have "f i \<in> A" using c by auto
  moreover
  have "f j \<in> A" using c by auto
  ultimately have "\<not>(f i \<preceq> f j)" using a by simp
  with e show "False" by simp
qed

definition
  minimal :: "letter list \<Rightarrow> letter lang \<Rightarrow> bool"
where
  "minimal x A \<equiv> (\<forall>y \<in> A. y \<preceq> x \<longrightarrow> x \<preceq> y)"

lemma main_lemma:
  shows "\<exists>M. finite M \<and> SUPSEQ A = SUPSEQ M"
proof -
  def M \<equiv> "{x \<in> A. minimal x A}"
  have "finite M"
    unfolding M_def minimal_def
    by (rule Higman_antichains) (auto simp add: emb_antisym)
  moreover
  have "SUPSEQ A \<subseteq> SUPSEQ M"
  proof
    fix x
    assume "x \<in> SUPSEQ A"
    then obtain y where "y \<in> A" and "y \<preceq> x" by (auto simp add: SUPSEQ_def)
    then have a: "y \<in> {y' \<in> A. y' \<preceq> x}" by simp
    obtain z where b: "z \<in> A" "z \<preceq> x" and c: "\<forall>y. y \<preceq> z \<and> y \<noteq> z \<longrightarrow> y \<notin> {y' \<in> A. y' \<preceq> x}"
      using wfE_min[OF emb_wf a] by auto
    then have "z \<in> M"
      unfolding M_def minimal_def
      by (auto intro: emb_trans)
    with b(2) show "x \<in> SUPSEQ M"
      by (auto simp add: SUPSEQ_def)
  qed
  moreover
  have "SUPSEQ M \<subseteq> SUPSEQ A"
    by (auto simp add: SUPSEQ_def M_def)
  ultimately
  show "\<exists>M. finite M \<and> SUPSEQ A = SUPSEQ M" by blast
qed

subsection {* Closure of @{const SUBSEQ} and @{const SUPSEQ} *}

lemma closure_SUPSEQ:
  fixes A::"letter lang" 
  shows "regular (SUPSEQ A)"
proof -
  obtain M where a: "finite M" and b: "SUPSEQ A = SUPSEQ M"
    using main_lemma by blast
  have "regular M" using a by (rule finite_regular)
  then have "regular (SUPSEQ M)" by (rule regular_SUPSEQ)
  then show "regular (SUPSEQ A)" using b by simp
qed

lemma closure_SUBSEQ:
  fixes A::"letter lang"
  shows "regular (SUBSEQ A)"
proof -
  have "regular (SUPSEQ (- SUBSEQ A))" by (rule closure_SUPSEQ)
  then have "regular (- SUBSEQ A)" by (subst SUBSEQ_complement) (simp)
  then have "regular (- (- (SUBSEQ A)))" by (rule closure_complement)
  then show "regular (SUBSEQ A)" by simp
qed

end
