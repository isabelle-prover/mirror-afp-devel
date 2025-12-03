theory Utils
imports
  Main
  ReadShow
  "HOL-Library.Finite_Map"
  "HOL-Eisbach.Eisbach"
begin

section \<open>Some Basic Lemmas for Finite Maps\<close>

lemma fmfinite: "finite ({(ad, x). fmlookup y ad = Some x})"
proof -
  have "{(ad, x). fmlookup y ad = Some x} \<subseteq> dom (fmlookup y) \<times> ran (fmlookup y)"
  proof
    fix x assume "x \<in> {(ad, x). fmlookup y ad = Some x}"
    then have "fmlookup y (fst x) = Some (snd x)" by auto
    then have "fst x \<in> dom (fmlookup y)" and "snd x \<in> ran (fmlookup y)" using Map.ranI by (blast,metis)
    then show "x \<in> dom (fmlookup y) \<times> ran (fmlookup y)" by (simp add: mem_Times_iff)
  qed
  thus ?thesis by (simp add: finite_ran finite_subset)
qed

lemma fmlookup_finite:
  fixes f :: "'a \<Rightarrow> 'a"
    and y :: "('a, 'b) fmap"
  assumes "inj_on (\<lambda>(ad, x). (f ad, x)) {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
  shows "finite {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
proof (cases rule: inj_on_finite[OF assms(1), of "{(ad, x)|ad x. (fmlookup y) ad = Some x}"])
  case 1
  then show ?case by auto
next
  case 2
  then have *: "finite {(ad, x) |ad x. fmlookup y ad = Some x}" using fmfinite[of y] by simp
  show ?case using finite_image_set[OF *, of "\<lambda>(ad, x). (ad, x)"] by simp
qed

lemma balance_inj: "inj_on (\<lambda>(ad, x). (ad + z::String.literal,x)) {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
proof
  fix v v' assume asm1: "v \<in> {(ad, x). (fmlookup y \<circ> f) ad = Some x}" and asm2: "v' \<in> {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
  and *:"(case v of (ad, x) \<Rightarrow> (ad + z,x)) = (case v' of (ad, x) \<Rightarrow> (ad + z,x))"
  then obtain ad ad' x x' where **: "v = (ad,x)" and ***: "v'=(ad',x')" by auto
  moreover from * ** *** have "ad + z = ad' + z" by simp
  with * ** have "ad = ad'" using String_Cancel[of ad z ad' ] by simp
  moreover from asm1 asm2 ** *** have "(fmlookup y \<circ> f) ad = Some x" and "(fmlookup y \<circ> f) ad' = Some x'" by auto
  with calculation(3) have "x=x'" by simp
  ultimately show "v=v'" by simp
qed

section \<open>Some Basic Proof Methods\<close>

method solve methods m = (m ; fail)

named_theorems intros
declare conjI[intros] impI[intros] allI[intros] ballI[intros]
method intros = (rule intros; intros?)

named_theorems elims
method elims = ((rule intros | erule elims); elims?)
declare conjE[elims]

end