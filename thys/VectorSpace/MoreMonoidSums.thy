header {*More sums in monoids*}

theory MoreMonoidSums

imports Main
  "~~/src/HOL/Algebra/Module"
  RingModuleFacts
  FunctionLemmas
  MonoidSums
begin

text {* Lemmas on finite products/sums that were not used in the development of vector spaces,
but are generally useful.*}

text {*"Double product/summation." A double product is the product over the direct product of the 
sets. Note this is subsumed by @{text "finprod_dept"}.  Add either this or finprod_dept to 
FiniteProduct.*}
lemma (in comm_monoid) finprod_AxB:
  fixes A B f
  assumes fa: "finite A" and fb: "finite B" and f: "f \<in> A \<rightarrow> (B \<rightarrow> carrier G)"
  shows "(\<Otimes> a\<in>A. (\<Otimes>b\<in>B. f a b)) = (\<Otimes>p\<in>A\<times>B.  f (fst p) (snd p))"
proof -
  from fa fb f show ?thesis
  proof (induct set: finite)
    case empty
    show ?case by auto
  next
    case (insert a A)
    from insert.prems insert.hyps have 1: "(\<Otimes>a\<in>insert a A. finprod G (f a) B) = finprod G (f a) B \<otimes> (\<Otimes>a\<in>A. finprod G (f a) B)"
      apply (intro finprod_insert, auto)
      by (intro finprod_closed, auto)
    have 2: "(insert a A) \<times> B = ({a} \<times> B) \<union> (A \<times> B)"
      by (metis Sigma_Un_distrib1 Un_insert_left sup_bot.left_neutral)
    have 3: "({a} \<times> B) \<inter> (A \<times> B) = {}" 
    proof - 
      have 31: "({a} \<times> B) \<inter> (A \<times> B) = ({a}\<inter>A) \<times> B" 
        by (metis Times_Int_distrib1)
      from insert.hyps have 32: "{a}\<inter>A={}" by auto
      from 31 32 show ?thesis by auto
    qed
    from 3 insert.prems insert.hyps have 4: "(\<Otimes>p\<in>({a} \<times> B) \<union> (A \<times> B). f (fst p) (snd p)) = 
      (\<Otimes>p\<in>({a} \<times> B). f (fst p) (snd p))\<otimes> (\<Otimes>p\<in>(A \<times> B). f (fst p) (snd p))"
      apply (intro finprod_Un_disjoint) apply auto
      by (metis Pi_mem2)
    have 5: "(\<Otimes>p\<in>({a} \<times> B). f (fst p) (snd p)) = (\<Otimes>b\<in> B. f a b)"
    proof - 
      (*injection*)
      let ?fp="\<lambda>p. f (fst p) (snd p)"
      let ?g="\<lambda>b. (a, b)"
      have 51: "inj_on ?g B"
        by (metis Pair_inject inj_on_def)
      have 52: "?g`B = {a}\<times> B" by blast
      from 51 insert.prems insert.hyps have 53: "finprod G ?fp (?g`B) = finprod G (%x. ?fp (?g x)) B"
        apply (intro finprod_reindex) apply auto done
      from 52 53 show ?thesis by fastforce
    qed
    from 1 2 4 5 insert.hyps insert.prems show ?case 
      by auto
qed
qed

text {*Definition of dependent pair (I don't know if this has been done elsewhere in Isabelle?)*}
definition dept_pair::"'a set\<Rightarrow>('a\<Rightarrow>('b set)) \<Rightarrow> ('a\<times>'b) set"
  where "dept_pair A B = {p. fst p \<in>A \<and> snd p \<in> B (fst p)}"

lemma dept_pair_finite:
  fixes A B
  assumes fa: "finite A" and fb: "\<forall>a\<in> A. (finite (B a))"
  shows "finite (dept_pair A B)"
proof -
  show ?thesis
  using assms proof (induct set: finite)
    case empty
    show ?case by (unfold dept_pair_def, auto)
  next
    case (insert a A)
      from insert.prems have 2: "dept_pair (insert a A) B = dept_pair {a} B \<union> dept_pair A B"
        apply (unfold dept_pair_def) by auto
      from insert.prems insert.hyps have 21: "finite (dept_pair {a} B)"
      proof - 
        have "{p. fst p \<in> {a} \<and> snd p \<in> B (fst p)} = {p. fst p = a \<and> snd p \<in> (B a)}"
          by auto
        let ?g = "\<lambda>  b. (a, b)" 
        have 1:"bij_betw ?g (B a) (dept_pair {a} B)"
          by (unfold bij_betw_def dept_pair_def inj_on_def, auto)
        from insert.prems insert.hyps have 2: "finite (B a)" by auto
        from 1 2 show ?thesis by (metis bij_betw_finite) 
      qed
      from insert.prems insert.hyps have 3: "finite (dept_pair A B)" by auto
      from 2 21 3 show ?case try0 by simp
   qed
qed

lemma (in comm_monoid) finprod_dep_prod:
  fixes A B C f
  assumes fa: "finite A" and fb: "\<forall>a\<in> A. (finite (B a))" and f: "f \<in> Pi A (\<lambda>a. (B a \<rightarrow> carrier G))"
    and c: "C = dept_pair A B"
  shows "(\<Otimes> a\<in>A. (\<Otimes>b\<in>B a. f a b)) = (\<Otimes>p\<in>C.  f (fst p) (snd p))"
proof -
  show ?thesis
  using assms proof (induct arbitrary: B C set: finite)
    case empty
    from empty.prems have 1: "C={}" by (unfold dept_pair_def, auto)
    from 1 show ?case by auto
  next
    case (insert a A)
    from insert.prems insert.hyps have 1: "(\<Otimes>a\<in>insert a A. finprod G (f a) (B a)) = finprod G (f a) (B a) \<otimes> (\<Otimes>a\<in>A. finprod G (f a) (B a))"
      apply (intro finprod_insert, auto)
      by (intro finprod_closed, auto)
    from insert.prems have 2: "dept_pair (insert a A) B = dept_pair {a} B \<union> dept_pair A B"
      apply (unfold dept_pair_def) by auto
    from insert.prems have 3: "dept_pair {a} B \<inter> dept_pair A B = {}" 
      apply (unfold dept_pair_def, auto) 
      by (metis insert.hyps(2))
    from 3 insert.prems insert.hyps have 4: "(\<Otimes>p\<in>dept_pair {a} B \<union> dept_pair A B. f (fst p) (snd p)) = 
      (\<Otimes>p\<in>dept_pair {a} B. f (fst p) (snd p))\<otimes> (\<Otimes>p\<in>dept_pair A B. f (fst p) (snd p))"
      apply (intro finprod_Un_disjoint) apply auto   
      apply (intro dept_pair_finite, auto)+
      apply (unfold dept_pair_def) by auto
    have 5: "(\<Otimes>p\<in>dept_pair {a} B. f (fst p) (snd p)) = (\<Otimes>b\<in> B a. f a b)"
    proof - 
      (*injection*)
      let ?fp="\<lambda>p. f (fst p) (snd p)"
      let ?g="\<lambda>b. (a, b)"
(*have 1:"bij_betw ?g (B a) (dept_pair {a} B)"
          by (unfold bij_betw_def dept_pair_def inj_on_def, auto)*)
      have 51: "bij_betw ?g (B a) (dept_pair {a} B)"
        by (unfold bij_betw_def dept_pair_def inj_on_def, auto)
      from 51 have 52: "inj_on ?g (B a)" by (unfold bij_betw_def, auto)
      from 51 have 53: "?g`(B a) = {a}\<times> (B a)" by auto
      from 51 have 54: "?g`(B a) = dept_pair {a} B" apply (unfold dept_pair_def, auto) done
      from 52 53 insert.prems insert.hyps have 55: "finprod G ?fp (?g`(B a)) = finprod G (%x. ?fp (?g x)) (B a)"
        apply (intro finprod_reindex) by auto
      from 54 55 show ?thesis by simp
    qed
    from 1 2 4 5 insert.hyps insert.prems show ?case 
      by auto
   qed
qed

text {*We can group terms in a finite product based on their image.*}
lemma (in comm_monoid) finprod_comp:
  fixes A B a b
  assumes  fa: "finite A" and a: "a\<in>A\<rightarrow>carrier G" 
    and h2: "\<And>y. y\<in> f`A\<Longrightarrow> (b y = (\<Otimes> x\<in> (f-`{y}\<inter>A). a x))"
    and im: "f`A=B"
  shows "(\<Otimes> x\<in> A. a x) = (\<Otimes> y\<in> B. b y)"  
proof -
  from assms have 1: "(\<Otimes> y\<in> f`A. (b y)) = (\<Otimes> y\<in> f`A. (\<Otimes> x\<in> (f-`{y}\<inter>A). (a x)))" 
    by (auto intro!: finprod_cong' finprod_closed)
  let ?B = "f`A"
  let ?A = "\<lambda>y. f-`{y}\<inter>A"
  from fa a have 2: "(\<Otimes> y\<in> f`A. (\<Otimes> x\<in> (f-`{y}\<inter>A). (a x))) = (\<Otimes> p\<in>dept_pair ?B ?A. a (snd p))"
    apply (intro finprod_dep_prod) by auto
  have 3: "(\<Otimes> p\<in>dept_pair ?B ?A. a (snd p)) = (\<Otimes> x\<in> A. a x)"
  proof - 
    let ?g = "\<lambda>a. (f a, a)" (*injection*)
    have inj: "inj_on ?g A"
      apply (unfold inj_on_def, metis Pair_inject) done
    have gA: "?g`A = dept_pair ?B ?A" apply (unfold dept_pair_def image_def) by auto
    from inj assms have reindex: "finprod G (\<lambda>p. a (snd p)) (?g`A) 
      = finprod G (\<lambda>x. (\<lambda>p. a (snd p)) (?g x)) A"
      apply (intro finprod_reindex) by auto
    from reindex show ?thesis by (auto simp add: gA)
  qed
  from 1 2 3 im show ?thesis by auto
qed

lemma (in comm_monoid) prod1:
  fixes P Q a v
  assumes "finite A" "a\<in>A\<rightarrow>carrier G" and "{x . x\<in>A \<and> Q x} = {v}"
  shows "(\<Otimes>\<^bsub>G\<^esub> x\<in>A. (if Q x then a x else \<one>\<^bsub>G\<^esub>)) = a v"
proof -
  from assms have 1: "(\<Otimes>\<^bsub>G\<^esub> x\<in>A. (if Q x then a x else \<one>\<^bsub>G\<^esub>)) = 
  (\<Otimes>\<^bsub>G\<^esub> x\<in>A. (if (v=x) then a x else \<one>\<^bsub>G\<^esub>))"
    by (intro finprod_cong', auto)
  from assms have 2: "... = a v"
    by (intro finprod_singleton, auto)
  from 1 2 show ?thesis by auto
qed


context abelian_monoid
begin
lemmas  finsum_dep_prod = add.finprod_dep_prod
lemmas finsum_comp = add.finprod_comp
lemmas sum1 = add.prod1
end
end
