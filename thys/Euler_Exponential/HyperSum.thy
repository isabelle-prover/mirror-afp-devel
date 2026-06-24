(*  Title:  HyperSum.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>Hyperfinite summation\<close> 

theory HyperSum
  imports "HOL-Nonstandard_Analysis.HSeries" Hyperfinite_Set HyperInt
begin 

definition (in comm_monoid_add) hypersum :: "('b star \<Rightarrow> 'a star) \<Rightarrow> 'b star set \<Rightarrow> 'a star" where
 "hypersum f A = star_n (\<lambda>n. sum ((*nf* f) n) ((*ns* A) n))"

notation hypersum ("\<Sum>\<^sub>h")
syntax "_hypersum" :: "pttrn \<Rightarrow> 'b star set \<Rightarrow> 'c star \<Rightarrow> 'c star" ("(2\<Sum>\<^sub>h (_/\<in>_)./ _)" [0, 51, 10] 10)
translations "\<Sum>\<^sub>h i\<in>A. b" == "CONST hypersum (\<lambda>i. b) A"

lemma hypersum: 
  "hypersum (*fn* f) (*sn* A) = star_n (\<lambda>n. sum (f n) (A n))"
proof (simp add: hypersum_def star_n_eq_iff)
  have "\<forall>\<^sub>F n in \<U>. (*nf* *fn* f) n = f n" 
    using n_starfun_starfun_n_eq_ultra by blast
  moreover have "\<forall>\<^sub>F n in \<U>. (*ns* *sn* A) n = A n"  
    using n_starset_starset_n_eq_ultra by blast
  ultimately have "\<forall>\<^sub>F n in \<U>. (*nf* *fn* f) n = f n \<and> (*ns* *sn* A) n = A n"
      by (simp add: eventually_conj_iff)
  then show "\<forall>\<^sub>F n in \<U>. sum ((*nf* *fn* f) n) ((*ns* *sn* A) n) = sum (f n) (A n)"
    using eventually_mono by force
qed

lemma hypersum_starfun2_n: 
  "hypersum ((*fn2* f) (star_n X)) (*sn* A) = star_n (\<lambda>n. sum (f n (X n)) (A n))"
proof (simp add: hypersum_def star_n_eq_iff)
   have "\<forall>\<^sub>F n in \<U>. (*ns* *sn* A) n = A n"
     by (simp add: n_starset_starset_n_eq_ultra)
   moreover  have "\<forall>\<^sub>F n in \<U>. (*nf* (*fn2* f) (star_n X)) n = f n (X n)"
     by (simp add: n_starfun_starfun2_n_eq_ultra)
   ultimately have "\<forall>\<^sub>F n in \<U>. 
                    (*ns* *sn* A) n = A n \<and> 
                    (*nf* (*fn2* f) (star_n X)) n = f n (X n)"
     by (simp add: eventually_conj_iff)
   then show "\<forall>\<^sub>F n in \<U>. 
                    sum ((*nf* (*fn2* f) (star_n X)) n) ((*ns* *sn* A) n) =
                    sum (f n (X n)) (A n)"
    using eventually_mono by force
qed

subsection\<open>Hypersum properties\<close> 

lemma hypersum_empty [simp]:
  assumes "f \<in> InternalFuns" shows "hypersum f {} = 0"
proof - 
  obtain F where fF: "f = *fn* F"
    by (metis InternalFuns_starfun_n_starfun assms) 
  then have "\<forall>\<^sub>F n in \<U>. (*nf* *fn* F) n = F n"
    using n_starfun_starfun_n_eq_ultra by blast
  then have "\<forall>\<^sub>F n in \<U>. sum ((*nf* *fn* F) n) ((*ns* {}) n) = 0"
    using n_starset_empty_ultra  eventually_mono sum.empty 
    by (metis (mono_tags, lifting))
  then show ?thesis using fF
    by (auto simp add: hypersum_def InternalFuns_def star_of_def 
        star_n_eq_iff star_zero_def)
qed

lemma hypersum_starfun_n_empty [simp]: " hypersum (*fn* f) {} = 0"
by (metis InternalFuns_starfun_n hypersum_empty)

(* Not proven before? *)
lemma setsum_singleton [simp]: "sum f {x} = f x"
by simp

lemma hypersum_singleton [simp]:
  assumes "f \<in> InternalFuns" 
  shows "hypersum f {a} = f a"
proof (cases a)
  case (star_n X)
  assume a: "a = star_n X"
  have X: "{star_n X} = *sn* (\<lambda>n. {X n})"
    by simp 
  moreover obtain F where fF: "f = *fn* F"
    by (metis InternalFuns_starfun_n_starfun assms) 
  ultimately have "\<forall>\<^sub>F n in \<U>. sum (F n) {X n} = F n (X n)"
    by (meson eventuallyI setsum_singleton)
  then show ?thesis using a fF X
    by (metis (full_types) hypersum star_n_eq_iff starfun_n)
qed

lemma hypersum_F_neutral_ivl [simp]:
  "hypersum (\<lambda>n. 0) {m..<n} = 0"
proof -
  have f_0: "(\<lambda>n. 0) = *fn* (\<lambda>n m. 0)"
    by force
  have "{m..<n} \<in> InternalSets" 
    by simp
  then show ?thesis 
    by (auto simp add: InternalSets_def f_0 hypersum star_n_zero_num [symmetric])
qed

lemma hypersum_head_hSuc:
  assumes "f \<in> InternalFuns" and "m \<le> n" 
  shows "hypersum f {m..n} = f m + hypersum f {hSuc m..n}"
proof - 
  obtain F where f: "f = *fn* F" using assms(1)
    by (metis InternalFuns_starfun_n_starfun) 
  then have "hypersum (*fn* F) {m..n} =
             (*fn* F) m + hypersum (*fn* F) {hSuc m..n}"
  proof (cases m, cases n)
    fix X Xa
    assume mn: "m = star_n X" "n = star_n Xa"
    then have " hypersum (*fn* F) {star_n X..star_n Xa} =
        (*fn* F) (star_n X) + hypersum (*fn* F) {hSuc (star_n X)..star_n Xa}"
      using assms(2) 
      by (auto  simp add: star_le_def starP2_star_n hSuc_def
            starset_n_atLeastAtMost [symmetric] starfun_star_n hypersum
            starfun_n star_n_add star_n_eq_iff eventually_mono  sum.atLeast_Suc_atMost)
    then show ?thesis using mn by simp
  qed  
  then show ?thesis 
    using f by simp
qed

lemma hypersum_head_upt_hSuc:
  assumes " f \<in> InternalFuns" and "m < n"
  shows "hypersum f {m..<n} = f m + hypersum f {hSuc m..<n}"
proof - 
  obtain F where f: "f = *fn* F" using assms(1)
    by (metis InternalFuns_starfun_n_starfun) 
  then have "hypersum (*fn* F) {m..<n} =
             (*fn* F) m + hypersum (*fn* F) {hSuc m..<n}"
  proof (cases m, cases n)
    fix X Xa
    assume mn: "m = star_n X" "n = star_n Xa"
    then have " hypersum (*fn* F) {star_n X..<star_n Xa} =
        (*fn* F) (star_n X) + hypersum (*fn* F) {hSuc (star_n X)..<star_n Xa}"
      using assms(2) 
      by (auto  simp add: star_less_def starP2_star_n hSuc_def starfun_star_n
            starset_n_atLeastLessThan_eq [symmetric] hypersum starfun_n
            star_n_add star_n_eq_iff  eventually_mono sum.atLeast_Suc_lessThan)
    then show ?thesis using mn by simp
  qed  
  then show ?thesis 
    using f by simp
qed

lemma hypersum_ub_add_hypernat: 
  assumes "f \<in> InternalFuns" 
  and "(m::hypnat) \<le> n + 1"
  shows "hypersum f {m..n + p} = hypersum f {m..n} + hypersum f {n + 1..n + p}"
proof (cases m, cases n, cases p)
  fix X Xa Xb
  assume mnp: "m = star_n X" "n = star_n Xa" "p = star_n Xb"
  then have ev_le: "\<forall>\<^sub>F n in \<U>. X n \<le> Xa n + 1" using assms(2)
    by (simp add: star_add_def star_n_le star_n_one_num starfun2_star_n)
  moreover 
    obtain F where internal_f: "f = *fn* F"
    by (metis InternalFuns_starfun_n_starfun assms(1))
  then
   have " \<forall>\<^sub>F n in \<U>.
           sum (F n) {X n..Xa n + Xb n} =
           sum (F n) {X n..Xa n} + sum (F n) {Xa n + 1..Xa n + Xb n}"
     using sum.ub_add_nat eventually_mono [OF ev_le]
     by (metis (mono_tags, lifting)) 
  then have "hypersum (*fn* F) {m..n + p} =
             hypersum (*fn* F) {m..n} + hypersum (*fn* F) {n + 1..n + p}"
    using mnp
    by (auto simp only: star_n_add starset_n_atLeastAtMost [symmetric] hypersum 
            star_n_one_num star_le_def starP2_star_n star_n_eq_iff )
  then show ?thesis
    using internal_f by blast
qed


lemma hypersum_op_ivl_Suc[simp]:
  assumes "f \<in> InternalFuns"
  shows "hypersum f {m..<hSuc n} = (if n < m then 0 else hypersum f {m..<n} + f(n))"
proof (cases m, cases n)
  fix X Xa 
  assume mn: "m = star_n X" "n = star_n Xa" 
  obtain F where internal_f: "f = *fn* F"
    by (metis InternalFuns_starfun_n_starfun assms(1))
  then show ?thesis
  proof (cases "n < m")
    case True
    then show ?thesis 
      using mn internal_f
      by (auto simp add: starset_n_atLeastLessThan_eq [symmetric] hSuc_def starfun hypersum
            star_n_eq_iff star_less_def starP2_star_n star_n_zero_num eventually_mono)
  next
    case False
    then show ?thesis 
      using mn internal_f 
      by (auto simp add: starset_n_atLeastLessThan_eq [symmetric] hSuc_def starfun hypersum
             star_n_eq_iff star_less_def starP2_star_n star_n_add starfun_n 
             FreeUltrafilterNat.eventually_imp_iff )
  qed
qed

lemma hypersum_insert:
  assumes "f \<in> InternalFuns" 
  and "A \<in> InternalSets"
  and "hyperfinite A" 
  and "a \<notin> A"
  shows "hypersum f (insert a A) = f a + hypersum f A"
proof (cases a)
  case (star_n X)
  assume a: "a = star_n X"
  obtain F As where f: "f = *fn* F" and A: "A = *sn* As"
    by (metis InternalFuns_starfun_n_starfun InternalSets_starset_n_starset assms(1) assms(2))
  then have "\<forall>\<^sub>F n in \<U>. finite (As n)"
    using assms(3) hyperfinite_starset_n_iff by blast 
  moreover have "\<forall>\<^sub>F x in \<U>. X x \<notin> As x" 
    using A assms(4) FreeUltrafilterNat.ultra star_n starset_n_star_n by blast
  ultimately have "\<forall>\<^sub>F n in \<U>. sum (F n) (insert (X n) (As n)) = F n (X n) + sum (F n) (As n)"
    using eventually_elim2 by fastforce
  then show ?thesis
    using f A a 
    by (auto simp add: insert_star_n_starset_n hypersum starfun_n star_n_eq_iff star_n_add)
qed

lemma hypersum_subset_diff: 
  assumes "f \<in> InternalFuns"
  and "A \<in> InternalSets"
  and "B \<in> InternalSets"
  and "B \<subseteq> A" 
  and "hyperfinite A"
  shows "hypersum f A = hypersum f (A - B) + hypersum f B"
proof -
  obtain F As Bs where f: "f = *fn* F" and A: "A = *sn* As" and B: "B = *sn* Bs"
    by (metis InternalFuns_starfun_n_starfun InternalSets_starset_n_starset assms(1) assms(2) assms(3))
  then have "\<forall>\<^sub>F n in \<U>. Bs n \<subseteq> As n" 
    using assms(4) by (auto simp add: starset_n_subset)
  moreover have "\<forall>\<^sub>F n in \<U>. finite (As n)"
    using A assms(5) hyperfinite_starset_n_iff by blast
  ultimately have "\<forall>\<^sub>F n in \<U>. sum (F n) (As n) = sum (F n) (As n - Bs n) + sum (F n) (Bs n)"
    using eventually_elim2 by (fastforce simp add: sum.subset_diff)
  then show ?thesis 
    using f A B by  (auto simp add: hypersum starset_n_diff [symmetric] star_n_add star_n_eq_iff)
qed

lemma hypersum_diff:
  assumes "f \<in> InternalFuns" 
  and "A \<in> InternalSets" 
  and "B \<in> InternalSets" 
  and "B \<subseteq> A" 
  and "hyperfinite A"
  shows "hypersum f (A - B) = hypersum f A - ((hypersum f B)::('a::ab_group_add star))"
  by (metis add_diff_cancel assms hypersum_subset_diff)

lemma hypersum_add_hypnat_ivl: 
  assumes "f \<in> InternalFuns" 
  and "m \<le> n" and "n \<le> p"
  shows "hypersum f {m..<n} + hypersum f {n..<p} = hypersum f {m..<p::hypnat}"
proof -
  obtain F M N P 
    where f: "f = *fn* F" and m: "m = star_n M" and n: "n = star_n N" and p: "p = star_n P"
    by (metis InternalFuns_starfun_n_starfun assms(1) star_cases)
  then have "\<forall>\<^sub>F n in \<U>. M n \<le> N n"
    using assms(2) star_n_le by blast
  moreover have "\<forall>\<^sub>F n in \<U>. N n \<le> P n"
    using assms(3) n p star_n_le by blast
  ultimately have "\<forall>\<^sub>F n in \<U>. sum (F n) {M n..<N n} + sum (F n) {N n..<P n} 
                              = sum (F n) {M n..<P n}"
    using eventually_elim2 
    by (fastforce simp add: sum.atLeastLessThan_concat)
  then show ?thesis
    using f m n p by (auto simp only: starset_n_atLeastLessThan_eq [symmetric] 
                      hypersum star_n_add star_n_eq_iff star_le_def starP2_star_n)
qed

lemma hypersum_diff_hypnat_ivl: 
  "\<lbrakk> (f::hypnat\<Rightarrow>'a::ab_group_add star) \<in> InternalFuns; m \<le> n; n \<le> p \<rbrakk> 
   \<Longrightarrow> hypersum f {m..<p} - hypersum f {m..<n} = hypersum f {n..<p::hypnat}"
  by (metis add_diff_cancel_left' hypersum_add_hypnat_ivl)

lemma InternalFuns2_hypersum:
  assumes "(\<lambda>j i. f j i) \<in> InternalFuns2" 
  shows "(\<lambda>i. hypersum (f i) {m..n}) \<in> InternalFuns"
proof -
  obtain F M N where f: "f = *fn2* F" and m: "m = star_n M" and n: "n = star_n N"
    by (metis InternalFuns2_starfun2_n_starfun2 assms star_cases) 
   have "\<exists>Fa. (\<lambda>i. hypersum ((*fn2* F) i) {m..n}) = *fn* Fa"
   proof (rule exI [where x="\<lambda>n i. sum (F n i) {M n..N n}"], rule ext)
     fix i::"'a star"
     obtain I where i: "i = star_n I"
       using star_cases by blast
      then show  "hypersum ((*fn2* F) i) {m..n} = (*fn* (\<lambda>n i. sum (F n i) {M n..N n})) i"
        using m n 
        by (auto simp add: starfun_n  starset_n_atLeastAtMost [symmetric] hypersum_starfun2_n)
    qed
    then show ?thesis using f by auto 
qed

lemma hypersum_starfun_atLeastAtMost:
  "hypersum (*f* f) {M..N} = (*f2* (\<lambda>m n. sum f {m..n})) M N"
proof (cases M, cases N)
  fix X Xa
  assume "M = star_n X" "N = star_n Xa"
  then show "hypersum (*f* f) {M..N} = (*f2* (\<lambda>m n. sum f {m..n})) M N"
    by (auto simp add: starset_n_atLeastAtMost [symmetric] 
        hypersum starfun_starfun_n_eq starfun2_star_n)
qed

lemma hypersum_starfun_atLeastLessThan:
  "hypersum (*f* f) {M..<N} = (*f2* (\<lambda>m n. sum f {m..<n})) M N"
proof (cases M, cases N)
  fix X Xa
  assume "M = star_n X" "N = star_n Xa"
  then show "hypersum (*f* f) {M..<N} = (*f2* (\<lambda>m n. sum f {m..<n})) M N "
    by (auto simp add: starset_n_atLeastLessThan_eq [symmetric] 
        hypersum starfun_starfun_n_eq starfun2_star_n)
qed

lemma hypersum_shift_bounds_cl_hSuc_ivl:
  assumes "f \<in> InternalFuns"
  shows "hypersum f {hSuc m..hSuc n} = hypersum (\<lambda>i. f(hSuc i)){m..n}"
proof -
  obtain F M N where f: "f = *fn* F" and m: "m = star_n M" and n: "n = star_n N"
    by (metis InternalFuns_starfun_n_starfun assms star_cases)
   have "\<forall>\<^sub>F n in \<U>.
              (\<Sum>i = M n..N n. F n (Suc i)) =
              (\<Sum>m = M n..N n. F n (Suc m))"
    by simp
  then show ?thesis using f m n 
    by (auto simp only: hSuc_def starfun starset_n_atLeastAtMost [symmetric] starfun_n
        starfun_starfun_n_eq starfun_n_o hypersum star_n_eq_iff  sum.shift_bounds_cl_Suc_ivl) 
qed

lemma hypersum_shift_bounds_hSuc_ivl:
  assumes "f \<in> InternalFuns" 
  shows "hypersum f {hSuc m..<hSuc n} = hypersum (\<lambda>i. f(hSuc i)){m..<n}"
proof - 
  obtain F M N where f: "f = *fn* F" and m: "m = star_n M" and n: "n = star_n N"
    by (metis InternalFuns_starfun_n_starfun assms star_cases)
  have "\<forall>\<^sub>F n in \<U>.
              (\<Sum>i = M n..<N n. F n (Suc i)) =
              (\<Sum>m = M n..<N n. F n (Suc m))"
    by simp
  then show ?thesis using f m n 
    by (auto simp only: hSuc_def starfun starset_n_atLeastLessThan_eq [symmetric] starfun_n
        starfun_starfun_n_eq starfun_n_o hypersum star_n_eq_iff sum.shift_bounds_Suc_ivl)
qed

lemma lemma_n_starfun2_add_eq: 
"eventually (\<lambda>n. ((*nf2* (\<lambda>x. (+) ((*fn* f) x))) n) = (\<lambda>x. (+) (f n x))) \<U>"
proof (simp add: n_starfun2_def)
  show "\<forall>\<^sub>F n in \<U>.
       (SOME Gs.
           (\<lambda>x. (+) ((*fn* f) x)) = (\<lambda>x. Ifun (star_n Gs \<star> x)))
        n =
       (\<lambda>x. (+) (f n x))"
  proof (rule someI2 [of "(\<lambda>Gs. (\<lambda>x. (+) ((*fn* f) x)) = (\<lambda>x. Ifun (star_n Gs \<star> x)))", of "\<lambda>n. (\<lambda>x. (+) (f n x))"])
    show  "(\<lambda>x. (+) ((*fn* f) x)) = (\<lambda>x. Ifun (star_n (\<lambda>n x. (+) (f n x)) \<star> x))"
    proof (rule ext)+
      fix x::"'a star" and xa::"'b star"
      obtain X Xa where x: "x = star_n X" and xa: "xa = star_n Xa"
        by (metis star_n_star)
      then show " (*fn* f) x + xa = star_n (\<lambda>n x. (+) (f n x)) \<star> x \<star> xa"
        by (simp add: Ifun_star_n starfun_n star_n_add)
    qed
  next 
    fix x 
    assume assm: "(\<lambda>x. (+) ((*fn* f) x)) = (\<lambda>xa. Ifun (star_n x \<star> xa))"
    then have "\<forall>xa xb. star_of (+) \<star> (star_n f \<star> xa) \<star> xb = star_n x \<star> xa \<star> xb"
      by (metis star_add_def starfun2_def starfun_n_def)
      {fix xa xb
        have "star_n x \<star> xa \<star> xb = star_n (\<lambda>n x. (+) (f n x)) \<star> xa \<star> xb"
          by (metis assm star_add_def starfun2_def starfun_def starfun_n_def starfun_starfun_n_o)
      }
      then have "*fn2* x = *fn2* (\<lambda>n x. (+) (f n x))"
        by (auto simp add: star_add_def starfun2_def starfun_n_def fun_eq_iff starfun2_n_def)
      then show "\<forall>\<^sub>F n in \<U>. x n = (\<lambda>x. (+) (f n x))"
        by (rule starfun2_n_eq_cancel [THEN iffD1])
  qed
qed

(* This doesn't seem to exist anymore -- we want it just so that we can have 
   the next definition of hypersum although we don't use the latter *)
lemma (in comm_monoid_add) setsum_def2: 
   "sum f A = (if finite A then (Finite_Set.fold (\<lambda>x y. (+) (f x) y) 0 A) else 0)"
proof (auto simp add: sum.eq_fold)
  assume "finite A" 
  then show "Finite_Set.fold ((+) \<circ> f) 0 A = Finite_Set.fold (\<lambda>x. (+) (f x)) 0 A"
    by (meson comp_apply)
qed

lemma hypersum_def2:
  assumes "f \<in> InternalFuns"
  shows "hypersum f A = (if hyperfinite A then hyperfold_image (+) f 0 A else 0)"
proof -
  obtain F where f: "f = *fn* F"
    by (metis InternalFuns_starfun_n_starfun assms) 
  then show ?thesis
  proof (cases "hyperfinite A")
    assume "hyperfinite A"
    then have "\<forall>\<^sub>F n in \<U>. finite ((*ns* A) n)"
      using hyperfinite_iff by blast
    moreover have "\<forall>\<^sub>F x in \<U>. n_star (star_n (\<lambda>n. 0 :: 'b)) x = 0"
      by (metis n_star_star_of_eq_ultra star_of_def)
    ultimately have "\<forall>\<^sub>F x in \<U>.  finite ((*ns* A) x) \<and> 
                      (*nf* *fn* F) x = F x \<and>
                      (*nf2* (\<lambda>x. (+) ((*fn* F) x))) x = (\<lambda>xa. (+) (F x xa)) \<and>
                      n_star (star_n (\<lambda>n.  0 :: 'b)) x = 0"
      by (auto intro!: eventually_conj simp add: lemma_n_starfun2_add_eq n_starfun_starfun_n_eq_ultra hyperfinite_iff)
    then have "\<forall>\<^sub>F n in \<U>.
                sum ((*nf* *fn* F) n) ((*ns* A) n) =
                Finite_Set.fold ((*nf2* (\<lambda>x. (+) ((*fn* F) x))) n)
                 (n_star (star_n (\<lambda>n. 0)) n) ((*ns* A) n)"
      by (fastforce intro: eventually_mono  simp add: setsum_def2)
    then show ?thesis using f
      by (simp add: \<open>hyperfinite A\<close> hyperfold_def hyperfold_image_def hypersum_def star_n_eq_iff star_n_zero_num) 
    next
      assume not_hyperfiniteA: "\<not> hyperfinite A"
      then have "\<forall>\<^sub>F n in \<U>. \<not> finite ((*ns* A) n)"
        using FreeUltrafilterNat.ultra hyperfinite_iff by blast
      then have "\<forall>\<^sub>F n in \<U>. sum ((*nf* *fn* F) n) ((*ns* A) n) = 0"
        using eventually_mono by fastforce
      then show ?thesis
        by (auto simp add: f not_hyperfiniteA hypersum_def star_zero_def star_of_def star_n_eq_iff)
  qed
qed

subsection\<open>The sumhr function as a  hypersum.\<close>

lemma sumhr_hypersum_eq:
  "sumhr(M,N,f) = hypersum (*f* f) {M..<N}"
  by (simp add: hypersum_starfun_atLeastLessThan sumhr_app)

lemma NSsums_hypersum_HNatInfinite_approx_iff:
  "(f NSsums s) = (\<forall>N\<in>HNatInfinite. hypersum (*f* f) {0..<N} \<approx> of_real s)" 
proof (auto simp add: NSsums_def NSLIMSEQ_def)
  fix N
  assume "\<forall>N\<in>HNatInfinite. (*f* (\<lambda>n. sum f {..<n})) N \<approx> hypreal_of_real s"
  and "N \<in> HNatInfinite"
  then have starfun_sum: "(*f* (\<lambda>n. sum f {..<n})) N \<approx> hypreal_of_real s" by blast
  then show "hypersum (*f* f) {0..<N} \<approx> hypreal_of_real s"
  proof (cases N)
    case (star_n X)
    then show ?thesis using starfun_sum 
      by (auto simp add: starset_n_atLeast_zero_LessThan_eq [symmetric] 
            starfun_starfun_n_eq hypersum starfun_n atLeast0LessThan)
  qed
next
  fix N
  assume  "\<forall>N\<in>HNatInfinite. hypersum (*f* f) {0..<N} \<approx> hypreal_of_real s" 
  and "N \<in> HNatInfinite"
  then have hypsetsum: "hypersum (*f* f) {0..<N} \<approx> hypreal_of_real s" by blast
  then show "(*f* (\<lambda>n. sum f {..<n})) N \<approx> hypreal_of_real s"
  proof (cases N)
    case (star_n X)
    then show ?thesis using  hypsetsum
      by (auto simp add: starset_n_atLeast_zero_LessThan_eq [symmetric] 
            starfun_starfun_n_eq hypersum starfun_n atLeast0LessThan)
  qed
qed

subsection\<open>Hyper-convergence\<close> 

definition
  HyperCauchy :: "(hypnat \<Rightarrow> 'a::real_normed_vector star) \<Rightarrow> bool" where
  "HyperCauchy X = (\<forall>M\<in>HNatInfinite. \<forall>N\<in>HNatInfinite. X M \<approx> X N)"
 
definition 
  HyperSummable :: "(hypnat \<Rightarrow> 'a::real_normed_vector star) \<Rightarrow> bool" where
  "HyperSummable F = HyperCauchy (\<lambda>N. hypersum F {0..<N})"

lemma NSCauchy_HyperCauchy_starfun_iff: 
  "NSCauchy X = HyperCauchy (*f* X)"
by (simp add: HyperCauchy_def NSCauchy_def)

lemma Cauchy_HyperCauchy_starfun_iff: 
  "Cauchy X = HyperCauchy (*f* X)"
by (metis NSCauchy_Cauchy_iff NSCauchy_HyperCauchy_starfun_iff)

lemma NSsummable_HyperSummable_starfun_iff:
  "NSsummable f = HyperSummable (*f* f)"
  by (smt HyperCauchy_def HyperSummable_def NSsummable_NSCauchy NSsummable_NSsums
      NSsums_sumhr_HNatInfinite_approx_iff approx_trans2 sumhr_hrabs_approx sumhr_hypersum_eq)

lemma starfun_setsum_atLeastLessThan_eq_hypesetsum_fun:
  "(*f* (\<lambda>n. sum f {k n..<g n})) = (\<lambda>N. hypersum (*f* f) {((*f* k) N)..< ((*f* g) N)})"
proof (rule ext)
  fix N
  show "(*f* (\<lambda>n. sum f {k n..<g n})) N = hypersum (*f* f) {(*f* k) N..<(*f* g) N}"
  proof (cases N)
    case (star_n X)
    then show ?thesis 
      by (auto simp add:  starfun_starfun_n_eq starfun_n hypersum  
       starset_n_atLeastLessThan_eq [symmetric])
  qed
qed


lemma starfun_setsum_atLeast_zero_hypesetsum_fun:
  "(*f* (\<lambda>n. sum f {0..<g n})) = (\<lambda>N. hypersum (*f* f) {0..< ((*f* g) N)})"
proof (rule ext)
  fix N
  show "(*f* (\<lambda>n. sum f {0..<g n})) N = hypersum (*f* f) {0..<(*f* g) N}"
  proof (cases N)
    case (star_n X)
    then show ?thesis 
      by (auto simp add:  starfun_starfun_n_eq starfun_n hypersum  
       starset_n_atLeast_zero_LessThan_eq [symmetric])
  qed
qed

lemma starfun_setsum_atLeast_zero_hypesetsum:
  "(*f* (\<lambda>n. sum f {0..<n})) = (\<lambda>N. hypersum (*f* f) {0..<N})"
using starfun_setsum_atLeast_zero_hypesetsum_fun [where g="\<lambda>x. x"] by auto

lemma hypersum_atLeast_zero_starfun:
  "hypersum (*f* f) {0..<N} = (*f* (\<lambda>n. sum f {0..<n})) N"
by (metis starfun_setsum_atLeast_zero_hypesetsum)

lemma hypersum_starfun_atLeast0LessThan:
  "hypersum (*f* f) {0..<N::nat star} = (*f* (\<lambda>n. \<Sum>i<n. f i)) N"
  using hypersum_atLeast_zero_starfun lessThan_atLeast0 by auto

(* rename *)
lemma hypersum_atLeast_zero_star_n_starfun_n:
  "hypersum (*fn* f) {0..<star_n X} = star_n((\<lambda>n. sum (f n) {0..<X n}))"
  by (auto simp add: starset_n_atLeast_zero_LessThan_eq [symmetric] hypersum star_n_eq_iff)

(* rename *)
lemma hypersum_atLeast_zero_starfun_n:
  "hypersum (*fn* f) {0..<N} =  (*fn* (\<lambda>n m. sum (f n) {0..<m})) N"
proof (cases N)
  case (star_n X)
  then show ?thesis 
    by (auto simp add: hypersum_atLeast_zero_star_n_starfun_n starfun_n)
qed

lemma hypersum_geometric:
  assumes "x \<noteq> 1" 
  shows "hypersum (\<lambda>n. x pow n) {0..<n} = (x pow n - 1) / (x - 1::'a::field star)"
proof -
  obtain X N where xn: "x = star_n X" "n = star_n N" 
    by (metis star_n_star)
  then have "\<forall>\<^sub>F n in \<U>. X n \<noteq> 1" using  assms 
    by (simp add: star_n_one_num star_n_eq_iff 
                  FreeUltrafilterNat.eventually_not_iff [symmetric])
  moreover have "\<forall>\<^sub>F n in \<U>. n_star (star_n X) n = X n"
    by (simp add: n_star_star_n_eq_ultra) 
  ultimately have "\<forall>\<^sub>F n in \<U>.
              sum ((^) (n_star (star_n X) n)) {0..<N n} =
              (n_star (star_n X) n ^ N n - 1) / (X n - 1)"
    by (force elim: eventually_elim2  simp add: atLeast0LessThan geometric_sum) 
  then show ?thesis 
    by (simp add: xn hyperpower_starfun_n hypersum_atLeast_zero_starfun_n starfun_n  
          star_n_eq_iff star_n_one_num star_n_diff star_n_divide)
qed

lemma HyperSummable_geometric:
  assumes "hnorm (x::'a::{real_normed_field} star) < 1" 
  and "\<not>hnorm x \<approx> 1"
  shows "HyperSummable (\<lambda>N. x pow N)"
proof (auto simp add: HyperSummable_def HyperCauchy_def)
  fix M N 
  assume MN: "M \<in> HNatInfinite" "N \<in> HNatInfinite"
  then show "hypersum ((pow) x) {0..<M} \<approx> hypersum ((pow) x) {0..<N}"
  proof (cases "x = 1")
    case True
    then show ?thesis
      using assms(2) by simp 
  next
    case False
    assume x_not_1: "x \<noteq> 1" 
    have "x \<in> HFinite" using assms 
      by (force intro: bexI [of _ 2] simp add:  HFinite_def)
    then have "x - 1 \<in> HFinite"
      by (simp add: HFinite_diff) 
    moreover have "x - 1 \<notin> Infinitesimal"
      using assms(2) bex_Infinitesimal_iff
      by (metis approx_hnorm hnorm_one) 
    moreover have "x pow M - 1 \<approx> x pow N - 1" using assms MN
      by (metis Infinitesimal_approx Infinitesimal_hyperpow_HNatInfinite approx_diff approx_refl)
    ultimately have "(x pow M - 1) / (x - 1) \<approx> (x pow N - 1) / (x - 1)"
      by (simp add: approx_divide_HFinite_diff_Infinitesimal)       
    then show ?thesis
      by (simp add: x_not_1 hypersum_geometric) 
  qed
qed

lemma summable_convergent_sumr_iff:
 "summable f = convergent (\<lambda>n. sum f {0..<n})"
  by (simp add: atLeast0LessThan summable_iff_convergent)

(* More general than for NSsummable *)
lemma HyperSummable_starfun_summable_iff: 
  "(HyperSummable ( (*f* f)::hypnat => 'a::banach star)) = (summable f)"
by (simp add: HyperSummable_def summable_convergent_sumr_iff Cauchy_convergent_iff [symmetric]
            Cauchy_HyperCauchy_starfun_iff starfun_setsum_atLeast_zero_hypesetsum)

lemma HyperSummable_def2:
  "HyperSummable f = (\<exists>s. \<forall>N\<in>HNatInfinite. hypersum f {0..<N} \<approx> s)"
proof (auto simp add: HyperSummable_def HyperCauchy_def)
  assume "\<forall>M\<in>HNatInfinite.
       \<forall>N\<in>HNatInfinite. hypersum f {0..<M} \<approx> hypersum f {0..<N}"
  then show "\<exists>s. \<forall>N\<in>HNatInfinite. hypersum f {0..<N} \<approx> s"
    by metis
next 
  fix M N s
  assume "M \<in> HNatInfinite" "N \<in> HNatInfinite"
          "\<forall>N\<in>HNatInfinite. hypersum f {0..<N} \<approx> s"
  then show "hypersum f {0..<M} \<approx> hypersum f {0..<N}"
    using approx_trans2 by blast
qed

lemma HyperSummable_def3:
  assumes "f \<in> InternalFuns"
  shows "HyperSummable f = (\<forall>M\<in>HNatInfinite.\<forall>N\<in>HNatInfinite. hypersum f {M..<N} \<approx> 0)"
proof (simp add: HyperSummable_def HyperCauchy_def, safe)
  fix M N
  assume approxsums: "\<forall>M\<in>HNatInfinite.
          \<forall>N\<in>HNatInfinite. hypersum f {0..<M} \<approx> hypersum f {0..<N}"
         and "M \<in> HNatInfinite" "N \<in> HNatInfinite"
  then have "hypersum f {0..<M} \<approx> hypersum f {0..<N}"
    by blast
  then have sums_diff: "hypersum f {0..<M} - hypersum f {0..<N} \<approx> 0"
    using approx_minus_iff by blast
  then show "hypersum f {M..<N} \<approx> 0"
  proof(cases "M < N")
    case True
     then show ?thesis using  sums_diff hypersum_diff_hypnat_ivl
      by (metis approx_minus_iff approx_sym assms  hypnat_le0 less_imp_le) 
  next
    case False
    then show ?thesis
      using assms by auto 
  qed
next
  fix M N
  assume approx_sum: "\<forall>M\<in>HNatInfinite.
               \<forall>N\<in>HNatInfinite. hypersum f {M..<N} \<approx> 0"
         and infs: "M \<in> HNatInfinite" "N \<in> HNatInfinite"
   show "hypersum f {0..<M} \<approx> hypersum f {0..<N}"
  proof (cases "N < M")
    case True
    then show ?thesis using approx_sum hypersum_diff_hypnat_ivl infs assms
      by (metis approx_minus_iff less_imp_le zero_less_HNatInfinite)
  next
    case False
    then have "hypersum f {0..<N} - hypersum f {0..<M} \<approx> hypersum f {M..<N}"
      using assms hypersum_diff_hypnat_ivl by fastforce
    then show ?thesis
      using approx_minus_iff approx_sum approx_sym approx_trans3 infs by blast 
  qed
qed

lemma HyperSummable_starfun_n:
  "HyperSummable (*fn* f) = (\<forall>M\<in>HNatInfinite.\<forall>N\<in>HNatInfinite. hypersum (*fn* f) {M..<N} \<approx> 0)"
by (metis HyperSummable_def3 InternalFuns_starfun_n)

(* This would be easier if set interval functions were nonstandard extensions *)
lemma atLeastLessThanhSuc_atLeastAtMost: 
  "\<And>m n. {m..<hSuc n} = {m..n}"
proof (auto)
  show "\<And> m n x. \<lbrakk>m \<le> x; x < hSuc n\<rbrakk> \<Longrightarrow> x \<le> n"
    by transfer simp
next
  show " \<And>m n x. \<lbrakk>m \<le> x; x \<le> n\<rbrakk> \<Longrightarrow> x < hSuc n" 
    by transfer simp
qed

lemma hypersum_op_ivl_Suc2[simp]:
   "hypersum (*fn* f) {m..<hSuc n} = (if n < m then 0 else hypersum (*fn* f) {m..<n} + (*fn*f) n)"
by (metis InternalFuns_starfun_n hypersum_op_ivl_Suc)

lemma hypersum_op_ivl_Suc2':
   "hypersum (*fn* f) {m..(n::hypnat)} = (if n < m then 0 else hypersum (*fn* f) {m..<n} + (*fn*f) n)"
  by (metis atLeastLessThanhSuc_atLeastAtMost hypersum_op_ivl_Suc2)

lemma HyperSummable_starfun_n_HNatInfinite:
  assumes "HyperSummable (*fn* f)"
  and "K\<in>HNatInfinite" 
  shows "(*fn* f) K \<approx> 0"
proof - 
  have "\<forall>M\<in>HNatInfinite. \<forall>N\<in>HNatInfinite. hypersum (*fn* f) {M..<N} \<approx> 0" 
    using assms(1) HyperSummable_starfun_n by blast
  moreover have "hSuc K \<in> HNatInfinite" using assms(2)
    by (metis HNatInfinite_add hSuc_eq_add_one hSuc_eq_add_one)
  ultimately have "hypersum (*fn* f) {K..<hSuc K} \<approx> 0" 
    using assms(2) by force
  thus ?thesis by simp
qed

(* These equivalences below are alternative definitions *)
lemma  HyperSummable_def': "HyperSummable F = HyperCauchy (\<lambda>N. hypersum F {0..N})"
  by (metis (no_types, lifting) HNatInfinite_add HNatInfinite_add_one_cancel 
      HNatInfinite_is_Suc HyperCauchy_def HyperSummable_def
      atLeastLessThanhSuc_atLeastAtMost hSuc_eq_add_one)

lemma HyperSummable_def3':
  assumes "f \<in> InternalFuns"
  shows "HyperSummable f = (\<forall>M\<in>HNatInfinite.\<forall>N\<in>HNatInfinite. hypersum f {M..N} \<approx> 0)"
  by (metis HNatInfinite_add HNatInfinite_add_one_cancel HNatInfinite_is_Suc HyperSummable_def3 assms
      atLeastLessThanhSuc_atLeastAtMost hSuc_eq_add_one)

lemma HyperSummable_def4:
  "HyperSummable (*fn* f) = (\<exists>s. \<forall>N\<in>HNatInfinite. hypersum (*fn* f) {0..N} \<approx> s)"
proof 
  assume hsummable_f: "HyperSummable (*fn* f)" 
  then obtain s where hsum_approx: "\<forall>N\<in>HNatInfinite. hypersum (*fn* f) {0..<N} \<approx> s"
    using HyperSummable_def2 by blast
  {fix N
  assume infN: "N\<in>HNatInfinite"
  then have "hypersum (*fn* f) {N..<N+1} \<approx> 0"
    using HNatInfinite_add HyperSummable_starfun_n hsummable_f by blast
  then have "hypersum (*fn* f) {0..N} \<approx> s"
    by (metis HNatInfinite_add atLeastLessThanhSuc_atLeastAtMost hSuc_eq_add_one hsum_approx infN)}
  then show "\<exists>s. \<forall>N\<in>HNatInfinite. hypersum (*fn* f) {0..N} \<approx> s"
    by blast
next 
  assume "\<exists>s. \<forall>N\<in>HNatInfinite. hypersum (*fn* f) {0..N} \<approx> s"
  then obtain s where hsum_approx: "\<forall>N\<in>HNatInfinite. hypersum (*fn* f) {0..N} \<approx> s"
    by clarify
  then have "\<forall>N\<in>HNatInfinite. hypersum (*fn* f) {0..<N+1} \<approx> s"
    using atLeastLessThanhSuc_atLeastAtMost hSuc_eq_add_one by auto
  then show "HyperSummable (*fn* f)"
    using HNatInfinite_add_one_cancel HNatInfinite_is_Suc HyperSummable_def2 by blast 
qed

lemma HyperSummable_shift_hSuc:
  assumes "f \<in> InternalFuns"
      and "HyperSummable f"
    shows "HyperSummable (\<lambda>n. f (hSuc n))"
proof (subst HyperSummable_def3)
  show "(\<lambda>n. f (hSuc n)) \<in> InternalFuns"
    by (simp add: InternalFuns_o2 assms(1))
next  
  show "\<forall>M\<in>HNatInfinite. \<forall>N\<in>HNatInfinite. hypersum (\<lambda>n. f (hSuc n)) {M..<N} \<approx> 0"
    by (metis HNatInfinite_add HyperSummable_def3 assms(1,2) hSuc_eq_add_one
        hypersum_shift_bounds_hSuc_ivl)
qed

lemma InternalFuns_hypersum_starfun_n_Interval:
    "(\<lambda>N. hypersum (*fn* F) {M..<N}) \<in> InternalFuns"
proof (simp add: InternalFuns_def)
  {fix X
    assume M_seq: "M = star_n X" 
    {fix N
      have "hypersum (*fn* F) {M..<N} = (*fn* (\<lambda>n N. sum (F n) {X n..<N})) N"
      proof (cases N)
        case (star_n Y)
        then show ?thesis using M_seq 
          by (auto simp add: starfun_n hypersum starset_n_atLeastLessThan_eq [symmetric])
      qed}
    then have "(\<lambda>N. hypersum (*fn* F) {M..<N}) =  *fn* (\<lambda>n N. sum (F n) {X n..<N})"
      using ext by blast}
    then show "\<exists>Fa. (\<lambda>N. hypersum (*fn* F) {M..<N}) = *fn* Fa"
      using star_cases by metis
qed

lemma InternalFuns_hypersum:
  assumes "f \<in> InternalFuns" 
  shows "(\<lambda>n. hypersum f {m..<n}) \<in> InternalFuns"
  using assms InternalFuns_hypersum_starfun_n_Interval
  by (metis InternalFuns_starfun_n_starfun) 

lemma InternalFuns_hypersum_starfun_n_Interval2:
    "(\<lambda>N. hypersum (*fn* F) {M..N}) \<in> InternalFuns"
proof (simp add: InternalFuns_def)
  {fix X
   assume M_seq: "M = star_n X"
    {fix N
      have "hypersum (*fn* F) {M..N} = (*fn* (\<lambda>n N. sum (F n) {X n..N})) N"
      proof (cases N)
        case (star_n Y)
        then show ?thesis using M_seq 
          by (auto simp add: starset_n_atLeastAtMost [symmetric] hypersum starfun_n)
      qed}
    then have "(\<lambda>N. hypersum (*fn* F) {M..N}) =  *fn* (\<lambda>n N. sum (F n) {X n..N})"
      using ext by blast}
    then show "\<exists>Fa. (\<lambda>N. hypersum (*fn* F) {M..N}) = *fn* Fa"
      using star_cases by metis
  qed

lemma InternalFuns_hypersum2:
  "f \<in> InternalFuns \<Longrightarrow> (\<lambda>n. hypersum f {m..n}) \<in> InternalFuns"
  using InternalFuns_hypersum_starfun_n_Interval2
  by (metis InternalFuns_starfun_n_starfun) 

lemma NSsummable_NSCauchy_setsum:
  "NSsummable f = NSCauchy (\<lambda>n. sum f {0..<n})"
proof (simp add: NSCauchy_def NSsummable_NSCauchy starfunNat_sumr, safe) 
  fix M N
  assume "\<forall>M\<in>HNatInfinite. \<forall>N\<in>HNatInfinite. sumhr (M, N, f) \<approx> 0"
         "M \<in> HNatInfinite" "N \<in> HNatInfinite"
  then show "sumhr (0, M, f) \<approx> sumhr (0, N, f)" 
    using approx_minus_iff approx_refl approx_sym sumhr_split_diff
    by (metis less_linear)
next
  fix M N
  assume "\<forall>M\<in>HNatInfinite.
               \<forall>N\<in>HNatInfinite. sumhr (0, M, f) \<approx> sumhr (0, N, f)"
         "M \<in> HNatInfinite" "N \<in> HNatInfinite"
  then show "sumhr (M, N, f) \<approx> 0"
    using sumhr_approx by blast
qed


lemma Hypersum_Comparison_Theorem_Nats:
  assumes "f \<in> InternalFuns" "g \<in> InternalFuns"
          "HyperSummable f" "HyperSummable g" 
          "\<forall>n\<in>Nats. f n \<approx> g n" 
          "N \<in> Nats" 
  shows "hypersum f {0..<N} \<approx> hypersum g {0..<N}"
proof - 
  {fix m
  have "hypersum f {0..<hypnat_of_nat m} \<approx>
             hypersum g {0..<hypnat_of_nat m}"
  proof(induct m)
    case 0
    then show ?case
      using assms(1) assms(2) by auto 
  next
    case (Suc m)
    then show ?case using assms(1,2,5) 
      by (auto intro: approx_add simp add: hSuc_eq_add_one [symmetric])
  qed}
  then show ?thesis using assms(6) Nats_hypnat_of_nat_iff by auto 
qed

lemma Hypersum_Comparison_Theorem_HNatInfinite:
  assumes int_f: "f \<in> InternalFuns" 
          and int_g: "(g::nat star \<Rightarrow> 'a::{real_normed_div_algebra, semiring_1_cancel} star) \<in> InternalFuns"
          and hyperSums: "HyperSummable f" "HyperSummable g" 
          and inf_close_fg: "\<forall>n\<in>Nats. f n \<approx> g n"
          and inf_N: "N \<in> HNatInfinite"
  shows "hypersum f {0..<N} \<approx> hypersum g {0..<N}"
proof - 
  have "\<forall>n\<in>Nats.  hypersum f {0..<n} \<approx> hypersum g {0..<n}"
    using Hypersum_Comparison_Theorem_Nats hyperSums(1) hyperSums(2) inf_close_fg int_f int_g by blast
  then obtain M where inf_M: "M \<in> HNatInfinite" 
           and inf_close_hsum: "\<forall>n<M. hypersum f {0..<n} \<approx> hypersum g {0..<n}"
    using InternalFuns_Sequential_Theorem2 InternalFuns_hypersum int_f int_g by blast
  then show ?thesis
  proof (cases "N < M")
    case True
    then show ?thesis using inf_close_hsum by blast
  next
    case False
    have "M - 1 < M"  using inf_M   
      by (metis hypnat_add_one_self_less hypnat_le_add_diff_inverse2 one_le_HNatInfinite)
    then have hsum1: "hypersum f {0..<M - 1} \<approx> hypersum g {0..<M - 1}" 
      using inf_close_hsum by blast  
    have "hypersum f {M - 1..<N} \<approx> 0"
      using HNatInfinite_diff HyperSummable_def3 Nats_1 hyperSums(1) inf_M inf_N int_f by blast
    moreover have "hypersum g {M - 1..<N} \<approx> 0"
      using HNatInfinite_diff HyperSummable_def3 Nats_1 hyperSums(2) inf_M inf_N int_g by blast
    ultimately have "hypersum f {M - 1..<N} \<approx> hypersum g {M - 1..<N}"
      using approx_trans2 by blast
    moreover have "hypersum f {0..<N} \<approx> hypersum f {0..<M - 1} + hypersum f {M - 1..<N}"
      using False \<open>M - 1 < M\<close> hypersum_add_hypnat_ivl int_f by fastforce
    moreover have "hypersum g {0..<N} \<approx> hypersum g {0..<M - 1} + hypersum g {M - 1..<N}"
      using False \<open>M - 1 < M\<close> hypersum_add_hypnat_ivl int_g by fastforce
    ultimately show ?thesis using hsum1 approx_add  
      by (metis (no_types, lifting) approx_monad_iff) 
  qed
qed

text\<open>Full version of the Summation Comparison Theorem\<close>
lemma Hypersum_Comparison_Theorem:
  "\<lbrakk> f \<in> InternalFuns; 
     (g::nat star \<Rightarrow> 'a::{real_normed_div_algebra, semiring_1_cancel} star) \<in> InternalFuns;
     HyperSummable f; HyperSummable g; \<forall>n\<in>Nats. f n \<approx> g n \<rbrakk> 
       \<Longrightarrow> hypersum f {0..<N} \<approx> hypersum g {0..<N}"
  by (metis HNatInfinite_not_Nats_iff Hypersum_Comparison_Theorem_HNatInfinite 
      Hypersum_Comparison_Theorem_Nats)

lemma Hypersum_Comparison_Theorem':
  "\<lbrakk> f \<in> InternalFuns; 
     (g::nat star \<Rightarrow> 'a::{real_normed_div_algebra, semiring_1_cancel} star) \<in> InternalFuns;
     HyperSummable f; HyperSummable g; \<forall>n\<in>Nats. f n \<approx> g n \<rbrakk> 
       \<Longrightarrow> hypersum f {0..N} \<approx> hypersum g {0..N}"
by (metis Hypersum_Comparison_Theorem atLeastLessThanhSuc_atLeastAtMost)

lemma HyperSummable_hypersum_approx:
  "\<lbrakk> HyperSummable f; M \<in> HNatInfinite; N \<in> HNatInfinite \<rbrakk>
   \<Longrightarrow> hypersum f {0..M} \<approx> hypersum f {0..N}"
by (metis HNatInfinite_upward_closed HyperSummable_def2 approx_monad_iff 
      atLeastLessThan_empty_iff atLeastLessThanhSuc_atLeastAtMost 
      atLeastatMost_empty_iff less_imp_le order_refl)

lemma hnorm_hypersum: 
  "\<lbrakk> f \<in> InternalFuns; A \<in> InternalSets \<rbrakk> \<Longrightarrow> hnorm (hypersum f A) \<le> hypersum (\<lambda>i. hnorm (f i)) A"
by (auto simp add: InternalSets_def InternalFuns_def hypersum hnorm_def starfun_starfun_n_o starfun 
       star_n_eq_iff star_le_def starP2_star_n norm_sum)

lemma hypersum_mono':
  assumes internal_f: "f \<in> InternalFuns" 
      and internal_g: "g \<in> InternalFuns" 
      and internal_setK: "K \<in> InternalSets"
      and fg_mono: "(\<forall>i. i \<in> K \<longrightarrow> f i \<le> ((g i)::('b::ordered_comm_monoid_add star)))" 
    shows "hypersum f K \<le> hypersum g K"
proof -
  obtain F Fa As
    where fnf: "f = *fn* F" and fng: "g = *fn* Fa" and snk: "K = *sn* As"
    and "\<forall>\<^sub>F x in \<U>. \<forall>y. y \<in> As x \<longrightarrow> F x y \<le> Fa x y"
    using internal_f internal_g internal_setK fg_mono
    by (auto dest!: FreeUltrafilterNat.eventually_all_iff [THEN iffD2] 
            simp add: InternalSets_def InternalFuns_def  star_le_def starP2_star_n
                       all_star_eq starfun_n starset_n_star_n 
                       FreeUltrafilterNat.eventually_imp_iff [symmetric])
  then have "\<forall>\<^sub>F n in \<U>. sum (F n) (As n) \<le> sum (Fa n) (As n)"
    by (simp add: eventually_mono sum_mono)
  then show ?thesis
    by (simp add: fnf fng hypersum snk star_n_le)
qed

lemma hypersum_mono:
   "\<lbrakk> f \<in> InternalFuns; g \<in> InternalFuns; K \<in> InternalSets; 
      (\<And>i. i \<in> K \<Longrightarrow> f i \<le> ((g i)::('b::ordered_comm_monoid_add star))) \<rbrakk> 
    \<Longrightarrow> hypersum f K \<le> hypersum g K"
by (metis hypersum_mono')


lemma hypersum_nonneg: 
  assumes "f \<in> InternalFuns" "A \<in> InternalSets"
          "\<forall>x\<in>A. (0::'a::ordered_comm_monoid_add star) \<le> f x"
  shows "0 \<le> hypersum f A"
proof -
  obtain F S where "f = *fn* F" and "A = *sn* S"
    using assms
    by (metis InternalFuns_starfun_n_starfun InternalSets_starset_n_starset) 
  then have " \<forall>\<^sub>F x in \<U>. \<forall>y. y \<in> S x \<longrightarrow> 0 \<le> F x y"
    using assms(3)  
    by (force dest!:  FreeUltrafilterNat.eventually_all_iff [THEN iffD2]
              simp add: star_n_zero_num star_le_def starP2_star_n
                      all_star_eq Ball_def starset_n_star_n 
                      FreeUltrafilterNat.eventually_imp_iff [symmetric] starfun_n)
  then have "\<forall>\<^sub>F n in \<U>. 0 \<le> sum (F n) (S n)" 
    by (force intro: eventually_mono simp add: sum_nonneg)
  then show ?thesis
    by (simp add: \<open>A = *sn* S\<close> \<open>f = *fn* F\<close> hypersum star_n_le star_n_zero_num) 
qed

lemma abs_hypersum_abs [simp]:
  "\<lbrakk> (f :: 'a star \<Rightarrow> ('b::ordered_ab_group_add_abs) star) \<in> InternalFuns; A \<in> InternalSets \<rbrakk> 
       \<Longrightarrow> abs(hypersum (\<lambda>i. abs(f i)) A) = hypersum (\<lambda>i. abs(f i)) A"
by (auto simp add: InternalSets_def InternalFuns_def hypersum star_abs_def 
            starfun_starfun_n_o starfun star_n_eq_iff)

lemma InternalFuns_hnorm_starfun_n [simp]: 
  "(\<lambda>i. hnorm ((*fn* F) i)) \<in> InternalFuns"
proof (auto simp add: hnorm_def)
  show "(\<lambda>i. (*f* norm) ((*fn* F) i)) \<in> InternalFuns"
    by (metis InternalFuns_starfun_n starfun_starfun_n_o)
qed

lemma InternalFuns_hnorm:
  "f \<in> InternalFuns \<Longrightarrow> (\<lambda>n. hnorm (f n)) \<in> InternalFuns"
by (metis InternalFuns_hnorm_starfun_n InternalFuns_starfun_n_starfun)

lemma HyperSummable_Cauchy: 
   "HyperSummable (*fn* F) \<Longrightarrow> (\<forall>e\<in>Reals. e>0 \<longrightarrow> (\<exists>N. \<forall>m\<ge>N. \<forall>n. hnorm (hypersum (*fn* F) {m..<n}) < e))"
  unfolding HyperSummable_starfun_n mem_infmal_iff [symmetric]
  by (metis HNatInfinite_upward_closed HNatInfinite_whn InfinitesimalD atLeastLessThan_empty nle_le)

lemma Cauchy_HyperSummable: 
   "(\<forall>e\<in>Reals. e>0 \<longrightarrow> (\<exists>N\<in>Nats. \<forall>m\<ge>N. \<forall>n. hnorm (hypersum (*fn* F) {m..<n}) < e)) \<Longrightarrow> HyperSummable (*fn* F)"
  by (metis HyperSummable_starfun_n InfinitesimalI Nats_le_HNatInfinite mem_infmal_iff)

lemma Cauchy_HyperSummable': 
   "(\<forall>e\<in>Reals. e>0 \<longrightarrow> (\<exists>N\<in>Nats. \<forall>m\<ge>N. \<forall>n\<ge>N. hnorm (hypersum (*fn* F) {m..<n}) < e)) \<Longrightarrow> 
    HyperSummable (*fn* F)"
  by (metis HyperSummable_starfun_n InfinitesimalI Nats_le_HNatInfinite mem_infmal_iff)

lemma HyperSummable_Cauchy': 
   assumes H: "HyperSummable (*fn* F)"
   shows "(\<forall>e\<in>Reals. e>0 \<longrightarrow> (\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. hnorm (hypersum (*fn* F) {m..<n}) < e))"
proof (safe)
    fix e::hypreal assume e: "0 < e" "e \<in> \<real>"
    have "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. hnorm (hypersum (*fn* F) {m..<n}) <  e"
    proof (intro exI allI impI)
      fix M assume "whn \<le> M"
      with HNatInfinite_whn have M: "M \<in> HNatInfinite"
        by (rule HNatInfinite_upward_closed)
      fix N assume "whn \<le> N"
      with HNatInfinite_whn have N: "N \<in> HNatInfinite"
        by (rule HNatInfinite_upward_closed)
      from H M N have "hypersum (*fn* F) {M..<N} \<approx> 0"
        using HyperSummable_starfun_n by blast
      then show "hnorm (hypersum (*fn* F) {M..<N}) <  e"
         by (simp add: InfinitesimalD e(1) e(2) mem_infmal_iff)
      qed 
   then show
     "(\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. hnorm (hypersum (*fn* F) {m..<n}) < e)" by blast
qed

lemma HyperSummable_comparison_test:
  assumes "f \<in> InternalFuns" "g \<in> InternalFuns"
          "\<exists>k\<in>Nats. \<forall>n. k \<le> n \<longrightarrow> hnorm ((f::hypnat => 'a::banach star) n) \<le> g n"
          "HyperSummable g" 
  shows "HyperSummable f"
proof -
  obtain F G where Int_f: "f = *fn* F" and Int_g: "g = *fn* G"
    by (metis InternalFuns_starfun_n_starfun assms(1) assms(2))
  {fix M N
  assume inf_M: "M\<in>HNatInfinite" and inf_N: "N\<in>HNatInfinite"
  then have Infinitesimal_hSum_g: "hypersum (*fn* G) {M..<N} \<in> Infinitesimal"
    using HyperSummable_def3 Int_g assms(2) assms(4) mem_infmal_iff by blast
  have hSum_G_ge_0: "0 \<le> hypersum (*fn* G) {M..<N}"
  proof -
    {fix x
     assume "M \<le> x" and "x < N" 
     then have "(*fn* G) x \<ge> (0::real star)"
       using assms(3) Int_g inf_M by (metis  Nats_le_HNatInfinite hnorm_ge_zero order_trans)
    }
    then show "0 \<le> hypersum (*fn* G) {M..<N}"
      using assms hypersum_nonneg[intro!] by force
  qed
  have "hnorm (hypersum (*fn* F) {M..<N}) \<le> hnorm (hypersum (*fn* G) {M..<N})"
  proof -
    {fix i 
     assume "M \<le> i" and "i < N"  
     then have "hnorm ((*fn* F) i) \<le> (*fn* G) i"
       using Int_f Int_g Nats_le_HNatInfinite assms(3) dual_order.trans inf_M by blast
    }
    then have X: "hypersum (\<lambda>i. hnorm ((*fn* F) i)) {M..<N} \<le>  hypersum (*fn* G) {M..<N}"
       by (force intro!: hypersum_mono)
     then show ?thesis 
       using hSum_G_ge_0 by (force intro: order_trans [OF hnorm_hypersum])
   qed
   then have "hypersum (*fn* F) {M..<N} \<in> Infinitesimal" 
      using  Infinitesimal_hSum_g by (fastforce intro: Infinitesimal_interval2a [of _ 0])
  }
  then show ?thesis
    using assms(1) Int_f 
    by (simp add:  InternalFuns_def HyperSummable_starfun_n mem_infmal_iff [symmetric] )
qed

lemma HyperSummable_hypreal_comparison_test:
     "\<lbrakk> (f::hypnat \<Rightarrow> hypreal) \<in> InternalFuns; 
        g \<in> InternalFuns;
        \<forall>n. f n \<ge> 0;
        \<exists>k\<in>Nats. \<forall>n. k \<le> n \<longrightarrow> f n \<le> g n; 
        HyperSummable g \<rbrakk> \<Longrightarrow> HyperSummable f"
by (metis HyperSummable_comparison_test abs_of_nonneg hypreal_hnorm_def)

lemma HyperSummable_comparison_test_norm:
     "f \<in> InternalFuns 
      \<Longrightarrow> HyperSummable (\<lambda>n. hnorm ((f::hypnat => 'a::banach star) n)) \<Longrightarrow>  HyperSummable f"
by (auto intro: HyperSummable_comparison_test InternalFuns_hnorm Nats_0)

lemma hypersum_atLeastLessThan_starfun_n:
  "hypersum (*fn* f) {M..<N} =  (*fn2* (\<lambda>i m n. sum (f i) {m..<n})) M N"
proof (cases M, cases N)
  fix X Xa
  assume "M = star_n X" "N = star_n Xa"
  then show ?thesis
    by (auto simp add: hypersum starfun2_n starfun_n 
        starset_n_atLeastLessThan_eq [symmetric]) 
qed

lemma hypersum_minus:
  "\<lbrakk> f \<in> InternalFuns; A \<in> InternalSets \<rbrakk>
   \<Longrightarrow> hypersum (\<lambda>x. - (f x)::'a::ab_group_add star) A = - hypersum f A"
by (auto simp add: InternalFuns_def InternalSets_def starfun_n_minus hypersum 
       star_n_minus star_n_eq_iff sum_negf)

lemma HyperSummable_minus:
  "\<lbrakk> f \<in> InternalFuns; HyperSummable f \<rbrakk> \<Longrightarrow>  HyperSummable (\<lambda>n. - f n)"
by (auto simp add: HyperSummable_def HyperCauchy_def hypersum_minus)

lemma HyperSummable_negf_iff:
  "f \<in> InternalFuns \<Longrightarrow> (HyperSummable (\<lambda>n. - f n)) =  (HyperSummable f)"
by (auto simp add: HyperSummable_def HyperCauchy_def hypersum_minus)

lemma hypersum_left_distrib:
  assumes "f \<in> InternalFuns"  "A \<in> InternalSets"
  shows "hypersum f A * (r::'a::semiring_0 star) = hypersum (\<lambda>n. f n * r) A"
proof (cases r)
  case (star_n X)
  then show ?thesis 
    using assms 
    by (auto simp add: InternalFuns_def InternalSets_def hypersum  star_n_mult 
       starfun_n_mult_star_n_right star_n_eq_iff sum_distrib_right) 
qed

lemma hypersum_right_distrib:
  assumes "f \<in> InternalFuns" "A \<in> InternalSets" 
  shows "(r::'a::semiring_0 star) * hypersum f A  = hypersum (\<lambda>n. r * f n) A"
proof (cases r)
  case (star_n X)
  then show ?thesis 
    using assms
    by (auto simp add: InternalFuns_def InternalSets_def hypersum  star_n_mult 
       starfun_n_mult_star_n_left star_n_eq_iff sum_distrib_left) 
qed

lemma hypersum_product:
  "\<lbrakk> f \<in> InternalFuns; g \<in> InternalFuns; A \<in> InternalSets;  B \<in> InternalSets \<rbrakk> 
   \<Longrightarrow> hypersum f A * hypersum g B = 
       hypersum (\<lambda>i. hypersum (\<lambda>j. f i * (g j::'a::semiring_0 star)) B) A"
  by  (auto simp add: InternalFuns_def InternalSets_def hypersum star_n_mult 
        sum_product starfun_n_mult hypersum_right_distrib [symmetric] 
        starfun_n_mult_star_n_right star_n_eq_iff sum_distrib_right) 

lemma starfun2_to_starfun_n_lemma:
  "(\<lambda>n. (*f2* f) (star_n X) ((*fn* F) n)) = *fn* (\<lambda>n m. f (X n) (F n m))"
by (rule ext, case_tac n, auto simp add: starfun_n starfun2_star_n)

lemma starfun2_to_starfun_n_lemma2:
  "(\<lambda>n. (*f2* f) ((*fn* F) n) (star_n X)) = *fn* (\<lambda>n m. f (F n m) (X n))"
by (rule ext, case_tac n, auto simp add: starfun_n starfun2_star_n)

lemma hypersum_divide_distrib:
  assumes "f \<in> InternalFuns" 
          "A \<in> InternalSets "
  shows "hypersum f A / (r::'a::field star) = hypersum (\<lambda>n. f n / r) A"
proof (cases r)
  case (star_n X)
  then show ?thesis using assms 
    by (auto simp add: InternalFuns_def InternalSets_def hypersum star_divide_def
       starfun2_star_n starfun2_to_starfun_n_lemma2 star_n_eq_iff sum_divide_distrib)
qed

lemma HyperSummable_HFinite_mult_left:
  "\<lbrakk> f \<in> InternalFuns; (c::'a::{real_normed_algebra} star) \<in> HFinite; HyperSummable f \<rbrakk> 
   \<Longrightarrow> HyperSummable (\<lambda>n. c * f n)"
by (auto intro: approx_mult2 simp add: HyperSummable_def HyperCauchy_def 
             hypersum_right_distrib [symmetric])

lemma HyperSummable_divide:
  assumes "f \<in> InternalFuns" 
          "HyperSummable f" 
          "r \<notin> Infinitesimal" 
  shows "HyperSummable (\<lambda>n. f n / (r::'a::{real_normed_field} star))"
proof -
  have "1/r \<in> HFinite"
    by (metis Infinitesimal_inverse_HFinite assms(3) inverse_eq_divide)
  then have "HyperSummable (\<lambda>n. 1/r * f n)"
    using HyperSummable_HFinite_mult_left assms(1) assms(2) by blast
  then show ?thesis by simp
qed


end