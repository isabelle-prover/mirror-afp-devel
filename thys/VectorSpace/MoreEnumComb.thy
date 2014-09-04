theory MoreEnumComb
imports Main
        "~~/src/HOL/Library/FuncSet"
        "~~/src/HOL/Number_Theory/Binomial"
        Vectors
begin



(*
lemma binom_choose:
  fixes m n
  assumes "0\<le>m" "m\<le>n"
  shows "finite (combinations n m)" "card (combinations n m) = n choose m" (is "?c m n = n choose m")
proof - 
(*show it satisfies the same recurrence relation*)
  have "\<And>k. ?c k 0 = (if k = 0 then 1 else 0)"
  proof -
    fix k 
    have "combinations 0 k = (if k=0 then {[]} else {})"
      by (unfold combinations_def Avector_def, auto)
    thus "?thesis k" by auto
  qed
  have "\<And>n k. ?c (Suc n) k = (if k = 0 then 1 else (?c n  (k - 1)) + (?c n k))"
  proof -
    fix n k 
    let ?A="(\<lambda>l. 0 # l)` (combinations n k)"
    let ?B="(\<lambda>l. 1 # l)` (combinations n (k - 1))"
    have emptyI: "?A \<inter> ?B ={}" by auto
    have union: "combinations (Suc n) k = ?A \<union> ?B"
    proof -
      have "\<And> li. li\<in> combinations (Suc n) k \<Longrightarrow>  li \<in> ?A \<union> ?B"
      proof - 
        fix li
        assume li: "li\<in> combinations (Suc n) k"
        from li have nonempty: "li \<noteq> []" by (unfold combinations_def Avector_def, auto)
        from li nonempty obtain x li2 where x: "li = x#li2" "x=0 \<or> x=1"
          apply (unfold combinations_def Avector_def, auto)
          by (metis list.exhaust nat.distinct(1) neq0_conv nth_Cons_0)
        from li x have c1: "Avector li2 {0,1} n" by (unfold combinations_def Avector_def, auto)
        show "?thesis li"
        proof (rule disjE[OF x(2), where ?R ="li \<in> ?A \<union> ?B"])
          assume x0: "x=0"      
          from x x0 have c2: "(\<Sum>x \<leftarrow> li. x) = (\<Sum>x \<leftarrow> li2. x)" by auto
          from li x c1 c2 show ?thesis 
            by (unfold combinations_def image_def, auto)
        next
          assume x0: "x=1"  
          from x x0 have c2: "(\<Sum>x \<leftarrow> li. x) = (\<Sum>x \<leftarrow> li2. x) + 1" by auto
          from li x c1 c2 show ?thesis 
            by (unfold combinations_def image_def, auto)
      qed
    qed
    show fin: "finite (combinations n m)"
    proof -
      have f1: "combinations n m \<subseteq> Avector l n" by (unfold combinations_def, auto)
      from assms have f2: "finite (Avector l n)" by (intro Avectors_card(1), auto)
      from f1 f2 show ?thesis by (metis finite_subset)
    qed
    from emptyI union fin show ?thesis 
(*easy*)
sorry
*)

(*replicate and sep*)

definition subsets::"'a set \<Rightarrow> nat \<Rightarrow> 'a set set"
  where "subsets B m  = {A. A\<subseteq>B \<and> card A = m}"

definition combinations::"nat \<Rightarrow> nat \<Rightarrow> bool list set"
  where "combinations n m  = {l::bool list. (vector l n \<and> 
    (card {i. i<n \<and> l!i}) = m)}"

(*theorem n_subsets: "finite A \<Longrightarrow> card {B. B \<subseteq> A \<and> card B = k} = (card A choose k)"*)
theorem subsets_card:
  assumes finB: "finite B"
  shows "finite (subsets B m) \<and> card (subsets B m) = binomial (card B) m"
proof - 
  from finB have bin: "card (subsets B m) = binomial (card B) m" 
    by (unfold subsets_def, rule n_subsets)
  have sub: "subsets B m \<subseteq>Pow B" by (unfold subsets_def, auto)
  from finB sub have fin: "finite (subsets B m)" 
    apply (unfold subsets_def)
    by (rule finite_subset[where ?B = "Pow B"], auto)
  from fin bin show ?thesis by auto
qed

abbreviation comb_to_subset:: "bool list \<Rightarrow> nat set" where
  "comb_to_subset l \<equiv> {i. i < length l \<and> l!i = True}"

abbreviation subset_to_comb:: "nat \<Rightarrow> nat set \<Rightarrow> bool list" where
  "subset_to_comb n B \<equiv> [(i\<in>B). i <- [0..<n]]"

lemma ith: 
  assumes n: "n>0" and i: "i<n"
  shows "[f i. i <- [0..<n]] ! i = f i"
proof -
  from n i show ?thesis by auto
qed

lemma and_simp:
  assumes "P\<Longrightarrow>Q=R"
  shows "(P\<and>Q) = (P \<and> R)"
proof - 
  from assms show ?thesis by (simp cong: conj_cong)
qed

theorem combs_card:
  "finite (combinations n m) \<and> card (combinations n m) = binomial n m"
proof (rule bijection_proof[where ?A="combinations n m" and ?B="subsets {0..<n} m" 
    and ?f="comb_to_subset" and ?g="subset_to_comb n"])
  show "inverses (combinations n m) (subsets {0..<n} m) comb_to_subset (subset_to_comb n)"
      apply (unfold combinations_def subsets_def vector_def)
      apply auto
      apply (auto cong: conj_cong)
      apply (subgoal_tac "{i. i < n \<and> i \<in> x} = x", auto)
      by (intro nth_equalityI, auto)
next
  have card: "n=card {0..<n}" by auto
  show " finite (subsets {0..<n} m) \<and> card (subsets {0..<n} m) = n choose m" 
    apply (subst (3) card)
    by (intro subsets_card[where ?B="{0..<n}"], auto)
qed

fun sep:: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "sep y [] = []"
  | "sep y [x] = x"
  | "sep y (x#xs) = ((x @ [y]) @ sep y xs)"

(*alternative - use replicate?*)
fun count_vector:: "bool list \<Rightarrow> nat list" where
  "count_vector [] = [0]"
  | "count_vector (True#xs) = 
      (let c = count_vector xs in 
        list_update c 0 (c ! 0 + 1))"
  | "count_vector (False#xs) = 
      (0#(count_vector xs))"
(*        (list_update (count_vector xs) 0 ((count_vector xs) ! 0 + 1))"
*)


lemma list_equal:
  fixes  l m 
  assumes  "length l = length m" "\<And>i. i< length l\<Longrightarrow> l!i=m!i"
  shows "l=m"
proof - 
  from assms show ?thesis
  by (metis list_eq_iff_nth_eq)
(*"(xs = ys) = (length xs = length ys \<and> (ALL i<length xs. xs!i = ys!i))"*)
qed
end
