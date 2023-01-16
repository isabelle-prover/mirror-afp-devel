section \<open>Deciding the Generalized Multiset Ordering is in NP\<close>

text \<open>We first define a SAT-encoding for the comparison of two multisets w.r.t. two relations S and NS,
  then show soundness of the encoding and finally show that the size of the encoding is quadratic in the input.\<close>

theory
  Multiset_Ordering_in_NP
imports
  Multiset_Ordering_More
  Propositional_Formula
begin

subsection \<open>Locale for Generic Encoding\<close>

text \<open>We first define a generic encoding which may be instantiated for both propositional formulas
  and for CNFs. Here, we require some encoding primitives with the semantics specified in the 
  enc-sound assumptions.\<close>

locale encoder = 
  fixes eval :: "('a \<Rightarrow> bool) \<Rightarrow> 'f \<Rightarrow> bool" 
  and enc_False :: "'f" 
  and enc_True :: 'f
  and enc_pos :: "'a \<Rightarrow> 'f" 
  and enc_neg :: "'a \<Rightarrow> 'f" 
  and enc_different :: "'a \<Rightarrow> 'a \<Rightarrow> 'f" 
  and enc_equiv_and_not :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'f" 
  and enc_equiv_ite :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'f"
  and enc_ite :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'f"
  and enc_impl :: "'a \<Rightarrow> 'f \<Rightarrow> 'f" 
  and enc_var_impl :: "'a \<Rightarrow> 'a \<Rightarrow> 'f" 
  and enc_not_and :: "'a \<Rightarrow> 'a \<Rightarrow> 'f"
  and enc_not_all :: "'a list \<Rightarrow> 'f"
  and enc_conj :: "'f list \<Rightarrow> 'f" 
assumes enc_sound[simp]: 
  "eval \<alpha> (enc_False) = False"
  "eval \<alpha> (enc_True) = True" 
  "eval \<alpha> (enc_pos x) = \<alpha> x"
  "eval \<alpha> (enc_neg x) = (\<not> \<alpha> x)"
  "eval \<alpha> (enc_different x y) = (\<alpha> x \<noteq> \<alpha> y)" 
  "eval \<alpha> (enc_equiv_and_not x y z) = (\<alpha> x \<longleftrightarrow> \<alpha> y \<and> \<not> \<alpha> z)" 
  "eval \<alpha> (enc_equiv_ite x y z u) = (\<alpha> x \<longleftrightarrow> (if \<alpha> y then \<alpha> z else \<alpha> u))" 
  "eval \<alpha> (enc_ite x y z) = (if \<alpha> x then \<alpha> y else \<alpha> z)" 
  "eval \<alpha> (enc_impl x f) = (\<alpha> x \<longrightarrow> eval \<alpha> f)" 
  "eval \<alpha> (enc_var_impl x y) = (\<alpha> x \<longrightarrow> \<alpha> y)" 
  "eval \<alpha> (enc_not_and x y) = (\<not> (\<alpha> x \<and> \<alpha> y))" 
  "eval \<alpha> (enc_not_all xs) = (\<not> (Ball (set xs) \<alpha>))" 
  "eval \<alpha> (enc_conj fs) = (Ball (set fs) (eval \<alpha>))" 
begin

subsection \<open>Definition of the Encoding\<close>

text \<open>We need to encode formulas of the shape that exactly one variable
  is evaluated to true. Here, we use the linear encoding of 
   \<^cite>\<open>\<open>Section~5.3\<close> in "DBLP:journals/jsat/EenS06"\<close>
  that requires some auxiliary variables. More precisely, for each
  propositional variable that we want to count we require two auxiliary variables.\<close>

fun encode_sum_0_1_main :: "('a \<times> 'a \<times> 'a) list \<Rightarrow> 'f list \<times> 'a \<times> 'a" where
  "encode_sum_0_1_main [(x, zero, one)] = ([enc_different zero x], zero, x)" 
| "encode_sum_0_1_main ((x, zero, one) # rest) = (case encode_sum_0_1_main rest of
      (conds, fzero, fone) \<Rightarrow> let
        czero = enc_equiv_and_not zero fzero x;
        cone  = enc_equiv_ite one x fzero fone
       in (czero # cone # conds, zero, one))" 

definition encode_exactly_one :: "('a \<times> 'a \<times> 'a) list \<Rightarrow> 'f \<times> 'f list" where
  "encode_exactly_one vars = (case vars of [] \<Rightarrow> (enc_False, [])
      | [(x,_,_)] \<Rightarrow> (enc_pos x, [])
      | ((x,_,_) # vars) \<Rightarrow> (case encode_sum_0_1_main vars of (conds, zero, one) 
              \<Rightarrow> (enc_ite x zero one, conds)))" 

fun encodeGammaCond :: "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'f" where
  "encodeGammaCond gam eps True True = enc_True" 
| "encodeGammaCond gam eps False False = enc_neg gam" 
| "encodeGammaCond gam eps False True = enc_var_impl gam eps" 
| "encodeGammaCond gam eps True False = enc_not_and gam eps" 
end

text \<open>The encoding of the multiset comparisons is based on \<^cite>\<open>\<open>Sections~3.6 and 3.7\<close> in "RPO_NP"\<close>.
  It uses propositional variables $\gamma_{ij}$ and $\epsilon_i$. 
  We further add auxiliary variables that are required for the exactly-one-encoding.\<close>

datatype PropVar = Gamma nat nat | Epsilon nat 
  | AuxZeroJI nat nat | AuxOneJI nat nat
  | AuxZeroIJ nat nat | AuxOneIJ nat nat

text \<open>At this point we define a new locale as an instance of @{locale encoder} where the 
  type of propositional variables is fixed to @{typ PropVar}.\<close>

locale ms_encoder = encoder eval for eval :: "(PropVar \<Rightarrow> bool) \<Rightarrow> 'f \<Rightarrow> bool" 
begin

definition formula14 :: "nat \<Rightarrow> nat \<Rightarrow> 'f list" where
"formula14 n m = (let 
    inner_left = \<lambda> j. case encode_exactly_one (map (\<lambda> i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0 ..< n])
       of (one, cands) \<Rightarrow> one # cands;
    left = List.maps inner_left [0 ..< m];
    inner_right = \<lambda> i. encode_exactly_one (map (\<lambda> j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0 ..< m]);
    right = List.maps (\<lambda> i. case inner_right i of (one, cands) \<Rightarrow> enc_impl (Epsilon i) one # cands) [0 ..< n]
    in left @ right)"

definition formula15 :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list" where
"formula15 cs cns n m = (let 
   conjs = List.maps (\<lambda> i. List.maps (\<lambda> j. let s = cs i j; ns = cns i j in 
       if s \<and> ns then [] else [encodeGammaCond (Gamma i j) (Epsilon i) s ns]) [0 ..< m]) [0 ..< n]  
  in conjs @ formula14 n m)" 

definition formula16 :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list" where
"formula16 cs cns n m = (enc_not_all (map Epsilon [0 ..< n]) # formula15 cs cns n m)" 

text \<open>The main encoding function. It takes a function as input
  that returns for each pair of elements a pair of Booleans, and
  these indicate whether the elements are strictly or weakly decreasing. Moreover, two input lists are given.
  Finally two formulas are returned, where the first is satisfiable iff the two lists are strictly decreasing w.r.t.
  the multiset ordering, and second is satisfiable iff there is a weak decrease w.r.t. the multiset ordering.\<close>

definition encode_mul_ext :: "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'f \<times> 'f" where
  "encode_mul_ext s_ns xs ys = (let 
     n = length xs; 
     m = length ys; 
     cs = (\<lambda> i j. fst (s_ns (xs ! i) (ys ! j)));
     cns = (\<lambda> i j. snd (s_ns (xs ! i) (ys ! j)));
     f15 = formula15 cs cns n m;
     f16 = enc_not_all (map Epsilon [0 ..< n]) # f15
    in (enc_conj f16, enc_conj f15))" 
end

subsection \<open>Soundness of the Encoding\<close>

context encoder
begin

abbreviation eval_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> bool" where
  "eval_all \<alpha> fs \<equiv> (Ball (set fs) (eval \<alpha>))" 

lemma encode_sum_0_1_main: assumes "encode_sum_0_1_main vars = (conds, zero, one)"
  and "\<And> i x ze on re. prop \<Longrightarrow> i < length vars \<Longrightarrow> drop i vars = ((x,ze,on) # re) \<Longrightarrow>
       (\<alpha> ze \<longleftrightarrow> \<not> (\<exists> y \<in> insert x (fst ` set re). \<alpha> y))
     \<and> (\<alpha> on \<longleftrightarrow> (\<exists>! y \<in> insert x (fst ` set re). \<alpha> y))"
  and "\<not> prop \<Longrightarrow> eval_all \<alpha> conds" 
  and "distinct (map fst vars)"
  and "vars \<noteq> []" 
shows "eval_all \<alpha> conds
  \<and> (\<alpha> zero \<longleftrightarrow> \<not> (\<exists> x \<in> fst ` set vars. \<alpha> x))
  \<and> (\<alpha> one \<longleftrightarrow> (\<exists>! x \<in> fst ` set vars. \<alpha> x))" 
  using assms
proof (induct vars arbitrary: conds zero one rule: encode_sum_0_1_main.induct)
  case (1 x zero' one' conds zero one)
  from 1(1,3-) 1(2)[of 0] show ?case by (cases "prop", auto)
next
  case Cons: (2 x zero one r rr conds' zero' one')
  let ?triple = "(x,zero,one)" 
  let ?rest = "r # rr" 
  obtain conds fzero fone where res: "encode_sum_0_1_main ?rest = (conds, fzero, fone)" 
    by (cases "encode_sum_0_1_main ?rest", auto)
  from Cons(2)[unfolded encode_sum_0_1_main.simps res split Let_def]
  have zero: "zero' = zero" and one: "one' = one" and
       conds': "conds' = enc_equiv_and_not zero fzero x # enc_equiv_ite one x fzero fone # conds" 
    by auto
  from Cons(5) have x: "x \<notin> fst ` set ?rest" 
      and dist: "distinct (map fst ?rest)" by auto
  have "eval_all \<alpha> conds \<and> \<alpha> fzero = (\<not> (\<exists>a\<in>fst ` set ?rest. \<alpha> a)) \<and> \<alpha> fone = (\<exists>!x. x \<in> fst ` set ?rest \<and> \<alpha> x)" 
    apply (rule Cons(1)[OF res _ _ dist])
    subgoal for i x ze on re using Cons(3)[of "Suc i" x ze on re] by auto
    subgoal using Cons(4) unfolding conds' by auto
    subgoal by auto
    done
  hence IH: "eval_all \<alpha> conds" "\<alpha> fzero = (\<not> (\<exists>a\<in>fst ` set ?rest. \<alpha> a))" 
    "\<alpha> fone = (\<exists>!x. x \<in> fst ` set ?rest \<and> \<alpha> x)" by auto
  show ?case
  proof (cases "prop")
    case True
    from Cons(3)[of 0 x zero one ?rest, OF True]
    have id: "\<alpha> zero = (\<forall>y\<in> insert x (fst ` set ?rest). \<not> \<alpha> y)" 
      "\<alpha> one = (\<exists>!y. y \<in> insert x (fst ` set ?rest) \<and> \<alpha> y)"  by auto 
    show ?thesis unfolding zero one conds' eval.simps using x IH(1)
      apply (simp add: IH id) 
      by blast
  next
    case False
    from Cons(4)[OF False, unfolded conds']
    have id: "\<alpha> zero = (\<not> \<alpha> x \<and> \<alpha> fzero)" 
       "\<alpha> one = (\<alpha> x \<and> \<alpha> fzero \<or> \<not> \<alpha> x \<and> \<alpha> fone)" by auto 
    show ?thesis unfolding zero one conds' eval.simps using x IH(1)
      apply (simp add: IH id) 
      by blast
  qed
qed auto

lemma encode_exactly_one_complete: assumes "encode_exactly_one vars = (one, conds)" 
  and "\<And> i x ze on. i < length vars \<Longrightarrow> 
        vars ! i = (x,ze,on) \<Longrightarrow>
       (\<alpha> ze \<longleftrightarrow> \<not> (\<exists> y \<in> fst ` set (drop i vars). \<alpha> y))
     \<and> (\<alpha> on \<longleftrightarrow> (\<exists>! y \<in> fst ` set (drop i vars). \<alpha> y))"
  and "distinct (map fst vars)" 
shows "eval_all \<alpha> conds \<and> (eval \<alpha> one \<longleftrightarrow> (\<exists>! x \<in> fst ` set vars. \<alpha> x))" 
proof -
  consider (empty) "vars = []" | (single) x ze on where "vars = [(x,ze,on)]" 
    | (other) x ze on v vs where "vars = (x,ze,on) # v # vs" 
    by (cases vars; cases "tl vars"; auto)
  thus ?thesis
  proof cases
    case (other x ze' on' v vs)
    obtain on zero where res: "encode_sum_0_1_main (v # vs) = (conds, zero, on)"   
      and one: "one = enc_ite x zero on"  
      using assms(1) unfolding encode_exactly_one_def other split list.simps 
      by (cases "encode_sum_0_1_main (v # vs)", auto)
    let ?vars = "v # vs" 
    define vars' where "vars' = ?vars" 
    from assms(3) other have dist: "distinct (map fst ?vars)" by auto
    have main: "eval_all \<alpha> conds  \<and> (\<alpha> zero \<longleftrightarrow> \<not> (\<exists> x \<in> fst ` set ?vars. \<alpha> x))
      \<and> (\<alpha> on \<longleftrightarrow> (\<exists>! x \<in> fst ` set ?vars. \<alpha> x))" 
      apply (rule encode_sum_0_1_main[OF res _ _ dist, of True])
      subgoal for i x ze on re using assms(2)[of "Suc i" x ze on] unfolding other 
        by (simp add: nth_via_drop)
      by auto
    hence conds: "eval_all \<alpha> conds" and zero: "\<alpha> zero \<longleftrightarrow> \<not> (\<exists> x \<in> fst ` set ?vars. \<alpha> x)" 
      and on: "\<alpha> on \<longleftrightarrow> (\<exists>! x \<in> fst ` set ?vars. \<alpha> x)" by auto
    have one: "eval \<alpha> one \<longleftrightarrow> (\<exists>! x \<in> fst ` set vars. \<alpha> x)" 
      unfolding one 
      apply (simp)
      using assms(3)
      unfolding zero on other vars'_def[symmetric] by simp blast
    show ?thesis using one conds by auto
  next
    case empty
    with assms have "one = enc_False" by (auto simp: encode_exactly_one_def)
    hence "eval \<alpha> one = False" by auto
    with assms empty show ?thesis by (auto simp: encode_exactly_one_def)
  qed (insert assms, auto simp: encode_exactly_one_def)
qed

lemma encode_exactly_one_sound: assumes "encode_exactly_one vars = (one, conds)"
  and "distinct (map fst vars)" 
  and "eval \<alpha> one"
  and "eval_all \<alpha> conds" 
shows "\<exists>! x \<in> fst ` set vars. \<alpha> x" 
proof -
  consider (empty) "vars = []" | (single) x ze on where "vars = [(x,ze,on)]" 
    | (other) x ze on v vs where "vars = (x,ze,on) # v # vs" 
    by (cases vars; cases "tl vars"; auto)
  thus ?thesis
  proof cases
    case (other x ze' on' v vs)
    obtain on zero where res: "encode_sum_0_1_main (v # vs) = (conds, zero, on)"   
      and one: "one = enc_ite x zero on" 
      using assms(1) unfolding encode_exactly_one_def other split list.simps 
      by (cases "encode_sum_0_1_main (v # vs)", auto)
    let ?vars = "v # vs" 
    define vars' where "vars' = ?vars" 
    from assms(2) other have dist: "distinct (map fst ?vars)" by auto
    have main: "eval_all \<alpha> conds  \<and> (\<alpha> zero \<longleftrightarrow> \<not> (\<exists> x \<in> fst ` set ?vars. \<alpha> x))
      \<and> (\<alpha> on \<longleftrightarrow> (\<exists>! x \<in> fst ` set ?vars. \<alpha> x))" 
      by (rule encode_sum_0_1_main[OF res _ assms(4) dist, of False], auto)
    hence conds: "eval_all \<alpha> conds" and zero: "\<alpha> zero \<longleftrightarrow> \<not> (\<exists> x \<in> fst ` set ?vars. \<alpha> x)" 
      and on: "\<alpha> on \<longleftrightarrow> (\<exists>! x \<in> fst ` set ?vars. \<alpha> x)" by auto
    have one: "eval \<alpha> one \<longleftrightarrow> (\<exists>! x \<in> fst ` set vars. \<alpha> x)" 
      unfolding one 
      apply (simp)
      using assms(2)
      unfolding zero on other vars'_def[symmetric] by simp blast
    with assms show ?thesis by auto
  next
    case empty
    with assms have "one = enc_False" by (auto simp: encode_exactly_one_def)
    hence "eval \<alpha> one = False" by auto
    with assms empty show ?thesis by (auto simp: encode_exactly_one_def)
  qed (insert assms, auto simp: encode_exactly_one_def)
qed

lemma encodeGammaCond[simp]: "eval \<alpha> (encodeGammaCond gam eps s ns) =
  (\<alpha> gam \<longrightarrow> (\<alpha> eps \<longrightarrow> ns) \<and> (\<not> \<alpha> eps \<longrightarrow> s))" 
  by (cases ns; cases s, auto)

lemma eval_all_append[simp]: "eval_all \<alpha> (fs @ gs) = (eval_all \<alpha> fs \<and> eval_all \<alpha> gs)" 
  by auto

lemma eval_all_Cons[simp]: "eval_all \<alpha> (f # gs) = (eval \<alpha> f \<and> eval_all \<alpha> gs)"
  by auto

lemma eval_all_concat[simp]: "eval_all \<alpha> (concat fs) = (\<forall> f \<in> set fs. eval_all \<alpha> f)"
  by auto

lemma eval_all_maps[simp]: "eval_all \<alpha> (List.maps f fs) = (\<forall> g \<in> set fs. eval_all \<alpha> (f g))"
  unfolding List.maps_def eval_all_concat by auto
end

context ms_encoder
begin

context
  fixes s t :: "nat \<Rightarrow> 'a"
    and n m :: nat
    and S NS :: "'a rel"
    and cs cns
assumes cs: "\<And> i j. cs i j = ((s i, t j) \<in> S)" 
  and cns:  "\<And> i j. cns i j = ((s i, t j) \<in> NS)"
begin

lemma encoding_sound: 
  assumes eval15: "eval_all v (formula15 cs cns n m)" 
  shows "(mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> ns_mul_ext NS S" 
    "eval_all v (formula16 cs cns n m) \<Longrightarrow> (mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> s_mul_ext NS S" 
proof -
  from eval15[unfolded formula15_def]
  have eval14: "eval_all v (formula14 n m)" by auto
  define property where "property i = v (Epsilon i)" for i
  define j_of_i :: "nat \<Rightarrow> nat" 
    where "j_of_i i = (THE j. j < m \<and> v (Gamma i j))" for i
  define i_of_j :: "nat \<Rightarrow> nat" 
    where "i_of_j j = (THE i. i < n \<and> v (Gamma i j))" for j
  define xs1 where "xs1 = filter (\<lambda> i. property i) [0 ..< n]" 
  define xs2 where "xs2 = filter (\<lambda> i. \<not> property i) [0 ..< n]" 
  define ys1 where "ys1 = map j_of_i xs1" 
  define ys2 where "ys2 = filter (\<lambda> j. j \<notin> set ys1) [0 ..< m]" 
  let ?xs1 = "map s xs1"
  let ?xs2 = "map s xs2" 
  let ?ys1 = "map t ys1"
  let ?ys2 = "map t ys2"
  {
    fix i
    assume *: "i < n" "v (Epsilon i)" 
    let ?vars = "map (\<lambda>j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0..<m]" 
    obtain one conds where enc: "encode_exactly_one ?vars = (one,conds)" by force
    have dist: "distinct (map fst ?vars)" unfolding map_map o_def fst_conv
      unfolding distinct_map by (auto simp: inj_on_def)
    have "eval_all v (enc_impl (Epsilon i) one # conds)" 
      using eval14[unfolded formula14_def Let_def eval_all_append, unfolded eval_all_maps, THEN conjunct2] *(1) enc by force
    with * have "eval v one" "eval_all v conds" by auto
    from encode_exactly_one_sound[OF enc dist this]
    have 1: "\<exists>!x. x \<in> set (map (\<lambda>j. Gamma i j) [0..<m]) \<and> v x" 
      by (simp add: image_comp)
    have 2: "(\<exists>!x. x \<in> set (map (\<lambda>j. Gamma i j) [0..<m]) \<and> v x) =
         (\<exists>! j. j < m \<and> v (Gamma i j))" by fastforce
    have 3: "\<exists>! j. j < m \<and> v (Gamma i j)" using 1 2 by auto
    have "j_of_i i < m \<and> v (Gamma i (j_of_i i))" 
      using 3 unfolding j_of_i_def
      by (metis (no_types, lifting) the_equality)
    note this 3
  } note j_of_i = this
  {
    fix j
    assume *: "j < m"  
    let ?vars = "map (\<lambda>i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0..<n]" 
    have dist: "distinct (map fst ?vars)" unfolding map_map o_def fst_conv
      unfolding distinct_map by (auto simp: inj_on_def)
    obtain one conds where enc: "encode_exactly_one ?vars = (one,conds)" by force
    have "eval_all v (one # conds)" 
      using eval14[unfolded formula14_def Let_def eval_all_append, unfolded eval_all_maps, THEN conjunct1] *(1) enc by force
    hence "eval v one" "eval_all v conds" by auto
    from encode_exactly_one_sound[OF enc dist this]
    have 1: "\<exists>!x. x \<in> set (map (\<lambda>i. Gamma i j) [0..<n]) \<and> v x" 
      by (simp add: image_comp)
    have 2: "(\<exists>!x. x \<in> set (map (\<lambda>i. Gamma i j) [0..<n]) \<and> v x) =
         (\<exists>! i. i < n \<and> v (Gamma i j))" by fastforce
    have 3: "\<exists>! i. i < n \<and> v (Gamma i j)" using 1 2 by auto
    have "i_of_j j < n \<and> v (Gamma (i_of_j j) j)" 
      using 3 unfolding i_of_j_def
      by (metis (no_types, lifting) the_equality)
    note this 3
  } note i_of_j = this

  have len: "length ?xs1 = length ?ys1"
    unfolding ys1_def by simp
  note goals = len
  {
    fix k
    define i where "i = xs1 ! k" 
    assume "k < length ?ys1" 
    hence k: "k < length xs1" using len by auto
    hence "i \<in> set xs1" using i_def by simp
    hence ir: "i < n" "v (Epsilon i)" 
      unfolding xs1_def property_def by auto
    from j_of_i this
    have **: "j_of_i i < m \<and> v (Gamma i (j_of_i i))" by auto
    have ys1k: "?ys1 ! k = t (j_of_i i)" unfolding i_def ys1_def using k by auto
    have xs1k: "?xs1 ! k = s i" unfolding i_def using k by auto
    from eval15 have "\<forall>i\<in>{0..<n}.
        \<forall>j\<in>{0..<m}. v (Gamma i j) \<longrightarrow> (v (Epsilon i) \<longrightarrow> cns i j)" 
      unfolding formula15_def Let_def eval_all_append eval_all_maps
      by (auto split: if_splits)
    hence "cns i (j_of_i i)" using ** ir by auto
    then have "(?xs1 ! k, ?ys1 ! k) \<in> NS" 
      unfolding xs1k ys1k using cns[of i "(j_of_i i)"] by (auto split: if_splits)
  } note step2 = this
  note goals = goals this
  have xexp : "mset (map s [0..<n]) = mset ?xs1 + mset ?xs2" 
    unfolding xs1_def xs2_def
    using mset_map_filter 
    by metis
  note goals = goals this
  {
    fix i
    assume "i < n" "property i" 
    hence "i_of_j (j_of_i i) = i" 
      using i_of_j j_of_i[of i] unfolding property_def by auto
  } note i_of_j_of_i = this
  have "mset ys1 = mset (filter (\<lambda>j. j \<in> set (map j_of_i xs1)) [0..<m])"
    (is "mset ?l = mset ?r")
  proof -
    have dl: "distinct ?l" unfolding ys1_def xs1_def distinct_map
    proof
      show "distinct (filter property [0..<n])" by auto
      show "inj_on j_of_i (set (filter property [0..<n]))" 
        by (intro inj_on_inverseI[of _ i_of_j], insert i_of_j_of_i, auto)
    qed
    have dr: "distinct ?r" by simp
    have id: "set ?l = set ?r" unfolding ys1_def xs1_def using j_of_i i_of_j
      by (auto simp: property_def)
    from dl dr id show ?thesis using set_eq_iff_mset_eq_distinct by blast
  qed      
  hence ys1: "mset (map t ys1) = mset (map t ?r)" by simp
  have yeyp: "mset (map t [0..<m]) = mset ?ys1 + mset ?ys2" 
    unfolding ys1 ys2_def unfolding ys1_def mset_map_filter ..
  note goals = goals this
  {
    fix y
    assume "y \<in> set ?ys2"
    then obtain j where j: "j \<in> set ys2" and y: "y = t j" by auto
    from j[unfolded ys2_def ys1_def]
    have j: "j < m" and nmem: "j \<notin> set (map j_of_i xs1)" by auto
    let ?i = "i_of_j j" 
    from i_of_j[OF j] have i: "?i < n" and gamm: "v (Gamma ?i j)" by auto
    from eval15[unfolded formula15_def Let_def eval_all_append eval_all_maps] i j gamm
    have "\<not> v (Epsilon ?i) \<Longrightarrow> cs ?i j" by (force split: if_splits)
    moreover have not: "\<not> v (Epsilon ?i)" using nmem i j i_of_j j_of_i
      unfolding xs1_def property_def
      by (metis atLeast0LessThan filter_set imageI lessThan_iff list.set_map member_filter set_upt)
    ultimately have "cs ?i j" by simp
    hence sy: "(s ?i,y) \<in> S" unfolding y using cs[of ?i j] by (auto split: if_splits) 
    from not i have "?i \<in> set xs2" unfolding xs2_def property_def by auto
    hence "s ?i \<in> set ?xs2" by simp
    hence "\<exists> x \<in> set ?xs2. (x,y) \<in> S" using sy by auto
  }
  note goals = goals this

  show "(mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> ns_mul_ext NS S" 
    by (rule ns_mul_ext_intro[OF goals(3,4,1,2,5)])  

  assume "eval_all v (formula16 cs cns n m)" 
  from this[unfolded formula16_def Let_def]
  obtain i where i: "i < n" and v: "\<not> v (Epsilon i)" by auto
  hence "i \<in> set xs2" unfolding xs2_def property_def by auto
  hence "?xs2 \<noteq> []" by auto
  note goals = goals this
  show "(mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> s_mul_ext NS S" 
    by (rule s_mul_ext_intro[OF goals(3,4,1,2,6,5)])  
qed

lemma bex1_cong: "X = Y \<Longrightarrow> (\<And> x. x \<in> Y \<Longrightarrow> P x = Q x) \<Longrightarrow> (\<exists>!x. x \<in> X \<and> P x) = (\<exists>!x. x \<in> Y \<and> Q x)" 
  by auto

lemma encoding_complete: 
  assumes "(mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> ns_mul_ext NS S" 
  shows "(\<exists> v. eval_all v (formula15 cs cns n m) \<and> 
    ((mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> s_mul_ext NS S \<longrightarrow> eval_all v (formula16 cs cns n m)))" 
proof -
  let ?S = "(mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> s_mul_ext NS S" 
  from ns_mul_ext_elim[OF assms] s_mul_ext_elim[of "mset (map s [0..<n])" "mset (map t [0..<m])" NS S]
  obtain Xs1 Xs2 Ys1 Ys2 where
    eq1: "mset (map s [0..<n]) = mset Xs1 + mset Xs2" and
    eq2: "mset (map t [0..<m]) = mset Ys1 + mset Ys2" and
    len: "length Xs1 = length Ys1" and
    ne: "?S \<Longrightarrow> Xs2 \<noteq> []" and
    NS: "\<And> i. i<length Ys1 \<Longrightarrow> (Xs1 ! i, Ys1 ! i) \<in> NS" and
    S: "\<And>  y. y\<in>set Ys2 \<Longrightarrow> \<exists>x\<in>set Xs2. (x, y) \<in> S"
    by blast
  from mset_map_split[OF eq1] obtain xs1 xs2 where 
      xs: "mset [0..<n] = mset xs1 + mset xs2" 
    and xs1: "Xs1 = map s xs1" 
    and xs2: "Xs2 = map s xs2" by auto
  from mset_map_split[OF eq2] obtain ys1 ys2 where 
      ys: "mset [0..<m] = mset ys1 + mset ys2" 
    and ys1: "Ys1 = map t ys1" 
    and ys2: "Ys2 = map t ys2" by auto
  from xs have dist_xs: "distinct (xs1 @ xs2)" 
    by (metis distinct_upt mset_append mset_eq_imp_distinct_iff)
  from xs have un_xs: "set xs1 \<union> set xs2 = {..<n}"
    by (metis atLeast_upt set_mset_mset set_mset_union)
  from ys have dist_ys: "distinct (ys1 @ ys2)" 
    by (metis distinct_upt mset_append mset_eq_imp_distinct_iff)
  from ys have un_ys: "set ys1 \<union> set ys2 = {..<m}"
    by (metis atLeast_upt set_mset_mset set_mset_union)  
  define pos_of where "pos_of xs i = (THE p. p < length xs \<and> xs ! p = i)" for i and xs :: "nat list" 
  from dist_xs dist_ys have "distinct xs1" "distinct ys1" by auto
  {
    fix xs :: "nat list" and x
    assume dist: "distinct xs" and x: "x \<in> set xs" 
    hence one: "\<exists>! i. i < length xs \<and> xs ! i = x" by (rule distinct_Ex1)
    from theI'[OF this, folded pos_of_def]
    have "pos_of xs x < length xs" "xs ! pos_of xs x = x" by auto
    note this one
  } note pos = this
  note p_xs = pos[OF \<open>distinct xs1\<close>]
  note p_ys = pos[OF \<open>distinct ys1\<close>]
  define i_of_j2 where "i_of_j2 j = (SOME i. i \<in> set xs2 \<and> cs i j)" for j 
  define v' :: "PropVar \<Rightarrow> bool" where
   "v' x = (case x of
       Epsilon i \<Rightarrow> i \<in> set xs1
     | Gamma i j \<Rightarrow> (i \<in> set xs1 \<and> j \<in> set ys1 \<and> i = xs1 ! pos_of ys1 j
           \<or> i \<in> set xs2 \<and> j \<in> set ys2 \<and> i = i_of_j2 j))" for x
  define v :: "PropVar \<Rightarrow> bool" where
    "v x = (case x of
       AuxZeroJI i j \<Rightarrow> (\<not> Bex (set (drop i (map (\<lambda>i. (Gamma i j)) [0..<n]))) v')
     | AuxOneJI i j \<Rightarrow> (\<exists>!y. y \<in> set (drop i (map (\<lambda>i. (Gamma i j)) [0..<n])) \<and> v' y)
     | AuxZeroIJ i j \<Rightarrow> (\<not> Bex (set (drop j (map (\<lambda>j. (Gamma i j)) [0..<m]))) v')
     | AuxOneIJ i j \<Rightarrow> (\<exists>!y. y \<in> set (drop j (map (\<lambda>j. (Gamma i j)) [0..<m])) \<and> v' y)
     | _ \<Rightarrow> v' x)" for x
  note v_defs = v_def v'_def
  {
    fix j
    assume j2: "j \<in> set ys2" 
    from j2 have "t j \<in> set Ys2" unfolding ys2 by auto
    from S[OF this, unfolded xs2] have "\<exists> i. i \<in> set xs2 \<and> cs i j" 
      by (auto simp: cs)
    from someI_ex[OF this, folded i_of_j2_def]
    have *: "i_of_j2 j \<in> set xs2" "cs (i_of_j2 j) j" by auto
    hence "v (Gamma (i_of_j2 j) j)" unfolding v_defs using j2 by auto
    note * this
  } note j_ys2 = this
  {
    fix j
    assume j1: "j \<in> set ys1" 
    let ?pj = "pos_of ys1 j" 
    from p_ys[OF j1] have pj: "?pj < length Ys1" and yj: "ys1 ! ?pj = j" 
      unfolding ys1 by auto
    have pj': "?pj < length Xs1" using len pj by auto
    from NS[OF pj] have "(Xs1 ! ?pj, Ys1 ! ?pj) \<in> NS" .
    also have "Ys1 ! ?pj = t j" using pj unfolding ys1 using yj by auto
    also have "Xs1 ! ?pj = s (xs1 ! ?pj)" using pj' unfolding xs1 by auto
    finally have cns: "cns (xs1 ! ?pj) j" unfolding cns .
    have mem: "xs1 ! ?pj \<in> set xs1" using pj' unfolding xs1 by auto
    have v: "v (Gamma (xs1 ! ?pj) j)" 
      unfolding v_defs using j1 mem by auto
    note mem cns v
  } note j_ys1 = this
  have 14: "eval_all v (formula14 n m)" 
    unfolding formula14_def Let_def eval_all_append eval_all_maps
  proof (intro conjI ballI, goal_cases)
    case (1 j f)
    then obtain one cands where j: "j < m" and f: "f \<in> set (one # cands)" 
      and enc: "encode_exactly_one (map (\<lambda>i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0..<n]) = (one, cands)" (is "?e = _")
      by (cases ?e, auto)
    have "eval_all v cands \<and>
          eval v one = (\<exists>!x. x \<in> fst ` set (map (\<lambda>i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0..<n]) \<and> v x)" 
      apply (rule encode_exactly_one_complete[OF enc])
      subgoal for i y ze on 
      proof (goal_cases)
        case 1
        hence ze: "ze = AuxZeroJI i j" and on: "on = AuxOneJI i j" by auto
        have id: "fst ` set (drop i (map (\<lambda>i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0..<n]))
        = set (drop i (map (\<lambda>i. (Gamma i j)) [0..<n]))"
          unfolding set_map[symmetric] drop_map by simp
        show ?thesis unfolding ze on id unfolding v_def drop_map
          by (intro conjI, force, simp, intro bex1_cong refl, auto)
      qed
      subgoal by (auto simp: distinct_map intro: inj_onI)
      done
    also have "fst ` set (map (\<lambda>i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0..<n])
       = (\<lambda>i. Gamma i j) ` set [0..<n]" unfolding set_map image_comp o_def by auto
    also have "(\<exists>!x. x \<in> \<dots> \<and> v x) = True" unfolding eq_True 
    proof -
      from j un_ys have "j \<in> set ys1 \<or> j \<in> set ys2" by auto
      thus "\<exists>!x. x \<in> (\<lambda>i. Gamma i j) ` set [0..<n] \<and> v x" 
      proof
        assume j: "j \<in> set ys2" 
        from j_ys2[OF j] un_xs have "i_of_j2 j \<in> {0..<n}" by auto
        from this j_ys2[OF j] dist_ys j
        show ?thesis 
          by (intro ex1I[of _ "(Gamma (i_of_j2 j) j)"], force, auto simp: v_defs)
      next
        assume j: "j \<in> set ys1" 
        from j_ys1[OF j] un_xs have "xs1 ! pos_of ys1 j \<in> {0..<n}" by auto
        from this j_ys1[OF j] dist_ys j
        show ?thesis 
          by (intro ex1I[of _ "(Gamma (xs1 ! pos_of ys1 j) j)"], force, auto simp: v_defs)
      qed
    qed
    finally show ?case using 1 f by auto
  next
    case (2 i f)
    then obtain one cands where i: "i < n" and f: "f \<in> set (enc_impl (Epsilon i) one # cands)" 
      and enc: "encode_exactly_one (map (\<lambda>j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0..<m]) = (one, cands)" (is "?e = _")
      by (cases ?e, auto)
    have "eval_all v cands \<and>
          eval v one = (\<exists>!x. x \<in> fst ` set (map (\<lambda>j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0..<m]) \<and> v x)" 
      apply (rule encode_exactly_one_complete[OF enc])
      subgoal for j y ze on 
      proof (goal_cases)
        case 1
        hence ze: "ze = AuxZeroIJ i j" and on: "on = AuxOneIJ i j" by auto
        have id: "fst ` set (drop j (map (\<lambda>j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0..<m]))
        = set (drop j (map (\<lambda>j. (Gamma i j)) [0..<m]))"
          unfolding set_map[symmetric] drop_map by simp
        show ?thesis unfolding ze on id unfolding v_def drop_map
          by (intro conjI, force, simp, intro bex1_cong refl, auto)
      qed
      subgoal by (auto simp: distinct_map intro: inj_onI)
      done
    also have "fst ` set (map (\<lambda>j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0..<m])
       = (\<lambda>j. Gamma i j) ` set [0..<m]" unfolding set_map image_comp o_def by auto
    finally have cands: "eval_all v cands" 
      and "eval v one = (\<exists>!x. x \<in> Gamma i ` set [0..<m] \<and> v x)" by auto
    note this(2)
    also have "v (Epsilon i) \<Longrightarrow> \<dots> = True" unfolding eq_True 
    proof -
      assume v: "v (Epsilon i)" 
      hence i_xs: "i \<in> set xs1" "i \<notin> set xs2" unfolding v_defs using dist_xs by auto
      from this[unfolded set_conv_nth] obtain p where p1: "p < length xs1" 
        and xpi: "xs1 ! p = i" by auto
      define j where "j = ys1 ! p" 
      from p1 len have p2: "p < length ys1" unfolding xs1 ys1 by auto
      hence j: "j \<in> set ys1" unfolding j_def by auto
      from p_ys[OF j] p2 have pp: "pos_of ys1 j = p" by (auto simp: j_def)
      from j un_ys have jm: "j < m" by auto
      have v: "v (Gamma i j)" unfolding v_defs using j pp xpi i_xs by simp
      {
        fix k
        assume vk: "v (Gamma i k)"
        from vk[unfolded v_defs] i_xs 
        have k: "k \<in> set ys1" and ik: "i = xs1 ! pos_of ys1 k" by auto
        from p_ys[OF k] ik xpi have id: "pos_of ys1 k = p"
          by (metis \<open>distinct xs1\<close> len length_map nth_eq_iff_index_eq p1 xs1 ys1)
        have "k = ys1 ! pos_of ys1 k" using p_ys[OF k] by auto
        also have "\<dots> = j" unfolding id j_def ..
        finally have "k = j" .
      } note unique = this
      show "\<exists>!j. j \<in> Gamma i ` set [0..<m] \<and> v j" 
        by (intro ex1I[of _ "Gamma i j"], use jm v in force, use unique in auto)
    qed
    finally show ?case using 2 f cands enc by auto
  qed
  {
    fix i j
    assume i: "i < n" and j: "j < m" 
    assume v: "v (Gamma i j)" 
    have strict: "\<not> v (Epsilon i) \<Longrightarrow> cs i j" using i j v j_ys2[of j] unfolding v_defs by auto
    {
      assume "v (Epsilon i)" 
      hence i': "i \<in> set xs1" "i \<notin> set xs2" unfolding v_defs using dist_xs by auto
      with v have j': "j \<in> set ys1" unfolding v_defs using dist_ys by auto
      from v[unfolded v_defs] i' have ii: "i = xs1 ! pos_of ys1 j" by auto
      from j_ys1[OF j', folded ii] have "cns i j" by auto
    }
    note strict this
  } note compare = this
  have 15: "eval_all v (formula15 cs cns n m)"
    unfolding formula15_def Let_def eval_all_maps eval_all_append using 14 compare by auto
  {
    assume ?S
    have 16: "\<exists>x\<in>{0..<n}. \<not> v (Epsilon x)" 
      by (rule bexI[of _ "hd xs2"]; insert ne[OF \<open>?S\<close>] xs2 un_xs dist_xs; cases xs2, auto simp: v_defs)
    have "eval_all v (formula16 cs cns n m)" 
      unfolding formula16_def Let_def using 15 16 by simp
  }
  with 15 show ?thesis by blast
qed

lemma formula15: "(mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> ns_mul_ext NS S 
  \<longleftrightarrow> (\<exists> v. eval_all v (formula15 cs cns n m))" 
  using encoding_sound encoding_complete by blast

lemma formula16: "(mset (map s [0 ..< n]), mset (map t [0 ..< m])) \<in> s_mul_ext NS S 
  \<longleftrightarrow> (\<exists> v. eval_all v (formula16 cs cns n m))" 
  using encoding_sound encoding_complete s_ns_mul_ext[of _ _ NS S] 
  unfolding formula16_def Let_def eval_all_Cons by blast
end

lemma encode_mul_ext: assumes "encode_mul_ext f xs ys = (\<phi>\<^sub>S, \<phi>\<^sub>N\<^sub>S)"
  shows "mul_ext f xs ys = ((\<exists> v. eval v \<phi>\<^sub>S), (\<exists> v. eval v \<phi>\<^sub>N\<^sub>S))" 
proof -
  have xs: "mset xs = mset (map (\<lambda> i. xs ! i) [0 ..< length xs])" by (simp add: map_nth)
  have ys: "mset ys = mset (map (\<lambda> i. ys ! i) [0 ..< length ys])" by (simp add: map_nth)
  from assms[unfolded encode_mul_ext_def Let_def, simplified]
  have phis: "\<phi>\<^sub>N\<^sub>S = enc_conj (formula15 (\<lambda>i j. fst (f (xs ! i) (ys ! j))) (\<lambda>i j. snd (f (xs ! i) (ys ! j))) (length xs) (length ys))"
    "\<phi>\<^sub>S = enc_conj (formula16 (\<lambda>i j. fst (f (xs ! i) (ys ! j))) (\<lambda>i j. snd (f (xs ! i) (ys ! j))) (length xs) (length ys))"
    by (auto simp: formula16_def)
  show ?thesis unfolding mul_ext_def Let_def unfolding xs ys prod.inject phis enc_sound
    by (intro conjI; rule formula15 formula16, auto)
qed
end

subsection \<open>Encoding into Propositional Formulas\<close>

global_interpretation pf_encoder: ms_encoder 
  "Disj []" 
  "Conj []" 
  "\<lambda> x. Prop x" 
  "\<lambda> x. Neg (Prop x)" 
  "\<lambda> x y. Equiv (Prop x) (Neg (Prop y))" 
  "\<lambda> x y z. Equiv (Prop x) (Conj [Prop y, Neg (Prop z)])" 
  "\<lambda> x y z u. Equiv (Prop x) (Disj [Conj [Prop y, Prop z], Conj [Neg (Prop y), Prop u]])" 
  "\<lambda> x y z. Disj [Conj [Prop x, Prop y], Conj [Neg (Prop x), Prop z]]" 
  "\<lambda> x f. Impl (Prop x) f" 
  "\<lambda> x y. Impl (Prop x) (Prop y)" 
  "\<lambda> x y. Neg (Conj [Prop x, Prop y])" 
  "\<lambda> xs. Neg (Conj (map Prop xs))" 
  Conj
  eval
  defines 
    pf_encode_sum_0_1_main = pf_encoder.encode_sum_0_1_main and
    pf_encode_exactly_one = pf_encoder.encode_exactly_one and
    pf_encodeGammaCond = pf_encoder.encodeGammaCond and
    pf_formula14 = pf_encoder.formula14 and
    pf_formula15 = pf_encoder.formula15 and
    pf_formula16 = pf_encoder.formula16 and
    pf_encode_mul_ext = pf_encoder.encode_mul_ext
  by (unfold_locales, auto)

text \<open>The soundness theorem of the propositional formula encoder\<close>

thm pf_encoder.encode_mul_ext

subsection \<open>Size of Propositional Formula Encoding is Quadratic\<close>

lemma size_pf_encode_sum_0_1_main: assumes "pf_encode_sum_0_1_main vars = (conds, one, zero)" 
  and "vars \<noteq> []" 
  shows "sum_list (map size_pf conds) = 16 * length vars - 12" 
  using assms
proof (induct vars arbitrary: conds one zero rule: pf_encoder.encode_sum_0_1_main.induct)
  case (1 x zero' one' conds zero one)
  hence "conds = [Equiv (Prop zero) (Neg (Prop x))]" by auto
  thus ?case by simp
next
  case Cons: (2 x zero one r rr conds' zero' one')
  let ?triple = "(x,zero,one)" 
  let ?rest = "r # rr" 
  obtain conds fzero fone where res: "pf_encode_sum_0_1_main ?rest = (conds, fzero, fone)" 
    by (cases "pf_encode_sum_0_1_main ?rest", auto)
  from Cons(2)[unfolded pf_encoder.encode_sum_0_1_main.simps res split Let_def]
  have conds': "conds' = Equiv (Prop zero) (Conj [Prop fzero, Neg (Prop x)]) #
         Equiv (Prop one) (Disj [Conj [Prop x, Prop fzero], Conj [Neg (Prop x), Prop fone]]) # conds" 
    by auto
  have "sum_list (map size_pf conds') = 16 + sum_list (map size_pf conds)"
    unfolding conds' by simp
  with Cons(1)[OF res]
  show ?case by simp
qed auto

lemma size_pf_encode_exactly_one: assumes "pf_encode_exactly_one vars = (one, conds)" 
  shows "size_pf one + sum_list (map size_pf conds) = 1 + (16 * length vars - 21)" 
proof (cases "vars = []")
  case True
  with assms have "size_pf one = 1" "conds = []"  
    by (auto simp add: pf_encoder.encode_exactly_one_def)
  thus ?thesis unfolding True by simp
next
  case False
  then obtain x ze' on' vs where vars: "vars = (x,ze',on') # vs" by (cases vars; auto)
  show ?thesis
  proof (cases vs)
    case Nil
    have "size_pf one = 1" "conds = []" using assms unfolding vars Nil 
      by (auto simp add: pf_encoder.encode_exactly_one_def)
    thus ?thesis unfolding vars Nil by simp
  next
    case (Cons v vs')
    obtain on zero where res: "pf_encode_sum_0_1_main vs = (conds, zero, on)" 
      and one: "one = Disj [Conj [Prop x, Prop zero], Conj [Neg (Prop x), Prop on]]"  
      using assms(1) False Cons unfolding pf_encoder.encode_exactly_one_def vars
      by (cases "pf_encode_sum_0_1_main vs", auto)  
    from size_pf_encode_sum_0_1_main[OF res] 
    have sum: "sum_list (map size_pf conds) = (16 * length vars - 28)" using Cons vars by auto
    have one: "size_pf one = 8" unfolding one by simp
    show ?thesis unfolding one sum vars Cons by simp
  qed
qed

lemma sum_list_concat: "sum_list (concat xs) = sum_list (map sum_list xs)" 
  by (induct xs, auto)


lemma sum_list_triv_cong: assumes "length xs = n" 
  and "\<And> x. x \<in> set xs \<Longrightarrow> f x = c"
shows "sum_list (map f xs) = n * c" 
  by (subst map_cong[OF refl, of _ _ "\<lambda> _ . c"], insert assms, auto simp: sum_list_triv)

lemma size_pf_formula14: "sum_list (map size_pf (pf_formula14 n m)) = m + 3 * n + m * (n * 16 - 21) + n * (m * 16 - 21)"
proof -
  have "sum_list (map size_pf (pf_formula14 n m)) = m * (1 + (16 * n - 21)) + n * (3 + (16 * m - 21))" 
    unfolding pf_encoder.formula14_def Let_def sum_list_append map_append map_concat List.maps_def sum_list_concat map_map o_def     
  proof (intro arg_cong2[of _ _ _ _ "(+)"], goal_cases)
    case 1
    show ?case
      apply (rule sum_list_triv_cong, force)
      subgoal for j
        by (cases "pf_encode_exactly_one (map (\<lambda>i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0..<n])",
            auto simp: size_pf_encode_exactly_one)
      done
  next
    case 2
    show ?case 
      apply (rule sum_list_triv_cong, force)
      subgoal for i
        by (cases "pf_encode_exactly_one (map (\<lambda>j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0..<m])",
            auto simp: size_pf_encode_exactly_one)
      done
  qed
  also have "\<dots> = m + 3 * n + m * (n * 16 - 21) + n * (m * 16 - 21)" 
    by (simp add: algebra_simps)
  finally show ?thesis .
qed


lemma size_pf_encodeGammaCond: "size_pf (pf_encodeGammaCond gam eps ns s) \<le> 4" 
  by (cases ns; cases s, auto)

lemma size_pf_formula15: "sum_list (map size_pf (pf_formula15 cs cns n m)) \<le> m + 3 * n + m * (n * 16 - 21) + n * (m * 16 - 21) + 4 * m * n" 
proof -
  have "sum_list (map size_pf (pf_formula15 cs cns n m)) \<le> sum_list (map size_pf (pf_formula14 n m)) + 4 * m * n" 
    unfolding pf_encoder.formula15_def Let_def
    apply (simp add: size_list_conv_sum_list List.maps_def map_concat o_def length_concat sum_list_triv sum_list_concat algebra_simps)
    apply (rule le_trans, rule sum_list_mono, rule sum_list_mono[of _ _ "\<lambda> _. 4"])
    by (auto simp: size_pf_encodeGammaCond sum_list_triv)
  also have "\<dots> = m + 3 * n + m * (n * 16 - 21) + n * (m * 16 - 21) + 4 * m * n" 
    unfolding size_pf_formula14 by auto
  finally show ?thesis .
qed

lemma size_pf_formula16: "sum_list (map size_pf (pf_formula16 cs cns n m)) \<le> 2 + m + 4 * n + m * (n * 16 - 21) + n * (m * 16 - 21) + 4 * m * n" 
proof -
  have "sum_list (map size_pf (pf_formula16 cs cns n m)) = sum_list (map size_pf (pf_formula15 cs cns n m)) + (n + 2)" 
    unfolding pf_encoder.formula16_def Let_def by (simp add: o_def size_list_conv_sum_list sum_list_triv)
  also have "\<dots> \<le> (m + 3 * n + m * (n * 16 - 21) + n * (m * 16 - 21) + 4 * m * n) + (n + 2)" 
    by (rule add_right_mono[OF size_pf_formula15])
  also have "\<dots> = 2 + m + 4 * n + m * (n * 16 - 21) + n * (m * 16 - 21) + 4 * m * n" by simp
  finally show ?thesis .
qed

lemma size_pf_encode_mul_ext: assumes "pf_encode_mul_ext f xs ys = (\<phi>\<^sub>S, \<phi>\<^sub>N\<^sub>S)" 
  and n: "n = max (length xs) (length ys)" 
  and n0: "n \<noteq> 0" 
shows "size_pf \<phi>\<^sub>S \<le> 36 * n\<^sup>2" 
     "size_pf \<phi>\<^sub>N\<^sub>S \<le> 36 * n\<^sup>2" 
proof -
  from assms[unfolded pf_encoder.encode_mul_ext_def Let_def, simplified]
  have phis: "\<phi>\<^sub>N\<^sub>S = Conj (pf_formula15 (\<lambda>i j. fst (f (xs ! i) (ys ! j))) (\<lambda>i j. snd (f (xs ! i) (ys ! j))) (length xs) (length ys))"
    "\<phi>\<^sub>S = Conj (pf_formula16 (\<lambda>i j. fst (f (xs ! i) (ys ! j))) (\<lambda>i j. snd (f (xs ! i) (ys ! j))) (length xs) (length ys))"
    by (auto simp: pf_encoder.formula16_def)
  have "size_pf \<phi>\<^sub>S \<le> 1 + (2 + n + 4 * n + n * (n * 16 - 21) + n * (n * 16 - 21) + 4 * n * n)" 
    unfolding phis unfolding n size_pf.simps
    by (rule add_left_mono, rule le_trans[OF size_pf_formula16], intro add_mono mult_mono le_refl, auto)
  also have "\<dots> \<le> 36 * n^2 - 24 * n" using n0 by (cases n; auto simp: power2_eq_square algebra_simps)
  finally show "size_pf \<phi>\<^sub>S \<le> 36 * n^2" by simp

  have "size_pf \<phi>\<^sub>N\<^sub>S \<le> 1 + (n + 4 * n + n * (n * 16 - 21) + n * (n * 16 - 21) + 4 * n * n)" 
    unfolding phis unfolding n size_pf.simps
    apply (rule add_left_mono)
    apply (rule le_trans[OF size_pf_formula15])
    by (intro max.mono add_mono mult_mono le_refl, auto)
  also have "\<dots> \<le> 36 * n^2 - 25 * n" using n0 by (cases n; auto simp: power2_eq_square algebra_simps)
  finally show "size_pf \<phi>\<^sub>N\<^sub>S \<le> 36 * n^2" by simp
qed


subsection \<open>Encoding into Conjunctive Normal Form\<close>

global_interpretation cnf_encoder: ms_encoder 
  "[[]]" 
  "[]" 
  "\<lambda> x. [[(x, True)]]" 
  "\<lambda> x. [[(x, False)]]" 
  "\<lambda> x y. [[(x, True), (y, True)], [(x, False), (y, False)]]" 
  "\<lambda> x y z. [[(x,False),(y,True)],[(x,False),(z,False)],[(x,True),(y,False),(z,True)]]"  
  "\<lambda> x y z u. [[(x,True),(y,True),(u,False)],[(x,True),(y,False),(z,False)],[(x,False),(y,False),(z,True)],[(x,False),(y,True),(u,True)]]"
  "\<lambda> x y z. [[(x,True),(z,True)],[(x,False),(y,True)]]"
  "\<lambda> x xs. map (\<lambda> c. (x,False) # c) xs"  
  "\<lambda> x y. [[(x,False), (y, True)]]" 
  "\<lambda> x y. [[(x,False), (y, False)]]" 
  "\<lambda> xs. [map (\<lambda> x. (x, False)) xs]"
  concat
  eval_cnf 
  defines 
    cnf_encode_sum_0_1_main = cnf_encoder.encode_sum_0_1_main and
    cnf_encode_exactly_one = cnf_encoder.encode_exactly_one and
    cnf_encodeGammaCond = cnf_encoder.encodeGammaCond and
    cnf_formula14 = cnf_encoder.formula14 and
    cnf_formula15 = cnf_encoder.formula15 and
    cnf_formula16 = cnf_encoder.formula16 and
    cnf_encode_mul_ext = cnf_encoder.encode_mul_ext
  by unfold_locales (force simp: eval_cnf_alt_def)+

text \<open>The soundness theorem of the CNF-encoder\<close>

thm cnf_encoder.encode_mul_ext


subsection \<open>Size of CNF-Encoding is Quadratic\<close>

lemma size_cnf_encode_sum_0_1_main: assumes "cnf_encode_sum_0_1_main vars = (conds, one, zero)" 
  and "vars \<noteq> []" 
  shows "sum_list (map size_cnf conds) = 26 * length vars - 20" 
  using assms
proof (induct vars arbitrary: conds one zero rule: cnf_encoder.encode_sum_0_1_main.induct)
  case (1 x zero' one' conds zero one)
  hence "conds =  [[[(zero, True), (one, True)], [(zero, False), (one, False)]]]" by auto
  hence "sum_list (map size_cnf conds) = 6" by (simp add: size_cnf_def)
  thus ?case by simp
next
  case Cons: (2 x zero one r rr conds' zero' one')
  let ?triple = "(x,zero,one)" 
  let ?rest = "r # rr" 
  obtain conds fzero fone where res: "cnf_encode_sum_0_1_main ?rest = (conds, fzero, fone)" 
    by (cases "cnf_encode_sum_0_1_main ?rest", auto)
  from Cons(2)[unfolded cnf_encoder.encode_sum_0_1_main.simps res split Let_def]
  have conds': "conds' = [[(zero, False), (fzero, True)], [(zero, False), (x, False)], [(zero, True), (fzero, False), (x, True)]] #
    [[(one, True), (x, True), (fone, False)], [(one, True), (x, False), (fzero, False)], [(one, False), (x, False), (fzero, True)],
    [(one, False), (x, True), (fone, True)]] #
    conds" 
    by auto
  have "sum_list (map size_cnf conds') = 26 + sum_list (map size_cnf conds)"
    unfolding conds' by (simp add: size_cnf_def)
  with Cons(1)[OF res]
  show ?case by simp
qed auto

lemma size_cnf_encode_exactly_one: assumes "cnf_encode_exactly_one vars = (one, conds)" 
  shows "size_cnf one + sum_list (map size_cnf conds) \<le> 2 + (26 * length vars - 42) \<and> length one \<le> 2" 
proof (cases "vars = []")
  case True
  with assms have "size_cnf one = 1" "length one = 1" "conds = []"  
    by (auto simp add: cnf_encoder.encode_exactly_one_def size_cnf_def)
  thus ?thesis unfolding True by simp
next
  case False
  then obtain x ze' on' vs where vars: "vars = (x,ze',on') # vs" by (cases vars; auto)
  show ?thesis
  proof (cases vs)
    case Nil
    have "size_cnf one = 2" "length one = 1" "conds = []" using assms unfolding vars Nil 
      by (auto simp add: cnf_encoder.encode_exactly_one_def size_cnf_def)
    thus ?thesis unfolding vars Nil by simp
  next
    case (Cons v vs')
    obtain on zero where res: "cnf_encode_sum_0_1_main vs = (conds, zero, on)" 
      and one: "one = [[(x, True), (on, True)], [(x, False), (zero, True)]]"  
      using assms(1) False Cons unfolding cnf_encoder.encode_exactly_one_def vars
      by (cases "cnf_encode_sum_0_1_main vs", auto)  
    from size_cnf_encode_sum_0_1_main[OF res] 
    have sum: "sum_list (map size_cnf conds) = 26 * length vars - 46" using Cons vars by auto
    have one: "size_cnf one = 6" "length one = 2" unfolding one by (auto simp add: size_cnf_def)
    show ?thesis unfolding one sum vars Cons by simp
  qed
qed

lemma sum_list_mono_const: assumes "\<And> x. x \<in> set xs \<Longrightarrow> f x \<le> c" 
  and "n = length xs" 
shows "sum_list (map f xs) \<le> n * c" 
  unfolding assms(2) using assms(1) 
  by (induct xs; force)

lemma size_cnf_formula14: "sum_list (map size_cnf (cnf_formula14 n m)) \<le> 2 * m + 4 * n + m * (26 * n - 42) + n * (26 * m - 42)"
proof -
  have "sum_list (map size_cnf (cnf_formula14 n m)) \<le> m * (2 + (26 * n - 42)) + n * (4 + (26 * m - 42))" 
    unfolding cnf_encoder.formula14_def Let_def sum_list_append map_append map_concat List.maps_def sum_list_concat map_map o_def     
  proof ((intro add_mono; intro sum_list_mono_const), goal_cases)
    case (1 j)
    obtain one conds where cnf: "cnf_encode_exactly_one (map (\<lambda>i. (Gamma i j, AuxZeroJI i j, AuxOneJI i j)) [0..<n]) = (one, conds)" (is "?e = _")
      by (cases ?e, auto)
    show ?case unfolding cnf split using size_cnf_encode_exactly_one[OF cnf] by auto
  next
    case (3 i)
    obtain one conds where cnf: "cnf_encode_exactly_one (map (\<lambda>j. (Gamma i j, AuxZeroIJ i j, AuxOneIJ i j)) [0..<m]) = (one, conds)" (is "?e = _")
      by (cases ?e, auto)
    have id: "size_cnf (map ((#) (Epsilon i, False)) one) = size_cnf one + length one" unfolding size_cnf_def by (induct one, auto simp: o_def)
    show ?case unfolding cnf split using size_cnf_encode_exactly_one[OF cnf] by (simp add: id)
  qed auto
  also have "\<dots> = 2 * m + 4 * n + m * (26 * n - 42) + n * (26 * m - 42)" 
    by (simp add: algebra_simps)
  finally show ?thesis .
qed


lemma size_cnf_encodeGammaCond: "size_cnf (cnf_encodeGammaCond gam eps ns s) \<le> 3" 
  by (cases ns; cases s, auto simp: size_cnf_def)

lemma size_cnf_formula15: "sum_list (map size_cnf (cnf_formula15 cs cns n m)) \<le> 2 * m + 4 * n + m * (26 * n - 42) + n * (26 * m - 42) + 3 * n * m" 
proof -
  have "sum_list (map size_cnf (cnf_formula15 cs cns n m)) \<le> sum_list (map size_cnf (cnf_formula14 n m)) + 3 * n * m" 
    unfolding cnf_encoder.formula15_def Let_def
    apply (simp add: size_list_conv_sum_list List.maps_def map_concat o_def length_concat sum_list_triv sum_list_concat algebra_simps)
    apply (rule le_trans, rule sum_list_mono_const[OF _ refl], rule sum_list_mono_const[OF _ refl, of _ _ 3])
    by (auto simp: size_cnf_encodeGammaCond)
  also have "\<dots> \<le> (2 * m + 4 * n + m * (26 * n - 42) + n * (26 * m - 42)) + 3 * n * m" 
    by (rule add_right_mono[OF size_cnf_formula14])
  finally show ?thesis .
qed

lemma size_cnf_formula16: "sum_list (map size_cnf (cnf_formula16 cs cns n m)) \<le> 1 + 2 * m + 5 * n + m * (26 * n - 42) + n * (26 * m - 42) + 3 * n * m" 
proof -
  have "sum_list (map size_cnf (cnf_formula16 cs cns n m)) = sum_list (map size_cnf (cnf_formula15 cs cns n m)) + (n + 1)" 
    unfolding cnf_encoder.formula16_def Let_def by (simp add: o_def size_list_conv_sum_list sum_list_triv size_cnf_def)
  also have "\<dots> \<le> (2 * m + 4 * n + m * (26 * n - 42) + n * (26 * m - 42) + 3 * n * m) + (n + 1)" 
    by (rule add_right_mono[OF size_cnf_formula15])
  also have "\<dots> = 1 + 2 * m + 5 * n + m * (26 * n - 42) + n * (26 * m - 42) + 3 * n * m" by simp
  finally show ?thesis .
qed

lemma size_cnf_concat: "size_cnf (concat xs) = sum_list (map size_cnf xs)" unfolding size_cnf_def
  by (induct xs, auto)

lemma size_cnf_encode_mul_ext: assumes "cnf_encode_mul_ext f xs ys = (\<phi>\<^sub>S, \<phi>\<^sub>N\<^sub>S)" 
  and n: "n = max (length xs) (length ys)" 
  and n0: "n \<noteq> 0" 
shows "size_cnf \<phi>\<^sub>S \<le> 55 * n\<^sup>2" 
     "size_cnf \<phi>\<^sub>N\<^sub>S \<le> 55 * n\<^sup>2" 
proof -
  let ?fns = "cnf_formula15 (\<lambda>i j. fst (f (xs ! i) (ys ! j))) (\<lambda>i j. snd (f (xs ! i) (ys ! j))) (length xs) (length ys)" 
  let ?fs = "cnf_formula16 (\<lambda>i j. fst (f (xs ! i) (ys ! j))) (\<lambda>i j. snd (f (xs ! i) (ys ! j))) (length xs) (length ys)" 
  from assms[unfolded cnf_encoder.encode_mul_ext_def Let_def, simplified]
  have phis: "\<phi>\<^sub>N\<^sub>S = concat ?fns" "\<phi>\<^sub>S = concat ?fs"
    by (auto simp: cnf_encoder.formula16_def)
  have le_s: "sum_list (map size_cnf ?fs) \<le> 1 + 2 * n + 5 * n + n * (26 * n - 42) + n * (26 * n - 42) + 3 * n * n" 
    by (rule le_trans[OF size_cnf_formula16], intro add_mono mult_mono le_refl, insert n, auto)
  have le_ns: "sum_list (map size_cnf ?fns) \<le> 2 * n + 4 * n + n * (26 * n - 42) + n * (26 * n - 42) + 3 * n * n"
    by (rule le_trans[OF size_cnf_formula15], intro add_mono mult_mono le_refl, insert n, auto)
  {
    fix \<phi>
    assume "\<phi> \<in> {\<phi>\<^sub>N\<^sub>S, \<phi>\<^sub>S}" 
    then obtain f where "f \<in> {?fs,?fns}" and phi: "\<phi> = concat f" unfolding phis by auto
    hence "size_cnf \<phi> \<le> 1 + 2 * n + 5 * n + n * (26 * n - 42) + n * (26 * n - 42) + 3 * n * n" 
      unfolding phi size_cnf_concat
      using le_s le_ns by auto
    also have "\<dots> = 1 + n * 7 + n * n * 3 + (n * n * 52 - n * 84)" by (simp add: algebra_simps)
    also have "\<dots> \<le> n * n * 55" using n0 by (cases n; auto)
    also have "\<dots> = 55 * n ^ 2" by (auto simp: power2_eq_square)
    finally have "size_cnf \<phi> \<le> 55 * n\<^sup>2" .
  }
  thus "size_cnf \<phi>\<^sub>N\<^sub>S \<le> 55 * n^2" "size_cnf \<phi>\<^sub>S \<le> 55 * n^2" by auto
qed


subsection \<open>Check Executability\<close>

text \<open>The constant 36 in the size-estimation for the PF-encoder is not that bad in comparison to the actual size,
  since using 34 in the size-estimation would be wrong:\<close>

value (code) "let n = 20 in (36 * n\<^sup>2, size_pf (fst (pf_encode_mul_ext (\<lambda> i j. (True, False)) [0..<n] [0..<n])), 34 * n\<^sup>2)" 

text \<open>Similarly, the constant 55 in the size-estimation for the CNF-encoder is not that bad in comparison to the actual size,
  since using 51 in the size-estimation would be wrong:\<close>

value (code) "let n = 20 in (55 * n\<^sup>2, size_cnf (fst (cnf_encode_mul_ext (\<lambda> i j. (True, False)) [0..<n] [0..<n])), 51 * n\<^sup>2)"


text \<open>Example encoding\<close>

value (code) "fst (pf_encode_mul_ext  (\<lambda> i j. (i > j, i \<ge> j)) [0..<3] [0..<5])" 
value (code) "fst (cnf_encode_mul_ext (\<lambda> i j. (i > j, i \<ge> j)) [0..<3] [0..<5])" 
 
end
