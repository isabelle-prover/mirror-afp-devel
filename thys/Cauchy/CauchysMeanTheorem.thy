(*  Title:       Cauchy's Mean Theorem
    Author:      Benjamin Porter <Benjamin.Porter at gmail.com>, 2006
                 cleaned up a bit by Tobias Nipkow, 2007
    Maintainer:  Benjamin Porter <Benjamin.Porter at gmail.com>
*)

chapter \<open>Cauchy's Mean Theorem\<close>

theory CauchysMeanTheorem
imports Complex_Main
begin

section \<open>Abstract\<close>

text \<open>The following document presents a proof of Cauchy's Mean
theorem formalised in the Isabelle/Isar theorem proving system.

{\em Theorem}: For any collection of positive real numbers the
geometric mean is always less than or equal to the arithmetic mean. In
mathematical terms: $$\sqrt[n]{x_1 x_2 \dots x_n} \leq \frac{x_1 +
\dots + x_n}{n}$$ We will use the term {\em mean} to denote the
arithmetic mean and {\em gmean} to denote the geometric mean.

{\em Informal Proof}:

This proof is based on the proof presented in [1]. First we need an
auxiliary lemma (the proof of which is presented formally below) that
states:

Given two pairs of numbers of equal sum, the pair with the greater
product is the pair with the least difference. Using this lemma we now
present the proof -

Given any collection $C$ of positive numbers with mean $M$ and product
$P$ and with some element not equal to M we can choose two elements
from the collection, $a$ and $b$ where $a>M$ and $b<M$. Remove these
elements from the collection and replace them with two new elements,
$a'$ and $b'$ such that $a' = M$ and $a' + b' = a + b$. This new
collection $C'$ now has a greater product $P'$ but equal mean with
respect to $C$. We can continue in this fashion until we have a
collection $C_n$ such that $P_n > P$ and $M_n = M$, but $C_n$ has all
its elements equal to $M$ and thus $P_n = M^n$. Using the definition
of geometric and arithmetic means above we can see that for any
collection of positive elements $E$ it is always true that gmean E
$\leq$ mean E. QED.


[1] Dorrie, H. "100 Great Problems of Elementary Mathematics." 1965, Dover.
\<close>


section \<open>Formal proof\<close>

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection \<open>Collection sum and product\<close>

text \<open>The finite collections of numbers will be modelled as
lists. We then define sum and product operations over these lists.\<close>

subsubsection \<open>Sum and product definitions\<close>

notation (input) sum_list (\<open>\<Sum>:_\<close> [999] 998)

notation (input) prod_list (\<open>\<Prod>:_\<close> [999] 998)

subsubsection \<open>Properties of sum and product\<close>

text \<open>We now present some useful properties of sum and product over
collections.\<close>

text \<open>These lemmas just state that if all the elements in a
collection $C$ are less (greater than) than some value $m$, then the
sum will less than (greater than) $m*length(C)$.\<close>

lemma sum_list_mono_lt [rule_format]:
  fixes xs::"real list"
  shows "xs \<noteq> [] \<and> (\<forall>x\<in> set xs. x < m)
         \<longrightarrow> ((\<Sum>:xs) < (m*(real (length xs))))"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons y ys)
  {
    assume ant: "y#ys \<noteq> [] \<and> (\<forall>x\<in>set(y#ys). x < m)"
    hence ylm: "y < m" by simp
    have "\<Sum>:(y#ys) < m * real (length (y#ys))"
    proof cases
      assume "ys \<noteq> []"
      moreover with ant have "\<forall>x\<in>set ys. x < m" by simp
      moreover with calculation Cons have "\<Sum>:ys < m*real (length ys)" by simp
      hence "\<Sum>:ys + y < m*real(length ys) + y" by simp
      with ylm have "\<Sum>:(y#ys) < m*(real(length ys) + 1)" by(simp add:field_simps)
      then have "\<Sum>:(y#ys) < m*(real(length ys + 1))"
        by (simp add: algebra_simps)
      hence "\<Sum>:(y#ys) < m*(real (length(y#ys)))" by simp
      thus ?thesis .
    next
      assume "\<not> (ys \<noteq> [])"
      hence "ys = []" by simp
      with ylm show ?thesis by simp
    qed
  }
  thus ?case by simp
qed


lemma sum_list_mono_gt [rule_format]:
  fixes xs::"real list"
  shows "xs \<noteq> [] \<and> (\<forall>x\<in>set xs. x > m)
         \<longrightarrow> ((\<Sum>:xs) > (m*(real (length xs))))"
txt \<open>proof omitted\<close>
(*<*)
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons y ys)
  {
    assume ant: "y#ys \<noteq> [] \<and> (\<forall>x\<in>set(y#ys). x > m)"
    hence ylm: "y > m" by simp
    have "\<Sum>:(y#ys) > m * real (length (y#ys))"
    proof cases
      assume "ys \<noteq> []"
      moreover with ant have "\<forall>x\<in>set ys. x > m" by simp
      moreover with calculation Cons have "\<Sum>:ys > m*real (length ys)" by simp
      hence "\<Sum>:ys + y > m*real(length ys) + y" by simp
      with ylm have "\<Sum>:(y#ys) > m*(real(length ys) + 1)" by(simp add:field_simps)
      then have "\<Sum>:(y#ys) > m*(real(length ys + 1))"
        by (simp add: algebra_simps)
      hence "\<Sum>:(y#ys) > m*(real (length(y#ys)))" by simp
      thus ?thesis .
    next
      assume "\<not> (ys \<noteq> [])"
      hence "ys = []" by simp
      with ylm show ?thesis by simp
    qed
  }
  thus ?case by simp
(*>*)
qed

text \<open>If $a$ is in $C$ then the sum of the collection $D$ where $D$
is $C$ with $a$ removed is the sum of $C$ minus $a$.\<close>

lemma sum_list_rmv1:
  "a \<in> set xs \<Longrightarrow> \<Sum>:(remove1 a xs) = \<Sum>:xs - (a :: 'a :: ab_group_add)"
by (induct xs) auto

text \<open>A handy addition and division distribution law over collection
sums.\<close>

lemma list_sum_distrib_aux:
  shows "(\<Sum>:xs/(n :: 'a :: archimedean_field) + \<Sum>:xs) = (1 + (1/n)) * \<Sum>:xs"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof -
    have
      "\<Sum>:(x#xs)/n = x/n + \<Sum>:xs/n"
      by (simp add: add_divide_distrib)
    also with Cons have
      "\<dots> = x/n + (1+1/n)*\<Sum>:xs - \<Sum>:xs"
      by simp
    finally have
      "\<Sum>:(x#xs) / n + \<Sum>:(x#xs) = x/n + (1+1/n)*\<Sum>:xs - \<Sum>:xs + \<Sum>:(x#xs)"
      by simp
    also have
      "\<dots> = x/n + (1+(1/n)- 1)*\<Sum>:xs + \<Sum>:(x#xs)"
      by (subst mult_1_left [symmetric, of "\<Sum>:xs"]) (simp add: field_simps)
    also have
      "\<dots> = x/n + (1/n)*\<Sum>:xs + \<Sum>:(x#xs)"
      by simp
    also have
      "\<dots> = (1/n)*\<Sum>:(x#xs) + 1*\<Sum>:(x#xs)" by(simp add: divide_simps)
    finally show ?thesis by (simp add: field_simps)
  qed
qed

lemma remove1_retains_prod:
  fixes a and xs::"'a :: comm_ring_1 list"
  shows "a \<in> set xs \<longrightarrow> \<Prod>:xs = \<Prod>:(remove1 a xs) * a"
  (is "?P xs")
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons aa list)
  assume plist: "?P list"
  show "?P (aa#list)"
  proof
    assume aml: "a \<in> set(aa#list)"
    show "\<Prod>:(aa # list) = \<Prod>:remove1 a (aa # list) * a"
    proof (cases)
      assume aeq: "a = aa"
      hence
        "remove1 a (aa#list) = list"
        by simp
      hence
        "\<Prod>:(remove1 a (aa#list)) = \<Prod>:list"
        by simp
      moreover with aeq have
        "\<Prod>:(aa#list) = \<Prod>:list * a"
        by simp
      ultimately show
        "\<Prod>:(aa#list) = \<Prod>:remove1 a (aa # list) * a"
        by simp
    next
      assume naeq: "a \<noteq> aa"
      with aml have aml2: "a \<in> set list" by simp
      from naeq have
        "remove1 a (aa#list) = aa#(remove1 a list)"
        by simp
      moreover hence
        "\<Prod>:(remove1 a (aa#list)) = aa * \<Prod>:(remove1 a list)"
        by simp
      moreover from aml2 plist have
        "\<Prod>:list = \<Prod>:(remove1 a list) * a"
        by simp
      ultimately show
        "\<Prod>:(aa#list) = \<Prod>:remove1 a (aa # list) * a"
        by simp
    qed
  qed
qed

text \<open>The final lemma of this section states that if all elements
are positive and non-zero then the product of these elements is also
positive and non-zero.\<close>

lemma el_gt0_imp_prod_gt0 [rule_format]:
  fixes xs::"'a :: archimedean_field list"
  shows "\<forall>y. y \<in> set xs \<longrightarrow> y > 0 \<Longrightarrow> \<Prod>:xs > 0"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons a xs)
  have exp: "\<Prod>:(a#xs) = \<Prod>:xs * a" by simp
  with Cons have "a > 0" by simp
  with exp Cons show ?case by simp
qed


(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection \<open>Auxiliary lemma\<close>

text \<open>This section presents a proof of the auxiliary lemma required
for this theorem.\<close>

lemma prod_exp:
  fixes x::real
  shows "4*(x*y) = (x+y)^2 - (x-y)^2"
  by (simp add: power2_diff power2_sum)

lemma abs_less_imp_sq_less [rule_format]:
  fixes x::real and y::real and z::real and w::real
  assumes diff: "abs (x-y) < abs (z-w)"
  shows "(x-y)^2 < (z-w)^2"
proof cases
  assume "x=y"
  hence "abs (x-y) = 0" by simp
  moreover with diff have "abs(z-w) > 0" by simp
  hence "(z-w)^2 > 0" by simp
  ultimately show ?thesis by auto
next
  assume "x\<noteq>y"
  hence "abs (x - y) > 0" by simp
  with diff have "(abs (x-y))^2 < (abs (z-w))^2"
    by - (drule power_strict_mono [where a="abs (x-y)" and n=2 and b="abs (z-w)"], auto)
  thus ?thesis by simp
qed

text \<open>The required lemma (phrased slightly differently than in the
informal proof.) Here we show that for any two pairs of numbers with
equal sums the pair with the least difference has the greater
product.\<close>

lemma le_diff_imp_gt_prod [rule_format]:
  fixes x::real and y::real and z::real and w::real
  assumes diff: "abs (x-y) < abs (z-w)" and sum: "x+y = z+w"
  shows "x*y > z*w"
proof -
  from sum have "(x+y)^2 = (z+w)^2" by simp
  moreover from diff have "(x-y)^2 < (z-w)^2" by (rule abs_less_imp_sq_less)
  ultimately have "(x+y)^2 - (x-y)^2 > (z+w)^2 - (z-w)^2" by auto
  thus "x*y > z*w" by (simp only: prod_exp [symmetric])
qed

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection \<open>Mean and GMean\<close>

text \<open>Now we introduce definitions and properties of arithmetic and
geometric means over collections of real numbers.\<close>

subsubsection \<open>Definitions\<close>

text \<open>{\em Arithmetic mean}\<close>

definition
  mean :: "(real list)\<Rightarrow>real" where
  "mean s = (\<Sum>:s / real (length s))"

text \<open>{\em Geometric mean}\<close>

definition
  gmean :: "(real list)\<Rightarrow>real" where
  "gmean s = root (length s) (\<Prod>:s)"


subsubsection \<open>Properties\<close>

text \<open>Here we present some trivial properties of {\em mean} and {\em gmean}.\<close>

lemma list_sum_mean:
  fixes xs::"real list"
  shows "\<Sum>:xs = ((mean xs) * (real (length xs)))"
  by (induct xs) (auto simp: mean_def)

lemma list_mean_eq_iff:
  fixes one::"real list" and two::"real list"
  assumes
    se: "( \<Sum>:one = \<Sum>:two )" and
    le: "(length one = length two)"
  shows "(mean one = mean two)"
proof -
  from se le have
    "(\<Sum>:one / real (length one)) = (\<Sum>:two / real (length two))"
    by auto
  thus ?thesis unfolding mean_def .
qed

lemma list_gmean_gt_iff:
  fixes one::"real list" and two::"real list"
  assumes
    gz1: "\<Prod>:one > 0" and gz2: "\<Prod>:two > 0" and
    ne1: "one \<noteq> []" and ne2: "two \<noteq> []" and
    pe: "(\<Prod>:one > \<Prod>:two)" and
    le: "(length one = length two)"
  shows "(gmean one > gmean two)"
  unfolding gmean_def
  using le ne2 pe by simp

text \<open>This slightly more complicated lemma shows that for every non-empty collection with mean $M$, adding another element $a$ where $a=M$ results in a new list with the same mean $M$.\<close>

lemma list_mean_cons [rule_format]:
  fixes xs::"real list"
  shows "xs \<noteq> [] \<longrightarrow> mean ((mean xs)#xs) = mean xs"
proof
  assume lne: "xs \<noteq> []"
  obtain len where ld: "len = real (length xs)" by simp
  with lne have lgt0: "len > 0" by simp
  hence lnez: "len \<noteq> 0" by simp
  from lgt0 have l1nez: "len + 1 \<noteq> 0" by simp
  from ld have mean: "mean xs = \<Sum>:xs / len" unfolding mean_def by simp
  with ld of_nat_add of_int_1 mean_def
  have "mean ((mean xs)#xs) = (\<Sum>:xs/len + \<Sum>:xs) / (1+len)"
    by simp
  also from list_sum_distrib_aux[of xs] have
    "\<dots> = (1 + (1/len))*\<Sum>:xs / (1+len)" by simp
  also have
    "\<dots> = (len + 1)*\<Sum>:xs / (len * (1+len))"
    by (smt (verit, best) lnez add_divide_distrib divide_divide_eq_left
        nonzero_divide_mult_cancel_left times_divide_eq_left)
  also from l1nez have "\<dots> = \<Sum>:xs / len"
    by (simp add: add.commute)
  finally show "mean ((mean xs)#xs) = mean xs" by (simp add: mean)
qed

text \<open>For a non-empty collection with positive mean, if we add a positive number to the collection then the mean remains positive.\<close>

lemma mean_gt_0:
  assumes "xs \<noteq> []" "0 < x" and mgt0: "0 < mean xs"
  shows "0 < mean (x # xs)"
proof -
  have lxsgt0: "length xs \<noteq> 0"
    using assms by simp
  from mgt0 have xsgt0: "0 < \<Sum>:xs"
    by (simp add: assms list_sum_mean)
  with \<open>x>0\<close> have "\<Sum>:(x#xs) > 0" by simp
  thus ?thesis
    using mean_def by force
qed

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection \<open>\<open>list_neq\<close>, \<open>list_eq\<close>\<close>

text \<open>This section presents a useful formalisation of the act of removing all the elements from a collection that are equal (not equal) to a particular value. We use this to extract all the non-mean elements from a collection as is required by the proof.\<close>

subsubsection \<open>Definitions\<close>

text \<open>\<open>list_neq\<close> and \<open>list_eq\<close> just extract elements from a collection that are not equal (or equal) to some value.\<close>

abbreviation
  list_neq :: "('a list) \<Rightarrow> 'a \<Rightarrow> ('a list)" where
  "list_neq xs el == filter (\<lambda>x. x\<noteq>el) xs"

abbreviation
  list_eq :: "('a list) \<Rightarrow> 'a \<Rightarrow> ('a list)" where
  "list_eq xs el == filter (\<lambda>x. x=el) xs"

subsubsection \<open>Properties\<close>

text \<open>This lemma just proves a required fact about \<open>list_neq\<close>, {\em remove1} and {\em length}.\<close>

lemma list_neq_remove1 [rule_format]:
  shows "a\<noteq>m \<and> a \<in> set xs
  \<longrightarrow> length (list_neq (remove1 a xs) m) < length (list_neq xs m)"
  (is "?A xs \<longrightarrow> ?B xs" is "?P xs")
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  note \<open>?P xs\<close>
  {
    assume a: "?A (x#xs)"
    hence
      a_ne_m: "a\<noteq>m" and
      a_mem_x_xs: "a \<in> set(x#xs)"
      by auto
    have b: "?B (x#xs)"
    proof cases
      assume "xs = []"
      with a_ne_m a_mem_x_xs show ?thesis
        by simp
    next
      assume xs_ne: "xs \<noteq> []"
      with a_ne_m a_mem_x_xs show ?thesis
      proof cases
        assume "a=x" with a_ne_m show ?thesis by simp
      next
        assume a_ne_x: "a\<noteq>x"
        with a_mem_x_xs xs_ne a_ne_m Cons have
          "length (list_neq (remove1 a xs) m) < length (list_neq xs m)"
          by simp
        then show ?thesis
          by (simp add: a_ne_x)
      qed
    qed
  }
  thus "?P (x#xs)" by simp
qed

text \<open>We now prove some facts about \<open>list_eq\<close>, \<open>list_neq\<close>, length, sum and product.\<close>

lemma list_eq_sum [simp]:
  fixes xs::"real list"
  shows "\<Sum>:(list_eq xs m) = (m * (real (length (list_eq xs m))))"
  by (induct xs) (auto simp:field_simps)

lemma list_eq_prod [simp]:
  fixes xs::"real list"
  shows "\<Prod>:(list_eq xs m) = (m ^ (length (list_eq xs m)))"
  by (induct xs) auto

lemma sum_list_split:
  fixes xs::"real list"
  shows "\<Sum>:xs = (\<Sum>:(list_neq xs m) + \<Sum>:(list_eq xs m))"
  by (induct xs) auto

lemma prod_list_split:
  fixes xs::"real list"
  shows "\<Prod>:xs = (\<Prod>:(list_neq xs m) * \<Prod>:(list_eq xs m))"
  by (induct xs) auto

lemma sum_list_length_split:
  fixes xs::"real list"
  shows "length xs = length (list_neq xs m) + length (list_eq xs m)"
  by (induct xs) auto



(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection \<open>Element selection\<close>

text \<open>We now show that given after extracting all the elements not equal to the mean there exists one that is greater then (or less than) the mean.\<close>

lemma pick_one_gt:
  fixes xs::"real list" and m::real
  defines m: "m \<equiv> (mean xs)" and neq: "noteq \<equiv> list_neq xs m"
  assumes asum: "noteq\<noteq>[]"
  shows "\<exists>e. e \<in> set noteq \<and> e > m"
proof (rule ccontr)
  let ?m = "(mean xs)"
  let ?neq = "list_neq xs ?m"
  let ?eq = "list_eq xs ?m"
  from list_eq_sum have "(\<Sum>:?eq) = ?m * (real (length ?eq))" by simp
  from asum have neq_ne: " ?neq \<noteq> []" unfolding m neq .
  assume not_el: "\<not>(\<exists>e. e \<in> set noteq \<and> m < e)"
  hence not_el_exp: "\<not>(\<exists>e. e \<in> set ?neq \<and> ?m < e)" unfolding m neq .
  hence "\<forall>e. \<not>(e \<in> set ?neq) \<or> \<not>(e > ?m)" by simp
  hence "\<forall>e. e \<in> set ?neq \<longrightarrow> \<not>(e > ?m)" by blast
  hence "\<forall>e. e \<in> set ?neq \<longrightarrow> e \<le> ?m" by (simp add: linorder_not_less)
  hence "\<forall>e. e \<in> set ?neq \<longrightarrow> e < ?m" by (simp add:order_le_less)
  with assms sum_list_mono_lt have "(\<Sum>:?neq) < ?m * (real (length ?neq))" by blast
  hence "(\<Sum>:?neq) + (\<Sum>:?eq) < ?m * (real (length ?neq)) + (\<Sum>:?eq)" by simp
  also have "\<dots> = (?m * ((real (length ?neq) + (real (length ?eq)))))"
    by (simp add:field_simps)
  also have "\<dots> = (?m * (real (length xs)))"
    by (metis of_nat_add sum_list_length_split)
  also have "\<dots> = \<Sum>:xs"
    by (simp add: list_sum_mean [symmetric])
  finally show False
    by (metis nless_le sum_list_split)
qed

lemma pick_one_lt:
  fixes xs::"real list" and m::real
  defines m: "m \<equiv> (mean xs)" and neq: "noteq \<equiv> list_neq xs m"
  assumes asum: "noteq\<noteq>[]"
  shows "\<exists>e. e \<in> set noteq \<and> e < m"
proof (rule ccontr) \<comment> \<open>reductio ad absurdum\<close>
  let ?m = "(mean xs)"
  let ?neq = "list_neq xs ?m"
  let ?eq = "list_eq xs ?m"
  from list_eq_sum have "(\<Sum>:?eq) = ?m * (real (length ?eq))" by simp
  from asum have neq_ne: " ?neq \<noteq> []" unfolding m neq .
  assume not_el: "\<not>(\<exists>e. e \<in> set noteq \<and> m > e)"
  hence not_el_exp: "\<not>(\<exists>e. e \<in> set ?neq \<and> ?m > e)" unfolding m neq .
  hence "\<forall>e. \<not>(e \<in> set ?neq) \<or> \<not>(e < ?m)" by simp
  hence "\<forall>e. e \<in> set ?neq \<longrightarrow> \<not>(e < ?m)" by blast
  hence "\<forall>e. e \<in> set ?neq \<longrightarrow> e \<ge> ?m" by (simp add: linorder_not_less)
  hence "\<forall>e. e \<in> set ?neq \<longrightarrow> e > ?m" by (auto simp: order_le_less)
  with assms sum_list_mono_gt have "(\<Sum>:?neq) > ?m * (real (length ?neq))" by blast
  hence
    "(\<Sum>:?neq) + (\<Sum>:?eq) > ?m * (real (length ?neq)) + (\<Sum>:?eq)" by simp
  also have
    "(?m * (real (length ?neq)) + (\<Sum>:?eq)) =
     (?m * (real (length ?neq)) + (?m * (real (length ?eq))))"
    by simp
  also have "\<dots> = (?m * ((real (length ?neq) + (real (length ?eq)))))"
    by (simp add:field_simps)
  also have "\<dots> = (?m * (real (length xs)))"
    by (metis of_nat_add sum_list_length_split)
  also have "\<dots> = \<Sum>:xs"
    by (simp add: list_sum_mean [symmetric])
  finally show False
    by (metis less_irrefl sum_list_split)
qed

(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)

subsection \<open>Abstract properties\<close>

text \<open>In order to maintain some comprehension of the following proofs we now introduce some properties of collections.\<close>

subsubsection \<open>Definitions\<close>


text \<open>{\em het}: The heterogeneity of a collection is the number of elements not equal to its mean. A heterogeneity of zero implies the all the elements in the collection are the same (i.e. homogeneous).\<close>

definition
  het :: "real list \<Rightarrow> nat" where
  "het l = length (list_neq l (mean l))"

lemma het_gt_0_imp_noteq_ne: "het l > 0 \<Longrightarrow> list_neq l (mean l) \<noteq> []"
  unfolding het_def by simp

lemma het_gt_0I: 
  assumes "a \<in> set xs" "b \<in> set xs" "a \<noteq> b"
  shows "het xs > 0"
  unfolding het_def
  by (metis (mono_tags, lifting) assms filter_empty_conv length_greater_0_conv)


text \<open>\<open>\<gamma>-eq\<close>: Two lists are $\gamma$-equivalent if and only
if they both have the same number of elements and the same arithmetic
means.\<close>

definition
  \<gamma>_eq :: "((real list)*(real list)) \<Rightarrow> bool" where
  "\<gamma>_eq a \<longleftrightarrow> mean (fst a) = mean (snd a) \<and> length (fst a) = length (snd a)"

text \<open>\<open>\<gamma>_eq\<close> is transitive and symmetric.\<close>

lemma \<gamma>_eq_sym: "\<gamma>_eq (a,b) = \<gamma>_eq (b,a)"
  unfolding \<gamma>_eq_def by auto

lemma \<gamma>_eq_trans:
  "\<gamma>_eq (x,y) \<Longrightarrow> \<gamma>_eq (y,z) \<Longrightarrow> \<gamma>_eq (x,z)"
  unfolding \<gamma>_eq_def by simp


text \<open>{\em pos}: A list is positive if all its elements are greater than 0.\<close>

definition
  pos :: "real list \<Rightarrow> bool" where
  "pos l \<longleftrightarrow> (if l=[] then False else \<forall>e. e \<in> set l \<longrightarrow> e > 0)"

lemma pos_empty [simp]: "pos [] = False" unfolding pos_def by simp
lemma pos_single [simp]: "pos [x] = (x > 0)" unfolding pos_def by simp
lemma pos_imp_ne: "pos xs \<Longrightarrow> xs\<noteq>[]" unfolding pos_def by auto

lemma pos_cons [simp]:
  "xs \<noteq> [] \<Longrightarrow> pos (x#xs) = (if (x>0) then pos xs else False)"
  by (auto simp: pos_def)

subsubsection \<open>Properties\<close>

text \<open>Here we prove some non-trivial properties of the abstract properties.\<close>

text \<open>Two lemmas regarding {\em pos}. The first states the removing
an element from a positive collection (of more than 1 element) results
in a positive collection. The second asserts that the mean of a
positive collection is positive.\<close>

lemma pos_imp_rmv_pos:
  assumes "(remove1 a xs)\<noteq>[]" "pos xs" shows "pos (remove1 a xs)"
  by (metis assms notin_set_remove1 pos_def)

lemma pos_mean: "pos xs \<Longrightarrow> mean xs > 0"
proof (induct xs)
  case Nil thus ?case by(simp add: pos_def)
next
  case (Cons x xs)
  then show ?case
  proof cases
    assume xse: "xs = []"
    thus ?thesis
      using Cons.prems mean_def by auto
  next
    assume xsne: "xs \<noteq> []"
    show ?thesis
      by (meson Cons.hyps Cons.prems mean_gt_0 pos_cons xsne)
  qed
qed

text \<open>We now show that homogeneity of a non-empty collection $x$
implies that its product is equal to \<open>(mean x)^(length x)\<close>.\<close>

lemma prod_list_het0:
  shows "x\<noteq>[] \<and> het x = 0 \<Longrightarrow> \<Prod>:x = (mean x) ^ (length x)"
proof -
  assume "x\<noteq>[] \<and> het x = 0"
  hence xne: "x\<noteq>[]" and hetx: "het x = 0" by auto
  from hetx have lz: "length (list_neq x (mean x)) = 0" unfolding het_def .
  hence "\<Prod>:(list_neq x (mean x)) = 1" by simp
  with prod_list_split have "\<Prod>:x = \<Prod>:(list_eq x (mean x))"
    by (metis mult_1)
  also have "\<dots> = (mean x) ^ (length (list_eq x (mean x)))" by simp
  finally have "\<Prod>:x = (mean x) ^ (length x)"
    by (metis add_0 lz sum_list_length_split)
  thus ?thesis by simp
qed

text \<open>Furthermore we present an important result - that a
homogeneous collection has equal geometric and arithmetic means.\<close>

lemma het_base:
  assumes "pos x" "het x = 0"
  shows "gmean x = mean x"
proof -
  have "root (length x) (\<Prod>:x) = root (length x) ((mean x)^(length x))"
    by (simp add: assms pos_imp_ne prod_list_het0)
  also have "\<dots> = mean x"
    by (simp add: \<open>pos x\<close> order.order_iff_strict pos_imp_ne pos_mean
        real_root_power_cancel)
  finally show "gmean x = mean x" unfolding gmean_def .
qed

(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)


subsection \<open>Existence of a new collection\<close>

text \<open>We now present the largest and most important proof in this
document. Given any positive and non-homogeneous collection of real
numbers there exists a new collection that is $\gamma$-equivalent,
positive, has a strictly lower heterogeneity and a greater geometric
mean.\<close>

lemma new_list_gt_gmean:
  fixes xs :: "real list" and m :: real
  and neq and eq
  defines
    m: "m \<equiv> mean xs" and
    neq: "noteq \<equiv> list_neq xs m" and
    eq: "eq \<equiv> list_eq xs m"
  assumes pos_xs: "pos xs" and het_gt_0: "het xs > 0"
  shows
  "\<exists>xs'. gmean xs' > gmean xs \<and> \<gamma>_eq (xs',xs) \<and>
          het xs' < het xs \<and> pos xs'"
proof -
  from pos_xs pos_imp_ne have
    pos_els: "\<forall>y. y \<in> set xs \<longrightarrow> y > 0" by (unfold pos_def, simp)
  with el_gt0_imp_prod_gt0[of xs] have pos_asm: "\<Prod>:xs > 0" by simp
  from neq het_gt_0 het_gt_0_imp_noteq_ne m have
    neqne: "noteq \<noteq> []" by simp

  txt \<open>Pick two elements from xs, one greater than m, one less than m.\<close>
  from assms pick_one_gt neqne obtain \<alpha> where
    \<alpha>_def: "\<alpha> \<in> set noteq \<and> \<alpha> > m" unfolding neq m by auto
  from assms pick_one_lt neqne obtain \<beta> where
    \<beta>_def: "\<beta> \<in> set noteq \<and> \<beta> < m" unfolding neq m by auto
  from \<alpha>_def \<beta>_def have \<alpha>_gt: "\<alpha> > m" and \<beta>_lt: "\<beta> < m" by auto
  from \<alpha>_def \<beta>_def have el_neq: "\<beta> \<noteq> \<alpha>" by simp
  from neqne neq have xsne: "xs \<noteq> []" by auto

  from \<beta>_def have \<beta>_mem: "\<beta> \<in> set xs" by (auto simp: neq)
  from \<alpha>_def have \<alpha>_mem: "\<alpha> \<in> set xs" by (auto simp: neq)

  from pos_xs pos_def xsne \<alpha>_mem \<beta>_mem \<alpha>_def \<beta>_def have
    \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0" by auto

  \<comment> \<open>remove these elements from xs, and insert two new elements\<close>
  obtain left_over where lo: "left_over = (remove1 \<beta> (remove1 \<alpha> xs))" by simp
  obtain b where bdef: "m + b = \<alpha> + \<beta>"
    by (drule meta_spec [of _ "\<alpha> + \<beta> - m"], simp)

  from m pos_xs pos_def pos_mean have m_pos: "m > 0" by simp
  with bdef \<alpha>_pos \<beta>_pos \<alpha>_gt \<beta>_lt have b_pos: "b > 0" by simp

  obtain new_list where nl: "new_list = m#b#(left_over)" by auto

  from el_neq \<beta>_mem \<alpha>_mem have "\<beta> \<in> set xs \<and> \<alpha> \<in> set xs \<and> \<beta> \<noteq> \<alpha>" by simp
 have mem : "\<alpha> \<in> set(remove1 \<beta> xs) \<and> \<beta> \<in> set(remove1 \<alpha> xs) \<and> remove1 \<alpha> xs \<noteq> [] \<and> (remove1 \<beta> xs) \<noteq> []"
   by (metis \<alpha>_mem \<beta>_mem el_neq empty_iff in_set_remove1 list.set(1))
  \<comment> \<open>prove that new list is positive\<close>
  from nl have nl_pos: "pos new_list"
    by (metis b_pos lo m_pos mem pos_cons pos_imp_rmv_pos pos_single pos_xs)

  \<comment> \<open>now show that the new list has the same mean as the old list\<close>
  with mem nl lo bdef \<alpha>_mem \<beta>_mem
    have s_eq_s: "\<Sum>:new_list = \<Sum>:xs"
      by (simp add: sum_list_rmv1)
    then have eq_mean: "mean new_list = mean xs"
      by (metis One_nat_def Suc_pred \<alpha>_mem length_Cons length_pos_if_in_set
          length_remove1 list_mean_eq_iff lo mem nl)

  \<comment> \<open>finally show that the new list has a greater gmean than the old list\<close>
  have gt_gmean: "gmean new_list > gmean xs"
  proof -
    have mb_gt_gt: "m*b > \<alpha>*\<beta>"
      using \<alpha>_gt \<beta>_lt bdef le_diff_imp_gt_prod by force
    moreover from nl have
      "\<Prod>:new_list = \<Prod>:left_over * (m*b)" by auto
    moreover
    from lo \<alpha>_mem \<beta>_mem mem remove1_retains_prod[where 'a = real] have
      xsprod: "\<Prod>:xs = \<Prod>:left_over * (\<alpha>*\<beta>)" by auto
    moreover from nl have
      nlne: "new_list \<noteq> []" by simp
    moreover from pos_asm lo have
      "\<Prod>:left_over > 0"
      using \<alpha>_pos \<beta>_pos mult_pos_pos xsprod zero_less_mult_pos2 by auto
    ultimately show "gmean new_list > gmean xs"
      using s_eq_s eq_mean list_gmean_gt_iff list_sum_mean m
        m_pos pos_asm xsne by force
  qed

  \<comment> \<open>auxiliary info\<close>
  from \<beta>_lt have \<beta>_ne_m: "\<beta> \<noteq> m" by simp
  from mem have
    \<beta>_mem_rmv_\<alpha>: "\<beta> \<in> set (remove1 \<alpha> xs)" and rmv_\<alpha>_ne: "(remove1 \<alpha> xs) \<noteq> []" by auto

  from \<alpha>_def have \<alpha>_ne_m: "\<alpha> \<noteq> m" by simp

  \<comment> \<open>now show that new list is more homogeneous\<close>
  have lt_het: "het new_list < het xs"
  proof cases
    assume bm: "b=m"
    with het_def have
      "het new_list = length (list_neq left_over m)"
      using assms(1) eq_mean nl by auto
    also have
      "\<dots> < length (list_neq (remove1 \<alpha> xs) m)"
      by (metis \<beta>_ne_m list_neq_remove1 lo mem)
    also have "\<dots> < length (list_neq xs m)"
      by (metis \<alpha>_mem \<alpha>_ne_m list_neq_remove1)
    also have "\<dots> = het xs"
      using het_def m by presburger
    finally show "het new_list < het xs" .
  next
    assume bnm: "b\<noteq>m"
    with het_def have
      "het new_list = length (b#(list_neq left_over m))"
      using eq_mean m nl by force
    also have "\<dots> = 1 + length (list_neq (remove1 \<beta> (remove1 \<alpha> xs)) m)"
      using lo by auto
    also have "\<dots> < 1 + length (list_neq (remove1 \<alpha> xs) m)"
      by (metis \<beta>_ne_m add_strict_left_mono list_neq_remove1 mem)
    finally have "het new_list \<le> length (list_neq (remove1 \<alpha> xs) m)"
      by simp
    also have "\<dots> < length (list_neq xs m)"
      by (metis \<alpha>_mem \<alpha>_ne_m list_neq_remove1)
    also have "\<dots> = het xs"
      using het_def m by presburger
    finally show ?thesis .
  qed
  then show ?thesis
      \<comment> \<open>thus thesis by existence of newlist\<close>
    using \<gamma>_eq_def eq_mean gt_gmean list_sum_mean nl_pos pos_mean s_eq_s
    by fastforce
qed


text \<open>Furthermore we show that for all non-homogeneous positive
collections there exists another collection that is
$\gamma$-equivalent, positive, has a greater geometric mean {\em and}
is homogeneous.\<close>

lemma existence_of_het0:
  shows "p = het x \<Longrightarrow> p > 0 \<Longrightarrow> pos x \<Longrightarrow>
  (\<exists>y. gmean y > gmean x \<and> \<gamma>_eq (x,y) \<and> het y = 0 \<and> pos y)"
proof (induct p arbitrary: x rule: nat_less_induct)
  case (1 n x)
  then have "het x > 0" and "pos x" by auto
  with new_list_gt_gmean  obtain \<beta> where
    \<beta>_def: "gmean \<beta> > gmean x \<and> \<gamma>_eq (x,\<beta>) \<and> het \<beta> < het x \<and> pos \<beta>" 
    using \<gamma>_eq_sym by blast
  then obtain b where bdef: "b = het \<beta>" by simp
  with 1 \<beta>_def have "b < n" by auto
  then show ?case
    by (smt (verit, best) "1.hyps" \<beta>_def \<gamma>_eq_trans bdef not_gr_zero)
qed


subsection \<open>Cauchy's Mean Theorem\<close>

text \<open>We now present the final proof of the theorem. For any
positive collection we show that its geometric mean is less than or
equal to its arithmetic mean.\<close>

theorem CauchysMeanTheorem:
  fixes z::"real list"
  assumes "pos z"
  shows "gmean z \<le> mean z"
proof -
  from \<open>pos z\<close> have zne: "z\<noteq>[]" by (rule pos_imp_ne)
  show "gmean z \<le> mean z"
  proof cases
    assume "het z = 0"
    with \<open>pos z\<close> zne het_base have "gmean z = mean z" by simp
    thus ?thesis by simp
  next
    assume "het z \<noteq> 0"
    hence "het z > 0" by simp
    moreover obtain k where "k = het z" by simp
    moreover with calculation \<open>pos z\<close> existence_of_het0 have
      "\<exists>y. gmean y > gmean z \<and> \<gamma>_eq (z,y) \<and> het y = 0 \<and> pos y" by auto
    then obtain \<alpha> where
      "gmean \<alpha> > gmean z \<and> \<gamma>_eq (z,\<alpha>) \<and> het \<alpha> = 0 \<and> pos \<alpha>" ..
    with het_base \<gamma>_eq_def pos_imp_ne have
      "mean z = mean \<alpha>" and
      "gmean \<alpha> > gmean z" and
      "gmean \<alpha> = mean \<alpha>" by auto
    hence "gmean z < mean z" by simp
    thus ?thesis by simp
  qed
qed

text \<open>In the equality version we prove that the geometric mean
  is identical to the arithmetic mean iff the collection is 
  homogeneous.\<close>
theorem CauchysMeanTheorem_Eq:
  fixes z::"real list"
  assumes "pos z"
  shows "gmean z = mean z \<longleftrightarrow> het z = 0"
proof 
  assume "het z = 0"
  with het_base[of z] \<open>pos z\<close> show "gmean z = mean z" by auto
next
  assume eq: "gmean z = mean z"
  show "het z = 0"
  proof (rule ccontr)
    assume "het z \<noteq> 0"
    hence "het z > 0" by auto
    moreover obtain k where "k = het z" by simp
    ultimately obtain \<alpha> where
      "gmean \<alpha> > gmean z \<and> \<gamma>_eq (z,\<alpha>) \<and> het \<alpha> = 0 \<and> pos \<alpha>" 
      using assms existence_of_het0 by blast
    with het_base \<gamma>_eq_def pos_imp_ne 
    have "mean z = mean \<alpha>" and "gmean \<alpha> > gmean z" and "gmean \<alpha> = mean \<alpha>" 
      by auto
    hence "gmean z < mean z" by simp
    thus False using eq by auto
  qed
qed
 
corollary CauchysMeanTheorem_Less:
  fixes z::"real list"
  assumes "pos z" and "het z > 0"
  shows "gmean z < mean z"
  by (metis CauchysMeanTheorem CauchysMeanTheorem_Eq assms nless_le)

end
