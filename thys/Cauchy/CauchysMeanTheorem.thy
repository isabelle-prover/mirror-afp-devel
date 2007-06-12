(*  Title:       Cauchy's Mean Theorem
    ID:          $Id: CauchysMeanTheorem.thy,v 1.7 2007-06-12 20:08:58 makarius Exp $
    Author:      Benjamin Porter <Benjamin.Porter at gmail.com>, 2006
    Maintainer:  Benjamin Porter <Benjamin.Porter at gmail.com>
*)

header {* Cauchy's Mean Theorem *}

theory CauchysMeanTheorem
imports Complex_Main
begin

(*<*)
(* These should be in RealDef.thy! *)

lemma real_binminus_uminus_conv:
  fixes a::real
  shows "a - b = a + - b"
by simp

lemma real_mult_ac [simp]: "(a::real) * (b + c) = a * b + a * c"
  apply (subst real_mult_commute)
  apply (subst real_add_mult_distrib)
  apply simp
done

lemma real_le_not_less: "((a::real) \<le> b) = (\<not>(a > b))"
by auto

lemma real_le_eq_or_less: "((a::real) \<le> b) = ((a = b) \<or> (a < b))"
by auto

lemma real_div_order [rule_format]:
  fixes a::real
  assumes agt0: "0 < a" and bgt0: "0 < b"
  shows "0 < a / b"
proof -
  have "a / b = a * inverse b" by (simp only: real_divide_def)
  moreover have "0 < a * inverse b"
  proof -
    from bgt0 have "0 < inverse b" by simp
    with agt0 show "0 < a * inverse b" by (rule real_mult_order)
  qed
  thus ?thesis by (simp only: real_divide_def [symmetric])
qed



(* Should be in List *)
lemma el_exists: "s \<noteq> [] \<Longrightarrow> \<exists>el. el mem s"
  apply (rule contrapos_np [of "s=[]"])
  apply simp
  apply simp
  apply (subst(asm) mem_iff)
  apply simp
done

lemma remove1_imp_not_empty [rule_format]:
  "remove1 a b \<noteq> [] \<longrightarrow> b \<noteq> []"
by auto

lemma mem_implies_len [rule_format]:
  "a mem lst \<longrightarrow> length lst > 0"
by auto

lemma remove1_el_not_nil [rule_format]:
  "(b mem lst \<and> a mem lst \<and> a\<noteq>b) \<longrightarrow> (remove1 a lst) \<noteq> []"
apply clarsimp
apply (case_tac lst)
apply simp
apply (case_tac "a=aa")
by simp+

lemma remove1_exist [rule_format]:
  "(a mem lst \<and> b mem lst \<and> a\<noteq> b) \<longrightarrow> a mem (remove1 b lst)"
apply clarsimp
apply (induct lst)
apply auto
done

lemma remove1_len [rule_format]:
  fixes lst::"'a list" and a::"'a"
  shows "a mem lst \<longrightarrow> length (remove1 a lst) = length lst - 1"
  (is "?P lst")
proof (induct lst)
  case Nil
  show ?case by simp
next
  case (Cons aa lst)
  from this have "?P lst" .
  show ?case
  proof (cases)
    assume "a = aa"
    then have "remove1 a (aa#lst) = lst" by simp
    thus ?case by simp
  next
    assume ana: "a \<noteq> aa"
    from prems have ind: "?P lst" by simp
    {
    assume "a mem (aa#lst)"
    with ana have am: "a mem lst"
      apply (simp only: mem_iff)
      apply simp
      done
    with ana have "remove1 a (aa#lst) = aa#(remove1 a lst)" by simp
    then have "length (remove1 a (aa#lst)) = length (aa#(remove1 a lst))" by simp
    also have "\<dots> = 1 + length(remove1 a lst)" by simp
    also with am ind have "\<dots> = 1 + ((length lst) - 1)" by auto
    also with am ind have "\<dots> = (1 + (length lst)) - 1"
      apply (subst diff_add_assoc)
      apply (drule mem_implies_len)
      apply (drule Suc_leI)
      by auto
    also have "\<dots> = (length (aa#lst)) - 1" by simp
    finally have "length (remove1 a (aa#lst)) = length(aa#lst) - 1" by simp
    }
    thus ?thesis by simp
  qed
qed

lemma remove1_mem:
  "\<forall>x. x mem (remove1 a lst) \<longrightarrow> x mem lst"
proof (induct lst)
  case Nil show ?case by simp
next
  case (Cons y ys)
  {
    fix q
    assume "q mem remove1 a (y#ys)"
    then have ym: "q mem (if (a=y) then ys else y#(remove1 a ys))" by simp
    {
      assume "a=y"
      with ym have "q mem ys" by simp
      then have "q mem (y#ys)" by simp
    }
    moreover
    {
      assume nay: "\<not>(a=y)"
      with ym have "q mem (y#(remove1 a ys))" by simp
      then have "q=y \<or> q mem (remove1 a ys)" by simp
      moreover
      {
        assume "q=y"
        then have "q mem (y#ys)" by simp
      }
      moreover
      {
        assume "q mem (remove1 a ys)"
        with Cons have "q mem ys" by simp
        hence "q mem (y#ys)" by simp
      }
      ultimately
      have "q mem (y#ys)" by auto
    }
    moreover have "a = y \<or> a \<noteq> y" by simp
    ultimately have "q mem (y#ys)" by blast
  }
  thus ?case by blast
qed

(*>*)


section {* Abstract *}

text {* The following document presents a proof of Cauchy's Mean
theorem formalised in the Isabelle/Isar theorem proving system.

{\em Theorem}: For any collection of positive real numbers the
geometric mean is always less than or equal to the arithmetic mean. In
mathematical terms: $$\sqrt[n]{x_1 x_2 \dots x_n} \leq \frac{x_1 +
\dots + x_n}{n}$$ We will use the term {\em mean} to denote the
arithmetic mean and {\em gmean} to denote the geometric mean.

{\em Informal Proof}:

This proof is based on the proof presented in [1]. First we need an
auxillary lemma (the proof of which is presented formally below) that
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
*}


section {* Formal proof *}

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection {* Collection sum and product *}

text {* The finite collections of numbers will be modelled as
lists. We then define sum and product operations over these lists. *}

subsubsection {* Sum and product definitions *}

constdefs
  listsum :: "(real list) \<Rightarrow> real" ("\<Sum>:_")
  "listsum s == foldr op+ s 0"

  listprod :: "(real list) \<Rightarrow> real" ("\<Prod>:_")
  "listprod s == foldr op* s 1"

lemma listsum_empty [simp]: "\<Sum>:[] = 0"
  apply (unfold listsum_def)
  by simp

lemma listsum_cons [simp]: "\<Sum>:(a#b) = a + \<Sum>:b"
proof (unfold listsum_def, induct b)
  case Nil show ?case by simp
next
  case Cons show ?case by simp
qed

lemma listprod_empty [simp]: "\<Prod>:[] = 1"
  apply (unfold listprod_def)
  by simp

lemma listprod_cons [simp]: "\<Prod>:(a#b) = a * \<Prod>:b"
proof (unfold listprod_def, induct b)
  case Nil show ?case by simp
next
  case Cons show ?case by simp
qed

subsubsection {* Properties of sum and product *}

text {* We now present some useful properties of sum and product over
collections. *}

text {* These lemmas just state that if all the elements in a
collection $C$ are less (greater than) than some value $m$, then the
sum will less than (greater than) $m*length(C)$. *}

lemma listsum_mono_lt [rule_format]:
  fixes lst::"real list"
  shows "lst \<noteq> [] \<and> (\<forall>x. (x mem lst \<longrightarrow> x < m))
         \<longrightarrow> ((\<Sum>:lst) < (m*(real (length lst))))"
proof (induct lst)
  case Nil show ?case by simp
next
  case (Cons y ys)
  {
    assume ant: "y#ys \<noteq> [] \<and> (\<forall>x. x mem (y#ys) \<longrightarrow> x < m)"
    then have ylm: "y < m" by simp
    have "\<Sum>:(y#ys) < m * real (length (y#ys))"
    proof cases
      assume "ys \<noteq> []"
      moreover with ant have "\<forall>x. x mem ys \<longrightarrow> x < m" by simp
      moreover with calculation Cons have "\<Sum>:ys < m*real (length ys)" by simp
      then have "\<Sum>:ys + y < m*real(length ys) + y" by simp
      with ylm have "\<Sum>:(y#ys) < m*(real(length ys) + 1)" by simp
      with real_of_nat_Suc have "\<Sum>:(y#ys) < m*(real(length ys + 1))"
        apply -
        apply (drule meta_spec [of _ "length ys"])
        apply (subst(asm) eq_sym_conv)
        by simp
      then have "\<Sum>:(y#ys) < m*(real (length(y#ys)))" by simp
      thus ?thesis .
    next
      assume "\<not> (ys \<noteq> [])"
      then have "ys = []" by simp
      with ylm show ?thesis by simp
    qed
  }
  thus ?case by simp
qed


lemma listsum_mono_gt [rule_format]:
  fixes lst::"real list"
  shows "lst \<noteq> [] \<and> (\<forall>x. (x mem lst \<longrightarrow> x > m))
         \<longrightarrow> ((\<Sum>:lst) > (m*(real (length lst))))"
txt {* proof omitted *}
(*<*)
proof (induct lst)
  case Nil show ?case by simp
next
  case (Cons y ys)
  {
    assume ant: "y#ys \<noteq> [] \<and> (\<forall>x. x mem (y#ys) \<longrightarrow> x > m)"
    then have ylm: "y > m" by simp
    have "\<Sum>:(y#ys) > m * real (length (y#ys))"
    proof cases
      assume "ys \<noteq> []"
      moreover with ant have "\<forall>x. x mem ys \<longrightarrow> x > m" by simp
      moreover with calculation Cons have "\<Sum>:ys > m*real (length ys)" by simp
      then have "\<Sum>:ys + y > m*real(length ys) + y" by simp
      with ylm have "\<Sum>:(y#ys) > m*(real(length ys) + 1)" by simp
      with real_of_nat_Suc have "\<Sum>:(y#ys) > m*(real(length ys + 1))"
        apply -
        apply (drule meta_spec [of _ "length ys"])
        apply (subst(asm) eq_sym_conv)
        by simp
      then have "\<Sum>:(y#ys) > m*(real (length(y#ys)))" by simp
      thus ?thesis .
    next
      assume "\<not> (ys \<noteq> [])"
      then have "ys = []" by simp
      with ylm show ?thesis by simp
    qed
  }
  thus ?case by simp
(*>*)
qed

text {* If $a$ is in $C$ then the sum of the collection $D$ where $D$
is $C$ with $a$ removed is the sum of $C$ minus $a$. *}

lemma listsum_rmv1 [rule_format]:
  fixes lst::"real list"
  shows "\<forall>a. lst \<noteq> [] \<and> a mem lst \<longrightarrow> \<Sum>:(remove1 a lst) = \<Sum>:lst - a"
proof (induct lst)
  case Nil show ?case by simp
next
  case (Cons el lst)
  from Cons
  show ?case
    apply (subst remove1.simps)
    apply clarsimp
    apply (case_tac "lst=[]")
    by simp+
qed

text {* A handy addition and division distribution law over collection
sums. *}

lemma list_sum_distrib_aux:
  shows "(\<Sum>:lst/n + \<Sum>:lst) = (1 + (1/n)) * \<Sum>:lst"
proof (induct lst)
  case Nil show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof -
    have
      "\<Sum>:x#xs/n = x/n + \<Sum>:xs/n"
      by (simp add: add_divide_distrib)
    also with Cons have
      "\<dots> = x/n + (1+1/n)*\<Sum>:xs - \<Sum>:xs"
      by simp
    finally have
      "\<Sum>:x # xs / n + \<Sum>:x # xs = x/n + (1+1/n)*\<Sum>:xs - \<Sum>:xs + \<Sum>:x#xs"
      by simp
    also have
      "\<dots> = x/n + (1+(1/n)- 1)*\<Sum>:xs + \<Sum>:x#xs"
      by (subst real_mult_1 [symmetric, of "\<Sum>:xs"], simp only: ring_eq_simps)
    also have
      "\<dots> = x/n + (1/n)*\<Sum>:xs + \<Sum>:x#xs"
      by simp
    also have
      "\<dots> = (1/n)*\<Sum>:x#xs + 1*\<Sum>:x#xs"
      by simp
    finally show ?thesis by (simp only: ring_eq_simps)
  qed
qed

lemma remove1_retains_prod:
  fixes a::real and lst::"real list"
  shows "a mem lst \<longrightarrow> \<Prod>:lst = \<Prod>:(remove1 a lst) * a"
  (is "?P lst")
proof (induct lst)
  case Nil
  show ?case by simp
next
  case (Cons aa list)
  assume plist: "?P list"
  show "?P (aa#list)"
  proof
    assume aml: "a mem aa#list"
    show "\<Prod>:aa # list = \<Prod>:remove1 a (aa # list) * a"
    proof (cases)
      assume aeq: "a = aa"
      then have
        "remove1 a (aa#list) = list"
        by simp
      then have
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
      with aml have aml2: "a mem list" by simp
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

text {* The final lemma of this section states that if all elements
are positive and non-zero then the product of these elements is also
positive and non-zero. *}

lemma el_gt0_imp_prod_gt0 [rule_format]:
  fixes lst::"real list"
  shows "\<forall>y. y mem lst \<longrightarrow> y > 0 \<Longrightarrow> \<Prod>:lst > 0"
proof (induct lst)
  case Nil show ?case by simp
next
  case (Cons a lst)
  have exp: "\<Prod>:(a#lst) = \<Prod>:lst * a" by simp
  with Cons have "a > 0" by simp
  with exp Cons show ?case by (simp add: mult_pos_pos)
qed


(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection {* Auxillary lemma *}

text {* This section presents a proof of the auxillary lemma required
for this theorem. *}

lemma prod_exp:
  fixes x::real
  shows "4*(x*y) = (x+y)^2 - (x-y)^2"
apply (simp only: real_binminus_uminus_conv)
apply (simp add: real_sum_squared_expand)
done

lemma abs_less_imp_sq_less [rule_format]:
  fixes x::real and y::real and z::real and w::real
  assumes diff: "abs (x-y) < abs (z-w)"
  shows "(x-y)^2 < (z-w)^2"
proof cases
  assume "x=y"
  then have "abs (x-y) = 0" by simp
  moreover with diff have "abs(z-w) > 0" by simp
  hence "(z-w)^2 > 0" by simp
  ultimately show ?thesis by auto
next
  assume "x\<noteq>y"
  then have "abs (x - y) > 0" by simp
  with diff have "(abs (x-y))^2 < (abs (z-w))^2"
    by - (drule power_strict_mono [where a="abs (x-y)" and n=2 and b="abs (z-w)"], auto)
  thus ?thesis by simp
qed

text {* The required lemma (phrased slightly differently than in the
informal proof.) Here we show that for any two pairs of numbers with
equal sums the pair with the least difference has the greater
product. *}

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

subsection {* Mean and GMean *}

text {* Now we introduce definitions and properties of arithmetic and
geometric means over collections of real numbers. *}

subsubsection {* Definitions *}

text {* {\em Arithmetic mean} *}

constdefs
  mean :: "(real list)\<Rightarrow>real"
  "mean s == \<Sum>:s / (real (length s))"

text {* {\em Geometric mean} *}

constdefs
  gmean :: "(real list)\<Rightarrow>real"
  "gmean s == (root (length s) (\<Prod>:s))"


subsubsection {* Properties *}

text {* Here we present some trival properties of {\em mean} and {\em gmean}. *}

lemma list_sum_mean:
  fixes lst::"real list"
  shows "\<Sum>:lst = ((mean lst) * (real (length lst)))"
apply (induct_tac lst)
apply simp
apply clarsimp
apply (unfold mean_def)
apply clarsimp
done

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
  thus ?thesis by (unfold mean_def)
qed

lemma list_gmean_gt_iff:
  fixes one::"real list" and two::"real list"
  assumes
    gz1: "\<Prod>:one > 0" and gz2: "\<Prod>:two > 0" and
    ne1: "one \<noteq> []" and ne2: "two \<noteq> []" and
    pe: "(\<Prod>:one > \<Prod>:two)" and
    le: "(length one = length two)"
  shows "(gmean one > gmean two)"
proof -
  from le obtain len where
    "len = length one \<and> len = length two" by simp
  moreover with ne1 ne2 have "len > 0" by auto
  moreover with gr0_conv_Suc obtain slen where
    "Suc slen = len" by auto
  moreover with pe gz1 gz2 have
    "(root (Suc slen) \<Prod>:one > root (Suc slen) \<Prod>:two)" by auto
  ultimately show ?thesis by (unfold gmean_def, auto)
qed

text {* This slightly more complicated lemma shows that for every non-empty collection with mean $M$, adding another element $a$ where $a=M$ results in a new list with the same mean $M$. *}

lemma list_mean_cons [rule_format]:
  fixes lst::"real list"
  shows "lst \<noteq> [] \<longrightarrow> mean ((mean lst)#lst) = mean lst"
proof
  assume lne: "lst \<noteq> []"
  obtain len where ld: "len = real (length lst)" by simp
  with lne have lgt0: "len > 0" by simp
  then have lnez: "len \<noteq> 0" by simp
  from lgt0 have l1nez: "len + 1 \<noteq> 0" by simp
  from ld have mean: "mean lst = \<Sum>:lst / len" by (unfold mean_def, simp)
  with ld real_of_nat_add real_of_one mean_def have
    "mean ((mean lst)#lst) = (\<Sum>:lst/len + \<Sum>:lst) / (1+len)"
    by simp
  also from list_sum_distrib_aux have
    "\<dots> = (1 + (1/len))*\<Sum>:lst / (1+len)" by simp
  also with lnez have
    "\<dots> = (len + 1)*\<Sum>:lst / (len * (1+len))"
    apply -
    apply (drule mult_divide_cancel_left
      [symmetric, where c="len" and a="(1 + 1 / len) * \<Sum>:lst" and b="1+len"])
    apply clarsimp
    done
  also from l1nez have "\<dots> = \<Sum>:lst / len"
    apply (subst real_mult_commute [where z="len"])
    apply (drule mult_divide_cancel_left
      [where c="len+1" and a="\<Sum>:lst" and b="len"])
    by (simp add: mult_ac add_ac)
  finally show "mean ((mean lst)#lst) = mean lst" by (simp add: mean)
qed

text {* For a non-empty collection with positive mean, if we add a positive number to the collection then the mean remains positive. *}

lemma mean_gt_0 [rule_format]:
  "xs\<noteq>[] \<and> 0 < x \<and> 0 < (mean xs) \<longrightarrow> 0 < (mean (x#xs))"
proof
  assume a: "xs \<noteq> [] \<and> 0 < x \<and> 0 < mean xs"
  then have xgt0: "0 < x" and mgt0: "0 < mean xs" by auto
  from a gr0_conv_Suc obtain len where len_def:
    "Suc len = length xs" by (simp only: length_greater_0_conv[symmetric], auto)
  from a have lxsgt0: "length xs \<noteq> 0" by simp
  from mgt0 have xsgt0: "0 < \<Sum>:xs"
  proof -
    have "mean xs = \<Sum>:xs / real (length xs)" by (unfold mean_def, simp)
    then have "\<Sum>:xs = mean xs * real (length xs)" by simp
    moreover from lxsgt0 have "real (length xs) > 0" by simp
    moreover with calculation lxsgt0 mgt0 real_mult_order show ?thesis by auto
  qed
  with xgt0 have "\<Sum>:(x#xs) > 0" by simp
  then show "0 < (mean (x#xs))"
  proof -
    assume "0 < \<Sum>:(x#xs)"
    moreover have "real (length (x#xs)) > 0" by simp
    ultimately show ?thesis by (unfold mean_def, rule real_div_order)
  qed
qed

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection {* @{text "list_neq"}, @{text "list_eq"} *}

text {* This section presents a useful formalisation of the act of removing all the elements from a collection that are equal (not equal) to a particular value. We use this to extract all the non-mean elements from a collection as is required by the proof. *}

subsubsection {* Definitions *}

text {* @{text "list_neq"} and @{text "list_eq"} just extract elements from a collection that are not equal (or equal) to some value. *}

constdefs
  list_neq :: "('a list) \<Rightarrow> 'a \<Rightarrow> ('a list)"
  "list_neq lst el == (List.filter (\<lambda>x. x\<noteq>el) lst)"

  list_eq :: "('a list) \<Rightarrow> 'a \<Rightarrow> ('a list)"
  "list_eq lst el == (List.filter (\<lambda>x. x=el) lst)"

text {* Trivial properties of @{text "list_neq"}. *}

lemma list_neq_empty[simp]: "list_neq [] m = []"
  apply (unfold list_neq_def)
  by simp

lemma list_neq_cons [simp]:
  "list_neq (a#b) m =
  (if a=m then list_neq b m else a#(list_neq b m))"
  apply (unfold list_neq_def)
  by simp

lemma list_neq_el [rule_format]:
  "\<forall>lst. (e::real) mem (list_neq lst a) \<longrightarrow> e \<noteq> a"
  apply (unfold list_neq_def)
  apply clarsimp
  apply (simp add: mem_iff)
done

lemma list_neq_el_orig [rule_format]:
  "\<forall>lst. (e::real) mem (list_neq lst a) \<longrightarrow> e mem lst"
  apply (unfold list_neq_def)
  apply clarsimp
  apply (simp add: mem_iff)
done

text {* Trivial properties of @{text "list_eq"}. *}

lemma list_eq_empty[simp]: "list_eq [] m = []"
  apply (unfold list_eq_def)
  by simp

lemma list_eq_cons[simp]:
  "list_eq (a#b) m =
  (if a=m then a#(list_eq b m) else list_eq b m)"
  apply (unfold list_eq_def)
  by simp

lemma list_eq_or_neq [rule_format]:
  "\<forall>m. e mem lst \<longrightarrow> (e mem (list_neq lst m)) =
  (\<not>(e mem (list_eq lst m)))"
  apply clarsimp
  apply (unfold list_eq_def list_neq_def)
  apply (simp add: mem_iff)
done

lemma list_eq_el_orig [rule_format]:
  "\<forall>lst. (e::real) mem (list_eq lst a) \<longrightarrow> e mem lst"
  apply (unfold list_eq_def)
  apply (simp add: mem_iff)
  apply clarsimp
done

subsubsection {* Properties *}

text {* This lemma just proves a required fact about @{text "list_neq"}, {\em remove1} and {\em length}. *}

lemma list_neq_remove1 [rule_format]:
  shows "a\<noteq>m \<and> lst\<noteq>[] \<and> a mem lst
  \<longrightarrow> length (list_neq (remove1 a lst) m) < length (list_neq lst m)"
  (is "?A lst \<longrightarrow> ?B lst" is "?P lst")
proof (induct lst)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have "?P xs" .
  {
    assume a: "?A (x#xs)"
    then have
      a_ne_m: "a\<noteq>m" and
      x_xs_ne: "x#xs \<noteq> []" and
      a_mem_x_xs: "a mem x#xs"
      by auto
    have b: "?B (x#xs)"
    proof cases
      assume "xs = []"
      with a_ne_m a_mem_x_xs show ?thesis
        apply (cases "x=a")
        by auto
    next
      assume xs_ne: "xs \<noteq> []"
      with a_ne_m a_mem_x_xs show ?thesis
      proof cases
        assume "a=x" with a_ne_m show ?thesis by simp
      next
        assume a_ne_x: "a\<noteq>x"
        with a_mem_x_xs have a_mem_xs: "a mem xs" by simp
        with xs_ne a_ne_m Cons x_xs_ne have
          rel: "length (list_neq (remove1 a xs) m) < length (list_neq xs m)"
          by simp
        show ?thesis
        proof cases
          assume x_e_m: "x=m"
          with Cons xs_ne a_ne_m a_mem_xs show ?thesis by simp
        next
          assume x_ne_m: "x\<noteq>m"
          from a_ne_x have
            "remove1 a (x#xs) = x#(remove1 a xs)"
            by simp
          then have
            "length (list_neq (remove1 a (x#xs)) m) =
             length (list_neq (x#(remove1 a xs)) m)"
            by simp
          also with x_ne_m have
            "\<dots> = 1 + length (list_neq (remove1 a xs) m)"
            by simp
          finally have
            "length (list_neq (remove1 a (x#xs)) m) =
             1 + length (list_neq (remove1 a xs) m)"
            by simp
          moreover with x_ne_m a_ne_x have
            "length (list_neq (x#xs) m) =
             1 + length (list_neq xs m)"
            by simp
          moreover with rel show ?thesis by simp
        qed
      qed
    qed
  }
  then show "?P (x#xs)" by simp
qed

text {* We now prove some facts about @{text "list_eq"}, @{text "list_neq"}, length, sum and product. *}

lemma list_eq_sum [simp]:
  fixes lst::"real list"
  shows "\<Sum>:(list_eq lst m) = (m * (real (length (list_eq lst m))))"
apply (induct_tac lst)
apply simp
apply clarsimp
apply (subst real_of_nat_Suc)
apply (subst add_commute)
apply (subst real_mult_ac)
by simp

lemma list_eq_prod [simp]:
  fixes lst::"real list"
  shows "\<Prod>:(list_eq lst m) = (m ^ (length (list_eq lst m)))"
apply (induct_tac lst)
apply simp
apply clarsimp
done

lemma listsum_split:
  fixes lst::"real list"
  shows "\<Sum>:lst = (\<Sum>:(list_neq lst m) + \<Sum>:(list_eq lst m))"
apply (induct lst)
apply simp
apply clarsimp
done

lemma listprod_split:
  fixes lst::"real list"
  shows "\<Prod>:lst = (\<Prod>:(list_neq lst m) * \<Prod>:(list_eq lst m))"
apply (induct lst)
apply simp
apply clarsimp
done

lemma listsum_length_split:
  fixes lst::"real list"
  shows "length lst = length (list_neq lst m) + length (list_eq lst m)"
apply (induct lst)
apply simp+
done



(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

subsection {* Element selection *}

text {* We now show that given after extracting all the elements not equal to the mean there exists one that is greater then (or less than) the mean. *}

lemma pick_one_gt [rule_format]:
  fixes lst::"real list" and m::real
  defines m: "m \<equiv> (mean lst)" and neq: "noteq \<equiv> list_neq lst m" and eq: "eq \<equiv> list_eq lst m"
  assumes asum: "noteq\<noteq>[]"
  shows "\<exists>e. e mem noteq \<and> e > m"
proof (rule ccontr)
  let ?m = "(mean lst)"
  let ?neq = "list_neq lst ?m"
  let ?eq = "list_eq lst ?m"
  from list_eq_sum have "(\<Sum>:?eq) = ?m * (real (length ?eq))" by simp
  from asum have neq_ne: " ?neq \<noteq> []" by (unfold m neq)
  assume not_el: "\<not>(\<exists>e. e mem noteq \<and> m < e)"
  then have not_el_exp: "\<not>(\<exists>e. e mem ?neq \<and> ?m < e)" by (unfold m neq)
  then have "\<forall>e. \<not>(e mem ?neq) \<or> \<not>(e > ?m)" by simp
  then have "\<forall>e. e mem ?neq \<longrightarrow> \<not>(e > ?m)" by simp
  then have "\<forall>e. e mem ?neq \<longrightarrow> e \<le> ?m" by (simp add: real_le_not_less[symmetric])
  with list_neq_el real_le_eq_or_less have "\<forall>e. e mem ?neq \<longrightarrow> e < ?m" by simp
  with prems listsum_mono_lt have "(\<Sum>:?neq) < ?m * (real (length ?neq))" by blast
  then have
    "(\<Sum>:?neq) + (\<Sum>:?eq) < ?m * (real (length ?neq)) + (\<Sum>:?eq)" by simp
  also have
    "\<dots> = (?m * (real (length ?neq)) + (?m * (real (length ?eq))))" by simp
  also have
    "\<dots> = (?m * ((real (length ?neq) + (real (length ?eq)))))"
      by (simp add: real_mult_ac)
  also have
    "\<dots> = (?m * (real (length lst)))"
      apply (subst real_of_nat_add [symmetric])
      by (simp add: listsum_length_split [symmetric])
  also have
    "\<dots> = \<Sum>:lst"
      by (simp add: list_sum_mean [symmetric])
  also from not_el calculation show False by (simp only: listsum_split [symmetric])
qed

lemma pick_one_lt [rule_format]:
  fixes lst::"real list" and m::real
  defines m: "m \<equiv> (mean lst)" and neq: "noteq \<equiv> list_neq lst m" and eq: "eq \<equiv> list_eq lst m"
  assumes asum: "noteq\<noteq>[]"
  shows "\<exists>e. e mem noteq \<and> e < m"
proof (rule ccontr) -- "reductio ad absurdum"
  let ?m = "(mean lst)"
  let ?neq = "list_neq lst ?m"
  let ?eq = "list_eq lst ?m"
  from list_eq_sum have "(\<Sum>:?eq) = ?m * (real (length ?eq))" by simp
  from asum have neq_ne: " ?neq \<noteq> []" by (unfold m neq)
  assume not_el: "\<not>(\<exists>e. e mem noteq \<and> m > e)"
  then have not_el_exp: "\<not>(\<exists>e. e mem ?neq \<and> ?m > e)" by (unfold m neq)
  then have "\<forall>e. \<not>(e mem ?neq) \<or> \<not>(e < ?m)" by simp
  then have "\<forall>e. e mem ?neq \<longrightarrow> \<not>(e < ?m)" by simp
  then have "\<forall>e. e mem ?neq \<longrightarrow> e \<ge> ?m" by (simp add: real_le_not_less[symmetric])
  with list_neq_el real_le_eq_or_less have "\<forall>e. e mem ?neq \<longrightarrow> e > ?m"
    apply clarsimp
    apply (drule meta_spec)+
    by auto
  with prems listsum_mono_gt have "(\<Sum>:?neq) > ?m * (real (length ?neq))" by blast
  then have
    "(\<Sum>:?neq) + (\<Sum>:?eq) > ?m * (real (length ?neq)) + (\<Sum>:?eq)" by simp
  also have
    "(?m * (real (length ?neq)) + (\<Sum>:?eq)) =
     (?m * (real (length ?neq)) + (?m * (real (length ?eq))))"
    by simp
  also have
    "\<dots> = (?m * ((real (length ?neq) + (real (length ?eq)))))"
      by (simp add: real_mult_ac)
  also have
    "\<dots> = (?m * (real (length lst)))"
      apply (subst real_of_nat_add [symmetric])
      by (simp add: listsum_length_split [symmetric])
  also have
    "\<dots> = \<Sum>:lst"
      by (simp add: list_sum_mean [symmetric])
  also from not_el calculation show False by (simp only: listsum_split [symmetric])
qed

(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)

subsection {* Abstract properties *}

text {* In order to maintain some comprehension of the following proofs we now introduce some properties of collections. *}

subsubsection {* Definitions *}




text {* {\em het}: The heterogeneity of a collection is the number of elements not equal to its mean. A heterogeneity of zero implies the all the elements in the collection are the same (i.e. homogeneous). *}

constdefs
  het :: "real list \<Rightarrow> nat"
  "het l \<equiv> length (list_neq l (mean l))"

lemma het_gt_0_imp_noteq_ne: "het l > 0 \<Longrightarrow> list_neq l (mean l) \<noteq> []"
  apply (unfold het_def)
  by simp

text {* @{text "\<gamma>-eq"}: Two lists are $\gamma$-equivalent if and only if they both have the same number of elements and the same arithmetic means. *}

constdefs
  \<gamma>_eq :: "((real list)*(real list)) \<Rightarrow> bool"
  "\<gamma>_eq a \<equiv> (mean (fst a) = mean (snd a) \<and> length (fst a) = length (snd a))"

text {* @{text "\<gamma>_eq"} is transitive and symmetric. *}

lemma \<gamma>_eq_sym: "\<gamma>_eq (a,b) = \<gamma>_eq (b,a)"
  apply (unfold \<gamma>_eq_def)
  by auto

lemma \<gamma>_eq_trans:
  assumes "\<gamma>_eq (x,y)" "\<gamma>_eq (y,z)"
  shows "\<gamma>_eq (x,z)"
proof -
  have "\<gamma>_eq (x,y) \<and> \<gamma>_eq (y,z)" ..
  then show "\<gamma>_eq (x,z)"
    apply (unfold \<gamma>_eq_def)
    by auto
qed



text {* {\em pos}: A list is positive if all its elements are greater than 0. *}
constdefs
  pos :: "real list \<Rightarrow> bool"
  "pos l \<equiv> if l=[] then False else \<forall>e. e mem l \<longrightarrow> e > 0"

lemma pos_empty [simp]: "pos [] = False" by (unfold pos_def, simp)
lemma pos_single [simp]: "pos [x] = (x > 0)" by (unfold pos_def, simp)
lemma pos_imp_ne [rule_format]: "pos lst \<longrightarrow> lst\<noteq>[]" by (unfold pos_def, simp)

lemma pos_cons [simp]:
  "xs \<noteq> [] \<longrightarrow> pos (x#xs) =
   (if (x>0) then pos xs else False)"
  (is "?P x xs" is "?A xs \<longrightarrow> ?S x xs")
proof (simp add: split_if, rule impI)
  assume xsne: "xs \<noteq> []"
  then have pxs_simp:
    "pos xs = (\<forall>e. e mem xs \<longrightarrow> e > 0)"
    by (unfold pos_def, simp)
  show
    "(0 < x \<longrightarrow> pos (x # xs) = pos xs) \<and>
     (\<not> 0 < x \<longrightarrow> \<not> pos (x # xs))"
  proof
    {
      assume xgt0: "0 < x"
      {
        assume pxs: "pos xs"
        with pxs_simp have "\<forall>e. e mem xs \<longrightarrow> e > 0" by simp
        then have "\<forall>e. e mem (x#xs) \<longrightarrow> e > 0" by simp
        hence "pos (x#xs)" by (unfold pos_def, simp)
      }
      moreover
      {
        assume pxxs: "pos (x#xs)"
        then have "\<forall>e. e mem (x#xs) \<longrightarrow> e > 0" by (unfold pos_def, simp)
        hence "\<forall>e. e mem xs \<longrightarrow> e > 0" by simp
        hence "pos xs" by (unfold pos_def, simp)
      }
      ultimately have "pos (x # xs) = pos xs"
        apply -
        apply (rule iffI)
        by auto
    }
    thus "0 < x \<longrightarrow> pos (x # xs) = pos xs" by simp
  next
    {
      assume xngt0: "\<not> (0<x)"
      {
        assume pxs: "pos xs"
        with pxs_simp have "\<forall>e. e mem xs \<longrightarrow> e > 0" by simp
        with xngt0 have "\<not> (\<forall>e. e mem (x#xs) \<longrightarrow> e > 0)" by auto
        hence "\<not> (pos (x#xs))" by (unfold pos_def, simp)
      }
      moreover
      {
        assume pxxs: "\<not>pos xs"
        with xsne have "\<not> (\<forall>e. e mem xs \<longrightarrow> e > 0)" by (unfold pos_def, simp)
        hence "\<not> (\<forall>e. e mem (x#xs) \<longrightarrow> e > 0)" by auto
        hence "\<not> (pos (x#xs))" by (unfold pos_def, simp)
      }
      ultimately have "\<not> pos (x#xs)" by auto
    }
    thus "\<not> 0 < x \<longrightarrow> \<not> pos (x # xs)" by simp
  qed
qed

subsubsection {* Properties *}

text {* Here we prove some non-trivial properties of the abstract properties. *}

text {* Two lemmas regarding {\em pos}. The first states the removing
an element from a positive collection (of more than 1 element) results
in a positive collection. The second asserts that the mean of a
positive collection is positive. *}

lemma pos_imp_rmv_pos [rule_format]:
  shows "(remove1 a lst)\<noteq>[] \<and> pos lst \<longrightarrow> pos (remove1 a lst)"
proof
  assume "(remove1 a lst)\<noteq>[] \<and> pos lst"
  then have pl: "pos lst" and rmvne: "(remove1 a lst)\<noteq>[]" by auto
  from pl have "lst \<noteq> []" by (rule pos_imp_ne)
  with pl pos_def have posdef: "\<forall>x. x mem lst \<longrightarrow> x > 0" by simp
  have "\<forall>x. x mem (remove1 a lst) \<longrightarrow> x > 0"
  proof
    fix z
    from remove1_mem have "z mem (remove1 a lst) \<longrightarrow> z mem lst"
      apply -
      apply (drule meta_spec [of _ a])
      apply (drule meta_spec [of _ lst])
      apply simp
      done
    -- "ReportNote: The above should be simpler"
    with posdef show "z mem (remove1 a lst) \<longrightarrow> z > 0" by simp
  qed
  with rmvne show "pos (remove1 a lst)" by (unfold pos_def, simp)
qed

lemma pos_mean [rule_format]:
  shows "pos lst \<longrightarrow> mean lst > 0"
proof (induct lst)
  case Nil show ?case
    apply (unfold pos_def)
    apply simp
    done
next
  case (Cons x xs)
  then have "pos xs \<longrightarrow> 0 < mean xs" ..
  then show "pos (x#xs) \<longrightarrow> 0 < mean (x#xs)"
  proof cases
    assume xse: "xs = []"
    then have pxxs: "pos (x#xs) = (x > 0)" by simp
    {
      assume "pos (x#xs)"
      with pxxs have "x>0" ..
      with xse have "0 < mean (x#xs)" by (unfold mean_def, auto)
    }
    thus ?thesis by simp
  next
    assume xsne: "xs \<noteq> []"
    show ?thesis
    proof cases
      assume pxs: "pos xs"
      with Cons have z_le_mxs: "0 < mean xs" ..
      {
        assume ass: "x > 0"
        with ass z_le_mxs xsne have "0 < mean (x#xs)"
          apply -
          apply (rule mean_gt_0)
          by simp
      }
      moreover
      {
        assume pxxs: "pos (x#xs)"
        with xsne pxs have "0 < x"
        proof cases
          assume "0 < x"
          then show ?thesis by simp
        next
          assume "\<not>(0 < x)"
          with xsne pos_cons have "pos (x#xs) = False" by simp
          with pxxs show ?thesis by simp
        qed
      }
      ultimately have "pos (x#xs) \<Longrightarrow> 0 < mean (x#xs)" by simp
      then show ?thesis by simp
    next
      assume npxs: "\<not>pos xs"
      with xsne pos_cons have "pos (x#xs) = False"  by simp
      thus ?thesis by simp
    qed
  qed
qed

text {* We now show that homogeneity of a non-empty collection $x$
implies that its product is equal to @{text "(mean x)^(length x)"}. *}

lemma listprod_het0:
  shows "x\<noteq>[] \<and> het x = 0 \<Longrightarrow> \<Prod>:x = (mean x) ^ (length x)"
proof -
  assume "x\<noteq>[] \<and> het x = 0"
  then have xne: "x\<noteq>[]" and hetx: "het x = 0" by auto
  from hetx have lz: "length (list_neq x (mean x)) = 0" by (unfold het_def)
  hence "\<Prod>:(list_neq x (mean x)) = 1" by simp
  with listprod_split have "\<Prod>:x = \<Prod>:(list_eq x (mean x))"
    apply -
    apply (drule meta_spec [of _ x])
    apply (drule meta_spec [of _ "mean x"])
    by simp
  also with list_eq_prod have
    "\<dots> = (mean x) ^ (length (list_eq x (mean x)))" by simp
  also with calculation lz listsum_length_split have
    "\<Prod>:x = (mean x) ^ (length x)"
    apply -
    apply (drule meta_spec [of _ x])
    apply (drule meta_spec [of _ "mean x"])
    by simp
  thus ?thesis by simp
qed

text {* Furthermore we present an important result - that a
homogeneous collection has equal geometric and arithmetic means. *}

lemma het_base:
  shows "pos x \<and> x\<noteq>[] \<and> het x = 0 \<Longrightarrow> gmean x = mean x"
proof -
  assume ass: "pos x \<and> x\<noteq>[] \<and> het x = 0"
  then have
    xne: "x\<noteq>[]" and
    hetx: "het x = 0" and
    posx: "pos x"
    by auto
  from posx pos_mean have mxgt0: "mean x > 0" by simp
  from xne have "length x > 0" by simp
  with gr0_conv_Suc obtain len where len_def: "Suc len = length x" by auto
  with ass listprod_het0 have
    "root (length x) \<Prod>:x = root (Suc len) ((mean x)^(Suc len))"
    by simp
  also with mxgt0 real_root_pos have "\<dots> = mean x" by auto
  finally show "gmean x = mean x" by (unfold gmean_def)
qed

(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)


subsection {* Existence of a new collection *}

text {* We now present the largest and most important proof in this
document. Given any positive and non-homogeneous collection of real
numbers there exists a new collection that is $\gamma$-equivalent,
positive, has a strictly lower heterogeneity and a greater geometric
mean. *}

lemma new_list_gt_gmean [rule_format]:
  fixes lst::"real list" and m::real
  defines
    m: "m \<equiv> (mean lst)" and
    neq: "noteq \<equiv> list_neq lst m" and
    eq: "eq \<equiv> list_eq lst m"
  assumes pos_lst: "pos lst" and het_gt_0: "het lst > 0"
  shows
  "\<exists>lst'. gmean lst' > gmean lst \<and> \<gamma>_eq (lst',lst) \<and>
          het lst' < het lst \<and> pos lst'"
proof -
  from pos_lst pos_imp_ne have
    pos_els: "\<forall>y. y mem lst \<longrightarrow> y > 0" by (unfold pos_def, simp)
  with el_gt0_imp_prod_gt0 have pos_asm: "\<Prod>:lst > 0" by simp
  from neq het_gt_0 het_gt_0_imp_noteq_ne m have
    neqne: "noteq \<noteq> []" by simp

  txt {* Pick two elements from lst, one greater than m, one less than m. *}
  from prems pick_one_gt neqne obtain \<alpha> where
    \<alpha>_def: "\<alpha> mem noteq \<and> \<alpha> > m" by (unfold neq m) auto
  from prems pick_one_lt neqne obtain \<beta> where
    \<beta>_def: "\<beta> mem noteq \<and> \<beta> < m" by (unfold neq m) auto
  from \<alpha>_def \<beta>_def have \<alpha>_gt: "\<alpha> > m" and \<beta>_lt: "\<beta> < m" by auto
  from prems have el_neq: "\<beta> \<noteq> \<alpha>" by simp
  from neqne neq have lstne: "lst \<noteq> []" by auto

  from prems list_neq_el_orig have \<beta>mem: "\<beta> mem lst"
    apply (unfold neq)
    apply (drule meta_spec)+
    apply (drule meta_mp)
    by clarsimp+
  from prems list_neq_el_orig have \<alpha>mem: "\<alpha> mem lst"
    apply (unfold neq)
    apply (drule meta_spec)+
    apply (drule meta_mp)
    by clarsimp+

  from pos_lst pos_def lstne \<alpha>mem \<beta>mem \<alpha>_def \<beta>_def have
    \<alpha>_pos: "\<alpha> > 0" and \<beta>_pos: "\<beta> > 0" by auto

  -- "remove these elements from lst, and insert two new elements"
  obtain left_over where lo: "left_over = (remove1 \<beta> (remove1 \<alpha> lst))" by simp
  obtain b where bdef: "m + b = \<alpha> + \<beta>"
    by (drule meta_spec [of _ "\<alpha> + \<beta> - m"], simp)

  from m pos_lst pos_def pos_mean have m_pos: "m > 0" by simp
  with bdef \<alpha>_pos \<beta>_pos \<alpha>_gt \<beta>_lt have b_pos: "b > 0" by simp

  obtain new_list where nl: "new_list = m#b#(left_over)" by auto

  from el_neq \<beta>mem \<alpha>mem have "\<beta> mem lst \<and> \<alpha> mem lst \<and> \<beta> \<noteq> \<alpha>" by simp
  then have "\<alpha> mem remove1 \<beta> lst \<and> \<beta> mem remove1 \<alpha> lst " by (auto simp add: remove1_exist)
  moreover then have "(remove1 \<alpha> lst) \<noteq> [] \<and> (remove1 \<beta> lst) \<noteq> []" by (auto simp add: mem_implies_len)
  ultimately have
    mem : "\<alpha> mem remove1 \<beta> lst \<and> \<beta> mem remove1 \<alpha> lst \<and>
          (remove1 \<alpha> lst) \<noteq> [] \<and> (remove1 \<beta> lst) \<noteq> []" by simp
  -- "prove that new list is positive"
  from nl have nl_pos: "pos new_list"
  proof cases
    assume "left_over = []"
    with nl b_pos m_pos show ?thesis by simp
  next
    assume lone: "left_over \<noteq> []"
    from mem pos_imp_rmv_pos pos_lst have "pos (remove1 \<alpha> lst)" by simp
    with lo lone pos_imp_rmv_pos have "pos left_over" by simp
    with lone mem nl m_pos b_pos show ?thesis by simp
  qed

  -- "now show that the new list has the same mean as the old list"
  with mem prems lo bdef \<alpha>mem \<beta>mem
    have "\<Sum>:new_list = \<Sum>:lst"
      apply clarsimp
      apply (subst listsum_rmv1)
        apply simp
      apply (subst listsum_rmv1)
        apply simp
        apply (drule remove1_imp_not_empty)
        apply assumption
      apply clarsimp
    done
  moreover from remove1_len lo nl \<beta>mem \<alpha>mem mem have
    leq: "length new_list = length lst"
    apply -
    apply (erule conjE)+
    apply (clarsimp)
    apply (drule remove1_len [of "\<beta>" "remove1 \<alpha> lst"])
    apply simp
    apply (drule remove1_len [of "\<alpha>" "lst"])
    apply simp
    apply (drule mem_implies_len)
    apply clarsimp
    done
  ultimately have eq_mean: "mean new_list = mean lst" by (rule list_mean_eq_iff)

  -- "finally show that the new list has a greater gmean than the old list"
  have gt_gmean: "gmean new_list > gmean lst"
  proof -
    from bdef \<alpha>_gt \<beta>_lt have "abs (m - b) < abs (\<alpha> - \<beta>)" by arith
    moreover from bdef have "m+b = \<alpha>+\<beta>" .
    ultimately have mb_gt_gt: "m*b > \<alpha>*\<beta>" by (rule le_diff_imp_gt_prod)
    moreover from nl have
      "\<Prod>:new_list = \<Prod>:left_over * (m*b)" by auto
    moreover
    from lo \<alpha>mem \<beta>mem mem remove1_retains_prod have
      lstprod: "\<Prod>:lst = \<Prod>:left_over * (\<alpha>*\<beta>)" by auto
    moreover from lstne have
      "lst \<noteq> []" .
    moreover from nl have
      nlne: "new_list \<noteq> []" by simp
    moreover from pos_asm lo have
      "\<Prod>:left_over > 0"
      proof -
        from pos_asm have "\<Prod>:lst > 0" .
        moreover
        from lstprod have "\<Prod>:lst = \<Prod>:left_over * (\<alpha>*\<beta>)" .
        ultimately have "\<Prod>:left_over * (\<alpha>*\<beta>) > 0" by simp
        moreover
        from pos_els \<alpha>mem \<beta>mem have "\<alpha> > 0" and "\<beta> > 0" by auto
        then have "\<alpha>*\<beta> > 0" by (rule real_mult_order)
        ultimately show "\<Prod>:left_over > 0"
          apply -
          apply (rule zero_less_mult_pos2 [where a="(\<alpha> * \<beta>)"])
          by auto
      qed
    ultimately have "\<Prod>:new_list > \<Prod>:lst"
      apply clarsimp
      apply (rule real_mult_less_mono2)
      apply assumption
      apply assumption
      done
    moreover with pos_asm nl have "\<Prod>:new_list > 0" by auto
    moreover from calculation pos_asm lstne nlne leq list_gmean_gt_iff
    show "gmean new_list > gmean lst" by simp
  qed

  -- "auxillary info"
  from \<beta>_lt have \<beta>_ne_m: "\<beta> \<noteq> m" by simp
  from mem have
    \<beta>_mem_rmv_\<alpha>: "\<beta> mem (remove1 \<alpha> lst)" and rmv_\<alpha>_ne: "(remove1 \<alpha> lst) \<noteq> []" by auto

  from \<alpha>_def have \<alpha>_ne_m: "\<alpha> \<noteq> m" by simp

  -- "now show that new list is more homogeneous"
  have lt_het: "het new_list < het lst"
  proof cases
    assume bm: "b=m"
    with het_def have
      "het new_list = length (list_neq new_list (mean new_list))"
      by simp
    also with m nl eq_mean have
      "\<dots> = length (list_neq (m#b#(left_over)) m)"
      by simp
    also with list_neq_cons bm have
      "\<dots> = length (list_neq left_over m)"
      by simp
    also with lo \<beta>_def \<alpha>_def have
      "\<dots> = length (list_neq (remove1 \<beta> (remove1 \<alpha> lst)) m)"
      by simp
    also from \<beta>_ne_m \<beta>_mem_rmv_\<alpha> rmv_\<alpha>_ne have
      "\<dots> < length (list_neq (remove1 \<alpha> lst) m)"
      apply -
      apply (rule list_neq_remove1)
      by simp
    also from \<alpha>mem \<alpha>_ne_m lstne have
      "\<dots> < length (list_neq lst m)"
      apply -
      apply (rule list_neq_remove1)
      by simp
    also with m het_def have "\<dots> = het lst" by simp
    finally show "het new_list < het lst" .
  next
    assume bnm: "b\<noteq>m"
    with het_def have
      "het new_list = length (list_neq new_list (mean new_list))"
      by simp
    also with m nl eq_mean have
      "\<dots> = length (list_neq (m#b#(left_over)) m)"
      by simp
    also with list_neq_cons bnm have
      "\<dots> = length (b#(list_neq left_over m))"
      by simp
    also have
      "\<dots> = 1 + length (list_neq left_over m)"
      by simp
    also with lo \<beta>_def \<alpha>_def have
      "\<dots> = 1 + length (list_neq (remove1 \<beta> (remove1 \<alpha> lst)) m)"
      by simp
    also from \<beta>_ne_m \<beta>_mem_rmv_\<alpha> rmv_\<alpha>_ne have
      "\<dots> < 1 + length (list_neq (remove1 \<alpha> lst) m)"
      apply -
      apply (simp only: nat_add_left_cancel_less)
      apply (rule list_neq_remove1)
      by simp
    finally have
      "het new_list \<le> length (list_neq (remove1 \<alpha> lst) m)"
      by simp
    also from \<alpha>mem \<alpha>_ne_m lstne have "\<dots> < length (list_neq lst m)"
      apply -
      apply (rule list_neq_remove1)
      by simp
    also with m het_def have "\<dots> = het lst" by simp
    finally show "het new_list < het lst" .
  qed

      -- "thus thesis by existence of newlist"
  from \<gamma>_eq_def lt_het gt_gmean eq_mean leq nl_pos show ?thesis by auto
qed


text {* Furthermore we show that for all non-homogeneous positive
collections there exists another collection that is
$\gamma$-equivalent, positive, has a greater geometric mean {\em and}
is homogeneous. *}

lemma existence_of_het0 [rule_format]:
  shows "\<forall>x. p = het x \<and> p > 0 \<and> pos x \<longrightarrow>
  (\<exists>y. gmean y > gmean x \<and> \<gamma>_eq (x,y) \<and> het y = 0 \<and> pos y)"
  (is "?Q p" is "\<forall>x. (?A x p \<longrightarrow> ?S x)")
proof (induct p rule: nat_less_induct)
  fix n
  assume ind: "\<forall>m<n. ?Q m"
  {
    fix x
    assume ass: "?A x n"
    then have "het x > 0" and "pos x" by auto
    with new_list_gt_gmean have
      "\<exists>y. gmean y > gmean x \<and> \<gamma>_eq (x,y) \<and> het y < het x \<and> pos y"
      apply -
      apply (drule meta_spec [of _ x])
      apply (drule meta_mp)
        apply assumption
      apply (drule meta_mp)
        apply assumption
      apply (subst(asm) \<gamma>_eq_sym)
      apply simp
      done
    then obtain \<beta> where
      \<beta>def: "gmean \<beta> > gmean x \<and> \<gamma>_eq (x,\<beta>) \<and> het \<beta> < het x \<and> pos \<beta>" ..
    then obtain b where bdef: "b = het \<beta>" by simp
    with ass \<beta>def have "b < n" by auto
    with ind have "?Q b" by simp
    with \<beta>def have
      ind2: "b = het \<beta> \<and> 0 < b \<and> pos \<beta> \<longrightarrow>
      (\<exists>y. gmean \<beta> < gmean y \<and> \<gamma>_eq (\<beta>, y) \<and> het y = 0 \<and> pos y)" by simp
    {
      assume "\<not>(0<b)"
      then have "b=0" by simp
      with bdef have "het \<beta> = 0" by simp
      with \<beta>def have "?S x" by auto
    }
    moreover
    {
      assume "0 < b"
      with bdef ind2 \<beta>def have "?S \<beta>" by simp
      then obtain \<gamma> where
        "gmean \<beta> < gmean \<gamma> \<and> \<gamma>_eq (\<beta>, \<gamma>) \<and> het \<gamma> = 0 \<and> pos \<gamma>" ..
      with \<beta>def have "gmean x < gmean \<gamma> \<and> \<gamma>_eq (x,\<gamma>) \<and> het \<gamma> = 0 \<and> pos \<gamma>"
        apply clarsimp
        apply (rule \<gamma>_eq_trans)
        by auto
      hence "?S x" by auto
    }
    ultimately have "?S x" by auto
  }
  then show "?Q n" by simp
qed


subsection {* Cauchy's Mean Theorem *}

text {* We now present the final proof of the theorem. For any
positive collection we show that its geometric mean is less than or
equal to its arithmetic mean. *}

theorem CauchysMeanTheorem:
  fixes z::"real list"
  assumes "pos z"
  shows "gmean z \<le> mean z"
proof -
  have pz: "pos z" .
  then have zne: "z\<noteq>[]" by (rule pos_imp_ne)
  show "gmean z \<le> mean z"
  proof cases
    assume "het z = 0"
    with pz zne het_base have "gmean z = mean z" by simp
    thus ?thesis by simp
  next
    assume "het z \<noteq> 0"
    then have "het z > 0" by simp
    moreover obtain k where "k = het z" by simp
    moreover with calculation pz existence_of_het0 have
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

end
