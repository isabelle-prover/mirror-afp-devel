theory Definition_O2H

imports Registers.Pure_States
  O2H_Additional_Lemmas

begin

unbundle cblinfun_syntax
unbundle lattice_syntax

section \<open>Definitions for the one-way to Hiding (O2H) Lemma\<close>
text \<open>Here, we first define the context of the O2H Lemma and foundations.\<close>

text \<open>First of all, we need a notion of a query to the oracle. This is defined in the unitary 
\<open>Uquery\<close>, where the input \<open>H\<close> is the (classical) oracle.\<close>


definition Uquery :: \<open>('x \<Rightarrow> ('y::plus)) \<Rightarrow> (('x \<times> 'y) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('x \<times> 'y) ell2)\<close> where
  "Uquery H = classical_operator (Some o (\<lambda>(x,y). (x, y + (H x))))"


subsection \<open>Locale for the general O2H setting\<close>


text \<open>Locale for O2H assumptions and setting.\<close>

locale o2h_setting =
  \<comment> \<open>Fix types for instantiations of locales\<close>
  fixes type_x ::"'x itself"
  fixes type_y :: "('y::group_add) itself"
  fixes type_mem :: "'mem itself"
  fixes type_l :: "'l itself"

\<comment> \<open>\<open>X\<close> and \<open>Y\<close> are the embeddings of the (classical) oracle domain types. \<open>'mem\<close> is the type of 
  the quantum memory we work on.\<close>
fixes X :: "'x update \<Rightarrow> 'mem update"
fixes Y :: "('y::group_add) update \<Rightarrow> 'mem update" 

\<comment> \<open>The embeddings \<open>X\<close> and \<open>Y\<close> must be compatible with the registers.\<close>
assumes compat[register]: "mutually compatible (X,Y)"

\<comment> \<open>We fix the query depth \<open>d\<close> of $A$. We ensure that we have queries at least once.\<close>
fixes d :: nat 
assumes d_gr_0: "d > 0" 
  \<comment> \<open>The initial quantum state \<open>init\<close> of the registers. For this version of the O2H, we work with 
    a pure initial state.\<close>
fixes init :: \<open>'mem ell2\<close>
assumes norm_init: "norm init = 1" \<comment>\<open>\<open>init\<close> is a pure state\<close>


\<comment> \<open>The type \<open>'l\<close> represents the quantum register for the query log.
    We also need three functions depending on the type \<open>'l\<close>, namely \<open>flip\<close>, \<open>bit\<close> and \<open>valid\<close>.
    \<open>flip\<close> is a bit-flipping operation that changes bits on the valid set and may behave like an
    identity function on the rest.
    \<open>bit\<close> is a function returning the $i$-th bit of a valid element in \<open>'l\<close>.
    \<open>valid\<close> is a functional representation of the valid set of the query log.
    Since \<open>'l\<close> may be (theoretically) infinitely large, we need to restrict on the valid set in 
    many lemmas.\<close>

fixes flip:: \<open>nat \<Rightarrow> 'l \<Rightarrow> 'l\<close>
fixes bit:: \<open>'l \<Rightarrow> nat \<Rightarrow> bool\<close>
fixes valid:: \<open>'l \<Rightarrow> bool\<close>
fixes empty :: \<open>'l\<close>

\<comment> \<open>Empty is the initial state on \<open>'l\<close> (equalling the zero state).\<close>
assumes valid_empty: "valid empty"

\<comment> \<open>Assumptions on \<open>flip\<close>, \<open>bit\<close> and \<open>valid\<close>: 
    \<open>flip\<close> is a function that takes an index \<open>i\<close> and an element \<open>l::'l\<close> and 
    "flips the $i$-th bit". However, to remain in the valid range, this flip is only performed for
    indices smaller than \<open>d\<close>, otherwise we may assume \<open>flip\<close> to be the identity.\<close>
assumes valid_flip: "i<d \<Longrightarrow> valid l \<Longrightarrow> valid (flip i l)"
  \<comment> \<open>The \<open>flip\<close> operation must be idempotent.\<close>
assumes inj_flip: "inj (flip i)"
assumes valid_flip_flip: "i<d \<Longrightarrow> valid l \<Longrightarrow> flip i (flip i l) = l"
  \<comment> \<open>The \<open>flip\<close> operation must be commutative with itself.\<close>
assumes valid_flip_comm: "i<d \<Longrightarrow> j<d \<Longrightarrow> valid l \<Longrightarrow> flip i (flip j l) = flip j (flip i l)"

\<comment> \<open>For valid elements, the bits in the range up to \<open>d\<close> behave as in a normal 
      bit-flipping operation.\<close>
assumes valid_bit_flip_same: "i<d \<Longrightarrow> valid l \<Longrightarrow> bit (flip i l) i = (\<not> (bit l i))"
assumes valid_bit_flip_diff: "i<d \<Longrightarrow> valid l \<Longrightarrow> i\<noteq>j \<Longrightarrow> bit (flip i l) j = bit l j"



begin
text \<open>We introduce a set of $2^d$ valid elements for counting.
Since we need a finite set for easier proofs while counting the adversarial queries, we embed the 
set of $2^d$ elements into the valid set. 
The elements from \<open>blog\<close> can all be derived by flipping bits from the initial empty state.
We then only look at the elements with bits in the first $d$ entries.\<close>
inductive blog :: "'l \<Rightarrow> bool" where
  "blog empty"
| "blog l \<Longrightarrow> i<d \<Longrightarrow> blog (flip i l)"


lemma blog_empty: "blog empty"
  by (rule blog.intros)

lemma blog_flip: "i<d \<Longrightarrow> blog l \<Longrightarrow> blog (flip i l)" (*bij_on valid flip*)
  by (rule blog.intros)

lemma blog_valid:
  "blog l \<Longrightarrow> valid l"
  by (induction rule: blog.induct) (auto simp add: valid_empty valid_flip)


lemma flip_flip: "i<d \<Longrightarrow> blog l \<Longrightarrow> flip i (flip i l) = l"
  using blog_valid valid_flip_flip by auto

lemma bit_flip_same: "i<d \<Longrightarrow> blog l \<Longrightarrow> bit (flip i l) i = (\<not> (bit l i))"
  using blog_valid valid_bit_flip_same by auto

lemma bit_flip_diff: "i<d \<Longrightarrow> blog l \<Longrightarrow> i\<noteq>j \<Longrightarrow> bit (flip i l) j = bit l j"
  using blog_valid valid_bit_flip_diff by auto

text \<open>The embedding of a boolean list (of length $d$) into the \<open>blog\<close> set.\<close>

fun list_to_l :: "bool list \<Rightarrow> 'l" where  (* intended only for d-length lists *)
  "list_to_l [] = empty" |
  "list_to_l (False # list) = list_to_l list" |
  "list_to_l (True # list) = flip (length list) (list_to_l list)"


definition len_d_lists :: "bool list set" where
  "len_d_lists = {xs. length xs = d}"

lemma card_len_d_lists:
  "card (len_d_lists) = (2::nat)^d" 
proof -
  have l: "len_d_lists = {xs. set xs \<subseteq> {True, False} \<and> length xs = d}" 
    unfolding len_d_lists_def by auto
  show ?thesis unfolding l 
    by (subst card_lists_length_eq[of "{True, False}"])(auto simp add: numeral_2_eq_2)
qed

lemma finite_len_d_lists[simp]:
  "finite len_d_lists"
  using card_len_d_lists card.infinite by force




lemma blog_list_to_l:
  assumes "length ls \<le> d"
  shows "blog (list_to_l ls)"
  using assms by (induction rule: list_to_l.induct) (auto simp add: blog.intros)

lemma flip_commute:
  assumes "i\<noteq>j" "i<d" "j<d" "length ls \<le> d"
  shows "flip i (flip j (list_to_l ls)) = flip j (flip i (list_to_l ls))"
  by (simp add: assms(2) assms(3) assms(4) blog_list_to_l blog_valid valid_flip_comm)

lemma flip_list_to_l:
  assumes "i < length ls" "length ls \<le> d"
  shows "flip i (list_to_l ls) = list_to_l (ls[length ls - i - 1 := \<not> ls ! (length ls - i - 1)])"
  using assms proof (induction ls arbitrary: i rule: list_to_l.induct)
  case (2 l)
  have "i<d" using 2 by auto
  show ?case proof (cases "i=length l")
    case True 
    have "flip i (list_to_l (False # l)) = flip i (list_to_l l)" by auto
    also have "\<dots> = list_to_l (True # l)" by (simp add: True)
    also have "\<dots> = list_to_l ((False # l)[length (False # l) - i - 1 :=
         \<not> (False # l) ! (length (False # l) - i - 1)])" unfolding \<open>i=length l\<close> by auto
    finally show ?thesis by auto
  next
    case False
    then have "i<length l" using "2"(2) by auto
    let ?l = "False # l"
    have "flip i (list_to_l (False # l)) = flip i (list_to_l l)" by auto
    also have "\<dots> = list_to_l (l[length l-i-1 := \<not>l!(length l-i-1)])" using 2 
      by (simp add: \<open>i < length l\<close>)
    also have "\<dots> = list_to_l (?l[length ?l-i-1 := \<not>?l!(length ?l-i-1)])"
      by (smt (verit, ccfv_threshold) "2"(2) Nat.diff_add_assoc2 Suc_diff_Suc Suc_eq_plus1 
          \<open>i < length l\<close> diff_Suc_1 diff_is_0_eq leD le_simps(3) list.size(4) list_update_code(3) 
          nth_Cons' numeral_nat(7) list_to_l.simps(2))
    finally show ?thesis by auto
  qed
next
  case (3 l)
  have "i<d" using 3 by auto
  show ?case proof (cases "i=length l")
    case True 
    have blog: "blog (list_to_l l)" using blog_list_to_l 3(3) by auto
    have "flip i (list_to_l (True # l)) = flip i (flip i (list_to_l l))" using True by auto
    also have "\<dots> = list_to_l l" using flip_flip[OF \<open>i<d\<close>] blog by auto
    finally show ?thesis using True by auto
  next
    case False
    then have "i<length l" using "3"(2) by auto
    let ?l = "True # l"
    have "flip i (list_to_l ?l) = flip i (flip (length l) (list_to_l l))" by auto
    also have "\<dots> = flip (length l) (flip i (list_to_l l))"
      by (intro flip_commute) (use 3 in \<open>auto simp add: False \<open>i<d\<close> \<close>)
    also have "\<dots> = flip (length l) (list_to_l (l[length l-i-1 := \<not>l!(length l-i-1)]))"
      using "3"(3) "3.IH" \<open>i < length l\<close> by auto
    also have "\<dots> = list_to_l (True # (l[length l-i-1 := \<not>l!(length l-i-1)]))" by simp
    also have "\<dots> = list_to_l (?l[length ?l-i-1 := \<not>?l!(length ?l-i-1)])"
      by (smt (verit, ccfv_threshold) Suc_diff_Suc \<open>i < length l\<close>
          cancel_ab_semigroup_add_class.diff_right_commute diff_Suc_eq_diff_pred length_tl list.sel(3) 
          list_update_code(3) nth_Cons_Suc)
    finally show ?thesis by auto
  qed
qed auto

text \<open>The initial list corresponding to the initial value \<open>empty\<close> is the list containing only 
\<open>False\<close>.\<close>

definition empty_list where
  "empty_list = replicate d False"

lemma empty_list_to_l_replicate:
  "list_to_l (replicate n False) = empty" 
  by (induct n, auto)

lemma empty_list_to_l [simp]:
  "list_to_l empty_list = empty" 
  by (auto simp add: empty_list_to_l_replicate empty_list_def)

lemma empty_list_len_d[simp]:
  "empty_list \<in> len_d_lists"
  unfolding empty_list_def len_d_lists_def by auto

lemma empty_list_to_l_elem [simp]:
  "empty \<in> list_to_l ` len_d_lists"
  by (metis empty_list_len_d empty_list_to_l imageI)


text \<open>Lemmas on how \<open>list_to_l\<close> works with \<open>flip\<close> and \<open>bit\<close>.\<close>

lemma list_to_l_flip:
  assumes "i < length ls" "length ls \<le> d"
  shows "list_to_l (ls[i := \<not> ls ! i]) = flip (length ls - 1 - i) (list_to_l ls)"
  using assms proof (induction ls arbitrary: i rule: list_to_l.induct)
  case (2 list)
  then show ?case proof (cases "i=0")
    case False
    then obtain j where j: "i = Suc j" using not0_implies_Suc by presburger
    have "list_to_l ((False # list)[i := \<not> (False # list) ! i]) = 
      list_to_l (False # list[i-1 := \<not> list ! (i-1)])" unfolding j by auto
    also have "\<dots> = list_to_l (list[i-1 := \<not> list ! (i-1)])" by auto
    also have "\<dots> = flip (length list - 1 - (i-1)) (list_to_l list)" using 2 "2.IH" j by auto
    also have "\<dots> = flip (length (False # list) - 1 - i) (list_to_l (False # list))"
      by (simp add: j)
    finally show ?thesis by auto
  qed auto
next
  case (3 list)
  then show ?case proof (cases "i=0")
    case True
    have False: "(True # list)[i := \<not> (True # list) ! i] = False # list" using True by auto
    have len: "length (True # list) - 1 - i = length list" using True by auto
    have len': "length list < d" using 3 by auto
    have len'': "length list \<le> d" using 3 by auto
    have "list_to_l list = flip (length list) (flip (length list) (list_to_l list))"
      using flip_flip[OF len'] by (simp add: blog_list_to_l len'') 
    then show ?thesis unfolding False len by (subst list_to_l.simps)+ auto
  next
    case False
    then obtain j where j: "i = Suc j" using not0_implies_Suc by presburger
    have len: "length list < d" using 3 by auto
    have "list_to_l ((True # list)[i := \<not> (True # list) ! i]) = 
      list_to_l (True # list[i-1 := \<not> list ! (i-1)])" unfolding j by auto
    also have "\<dots> = flip (length list) (list_to_l (list[i-1 := \<not> list ! (i-1)]))" by auto
    also have "\<dots> = flip (length list) (flip (length list - 1 - (i-1)) (list_to_l list))" 
      using 3 "3.IH" j by auto
    also have "\<dots> = flip (length list) (flip (length (True # list) - 1 - i) (list_to_l list))"
      by (simp add: j)
    also have "\<dots> = flip (length (True # list) - 1 - i) (flip (length list) (list_to_l list))"
      by (intro flip_commute) (use 3 j in \<open>auto simp add: len\<close>)
    finally show ?thesis by auto
  qed
qed auto

lemma surj_list_to_l: "list_to_l  ` len_d_lists = Collect blog" 
proof (safe, goal_cases)
  case (1 _ xa)
  then have "length xa \<le> d" unfolding len_d_lists_def by auto
  then show ?case proof (induct xa rule: list_to_l.induct)
    case 1
    show ?case by (auto simp add: blog.intros)
  next
    case (2 list)
    then show ?case by (subst list_to_l.simps(2), simp)
  next
    case (3 list)
    then show ?case by (subst list_to_l.simps(3), intro blog.intros, auto)
  qed
next
  case (2 x)
  then show ?case proof (induct rule: blog.induct)
    case 1
    show ?case by (subst empty_list_to_l[symmetric]) auto
  next
    case (2 l i)
    then obtain ls where ls: "list_to_l ls = l" "length ls = d" using len_d_lists_def by force
    have "blog (flip i l)" using 2 by (intro blog.intros, auto)
    define flip_ls where "flip_ls = ls [d-i-1:= \<not> ls!(d-i-1)]"
    then have "length flip_ls = d" using \<open>length ls = d\<close> by auto
    moreover have "list_to_l flip_ls = flip i l" unfolding flip_ls_def ls(2)[symmetric] 
      by (subst flip_list_to_l[symmetric]) (auto simp add:2 ls)
    ultimately show ?case unfolding len_d_lists_def by (simp add: rev_image_eqI)
  qed
qed

lemma bit_list_to_l_over:
  assumes "length l \<le> d" "i<d" "length l \<le> i"
  shows "bit (list_to_l l) i = bit empty i"
  using assms proof (induct rule: list_to_l.induct)
  case (2 list)
  then show ?case using bit_flip_same[OF \<open>i<d\<close>] by auto
next
  case (3 list)
  then show ?case by (auto simp add: bit_flip_diff blog_list_to_l)
qed auto


lemma bit_list_to_l:
  assumes "length l \<le> d" "i<length l"
  shows "bit (list_to_l l) i = (if l!(length l-i-1) then \<not> bit empty i else bit empty i)"
  using assms proof (induct rule: list_to_l.induct)
  case (2 list)
  let ?l = "False # list"
  have "length list \<le> d" using 2 by auto
  have "i<d" using 2 by auto
  have rew: "bit (list_to_l ?l) i = bit (list_to_l list) i" by auto
  have c1: "bit (list_to_l list) i = (if ?l!(length ?l-i-1) then \<not> bit empty i else bit empty i)"
    if "i\<noteq>length list" using "2"(1) "2"(3) \<open>length list \<le> d\<close> that by auto
  have c2: "bit (list_to_l list) i = (if ?l!(length ?l-i-1) then \<not> bit empty i else bit empty i)"
    if "i=length list" using that by (subst bit_list_to_l_over[OF \<open>length list \<le> d\<close> \<open>i<d\<close>]) auto
  show ?case by (subst rew, cases "i = length list")(use c1 c2 in \<open>auto\<close>)
next
  case (3 list)
  let ?l = "True # list"
  have "length list \<le> d" using 3 by auto
  have "i<d" using 3 by auto
  have rew: "bit (list_to_l ?l) i = bit (flip (length list) (list_to_l list)) i" (is "_ = ?right") 
    by auto
  have c1: "?right = (if ?l!(length ?l-i-1) then \<not> bit empty i else bit empty i)" 
    if "i\<noteq>length list"
  proof -
    have "?right = bit (list_to_l list) i" using that "3"(2) blog_list_to_l 
        blog_valid valid_bit_flip_diff by force
    also have "\<dots> = (if ?l!(length ?l-i-1) then \<not> bit empty i else bit empty i)" 
      using 3 \<open>length list \<le> d\<close> that by auto
    finally show ?thesis by auto
  qed
  have c2: "?right = (if ?l!(length ?l-i-1) then \<not> bit empty i else bit empty i)"
    if "i=length list" 
  proof -
    have "?right = (\<not> bit (list_to_l list) i)"
      using \<open>i < d\<close> \<open>length list \<le> d\<close> bit_flip_same blog_list_to_l that by blast
    also have "\<dots> = (\<not> bit empty i)"
      using \<open>i < d\<close> bit_list_to_l_over less_or_eq_imp_le that by blast 
    finally show ?thesis using that by auto
  qed
  show ?case by (subst rew, cases "i = length list")(use c1 c2 in \<open>auto\<close>)
qed auto

lemma list_to_l_eq:
  assumes "list_to_l xs = list_to_l ys" "length xs = d" "length ys = d"
  shows "xs = ys"
  using le0[of d] assms proof (induct d arbitrary: xs ys rule: Nat.dec_induct)
  case (step n)
  obtain x xs' where xs: "xs = x # xs'" "length xs' = n" using step by (meson length_Suc_conv)
  obtain y ys' where ys: "ys = y # ys'" "length ys' = n"using step by (meson length_Suc_conv)
  consider (same) "x=y" | (neq) "x\<noteq>y" by blast 
  then have "list_to_l xs' = list_to_l ys' \<and> x=y" 
  proof (cases)
    case same
    then have "list_to_l xs' = list_to_l ys'"
      by (metis (full_types) blog_list_to_l flip_flip list_to_l.simps(2,3) step(2,4) 
          not_le order.asym xs ys)
    then show ?thesis using same by blast
  next
    case neq
    have False by (metis One_nat_def Suc_leI bit_list_to_l diff_Suc_1 diff_add_inverse2 lessI 
          step(2,4,5,6) neq nth_Cons_0 plus_1_eq_Suc xs(1) ys(1))
    then show ?thesis by auto
  qed
  then show ?case unfolding xs ys by (simp add: local.step(3) xs(2) ys(2))
qed auto


lemma inj_list_to_l: "inj_on list_to_l (len_d_lists)" 
  unfolding inj_on_def proof (safe, goal_cases)
  case (1 xs ys)
  have len: "length xs = d" "length ys = d" using 1 unfolding len_d_lists_def by auto
  show ?case using len 1 list_to_l_eq by auto
qed


lemma bij_betw_list_to_l: "bij_betw list_to_l len_d_lists (Collect blog)"
  using bij_betw_def inj_list_to_l surj_list_to_l by blast

lemma card_blog: "card (Collect blog) = 2^d"
  by (metis card_image card_len_d_lists inj_list_to_l surj_list_to_l)





text \<open>We split the $2^d$ elements into elements that have bits only in a certain set.
This is later used to argue that an adversary running up to some $n$ can only generate a 
count up to the $n$-th bit.\<close>

(* How to address values in {2^n..<2^d} in len_d_list *)
definition has_bits :: "nat set \<Rightarrow> bool list set" where
  "has_bits A = {l. l\<in>len_d_lists \<and> True \<in> (\<lambda>i. l!(d-i-1)) ` A}"


lemma has_bits_empty[simp]:
  "has_bits {} = {}" 
  unfolding has_bits_def by auto

lemma has_bits_not_empty:
  assumes "y \<in> has_bits A" "A\<noteq>{}" "y\<in>len_d_lists"
  shows "list_to_l y \<noteq> empty"
proof -
  obtain x where "x\<in>A" "y!(d-x-1)" using assms unfolding has_bits_def by auto
  then show ?thesis
    by (smt (verit, best) assms(3) bit_list_to_l d_gr_0 diff_Suc_1 diff_diff_cancel diff_is_0_eq' 
        diff_le_self le_simps(2) len_d_lists_def mem_Collect_eq not_le)
qed

lemma has_bits_empty_list:
  "empty_list \<notin> has_bits {0..<d}"
  using has_bits_not_empty by fastforce

lemma has_bits_incl:
  assumes "A\<subseteq>B"
  shows "has_bits A \<subseteq> has_bits B"
  using assms has_bits_def by auto

lemma has_bits_in_len_d_lists[simp]:
  "has_bits A \<subseteq> len_d_lists"
  unfolding has_bits_def by auto

lemma finite_has_bits[simp]:
  "finite (has_bits A)"
  by (meson finite_len_d_lists has_bits_in_len_d_lists rev_finite_subset)

lemma has_bits_not_elem:
  assumes "y\<in>has_bits A" "A\<noteq>{}" "A\<subseteq>{0..<d}" "y\<in>len_d_lists" "n \<notin> A" "n<d"
  shows "y[d-n-1:=\<not>y!(d-n-1)] \<in> has_bits A"
proof -
  obtain i where i: "y ! (d - i - 1)" "i\<in>A" using assms has_bits_def by auto
  then have "n\<noteq>i" using assms by auto
  then have "y[d-n-1 := \<not> y!(d-n-1)]!(d-i-1)" using i assms by (subst nth_list_update_neq) auto
  moreover have "length (y[d - n - 1 := \<not> y ! (d - n - 1)]) = d" using assms len_d_lists_def by auto
  ultimately show ?thesis using \<open>i\<in>A\<close> unfolding has_bits_def len_d_lists_def by auto
qed

lemma has_bits_split_Suc:
  assumes "n<d"
  shows "has_bits {n..<d} = has_bits {n} \<union> has_bits {Suc n..<d}"
proof -
  have "x \<in> len_d_lists \<Longrightarrow> x ! (d - Suc xa) \<Longrightarrow> \<forall>xa\<in>{Suc n..<d}. \<not> x ! (d - Suc xa) \<Longrightarrow>
       n \<le> xa \<Longrightarrow> xa < d \<Longrightarrow> x ! (d - Suc n)" for x xa
    by (metis atLeastLessThan_iff le_eq_less_or_eq le_simps(3))
  moreover have "x \<in> len_d_lists \<Longrightarrow> x ! (d - Suc n) \<Longrightarrow> \<exists>xa\<in>{n..<d}. x ! (d - Suc xa)" for x
    using assms atLeastLessThan_iff by blast
  ultimately show ?thesis unfolding has_bits_def by auto
qed

text \<open>The function \<open>has_bits_upto\<close> looks only at elements with bits lower than some $n$.\<close>

definition has_bits_upto where
  "has_bits_upto n = len_d_lists - has_bits {n..<d}"

lemma finite_has_bits_upto [simp]:
  "finite (has_bits_upto n)"
  unfolding has_bits_upto_def by auto

lemma has_bits_elem:
  assumes "x \<in> len_d_lists - has_bits A" "a\<in>A"
  shows "\<not>x!(d-a-1)"
  using assms(1) assms(2) has_bits_def by force

lemma has_bits_upto_elem:
  assumes "x \<in> has_bits_upto n" "n<d"
  shows "\<not>x!(d-n-1)"
  using assms has_bits_upto_def by (intro has_bits_elem[of x "{n..<d}" n]) auto

lemma has_bits_upto_incl:
  assumes "n \<le> m"
  shows "has_bits_upto n \<subseteq> has_bits_upto m"
  using assms unfolding has_bits_upto_def by (simp add: Diff_mono has_bits_incl)

lemma has_bits_upto_d:
  "has_bits_upto d = len_d_lists"
  unfolding has_bits_upto_def by auto

lemma empty_list_has_bits_upto:
  "empty_list \<in> has_bits_upto n" 
  using empty_list_to_l has_bits_not_empty has_bits_upto_def by fastforce

lemma empty_list_to_l_has_bits_upto:
  "empty \<in> list_to_l ` has_bits_upto n"
  using empty_list_has_bits_upto empty_list_to_l by (metis image_eqI)

lemma len_d_empty_has_bits:
  "len_d_lists - {empty_list} = has_bits {0..<d}"
proof (safe, goal_cases)
  case (1 x)
  then have "\<not> x!(d-i-1)" if "i<d" for i using has_bits_elem that by auto
  then have "\<not> x!i" if "i<d" for i
    by (metis Suc_leI d_gr_0 diff_Suc_less diff_add_inverse diff_diff_cancel plus_1_eq_Suc that)
  then have "x = empty_list" unfolding empty_list_def
    by (smt (verit, best) "1"(1) in_set_conv_nth len_d_lists_def mem_Collect_eq replicate_eqI)
  then show ?case by auto
qed (auto simp add: has_bits_def has_bits_empty_list empty_list_def)






text \<open>Properties of \<open>d\<close>\<close>
lemma two_d_gr_1:
  "2^d > (1::nat)"
  by (meson d_gr_0 one_less_power rel_simps(49) semiring_norm(76))

text \<open>Lemmas on \<open>flip\<close>, \<open>bit\<close> and \<open>valid\<close>.\<close>
lemma valid_inv: "- Collect valid = valid -` {False}" by auto

lemma blog_inv: "- Collect blog = blog -` {False}" by auto

lemma not_blog_flip: "i<d \<Longrightarrow> (\<not> blog l) \<Longrightarrow> (\<not> blog (flip i l))"
  by (metis blog.intros(2) blog_valid inj_def inj_flip valid_flip_flip)




text \<open>Lemmas on \<open>X\<close> and \<open>Y\<close>. 
\<open>X\<close> and \<open>Y\<close> are embeddings of the classical memory parts of input and output registers to the 
oracle function into the quantum register \<open>'mem\<close>.\<close>
lemma register_X:
  "register X"
  by auto

lemma register_Y:
  "register Y"
  by auto

lemma X_0:
  "X 0 = 0" using clinear_register complex_vector.linear_0 register_X by blast


text \<open>How to check that no qubit in \<open>'x\<close> is in the set \<open>S\<close> in a quantum setting.
This is more complicated, since we cannot just ask if $x\in S$. We need to ask for the embedding 
of the projection of the classical set $S$ in the register \<open>X\<close>.\<close>

definition "proj_classical_set M = Proj (ccspan (ket ` M))" 
  (* This definition was taken from https://github.com/dominique-unruh/qrhl-tool/blob/
ecffff7667ab1e9b2cf957de82dfa7d22a8bd91a/isabelle-thys/QRHL_Core.thy#LL1864C1-L1864C69 *)
definition "S_embed S' = X (proj_classical_set (Collect S'))"
definition "not_S_embed S' = X (proj_classical_set (- (Collect S')))"


lemma is_Proj_proj_classical_set:
  "is_Proj (proj_classical_set M)"
  unfolding proj_classical_set_def by auto

lemma proj_classical_set_split_id:
  "id_cblinfun = proj_classical_set M + proj_classical_set (-M)"
  unfolding proj_classical_set_def
  by (smt (verit) Compl_iff Proj_orthog_ccspan_union Proj_top boolean_algebra_class.sup_compl_top 
      ccspan_range_ket imageE image_Un orthogonal_ket)

lemma proj_classical_set_sum_ket_finite:
  assumes "finite A"
  shows "proj_classical_set A = (\<Sum>i\<in>A. selfbutter (ket i))"
  using assms proof (induction A rule: Finite_Set.finite.induct)
  case (insertI A a)
  show ?case proof (cases "a\<in>A")
    case False
    have insert: "ket ` (insert a A) = insert (ket a) (ket ` A)" by auto
    have Proj: "Proj (ccspan (ket ` A)) = (\<Sum>i\<in>A. proj (ket i))" 
      using insertI unfolding proj_classical_set_def by (auto simp add: butterfly_eq_proj)
    show ?thesis unfolding proj_classical_set_def insert 
    proof (subst Proj_orthog_ccspan_insert, goal_cases)
      case 2
      then show ?case unfolding Proj
        by (simp add: False butterfly_eq_proj local.insertI(1))
    qed  (auto simp add: False)
  qed (simp add: insertI insert_absorb)
qed (auto simp add: proj_classical_set_def)


lemma proj_classical_set_not_elem:
  assumes "i\<notin>A"
  shows "proj_classical_set A *\<^sub>V ket i = 0"
  by (metis Compl_iff Proj_fixes_image add_cancel_right_left assms cblinfun.add_left ccspan_superset' 
      id_cblinfun_apply proj_classical_set_def proj_classical_set_split_id rev_image_eqI)

lemma proj_classical_set_elem:
  assumes "i\<in>A"
  shows "proj_classical_set A *\<^sub>V ket i = ket i"
  using assms by (simp add: Proj_fixes_image ccspan_superset' proj_classical_set_def)


lemma proj_classical_set_upto:
  assumes "i<j"
  shows "proj_classical_set {j..} *\<^sub>V ket (i::nat) = 0"
  by (intro proj_classical_set_not_elem) (use assms in \<open>auto\<close>)

lemma proj_classical_set_apply:
  assumes "finite A"
  shows "proj_classical_set A *\<^sub>V y = (\<Sum>i\<in>A. Rep_ell2 y i *\<^sub>C ket i)"
  unfolding proj_classical_set_def trunc_ell2_as_Proj[symmetric]
  by (intro trunc_ell2_finite_sum, simp add: assms)

lemma proj_classical_set_split_Suc:
  "proj_classical_set {n..} = proj (ket n) + proj_classical_set {Suc n..}"
proof -
  have " ket ` {n..} = insert (ket n) (ket ` {Suc n..})" by fastforce
  then show ?thesis unfolding proj_classical_set_def 
    by (subst Proj_orthog_ccspan_insert[symmetric]) auto 
qed

lemma proj_classical_set_union:
  assumes "\<And>x y. x \<in> ket ` A \<Longrightarrow> y \<in> ket ` B \<Longrightarrow> is_orthogonal x y"
  shows "proj_classical_set (A \<union> B) = proj_classical_set A + proj_classical_set B"
  unfolding proj_classical_set_def 
  by (subst image_Un, intro Proj_orthog_ccspan_union)(auto simp add: assms)


text \<open>Later, we need to project only on the second part of the register (the counting part).\<close>

definition Proj_ket_set :: "'a set \<Rightarrow> ('mem \<times> 'a) update" where
  "Proj_ket_set A = id_cblinfun \<otimes>\<^sub>o proj_classical_set A"

lemma Proj_ket_set_vec:
  assumes "y \<in> A"
  shows "Proj_ket_set A *\<^sub>V (v \<otimes>\<^sub>s ket y) = v \<otimes>\<^sub>s ket y"
  unfolding Proj_ket_set_def using proj_classical_set_elem[OF assms] 
  by (auto simp add: tensor_op_ell2)


definition Proj_ket_upto :: "bool list set \<Rightarrow> ('mem \<times> 'l) update" where
  "Proj_ket_upto A = Proj_ket_set (list_to_l ` A)"

lemma Proj_ket_upto_vec:
  assumes "y \<in> A"
  shows "Proj_ket_upto A *\<^sub>V (v \<otimes>\<^sub>s ket (list_to_l y)) = v \<otimes>\<^sub>s ket (list_to_l y)"
  unfolding Proj_ket_upto_def using assms by (auto intro!: Proj_ket_set_vec)


text \<open>We can split a state into two parts: the part in \<open>S\<close> and the one not in \<open>S\<close>.\<close>
lemma S_embed_not_S_embed_id [simp]:
  "S_embed S' + not_S_embed S' = id_cblinfun"
proof -
  have "proj_classical_set (Collect S') + proj_classical_set (- (Collect S')) = id_cblinfun"
    unfolding proj_classical_set_def 
    by (subst Proj_orthog_ccspan_union[symmetric]) (auto simp add: image_Un[symmetric])
  then have *: "X (proj_classical_set (Collect S') + proj_classical_set (- (Collect S'))) = 
    X id_cblinfun" by auto
  have "X (proj_classical_set (Collect S')) + X (proj_classical_set (- (Collect S'))) = 
    X id_cblinfun" unfolding *[symmetric]
    using clinear_register[OF register_X] by (simp add: clinear_iff)
  then show ?thesis unfolding S_embed_def not_S_embed_def by auto
qed

lemma S_embed_not_S_embed_add:
  "S_embed S' (ket a) + not_S_embed S' (ket a) = ket a"
  using S_embed_not_S_embed_id
  by (metis cblinfun_id_cblinfun_apply plus_cblinfun.rep_eq)

lemma S_embed_idem [simp]:
  "S_embed S' o\<^sub>C\<^sub>L S_embed S' = S_embed S'"
  unfolding S_embed_def Axioms_Quantum.register_mult[OF register_X] proj_classical_set_def by auto

lemma S_embed_adj:
  "(S_embed S')* = S_embed S'"
  unfolding S_embed_def register_adj[OF register_X, symmetric] proj_classical_set_def adj_Proj
  by auto

lemma not_S_embed_idem:
  "not_S_embed S' o\<^sub>C\<^sub>L not_S_embed S' = not_S_embed S'"
  unfolding not_S_embed_def Axioms_Quantum.register_mult[OF register_X] proj_classical_set_def by auto

lemma not_S_embed_adj:
  "(not_S_embed S')* = not_S_embed S'"
  unfolding not_S_embed_def register_adj[OF register_X, symmetric] proj_classical_set_def adj_Proj
  by auto


lemma not_S_embed_S_embed [simp]:
  "not_S_embed S' o\<^sub>C\<^sub>L S_embed S' = 0"
proof -
  have "orthogonal_spaces (ccspan (ket ` (- Collect S'))) (ccspan (ket ` Collect S'))" 
    using orthogonal_spaces_ccspan by fastforce
  then have "proj_classical_set (- Collect S') o\<^sub>C\<^sub>L proj_classical_set (Collect S') = 0"
    unfolding proj_classical_set_def using orthogonal_projectors_orthogonal_spaces by auto
  then show ?thesis unfolding not_S_embed_def S_embed_def Axioms_Quantum.register_mult[OF register_X] 
    using X_0 by auto
qed

lemma S_embed_not_S_embed [simp]:
  "S_embed S' o\<^sub>C\<^sub>L not_S_embed S' = 0"
  by (metis S_embed_adj adj_0 adj_cblinfun_compose not_S_embed_S_embed not_S_embed_adj)

lemma not_S_embed_Proj:
  "not_S_embed S = Proj (not_S_embed S *\<^sub>S \<top>)"
  unfolding not_S_embed_def using register_projector[OF register_X is_Proj_proj_classical_set]
  by (simp add: Proj_on_own_range)

lemma not_S_embed_in_X_image:
  assumes "a \<in> space_as_set (- (not_S_embed S *\<^sub>S \<top>))" 
  shows "(not_S_embed S)*\<^sub>V a = 0"
  using register_projector[OF register_X is_Proj_proj_classical_set]
    Proj_0_compl[OF assms] unfolding not_S_embed_def by (simp add: Proj_on_own_range)

text \<open>In the register for the adversary runs \<open>run_B\<close> and \<open>run_B_count\<close>, 
we want to look at the \<open>'mem\<close> part only.
\<open>\<Psi>s\<close> lets us look at the \<open>'mem\<close> part that is tensored with the \<open>i\<close>-th ket state.\<close>
definition \<Psi>s where "\<Psi>s i v = (tensor_ell2_right (ket i)*) *\<^sub>V v"

lemma tensor_ell2_right_compose_id_cblinfun:
  "tensor_ell2_right (ket a)* o\<^sub>C\<^sub>L A \<otimes>\<^sub>o id_cblinfun = A o\<^sub>C\<^sub>L tensor_ell2_right (ket a)*"
  by (intro equal_ket)(auto simp add: tensor_ell2_ket[symmetric] tensor_op_ell2 cblinfun.scaleC_right)

lemma \<Psi>s_id_cblinfun:
  "\<Psi>s a ((A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V v) = A *\<^sub>V (\<Psi>s a v)"
  unfolding \<Psi>s_def 
  by (auto simp add: cblinfun_apply_cblinfun_compose[symmetric] tensor_ell2_right_compose_id_cblinfun
      simp del: cblinfun_apply_cblinfun_compose)


text \<open>Additional Lemmas\<close>

lemma id_cblinfun_tensor_split_finite:
  assumes "finite A"
  shows "(id_cblinfun:: ('mem \<times> 'a) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('mem \<times> 'a) ell2) = 
 (\<Sum>i\<in>A. (tensor_ell2_right (ket i)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)*)) + 
  Proj_ket_set (-A)" 
proof -
  have "(id_cblinfun:: ('mem \<times> 'a) update) = id_cblinfun \<otimes>\<^sub>o id_cblinfun" by auto
  also have "\<dots> = id_cblinfun \<otimes>\<^sub>o (proj_classical_set A + proj_classical_set (-A))"
    by (subst proj_classical_set_split_id[of "A"]) (auto)
  also have "\<dots> = id_cblinfun \<otimes>\<^sub>o (\<Sum>i\<in>A. selfbutter (ket i)) + 
    Proj_ket_set (-A)" unfolding Proj_ket_set_def
    by (subst proj_classical_set_sum_ket_finite[OF assms])(auto simp add: tensor_op_right_add)
  also have "\<dots> = (\<Sum>i\<in>A. id_cblinfun \<otimes>\<^sub>o selfbutter (ket i)) +
    Proj_ket_set (-A)"
    using clinear_tensor_right complex_vector.linear_sum by (smt (verit, best) sum.cong)
  also have "\<dots> = (\<Sum>i\<in>A. (tensor_ell2_right (ket i)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)*)) +
    Proj_ket_set (-A)" 
    by (simp add: tensor_ell2_right_butterfly)
  finally show ?thesis by auto
qed


text \<open>Lemmas on sums of butterflys\<close>

lemma sum_butterfly_ket0:
  assumes "(y::nat)<d+1"
  shows "(\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V (ket y) = ket 0"
proof -
  have "(\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V ket y = (\<Sum>i<d+1. if i=y then ket 0 else 0)"
    by (subst cblinfun.sum_left, intro sum.cong, auto)
  also have "\<dots> = ket 0"  by (subst sum.delta, use assms in \<open>auto\<close>)
  finally show ?thesis by auto
qed

lemma sum_butterfly_ket0':
  "(\<Sum>i<d+1. butterfly (ket 0) (ket i))*\<^sub>V proj_classical_set {..<d+1} *\<^sub>V y =
 (\<Sum>i<d+1. Rep_ell2 y i) *\<^sub>C ket 0" 
  for y::"nat ell2"
proof -
  have "(\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V proj_classical_set {..<d+1} *\<^sub>V y =
        (\<Sum>i<d+1. Rep_ell2 y i *\<^sub>C (\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V ket i)"
    by (subst proj_classical_set_apply, simp) 
      (subst cblinfun.sum_right, intro sum.cong, auto simp add: cblinfun.scaleC_right)
  also have "\<dots> = (\<Sum>i<d+1. Rep_ell2 y i *\<^sub>C ket 0)" 
    by (intro sum.cong) (use sum_butterfly_ket0 in \<open>auto\<close>)
  also have "\<dots> = (\<Sum>i<d+1. Rep_ell2 y i) *\<^sub>C ket 0" by (rule scaleC_sum_left[symmetric]) 
  finally show ?thesis by auto
qed




text \<open>The oracle query is a unitary.\<close>

lemma inj_Uquery_map:
  "inj (\<lambda>(x, (y::'y)). (x, y + H x))"
  unfolding inj_def by auto

lemma classical_operator_exists_Uquery:
  "classical_operator_exists (Some o (\<lambda>(x,(y::'y)). (x, y + (H x))))"
  by (intro classical_operator_exists_inj, subst inj_map_total)
    (auto simp add: inj_Uquery_map)

lemma Uquery_ket:
  "Uquery F *\<^sub>V ket (a::'x) \<otimes>\<^sub>s ket (b::'y) = ket a \<otimes>\<^sub>s ket (b + F a)"
  unfolding Uquery_def tensor_ell2_ket 
  by (subst classical_operator_ket[OF classical_operator_exists_Uquery]) auto



lemma unitary_H: "unitary (Uquery (H::'x \<Rightarrow> 'y))"
proof -
  have inj: "inj (\<lambda>(x, y). (x, y + H x))" by (auto simp add: inj_on_def)
  have surj: "surj (\<lambda>(x, y). (x, y + H x))" 
    by (metis (mono_tags, lifting) case_prod_Pair_iden diff_add_cancel split_conv split_def surj_def)
  show ?thesis unfolding Uquery_def 
    by (intro unitary_classical_operator) (auto simp add: inj surj bij_def)
qed

end

unbundle no cblinfun_syntax
unbundle no lattice_syntax

end