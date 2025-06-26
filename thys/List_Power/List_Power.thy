(*
Author: Tobias Nipkow
Author: Štěpán Holub, Charles University

Based on the AFP entry Combinatorics_Words by Holub, Raška and Starosta
*)

section \<open>The Power Operator \<open>^^\<close> on Lists\<close>

theory List_Power
imports Main
begin

overloading pow_list == "compow :: nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
begin

primrec pow_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pow_list 0 xs = []" |
  "pow_list (Suc n) xs = xs @ pow_list n xs"

end

context
begin

interpretation monoid_mult "[]" "append"
  rewrites "power u n = u ^^ n"
proof-
  show "class.monoid_mult [] (@)"
    by (unfold_locales, simp_all)
  show "power.power [] (@) u n = u ^^ n"
    by(induction n) (auto simp add: power.power.simps)
qed

\<comment> \<open>inherited power properties\<close>

lemmas pow_list_zero = power.power_0 and
  pow_list_one = power_Suc0_right and
  pow_list_1 = power_one_right and
  pow_list_Nil = power_one and
  pow_list_2 = power2_eq_square and
  pow_list_Suc = power_Suc and
  pow_list_Suc2 = power_Suc2 and
  pow_list_comm = power_commutes and
  pow_list_add = power_add and
  pow_list_eq_if = power_eq_if and
  pow_list_mult = power_mult and
  pow_list_commuting_commutes = power_commuting_commutes

end

lemmas[simp] = pow_list_Nil pow_list_zero pow_list_one pow_list_1 pow_list_Suc pow_list_2

lemma pow_list_alt: "xs^^n = concat (replicate n xs)"
  by (induct n) auto

lemma pow_list_single: "[a] ^^ m = replicate m a"
  by(simp add: pow_list_alt)

lemma length_pow_list_single [simp]: "length([a] ^^ n) = n"
  by (simp add: pow_list_single)

lemma nth_pow_list_single: "i < m \<Longrightarrow> ([a] ^^ m) ! i = a"
  by (simp add: pow_list_single)

lemma pow_list_not_NilD: "xs ^^ m \<noteq> [] \<Longrightarrow> 0 < m"
  by (cases m) auto

lemma length_pow_list:  "length(xs ^^ k) = k * length xs"
  by (induction k) simp+

lemma pow_list_set: "set (w ^^ Suc k) = set w"
  by (induction k)(simp_all)

lemma pow_list_set_if: "set (w ^^ k) = (if k=0 then {} else set w)"
  using pow_list_set[of _ w] by (auto dest: gr0_implies_Suc)

lemma in_pow_list_set[simp]: "x \<in> set (ys ^^ m) \<longleftrightarrow> x \<in> set ys \<and> m \<noteq> 0"
  by (simp add: pow_list_set_if)

lemma pow_list_slide: "xs @ (ys @ xs) ^^ n  @ ys = (xs @ ys)^^(Suc n)"
  by (induction n) simp+

lemma hd_pow_list: "0 < n \<Longrightarrow> hd(xs ^^ n) = hd xs"
  by(auto simp: pow_list_alt hd_append gr0_conv_Suc)

lemma rev_pow_list: "rev (xs ^^ m) = (rev xs) ^^ m"
  by (induction m)(auto simp: pow_list_comm)

lemma eq_pow_list_iff_eq_exp[simp]: assumes "xs \<noteq> []" shows "xs ^^ k = xs ^^ m \<longleftrightarrow> k = m"
proof
  assume "k = m" thus "xs ^^ k = xs ^^ m" by simp
next
  assume "xs ^^ k = xs ^^ m"
  thus "k = m" using \<open>xs \<noteq> []\<close>[folded length_0_conv]
    by (metis length_pow_list mult_cancel2)
qed

lemma pow_list_Nil_iff_0: "xs \<noteq> [] \<Longrightarrow> xs ^^ m = [] \<longleftrightarrow> m = 0"
  by (simp add: pow_list_eq_if)

lemma pow_list_Nil_iff_Nil: "0 < m \<Longrightarrow> xs ^^ m = [] \<longleftrightarrow>  xs = []"
  using pow_list_Nil_iff_0 by fastforce

lemma pow_eq_eq:
  assumes "xs ^^ k = ys ^^ k" and "0 < k"
  shows "(xs::'a list) = ys"
proof-
  have "length xs = length ys"
    using assms(1) length_pow_list by (metis nat_mult_eq_cancel1[OF \<open>0 < k\<close>])
  thus ?thesis by (metis Suc_pred append_eq_append_conv assms(1,2) pow_list.simps(2))
qed

lemma pow_list_eq_appends_iff:
  "n \<ge> m \<Longrightarrow> xs^^n @ ys = xs^^m @ zs \<longleftrightarrow> zs = xs^^(n-m) @ ys"
using pow_list_add[of m "n-m" xs] by auto

lemmas pow_list_eq_appends_iff2 = pow_list_eq_appends_iff[THEN eq_iff_swap]

lemma pow_list_eq_single_appends_iff[simp]:
  "\<lbrakk> x \<notin> set ys; x \<notin> set zs \<rbrakk> \<Longrightarrow> [x]^^m @ ys = [x]^^n @ zs \<longleftrightarrow> m = n \<and> ys = zs"
using append_eq_append_conv_if_disj[of "[x]^^m" "[x]^^n" "ys" "zs"]
by (auto simp: disjoint_iff pow_list_single)

lemma map_pow_list[simp]: "map f (xs ^^ k) = (map f xs) ^^ k"
  by (induction k) simp_all

lemma concat_pow_list: "concat (xs ^^ k) = (concat xs) ^^ k"
  by (induction k) simp_all

lemma concat_pow_list_single[simp]: "concat ([a] ^^ k) = a ^^ k"
  by (simp add: pow_list_alt)

lemma pow_list_single_Nil_iff: "[a] ^^ n = [] \<longleftrightarrow> n = 0"
  by (simp add: pow_list_single)

lemma hd_pow_list_single: "k \<noteq> 0 \<Longrightarrow> hd ([a] ^^ k) = a"
  by (cases k) simp+

lemma index_pow_mod: "i < length(xs ^^ k) \<Longrightarrow> (xs ^^ k)!i = xs!(i mod length xs)"
proof(induction k)
  have aux:  "length(xs ^^ Suc l) = length(xs ^^ l) + length xs" for l
    by simp
  have aux1: "length (xs ^^ l) \<le> i \<Longrightarrow> i < length(xs ^^ l) + length xs \<Longrightarrow>  i mod length xs = i -  length(xs^^l)" for l
    unfolding length_pow_list[of l xs]
     using less_diff_conv2[of "l * length xs" i "length xs", unfolded add.commute[of "length xs"  "l * length xs"]]
       le_add_diff_inverse[of "l*length xs" i]
    by (simp add: mod_nat_eqI)
  case (Suc k)
  show ?case
    unfolding aux sym[OF pow_list_Suc2[symmetric]] nth_append le_mod_geq
    using aux1[ OF _ Suc.prems[unfolded aux]]
      Suc.IH pow_list_Suc2[symmetric] Suc.prems[unfolded aux] leI[of i "length(xs ^^ k)"] by presburger
qed auto

lemma unique_letter_word: assumes "\<And>c. c \<in> set w \<Longrightarrow> c = a" shows "w = [a] ^^ length w"
  using assms proof (induction w)
  case (Cons b w)
  have "[a] ^^ length w = w" using Cons.IH[OF Cons.prems[OF list.set_intros(2)]]..
  then show "b # w = [a] ^^ length(b # w)"
    unfolding Cons.prems[OF list.set_intros(1)] by auto
qed simp

lemma count_list_pow_list: "count_list (w ^^ k) a = k * (count_list w a)"
  by (induction k) simp+

lemma sing_pow_lists: "a \<in> A \<Longrightarrow> [a] ^^ n \<in> lists A"
  by (induction n) auto

lemma one_generated_list_power: "u \<in> lists {x} \<Longrightarrow> \<exists>k. concat u = x ^^ k"
proof(induction u rule: lists.induct)
  case Nil
  then show ?case by (metis concat.simps(1) pow_list.simps(1))
next
  case Cons
  then show ?case by (metis concat.simps(2) pow_list_Suc singletonD)
qed

lemma pow_list_in_lists: "0 < k \<Longrightarrow> u ^^ k \<in> lists B \<Longrightarrow> u \<in> lists B"
by (metis Suc_pred in_lists_conv_set pow_list_set)

text \<open>For code generation. \<close>
(*inspired by Nat.thy*)
context
begin

qualified definition list_pow :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a  list"
  where list_pow_code_def [code_abbrev]: "list_pow = compow"

lemma [code]:
  "list_pow 0 u = []"
  "list_pow (Suc n) u = u @ list_pow n u"
  by (simp_all add: list_pow_code_def)

end

lemma pows_list_comm: "t^^k @ t^^m = t^^m @ t^^k"
  using add.commute pow_list_add by metis

lemma comm_append_pow_list_iff: "u @ v = v @ u \<longleftrightarrow> (\<exists> r k m. u = r^^k \<and> v = r^^m)"
    using  comm_append_are_replicate[of u v, folded pow_list_alt] pows_list_comm by auto

lemma pow_list_comm_comm: assumes "0 < j" and "x^^j = y^^k" shows "x @ y = y @ x"
proof (cases "k = 0")
  assume "k = 0"
  hence "x = []"
    using assms by (simp add: pow_list_Nil_iff_Nil) 
  thus "x @ y = y @ x"
    by force
next
  assume "k \<noteq> 0"
  from this[folded zero_less_iff_neq_zero]
  have popy1 : "y^^k = y @ y^^(k-1)"
    using pow_list_Suc[of "k-1" y, folded Suc_pred'[OF \<open>0 < k\<close>]] by simp
  have popy2 : "y^^k = y^^(k-1)@y"
    using pow_list_Suc2[of "k-1" y, folded Suc_pred'[OF \<open>0 < k\<close>]].  
  have popx1 : "x^^j = x @ x^^(j-1)"
    using pow_list_Suc[of "j-1" x, folded Suc_pred'[OF \<open>0 < j\<close>]].
  have popx2 : "x^^j = x^^(j-1)@x"
    using pow_list_Suc2[of "j-1" x, folded Suc_pred'[OF \<open>0 < j\<close>]].

  have "y @ x @ x^^(j-1) @ y^^(k-1) = y @ x^^j @ y^^(k-1)"
    unfolding popx1 append_assoc..
  also have "... = x^^j @ x^^j"
    unfolding \<open>x^^j = y^^k\<close> using popy1 popy2 by force
  also have "... = x @ y^^k @ x^^(j-1)"
    unfolding \<open>x^^j = y^^k\<close>[symmetric] using popx1 popx2 by force
  also have "... = x @ y @ y^^(k-1) @ x^^(j-1)"
    unfolding popy1 append_assoc..
  finally have "(x @ y) @ y^^(k-1) @ x^^(j-1) = (y @ x) @ x^^(j-1) @ y^^(k-1)"
    unfolding append_assoc by simp
  thus "x @ y = y @ x"
    using append_eq_append_conv[of "x @ y" "y @ x"] by simp
qed
     
lemma comm_common_pow_list_iff: "u @ v = v @ u \<longleftrightarrow> u ^^ length v = v ^^ length u"
proof (cases "v = []")
  assume "v = []"
  thus ?thesis
    using append.left_neutral append.right_neutral list.size(3) pow_list.simps(1) pow_list_Nil by metis  
next
  assume "v \<noteq> []" 
  show ?thesis
  proof
    assume "u @ v = v @ u"
    then obtain r k m where "u = r^^k" "v = r^^m"
      unfolding comm_append_pow_list_iff by blast
    hence "r \<noteq> []"
      using \<open>v \<noteq> []\<close> pow_list_Nil[of m] by blast 
    show "u ^^ length v = v ^^ length u"
      unfolding \<open>u = r^^k\<close> \<open>v = r^^m\<close> length_pow_list pow_list_mult[symmetric] 
      eq_pow_list_iff_eq_exp[OF \<open>r \<noteq> []\<close>] by simp
  next
    assume "u ^^ length v = v ^^ length u"
    show  "u @ v = v @ u"
      by (rule pow_list_comm_comm[OF _ \<open>u ^^ length v = v ^^ length u\<close>]) (use \<open>v \<noteq> []\<close> in blast)
  qed
qed

lemma comm_pows_list_comm: assumes  "0 < k" "0 < m"  
  shows "u ^^ k @ v ^^ m  = v ^^ m @ u ^^ k \<longleftrightarrow> u @ v = v @ u"
proof (cases "v = []")
  assume "v \<noteq> []"
  hence "0 < k * length (v^^m)"
    by (simp add: pow_list_Nil_iff_Nil  \<open>0 < k\<close> \<open>0 < m\<close>) 
  show ?thesis
  proof
    show "u ^^ k @ v ^^ m  = v ^^ m @ u ^^ k \<Longrightarrow> u @ v = v @ u"
      using  pow_list_comm_comm \<open>0 < k * length (v^^m)\<close>
      unfolding comm_common_pow_list_iff pow_list_mult[symmetric] by blast
    show  "u ^^ k @ v ^^ m  = v ^^ m @ u ^^ k" if "u @ v = v @ u"
    proof-
      have "(u ^^ (length v))^^(k*m) =  (v^^(length u))^^(m*k)"
        unfolding \<open>u @ v = v @ u\<close>[unfolded comm_common_pow_list_iff] mult.commute[of k]..
      then show "u ^^ k @ v ^^ m  = v ^^ m @ u ^^ k"   
        unfolding comm_common_pow_list_iff pow_list_mult[symmetric] length_pow_list 
          mult.assoc[symmetric] mult.commute[of _ "length _"].
    qed
  qed
qed simp

lemma rotate1_pow_list_swap: "rotate1 (u ^^ k) = (rotate1 u) ^^ k" 
proof (cases "u = [] \<or> k = 0")
  assume "\<not> (u = [] \<or> k = 0)"
  hence "u^^k \<noteq> []" "u \<noteq> []" "k \<noteq> 0"
    using pow_list_Nil_iff_0[of u k] by blast+ 
  show "rotate1 (u ^^ k) = rotate1 u ^^ k"
    unfolding  rotate1_hd_tl[OF \<open>u \<noteq> []\<close>] rotate1_hd_tl[OF \<open>u^^k \<noteq> []\<close>]
    using \<open>k \<noteq> 0\<close>
  proof (induct k, blast)
    case (Suc k)
    then show ?case 
    proof (cases "k = 0", force)
      assume "k \<noteq> 0"
      show ?case
      proof-
        have "[hd u] @ tl u = u"
          using \<open>u \<noteq> []\<close> by simp
        have "tl (u ^^ Suc k) = tl (u^^k) @ [hd u] @ tl u"
          unfolding pow_list_Suc2 tl_append_if \<open>[hd u] @ tl u = u\<close>
          using \<open>k \<noteq> 0\<close> pow_list_Nil_iff_0[OF \<open>u \<noteq> []\<close>, of k] by force 
        have "hd (u^^k) = hd u" "hd (u^^Suc k) = hd u"
          using \<open>u \<noteq> []\<close> \<open>k \<noteq> 0\<close> hd_pow_list[folded neq0_conv] by blast+  
        show ?case
          using Suc.hyps[OF \<open>k \<noteq> 0\<close>] unfolding \<open>hd (u^^k) = hd u\<close> \<open>hd (u^^Suc k) = hd u\<close>
            \<open>tl (u ^^ Suc k) = tl (u^^k) @ [hd u] @ tl u\<close> append_assoc unfolding pow_list_Suc2 by force
      qed 
    qed
  qed
qed (metis pow_list_Nil pow_list_eq_if rotate1_is_Nil_conv)
   
lemma rotate_pow_list_swap: "rotate n (u ^^ k) = (rotate n u) ^^ k"
  by (induct n, force) (metis rotate_Suc rotate1_pow_list_swap)  

end
