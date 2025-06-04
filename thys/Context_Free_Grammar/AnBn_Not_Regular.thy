(*
Authors: Kaan Taskin, Tobias Nipkow
*)

section \<open>\<open>a\<^sup>nb\<^sup>n\<close> is Not Regular\<close>

theory AnBn_Not_Regular
imports Pumping_Lemma_Regular
begin

(* TODO:rm after next release *)

lemma pow_list_set_if: "set (w ^^ k) = (if k=0 then {} else set w)"
  using pow_list_set[of _ w] by (auto dest: gr0_implies_Suc)
lemma in_pow_list_set[simp]: "x \<in> set (ys ^^ m) \<longleftrightarrow> x \<in> set ys \<and> m \<noteq> 0"
  by (simp add: pow_list_set_if)
lemma pow_list_eq_appends_iff:
  "n \<ge> m \<Longrightarrow> x^^n @ y = x^^m @ z \<longleftrightarrow> z = x^^(n-m) @ y"
  using pow_list_add[of m "n-m" x] by auto
lemma append_eq_append_conv_if_disj:
  "(set xs \<union> set xs') \<inter> (set ys \<union> set ys') = {}
  \<Longrightarrow>  xs @ ys = xs' @ ys' \<longleftrightarrow> xs = xs' \<and> ys = ys'"
by (auto simp: all_conj_distrib disjoint_iff append_eq_append_conv2)
lemma pow_list_eq_single_appends_iff[simp]:
  "\<lbrakk> x \<notin> set ys; x \<notin> set zs \<rbrakk> \<Longrightarrow> [x]^^m @ ys = [x]^^n @ zs \<longleftrightarrow> m = n \<and> ys = zs"
using append_eq_append_conv_if_disj[of "[x]^^m" "[x]^^n" "ys" "zs"]
by (auto simp: disjoint_iff pow_list_single)

text
\<open>The following theorem proves that the language \<open>a^nb^n\<close> cannot be produced by a right linear production set, using the contrapositive form 
 of the pumping lemma\<close>

theorem not_rlin2_ab:
  assumes "a \<noteq> b"
      and "Lang P A = (\<Union>n. {[a]^^n @ [b]^^n})" (is "_ = ?AnBn")
      and "finite P"
    shows "\<not>rlin2 P"
proof -
  have "\<exists>w \<in> Lang P A. length w \<ge> n \<and> (\<forall>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<longrightarrow> (\<exists>i. x@(y^^i)@z \<notin> Lang P A))" for n
  proof -
    let ?anbn = "[a]^^n @ [b]^^n"
    show ?thesis
    proof
      have **: "(\<exists>i. x @ (y^^i) @ z \<notin> Lang P A)"
        if asm: "?anbn = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n" for x y z
      proof
        from asm have asm1: "[a]^^n @ [b]^^n = x @ y @ z" by blast
        from asm have asm2: "1 \<le> length y" by blast
        from asm have asm3: "length (x @ y) \<le> n" by blast
        let ?kx = "length x" let ?ky = "length y"
        have splitted: "x = [a]^^?kx \<and> y = [a]^^?ky \<and> z = [a]^^(n - ?kx - ?ky) @ [b]^^n"
        proof -
          have "\<forall>i < n. ([a]^^n @ [b]^^n)!i = a"
            by (simp add: nth_append nth_pow_list_single)
          with asm1 have xyz_tma: "\<forall>i < n. (x@y@z)!i = a" by metis
          with asm3 have xy_tma: "\<forall>i < length(x@y). (x@y)!i = a"
            by (metis append_assoc nth_append order_less_le_trans)
          from xy_tma have "\<forall>i < ?kx. x!i = a"
            by (metis le_add1 length_append nth_append order_less_le_trans)
          hence *: "x = [a]^^?kx"
            by (simp add: list_eq_iff_nth_eq nth_pow_list_single)
          from xy_tma have "\<forall>i < ?ky. y!i = a"
            by (metis length_append nat_add_left_cancel_less nth_append_length_plus)
          hence **: "y = [a]^^?ky"
            by (simp add: nth_equalityI pow_list_single)
          from * ** asm1 have "[a]^^n @ [b]^^n = [a]^^?kx @ [a]^^?ky @ z" by simp
          hence z_rest: "[a]^^n @ [b]^^n = [a]^^(?kx+?ky) @ z"
            by (simp add: pow_list_add)
          from asm3 have ***: "z = [a]^^(n-?kx-?ky) @ [b]^^n" 
            using pow_list_eq_appends_iff[THEN iffD1, OF _ z_rest] by simp
          from * ** *** show ?thesis by blast
        qed
        from splitted have "x @ y^^2 @ z = [a]^^?kx @ ([a]^^?ky)^^2 @ [a]^^(n - ?kx - ?ky) @ [b]^^n" by simp
        also have "... = [a]^^?kx @ [a]^^(?ky*2) @ [a]^^(n - ?kx - ?ky) @ [b]^^n"
          by (simp add: pow_list_mult)
        also have "... = [a]^^(?kx + ?ky*2 + (n - ?kx - ?ky)) @ [b]^^n"
          by (simp add: pow_list_add)
        also from asm3 have "... = [a]^^(n+?ky) @ [b]^^n"
          by (simp add: add.commute)
        finally have wit: "x @ y^^2 @ z = [a]^^(n+?ky) @ [b]^^n" .
        from asm2 have "[a]^^(n + ?ky) @ [b]^^n \<notin> ?AnBn" 
          using \<open>a\<noteq>b\<close> by auto
        with wit have "x @ y^^2 @ z \<notin> ?AnBn" by simp
        thus "x @ y^^2 @ z \<notin> Lang P A" using assms(2) by blast
      qed
      from ** show "n \<le> length ?anbn \<and> (\<forall>x y z. ?anbn = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n \<longrightarrow> (\<exists>i. x @ (y^^i) @ z \<notin> Lang P A))" by simp
    next
      have "?anbn \<in> ?AnBn" by blast
      thus "?anbn \<in> Lang P A" 
        by (simp add: assms(2)) 
    qed
  qed
  thus ?thesis 
    using pumping_lemma_regular_contr[OF assms(3)] by blast
qed

end