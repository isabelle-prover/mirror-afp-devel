(* 
Author:     Bruno Philipp, TU München
Author:     Tobias Nipkow
*)

section \<open>\<open>a\<^sup>nb\<^sup>nc\<^sup>n\<close> is Not Context-Free\<close>

theory AnBnCn_not_CFL
imports Pumping_Lemma_CFG
begin                           

text \<open>This theory proves that the language @{term "\<Union>n. {[a]^^n @ [b]^^n @ [c]^^n}"}
is not context-free using the Pumping lemma.

The formal proof follows the textbook proof (e.g.\ \<^cite>\<open>HopcroftMU\<close>) closely.
The Isabelle proof is about 10\% of the length of the Coq proof by Ramos \emph{et al.} \<^cite>\<open>RamosAMQ and RamosGithub\<close>.
The latter proof suffers from excessive case analyses.\<close>

declare count_list_pow_list[simp]

context
  fixes a b c
  assumes neq: "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
begin

lemma  c_greater_count0:
  assumes "x@y = [a]^^n @ [b]^^n @ [c]^^n" "length y\<ge>n"
  shows "count_list x c = 0"
  using assms proof -
   have "drop (2*n) (x@y) = [c]^^n" using assms
     by simp
   then have count_c_end: "count_list (drop (2*n) (x@y)) c = n"
     by (simp)
   have "count_list (x@y) c= n" using assms neq
     by (simp)
   then have count_c_front: "count_list (take (2*n) (x@y)) c = 0"
     using count_c_end by (metis add_cancel_left_left append_take_drop_id count_list_append)
   have  "\<exists>i. length y = n+i" using assms
     by presburger
   then obtain i where i: "length y= n+i"
     by blast
   then have "x = take (3*n-n-i) (x@y)"
   proof -
     have "x = take (2 * n - i) x @ take (2 * n - (i + length x)) y"
       using i by (metis add.commute add_diff_cancel_left' append_eq_conv_conj assms(1) diff_diff_left
         length_append length_pow_list_single mult_2 take_append)
     then show ?thesis
       by (simp)
   qed
   then have "x = take (3*n-n-i) (take (3*n-n) (x@y))"
     by (metis diff_le_self min_def take_take)
   then have "x = take (3*n-n-i) (take (2*n) (x@y))" 
     by fastforce  
  then show ?thesis using count_c_front count_list_0_iff in_set_takeD
    by metis
qed

lemma  a_greater_count0:
  assumes "x@y = [a]^^n @ [b]^^n @ [c]^^n" "length x\<ge>n"
  shows "count_list y a = 0"
  text \<open>this prof is easier than @{thm c_greater_count0} since a is at the start of the word rather than at the end \<close>
proof -
  have count_whole: "count_list (x@y) a = n"
    using assms neq by auto
  have take_n: "take n (x@y) = [a]^^n"
    using assms by simp
  then have count_take_n: "count_list (take n (x@y)) a = n"
    by (simp)
  have "\<exists> z. x = take n (x@y) @ z" 
    by (metis append_eq_conv_conj assms(2) nat_le_iff_add take_add)
  then have  count_a_x:"count_list x a = n" using count_take_n take_n count_whole 
    by (metis add_diff_cancel_left' append.right_neutral count_list_append diff_add_zero)
  have "count_list (x@y) a = n"
    using assms neq by simp
   then have "count_list y a = 0"
    using count_a_x by simp
  then show ?thesis
    by presburger
qed

lemma a_or_b_zero:
  assumes "u@w@y = [a]^^n @ [b]^^n @ [c]^^n" "length w \<le> n" (* neq not used *)
  shows "count_list w a = 0 \<or> count_list w c = 0"
  text \<open>This lemma uses @{term "count_list w a = 0 \<or> count_list w c = 0"} similar to all following proofs, focusing on the number of \<open>a\<close> and \<open>c\<close> found in \<open>w\<close> rather than the concrete structure.
        It is also the merge of the two previous lemmas to make the final proof shorter\<close>
proof-
  show ?thesis proof (cases "length u <n")
    case True 
    have "length (u@w@y) = 3*n"  using assms 
      by simp  
    then have "length u + length w + length y = 3*n" 
      by simp
    then have "length u + length y \<ge> 2*n" using assms 
      by linarith
    then have u_or_y: "length u \<ge> n \<or> length y \<ge> n" 
      by linarith
    then  have "length y\<ge>n" using True  
      by simp
    then show ?thesis using c_greater_count0[of "u@w" y n] neq assms 
      by simp
  next
    case False
    then have "length u \<ge> n" 
      by simp
    then show ?thesis using a_greater_count0[of u "w@y" n ] neq assms 
      by auto
  qed
qed

lemma count_vx_not_zero:
  assumes "u@v@w@x@y = [a]^^n @ [b]^^n @ [c]^^n" "v@x \<noteq> []"
  shows "count_list (v@x) a \<noteq> 0 \<or> count_list (v@x) b \<noteq> 0 \<or> count_list (v@x) c \<noteq> 0"
proof -
  have set: "set ([a]^^n @ [b]^^n @ [c]^^n) = {a,b,c}" using assms pow_list_single_Nil_iff
    by (fastforce simp add: pow_list_single)
  show ?thesis proof (cases  "v\<noteq>[]")
    case True
    then have "\<exists>d\<in>set([a]^^n @ [b]^^n @ [c]^^n). count_list v d \<noteq> 0"
      using assms(1)
      by (metis append_Cons count_list_0_iff in_set_conv_decomp list.exhaust list.set_intros(1))
    then have "count_list v a \<noteq> 0 \<or> count_list v b \<noteq> 0 \<or> count_list v c \<noteq>0"
      using set by simp
    then show ?thesis 
      by force
  next
    case False
    then have "x\<noteq>[]" using assms 
      by fast
    then have "\<exists>d\<in>set ([a]^^n @ [b]^^n @ [c]^^n). count_list x d \<noteq> 0"
    proof -
      have "\<exists>d\<in>set ([a] ^^ n) \<union> (set ([b] ^^ n) \<union> set ([c] ^^ n)). ya \<noteq> d \<longrightarrow> 0 < count_list ys d"
        if "u @ v @ w @ ya # ys @ y = [a] ^^ n @ [b] ^^ n @ [c] ^^ n"
          and "x = ya # ys"
        for ya :: 'a
          and ys :: "'a list"
        using that by (metis Un_iff in_set_conv_decomp set_append)
      then show ?thesis
        using assms(1) \<open>x \<noteq> []\<close> by (auto simp: neq_Nil_conv)
    qed
    then have "count_list x a \<noteq> 0 \<or> count_list x b \<noteq> 0 \<or> count_list x c \<noteq> 0"
       using set by simp
    then show ?thesis 
       by force
   qed
qed

lemma not_ex_y_count:
  assumes "i\<noteq>k \<or> k\<noteq>j \<or> i\<noteq>j" "count_list w a = i" "count_list w b = k" "count_list w c = j"
  shows "\<not>(EX y. w = [a]^^y @ [b]^^y @ [c]^^y)"
 proof 
   assume "EX y. w = [a]^^y @ [b]^^y @ [c]^^y"
   then obtain y where y: "w = [a]^^y @ [b]^^y @ [c]^^y" 
     by blast
   then have "count_list w a = y" using neq 
     by simp
   then have i_eq_y: "i=y" using assms 
     by argo
   then have "count_list w b = y"
     using neq assms(2) y by (auto)
   then have k_eq_y: "k=y" using assms 
     by argo
   have "count_list w c = y" using neq y
     by simp
   then have j_eq_y: "j=y" using assms  
     by argo
   show False  using i_eq_y k_eq_y j_eq_y assms 
      by presburger
 qed

lemma not_in_count:
  assumes (* no neq *) "count_list w a \<noteq> count_list w b \<or> count_list w b \<noteq> count_list w c \<or> count_list w c \<noteq> count_list w a"
  shows "w \<notin> {word. \<exists> n.  word = [a]^^n @ [b]^^n @ [c]^^n}"
  text \<open>This definition of a word not in the language is useful as it allows us to prove a word is not in the language just by knowing the number of each letter in a word\<close>
  using assms not_ex_y_count
  by (smt (verit, del_insts) mem_Collect_eq)

text \<open>This is the central and only case analysis, which follows the textbook proofs.
The Coq proof by Ramos is considerably more involved and ends up with a total of 24 cases\<close>

lemma pumping_application:
  assumes "u@v@w@x@y = [a]^^n @ [b]^^n @ [c]^^n"
  and "count_list (v@w@x) a = 0 \<or> count_list (v@w@x) c = 0" and "v@x\<noteq>[]"
  shows "u@w@y \<notin> (\<Union>n. {[a]^^n @ [b]^^n @ [c]^^n})"
  text \<open>In this lemma it is proven that a word @{term "u @ v^^0 @ w @ x^^0 @ y"}
        is not in the language @{term "\<Union>n. {[a]^^n @ [b]^^n @ [c]^^n}"}
        as this is the easiest counterexample useful for the Pumping lemma\<close>
proof-
  have count_word_a: "count_list (u@v@w@x@y) a = n"
    using neq assms(1) by simp
  have count_word_b: "count_list (u@v@w@x@y) b = n"
    using neq assms(1) by simp
  have count_word_c: "count_list (u@v@w@x@y) c = n"
    using neq assms(1) by simp
  have count_non_zero: "((count_list (v@x) a) \<noteq>0) \<or> (count_list (v@x) b\<noteq>0) \<or> (count_list (v@x) c \<noteq> 0)"
    using count_vx_not_zero[of u v w x y n] assms(1,3) by simp  
  from assms(2) show ?thesis proof
    assume *: "count_list (v @ w @ x) a = 0"
    then have vx_b_or_c_not0: "count_list (v@x) b \<noteq> 0 \<or> count_list (v@x) c \<noteq> 0" using count_non_zero
      by simp
    have uwy_count_a: "count_list (u@w@y) a = n" using * count_word_a 
      by simp 
    have "count_list (u@w@y) b \<noteq> n \<or> count_list (u@w@y) c \<noteq> n" using vx_b_or_c_not0 count_word_b count_word_c 
      by auto
    then have "(count_list (u@w@y) a \<noteq> count_list (u@w@y) b) \<or> (count_list (u@w@y) c \<noteq> count_list (u@w@y) a)" using uwy_count_a
      by argo
    then show ?thesis using not_in_count[of "u@w@y"] 
      by blast
  next
    assume *: "count_list (v @ w @ x) c = 0"
    then have vx_a_or_b_not0: "(count_list (v@x) a\<noteq>0) \<or> (count_list (v@x) b \<noteq> 0)" using count_non_zero
      by fastforce
    have uwy_count_c: "count_list (u@w@y) c=n" using * count_word_c 
      by auto 
    have "count_list (u@w@y) a \<noteq>n \<or> count_list (u@w@y) b \<noteq>n" using vx_a_or_b_not0 count_word_a count_word_b
      by force
    then have "(count_list (u@w@y) a \<noteq> count_list (u@w@y) b) \<or> (count_list (u@w@y) c \<noteq> count_list (u@w@y) a)" using uwy_count_c
      by argo
    then show ?thesis using not_in_count[of "u@w@y"] 
      by blast  
  qed
qed

theorem anbncn_not_cfl:
  assumes "finite (P :: ('n::infinite,'a)Prods)"
  shows "Lang P S \<noteq> (\<Union>n. {[a]^^n @ [b]^^n @ [c]^^n})" (is "\<not> ?E")
proof
  assume "?E"
  from Pumping_Lemma[OF \<open>finite P\<close>, of S] obtain n where
    pump: "\<forall>word \<in> Lang P S. length word \<ge> n \<longrightarrow>
     (\<exists>u v w x y. word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v^^i)@w@(x^^i)@y \<in> Lang P S))" 
    by blast
  let ?word = "[a]^^n @ [b]^^n @ [c]^^n"
  have wInLg: "?word \<in> Lang P S"
    using \<open>?E\<close> by blast
  have "length ?word \<ge> n"
    by simp
  then obtain u v w x y where uvwxy: "?word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v^^i)@w@(x^^i)@y \<in> Lang P S)"
    using pump wInLg by metis
  let ?vwx= "v@w@x"
  have "(count_list ?vwx  a=0 ) \<or> (count_list ?vwx c=0)" using  uvwxy a_or_b_zero assms 
    by (metis (no_types, lifting) append.assoc)
  then show False using assms uvwxy pumping_application[of u v w x y n]
    by (metis \<open>?E\<close> append_Nil length_0_conv not_one_le_zero pow_list.simps(1))
qed

end

end
