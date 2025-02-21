section \<open> Key algorithms for WEST \<close>

theory Regex_Equivalence

imports WEST_Algorithms WEST_Proofs

begin

fun depth_dataype_list:: "state_regex \<Rightarrow> nat"
  where "depth_dataype_list [] = 0"
  | "depth_dataype_list (One#T) = 1 + depth_dataype_list T"
  | "depth_dataype_list (Zero#T) = 1 + depth_dataype_list T"
  | "depth_dataype_list (S#T) = 2 + 2*(depth_dataype_list T)"


function enumerate_list:: "state_regex \<Rightarrow> trace_regex"
  where "enumerate_list [] = [[]]"
  | "enumerate_list (One#T) =  (map (\<lambda>x. One#x) (enumerate_list T))"
  | "enumerate_list (Zero#T) =  (map (\<lambda>x. Zero#x) (enumerate_list T))"
  | "enumerate_list (S#T) =  (enumerate_list (Zero#T))@(enumerate_list (One#T))"
  apply (metis WEST_and_bitwise.elims list.exhaust)
  by simp_all
termination  apply (relation "measure (\<lambda>L. depth_dataype_list L)")
  by simp_all



fun flatten_list:: "'a list list \<Rightarrow> 'a list"
  where "flatten_list L = foldr (@) L []"

value "flatten_list [[12, 13::nat], [15]]"

value "flatten_list (let enumerate_H = enumerate_list [S, One] in
let enumerate_T = [[]] in
map (\<lambda>t. (map (\<lambda>h. h#t) enumerate_H)) enumerate_T)"


fun enumerate_trace:: "trace_regex \<Rightarrow> WEST_regex"
  where "enumerate_trace [] = [[]]"
  | "enumerate_trace (H#T) = flatten_list
  (let enumerate_H = enumerate_list H in
   let enumerate_T = enumerate_trace T in
   map (\<lambda>t. (map (\<lambda>h. h#t) enumerate_H)) enumerate_T)"

value "enumerate_trace [[S, One], [S], [One]]"
value "enumerate_trace [[]]"

fun enumerate_sets:: "WEST_regex \<Rightarrow> trace_regex set"
  where "enumerate_sets [] = {}"
  | "enumerate_sets (h#T) = (set (enumerate_trace h)) \<union> (enumerate_sets T)"

fun naive_equivalence:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow> bool"
  where "naive_equivalence A B = (A = B \<or> (enumerate_sets A) = (enumerate_sets B))"


section \<open> Regex Equivalence Correctness \<close>

lemma enumerate_list_len_alt:
  shows "\<forall> state \<in> set (enumerate_list state_regex).
         length state = length state_regex"
proof(induct state_regex)
  case Nil
  then show ?case by simp
next
  case (Cons a state_regex)
  {assume zero: "a = Zero"
    then have "\<forall> state \<in> set (enumerate_list state_regex).
         length state = length state_regex"
      using Cons by blast
    then have ?case unfolding zero
      by simp
  } moreover {
    assume one: "a = One"
    then have "\<forall> state \<in> set (enumerate_list state_regex).
         length state = length state_regex"
      using Cons by blast
    then have ?case unfolding one
      by simp
  } moreover {
    assume s: "a = S"
    then have "\<forall> state \<in> set (enumerate_list state_regex).
         length state = length state_regex"
      using Cons by blast
    then have ?case unfolding s by auto
  }
  ultimately show ?case
    using WEST_bit.exhaust by blast
qed


lemma enumerate_list_len:
  assumes "state \<in> set (enumerate_list state_regex)"
  shows "length state = length state_regex"
  using assms enumerate_list_len_alt by blast


lemma enumerate_list_prop:
  assumes "(\<And>k. List.member j k \<Longrightarrow> k \<noteq> S)"
  shows "enumerate_list j = [j]"
  using assms
proof (induct j)
  case Nil
  then show ?case by auto
next
  case (Cons h t)
  then have elt: "enumerate_list t = [t]"
    by (simp add: member_rec(1))
  then have "h = One \<or> h = Zero"
    using Cons
    by (meson WEST_bit.exhaust member_rec(1))
  then show ?case using enumerate_list.simps(2-3) elt
    by fastforce
qed


lemma enumerate_fixed_trace:
  fixes h1:: "trace_regex"
  assumes "\<And>j. List.member h1 j \<Longrightarrow> (\<And>k. List.member j k \<Longrightarrow> k \<noteq> S)"
  shows "(enumerate_trace h1) = [h1]"
  using assms
proof (induct h1)
  case Nil
  then show ?case by auto
next
  case (Cons h t)
  then have ind: "enumerate_trace t = [t]"
    by (meson member_rec(1))
  have "enumerate_list h = [h]"
    using enumerate_list_prop Cons
    by (meson member_rec(1))
  then show ?case
    using Cons ind unfolding enumerate_trace.simps
    by auto
qed

text \<open> If we have two state regexs that don't contain S's,
   then enumerate trace on each is different. \<close>
lemma enum_trace_prop:
  fixes h1 h2:: "trace_regex"
  assumes "\<And>j. List.member h1 j \<Longrightarrow> (\<And>k. List.member j k \<Longrightarrow> k \<noteq> S)"
  assumes "\<And>j. List.member h2 j \<Longrightarrow> (\<And>k. List.member j k \<Longrightarrow> k \<noteq> S)"
  assumes "(set h1) \<noteq> (set h2)"
  shows "set (enumerate_trace h1) \<noteq> set (enumerate_trace h2)"
  using enumerate_fixed_trace[of h1] enumerate_fixed_trace[of h2] assms
  by auto

lemma enumerate_list_tail_in:
  assumes "head_t#tail_t \<in> set (enumerate_list (h#trace))"
  shows "tail_t \<in> set (enumerate_list trace)"
proof-
  {assume one: "h = One"
    have ?thesis
      using assms unfolding one enumerate_list.simps by auto
  } moreover {
    assume zero: "h = Zero"
    have ?thesis
      using assms unfolding zero enumerate_list.simps by auto
  } moreover {
    assume s: "h = S"
    have ?thesis
      using assms unfolding s enumerate_list.simps by auto
  }
  ultimately show ?thesis using WEST_bit.exhaust by blast
qed

lemma enumerate_list_fixed:
  assumes "t \<in> set (enumerate_list trace)"
  shows "(\<forall>k. List.member t k \<longrightarrow> k \<noteq> S)"
  using assms
proof (induct trace arbitrary: t)
  case Nil
  then show ?case using member_rec(2) by force
next
  case (Cons h trace)
  obtain head_t tail_t where obt: "t = head_t#tail_t"
    using Cons.prems enumerate_list_len
    by (metis length_0_conv neq_Nil_conv)
  have "tail_t \<in> set (enumerate_list trace)"
    using enumerate_list.simps obt Cons.prems enumerate_list_tail_in by blast
  then have hyp: "\<forall>k. List.member tail_t k \<longrightarrow> k \<noteq> S"
    using Cons.hyps(1)[of tail_t] by auto
  {assume one: "h = One"
    then have "head_t = One"
      using obt Cons.prems unfolding enumerate_list.simps by auto
    then have ?case
      using hyp obt
      by (simp add: member_rec(1))
  } moreover {
    assume zero: "h = Zero"
    then have "head_t = Zero"
      using obt Cons.prems unfolding enumerate_list.simps by auto
    then have ?case
      using hyp obt
      by (simp add: member_rec(1))
  } moreover {
    assume s: "h = S"
    then have "head_t = Zero \<or> head_t = One"
      using obt Cons.prems unfolding enumerate_list.simps by auto
    then have ?case
      using hyp obt
      by (metis calculation(1) calculation(2) member_rec(1) s)
  }
  ultimately show ?case using WEST_bit.exhaust by blast
qed


lemma map_enum_list_nonempty:
  fixes t::"WEST_bit list list"
  fixes head::"WEST_bit list"
  shows "map (\<lambda>h. h # t) (enumerate_list head) \<noteq> []"
proof(induct head arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a head)
  {assume a: "a = One"
    then have ?case unfolding a enumerate_list.simps
      using Cons by auto
  } moreover {
    assume a: "a = Zero"
    then have ?case unfolding a enumerate_list.simps
      using Cons by auto
  } moreover {
    assume a: "a = S"
    then have ?case unfolding a enumerate_list.simps
      using Cons by auto
  }
  ultimately show ?case using WEST_bit.exhaust by blast
qed



lemma length_of_flatten_list:
assumes "flat =
  foldr (@)
   (map (\<lambda>t. map (\<lambda>h. h # t) H) T) []"
shows " length flat = length T * length H"
  using assms
proof (induct T arbitrary: flat)
  case Nil
  then show ?case by auto
next
  case (Cons t1 T2)
  then have "flat = foldr (@)
     (map (\<lambda>t. map (\<lambda>h. h # t) H) (t1 # T2)) []"
    by auto
  then have "flat = foldr (@)
    (map (\<lambda>h. h # t1) H #(map (\<lambda>t. map (\<lambda>h. h # t) H) T2)) []"
    by auto
  then have "flat = map (\<lambda>h. h # t1) H @ (foldr (@) (map (\<lambda>t. map (\<lambda>h. h # t) H) T2)) []"
    by simp
  then have "length flat = length H + length (T2) * length H"
    using Cons by auto
  then show ?case by simp
qed


lemma flatten_list_idx:
  assumes "flat = flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) head) tail)"
  assumes "i < length tail"
  assumes "j < length head"
  shows "(head!j)#(tail!i) = flat!(i*(length head) + j) \<and> i*(length head) + j < length flat"
  using assms
proof(induct tail arbitrary: head i j flat)
  case Nil
  then show ?case
    by auto
next
  case (Cons a tail)
  let ?flat = "flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) head) tail)"
  have cond1: "?flat = ?flat" by auto
  have equiv: "(map (\<lambda>t. map (\<lambda>h. h # t) head) (a # tail)) =
      (map (\<lambda>h. h # a) head) # (map (\<lambda>t. map (\<lambda>h. h # t) head) tail)"
      by auto
  then have flat_is: "flat = (map (\<lambda>h. h # a) head) @ flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) head) tail)"
    using Cons(2) unfolding flatten_list.simps by simp

  {assume i0: "i = 0"
    then have bound: "i * length head + j < length flat"
      using Cons by simp
     have "length (map (\<lambda>h. h # a) head) > j"
      using Cons(4) by auto
    then have "(map (\<lambda>h. h # a) head) ! j = flat ! j"
      using flat_is
      by (simp add: nth_append)
    then have "(head ! j)#a  = flat ! j"
      using Cons(4) by simp
    then have "head ! j # (a # tail) ! i = flat ! (i * length head + j)"
      unfolding i0 by simp
    then have ?case using bound by auto
  } moreover {
    assume i_ge_0: "i > 0"
    have len_flat: "length flat = length head * length (a # tail)"
     using Cons(3-4) length_of_flatten_list[of flat head "a#tail"]
      Cons(2) unfolding flatten_list.simps
     by simp
   have "i * length head \<le> (length (a # tail) - 1)*length head"
     using Cons(3) by auto
   then have "i * length head \<le> (length (a # tail))*length head - length head"
     by auto
   then have "i * length head + j < (length (a # tail))*length head - length head + length head"
     using Cons(4) by linarith
   then have "i * length head + j < (length (a # tail))*length head"
     by auto
    then have bound: "i * length head + j < length flat"
      using len_flat
      by (simp add: mult.commute)
    have i_minus: " i - 1 < length tail"
      using i_ge_0 Cons(3)
      by auto
    have "flat ! (i * length head + j) = flat ! ((i-1) * length head + j + length head)"
      using i_ge_0
      by (smt (z3) add.commute bot_nat_0.not_eq_extremum group_cancel.add1 mult_eq_if)
    then have "flat ! (i * length head + j) = flatten_list
     (map (\<lambda>t. map (\<lambda>h. h # t) head) tail) !
    ((i - 1) * length head + j)"
      using flat_is
      by (smt (verit, ccfv_threshold) add.commute length_map nth_append_length_plus)
    then have  "flat ! (i * length head + j) = head ! j # tail ! (i - 1)"
          using Cons.hyps[OF cond1 i_minus Cons(4)]
          by argo
    then have access: "head ! j # (a # tail) ! i =
    flat ! (i * length head + j)"
      using i_ge_0
      by simp
    have ?case
      using bound access
      by auto
  }
  ultimately show ?case by blast
qed


lemma flatten_list_shape:
  assumes "List.member flat x1"
  assumes "flat = flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) H) T)"
  shows "\<exists> x1_head x1_tail. x1 = x1_head#x1_tail \<and> List.member H x1_head \<and> List.member T x1_tail"
  using assms
proof(induction T arbitrary: flat H)
  case Nil
  have "flat = (flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) H) []))"
    using Nil(1) unfolding Nil by blast
  then have "flat = []"
    by simp
  then show ?case
    using Nil
    by (simp add: member_rec(2))
next
  case (Cons a T)
  have "\<exists>k. x1 = flat ! k \<and> k < length flat"
     using Cons(2)
     by (metis in_set_conv_nth member_def)
  then obtain k where k_is: "x1 = flat ! k \<and> k < length flat"
    by auto
  have len_flat: "length flat = (length (a#T)*length H)"
    using Cons(3) length_of_flatten_list
    by auto
  let ?j = "k mod (length H)"
  have "\<exists>i . k = (i*(length H)+?j)"
    by (meson mod_div_decomp)
  then obtain i where i_is: "k = (i*(length H)+?j)"
    by auto
  then have i_lt: "i < length (a#T)"
    using len_flat k_is
    by (metis add_lessD1 mult_less_cancel2)
  have j_lt: "?j < length H"
    by (metis k_is len_flat length_0_conv length_greater_0_conv mod_by_0 mod_less_divisor mult_0_right)
  have "\<exists>i < length (a # T). k = (i*(length H)+?j)"
    using i_is i_lt by blast
  then have "\<exists>i < length (a # T). \<exists>j < length H. k = (i*(length H)+j)"
    using j_lt by blast
  then obtain i j where ij_props: "i < length (a#T)" "j < length H" "k = (i*(length H)+j)"
    by blast
  then have "flat ! k =  H ! j # (a # T) ! i"
    using flatten_list_idx[OF Cons(3) ij_props(1) ij_props(2) ]
      Cons(2) k_is ij_props(3)
    by argo
  then obtain x1_head x1_tail where "x1 = x1_head#x1_tail"
  and "List.member H x1_head" and "List.member (a#T) x1_tail"
    using ij_props
    by (simp add: index_of_L_in_L k_is)
  then show ?case
    using Cons(3) by simp
qed


lemma flatten_list_len:
  assumes "\<And>t. List.member T t \<Longrightarrow> length t = n"
  assumes "flat = flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) H) T)"
  shows "\<And>x1. List.member flat x1 \<Longrightarrow> length x1 = n+1"
  using assms
proof(induction T arbitrary: flat n H)
  case Nil
  have "flat = (flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) H) []))"
    using Nil(1) unfolding Nil(3) by blast
  then have "flat = []"
    by simp
  then show ?case
    using Nil by (simp add: member_rec(2))
next
  case (Cons a T)
  have "\<exists>k. x1 = flat ! k \<and> k < length flat"
     using Cons(2)
     by (metis in_set_conv_nth member_def)
  then obtain k where k_is: "x1 = flat ! k \<and> k < length flat"
    by auto
  have len_flat: "length flat = (length (a#T)*length H)"
    using Cons(4) length_of_flatten_list
    by auto
  let ?j = "k mod (length H)"
  have "\<exists>i . k = (i*(length H)+?j)"
    by (meson mod_div_decomp)
  then obtain i where i_is: "k = (i*(length H)+?j)"
    by auto
  then have i_lt: "i < length (a#T)"
    using len_flat k_is
    by (metis add_lessD1 mult_less_cancel2)
  have j_lt: "?j < length H"
    by (metis k_is len_flat length_0_conv length_greater_0_conv mod_by_0 mod_less_divisor mult_0_right)
  have "\<exists>i < length (a # T). k = (i*(length H)+?j)"
    using i_is i_lt by blast
  then have "\<exists>i < length (a # T). \<exists>j < length H. k = (i*(length H)+j)"
    using j_lt by blast
  then obtain i j where ij_props: "i < length (a#T)" "j < length H" "k = (i*(length H)+j)"
    by blast
  then have "flat ! k =  H ! j # (a # T) ! i"
    using flatten_list_idx[OF Cons(4) ij_props(1) ij_props(2) ]
      Cons(2) k_is ij_props(3)
    by argo
  then obtain x1_head x1_tail where "x1 = x1_head#x1_tail"
  and "List.member H x1_head" and "List.member (a#T) x1_tail"
    using ij_props
    by (simp add: index_of_L_in_L k_is)
  then show ?case
    using Cons(3) by simp
qed


lemma flatten_list_lemma:
  assumes "\<And>x1. List.member to_flatten x1 \<Longrightarrow> (\<And>x2. List.member x1 x2 \<Longrightarrow> length x2 = length trace)"
  assumes "a \<in> set (flatten_list to_flatten)"
  shows "length a = length trace"
  using assms proof (induct to_flatten)
  case Nil
  then show ?case by auto
next
  case (Cons h t)
   have a_in: "a \<in> set h \<or> a \<in> set (flatten_list t)"
     using Cons(3) unfolding flatten_list.simps foldr_def by simp
  {assume *: "a \<in> set h"
    then have ?case
      using Cons(2)[of h]
      by (simp add: in_set_member member_rec(1))
  } moreover {assume *: "a \<in> set (flatten_list t)"
    have ind_h_setup: "(\<And>x1 x2. List.member t x1 \<Longrightarrow> List.member x1 x2 \<Longrightarrow>
        length x2 = length trace)"
      using Cons(2) by (meson member_rec(1))
    have " a \<in> set (flatten_list t) \<Longrightarrow> length a = length trace"
      using Cons(1) ind_h_setup
      by auto
    then have ?case
      using * by auto
  }
  ultimately show ?case
    using a_in by blast
qed


lemma enumerate_trace_len:
  assumes "a \<in> set (enumerate_trace trace)"
  shows "length a = length trace"
  using assms
proof(induct "length trace" arbitrary: trace a)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain h t where trace_is: "trace = h#t"
    by (meson Suc_length_conv)
  obtain i where "(enumerate_trace trace)!i = a"
    using Suc.prems
    by (meson in_set_conv_nth)
  let ?enumerate_H = "enumerate_list h"
  let ?enumerate_t = "enumerate_trace t"
  have enum_tr_is: "enumerate_trace trace =
      flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) ?enumerate_H) ?enumerate_t)"
    using trace_is by auto
  let ?to_flatten = "map (\<lambda>t. map (\<lambda>h. h # t) ?enumerate_H) ?enumerate_t"

  have all_w: "(\<And>w. List.member (enumerate_trace t) w \<Longrightarrow> length w = length t)"
    using Suc(1)[of t] Suc(2) trace_is
    by (simp add: in_set_member)
  have a_mem: "List.member (enumerate_trace trace) a"
    using Suc(3) in_set_member by fast
  show ?case
    using flatten_list_len[OF _ enum_tr_is a_mem, of "length t"] all_w
    trace_is by simp
qed

definition regex_zeros_and_ones:: "trace_regex \<Rightarrow> bool"
  where "regex_zeros_and_ones tr =
    (\<forall>j. List.member tr j \<longrightarrow> (\<forall>k. List.member j k \<longrightarrow> k \<noteq> S))"


lemma match_enumerate_state_aux_first_bit:
  assumes "a_head = Zero \<or> a_head = One"
  assumes "a_head # a_tail \<in> set (enumerate_list (h_head # h))"
  shows "h_head = a_head \<or> h_head = S"
proof-
  {assume h_head: "h_head = One"
    then have ?thesis
      using assms unfolding h_head enumerate_list.simps by auto
  } moreover {
    assume h_head: "h_head = Zero"
    then have ?thesis
      using assms unfolding h_head enumerate_list.simps by auto
  } moreover {
    assume "h_head = S"
    then have ?thesis by auto
  }
  ultimately show ?thesis using WEST_bit.exhaust by blast
qed

lemma advance_state_iff:
  assumes "x > 0"
  shows "x \<in> state \<longleftrightarrow> (x-1) \<in> advance_state state"
proof-
  have forward: "x \<in> state \<longrightarrow> (x-1) \<in> advance_state state"
    using assms by auto
  have converse: "(x-1) \<in> advance_state state \<longrightarrow> x \<in> state"
    unfolding advance_state.simps using assms
    by (smt (verit, best) Suc_diff_1 diff_0_eq_0 diff_Suc_1' diff_self_eq_0 less_one mem_Collect_eq nat.distinct(1) not0_implies_Suc not_gr_zero old.nat.exhaust)
  show ?thesis using forward converse by blast
qed

lemma match_enumerate_state_aux:
  assumes "a \<in> set (enumerate_list h)"
  assumes "match_timestep state a"
  shows "match_timestep state h"
  using assms
proof(induct h arbitrary: state a)
  case Nil
  have "a = []"
    using Nil by auto
  then show ?case using Nil by blast
next
  case (Cons h_head h)
  then obtain a_head a_tail where obt: "a = a_head#a_tail"
    using enumerate_list_len Cons
    by (metis length_0_conv list.exhaust)
  let ?adv_state = "advance_state state"
  {assume in_state: "0 \<in> state"
    then have "a_head = One"
      using Cons.prems(2) unfolding obt match_timestep_def
      using enumerate_list_fixed
      by (metis WEST_bit.exhaust Cons(2) length_pos_if_in_set list.set_intros(1) member_rec(1) nth_Cons_0 obt)
    then have h_head: "h_head = One \<or> h_head = S"
      using Cons.prems(1) unfolding obt
      using match_enumerate_state_aux_first_bit by blast
    have match_adv: "match_timestep (advance_state state) h"
      using Cons.hyps[of a_tail ?adv_state]
      using Cons.prems(1) Cons.prems(2) advance_state_match_timestep enumerate_list_tail_in obt by blast
    have "\<And>x. x<length (h_head # h) \<Longrightarrow>
       ((h_head # h) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((h_head # h) ! x = Zero \<longrightarrow> x \<notin> state)"
    proof-
      fix x
      assume x: "x<length (h_head # h)"
      let ?thesis = "((h_head # h) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((h_head # h) ! x = Zero \<longrightarrow> x \<notin> state)"
      {assume x0: "x = 0"
        then have ?thesis unfolding x0 using h_head in_state by auto
      } moreover {
        assume x_ge_0: "x > 0"
        then have "x-1 < length h"
          using x by simp
        then have *:"(h ! (x-1) = One \<longrightarrow> (x-1) \<in> advance_state state) \<and>
                   (h ! (x-1) = Zero \<longrightarrow> (x-1) \<notin> advance_state state)"
          using match_adv unfolding match_timestep_def by blast
        have "h ! (x-1) = (h_head # h) ! x" using x_ge_0 by auto
        then have *: "((h_head # h) ! x = One \<longrightarrow> (x-1) \<in> advance_state state) \<and>
                   ((h_head # h) ! x = Zero \<longrightarrow> (x-1) \<notin> advance_state state)"
          using * by argo
        then have ?thesis using advance_state_iff x_ge_0 by blast
      }
      ultimately show ?thesis by blast
    qed
    then have ?case
      using h_head unfolding match_timestep_def by blast
  } moreover {
    assume not_in: "0 \<notin> state"
    then have "a_head = Zero"
      using Cons.prems(2) unfolding obt match_timestep_def
      using enumerate_list_fixed
      by (metis WEST_bit.exhaust Cons(2) length_pos_if_in_set list.set_intros(1) member_rec(1) nth_Cons_0 obt)
    then have h_head: "h_head = Zero \<or> h_head = S"
      using Cons.prems(1) unfolding obt
      using match_enumerate_state_aux_first_bit by blast
    have match_adv: "match_timestep (advance_state state) h"
      using Cons.hyps[of a_tail ?adv_state]
      using Cons.prems(1) Cons.prems(2) advance_state_match_timestep enumerate_list_tail_in obt by blast
    have "\<And>x. x<length (h_head # h) \<Longrightarrow>
       ((h_head # h) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((h_head # h) ! x = Zero \<longrightarrow> x \<notin> state)"
    proof-
      fix x
      assume x: "x<length (h_head # h)"
      let ?thesis = "((h_head # h) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((h_head # h) ! x = Zero \<longrightarrow> x \<notin> state)"
      {assume x0: "x = 0"
        then have ?thesis unfolding x0 using h_head not_in by auto
      } moreover {
        assume x_ge_0: "x > 0"
        then have "x-1 < length h"
          using x by simp
        then have *:"(h ! (x-1) = One \<longrightarrow> (x-1) \<in> advance_state state) \<and>
                   (h ! (x-1) = Zero \<longrightarrow> (x-1) \<notin> advance_state state)"
          using match_adv unfolding match_timestep_def by blast
        have "h ! (x-1) = (h_head # h) ! x" using x_ge_0 by auto
        then have *: "((h_head # h) ! x = One \<longrightarrow> (x-1) \<in> advance_state state) \<and>
                   ((h_head # h) ! x = Zero \<longrightarrow> (x-1) \<notin> advance_state state)"
          using * by argo
        then have ?thesis using advance_state_iff x_ge_0 by blast
      }
      ultimately show ?thesis by blast
    qed
    then have ?case
      using h_head unfolding match_timestep_def by blast
  }
  ultimately show ?case using WEST_bit.exhaust by blast
qed


lemma enumerate_list_index_one:
  assumes "j < length (enumerate_list a)"
  shows "One # enumerate_list a ! j = enumerate_list (S # a) ! (length (enumerate_list a) + j) \<and>
    (length (enumerate_list a) + j < length (enumerate_list (S # a)))"
  using assms
proof(induct a arbitrary: j)
  case Nil
  then show ?case by auto
next
  case (Cons a1 a2)
  then show ?case unfolding enumerate_list.simps
    by (metis (mono_tags, lifting) length_append length_map nat_add_left_cancel_less nth_append_length_plus nth_map)
qed

lemma list_concat_index:
  assumes "j < length L1"
  shows "(L1@L2)!j = L1!j"
  using assms
  by (simp add: nth_append)

lemma enumerate_list_index_zero:
  assumes "j < length (enumerate_list a)"
  shows "Zero # enumerate_list a ! j = enumerate_list (S # a) ! j \<and>
    j < length (enumerate_list (S # a))"
  using assms unfolding enumerate_list.simps
proof(induct a arbitrary: j)
  case Nil
  then show ?case by simp
next
  case (Cons a1 a2)
  then have j_bound: "j < length (enumerate_list (S # a1 # a2))"
    by simp
  let ?subgoal = "Zero # enumerate_list (a1 # a2) ! j = enumerate_list (S # a1 # a2) ! j"
  have "j < length (map ((#) Zero) (enumerate_list (a1 # a2)))"
    using j_bound Cons by simp
  then have "(((map ((#) Zero) (enumerate_list (a1 # a2)) @
     map ((#) One) (enumerate_list (a1 # a2)))) !
    j) = (map ((#) Zero) (enumerate_list (a1 # a2)))!j"
    using Cons.prems j_bound list_concat_index by blast
  then have ?subgoal using Cons unfolding enumerate_list.simps
    by simp
  then show ?case using j_bound by auto
qed


lemma match_enumerate_list:
  assumes "match_timestep state a"
  shows "\<exists>j<length (enumerate_list a).
         match_timestep state (enumerate_list a ! j)"
  using assms
proof(induct a arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons head a)
  let ?adv_state = "advance_state state"
  {assume in_state: "0 \<in> state"
    then have "(head # a) ! 0 \<noteq> Zero"
      using Cons.prems unfolding match_timestep_def by blast
    then have head: "head = One \<or> head = S"
      using WEST_bit.exhaust by auto
    have "match_timestep ?adv_state a"
      using Cons.prems
      using advance_state_match_timestep by auto
    then obtain j where obt: "match_timestep ?adv_state (enumerate_list a ! j)
                            \<and> j < length (enumerate_list a)"
      using Cons.hyps[of ?adv_state] by blast
    let ?state = "(enumerate_list a ! j)"
    {assume headcase: "head = One"
      let ?s = "One # ?state"
      have "\<And>x. x<length ?s \<Longrightarrow>
       ((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
      proof-
        fix x
        assume x: "x<length ?s"
        let ?thesis = "((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
        {assume x0: "x = 0"
          then have ?thesis using in_state by simp
        } moreover {
          assume x_ge_0: "x > 0"
          have cond1: "(One = One \<longrightarrow> 0 \<in> state) \<and> (One = Zero \<longrightarrow> 0 \<notin> state)"
            using in_state by blast
          have cond2: "\<forall>x<length (enumerate_list a ! j).
       (enumerate_list a ! j ! x = One \<longrightarrow> x + 1 \<in> state) \<and>
       (enumerate_list a ! j ! x = Zero \<longrightarrow> x + 1 \<notin> state)"
            using obt unfolding match_timestep_def advance_state_iff by fastforce
          have "x<length (One # enumerate_list a ! j)"
            using x by blast
          then have ?thesis
            using index_shift[of "One" state ?state, OF cond1 cond2] by blast
        }
        ultimately show ?thesis by blast
      qed
      then have match: "match_timestep state ?s"
        using obt headcase in_state unfolding match_timestep_def by blast
      have "(map ((#) One) (enumerate_list a) ! j) = One # (enumerate_list a ! j)"
        using obt by simp
      then have ?case unfolding headcase enumerate_list.simps
        using match obt by auto
    } moreover {
      assume headcase: "head = S"
      let ?s = "One # ?state"
      have "\<And>x. x<length ?s \<Longrightarrow>
       ((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
      proof-
        fix x
        assume x: "x<length ?s"
        let ?thesis = "((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
        {assume x0: "x = 0"
          then have ?thesis using in_state by simp
        } moreover {
          assume x_ge_0: "x > 0"
          have cond1: "(One = One \<longrightarrow> 0 \<in> state) \<and> (One = Zero \<longrightarrow> 0 \<notin> state)"
            using in_state by blast
          have cond2: "\<forall>x<length (enumerate_list a ! j).
       (enumerate_list a ! j ! x = One \<longrightarrow> x + 1 \<in> state) \<and>
       (enumerate_list a ! j ! x = Zero \<longrightarrow> x + 1 \<notin> state)"
            using obt unfolding match_timestep_def advance_state_iff by fastforce
          have "x<length (One # enumerate_list a ! j)"
            using x by blast
          then have ?thesis
            using index_shift[of "One" state ?state, OF cond1 cond2] by blast
        }
        ultimately show ?thesis by blast
      qed
      then have match: "match_timestep state ?s"
        using obt headcase in_state unfolding match_timestep_def by blast
      have "\<And>x. x<length (S # enumerate_list a ! j) \<Longrightarrow>
       ((S # enumerate_list a ! j) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((S # enumerate_list a ! j) ! x = Zero \<longrightarrow> x \<notin> state)"
      proof-
        fix x
        assume x: "x<length (S # enumerate_list a ! j)"
        let ?thesis = "((S # enumerate_list a ! j) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((S # enumerate_list a ! j) ! x = Zero \<longrightarrow> x \<notin> state)"
        {assume x0: "x = 0"
          then have ?thesis by auto
        } moreover {
          assume x_ge_0: "x > 0"
          then have ?thesis using x match unfolding match_timestep_def by simp
        }
        ultimately show ?thesis by blast
      qed
      then have match_S: "match_timestep state (S # enumerate_list a ! j)"
        using match unfolding match_timestep_def by blast
      have j_bound: "j < length (enumerate_list a)"
        using obt by blast
      have "?s = enumerate_list (S # a)!((length (enumerate_list a))+j)
            \<and> (length (enumerate_list a))+j < length (enumerate_list (S # a))"
        using j_bound enumerate_list_index_one by blast
      then have ?case unfolding headcase
        using match obt match_S by metis
    }
    ultimately have ?case using head by blast
  } moreover {
    assume not_in: "0 \<notin> state"
    then have "(head # a) ! 0 \<noteq> One"
      using Cons.prems unfolding match_timestep_def by blast
    then have head: "head = Zero \<or> head = S"
      using WEST_bit.exhaust by auto
    have "match_timestep ?adv_state a"
      using Cons.prems
      using advance_state_match_timestep by auto
    then obtain j where obt: "match_timestep ?adv_state (enumerate_list a ! j)
                            \<and> j < length (enumerate_list a)"
      using Cons.hyps[of ?adv_state] by blast
    let ?state = "(enumerate_list a ! j)"
    {assume headcase: "head = Zero"
      let ?s = "Zero # ?state"
      have "\<And>x. x<length ?s \<Longrightarrow>
       ((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
      proof-
        fix x
        assume x: "x<length ?s"
        let ?thesis = "((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
        {assume x0: "x = 0"
          then have ?thesis using not_in headcase by simp
        } moreover {
          assume x_ge_0: "x > 0"
          have cond1: "(Zero = One \<longrightarrow> 0 \<in> state) \<and> (Zero = Zero \<longrightarrow> 0 \<notin> state)"
            using not_in by blast
          have cond2: "\<forall>x<length (enumerate_list a ! j).
       (enumerate_list a ! j ! x = One \<longrightarrow> x + 1 \<in> state) \<and>
       (enumerate_list a ! j ! x = Zero \<longrightarrow> x + 1 \<notin> state)"
            using obt unfolding match_timestep_def advance_state_iff by fastforce
          have "x<length (Zero # enumerate_list a ! j)"
            using x by blast
          then have ?thesis
            using index_shift[of "Zero" state ?state, OF cond1 cond2] by blast
        }
        ultimately show ?thesis by blast
      qed
      then have match: "match_timestep state ?s"
        using obt headcase not_in unfolding match_timestep_def by blast
      have ?case unfolding headcase enumerate_list.simps
        using match obt by auto
    } moreover {
      assume headcase: "head = S"
      let ?s = "Zero # ?state"
      have "\<And>x. x<length ?s \<Longrightarrow>
       ((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
      proof-
        fix x
        assume x: "x<length ?s"
        let ?thesis = "((?s ! x = One \<longrightarrow> x \<in> state) \<and> (?s ! x = Zero \<longrightarrow> x \<notin> state))"
        {assume x0: "x = 0"
          then have ?thesis using not_in by simp
        } moreover {
          assume x_ge_0: "x > 0"
          have cond1: "(Zero = One \<longrightarrow> 0 \<in> state) \<and> (Zero = Zero \<longrightarrow> 0 \<notin> state)"
            using not_in by blast
          have cond2: "\<forall>x<length (enumerate_list a ! j).
       (enumerate_list a ! j ! x = One \<longrightarrow> x + 1 \<in> state) \<and>
       (enumerate_list a ! j ! x = Zero \<longrightarrow> x + 1 \<notin> state)"
            using obt unfolding match_timestep_def advance_state_iff by fastforce
          have "x<length (Zero # enumerate_list a ! j)"
            using x by blast
          then have ?thesis
            using index_shift[of "Zero" state ?state, OF cond1 cond2] by blast
        }
        ultimately show ?thesis by blast
      qed
      then have match: "match_timestep state ?s"
        using obt headcase not_in unfolding match_timestep_def by blast
      have "\<And>x. x<length (S # enumerate_list a ! j) \<Longrightarrow>
       ((S # enumerate_list a ! j) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((S # enumerate_list a ! j) ! x = Zero \<longrightarrow> x \<notin> state)"
      proof-
        fix x
        assume x: "x<length (S # enumerate_list a ! j)"
        let ?thesis = "((S # enumerate_list a ! j) ! x = One \<longrightarrow> x \<in> state) \<and>
       ((S # enumerate_list a ! j) ! x = Zero \<longrightarrow> x \<notin> state)"
        {assume x0: "x = 0"
          then have ?thesis by auto
        } moreover {
          assume x_ge_0: "x > 0"
          then have ?thesis using x match unfolding match_timestep_def by simp
        }
        ultimately show ?thesis by blast
      qed
      then have match_S: "match_timestep state (S # enumerate_list a ! j)"
        using match unfolding match_timestep_def by blast
      have j_bound: "j < length (enumerate_list a)"
        using obt by blast
      have "?s = enumerate_list (S # a)!(j)
            \<and> j < length (enumerate_list (S # a))"
        using j_bound enumerate_list_index_zero by blast
      then have ?case unfolding headcase
        using match obt match_S by metis
    }
    ultimately have ?case using head by blast
  }
  ultimately show ?case by blast
qed


lemma enumerate_trace_head_in:
  assumes "a_head # a_tail \<in> set (enumerate_trace (h # trace))"
  shows " a_head \<in> set (enumerate_list h)"
proof -
    let ?flat = "flatten_list
     (map (\<lambda>t. map (\<lambda>h. h # t)
                 (enumerate_list h))
       (enumerate_trace trace))"
    have flat_is: "?flat = ?flat"
      by auto
    have mem: "List.member
     ?flat
     (a_head # a_tail)"
      using assms unfolding enumerate_trace.simps
      using in_set_member by metis
    then obtain x1_head x1_tail where
      x1_props: "a_head # a_tail = x1_head # x1_tail \<and>
     List.member (enumerate_list h) x1_head \<and>
     List.member (enumerate_trace trace) x1_tail"
     using flatten_list_shape[OF mem flat_is]  by auto
   then have "a_head = x1_head"
     by auto
   then have "List.member (enumerate_list h) a_head "
     using x1_props
     by auto
   then show ?thesis
    using in_set_member
    by fast
qed


lemma enumerate_trace_tail_in:
  assumes "a_head # a_tail \<in> set (enumerate_trace (h # trace))"
  shows "a_tail \<in> set (enumerate_trace trace)"
proof -
    let ?flat = "flatten_list
     (map (\<lambda>t. map (\<lambda>h. h # t)
                 (enumerate_list h))
       (enumerate_trace trace))"
    have flat_is: "?flat = ?flat"
      by auto
    have mem: "List.member
     ?flat
     (a_head # a_tail)"
      using assms unfolding enumerate_trace.simps
      using in_set_member by metis
    then obtain x1_head x1_tail where
      x1_props: "a_head # a_tail = x1_head # x1_tail \<and>
     List.member (enumerate_list h) x1_head \<and>
     List.member (enumerate_trace trace) x1_tail"
     using flatten_list_shape[OF mem flat_is]  by auto
   then have "a_tail = x1_tail"
     by auto
   then have "List.member (enumerate_trace trace) a_tail "
     using x1_props
     by auto
   then show ?thesis
    using in_set_member
    by fast
qed


text \<open> Intuitively, this says that the traces in enumerate trace h are
``more specific'' than h, which is ``more generic''---i.e., h
matches everything that each element of enumerate trace h matches. \<close>
lemma match_enumerate_trace_aux:
  assumes "a \<in> set (enumerate_trace trace)"
  assumes "match_regex \<pi> a"
  shows "match_regex \<pi> trace"
proof -
  show ?thesis using assms proof (induct trace arbitrary: a \<pi>)
    case Nil
    then show ?case by auto
  next
    case (Cons h trace)
    then obtain a_head a_tail where obt_a: "a = a_head#a_tail"
      using enumerate_trace_len
      by (metis length_0_conv neq_Nil_conv)
    have "length \<pi> > 0"
      using Cons unfolding match_regex_def obt_a by auto
    then obtain \<pi>_head \<pi>_tail where obt_\<pi>: "\<pi> = \<pi>_head#\<pi>_tail"
      using min_list.cases by auto
    have cond1: "a_tail \<in> set (enumerate_trace trace)"
      using Cons.prems(1) unfolding obt_a
      using enumerate_trace_tail_in by blast
    have cond2: "match_regex \<pi>_tail a_tail"
      using Cons.prems(2) unfolding obt_a obt_\<pi> match_regex_def by auto
    have match_tail: "match_regex \<pi>_tail trace"
      using Cons.hyps[OF cond1 cond2] by blast
    have a_head: "a_head \<in> set (enumerate_list h)"
      using Cons.prems(1) unfolding obt_a
      using enumerate_trace_head_in by blast
    have "match_timestep \<pi>_head a_head"
      using Cons.prems(2) unfolding obt_\<pi> match_regex_def
      using obt_a by auto
    then have match_head: "match_timestep \<pi>_head h"
      using match_enumerate_state_aux[of a_head h \<pi>_head] a_head by blast
    have "\<And>time. time<length (h # trace) \<Longrightarrow>
        match_timestep ((\<pi>_head # \<pi>_tail) ! time) ((h # trace) ! time)"
    proof-
      fix time
      assume time: "time<length (h # trace)"
      let ?thesis = "match_timestep ((\<pi>_head # \<pi>_tail) ! time) ((h # trace) ! time)"
      {assume time0: "time = 0"
        then have ?thesis using match_head by simp
      } moreover {
        assume time_ge_0: "time > 0"
        then have ?thesis
          using match_tail time_ge_0 time unfolding match_regex_def by simp
      }
      ultimately show ?thesis by blast
    qed
    then show ?case using match_tail unfolding match_regex_def obt_a obt_\<pi>
      by simp
  qed
qed


lemma match_enumerate_trace:
  assumes "a \<in> set (enumerate_trace h) \<and> match_regex \<pi> a"
  shows "match \<pi> (h # T)"
proof-
  show ?thesis
    unfolding match_def
    using match_enumerate_trace_aux assms
    by auto
qed


lemma match_enumerate_sets1:
  assumes "(\<exists>r \<in> (enumerate_sets R). match_regex \<pi> r)"
  shows "(match \<pi> R)"
  using assms
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons h T)
  then obtain a where a_prop: "a\<in>set (enumerate_trace h) \<union> enumerate_sets T \<and> match_regex \<pi> a"
    by auto
  { assume *: "a \<in> set (enumerate_trace h)"
    then have ?case
      using match_enumerate_trace a_prop
      by blast
  } moreover {assume *: "a \<in> enumerate_sets T"
    then have "match \<pi> T"
      using Cons a_prop by blast
    then have ?case
      by (metis Suc_leI le_imp_less_Suc length_Cons match_def nth_Cons_Suc)
  }
  ultimately show ?case
    using a_prop by auto
qed

lemma match_cases:
  assumes "match \<pi> (a # R)"
  shows "match \<pi> [a] \<or> match \<pi> R"
proof-
  obtain i where obt: "match_regex \<pi> ((a # R)!i) \<and> i < length (a # R)"
    using assms unfolding match_def by blast
  {assume i0: "i = 0"
    then have ?thesis
      using assms unfolding match_def using obt by simp
  } moreover {
    assume i_ge_0: "i > 0"
    then have "match_regex \<pi> (R ! (i-1))"
      using assms obt unfolding match_def by simp
    then have "match \<pi> R"
      unfolding match_def using obt i_ge_0
      by (metis Suc_diff_1 Suc_less_eq length_Cons)
    then have ?thesis by blast
  }
  ultimately show ?thesis using assms unfolding match_def by blast
qed


lemma enumerate_trace_decompose:
  assumes "state \<in> set (enumerate_list h)"
  assumes "trace \<in> set (enumerate_trace T)"
  shows "state#trace \<in> set (enumerate_trace (h#T))"
proof-
  let ?enumh = "enumerate_list h"
  let ?enumT = "enumerate_trace T"
  let ?flat = "flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) ?enumh) ?enumT)"
  have enum: "enumerate_trace (h#T) = ?flat"
    unfolding enumerate_trace.simps by simp
  obtain i where i: "?enumT!i = trace \<and> i < length ?enumT"
    using assms(2) by (meson in_set_conv_nth)
  obtain j where j: "?enumh!j = state \<and> j < length ?enumh"
    using assms(1) by (meson in_set_conv_nth)
  have "enumerate_list h ! j # enumerate_trace T ! i =
    flatten_list (map (\<lambda>t. map (\<lambda>h. h # t) (enumerate_list h)) (enumerate_trace T)) !
    (i * length (enumerate_list h) + j) \<and>
    i * length (enumerate_list h) + j
    < length
       (flatten_list
         (map (\<lambda>t. map (\<lambda>h. h # t) (enumerate_list h)) (enumerate_trace T)))"
    using flatten_list_idx[of ?flat ?enumh ?enumT i j] enum i j by blast
  then show ?thesis
    using i j enum by simp
qed


lemma match_enumerate_trace_aux_converse:
  assumes "match_regex \<pi> trace"
  shows "match \<pi> (enumerate_trace trace)"
  using assms
proof(induct trace arbitrary: \<pi>)
  case Nil
  have enum: "enumerate_trace [] = [[]]"
    by simp
  show ?case unfolding enum match_def match_regex_def by auto
next
  case (Cons a trace)
  have "length \<pi> > 0"
    using Cons.prems unfolding match_regex_def by auto
  then obtain pi_head pi_tail where pi_obt: "\<pi> = pi_head#pi_tail"
    using list.exhaust by auto
  have cond: "match_regex pi_tail trace"
    using Cons.prems pi_obt unfolding match_regex_def by auto
  then have match_tail: "match pi_tail (enumerate_trace trace)"
    using Cons.hyps by blast
  then obtain i where obt_i: "match_regex pi_tail (enumerate_trace trace ! i) \<and>
         i<length (enumerate_trace trace)"
    unfolding match_def by blast
  let ?enum_tail = "(enumerate_trace trace ! i)"

  have match_head: "match_timestep pi_head a"
    using Cons.prems unfolding match_regex_def
    by (metis Cons.prems WEST_and_trace_correct_forward_aux nth_Cons' pi_obt)
  then have "\<exists>j < length (enumerate_list a).
             match_timestep pi_head ((enumerate_list a)!j)"
    using match_enumerate_list by blast
  then obtain j where obt_j: "match_timestep pi_head ((enumerate_list a)!j) \<and>
                       j < length (enumerate_list a)"
    by blast
  let ?enum_head = "(enumerate_list a)!j"

  have "(?enum_head#?enum_tail) \<in> set(enumerate_trace (a # trace))"
    using enumerate_trace_decompose
    by (meson in_set_conv_nth obt_i obt_j)
  have match_tail: "match_regex pi_tail ?enum_tail"
    using obt_i by blast
  have match_head: "match_timestep pi_head ((enumerate_list a)!j)"
    using obt_j by blast
  have match: "match_regex \<pi> (?enum_head#?enum_tail)"
    using match_head match_tail
    using WEST_and_trace_correct_forward_aux_converse[OF pi_obt match_head match_tail] by auto
  let ?flat = "flatten_list
     (map (\<lambda>t. map (\<lambda>h. h # t) (enumerate_list a))
       (enumerate_trace trace))"
  have "enumerate_list a ! j # enumerate_trace trace ! i =
  flatten_list
   (map (\<lambda>t. map (\<lambda>h. h # t) (enumerate_list a)) (enumerate_trace trace)) !
  (i * length (enumerate_list a) + j) \<and>
  i * length (enumerate_list a) + j
  < length
     (flatten_list
       (map (\<lambda>t. map (\<lambda>h. h # t) (enumerate_list a)) (enumerate_trace trace)))"
    using flatten_list_idx[of ?flat "enumerate_list a" "enumerate_trace trace" i j]
    using obt_i obt_j by blast
  then show ?case
    unfolding match_def using match
    by auto
qed


lemma match_enumerate_sets2:
  assumes "(match \<pi> R)"
  shows "(\<exists>r \<in> enumerate_sets R. match_regex \<pi> r)"
  using assms
proof(induct R arbitrary: \<pi>)
  case Nil
  then show ?case unfolding match_def by auto
next
  case (Cons a R)
  have "enumerate_sets (a # R) = set (enumerate_trace a) \<union> enumerate_sets R"
    unfolding enumerate_sets.simps by blast
  {assume match_a: "match \<pi> [a]"
    then have "match_regex \<pi> a"
      unfolding match_def by simp
    then have "match \<pi> (enumerate_trace a)"
      using match_enumerate_trace_aux
      using match_enumerate_trace_aux_converse by blast
    then have "\<exists>b \<in> set (enumerate_trace a). match_regex \<pi> b"
      unfolding match_def by auto
    then have ?case by auto
  } moreover {
    assume match_R: "match \<pi> R"
    then have ?case
      using Cons by auto
  }
  ultimately show ?case
    using Cons.prems match_cases by blast
qed


lemma match_enumerate_sets:
  shows "(\<exists>r \<in> enumerate_sets R. match_regex \<pi> r) \<longleftrightarrow> (match \<pi> R)"
  using match_enumerate_sets1 match_enumerate_sets2
  by blast

lemma regex_equivalence_correct1:
  assumes "(naive_equivalence A B)"
  shows "match \<pi> A = match \<pi> B"
  unfolding regex_equiv_def
  using match_enumerate_sets[of A \<pi>] match_enumerate_sets[of B \<pi>]
  using assms
  unfolding naive_equivalence.simps
  by blast


lemma regex_equivalence_correct:
  shows "(naive_equivalence A B) \<longrightarrow> (regex_equiv A B)"
  using regex_equivalence_correct1
  unfolding regex_equiv_def
  by metis


export_code naive_equivalence in Haskell module_name regex_equiv

end