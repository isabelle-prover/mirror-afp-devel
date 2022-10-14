(* Title: thys/StrongCopyTM.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

subsubsection \<open>A Turing machine that duplicates its input iff the input is a single numeral\<close>

theory StrongCopyTM
  imports
    WeakCopyTM
begin

text \<open>If we run \<open>tm_strong_copy\<close> on a single numeral, it behaves like the original weak version \<open>tm_weak_copy\<close>.
However, if we run the strong machine on an empty list, the result is an empty list.
If we run the machine on a list with more than two numerals, this
strong variant will just return the first numeral of the list (a singleton list).

Thus, the result will be a list of two numerals only if we run it on a singleton list.

This is exactly the property, we need for the reduction of problem \<open>K1\<close> to problem \<open>H1\<close>.
\<close>

(* ---------- tm_skip_first_arg ---------- *)

(*
let
tm_skip_first_arg = from_raw [
  (L,0),(R,2),     --  1  on Bk stop and delegate to tm_erase_right_then_dblBk_left, on Oc investigate further
  (R,3),(R,2),     --  2  'go right until Bk': on Bk check for further args, on Oc continue loop 'go right until Bk'
  (L,4),(WO,0),    --  3  on 2nd Bk go for OK path, on Oc delegate to tm_erase_right_then_dblBk_left
  --
  (L,5),(L,5),     --  4  skip 1st Bk
  --
  (R,0),(L,5)      --  5  'go left until Bk': on 2nd Bk stop, on Oc continue loop 'go left until Bk'
  ]
*)

definition 
  tm_skip_first_arg :: "instr list"
  where
    "tm_skip_first_arg \<equiv>
    [ (L,0),(R,2), (R,3),(R,2), (L,4),(WO,0), (L,5),(L,5), (R,0),(L,5) ]"

(* Prove partial correctness and termination for tm_skip_first_arg *)

(* ERROR case: length nl = 0 *)

lemma tm_skip_first_arg_correct_Nil:
  "\<lbrace>\<lambda>tap. tap = ([], [])\<rbrace> tm_skip_first_arg \<lbrace>\<lambda>tap. tap = ([], [Bk]) \<rbrace>"
proof -
  have "steps0 (1, [], []) tm_skip_first_arg 1 = (0::nat, [], [Bk])"
    by (simp add: step.simps steps.simps numeral_eqs_upto_12  tm_skip_first_arg_def)
  then show ?thesis
    by (smt Hoare_haltI holds_for.simps is_final_eq)
qed

corollary tm_skip_first_arg_correct_Nil':
  "length nl = 0
   \<Longrightarrow>  \<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace> tm_skip_first_arg \<lbrace>\<lambda>tap. tap = ([], [Bk]) \<rbrace>"
  using tm_skip_first_arg_correct_Nil
  by (simp add: tm_skip_first_arg_correct_Nil )

(*  OK cases: length nl = 1 *)

(*
ctxrunTM tm_skip_first_arg (1, [], [Oc])

0: [] _1_ [Oc]
=> 
1: [Oc] _2_ []
=> 
2: [Oc,Bk] _3_ []
=> 
3: [Oc] _4_ [Bk]
=> 
4: [] _5_ [Oc,Bk]
=> 
5: [] _5_ [Bk,Oc,Bk]
=> 
6: [Bk] _0_ [Oc,Bk]

ctxrunTM tm_skip_first_arg (1, [], [Oc, Oc, Oc, Oc])

0: [] _1_ [Oc,Oc,Oc,Oc]
=> 
1: [Oc] _2_ [Oc,Oc,Oc]
=> 
2: [Oc,Oc] _2_ [Oc,Oc]
=> 
3: [Oc,Oc,Oc] _2_ [Oc]
=> 
4: [Oc,Oc,Oc,Oc] _2_ []
=> 
5: [Oc,Oc,Oc,Oc,Bk] _3_ []
=> 
6: [Oc,Oc,Oc,Oc] _4_ [Bk]
=> 
7: [Oc,Oc,Oc] _5_ [Oc,Bk]
=> 
8: [Oc,Oc] _5_ [Oc,Oc,Bk]
=> 
9: [Oc] _5_ [Oc,Oc,Oc,Bk]
=> 
10: [] _5_ [Oc,Oc,Oc,Oc,Bk]
=> 
11: [] _5_ [Bk,Oc,Oc,Oc,Oc,Bk]
=> 
12: [Bk] _0_ [Oc,Oc,Oc,Oc,Bk]

*)

fun 
  inv_tm_skip_first_arg_len_eq_1_s0 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_eq_1_s1 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_eq_1_s2 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_eq_1_s3 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_eq_1_s4 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_eq_1_s5 :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_skip_first_arg_len_eq_1_s0 n (l, r) = (
      l = [Bk] \<and> r = Oc \<up> (Suc n) @ [Bk])"
  | "inv_tm_skip_first_arg_len_eq_1_s1 n (l, r) = ( 
      l = [] \<and> r = Oc \<up> Suc n)"
  | "inv_tm_skip_first_arg_len_eq_1_s2 n (l, r) = 
      (\<exists>n1 n2. l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 \<and> Suc n1 + n2 = Suc n)"
  | "inv_tm_skip_first_arg_len_eq_1_s3 n (l, r) = (
      l = Bk # Oc \<up> (Suc n) \<and> r = [])"
  | "inv_tm_skip_first_arg_len_eq_1_s4 n (l, r) = ( 
      l = Oc \<up> (Suc n) \<and> r = [Bk])"
  | "inv_tm_skip_first_arg_len_eq_1_s5 n (l, r) = 
       (\<exists>n1 n2. (l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) \<or>
                (l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) )"


fun inv_tm_skip_first_arg_len_eq_1 :: "nat \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_tm_skip_first_arg_len_eq_1 n (s, tap) = 
        (if s = 0 then inv_tm_skip_first_arg_len_eq_1_s0 n tap else
         if s = 1 then inv_tm_skip_first_arg_len_eq_1_s1 n tap else
         if s = 2 then inv_tm_skip_first_arg_len_eq_1_s2 n tap else
         if s = 3 then inv_tm_skip_first_arg_len_eq_1_s3 n tap else
         if s = 4 then inv_tm_skip_first_arg_len_eq_1_s4 n tap else
         if s = 5 then inv_tm_skip_first_arg_len_eq_1_s5 n tap 
         else False)"

lemma tm_skip_first_arg_len_eq_1_cases: 
  fixes s::nat
  assumes "inv_tm_skip_first_arg_len_eq_1 n (s,l,r)"
    and "s=0 \<Longrightarrow> P"
    and "s=1 \<Longrightarrow> P"
    and "s=2 \<Longrightarrow> P"
    and "s=3 \<Longrightarrow> P"
    and "s=4 \<Longrightarrow> P"
    and "s=5 \<Longrightarrow> P"
  shows "P"
proof -
  have "s < 6"
  proof (rule ccontr)
    assume "\<not> s < 6"
    with \<open>inv_tm_skip_first_arg_len_eq_1 n (s,l,r)\<close> show False by auto
  qed
  then have "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3  \<or> s = 4 \<or> s = 5" by auto
  with assms show ?thesis by auto
qed

lemma inv_tm_skip_first_arg_len_eq_1_step: 
  assumes "inv_tm_skip_first_arg_len_eq_1 n cf" 
  shows "inv_tm_skip_first_arg_len_eq_1 n (step0 cf tm_skip_first_arg)"
proof (cases cf)
  case (fields s l r)
  then have cf_cases: "cf = (s, l, r)" .
  show "inv_tm_skip_first_arg_len_eq_1 n (step0 cf tm_skip_first_arg)"
  proof (rule tm_skip_first_arg_len_eq_1_cases)
    from cf_cases and assms
    show "inv_tm_skip_first_arg_len_eq_1 n (s, l, r)" by auto
  next
    assume "s = 0"
    with cf_cases and assms
    show ?thesis by (auto simp add: tm_skip_first_arg_def)
  next
    assume "s = 1"
    show ?thesis
    proof -
      have "inv_tm_skip_first_arg_len_eq_1 n (step0 (1, l, r) tm_skip_first_arg)"
      proof (cases r)
        case Nil
        then have "r = []" .
        with assms and cf_cases and \<open>s = 1\<close> show ?thesis
          by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases a)
        next
          case Bk
          then have "a = Bk" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 1\<close>
          show ?thesis 
            by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
        next
          case Oc
          then have "a = Oc" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 1\<close>
          show ?thesis
            by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
        qed
      qed
      with cf_cases and \<open>s=1\<close> show ?thesis by auto
    qed
  next
    assume "s = 2"
    show ?thesis
    proof -
      have "inv_tm_skip_first_arg_len_eq_1 n (step0 (2, l, r) tm_skip_first_arg)"
      proof (cases r)
        case Nil
        then have "r = []" .
        with assms and cf_cases and \<open>s = 2\<close>
        have "inv_tm_skip_first_arg_len_eq_1_s2 n (l, r)" by auto
        then have "(\<exists>n1 n2. l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 \<and> Suc n1 + n2 = Suc n)"
          by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)

        then obtain n1 n2 where
          w_n1_n2: "l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 \<and> Suc n1 + n2 = Suc n" by blast

        with \<open>r = []\<close> have "n2 = 0" by auto 

        then have "step0 (2, Oc \<up> (Suc n1),  Oc \<up> n2) tm_skip_first_arg = (3, Bk # Oc \<up> (Suc n1), [])"
          by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)

        moreover with \<open>n2 = 0\<close> and w_n1_n2
        have "inv_tm_skip_first_arg_len_eq_1 n (3, Bk # Oc \<up> (Suc n1), [])" 
          by fastforce
        ultimately show ?thesis using  w_n1_n2
          by auto
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases a)
          case Bk (* not possible due to invariant in state 2 *)
          then have "a = Bk" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 2\<close>
          show ?thesis 
            by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
        next
          case Oc
          then have "a = Oc" .

          with assms and cf_cases and \<open>s = 2\<close>
          have "inv_tm_skip_first_arg_len_eq_1_s2 n (l, r)" by auto
          then have "\<exists>n1 n2. l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 \<and> Suc n1 + n2 = Suc n"
            by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
          then obtain n1 n2 where
            w_n1_n2: "l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 \<and> Suc n1 + n2 = Suc n" by blast

          with \<open>r = a # rs\<close> and \<open>a = Oc\<close> have "Oc # rs = Oc \<up> n2" by auto
          then have "n2 > 0" by (meson Cons_replicate_eq)

          then have "step0 (2, Oc \<up> (Suc n1),  Oc \<up> n2) tm_skip_first_arg = (2, Oc # Oc \<up> (Suc n1), Oc \<up> (n2-1))"
            by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_skip_first_arg_len_eq_1 n (2, Oc # Oc \<up> (Suc n1), Oc \<up> (n2-1))"
          proof -
            from \<open>n2 > 0\<close> and w_n1_n2
            have "Oc # Oc \<up> (Suc n1) =  Oc \<up> (Suc (Suc n1)) \<and> Oc \<up> (n2-1) = Oc \<up> (n2-1) \<and>
              Suc (Suc n1) + (n2-1) = Suc n" by auto
            then have "(\<exists>n1' n2'. Oc # Oc \<up> (Suc n1) =  Oc \<up> (Suc n1') \<and> Oc \<up> (n2-1) = Oc \<up> n2' \<and>
              Suc n1' + n2' = Suc n)" by auto
            then show "inv_tm_skip_first_arg_len_eq_1 n (2, Oc # Oc \<up> (Suc n1), Oc \<up> (n2-1))"
              by auto
          qed
          ultimately show ?thesis
            using  assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 2\<close> and w_n1_n2
            by auto
        qed
      qed
      with cf_cases and \<open>s=2\<close> show ?thesis by auto
    qed
  next
    assume "s = 3"
    show ?thesis
    proof -
      have "inv_tm_skip_first_arg_len_eq_1 n (step0 (3, l, r) tm_skip_first_arg)"
      proof (cases r)
        case Nil
        then have "r = []" .
        with assms and cf_cases and \<open>s = 3\<close>
        have "inv_tm_skip_first_arg_len_eq_1_s3 n (l, r)" by auto
        then have "l = Bk # Oc \<up> (Suc n) \<and> r = []"
          by auto
        then 
        have "step0 (3, Bk # Oc \<up> (Suc n), []) tm_skip_first_arg = (4, Oc \<up> (Suc n), [Bk])"
          by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)
        moreover
        have "inv_tm_skip_first_arg_len_eq_1 n (4, Oc \<up> (Suc n), [Bk])" 
          by fastforce
        ultimately show ?thesis
          using \<open>l = Bk # Oc \<up> (Suc n) \<and> r = []\<close> by auto
      next
        case (Cons a rs) (* not possible due to invariant in state 3 *)
        then have "r = a # rs" .

        with assms and cf_cases and \<open>s = 3\<close>
        have "inv_tm_skip_first_arg_len_eq_1_s3 n (l, r)" by auto
        then have "l = Bk # Oc \<up> (Suc n) \<and> r = []"
          by auto

        with \<open>r = a # rs\<close> have False by auto
        then show ?thesis by auto
      qed
      with cf_cases and \<open>s=3\<close> show ?thesis by auto
    qed
  next
    assume "s = 4"
    show ?thesis
    proof -
      have "inv_tm_skip_first_arg_len_eq_1 n (step0 (4, l, r) tm_skip_first_arg)"
      proof (cases r)
        case Nil  (* not possible due to invariant in state 4 *)
        then have "r = []" .
        with assms and cf_cases and \<open>s = 4\<close> show ?thesis
          by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases a)
        next
          case Bk
          then have "a = Bk" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 4\<close>
          have "inv_tm_skip_first_arg_len_eq_1_s4 n (l, r)" by auto
          then have "l = Oc \<up> (Suc n) \<and> r = [Bk]" by auto

          then have F0: "step0 (4,  Oc \<up> (Suc n), [Bk]) tm_skip_first_arg = (5, Oc \<up> n, Oc \<up> (Suc 0) @ [Bk])"
            by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)
          moreover
          have "inv_tm_skip_first_arg_len_eq_1_s5 n (Oc \<up> n, Oc \<up> (Suc 0) @ [Bk])"
          proof (cases n)
            case 0
            then have "n=0" .
            then have "inv_tm_skip_first_arg_len_eq_1_s5 0 ([], Oc \<up> (Suc 0) @ [Bk])"
              by auto
            moreover with \<open>n=0\<close> have "(5, Oc \<up> n, Oc \<up> (Suc 0) @ [Bk]) = (5, [], Oc \<up> (Suc 0) @ [Bk])" by auto
            ultimately show ?thesis by auto
          next
            case (Suc n')
            then have "n = Suc n'" .
            then have "(5, Oc \<up> n, Oc \<up> (Suc 0) @ [Bk]) = (5, Oc \<up> Suc n', Oc \<up> (Suc 0) @ [Bk])" by auto
            with \<open>n=Suc n'\<close> have "Suc n' + Suc 0 = Suc n" by arith
            then have "(Oc \<up> Suc n' = Oc \<up> Suc n' \<and> Oc \<up> (Suc 0) @ [Bk] = Oc \<up> Suc 0 @ [Bk] \<and> Suc n' + Suc 0 = Suc n)" by auto
            with \<open>(5, Oc \<up> n, Oc \<up> (Suc 0) @ [Bk]) = (5, Oc \<up> Suc n', Oc \<up> (Suc 0) @ [Bk])\<close>
            show ?thesis
              by (simp add: Suc \<open>Suc n' + Suc 0 = Suc n\<close>)
          qed
          then have "inv_tm_skip_first_arg_len_eq_1 n (5, Oc \<up> n, Oc \<up> (Suc 0) @ [Bk])" by auto
          ultimately show ?thesis
            using \<open>l = Oc \<up> (Suc n) \<and> r = [Bk]\<close> by auto
        next
          case Oc (* not possible due to invariant in state 4 *)
          then have "a = Oc" . 
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 4\<close>
          show ?thesis 
            by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
        qed
      qed
      with cf_cases and \<open>s=4\<close> show ?thesis by auto
    qed
  next
    assume "s = 5"
    show ?thesis
    proof -
      have "inv_tm_skip_first_arg_len_eq_1 n (step0 (5, l, r) tm_skip_first_arg)"
      proof (cases r)
        case Nil  (* not possible due to invariant in state 5 *)
        then have "r = []" .
        with assms and cf_cases and \<open>s = 5\<close> show ?thesis
          by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases a)

          case Bk
          then have "a = Bk" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 5\<close>
          have "inv_tm_skip_first_arg_len_eq_1_s5 n (l, r)" by auto
          then have "\<exists>n1 n2. (l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                             (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) \<or>
                             (l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n)" 
            by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
          then obtain n1 n2 where
            w_n1_n2: "(l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                      (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) \<or>
                      (l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n)" by blast

          with \<open>a = Bk\<close> and \<open>r = a # rs\<close>
          have "l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n"            
            by auto

          then have "step0 (5, [], Bk#Oc \<up> Suc n2 @ [Bk]) tm_skip_first_arg = (0, [Bk], Oc \<up> Suc n2 @ [Bk])"
            by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_skip_first_arg_len_eq_1 n (0, [Bk], Oc \<up> Suc n @ [Bk])"
          proof - 
            have  "inv_tm_skip_first_arg_len_eq_1_s0 n ([Bk], Oc \<up> Suc n @ [Bk])"
              by (simp)
            then show "inv_tm_skip_first_arg_len_eq_1 n (0, [Bk], Oc \<up> Suc n @ [Bk])"
              by auto
          qed
          ultimately show ?thesis
            using  assms and \<open>a = Bk\<close> and \<open>r = a # rs\<close> and cf_cases and \<open>s = 5\<close>
              and \<open>l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n\<close>
            by (simp)
        next
          case Oc
          then have "a = Oc" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 5\<close>
          have "inv_tm_skip_first_arg_len_eq_1_s5 n (l, r)" by auto
          then have "\<exists>n1 n2. (l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                             (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) \<or>
                             (l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n)" 
            by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
          then obtain n1 n2 where
            w_n1_n2: "(l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                      (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) \<or>
                      (l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n)" by blast

          with \<open>a = Oc\<close> and \<open>r = a # rs\<close>
          have "(l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n)" by auto

          then show ?thesis
          proof
            assume "l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n"
            then have "step0 (5, l, r) tm_skip_first_arg = (5, Oc \<up> n1 , Oc \<up> Suc (Suc n2) @ [Bk])"
              by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)

            moreover have "inv_tm_skip_first_arg_len_eq_1 n (5, Oc \<up> n1 , Oc \<up> Suc (Suc n2) @ [Bk])"
            proof -
              from \<open>l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n\<close> 
              have  "inv_tm_skip_first_arg_len_eq_1_s5 n (Oc \<up> n1, Oc \<up> Suc (Suc n2) @ [Bk])"
                by (cases n1) auto
              then show "inv_tm_skip_first_arg_len_eq_1 n (5, Oc \<up> n1 , Oc \<up> Suc (Suc n2) @ [Bk])"
                by auto
            qed
            ultimately show "inv_tm_skip_first_arg_len_eq_1 n (step0 (5, l, r) tm_skip_first_arg)"
              by auto
          next
            assume "l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n"
            then have "step0 (5, l, r) tm_skip_first_arg = (5, [], Bk # Oc \<up> Suc n2 @ [Bk])"
              by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)

            moreover have "inv_tm_skip_first_arg_len_eq_1 n (step0 (5, l, r) tm_skip_first_arg)"
            proof -
              from \<open>l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n\<close>
              have "inv_tm_skip_first_arg_len_eq_1_s5 n (l, r)"                
                by simp
              then show "inv_tm_skip_first_arg_len_eq_1 n (step0 (5, l, r) tm_skip_first_arg)"
                using \<open>l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n\<close>
                  and \<open>step0 (5, l, r) tm_skip_first_arg = (5, [], Bk # Oc \<up> Suc n2 @ [Bk])\<close>
                by simp
            qed

            ultimately show ?thesis
              using  assms and \<open>a = Oc\<close> and \<open>r = a # rs\<close> and cf_cases and \<open>s = 5\<close>
                and \<open>l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n\<close>
              by (simp )
          qed
        qed
      qed
      with cf_cases and \<open>s=5\<close> show ?thesis by auto

    qed
  qed
qed

lemma inv_tm_skip_first_arg_len_eq_1_steps: 
  assumes "inv_tm_skip_first_arg_len_eq_1 n cf" 
  shows "inv_tm_skip_first_arg_len_eq_1 n (steps0 cf tm_skip_first_arg stp)"
proof (induct stp)
  case 0
  with assms show ?case
    by (auto simp add: inv_tm_skip_first_arg_len_eq_1_step step.simps steps.simps)
next
  case (Suc stp)
  with assms show ?case
    using inv_tm_skip_first_arg_len_eq_1_step step_red by auto 
qed

lemma tm_skip_first_arg_len_eq_1_partial_correctness:
  assumes "\<exists>stp. is_final (steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp)"
  shows "\<lbrace> \<lambda>tap. tap = ([], <[n::nat]>) \<rbrace> 
           tm_skip_first_arg
         \<lbrace> \<lambda>tap. tap = ([Bk], <[n::nat]> @[Bk]) \<rbrace>"
proof (rule Hoare_consequence)
  show "(\<lambda>tap. tap = ([], <[n::nat]>)) \<mapsto> (\<lambda>tap. tap = ([], <[n::nat]>))"
    by auto
next
  show "inv_tm_skip_first_arg_len_eq_1_s0 n \<mapsto> (\<lambda>tap. tap = ([Bk], <[n::nat]> @ [Bk]))"
    by (simp add: assert_imp_def  tape_of_list_def tape_of_nat_def)
next
  show "\<lbrace>\<lambda>tap. tap = ([], <[n]>)\<rbrace> tm_skip_first_arg \<lbrace>inv_tm_skip_first_arg_len_eq_1_s0 n\<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r:: "cell list"
    assume major: "(l, r) = ([], <[n]>)"
    show "\<exists>stp. is_final (steps0 (1, l, r) tm_skip_first_arg stp) \<and>
                inv_tm_skip_first_arg_len_eq_1_s0 n holds_for steps0 (1, l, r) tm_skip_first_arg stp"
    proof -
      from major and assms have "\<exists>stp. is_final (steps0 (1, l, r) tm_skip_first_arg stp)" by auto
      then obtain stp where
        w_stp: "is_final (steps0 (1, l, r) tm_skip_first_arg stp)" by blast

      moreover have "inv_tm_skip_first_arg_len_eq_1_s0 n holds_for steps0 (1, l, r) tm_skip_first_arg stp"
      proof -
        have "inv_tm_skip_first_arg_len_eq_1 n (1, l, r)"
          by (simp add: major tape_of_list_def tape_of_nat_def)

        then have "inv_tm_skip_first_arg_len_eq_1 n (steps0 (1, l, r) tm_skip_first_arg stp)"
          using inv_tm_skip_first_arg_len_eq_1_steps by auto

        then show ?thesis
          by (smt holds_for.elims(3) inv_tm_skip_first_arg_len_eq_1.simps is_final_eq w_stp)
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed

(* --- now, we prove termination of tm_skip_first_arg on singleton lists --- *)
(* 
    Lexicographic orders (See List.measures)
    quote: "These are useful for termination proofs"
    
    lemma in_measures[simp]:
      "(x, y) \<in> measures [] = False"
      "(x, y) \<in> measures (f # fs)
             = (f x < f y \<or> (f x = f y \<and> (x, y) \<in> measures fs))"
*)

(* Assemble a lexicographic measure function *)

definition measure_tm_skip_first_arg_len_eq_1 :: "(config \<times> config) set"
  where
    "measure_tm_skip_first_arg_len_eq_1 = measures [
      \<lambda>(s, l, r). (if s = 0 then 0 else 5 - s),
      \<lambda>(s, l, r). (if s = 2 then length r else 0),
      \<lambda>(s, l, r). (if s = 5 then length l + (if hd r = Oc then 2 else 1) else 0)
      ]"

lemma wf_measure_tm_skip_first_arg_len_eq_1: "wf measure_tm_skip_first_arg_len_eq_1"
  unfolding measure_tm_skip_first_arg_len_eq_1_def
  by (auto)

lemma measure_tm_skip_first_arg_len_eq_1_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_tm_skip_first_arg_len_eq_1\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_tm_skip_first_arg_len_eq_1
  by (metis wf_iff_no_infinite_down_chain)

(* Machine tm_skip_first_arg always halts on a singleton list *)

lemma tm_skip_first_arg_len_eq_1_halts:
  "\<exists>stp. is_final (steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp)"
proof (induct rule: measure_tm_skip_first_arg_len_eq_1_induct)
  case (Step stp)
  then have not_final: "\<not> is_final (steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp)" .

  have INV: "inv_tm_skip_first_arg_len_eq_1 n (steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp)"
  proof (rule_tac inv_tm_skip_first_arg_len_eq_1_steps)
    show  "inv_tm_skip_first_arg_len_eq_1 n (1, [], <[n::nat]>)"
      by (simp add: tape_of_list_def tape_of_nat_def  )
  qed

  have SUC_STEP_RED: "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
        step0 (steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp) tm_skip_first_arg"
    by (rule step_red)

  show "( steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp),
          steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp
        ) \<in> measure_tm_skip_first_arg_len_eq_1"
  proof (cases "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp")
    case (fields s l r)
    then have cf_cases: "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (s, l, r)" .

    show ?thesis
    proof (rule tm_skip_first_arg_len_eq_1_cases)
      from INV and cf_cases
      show "inv_tm_skip_first_arg_len_eq_1 n (s, l, r)" by auto
    next
      assume "s=0" (* not possible *)
      with cf_cases not_final
      show ?thesis by auto
    next
      assume "s=1"
      show ?thesis
      proof (cases r)
        case Nil        
        then have "r = []" .

        with cf_cases and \<open>s=1\<close>
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (1, l, [])"
          by auto
        with INV have False by auto (* not possible due to invariant in s=1 *)
        then show ?thesis by auto
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases "a")
          case Bk
          then have "a=Bk" .
          with cf_cases and \<open>s=1\<close> and \<open>r = a # rs\<close>
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (1, l, Bk#rs)"
            by auto       

          with INV have False by auto (* not possible due to invariant in s=1 *)
          then show ?thesis by auto
        next
          case Oc
          then have "a=Oc" .
          with cf_cases and \<open>s=1\<close> and \<open>r = a # rs\<close>
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (1, l, Oc#rs)"
            by auto   

          with SUC_STEP_RED
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (1, l, Oc#rs) tm_skip_first_arg"
            by auto

          also have "... = (2,Oc#l,rs)"
            by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) = (2,Oc#l,rs)"
            by auto

          with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (1, l, Oc#rs)\<close>
          show ?thesis           
            by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
        qed         
      qed
    next
      assume "s=2"
      show ?thesis
      proof -
        from cf_cases and \<open>s=2\<close>
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (2, l, r)"
          by auto

        with cf_cases  and \<open>s=2\<close> and INV
        have "(\<exists>n1 n2. l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 \<and> Suc n1 + n2 = Suc n)"
          by auto
        then have "(\<exists>n2. r = Oc \<up> n2)" by blast
        then obtain n2 where w_n2: "r = Oc \<up> n2" by blast
        show ?thesis
        proof (cases n2)
          case 0
          then have "n2 = 0" .
          with w_n2 have "r = []" by auto
          with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (2, l, r)\<close>
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (2, l, [])"
            by auto

          with SUC_STEP_RED
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (2, l, []) tm_skip_first_arg"
            by auto

          also have "... = (3,Bk#l,[])"
            by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) = (3,Bk#l,[])"
            by auto

          with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (2, l, [])\<close>
          show ?thesis           
            by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
        next
          case (Suc n2')
          then have "n2 = Suc n2'" .

          with w_n2 have "r = Oc \<up> Suc n2'" by auto
          with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (2, l, r)\<close>
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (2, l, Oc#Oc \<up> n2')"
            by auto

          with SUC_STEP_RED
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (2, l, Oc#Oc \<up> n2') tm_skip_first_arg"
            by auto

          also have "... = (2,Oc#l,Oc \<up> n2')"
            by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) = (2,Oc#l,Oc \<up> n2')"
            by auto

          with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (2, l, Oc#Oc \<up> n2')\<close>
          show ?thesis           
            by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
        qed
      qed
    next
      assume "s=3"
      show ?thesis
      proof -
        from cf_cases and \<open>s=3\<close>
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (3, l, r)"
          by auto

        with cf_cases  and \<open>s=3\<close> and INV

        have "l = Bk # Oc \<up> (Suc n) \<and> r = []"
          by auto

        with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (3, l, r)\<close>
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (3, Bk # Oc \<up> (Suc n), [])"
          by auto

        with SUC_STEP_RED
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (3, Bk # Oc \<up> (Suc n), []) tm_skip_first_arg"
          by auto

        also have "... = (4,Oc \<up> (Suc n),[Bk])"
          by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) = (4,Oc \<up> (Suc n),[Bk])"
          by auto

        with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (3, Bk # Oc \<up> (Suc n), [])\<close>
        show ?thesis           
          by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
      qed
    next
      assume "s=4"
      show ?thesis
      proof -
        from cf_cases and \<open>s=4\<close>
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (4, l, r)"
          by auto

        with cf_cases  and \<open>s=4\<close> and INV

        have "l = Oc \<up> (Suc n) \<and> r = [Bk]"
          by auto

        with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (4, l, r)\<close>
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (4, Oc \<up> (Suc n), [Bk])"
          by auto

        with SUC_STEP_RED
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (4, Oc \<up> (Suc n), [Bk]) tm_skip_first_arg"
          by auto

        also have "... = (5,Oc \<up> n,[Oc, Bk])"
          by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) = (5,Oc \<up> n,[Oc, Bk])"
          by auto

        with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (4, Oc \<up> (Suc n), [Bk])\<close>
        show ?thesis           
          by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
      qed
    next
      assume "s=5"
      show ?thesis
      proof -
        from cf_cases and \<open>s=5\<close>
        have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, l, r)"
          by auto

        with cf_cases  and \<open>s=5\<close> and INV

        have "(\<exists>n1 n2.
                (l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) \<or>
                (l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) )"
          by auto

        then obtain n1 n2 where
          w_n1_n2: "(l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n) \<or>
                    (l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n) \<or>
                    (l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n)"
          by blast
        then show ?thesis
        proof
          assume "l = Oc \<up> Suc n1 \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n1 + Suc n2 = Suc n"

          with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, l, r)\<close>
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, Oc \<up> Suc n1, Oc \<up> Suc n2 @ [Bk])"
            by auto

          with SUC_STEP_RED
          have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (5, Oc \<up> Suc n1, Oc \<up> Suc n2 @ [Bk]) tm_skip_first_arg"
            by auto

          also have "... = (5,Oc \<up> n1,Oc#Oc \<up> Suc n2 @ [Bk])"
            by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                        (5,Oc \<up> n1,Oc#Oc \<up> Suc n2 @ [Bk])"
            by auto

          with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, Oc \<up> Suc n1, Oc \<up> Suc n2 @ [Bk])\<close>
          show ?thesis           
            by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
        next
          assume "l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n \<or>
                  l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n"
          then show ?thesis
          proof
            assume "l = [] \<and> r = Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n"

            with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, l, r)\<close>
            have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, [], Oc \<up> Suc n2 @ [Bk])"
              by auto

            with SUC_STEP_RED
            have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (5, [], Oc \<up> Suc n2 @ [Bk]) tm_skip_first_arg"
              by auto

            also have "... = (5,[],Bk#Oc \<up> Suc n2 @ [Bk])"
              by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                        (5,[],Bk#Oc \<up> Suc n2 @ [Bk])"
              by auto

            with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, [], Oc \<up> Suc n2 @ [Bk])\<close>
            show ?thesis           
              by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
          next
            assume "l = [] \<and> r = Bk # Oc \<up> Suc n2 @ [Bk] \<and> Suc n2 = Suc n"

            with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, l, r)\<close>
            have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, [], Bk # Oc \<up> Suc n2 @ [Bk])"
              by auto

            with SUC_STEP_RED
            have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                step0 (5, [], Bk # Oc \<up> Suc n2 @ [Bk]) tm_skip_first_arg"
              by auto

            also have "... = (0,[Bk], Oc \<up> Suc n2 @ [Bk])"
              by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [], <[n::nat]>) tm_skip_first_arg (Suc stp) =
                        (0,[Bk], Oc \<up> Suc n2 @ [Bk])"
              by auto

            with \<open>steps0 (1, [], <[n::nat]>) tm_skip_first_arg stp = (5, [], Bk # Oc \<up> Suc n2 @ [Bk])\<close>
            show ?thesis         
              by (auto simp add: measure_tm_skip_first_arg_len_eq_1_def)
          qed
        qed
      qed
    qed
  qed
qed

lemma tm_skip_first_arg_len_eq_1_total_correctness:
  "\<lbrace> \<lambda>tap. tap = ([], <[n::nat]>)\<rbrace>
     tm_skip_first_arg
   \<lbrace> \<lambda>tap. tap = ([Bk], <[n::nat]> @[Bk])\<rbrace>"
proof (rule tm_skip_first_arg_len_eq_1_partial_correctness)
  show "\<exists>stp. is_final (steps0 (1, [], <[n]>) tm_skip_first_arg stp)"
    using  tm_skip_first_arg_len_eq_1_halts by auto
qed

lemma tm_skip_first_arg_len_eq_1_total_correctness':
  "length nl = 1
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = ([Bk],  <[hd nl]> @[Bk])\<rbrace>"
proof -
  assume "length nl = 1"
  then have "nl = [hd nl]"
    by (metis One_nat_def diff_Suc_1 length_0_conv length_greater_0_conv length_tl list.distinct(1)
        list.expand list.sel(1) list.sel(3) list.size(3) zero_neq_one)
  moreover have "\<lbrace> \<lambda>tap. tap = ([], <[hd nl]>)\<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = ([Bk], <[hd nl]> @[Bk])\<rbrace>"
    by (rule tm_skip_first_arg_len_eq_1_total_correctness)
  ultimately show ?thesis
    by (simp add: Hoare_haltE Hoare_haltI tape_of_list_def)
qed

(* ERROR cases: length nl > 1 *)

(*
ctxrunTM tm_skip_first_arg (1,[],[Oc, Bk, Oc])
0: [] _1_ [Oc,Bk,Oc]
=>
1: [Oc] _2_ [Bk,Oc]
=>
2: [Oc,Bk] _3_ [Oc]
=>
3: [Oc,Bk] _0_ [Oc]

ctxrunTM tm_skip_first_arg (1,[],[Oc,Oc, Bk, Oc,Oc])
0: [] _1_ [Oc,Oc,Bk,Oc,Oc]
=>
1: [Oc] _2_ [Oc,Bk,Oc,Oc]
=> 
2: [Oc,Oc] _2_ [Bk,Oc,Oc]
=>
3: [Oc,Oc,Bk] _3_ [Oc,Oc]
=>
4: [Oc,Oc,Bk] _0_ [Oc,Oc]

ctxrunTM tm_skip_first_arg (1,[],[Oc,Oc,Oc, Bk, Oc,Oc])
0: [] _1_ [Oc,Oc,Oc,Bk,Oc,Oc]
=>
1: [Oc] _2_ [Oc,Oc,Bk,Oc,Oc]
=>
2: [Oc,Oc] _2_ [Oc,Bk,Oc,Oc]
=>
3: [Oc,Oc,Oc] _2_ [Bk,Oc,Oc]
=>
4: [Oc,Oc,Oc,Bk] _3_ [Oc,Oc]
=>
5: [Oc,Oc,Oc,Bk] _0_ [Oc,Oc]

ctxrunTM tm_skip_first_arg (1, [], [Oc,Oc,Bk, Oc,Bk, Oc,Oc])
0: [] _1_ [Oc,Oc,Bk,Oc,Bk,Oc,Oc]
=>
1: [Oc] _2_ [Oc,Bk,Oc,Bk,Oc,Oc]
=>
2: [Oc,Oc] _2_ [Bk,Oc,Bk,Oc,Oc]
=>
3: [Bk,Oc,Oc] _3_ [Oc,Bk,Oc,Oc]
=>
4: [Bk,Oc,Oc] _0_ [Oc,Bk,Oc,Oc]


*)


fun 
  inv_tm_skip_first_arg_len_gt_1_s0 :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_gt_1_s1 :: "nat \<Rightarrow> nat list\<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_gt_1_s2 :: "nat \<Rightarrow> nat list\<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_skip_first_arg_len_gt_1_s3 :: "nat \<Rightarrow> nat list\<Rightarrow> tape \<Rightarrow> bool"
  where
   "inv_tm_skip_first_arg_len_gt_1_s1 n ns (l, r) = (
      l = [] \<and> r = Oc \<up> Suc n @ [Bk] @ (<ns::nat list>) )"
  | "inv_tm_skip_first_arg_len_gt_1_s2 n ns (l, r) = 
      (\<exists>n1 n2. l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 @ [Bk] @ (<ns::nat list>) \<and>
                Suc n1 + n2 = Suc n)"
  | "inv_tm_skip_first_arg_len_gt_1_s3 n ns (l, r) = (
      l = Bk # Oc \<up> (Suc n) \<and> r = (<ns::nat list>)
      )"
  |  "inv_tm_skip_first_arg_len_gt_1_s0 n ns (l, r) = (
      l = Bk# Oc \<up> (Suc n) \<and> r = (<ns::nat list>)
      )"

fun inv_tm_skip_first_arg_len_gt_1 :: "nat \<Rightarrow> nat list \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_tm_skip_first_arg_len_gt_1 n ns (s, tap) = 
        (if s = 0 then inv_tm_skip_first_arg_len_gt_1_s0 n ns tap else
         if s = 1 then inv_tm_skip_first_arg_len_gt_1_s1 n ns tap else
         if s = 2 then inv_tm_skip_first_arg_len_gt_1_s2 n ns tap else
         if s = 3 then inv_tm_skip_first_arg_len_gt_1_s3 n ns tap
         else False)"

lemma tm_skip_first_arg_len_gt_1_cases: 
  fixes s::nat
  assumes "inv_tm_skip_first_arg_len_gt_1 n ns (s,l,r)"
    and "s=0 \<Longrightarrow> P"
    and "s=1 \<Longrightarrow> P"
    and "s=2 \<Longrightarrow> P"
    and "s=3 \<Longrightarrow> P"
    and "s=4 \<Longrightarrow> P"
    and "s=5 \<Longrightarrow> P"
  shows "P"
proof -
  have "s < 6"
  proof (rule ccontr)
    assume "\<not> s < 6"
    with \<open>inv_tm_skip_first_arg_len_gt_1 n ns (s,l,r)\<close> show False by auto
  qed
  then have "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3  \<or> s = 4 \<or> s = 5" by auto
  with assms show ?thesis by auto
qed

lemma inv_tm_skip_first_arg_len_gt_1_step: 
  assumes "length ns > 0"
    and "inv_tm_skip_first_arg_len_gt_1 n ns cf" 
  shows "inv_tm_skip_first_arg_len_gt_1 n ns (step0 cf tm_skip_first_arg)"
proof (cases cf)
  case (fields s l r)
  then have cf_cases: "cf = (s, l, r)" .
  show "inv_tm_skip_first_arg_len_gt_1 n ns (step0 cf tm_skip_first_arg)"
  proof (rule tm_skip_first_arg_len_gt_1_cases)
    from cf_cases and assms
    show "inv_tm_skip_first_arg_len_gt_1 n ns (s, l, r)" by auto
  next
    assume "s = 0"
    with cf_cases and assms
    show ?thesis by (auto simp add: tm_skip_first_arg_def)
  next
    assume "s = 4"
    with cf_cases and assms
    show ?thesis by (auto simp add: tm_skip_first_arg_def)
  next
    assume "s = 5"
    with cf_cases and assms
    show ?thesis by (auto simp add: tm_skip_first_arg_def)
  next
    assume "s = 1"
    with cf_cases and assms
    have "l = [] \<and> r = Oc \<up> Suc n @ [Bk] @ (<ns::nat list>)"
      by auto
    with assms and cf_cases and \<open>s = 1\<close> show ?thesis
      by (auto simp add: tm_skip_first_arg_def step.simps steps.simps)
  next
    assume "s = 2"
    with cf_cases and assms
    have "(\<exists>n1 n2. l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 @ [Bk] @ (<ns::nat list>) \<and> Suc n1 + n2 = Suc n)"
      by auto
    then obtain n1 n2
      where w_n1_n2: "l = Oc \<up> (Suc n1) \<and> r = Oc \<up> n2 @ [Bk] @ (<ns::nat list>) \<and> Suc n1 + n2 = Suc n" by blast
    show ?thesis
    proof (cases n2)
      case 0
      then have "n2 = 0" .
      with w_n1_n2 have "l = Oc \<up> (Suc n1) \<and> r = [Bk] @ (<ns::nat list>) \<and> Suc n1 = Suc n"
        by auto

      then have "step0 (2, Oc \<up> (Suc n1),  [Bk] @ (<ns::nat list>)) tm_skip_first_arg = (3, Bk # Oc \<up> (Suc n1), (<ns::nat list>))"
        by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)

      moreover have "inv_tm_skip_first_arg_len_gt_1 n ns (3, Bk # Oc \<up> (Suc n1), (<ns::nat list>))"
      proof -
        from \<open>l = Oc \<up> (Suc n1) \<and> r = [Bk] @ (<ns::nat list>) \<and> Suc n1 = Suc n\<close>
        have "Oc \<up> (Suc n1) = Oc \<up> (Suc n1) \<and> Bk # Oc \<up> (Suc n1) = Bk#Oc#Oc \<up> n1 \<and> Suc n1 + 0 = Suc n" by auto
        then show "inv_tm_skip_first_arg_len_gt_1 n ns (3, Bk # Oc \<up> (Suc n1), (<ns::nat list>))" by auto
      qed

      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 2\<close> and w_n1_n2
        by auto
    next
      case (Suc n2')
      then have "n2 = Suc n2'" .
      with w_n1_n2 have "l = Oc \<up> (Suc n1) \<and> r = Oc \<up> Suc n2' @ [Bk] @ (<ns::nat list>) \<and> Suc n1 + n2 = Suc n"
        by auto

      then have "step0 (2, Oc \<up> (Suc n1),  Oc \<up> Suc n2' @ [Bk] @ (<ns::nat list>)) tm_skip_first_arg
                  = (2, Oc # Oc \<up> (Suc n1), Oc \<up> n2' @ [Bk] @ (<ns::nat list>))"
        by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)

      moreover have "inv_tm_skip_first_arg_len_gt_1 n ns (2, Oc # Oc \<up> (Suc n1), Oc \<up> n2' @ [Bk] @ (<ns::nat list>))"
      proof -
        from \<open>l = Oc \<up> (Suc n1) \<and> r = Oc \<up> Suc n2' @ [Bk] @ (<ns::nat list>) \<and> Suc n1 + n2 = Suc n\<close>
        have "Oc # Oc \<up> (Suc n1) = Oc \<up> Suc (Suc n1) \<and> Oc \<up> n2' @ [Bk] @ (<ns::nat list>)
                 = Oc \<up> n2' @ [Bk] @ (<ns::nat list>) \<and> Suc (Suc n1) + n2' = Suc n"
          by (simp add: Suc add_Suc_shift)
        then show "inv_tm_skip_first_arg_len_gt_1 n ns (2, Oc # Oc \<up> (Suc n1), Oc \<up> n2' @ [Bk] @ (<ns::nat list>))" 
          by force
      qed

      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 2\<close> and w_n1_n2
        using \<open>l = Oc \<up> (Suc n1) \<and> r = Oc \<up> Suc n2' @ [Bk] @ (<ns::nat list>) \<and> Suc n1 + n2 = Suc n\<close>
        by force
    qed
  next
    assume "s = 3"
    with cf_cases and assms
    have unpackedINV: "l = Bk # Oc \<up> (Suc n) \<and> r = (<ns::nat list>)"
      by auto
    moreover with \<open>length ns > 0\<close> have "(ns::nat list) \<noteq> [] \<and> hd (<ns::nat list>) = Oc"
      using numeral_list_head_is_Oc
      by force
    moreover from this have "<ns::nat list> = Oc#(tl (<ns::nat list>))"
      by (metis append_Nil list.exhaust_sel tape_of_list_empty
          unique_Bk_postfix_numeral_list_Nil)
    ultimately have "step0 (3, Bk # Oc \<up> (Suc n),  (<ns::nat list>)) tm_skip_first_arg
                     = (0, Bk # Oc \<up> (Suc n), (<ns::nat list>))"
    proof -
      from \<open><ns> = Oc # tl (<ns>)\<close>
      have "step0 (3, Bk # Oc \<up> (Suc n),  (<ns::nat list>)) tm_skip_first_arg
            = step0 (3, Bk # Oc \<up> (Suc n), Oc # tl (<ns>)) tm_skip_first_arg"
        by auto
      also have "... = (0, Bk # Oc \<up> (Suc n),  Oc # tl (<ns>))"
        by (simp add:  tm_skip_first_arg_def step.simps steps.simps numeral_eqs_upto_12)
      also with  \<open><ns> = Oc # tl (<ns>)\<close> have "... =  (0, Bk # Oc \<up> (Suc n),  (<ns::nat list>))" by auto
      finally show "step0 (3, Bk # Oc \<up> (Suc n),  (<ns::nat list>)) tm_skip_first_arg
                    = (0, Bk # Oc \<up> (Suc n), (<ns::nat list>))"
        by auto
    qed

    moreover with \<open>l = Bk # Oc \<up> (Suc n) \<and> r = (<ns::nat list>)\<close>
    have "inv_tm_skip_first_arg_len_gt_1 n ns (0, Bk # Oc \<up> (Suc n), (<ns::nat list>))"
      by auto

    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 3\<close> and unpackedINV
      by auto
  qed
qed

lemma inv_tm_skip_first_arg_len_gt_1_steps: 
  assumes "length ns > 0"
  and "inv_tm_skip_first_arg_len_gt_1 n ns cf" 
  shows "inv_tm_skip_first_arg_len_gt_1 n ns (steps0 cf tm_skip_first_arg stp)"
proof (induct stp)
  case 0
  with assms show ?case
    by (auto simp add: inv_tm_skip_first_arg_len_gt_1_step step.simps steps.simps)
next
  case (Suc stp)
  with assms show ?case
    using inv_tm_skip_first_arg_len_gt_1_step step_red by auto 
qed

lemma tm_skip_first_arg_len_gt_1_partial_correctness:
  assumes "\<exists>stp. is_final (steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns::nat list>) ) tm_skip_first_arg stp)"
  and "0 < length ns"
  shows "\<lbrace>\<lambda>tap. tap = ([], Oc \<up> Suc n @ [Bk] @ (<ns::nat list>) ) \<rbrace> 
           tm_skip_first_arg
         \<lbrace> \<lambda>tap. tap = (Bk# Oc \<up> Suc n, (<ns::nat list>) ) \<rbrace>"
proof (rule Hoare_consequence)
  show " (\<lambda>tap. tap = ([],  Oc \<up> Suc n @ [Bk] @ (<ns::nat list>)))
         \<mapsto> (\<lambda>tap. tap = ([],  Oc \<up> Suc n @ [Bk] @ (<ns::nat list>)))"
    by (simp add: assert_imp_def tape_of_nat_def)
next
  show "inv_tm_skip_first_arg_len_gt_1_s0 n ns \<mapsto> (\<lambda>tap. tap = (Bk # Oc \<up> Suc n, <ns>))"
    using assert_imp_def inv_tm_skip_first_arg_len_gt_1_s0.simps rev_numeral tape_of_nat_def by auto
next
  show "\<lbrace>\<lambda>tap. tap = ([], Oc \<up> Suc n @ [Bk] @ <ns>)\<rbrace> tm_skip_first_arg \<lbrace>inv_tm_skip_first_arg_len_gt_1_s0 n ns\<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r:: "cell list"
    assume major: "(l, r) = ([], Oc \<up> Suc n @ [Bk] @ <ns::nat list>)"
    show "\<exists>stp. is_final (steps0 (1, l, r) tm_skip_first_arg stp) \<and>
            inv_tm_skip_first_arg_len_gt_1_s0 n ns holds_for steps0 (1, l, r) tm_skip_first_arg stp"
    proof -
      from major and assms have "\<exists>stp. is_final (steps0 (1, l, r) tm_skip_first_arg stp)" by auto
      then obtain stp where
        w_stp: "is_final (steps0 (1, l, r) tm_skip_first_arg stp)" by blast

      moreover have "inv_tm_skip_first_arg_len_gt_1_s0 n ns holds_for steps0 (1, l, r) tm_skip_first_arg stp"
      proof -
        have "inv_tm_skip_first_arg_len_gt_1 n ns (1, l, r)"
          by (simp add: major tape_of_list_def tape_of_nat_def)

        with assms  have "inv_tm_skip_first_arg_len_gt_1 n ns (steps0 (1, l, r) tm_skip_first_arg stp)"
          using inv_tm_skip_first_arg_len_gt_1_steps by auto

        then show ?thesis
          by (smt holds_for.elims(3) inv_tm_skip_first_arg_len_gt_1.simps is_final_eq w_stp)
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed

(* --- now, we prove termination of tm_skip_first_arg on arguments containing more than one numeral --- *)
(* 
    Lexicographic orders (See List.measures)
    quote: "These are useful for termination proofs"
    
    lemma in_measures[simp]:
      "(x, y) \<in> measures [] = False"
      "(x, y) \<in> measures (f # fs)
             = (f x < f y \<or> (f x = f y \<and> (x, y) \<in> measures fs))"
*)

(* Assemble a lexicographic measure function *)

definition measure_tm_skip_first_arg_len_gt_1 :: "(config \<times> config) set"
  where
    "measure_tm_skip_first_arg_len_gt_1 = measures [
      \<lambda>(s, l, r). (if s = 0 then 0 else 4 - s),
      \<lambda>(s, l, r). (if s = 2 then length r else 0)
      ]"

lemma wf_measure_tm_skip_first_arg_len_gt_1: "wf measure_tm_skip_first_arg_len_gt_1"
  unfolding measure_tm_skip_first_arg_len_gt_1_def
  by (auto)

lemma measure_tm_skip_first_arg_len_gt_1_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_tm_skip_first_arg_len_gt_1\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_tm_skip_first_arg_len_gt_1
  by (metis wf_iff_no_infinite_down_chain)

lemma tm_skip_first_arg_len_gt_1_halts:
  "0 < length ns \<Longrightarrow> \<exists>stp. is_final (steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns::nat list>) tm_skip_first_arg stp)"
proof -
  assume A:  "0 < length ns"
  show "\<exists>stp. is_final (steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns::nat list>) tm_skip_first_arg stp)"
  proof (induct rule: measure_tm_skip_first_arg_len_gt_1_induct)
    case (Step stp)
    then have not_final: "\<not> is_final (steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg stp)" .

    have INV: "inv_tm_skip_first_arg_len_gt_1 n ns (steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg stp)"
    proof (rule_tac inv_tm_skip_first_arg_len_gt_1_steps)
      from A show "0 < length ns " .
      then show  "inv_tm_skip_first_arg_len_gt_1 n ns (1, [], Oc \<up> Suc n @ [Bk] @ <ns>)"
        by (simp add: tape_of_list_def tape_of_nat_def)
    qed

    have SUC_STEP_RED:
      "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg (Suc stp) =
         step0 (steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg stp) tm_skip_first_arg"
      by (rule step_red)

    show "( steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg (Suc stp),
          steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg stp
        ) \<in> measure_tm_skip_first_arg_len_gt_1"

    proof (cases "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg stp")
      case (fields s l r2)
      then have
        cf_cases: "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ <ns>) tm_skip_first_arg stp = (s, l, r2)" .
      show ?thesis
      proof (rule tm_skip_first_arg_len_gt_1_cases)
        from INV and cf_cases
        show "inv_tm_skip_first_arg_len_gt_1 n ns (s, l, r2)" by auto
      next
        assume "s=0" (* not possible *)
        with cf_cases not_final
        show ?thesis by auto
      next
        assume "s=4" (* not possible *)
        with cf_cases not_final INV
        show ?thesis by auto
      next
        assume "s=5" (* not possible *)
        with cf_cases not_final INV
        show ?thesis by auto
      next
        assume "s=1"
        show ?thesis
        proof -
          from cf_cases and \<open>s=1\<close>
          have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (1, l, r2)"
            by auto

          with cf_cases  and \<open>s=1\<close> and INV
          have unpackedINV: "l = [] \<and> r2 = Oc \<up> Suc n @ [Bk] @ (<ns>)"
            by auto          

          with cf_cases and \<open>s=1\<close> and SUC_STEP_RED
          have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp) =
                step0 (1, [],  Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg"
            by auto
          also have "... = (2,[Oc],Oc \<up> n @ [Bk] @ (<ns>))"
            by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp)
                       = (2,[Oc],Oc \<up> n @ [Bk] @ (<ns>))"
            by auto

          with \<open>steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (1, l, r2)\<close>
          show ?thesis
            by (auto simp add: measure_tm_skip_first_arg_len_gt_1_def)
        qed
      next
        assume "s=2"
        show ?thesis
        proof -
          from cf_cases and \<open>s=2\<close>
          have "steps0 (1, [],Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (2, l, r2)"
            by auto

          with cf_cases  and \<open>s=2\<close> and INV
          have "(\<exists>n1 n2. l = Oc \<up> (Suc n1) \<and> r2 = Oc \<up> n2 @ [Bk] @ (<ns::nat list>) \<and>
                Suc n1 + n2 = Suc n)"
            by auto
          then obtain n1 n2 where
            w_n1_n2: "l = Oc \<up> (Suc n1) \<and> r2 = Oc \<up> n2 @ [Bk] @ (<ns::nat list>) \<and> Suc n1 + n2 = Suc n" by blast
          show ?thesis
          proof (cases n2)
            case 0
            then have "n2 = 0" .
            with w_n1_n2 have "r2 = [Bk] @ (<ns::nat list>)" by auto
            with \<open>steps0 (1, [],Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (2, l, r2)\<close>
            have "steps0 (1, [],Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (2, l, [Bk] @ (<ns::nat list>))"
              by auto

            with SUC_STEP_RED
            have "steps0 (1, [],Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp) =
                step0 (2, l, [Bk] @ (<ns::nat list>)) tm_skip_first_arg"
              by auto
            also have "... = (3,Bk#l,(<ns>))"
              by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [],Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp) = (3,Bk#l,(<ns>))"
              by auto

            with \<open>steps0 (1, [],Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (2, l, [Bk] @ (<ns::nat list>))\<close>
            show ?thesis           
              by (auto simp add: measure_tm_skip_first_arg_len_gt_1_def)
          next
            case (Suc n2')
            then have "n2 = Suc n2'" .
            with w_n1_n2 have "r2 = Oc \<up> Suc n2'@Bk#(<ns>)" by auto

            with \<open>steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (2, l, r2)\<close>
            have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (2, l, Oc \<up> Suc n2'@Bk#(<ns>))"
              by auto

            with SUC_STEP_RED
            have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp) =
                step0 (2, l, Oc \<up> Suc n2'@Bk#(<ns>)) tm_skip_first_arg"
              by auto
            also have "... = (2,Oc#l,Oc \<up> n2'@Bk#(<ns>))"
              by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp)
                         = (2,Oc#l,Oc \<up> n2'@Bk#(<ns>))"
              by auto

            with \<open>steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (2, l, Oc \<up> Suc n2'@Bk#(<ns>))\<close>
            show ?thesis           
              by (auto simp add: measure_tm_skip_first_arg_len_gt_1_def)
          qed
        qed
      next
        assume "s=3"
        show ?thesis
        proof -
          from cf_cases and \<open>s=3\<close>
          have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (3, l, r2)"
            by auto

          with cf_cases  and \<open>s=3\<close> and INV

          have unpacked_INV: "l = Bk # Oc \<up> (Suc n) \<and> r2 = (<ns::nat list>)"
            by auto
          with \<open>steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (3, l, r2)\<close>

          have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (3,  Bk # Oc \<up> (Suc n), (<ns::nat list>))"
            by auto

          with SUC_STEP_RED
          have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp) =
                step0 (3,  Bk # Oc \<up> (Suc n), (<ns::nat list>)) tm_skip_first_arg"
            by auto

          also have "... = (0, Bk # Oc \<up> (Suc n),(<ns::nat list>))"
          proof -
            from \<open>length ns > 0\<close> have "(ns::nat list) \<noteq> [] \<and> hd (<ns::nat list>) = Oc"
              using numeral_list_head_is_Oc
              by force
            then have "<ns::nat list> = Oc#(tl (<ns::nat list>))"
              by (metis append_Nil list.exhaust_sel tape_of_list_empty
                  unique_Bk_postfix_numeral_list_Nil)

            then have "step0 (3,  Bk # Oc \<up> (Suc n), (<ns::nat list>)) tm_skip_first_arg
                     = step0 (3,  Bk # Oc \<up> (Suc n), Oc#(tl (<ns::nat list>))) tm_skip_first_arg"
              by auto
            also have "... = (0, Bk # Oc \<up> (Suc n), Oc#(tl (<ns::nat list>)))"
              by (auto simp add: tm_skip_first_arg_def numeral_eqs_upto_12 step.simps steps.simps)
            also with \<open><ns::nat list> = Oc#(tl (<ns::nat list>))\<close>
            have "... = (0, Bk # Oc \<up> (Suc n), <ns::nat list>)"
              by auto
            finally show "step0 (3,  Bk # Oc \<up> (Suc n), (<ns::nat list>)) tm_skip_first_arg
                     = (0, Bk # Oc \<up> (Suc n), <ns::nat list>)" by auto
          qed
          finally have "steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg (Suc stp) =
                      (0, Bk # Oc \<up> (Suc n),(<ns::nat list>))"
            by auto

          with \<open>steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns>)) tm_skip_first_arg stp = (3,  Bk # Oc \<up> (Suc n), (<ns::nat list>))\<close>
          show ?thesis
            by (auto simp add: measure_tm_skip_first_arg_len_gt_1_def)
        qed
      qed
    qed
  qed
qed

lemma tm_skip_first_arg_len_gt_1_total_correctness_pre:
  assumes "0 < length ns"
  shows "\<lbrace>\<lambda>tap. tap = ([], Oc \<up> Suc n @ [Bk] @ (<ns::nat list>) ) \<rbrace> 
           tm_skip_first_arg
         \<lbrace> \<lambda>tap. tap = (Bk# Oc \<up> Suc n, (<ns::nat list>) ) \<rbrace>"
proof (rule tm_skip_first_arg_len_gt_1_partial_correctness)
  from assms show "0 < length ns" .
  from assms show "\<exists>stp. is_final (steps0 (1, [], Oc \<up> Suc n @ [Bk] @ (<ns::nat list>) ) tm_skip_first_arg stp)"
    using  tm_skip_first_arg_len_gt_1_halts by auto
qed

lemma tm_skip_first_arg_len_gt_1_total_correctness:
  assumes "1 < length (nl::nat list)"
  shows "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = (Bk# <rev [hd nl]>, <tl nl>) \<rbrace>"
proof -
  from assms have major: "(nl::nat list) = hd nl # tl nl"
    by (metis list.exhaust_sel list.size(3)  not_one_less_zero)
  from assms have "tl nl \<noteq> []"
    using list_length_tl_neq_Nil by auto
  from assms have "(nl::nat list) \<noteq> []" by auto

  from \<open>(nl::nat list) = hd nl # tl nl\<close>
  have "<nl::nat list> = <hd nl # tl nl>"
    by auto
  also with \<open>tl nl \<noteq> []\<close> have "... = <hd nl> @ [Bk] @ (<tl nl>)"
    by (simp add:  tape_of_nat_list_cons_eq)
  also with \<open>(nl::nat list) \<noteq> []\<close> have "... = Oc \<up> Suc (hd nl) @ [Bk] @ (<tl nl>)"
    using tape_of_nat_def by blast
  finally have "<nl::nat list> = Oc \<up> Suc (hd nl) @ [Bk] @ (<tl nl>)"
    by auto

  from \<open>tl nl \<noteq> []\<close> have "0 < length (tl nl)"
    using length_greater_0_conv by blast
  with assms have 
    "\<lbrace>\<lambda>tap. tap = ([], Oc \<up> Suc (hd nl) @ [Bk] @ (<tl nl>) ) \<rbrace> 
           tm_skip_first_arg
     \<lbrace> \<lambda>tap. tap = (Bk# Oc \<up> Suc (hd nl), (<tl nl>) ) \<rbrace>"
    using tm_skip_first_arg_len_gt_1_total_correctness_pre
    by force
  with \<open><nl::nat list> = Oc \<up> Suc (hd nl) @ [Bk] @ (<tl nl>)\<close> have 
    "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list> ) \<rbrace> 
           tm_skip_first_arg
     \<lbrace> \<lambda>tap. tap = (Bk# Oc \<up> Suc (hd nl), (<tl nl>) ) \<rbrace>"
    by force
  moreover have "<rev [hd nl]> = Oc \<up> Suc (hd nl)"
    by (simp add: tape_of_list_def tape_of_nat_def)
  ultimately 
  show ?thesis
    by (simp add: rev_numeral rev_numeral_list tape_of_list_def )
qed

(* ---------- tm_erase_right_then_dblBk_left ---------- *)

(* We will prove:

-- DO_NOTHING path, the eraser should do nothing

lemma tm_erase_right_then_dblBk_left_dnp_total_correctness:
 "\<lbrace> \<lambda>tap. tap = ([], r ) \<rbrace> 
    tm_erase_right_then_dblBk_left
  \<lbrace> \<lambda>tap. tap = ([Bk,Bk], r ) \<rbrace>"

-- ERASE path

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_one_arg:
  assumes "1 \<le> length (nl::nat list)"
  shows "\<lbrace> \<lambda>tap. tap = (Bk# rev(<hd nl>), <tl nl>) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (<hd nl>) @ [Bk] @ Bk \<up> rex ) \<rbrace>"

*)

(* Test runs for the formulation of invariants:
 *
 * See file EngineeringOf_StrongCopy2.hs for more test runs
 *

ctxrunTM tm_erase_right_then_dblBk_left (1, [Bk,Oc], [Oc])
0: [Bk,Oc] _1_ [Oc]
=> 
1: [Oc] _2_ [Bk,Oc]
=> 
2: [] _3_ [Oc,Bk,Oc]
=> 
3: [Oc] _5_ [Bk,Oc]
=> 
4: [Bk,Oc] _6_ [Oc]
=> 
5: [Bk,Oc] _6_ [Bk]
=> 
6: [Bk,Bk,Oc] _7_ []
=> 
7: [Bk,Bk,Bk,Oc] _9_ []
=> 
8: [Bk,Bk,Oc] _10_ [Bk]
=> 
9: [Bk,Oc] _10_ [Bk,Bk]
=> 
10: [Oc] _10_ [Bk,Bk,Bk]
=> 
11: [] _10_ [Oc,Bk,Bk,Bk]
=> 
12: [] _11_ [Bk,Oc,Bk,Bk,Bk]
=> 
13: [] _12_ [Bk,Bk,Oc,Bk,Bk,Bk]
=> 
14: [] _0_ [Bk,Bk,Oc,Bk,Bk,Bk]

ctxrunTM tm_erase_right_then_dblBk_left (1, [Bk,Oc,Oc], [Oc,Oc,Oc])
0: [Bk,Oc,Oc] _1_ [Oc,Oc,Oc]
=>
1: [Oc,Oc] _2_ [Bk,Oc,Oc,Oc]
=>
2: [Oc] _3_ [Oc,Bk,Oc,Oc,Oc]
=>
3: [Oc,Oc] _5_ [Bk,Oc,Oc,Oc]
=>
4: [Bk,Oc,Oc] _6_ [Oc,Oc,Oc]
=>
5: [Bk,Oc,Oc] _6_ [Bk,Oc,Oc]
=>
6: [Bk,Bk,Oc,Oc] _7_ [Oc,Oc]
=>
7: [Bk,Bk,Oc,Oc] _8_ [Bk,Oc]
=>
8: [Bk,Bk,Bk,Oc,Oc] _7_ [Oc]
=>
9: [Bk,Bk,Bk,Oc,Oc] _8_ [Bk]
=>
10: [Bk,Bk,Bk,Bk,Oc,Oc] _7_ []
=>
11: [Bk,Bk,Bk,Bk,Bk,Oc,Oc] _9_ []
=>
12: [Bk,Bk,Bk,Bk,Oc,Oc] _10_ [Bk]
=>
13: [Bk,Bk,Bk,Oc,Oc] _10_ [Bk,Bk]
=>
14: [Bk,Bk,Oc,Oc] _10_ [Bk,Bk,Bk]
=>
15: [Bk,Oc,Oc] _10_ [Bk,Bk,Bk,Bk]
=>
16: [Oc,Oc] _10_ [Bk,Bk,Bk,Bk,Bk]
=>
17: [Oc] _10_ [Oc,Bk,Bk,Bk,Bk,Bk]
=>
18: [] _11_ [Oc,Oc,Bk,Bk,Bk,Bk,Bk]
=>
19: [] _11_ [Bk,Oc,Oc,Bk,Bk,Bk,Bk,Bk]
=>
20: [] _12_ [Bk,Bk,Oc,Oc,Bk,Bk,Bk,Bk,Bk]
=>
21: [] _0_ [Bk,Bk,Oc,Oc,Bk,Bk,Bk,Bk,Bk]

 *)

(*  Commented definition of tm_erase_right_then_dblBk_left

let
tm_erase_right_then_dblBk_left = from_raw [
  -- 'check the left tape':
  (L, 2),(L, 2), -- 1   one step left
  (L, 3),(R, 5), -- 2   on Bk do one more step left, on Oc right towards 'check the right tape'
  (R, 4),(R, 5), -- 3   on 2nd Bk right to towards termination, on Oc right towards 'check the right tape'
  (R, 0),(R, 0), -- 4   one step right and terminate
  (R, 6),(R, 6), -- 5   one more step right to erase path
  -- 'check the right tape':
  (R, 7),(WB,6), -- 6   on Bk goto loop 'erase all to the right', on Oc erase
  --
  (R, 9),(WB,8), -- 7   loop 'erase all to the right': on Bk leave loop, on Oc erase
  (R, 7),(R, 7), -- 8   move right and continue loop 'erase all to the right'
  (L,10),(WB,8), -- 9   on 2nd Bk start loop 'move to left until Oc', on Oc continue 'erase all to the right'
  --
  (L,10),(L,11), -- 10  loop 'move to left until Oc': on Bk continue loop 'move to left until Oc', on Oc goto loop 'move left until DblBk'
  --
  (L,12),(L,11), -- 11  loop 'move left until DblBk': on 1st Bk move once more to the left, on Oc continue loop  'move left until DblBk' 
  (WB,0),(L,11)  -- 12  on 2nd Bk stop, on Oc (possible in generic case) continue loop 'move left until DblBk'
  ]

-- Note:
-- In a more generic context, the 'move left until DblBk' may see an Oc in state 12.
-- However, in our context of tm_check_for_one_arg there cannot be an Oc in state 12.

*)

definition 
  tm_erase_right_then_dblBk_left :: "instr list"
  where
    "tm_erase_right_then_dblBk_left \<equiv>
    [ (L, 2),(L, 2),
      (L, 3),(R, 5),
      (R, 4),(R, 5),
      (R, 0),(R, 0),
      (R, 6),(R, 6),
      
      (R, 7),(WB,6),
      (R, 9),(WB,8),

      (R, 7),(R, 7),
      (L,10),(WB,8),

      (L,10),(L,11),

      (L,12),(L,11),
      (WB,0),(L,11)
    ]"


(* Partial and total correctness for tm_erase_right_then_dblBk_left
 *
 * The leading 2 symbols on the left tape are used to differentiate!
 *
 * [Bk,Bk] \<longrightarrow> DO NOTHING path
 * [Bk,Oc] \<longrightarrow> ERASE path
 *
*)

(* ----------------------------------------------------------------- *)
(* DO NOTHING path tm_erase_right_then_dblBk_left_dnp                *)
(* Sequence of states on the DO NOTHING path: 1,2,3 then 4, 0        *)
(* ----------------------------------------------------------------- *)
(*
 *   "\<lbrace> \<lambda>tap. tap = ([], r ) \<rbrace> 
 *      tm_erase_right_then_dblBk_left
 *    \<lbrace> \<lambda>tap. tap = ([Bk,Bk], r ) \<rbrace>"
 *)

(* Definition of invariants for the DO_NOTHING path *)

fun
  inv_tm_erase_right_then_dblBk_left_dnp_s0 :: "(cell list) \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_erase_right_then_dblBk_left_dnp_s1 :: "(cell list) \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_erase_right_then_dblBk_left_dnp_s2 :: "(cell list) \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_erase_right_then_dblBk_left_dnp_s3 :: "(cell list) \<Rightarrow> tape \<Rightarrow> bool" and
  inv_tm_erase_right_then_dblBk_left_dnp_s4 :: "(cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_dnp_s0 CR (l, r) = (l = [Bk, Bk] \<and> CR = r)"
  | "inv_tm_erase_right_then_dblBk_left_dnp_s1 CR (l, r) = (l = []       \<and> CR = r)"
  | "inv_tm_erase_right_then_dblBk_left_dnp_s2 CR (l, r) = (l = []       \<and> r = Bk#CR)"
  | "inv_tm_erase_right_then_dblBk_left_dnp_s3 CR (l, r) = (l = []       \<and> r = Bk#Bk#CR)"
  | "inv_tm_erase_right_then_dblBk_left_dnp_s4 CR (l, r) = (l = [Bk]     \<and> r = Bk#CR)"


fun inv_tm_erase_right_then_dblBk_left_dnp :: "(cell list) \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_dnp CR (s, tap) = 
        (if s = 0 then inv_tm_erase_right_then_dblBk_left_dnp_s0 CR tap else
         if s = 1 then inv_tm_erase_right_then_dblBk_left_dnp_s1 CR tap else
         if s = 2 then inv_tm_erase_right_then_dblBk_left_dnp_s2 CR tap else
         if s = 3 then inv_tm_erase_right_then_dblBk_left_dnp_s3 CR tap else
         if s = 4 then inv_tm_erase_right_then_dblBk_left_dnp_s4 CR tap
         else False)"

lemma tm_erase_right_then_dblBk_left_dnp_cases: 
  fixes s::nat
  assumes "inv_tm_erase_right_then_dblBk_left_dnp CR (s,l,r)"
    and "s=0 \<Longrightarrow> P"
    and "s=1 \<Longrightarrow> P"
    and "s=2 \<Longrightarrow> P"
    and "s=3 \<Longrightarrow> P"
    and "s=4 \<Longrightarrow> P"
  shows "P"
proof -
  have "s < 5"
  proof (rule ccontr)
    assume "\<not> s < 5"
    with \<open>inv_tm_erase_right_then_dblBk_left_dnp CR (s,l,r)\<close> show False by auto
  qed
  then have "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3  \<or> s = 4" by auto
  with assms show ?thesis by auto
qed

lemma inv_tm_erase_right_then_dblBk_left_dnp_step: 
  assumes "inv_tm_erase_right_then_dblBk_left_dnp CR cf" 
  shows "inv_tm_erase_right_then_dblBk_left_dnp CR (step0 cf tm_erase_right_then_dblBk_left)"
proof (cases cf)
  case (fields s l r)
  then have cf_cases: "cf = (s, l, r)" .
  show "inv_tm_erase_right_then_dblBk_left_dnp CR (step0 cf tm_erase_right_then_dblBk_left)"
  proof (rule tm_erase_right_then_dblBk_left_dnp_cases)
    from cf_cases and assms
    show "inv_tm_erase_right_then_dblBk_left_dnp CR (s, l, r)" by auto
  next
    assume "s = 0"
    with cf_cases and assms
    show ?thesis by (auto simp add: tm_erase_right_then_dblBk_left_def)
  next
    assume "s = 1"
    with cf_cases and assms
    have "l = []"
      by auto
    show ?thesis
    proof (cases r)
      case Nil
      then have "r = []" .
      with assms and cf_cases and \<open>s = 1\<close> show ?thesis
        by (auto simp add: tm_erase_right_then_dblBk_left_def step.simps steps.simps)
    next
      case (Cons a rs)
      then have "r = a # rs" .
      show ?thesis
      proof (cases a)
        case Bk
        with assms and cf_cases and \<open>s = 1\<close> and \<open>r = a # rs\<close> show ?thesis
          by (auto simp add: tm_erase_right_then_dblBk_left_def step.simps steps.simps)
      next
        case Oc
        with assms and cf_cases and \<open>s = 1\<close> and \<open>r = a # rs\<close> show ?thesis
          by (auto simp add: tm_erase_right_then_dblBk_left_def step.simps steps.simps)
      qed
    qed
  next
    assume "s = 2"
    with cf_cases and assms
    have "l = [] \<and> r = Bk#CR" by auto

    then have "step0 (2, [], Bk#CR) tm_erase_right_then_dblBk_left = (3, [], Bk# Bk # CR)"
      by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

    moreover have "inv_tm_erase_right_then_dblBk_left_dnp CR (3, [], Bk# Bk # CR)"
    proof -
      from \<open>l = [] \<and> r = Bk#CR\<close>
      show "inv_tm_erase_right_then_dblBk_left_dnp CR (3, [], Bk# Bk # CR)" by auto
    qed

    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 2\<close> and \<open>l = [] \<and> r = Bk#CR\<close>
      by auto
  next
    assume "s = 3"
    with cf_cases and assms
    have "l = [] \<and> r = Bk#Bk#CR"
      by auto

    then have "step0 (3, [], Bk#Bk#CR) tm_erase_right_then_dblBk_left = (4, [Bk], Bk # CR)"
      by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

    moreover have "inv_tm_erase_right_then_dblBk_left_dnp CR (4, [Bk], Bk # CR)"
    proof -
      from \<open>l = [] \<and> r = Bk#Bk#CR\<close>
      show "inv_tm_erase_right_then_dblBk_left_dnp CR (4, [Bk], Bk # CR)" by auto
    qed

    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 3\<close> and \<open>l = [] \<and> r = Bk#Bk#CR\<close>
      by auto
  next
    assume "s = 4"
    with cf_cases and assms
    have "l = [Bk] \<and> r = Bk#CR"
      by auto

    then have "step0 (4, [Bk], Bk#CR) tm_erase_right_then_dblBk_left = (0, [Bk,Bk], CR)"
      by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

    moreover have "inv_tm_erase_right_then_dblBk_left_dnp CR (0, [Bk,Bk], CR)"
    proof -
      from \<open>l = [Bk] \<and> r = Bk#CR\<close>
      show "inv_tm_erase_right_then_dblBk_left_dnp  CR (0, [Bk,Bk], CR)" by auto
    qed

    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 4\<close> and \<open>l = [Bk] \<and> r = Bk#CR\<close>
      by auto
  qed
qed

lemma inv_tm_erase_right_then_dblBk_left_dnp_steps: 
  assumes "inv_tm_erase_right_then_dblBk_left_dnp CR cf" 
  shows "inv_tm_erase_right_then_dblBk_left_dnp CR (steps0 cf tm_erase_right_then_dblBk_left stp)"
proof (induct stp)
  case 0
  with assms show ?case
    by (auto simp add: inv_tm_erase_right_then_dblBk_left_dnp_step step.simps steps.simps)
next
  case (Suc stp)
  with assms show ?case
    using inv_tm_erase_right_then_dblBk_left_dnp_step step_red by auto 
qed


lemma tm_erase_right_then_dblBk_left_dnp_partial_correctness:
  assumes "\<exists>stp. is_final (steps0 (1, [], r) tm_erase_right_then_dblBk_left stp)"
  shows "\<lbrace> \<lambda>tap. tap = ([], r ) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. tap = ([Bk,Bk], r ) \<rbrace>"
proof (rule Hoare_consequence)
  show "(\<lambda>tap. tap = ([], r) ) \<mapsto> (\<lambda>tap. tap = ([], r) )"
    by auto
next
  show "inv_tm_erase_right_then_dblBk_left_dnp_s0 r  \<mapsto> (\<lambda>tap. tap = ([Bk,Bk], r ))"
    by (simp add: assert_imp_def  tape_of_list_def tape_of_nat_def)
next
  show "\<lbrace>\<lambda>tap. tap = ([], r)\<rbrace>
         tm_erase_right_then_dblBk_left
        \<lbrace>inv_tm_erase_right_then_dblBk_left_dnp_s0 r \<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r'':: "cell list"
    assume major: "(l, r'') = ([], r)"
    show "\<exists>stp. is_final (steps0 (1, l, r'') tm_erase_right_then_dblBk_left stp) \<and>
                inv_tm_erase_right_then_dblBk_left_dnp_s0 r holds_for steps0 (1, l, r'') tm_erase_right_then_dblBk_left stp"
    proof -
      from major and assms have "\<exists>stp. is_final (steps0 (1, l, r'') tm_erase_right_then_dblBk_left stp)" by auto
      then obtain stp where
        w_stp: "is_final (steps0 (1, l, r'') tm_erase_right_then_dblBk_left stp)" by blast

      moreover have "inv_tm_erase_right_then_dblBk_left_dnp_s0 r holds_for steps0 (1, l, r'') tm_erase_right_then_dblBk_left stp"
      proof -
        have "inv_tm_erase_right_then_dblBk_left_dnp r (1, l, r'')"
          by (simp add: major tape_of_list_def tape_of_nat_def)

        then have "inv_tm_erase_right_then_dblBk_left_dnp r (steps0 (1, l, r'') tm_erase_right_then_dblBk_left stp)"
          using inv_tm_erase_right_then_dblBk_left_dnp_steps by auto

        then show ?thesis
          by (smt holds_for.elims(3) inv_tm_erase_right_then_dblBk_left_dnp.simps is_final_eq w_stp)
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed

(* Total correctness of tm_erase_right_then_dblBk_left for DO NOTHING path *)

(* Assemble a lexicographic measure function  for the DO NOTHING path *)

definition measure_tm_erase_right_then_dblBk_left_dnp :: "(config \<times> config) set"
  where
    "measure_tm_erase_right_then_dblBk_left_dnp = measures [
      \<lambda>(s, l, r). (if s = 0 then 0 else 5 - s)
      ]"

lemma wf_measure_tm_erase_right_then_dblBk_left_dnp: "wf measure_tm_erase_right_then_dblBk_left_dnp"
  unfolding measure_tm_erase_right_then_dblBk_left_dnp_def
  by (auto)

lemma measure_tm_erase_right_then_dblBk_left_dnp_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_tm_erase_right_then_dblBk_left_dnp\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_tm_erase_right_then_dblBk_left_dnp
  by (metis wf_iff_no_infinite_down_chain)


lemma tm_erase_right_then_dblBk_left_dnp_halts:
  "\<exists>stp. is_final (steps0 (1, [], r) tm_erase_right_then_dblBk_left stp)"
proof (induct rule: measure_tm_erase_right_then_dblBk_left_dnp_induct)
  case (Step stp)
  then have not_final: "\<not> is_final (steps0 (1, [], r) tm_erase_right_then_dblBk_left stp)" .

  have INV: "inv_tm_erase_right_then_dblBk_left_dnp r (steps0 (1, [], r) tm_erase_right_then_dblBk_left stp)"
  proof (rule_tac inv_tm_erase_right_then_dblBk_left_dnp_steps)
    show  "inv_tm_erase_right_then_dblBk_left_dnp r (1, [], r)"
      by (simp add: tape_of_list_def tape_of_nat_def  )
  qed

  have SUC_STEP_RED: "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =
        step0 (steps0 (1, [], r) tm_erase_right_then_dblBk_left stp) tm_erase_right_then_dblBk_left"
    by (rule step_red)

  show "( steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp),
          steps0 (1, [], r) tm_erase_right_then_dblBk_left stp
        ) \<in> measure_tm_erase_right_then_dblBk_left_dnp"

  proof (cases "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp")
    case (fields s l r2)
    then have
      cf_cases: "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (s, l, r2)" .
    show ?thesis
    proof (rule tm_erase_right_then_dblBk_left_dnp_cases)
      from INV and cf_cases
      show "inv_tm_erase_right_then_dblBk_left_dnp r (s, l, r2)" by auto
    next
      assume "s=0" (* not possible *)
      with cf_cases not_final
      show ?thesis by auto
    next
      assume "s=1"
      show ?thesis
      proof (cases r)
        case Nil
        then have "r = []" .
        from cf_cases and \<open>s=1\<close>
        have "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (1, l, r2)"
          by auto
        with cf_cases  and \<open>s=1\<close> and INV
        have "l = [] \<and> r = r2"
          by auto          
        with cf_cases and \<open>s=1\<close> and SUC_STEP_RED
        have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (1, [],  r) tm_erase_right_then_dblBk_left"
          by auto
        also with \<open>r = []\<close> and \<open>l = [] \<and> r = r2\<close> have "... = (2,[],Bk#r2)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)

        finally have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =  (2,[],Bk#r2)"
          by auto

        with \<open>steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (1, l, r2)\<close>
        show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_dnp_def)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        then show ?thesis
        proof (cases a)
          case Bk
          then have "a = Bk" .
          from cf_cases and \<open>s=1\<close>
          have "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (1, l, r2)"
            by auto
          with cf_cases  and \<open>s=1\<close> and INV
          have "l = [] \<and> r = r2"
            by auto          
          with cf_cases and \<open>s=1\<close> and SUC_STEP_RED
          have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (1, [],  r) tm_erase_right_then_dblBk_left"
            by auto
          also with \<open>r = a # rs\<close> and \<open>a=Bk\<close> and \<open>l = [] \<and> r = r2\<close> have "... = (2,[],Bk#r2)"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)

          finally have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =  (2,[],Bk#r2)"
            by auto

          with \<open>steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (1, l, r2)\<close>
          show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_dnp_def)
        next
          case Oc
          then have "a = Oc" .
          from cf_cases and \<open>s=1\<close>
          have "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (1, l, r2)"
            by auto
          with cf_cases  and \<open>s=1\<close> and INV
          have "l = [] \<and> r = r2"
            by auto          
          with cf_cases and \<open>s=1\<close> and SUC_STEP_RED
          have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (1, [],  r) tm_erase_right_then_dblBk_left"
            by auto
          also with \<open>r = a # rs\<close> and \<open>a=Oc\<close> and \<open>l = [] \<and> r = r2\<close> have "... = (2,[],Bk#r2)"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)

          finally have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =  (2,[],Bk#r2)"
            by auto

          with \<open>steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (1, l, r2)\<close>
          show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_dnp_def)
        qed
      qed
    next
      assume "s=2"
      with cf_cases
      have "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (2, l, r2)"
        by auto

      with cf_cases  and \<open>s=2\<close> and INV
      have "(l = []       \<and> r2 = Bk#r)"
        by auto      

      with cf_cases and \<open>s=2\<close> and SUC_STEP_RED
      have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (2, l,  r2) tm_erase_right_then_dblBk_left"
        by auto

      also with \<open>s=2\<close> and \<open>(l = []       \<and> r2 = Bk#r)\<close> have "... = (3,[],Bk#r2)"
        by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)

      finally have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =  (3,[],Bk#r2)"
        by auto

      with \<open>steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (2, l, r2)\<close>
      show ?thesis
        by (auto simp add: measure_tm_erase_right_then_dblBk_left_dnp_def)
    next
      assume "s=3"
      with cf_cases
      have "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (3, l, r2)"
        by auto

      with cf_cases  and \<open>s=3\<close> and INV
      have "(l = []       \<and> r2 = Bk#Bk#r)"
        by auto      

      with cf_cases and \<open>s=3\<close> and SUC_STEP_RED
      have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (3, l,  r2) tm_erase_right_then_dblBk_left"
        by auto

      also with \<open>s=3\<close> and \<open>(l = []       \<and> r2 = Bk#Bk#r)\<close> have "... = (4,[Bk],Bk#r)"
        by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)

      finally have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =  (4,[Bk],Bk#r)"
        by auto

      with \<open>steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (3, l, r2)\<close>
      show ?thesis
        by (auto simp add: measure_tm_erase_right_then_dblBk_left_dnp_def)
    next
      assume "s=4"
      with cf_cases
      have "steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (4, l, r2)"
        by auto

      with cf_cases  and \<open>s=4\<close> and INV
      have "(l = [Bk]       \<and> r2 = Bk#r)"
        by auto      

      with cf_cases and \<open>s=4\<close> and SUC_STEP_RED
      have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (4, l,  r2) tm_erase_right_then_dblBk_left"
        by auto

      also with \<open>s=4\<close> and \<open>(l = [Bk]       \<and> r2 = Bk#r)\<close> have "... = (0,[Bk,Bk],r)"
        by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)

      finally have "steps0 (1, [], r) tm_erase_right_then_dblBk_left (Suc stp) =  (0,[Bk,Bk],r)"
        by auto

      with \<open>steps0 (1, [], r) tm_erase_right_then_dblBk_left stp = (4, l, r2)\<close>
      show ?thesis
        by (auto simp add: measure_tm_erase_right_then_dblBk_left_dnp_def)
    qed
  qed
qed

lemma tm_erase_right_then_dblBk_left_dnp_total_correctness:
 "\<lbrace> \<lambda>tap. tap = ([], r ) \<rbrace> 
    tm_erase_right_then_dblBk_left
  \<lbrace> \<lambda>tap. tap = ([Bk,Bk], r ) \<rbrace>"
proof (rule tm_erase_right_then_dblBk_left_dnp_partial_correctness)
  show "\<exists>stp. is_final (steps0 (1, [], r) tm_erase_right_then_dblBk_left stp)"
    using  tm_erase_right_then_dblBk_left_dnp_halts by auto
qed

(* ----------------------------------------------------------------- *)
(* ERASE path tm_erase_right_then_dblBk_left_erp                     *)
(* Sequence of states on the      ERASE path: 1,2,3 then 5...        *)
(* ----------------------------------------------------------------- *)
(*
 *        \<lbrace> \<lambda>tap. tap = (Bk# rev(<hd nl>), <tl nl>) \<rbrace> 
 *          tm_erase_right_then_dblBk_left
 *        \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (<hd nl>) @ [Bk] @ Bk \<up> rex ) \<rbrace>"
 *)

(* Definition of invariants for the ERASE path: had to split definitions *)

fun inv_tm_erase_right_then_dblBk_left_erp_s1  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s1  CL CR (l, r) =
        (l = [Bk,Oc] @ CL \<and> r = CR)"
fun inv_tm_erase_right_then_dblBk_left_erp_s2  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s2  CL CR (l, r) = 
        (l = [Oc]    @ CL \<and> r = Bk#CR)"
fun inv_tm_erase_right_then_dblBk_left_erp_s3  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s3  CL CR (l, r) = 
        (l =           CL \<and> r = Oc#Bk#CR)"

fun inv_tm_erase_right_then_dblBk_left_erp_s5  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s5  CL CR (l, r) = 
        (l = [Oc]    @ CL \<and> r = Bk#CR)"

fun inv_tm_erase_right_then_dblBk_left_erp_s6  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s6  CL CR (l, r) =
        (l = [Bk,Oc] @ CL \<and> ( (CR = [] \<and> r = CR) \<or> (CR \<noteq> [] \<and> (r = CR \<or> r = Bk # tl CR)) )  )"

(* ENHANCE: simplify invariant of s6 (simpler to use for proof by cases

    "inv_tm_erase_right_then_dblBk_left_erp_s6  CL CR (l, r) =
         (l = [Bk,Oc] @ CL \<and> CR = [] \<and> r = CR \<or>
          l = [Bk,Oc] @ CL \<and> CR \<noteq> [] \<and> r = Oc # tl CR \<or>
          l = [Bk,Oc] @ CL \<and> CR \<noteq> [] \<and> r = Bk # tl CR   )"
*)

fun inv_tm_erase_right_then_dblBk_left_erp_s7  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s7  CL CR (l, r) =
        ((\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs. CR = rs @ r) )"

fun inv_tm_erase_right_then_dblBk_left_erp_s8  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s8  CL CR (l, r) = 
        ((\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and>
         (\<exists>rs1 rs2. CR = rs1 @ [Oc] @ rs2 \<and> r = Bk#rs2) )"

fun inv_tm_erase_right_then_dblBk_left_erp_s9  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s9  CL CR (l, r) = 
        ((\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs. CR = rs @ [Bk] @ r \<or> CR = rs \<and> r = []) )"

fun inv_tm_erase_right_then_dblBk_left_erp_s10 :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s10  CL CR (l, r) = 
        (
          (\<exists>lex rex. l = Bk \<up> lex @ [Bk,Oc] @ CL \<and> r = Bk \<up> Suc rex) \<or>
          (\<exists>rex. l = [Oc] @ CL \<and> r = Bk \<up> Suc rex) \<or>
          (\<exists>rex. l = CL \<and> r = Oc # Bk \<up> Suc rex)
        )"

fun inv_tm_erase_right_then_dblBk_left_erp_s11 :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s11  CL CR (l, r) = 
        (
          (\<exists>rex.         l = []         \<and> r = Bk# rev CL    @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc))              \<or>

          (\<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk ) \<or>
          (\<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc ) \<or>

          (\<exists>rex.         l = [Bk]       \<and> r = rev [Oc]      @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]) \<or>

          (\<exists>rex ls1 ls2. l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc] ) \<or>
          (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk] ) \<or>
          (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc] ) \<or>

          (\<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> tl ls1 \<noteq> [])

       )"

(*

YYYY1'    (\<exists>rex.         l =        []  \<and> r = Bk# rev CL    @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc) ) \<or>       (s11 \<longrightarrow> s11)                  

YYYY2'    (\<exists>rex.         l =        []  \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> []  \<and> last CL = Bk) \<or>  (s11 \<longrightarrow> s11)
YYYY2''   (\<exists>rex.         l =        []  \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> []  \<and> last CL = Oc) \<or>  (s11 \<longrightarrow> s11)

YYYY5     (\<exists>rex.         l =      [Bk]  \<and> r = rev [Oc] @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]) \<or>            (s10 \<longrightarrow> s11)

YYYY6     (\<exists>rex ls1 ls2. l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc] ) \<or>                           (s10 \<longrightarrow> s11)
YYYY3     (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk] ) \<or>                           (s10 \<longrightarrow> s11)
YYYY7     (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc] ) \<or>                           (s10 \<longrightarrow> s11)
YYYY8     (\<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> tl ls1 \<noteq> [])              (s11 \<longrightarrow> s11)

*)

fun inv_tm_erase_right_then_dblBk_left_erp_s12 :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s12  CL CR (l, r) = 
        (
          (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc) \<or>

          (\<exists>rex. l = []  \<and> r = Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk) \<or>
          (\<exists>rex. l = []  \<and> r = Bk#Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc) ) \<or>
          False
        )"

(*
     YYYY4      (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc)

     YYYY6'''   (\<exists>rex. l = []  \<and> r = Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk)

     YYYY9      (\<exists>rex. l = []  \<and> r = Bk#Bk#rev CL @ Oc # Bk \<up> Suc rex) \<or>

*)

fun inv_tm_erase_right_then_dblBk_left_erp_s0  :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp_s0  CL CR (l, r) =
       (
        (\<exists>rex. l = [] \<and>  r = [Bk, Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex \<and> (CL = [] \<or> last CL = Oc)  ) \<or>
        (\<exists>rex. l = [] \<and>  r = [Bk]     @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex \<and>  CL \<noteq> [] \<and> last CL = Bk )
       )"

fun inv_tm_erase_right_then_dblBk_left_erp :: "(cell list) \<Rightarrow> (cell list) \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_tm_erase_right_then_dblBk_left_erp CL CR (s, tap) = 
        (if s = 0 then inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR tap else
         if s = 1 then inv_tm_erase_right_then_dblBk_left_erp_s1 CL CR tap else
         if s = 2 then inv_tm_erase_right_then_dblBk_left_erp_s2 CL CR tap else
         if s = 3 then inv_tm_erase_right_then_dblBk_left_erp_s3 CL CR tap else
         if s = 5 then inv_tm_erase_right_then_dblBk_left_erp_s5 CL CR tap else
         if s = 6 then inv_tm_erase_right_then_dblBk_left_erp_s6 CL CR tap else
         if s = 7 then inv_tm_erase_right_then_dblBk_left_erp_s7 CL CR tap else
         if s = 8 then inv_tm_erase_right_then_dblBk_left_erp_s8 CL CR tap else
         if s = 9 then inv_tm_erase_right_then_dblBk_left_erp_s9 CL CR tap else
         if s = 10 then inv_tm_erase_right_then_dblBk_left_erp_s10 CL CR tap else
         if s = 11 then inv_tm_erase_right_then_dblBk_left_erp_s11 CL CR tap else
         if s = 12 then inv_tm_erase_right_then_dblBk_left_erp_s12 CL CR tap
         else False)"

lemma tm_erase_right_then_dblBk_left_erp_cases: 
  fixes s::nat
  assumes "inv_tm_erase_right_then_dblBk_left_erp CL CR (s,l,r)"
    and "s=0 \<Longrightarrow> P"
    and "s=1 \<Longrightarrow> P"
    and "s=2 \<Longrightarrow> P"
    and "s=3 \<Longrightarrow> P"
    and "s=5 \<Longrightarrow> P"
    and "s=6 \<Longrightarrow> P"
    and "s=7 \<Longrightarrow> P"
    and "s=8 \<Longrightarrow> P"
    and "s=9 \<Longrightarrow> P"
    and "s=10 \<Longrightarrow> P"
    and "s=11 \<Longrightarrow> P"
    and "s=12 \<Longrightarrow> P"
  shows "P"
proof -
  have "s < 4 \<or> 4 < s \<and> s < 13"
  proof (rule ccontr)
    assume "\<not> (s < 4 \<or> 4 < s \<and> s < 13)"
    with \<open>inv_tm_erase_right_then_dblBk_left_erp CL CR (s,l,r)\<close> show False by auto
  qed
  then have "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3  \<or> s = 5  \<or> s = 6 \<or> s = 7 \<or>
             s = 8 \<or> s = 9 \<or> s = 10 \<or> s = 11 \<or> s = 12"
    by arith
  with assms show ?thesis by auto
qed

(* -------------- step - lemma for the invariants of the ERASE path of tm_erase_right_then_dblBk_left ------------------ *)

lemma inv_tm_erase_right_then_dblBk_left_erp_step: 
  assumes "inv_tm_erase_right_then_dblBk_left_erp CL CR cf"
    and "noDblBk CL"
    and "noDblBk CR"
  shows "inv_tm_erase_right_then_dblBk_left_erp CL CR (step0 cf tm_erase_right_then_dblBk_left)"
proof (cases cf)
  case (fields s l r)
  then have cf_cases: "cf = (s, l, r)" .
  show "inv_tm_erase_right_then_dblBk_left_erp CL CR (step0 cf tm_erase_right_then_dblBk_left)"
  proof (rule tm_erase_right_then_dblBk_left_erp_cases)
    from cf_cases and assms
    show "inv_tm_erase_right_then_dblBk_left_erp CL CR (s, l, r)" by auto
  next
    assume "s = 1"
    with cf_cases and assms
    have "(l = [Bk,Oc] @ CL \<and> r = CR)" by auto
    show ?thesis
    proof (cases r)
      case Nil
      then have "r = []" .
      with assms and cf_cases and \<open>s = 1\<close> show ?thesis
        by (auto simp add: tm_erase_right_then_dblBk_left_def step.simps steps.simps)
    next
      case (Cons a rs)
      then have "r = a # rs" .
      show ?thesis
      proof (cases a)
        case Bk
        with assms and cf_cases and \<open>r = a # rs\<close> and \<open>s = 1\<close> show ?thesis
          by (auto simp add: tm_erase_right_then_dblBk_left_def step.simps steps.simps)
      next
        case Oc
        with assms and cf_cases and \<open>r = a # rs\<close> and \<open>s = 1\<close> show ?thesis
          by (auto simp add: tm_erase_right_then_dblBk_left_def step.simps steps.simps)
      qed
    qed
  next
    assume "s = 2"
    with cf_cases and assms
    have "l = [Oc] @ CL \<and> r = Bk#CR" by auto

    then have "step0 (2, [Oc]    @ CL, Bk#CR) tm_erase_right_then_dblBk_left = (3, CL, Oc# Bk # CR)"
      by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

    moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (3, CL, Oc# Bk # CR)"
      by auto

    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 2\<close> and \<open>l = [Oc] @ CL \<and> r = Bk#CR\<close>
      by auto
  next
    assume "s = 3"
    with cf_cases and assms
    have "l = CL \<and> r = Oc#Bk#CR" by auto

    then have "step0 (3, CL, Oc#Bk#CR) tm_erase_right_then_dblBk_left = (5, Oc#CL, Bk # CR)"
      by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

    moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (5, Oc#CL, Bk # CR)"
      by auto
    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 3\<close> and \<open>l = CL \<and> r = Oc#Bk#CR\<close>
      by auto
  next
    assume "s = 5"
    with cf_cases and assms
    have "l = [Oc] @ CL \<and> r = Bk#CR" by auto

    then have "step0 (5, [Oc] @ CL, Bk#CR) tm_erase_right_then_dblBk_left = (6, Bk#Oc#CL, CR)"
      by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

    moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (6, Bk#Oc#CL, CR)"
    proof (cases CR)
      case Nil
      then show ?thesis by auto
    next
      case (Cons a cs)
      then have "CR = a # cs" .

      with \<open>l = [Oc] @ CL \<and> r = Bk#CR\<close> and \<open>s = 5\<close> and \<open>CR = a # cs\<close>
      have  "inv_tm_erase_right_then_dblBk_left_erp_s6 CL CR (Bk#Oc#CL, CR)"        
        by simp
      with \<open>s=5\<close> 
      show "inv_tm_erase_right_then_dblBk_left_erp CL CR (6, Bk#Oc#CL, CR)"
        by auto     
    qed
    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 5\<close> and \<open>l = [Oc] @ CL \<and> r = Bk#CR\<close>
      by auto
  next
    assume "s = 6"
    with cf_cases and assms
    have "l = [Bk,Oc] @ CL" and "( (CR = [] \<and> r = CR) \<or> (CR \<noteq> [] \<and> (r = CR \<or> r = Bk # tl CR)) )"
      by auto
    from \<open>( (CR = [] \<and> r = CR) \<or> (CR \<noteq> [] \<and> (r = CR \<or> r = Bk # tl CR)) )\<close> show ?thesis
    proof 
      assume "CR = [] \<and> r = CR"
      have "step0 (6, [Bk,Oc] @ CL, []) tm_erase_right_then_dblBk_left = (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, [])"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

      moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, [])"
        by auto
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 6\<close> and \<open>l = [Bk,Oc] @ CL\<close> and \<open>CR = [] \<and> r = CR\<close>
        by auto
    next
      assume "CR \<noteq> [] \<and> (r = CR \<or> r = Bk # tl CR)"
      then have "CR \<noteq> []" and "r = CR \<or> r = Bk # tl CR" by auto
      from \<open>r = CR \<or> r = Bk # tl CR\<close>
      show "inv_tm_erase_right_then_dblBk_left_erp CL CR (step0 cf tm_erase_right_then_dblBk_left)"
      proof
        assume "r = CR"
        show "inv_tm_erase_right_then_dblBk_left_erp CL CR (step0 cf tm_erase_right_then_dblBk_left)"
        proof (cases r)
          case Nil
          then have "r = []" .
          then have "step0 (6, [Bk,Oc] @ CL, []) tm_erase_right_then_dblBk_left = (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, [])"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, [])"
            by auto
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 6\<close> and \<open>l = [Bk,Oc] @ CL\<close> and \<open>r = []\<close> 
            by auto
        next
          case (Cons a rs')
          then have "r = a # rs'" .
          with \<open>r = CR\<close>  have "r = a # tl CR" by auto
          show ?thesis
          proof (cases a)
            case Bk
            then have "a = Bk" .
            then have "step0 (6, [Bk,Oc] @ CL, Bk # tl CR) tm_erase_right_then_dblBk_left = (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, tl CR)"
              by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

            moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, tl CR)"
            proof -
              from \<open>CR \<noteq> []\<close> and \<open>r = CR\<close> and \<open>a = Bk\<close> and \<open>r = a # tl CR\<close> and \<open>l = [Bk,Oc] @ CL\<close> 
              have "inv_tm_erase_right_then_dblBk_left_erp_s7 CL CR (Bk \<up> Suc 0 @ [Bk,Oc] @ CL, tl CR)"                
                by (metis append.left_neutral append_Cons  empty_replicate inv_tm_erase_right_then_dblBk_left_erp_s7.simps
                    replicate_Suc )
              then show "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, tl CR)" by auto
            qed
            ultimately show ?thesis
              using \<open>CR \<noteq> []\<close> and \<open>r = CR\<close> and \<open>a = Bk\<close> and \<open>r = a # tl CR\<close> and \<open>l = [Bk,Oc] @ CL\<close> and \<open>s = 6\<close> and cf_cases
              by auto
          next
            case Oc
            then have "a = Oc" .
            then have "step0 (6, [Bk,Oc] @ CL, Oc # rs') tm_erase_right_then_dblBk_left = (6, [Bk,Oc] @ CL, Bk # rs')"
              by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

            moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (6, [Bk,Oc] @ CL, Bk # rs')"
            proof -
              from \<open>CR \<noteq> []\<close> and \<open>r = CR\<close> and \<open>a = Oc\<close> and \<open>r = a # tl CR\<close> and \<open>l = [Bk,Oc] @ CL\<close> 
              have "inv_tm_erase_right_then_dblBk_left_erp_s6 CL CR ([Bk,Oc] @ CL, Bk # rs')"
                using inv_tm_erase_right_then_dblBk_left_erp_s6.simps list.sel(3) local.Cons by blast
              then show "inv_tm_erase_right_then_dblBk_left_erp CL CR (6, [Bk,Oc] @ CL, Bk # rs')"
                by auto
            qed
            ultimately show ?thesis
              using \<open>CR \<noteq> []\<close> and \<open>r = CR\<close> and \<open>a = Oc\<close> and \<open>r = a # tl CR\<close> and \<open>l = [Bk,Oc] @ CL\<close> and \<open>s = 6\<close> and cf_cases
              by auto
          qed
        qed
      next
        assume "r = Bk # tl CR"

        have "step0 (6, [Bk,Oc] @ CL, Bk # tl CR) tm_erase_right_then_dblBk_left = (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, tl CR)"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

        moreover with \<open>CR \<noteq> []\<close> and \<open>r = Bk # tl CR\<close>
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, tl CR)"
        proof -
          have "(\<exists>lex. Bk \<up> Suc 0 @ [Bk,Oc] @ CL = Bk \<up> Suc lex @ [Bk,Oc] @ CL) " by blast
          moreover with \<open>CR \<noteq> []\<close> have "(\<exists>rs. CR = rs @ tl CR)"
            by (metis append_Cons append_Nil list.exhaust list.sel(3))
          ultimately 
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc 0 @ [Bk,Oc] @ CL, tl CR)"
            by auto
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 6\<close> and \<open>CR \<noteq> []\<close> and \<open>r = Bk # tl CR\<close> and \<open>l = [Bk,Oc] @ CL\<close> and cf_cases        
          by auto
      qed
    qed
  next
    assume "s = 7"
    with cf_cases and assms
    have "(\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs. CR = rs @ r)" by auto
    then obtain lex rs where
      w_lex_rs: "l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> CR = rs @ r" by blast
    show ?thesis
    proof (cases r)
      case Nil
      then have "r=[]" .
      with w_lex_rs have "CR = rs" by auto
      have "step0 (7, Bk \<up> Suc lex @ [Bk,Oc] @ CL, []) tm_erase_right_then_dblBk_left =
             (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, [])"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover with \<open>CR = rs\<close>
      have "inv_tm_erase_right_then_dblBk_left_erp CL CR (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, [])"
      proof -
        have "(\<exists>lex'. Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL = Bk \<up> Suc lex' @ [Bk,Oc] @ CL)" by blast
        moreover have "\<exists>rs. CR = rs" by auto
        ultimately
        show "inv_tm_erase_right_then_dblBk_left_erp CL CR (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, [])"
          by auto
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 7\<close> and w_lex_rs and \<open>CR = rs\<close> and \<open>r=[]\<close>
        by auto
    next
      case (Cons a rs')
      then have "r = a # rs'" .
      show ?thesis
      proof (cases a)
        case Bk
        then have "a = Bk" .
        with w_lex_rs and \<open>r = a # rs'\<close> have "CR = rs@(Bk#rs')" by auto

        have "step0 (7, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs') tm_erase_right_then_dblBk_left = (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs')"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
        moreover with \<open>CR = rs@(Bk#rs')\<close>
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs')"
        proof -
          have "(\<exists>lex'. Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL = Bk \<up> Suc lex' @ [Bk,Oc] @ CL)" by blast
          moreover with \<open>r = a # rs'\<close> and \<open>a = Bk\<close> and \<open>CR = rs@(Bk#rs')\<close> have "\<exists>rs. CR = rs @ [Bk] @ rs'" by auto
          ultimately
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs')"
            by auto
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 7\<close> and w_lex_rs and \<open>a = Bk\<close> and \<open>r = a # rs'\<close>
          by simp
      next
        case Oc
        then have "a = Oc" .
        with w_lex_rs and \<open>r = a # rs'\<close> have "CR = rs@(Oc#rs')" by auto

        have "step0 (7, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Oc#rs') tm_erase_right_then_dblBk_left = (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
        moreover  
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
        proof -
          have "(\<exists>lex'. Bk \<up> Suc lex @ [Bk,Oc] @ CL = Bk \<up> Suc lex' @ [Bk,Oc] @ CL)" by blast
          moreover with \<open>r = a # rs'\<close> and \<open>a = Oc\<close> and \<open>CR = rs@(Oc#rs')\<close>         
          have "\<exists>rs1 rs2. CR = rs1 @ [Oc] @ rs2 \<and> Bk#rs' = Bk#rs2" by auto
          ultimately
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
            by auto
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 7\<close> and w_lex_rs and \<open>a = Oc\<close> and \<open>r = a # rs'\<close>
          by simp
      qed
    qed
  next
    assume "s = 8"
    with cf_cases and assms
    have "((\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs1 rs2. CR = rs1 @ [Oc] @ rs2 \<and> r = Bk#rs2) )" by auto
    then obtain lex rs1 rs2 where
      w_lex_rs1_rs2: "l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> CR = rs1 @ [Oc] @ rs2 \<and> r = Bk#rs2"
      by blast
    have "step0 (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs2) tm_erase_right_then_dblBk_left = (7, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs2)"
      by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

    moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs2)"
    proof -
      have "(\<exists>lex'. Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL = Bk \<up> Suc lex' @ [Bk,Oc] @ CL)" by blast
      moreover have "\<exists>rs. CR = rs @ []" by auto
      ultimately
      show "inv_tm_erase_right_then_dblBk_left_erp CL CR (7, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs2)"
        using w_lex_rs1_rs2
        by auto
    qed
    ultimately show ?thesis
      using  assms and cf_cases and \<open>s = 8\<close> and w_lex_rs1_rs2
      by auto
  next
    assume "s = 9"
    with cf_cases and assms
    have "(\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs. CR = rs @ [Bk] @ r \<or> CR = rs \<and> r = [])" by auto
    then obtain lex rs where
      w_lex_rs: "l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> (CR = rs @ [Bk] @ r \<or> CR = rs \<and> r = [])" by blast

    then have "CR = rs @ [Bk] @ r \<or> CR = rs \<and> r = []" by auto
    then show ?thesis
    proof 
      assume "CR = rs \<and> r = []"
      have "step0 (9, Bk \<up> Suc lex @ [Bk,Oc] @ CL, []) tm_erase_right_then_dblBk_left
                = (10, Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover with \<open>CR = rs \<and> r = []\<close>
      have "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
      proof -
        from w_lex_rs and \<open>CR = rs \<and> r = []\<close>
        have "\<exists>lex' rex.  Bk \<up> lex @ [Bk,Oc] @ CL = Bk \<up> lex' @ [Bk,Oc] @ CL \<and> [Bk] = Bk \<up> Suc rex"
          by (simp)
        then show "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
          by auto
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 9\<close> and w_lex_rs and \<open>CR = rs \<and> r = []\<close>
        by auto
    next
      assume "CR = rs @ [Bk] @ r"
      show ?thesis
      proof (cases r)
        case Nil
        then have "r=[]" .
        have "step0 (9, Bk \<up> Suc lex @ [Bk,Oc] @ CL, []) tm_erase_right_then_dblBk_left
                = (10, Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
        moreover with \<open>CR = rs @ [Bk] @ r\<close>
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
        proof -
          from w_lex_rs and \<open>CR = rs @ [Bk] @ r\<close>
          have "\<exists>lex' rex.  Bk \<up> lex @ [Bk,Oc] @ CL = Bk \<up> lex' @ [Bk,Oc] @ CL \<and> [Bk] = Bk \<up> Suc rex"
            by (simp)
          with \<open>s=9\<close> show "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
            by auto
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 9\<close> and w_lex_rs and \<open>r=[]\<close>
          by auto
      next
        case (Cons a rs')
        then have "r = a # rs'" .
        show ?thesis
        proof (cases a)
          case Bk
          then have "a = Bk" .
          with \<open>CR = rs @ [Bk] @ r\<close> and \<open>r = a # rs'\<close> have "CR = rs @ [Bk] @ Bk # rs'" by auto
          moreover from assms  have "noDblBk CR" by auto
          ultimately have False using hasDblBk_L1 by auto
          then show ?thesis by auto
        next
          case Oc
          then have "a = Oc" .
          with \<open>CR = rs @ [Bk] @ r\<close> and \<open>r = a # rs'\<close> have "CR = rs @ [Bk] @ Oc # rs'" by auto

          have "step0 (9, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Oc # rs') tm_erase_right_then_dblBk_left
                = (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk # rs')"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

          moreover  
          have "inv_tm_erase_right_then_dblBk_left_erp CL CR (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk # rs')"
          proof -
            have "(\<exists>lex'. Bk \<up> Suc lex @ [Bk,Oc] @ CL = Bk \<up> Suc lex' @ [Bk,Oc] @ CL)" by blast
            moreover with \<open>r = a # rs'\<close> and \<open>a = Oc\<close> and \<open>CR = rs @ [Bk] @ Oc # rs'\<close>         
            have "\<exists>rs1 rs2. CR = rs1 @ [Oc] @ rs2 \<and> Bk#rs' = Bk#rs2" by auto
            ultimately
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
              by auto
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 9\<close> and w_lex_rs and \<open>a = Oc\<close> and \<open>r = a # rs'\<close>
            by simp
        qed
      qed
    qed
  next
    assume "s = 10"
    with cf_cases and assms
    have "(\<exists>lex rex. l = Bk \<up> lex @ [Bk,Oc] @ CL \<and> r = Bk \<up> Suc rex) \<or>
          (\<exists>rex. l = [Oc] @ CL \<and> r = Bk \<up> Suc rex) \<or>
          (\<exists>rex. l = CL \<and> r = Oc # Bk \<up> Suc rex)" by auto
    then obtain lex rex where
      w_lex_rex: "l = Bk \<up> lex @ [Bk,Oc] @ CL \<and> r = Bk \<up> Suc rex \<or>
                  l = [Oc] @ CL \<and> r = Bk \<up> Suc rex \<or>
                  l = CL \<and> r = Oc # Bk \<up> Suc rex" by blast
    then show ?thesis
    proof
      assume "l = Bk \<up> lex @ [Bk, Oc] @ CL \<and> r = Bk \<up> Suc rex"
      then have "l = Bk \<up> lex @ [Bk, Oc] @ CL" and "r = Bk \<up> Suc rex" by auto
      show ?thesis
      proof (cases lex)
        case 0
        with \<open>l = Bk \<up> lex @ [Bk, Oc] @ CL\<close> have "l = [Bk, Oc] @ CL" by auto
        have "step0 (10, [Bk, Oc] @ CL, Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                 = (10, [Oc] @ CL, Bk \<up> Suc (Suc rex))"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
        moreover
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, [Oc] @ CL, Bk \<up> Suc (Suc rex))"
        proof -
          from \<open>l = [Bk, Oc] @ CL\<close> and \<open>r = Bk \<up> Suc rex\<close>
          have "\<exists>rex'. [Oc] @ CL = [Oc] @ CL \<and> Bk \<up> Suc (Suc rex) = Bk \<up> Suc rex'"
            by blast
          with \<open>l = [Bk, Oc] @ CL\<close>
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, [Oc] @ CL, Bk \<up> Suc (Suc rex))"    
            by auto
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 10\<close> and  \<open>l = [Bk, Oc] @ CL\<close> and \<open>r = Bk \<up> Suc rex\<close>
          by auto
      next
        case (Suc nat)
        then have "lex = Suc nat" .
        with \<open>l = Bk \<up> lex @ [Bk, Oc] @ CL\<close> have "l= Bk \<up> Suc nat @ [Bk, Oc] @ CL" by auto
        have "step0 (10, Bk \<up> Suc nat @ [Bk, Oc] @ CL, Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                 = (10, Bk \<up> nat @ [Bk, Oc] @ CL, Bk \<up> Suc (Suc rex))"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
        moreover
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, Bk \<up> nat @ [Bk, Oc] @ CL, Bk \<up> Suc (Suc rex))"
        proof -
          from \<open>l= Bk \<up> Suc nat @ [Bk, Oc] @ CL\<close> and \<open>r = Bk \<up> Suc rex\<close>
          have  "\<exists>lex' rex'. Bk \<up> Suc nat @ [Bk, Oc] @ CL = Bk \<up> lex' @ [Bk,Oc] @ CL \<and> Bk \<up> Suc (Suc rex) = Bk \<up> Suc rex'"
            by blast
          with \<open>l= Bk \<up> Suc nat @ [Bk, Oc] @ CL\<close>
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, Bk \<up> nat @ [Bk, Oc] @ CL, Bk \<up> Suc (Suc rex))"
            by auto
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 10\<close> and \<open>l= Bk \<up> Suc nat @ [Bk, Oc] @ CL\<close> and \<open>r = Bk \<up> Suc rex\<close>
          by auto
      qed
    next
      assume "l = [Oc] @ CL \<and> r = Bk \<up> Suc rex \<or> l = CL \<and> r = Oc # Bk \<up> Suc rex"
      then show ?thesis
      proof
        assume "l = [Oc] @ CL \<and> r = Bk \<up> Suc rex"
        then have "l = [Oc] @ CL" and "r = Bk \<up> Suc rex" by auto

        have "step0 (10, [Oc] @ CL, Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                 = (10, CL, Oc# Bk \<up> (Suc rex))"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
        moreover
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, CL, Oc# Bk \<up> (Suc rex))"
        proof -
          from \<open>l = [Oc] @ CL\<close> and \<open>r = Bk \<up> Suc rex\<close>
          have "\<exists>rex'. [Oc] @ CL = [Oc] @ CL \<and> Bk \<up> Suc rex = Bk \<up> Suc rex'"
            by blast
          with \<open>l = [Oc] @ CL\<close>
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (10, CL, Oc# Bk \<up> (Suc rex))"    
            by auto
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 10\<close> and  \<open>l = [Oc] @ CL\<close> and \<open>r = Bk \<up> Suc rex\<close>
          by auto
      next
        assume "l = CL \<and> r = Oc # Bk \<up> Suc rex"
        then have "l = CL" and "r = Oc # Bk \<up> Suc rex" by auto
        show ?thesis
        proof (cases CL) (* here, we start decomposing CL in the loop 'move to left until Oc *)
          case Nil
          then have "CL = []" .
          with \<open>l = CL\<close> have "l = []" by auto
          have "step0 (10, [], Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                 = (11, [], Bk#Oc# Bk \<up> (Suc rex))"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
          moreover
          have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#Oc# Bk \<up> (Suc rex))"
          proof -
            (* Special case: CL = [] 
               from call (1, [Oc, Bk], []) we get 11: [] _11_ [Bk,Oc,Bk,Bk,Bk]

               YYYY1' "\<exists>rex'. ] = [] \<and> Bk# Oc# Bk \<up> Suc rex = [Bk] @ rev CL @ Oc # Bk \<up> Suc rex' \<and> (CL = [] \<or> last CL = Oc)" 
             *)
            from \<open>CL = []\<close>
            have "\<exists>rex'. [] = [] \<and> Bk# Oc# Bk \<up> Suc rex = [Bk] @ rev CL @ Oc # Bk \<up> Suc rex' \<and> (CL = [] \<or> last CL = Oc)"
              by auto           
            with \<open>l = []\<close>
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#Oc# Bk \<up> (Suc rex))"    
              by auto
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 10\<close> and  \<open>l = []\<close> and \<open>r = Oc # Bk \<up> Suc rex\<close>
            by auto
        next
          case (Cons a cls)
          then have "CL = a # cls" .
          with \<open>l = CL\<close> have "l =  a # cls" by auto
          then show ?thesis
          proof (cases a)
            case Bk
            then have "a = Bk" .
            with \<open>l =  a # cls\<close> have "l =  Bk # cls" by auto
            with \<open>a = Bk\<close> \<open>CL = a # cls\<close> have "CL = Bk # cls" by auto

            have "step0 (10,  Bk # cls, Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                 = (11, cls, Bk# Oc # Bk \<up> Suc rex)"
              by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
            moreover
            have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Bk# Oc # Bk \<up> Suc rex)"

            proof (cases cls)
              case Nil
              then have "cls = []" .
              with \<open>CL = Bk # cls\<close> have "CL = [Bk]" by auto
                  (* Special case: CL ends with a blank 
                     from call ctxrunTM tm_erase_right_then_dblBk_left (1, [Bk, Oc,Bk], [Bk,Oc,Oc,Bk,Oc,Oc])
                          24: [Bk] _10_ [Oc,Bk,Bk,Bk,Bk,Bk,Bk,Bk,Bk]
                          25: [] _11_ [Bk,Oc,Bk,Bk,Bk,Bk,Bk,Bk,Bk,Bk]

                     YYYY2' "\<exists>rex'.         [] = []  \<and>     Bk# Oc# Bk \<up> Suc rex = rev CL        @ Oc # Bk \<up> Suc rex' \<and> \<and> CL \<noteq> [] \<and> last CL = Bk" 

                   *)
              then have "\<exists>rex'. [] = [] \<and> Bk# Oc# Bk \<up> Suc rex = rev CL @ Oc # Bk \<up> Suc rex' \<and> CL \<noteq> [] \<and> last CL = Bk"
                by auto
              with \<open>l =  Bk # cls\<close> and \<open>cls = []\<close>
              show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Bk# Oc # Bk \<up> Suc rex)"    
                by auto
            next
              case (Cons a cls')
              then have "cls = a # cls'" .
              then show ?thesis
              proof (cases a)
                case Bk
                with \<open>CL = Bk # cls\<close> and \<open>cls = a # cls'\<close> have "CL = Bk# Bk# cls'" by auto
                with \<open>noDblBk CL\<close> have False using noDblBk_def by auto
                then show ?thesis by auto
              next
                case Oc
                then have "a = Oc" .
                with \<open>CL = Bk # cls\<close> and \<open>cls = a # cls'\<close> and \<open>l =  Bk # cls\<close>
                have "CL = Bk# Oc# cls' \<and> l =  Bk # Oc # cls'" by auto
                    (* from call (1, [Oc,Oc,Bk,Oc,Bk], [Oc,Oc,Oc,Bk,Oc,Oc])
                       we get 26: [Oc,Oc] _11_ [Bk,Oc,Bk,Bk,Bk,Bk,Bk,Bk,Bk,Bk]
  
                       YYYY3 "\<exists>rex' ls1 ls2. Oc#cls' = Oc#ls2 \<and> Bk# Oc# Bk \<up> Suc rex = rev ls1 @ Oc # Bk \<up> Suc rex' \<and>
                                    CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk]"
                     *)
                with \<open>cls = a # cls'\<close> and \<open>a=Oc\<close>
                have "\<exists>rex' ls1 ls2. Oc#cls' = Oc#ls2 \<and> Bk# Oc# Bk \<up> Suc rex = rev ls1 @ Oc # Bk \<up> Suc rex' \<and>
                                     CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk]"
                  by auto
                with \<open>cls = a # cls'\<close> and \<open>a=Oc\<close>
                show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Bk# Oc # Bk \<up> Suc rex)"    
                  by auto
              qed
            qed
            ultimately show ?thesis
              using  assms and cf_cases and \<open>s = 10\<close> and  \<open>l =  Bk # cls\<close> and \<open>r = Oc # Bk \<up> Suc rex\<close>
              by auto
          next
            case Oc
            then have "a = Oc" .
            with \<open>l =  a # cls\<close> have "l =  Oc # cls" by auto
            with \<open>a = Oc\<close> \<open>CL = a # cls\<close> have "CL = Oc # cls" by auto  (* a normal case *)

            have "step0 (10,  Oc # cls, Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                 = (11, cls, Oc # Oc # Bk \<up> Suc rex)"
              by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
            moreover
            have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Oc # Oc # Bk \<up> Suc rex)"
            proof (cases cls)
              case Nil
              then have "cls = []" .
              with \<open>CL = Oc # cls\<close> have "CL = [Oc]" by auto
               (* from call (1, [Oc,Oc,Bk], [Oc,Oc,Oc,Bk,Oc,Oc])
                    we get 26: [] _11_ [Oc,Oc,Bk,Bk,Bk,Bk,Bk,Bk,Bk,Bk]

                   YYYY2''   "\<exists>rex'. [] = [] \<and> Oc# Oc# Bk \<up> Suc rex = rev CL @ Oc # Bk \<up> Suc rex' \<and>
                                     CL \<noteq> [] \<and> last CL = Oc"
               *)
              then have "\<exists>rex'. [] = [] \<and> Oc# Oc# Bk \<up> Suc rex = rev CL @ Oc # Bk \<up> Suc rex' \<and> CL \<noteq> [] \<and> last CL = Oc"
                by auto
              with \<open>l =  Oc # cls\<close> and \<open>cls = []\<close>
              show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Oc# Oc # Bk \<up> Suc rex)"    
                by auto
            next
              case (Cons a cls')
              then have "cls = a # cls'" .
              then show ?thesis
              proof (cases a)
                case Bk
                then have "a=Bk" .
                with \<open>CL = Oc # cls\<close> and \<open>cls = a # cls'\<close> and \<open>l =  Oc # cls\<close>
                have "CL = Oc# Bk# cls'" and "l =  Oc # Bk # cls'" and "CL = l" and \<open>cls = Bk # cls'\<close> by auto

                from \<open>CL = Oc# Bk# cls'\<close> and \<open>noDblBk CL\<close>
                have "cls' = [] \<or> (\<exists>cls''. cls' = Oc# cls'')"
                  by (metis (full_types) \<open>CL = Oc # cls\<close> \<open>cls = Bk # cls'\<close> append_Cons append_Nil cell.exhaust hasDblBk_L1 neq_Nil_conv)

                then show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Oc # Oc # Bk \<up> Suc rex)"
                proof
                  assume "cls' = []"
                  with \<open>CL = Oc# Bk# cls'\<close> and \<open>CL = l\<close> and \<open>cls = Bk # cls'\<close>
                  have "CL = Oc# Bk# []" and "l = Oc# Bk# []" and "cls = [Bk]" by auto
                      (* from call (1, [Bk,Oc,Oc,Bk], [Oc,Oc,Oc,Bk,Oc,Oc])
                        we get 26: [Bk] _11_ [Oc,Oc,Bk,Bk,Bk,Bk,Bk,Bk,Bk,Bk]

                        YYYY5 "\<exists>rex'.     cls = [Bk] \<and> Oc# Oc# Bk \<up> Suc rex = rev [Oc] @ Oc # Bk \<up> Suc rex' \<and> CL = [Oc, Bk]"

                      *)
                  then have "\<exists>rex'.     cls = [Bk] \<and> Oc# Oc# Bk \<up> Suc rex = rev [Oc] @ Oc # Bk \<up> Suc rex' \<and> CL = [Oc, Bk]"
                    by auto
                  with \<open>CL = Oc# Bk# []\<close> show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Oc # Oc # Bk \<up> Suc rex)" 
                    by auto
                next
                  assume "\<exists>cls''. cls' = Oc # cls''"
                  then obtain cls'' where "cls' = Oc # cls''" by blast
                  with \<open>CL = Oc# Bk# cls'\<close> and \<open>CL = l\<close> and \<open>cls = Bk # cls'\<close>
                  have "CL = Oc# Bk# Oc # cls''" and "l = Oc# Bk# Oc # cls''" and "cls = Bk#Oc # cls''" by auto
                      (* very special case  call (1, [*,Oc,Bk, Oc,Oc,Bk], [Oc,Oc,Oc,Bk,Oc,Oc])
                         trailing Bk on initial left tape
                         
                         from call (1, [Oc,Bk, Oc,Oc,Bk], [Oc,Oc,Oc,Bk,Oc,Oc])
                            we get 26: [Oc,Bk] _11_ [Oc,Oc,Bk,Bk,Bk,Bk,Bk,Bk,Bk,Bk]
    
                         from call (1, [Oc,Oc,Bk,Oc,Bk, Oc,Oc,Bk], [Oc,Oc,Oc,Bk,Oc,Oc])
                            we get 26: [Oc,Oc,Bk,Oc,Bk] _11_ [Oc,Oc,Bk,Bk,Bk,Bk,Bk,Bk,Bk,Bk]

                        YYYY6   "\<exists>rex' ls1 ls2. cls     = Bk#Oc#ls2  \<and> Oc# Oc# Bk \<up> Suc rex = rev ls1 @ Oc # Bk \<up> Suc rex'
                                                \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc]"
                   *)
                  then have "\<exists>rex' ls1 ls2. cls     = Bk#Oc#ls2  \<and> Oc# Oc# Bk \<up> Suc rex = rev ls1 @ Oc # Bk \<up> Suc rex'
                                                \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc]"
                    by auto
                  then show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Oc # Oc # Bk \<up> Suc rex)"
                    by auto
                qed

              next
                case Oc
                then have "a=Oc" .
                with \<open>CL = Oc # cls\<close> and \<open>cls = a # cls'\<close> and \<open>l =  Oc # cls\<close>
                have "CL = Oc# Oc# cls'" and "l =  Oc # Oc # cls'" and "CL = l" and \<open>cls = Oc # cls'\<close> by auto
                (* We know more : ls1 = [Oc]
                   YYYY7   "\<exists>rex' ls1 ls2. cls = Oc#ls2 \<and> Oc# Oc# Bk \<up> Suc rex = rev ls1 @ Oc # Bk \<up> Suc rex' \<and>
                                           CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc]"

                           "\<exists>rex' ls1 ls2. cls = Oc#ls2 \<and> Oc# Oc# Bk \<up> Suc rex = rev ls1 @ Oc # Bk \<up> Suc rex' \<and>
                                           CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc]"
                *)
                then have "\<exists>rex' ls1 ls2. cls = Oc#ls2 \<and> Oc# Oc# Bk \<up> Suc rex = rev ls1 @ Oc # Bk \<up> Suc rex' \<and>
                                           CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc]"
                  by auto
                then show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, cls, Oc # Oc # Bk \<up> Suc rex)"
                  by auto
              qed
            qed
            ultimately show ?thesis
              using  assms and cf_cases and \<open>s = 10\<close> and  \<open>l =  Oc # cls\<close> and \<open>r = Oc # Bk \<up> Suc rex\<close>
              by auto
          qed
        qed
      qed
    qed
  next
    assume "s = 11"
    with cf_cases and assms
    have "(\<exists>rex.         l = []         \<and> r = Bk# rev CL    @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc))              \<or>
          (\<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk ) \<or>
          (\<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc ) \<or>

          (\<exists>rex.         l = [Bk]       \<and> r = rev [Oc]      @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]) \<or>

          (\<exists>rex ls1 ls2. l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc] ) \<or>
          (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk] ) \<or>
          (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc] ) \<or>
 
          (\<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> tl ls1 \<noteq> [])"
      by auto

    then have s11_cases:
      "\<And>P. \<lbrakk> \<exists>rex.         l = []         \<and> r = Bk# rev CL    @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc) \<Longrightarrow> P;
             \<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk \<Longrightarrow> P;
             \<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc \<Longrightarrow> P;

             \<exists>rex.         l = [Bk]       \<and> r = rev [Oc]      @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk] \<Longrightarrow> P;

             \<exists>rex ls1 ls2. l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc] \<Longrightarrow> P;
             \<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk] \<Longrightarrow> P;
             \<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc] \<Longrightarrow> P;

             \<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> tl ls1 \<noteq> [] \<Longrightarrow> P
            \<rbrakk> \<Longrightarrow> P"
      by blast

    show ?thesis
    proof (rule s11_cases)
      assume "\<exists>rex ls1 ls2. l = Bk # Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk # Oc # ls2 \<and> ls1 = [Oc]"
      then obtain rex ls1 ls2 where A_case: "l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc]" by blast

      then have "step0 (11,  Bk # Oc # ls2, r) tm_erase_right_then_dblBk_left
                 = (11, Oc # ls2, Bk # r)"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

      moreover
      have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, Oc # ls2, Bk # r)"
      proof -         
        from A_case   (* YYYY8 *)
        have "\<exists>rex' ls1' ls2'. Oc#ls2 = ls2'  \<and> Bk# Oc# Oc# Bk \<up> Suc rex' = rev ls1' @ Oc # Bk \<up> Suc rex' \<and>
                                         CL = ls1' @ ls2' \<and> tl ls1' \<noteq> []"
          by force
        with A_case
        show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, Oc # ls2, Bk # r)"
          by auto
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 11\<close> and A_case
        by simp
    next
      assume "\<exists>rex ls1 ls2. l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Oc]"
      then obtain rex ls1 ls2 where
        A_case: "l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Oc]" by blast
      then have "step0 (11, Oc # ls2, r) tm_erase_right_then_dblBk_left
                 = (11, ls2, Oc#r)"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover
      have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, ls2, Oc#r)"
      proof (rule noDblBk_cases)
        from \<open>noDblBk CL\<close> show "noDblBk CL" .
      next
        from A_case show "CL = [Oc,Oc] @ ls2" by auto
      next
        assume "ls2 = []" 
(*
        with A_case  (* YYYY7''' *)
        have "\<exists>rex'. ls2 = [] \<and> [Oc,Oc] @ Oc # Bk \<up> Suc rex = rev CL @ Oc # Bk \<up> Suc rex' \<and> CL = [Oc, Oc]"
          by force
*)
        with A_case  (* YYYY2'' *)
        have "\<exists>rex'. ls2 = [] \<and> [Oc,Oc] @ Oc # Bk \<up> Suc rex = rev CL @ Oc # Bk \<up> Suc rex'"
          by force
        with A_case and \<open>ls2 = []\<close> show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, ls2, Oc#r)"
          by auto
      next
        assume "ls2 = [Bk]"
        (* YYYY8 *)
        with A_case
        have "\<exists>rex' ls1' ls2'.    ls2 = ls2'      \<and>     Oc#Oc# Oc# Bk \<up> Suc rex  = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and> CL = ls1' @ ls2'       \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> []"
          by simp

        with A_case and \<open>ls2 = [Bk]\<close> show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, ls2, Oc#r)"
          by force
      next
        fix C3
        assume "ls2 = Bk # Oc # C3"
        (* YYYY8 *)
        with A_case
        have "\<exists>rex' ls1' ls2'.    ls2 = ls2'      \<and>     Oc#Oc# Oc# Bk \<up> Suc rex  = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and> CL = ls1' @ ls2'       \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> []"
          by simp
        with A_case and \<open>ls2 = Bk # Oc # C3\<close> show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, ls2, Oc#r)"
          by force
      next
        fix C3
        assume "ls2 = Oc # C3"
        (* YYYY8 *)
        with A_case
        have "\<exists>rex' ls1' ls2'.    ls2 = ls2'      \<and>     Oc#Oc# Oc# Bk \<up> Suc rex  = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and> CL = ls1' @ ls2'       \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> []"
          by simp
        with A_case and \<open>ls2 = Oc # C3\<close> show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, ls2, Oc#r)"
          by force
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 11\<close> and A_case
        by simp
    next
      assume "\<exists>rex. l = [Bk] \<and> r = rev [Oc] @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]"
      then obtain rex where
        A_case: "l = [Bk] \<and> r = rev [Oc] @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]" by blast
      then have "step0 (11, [Bk] , r) tm_erase_right_then_dblBk_left
                 = (11, [], Bk#r)"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#r)"
      proof -
        from A_case
(*
        have "\<exists>rex'.         [] = []         \<and> Bk#rev [Oc] @ Oc # Bk \<up> Suc rex = rev CL        @ Oc # Bk \<up> Suc rex' \<and> CL = [Oc, Bk]" (* YYYY5' *)
          by simp
*)
        have "\<exists>rex'.         [] = []         \<and> Bk#rev [Oc] @ Oc # Bk \<up> Suc rex = rev CL        @ Oc # Bk \<up> Suc rex'" (* YYYY2' *)
          by simp
        with A_case  show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#r)"
          by force
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 11\<close> and A_case
        by simp
    next
      (* YYYY8 for s11 *)
      assume "\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []"
      then obtain rex ls1 ls2 where
        A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []" by blast
      then have "\<exists>z b bs. ls1 = z#bs@[b]"  (* the symbol z does not matter *) 
        by (metis Nil_tl list.exhaust_sel rev_exhaust)
      then have "\<exists>z bs. ls1 = z#bs@[Bk] \<or> ls1 = z#bs@[Oc]"
        using cell.exhaust by blast
      then obtain z bs where w_z_bs: "ls1 = z#bs@[Bk] \<or> ls1 = z#bs@[Oc]" by blast
      then show "inv_tm_erase_right_then_dblBk_left_erp CL CR (step0 cf tm_erase_right_then_dblBk_left)"
      proof
        assume major1: "ls1 = z # bs @ [Bk]"
        then have major2: "rev ls1 = Bk#(rev bs)@[z]" by auto  (* in this case all transitions will be s11 \<longrightarrow> s12 *)
        show ?thesis
        proof  (rule noDblBk_cases)
          from \<open>noDblBk CL\<close> show "noDblBk CL" .
        next
          from A_case show "CL = ls1 @ ls2" by auto
        next
          assume "ls2 = []"
          with A_case have "step0 (11, [] , Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (12, [], Bk#Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
          moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, [], Bk#Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
          proof -
            from A_case \<open>rev ls1 = Bk#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            have "ls1 = z#bs@[Bk]" and "CL = ls1" and "r = rev CL @ Oc # Bk \<up> Suc rex" by auto
            (*  YYYY6'''    \<exists>rex. l = []  \<and> r = Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk *)
            with A_case \<open>rev ls1 = Bk#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            have "\<exists>rex'. [] = []  \<and> Bk#Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex = Bk#rev CL @ Oc # Bk \<up> Suc rex' \<and> CL \<noteq> [] \<and> last CL = Bk"
              by simp
            with A_case \<open>rev ls1 = Bk#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, [], Bk#Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
              by force
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 11\<close> and A_case and \<open>rev ls1 = Bk#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            by simp
        next
          assume "ls2 = [Bk]"
            (* A_case: l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [] *)
          with A_case \<open>rev ls1 = Bk#(rev bs)@[z]\<close> and \<open>ls2 = [Bk]\<close>
          have "ls1 = z#bs@[Bk]" and "CL = z#bs@[Bk]@[Bk]" by auto
          with \<open>noDblBk CL\<close> have False               
            by (metis A_case  \<open>ls2 = [Bk]\<close> append_Cons hasDblBk_L5 major2)
          then show ?thesis by auto
        next
          fix C3
          assume minor: "ls2 = Bk # Oc # C3"
          with A_case and major2 have "CL = z # bs @ [Bk] @ Bk # Oc # C3" by auto
          with \<open>noDblBk CL\<close> have False
            by (metis append.left_neutral append_Cons append_assoc hasDblBk_L1 major1 minor)
          then show ?thesis by auto     
        next
          fix C3
          assume minor: "ls2 = Oc # C3"
            (*
               A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> []"
        
                  major1: "ls1 = Oc # bs @ [Bk]"
                  major2: "rev ls1 = Bk # rev bs @ [Oc]"
        
                  minor1: "ls2 = Oc # C3"
        
                          l =  Oc # C3
        
                          r = rev ls1           @ Oc # Bk \<up> Suc rex
        
                          r = Bk#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex
        
                  thus: s11 \<longrightarrow> s12
        
                          (12, C3, Oc#Bk#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex )
                  
                          l' = C3
                          r' = Oc#Bk#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex
        
                          ls2' = C3
                          
                          rev ls1' = Oc#Bk#(rev bs)@[Oc]
        
                          ls1' = Oc# bs @ [Bk] @ [Oc] = ls1@[Oc]
        
                          CL = ls1 @ ls2 = ls1 @ Oc # C3 = ls1 @ [Oc] @ [C3] = ls1' @ ls2'
        
                              \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> []
        
                           (\<exists>rex' ls1' ls2'. C3 = ls2'  \<and> Oc#Bk#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and>
                                                         CL =  ls1' @ ls2'  \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> [] \<and> last ls1' = Oc)
        
               again       YYYY4 (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc)
             *)

          with A_case have "step0 (11, Oc # C3 , Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (12, C3, Oc#Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex )"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, C3, Oc#Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex )"
          proof -
            from A_case and \<open>rev ls1 = Bk # rev bs @ [z]\<close> and \<open>ls2 = Oc # C3\<close> and \<open>ls1 = z # bs @ [Bk]\<close>
            have "\<exists>rex' ls1' ls2'. C3 = ls2'  \<and> Oc#Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and>
                                                 CL =  ls1' @ ls2'  \<and> hd ls1' = z \<and> tl ls1' \<noteq> [] \<and> last ls1' = Oc"            
              by simp

            with A_case \<open>rev ls1 = Bk # rev bs @ [z]\<close> and \<open>ls2 = Oc # C3\<close> and \<open>ls1 = z # bs @ [Bk]\<close>
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, C3, Oc#Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex )"           
              by simp
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 11\<close> and A_case and \<open>rev ls1 = Bk#(rev bs)@[z]\<close> and  \<open>ls2 = Oc # C3\<close>
            by simp      
        qed
      next
        assume major1: "ls1 = z # bs @ [Oc]"
        then have major2: "rev ls1 = Oc#(rev bs)@[z]" by auto (* in this case all transitions will be s11 \<longrightarrow> s11 *)
        show ?thesis
        proof  (rule noDblBk_cases)
          from \<open>noDblBk CL\<close> show "noDblBk CL" .
        next
          from A_case show "CL = ls1 @ ls2" by auto
        next
          assume "ls2 = []"
            (* A_case: l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [] 

              l = []
              r = rev ls1          @ Oc # Bk \<up> Suc rex
              r = Oc#(rev bs)@[Oc] @ Oc # Bk \<up> Suc rex

              l' = []
              r' = Bk#Oc#(rev bs)@[Oc] @ Oc # Bk \<up> Suc rex

              ls1 = Oc # bs @ [Oc]
              rev ls1 = Oc#(rev bs)@[Oc]
              
              rev ls1' =  Bk#Oc#(rev bs)@[Oc]

              ls1' = Oc # bs @ [Oc] @ [Bk]

              ls2' = []

              CL = ls1 @ ls2 = (Oc # bs @ [Oc]) @ [] = Oc # bs @ [Oc] = ls1

              rev ls1 = rev CL

              \<exists>rex'. [] = []  \<and> Bk#Oc#(rev bs)@[Oc] @ Oc # Bk \<up> Suc rex = Bk#rev CL @ Oc # Bk \<up> Suc rex' \<and> last CL = Oc

                      (\<exists>rex. l = []  \<and> r = Bk# rev CL @ Oc # Bk \<up> Suc rex \<and> last CL = Oc) 

              we simplify
              YYYY1'  (\<exists>rex. l = []  \<and> r = Bk# rev CL @ Oc # Bk \<up> Suc rex)

              now, we generalize to 
              YYYY1'  (\<exists>rex. l = []  \<and> r = Bk# rev CL @ Oc # Bk \<up> Suc rex) \<and> (CL = [] \<or> last CL = Oc)

           *)

          with A_case have "step0 (11, [] , Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex)"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
          proof -
            from A_case \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            have "ls1 = z # bs @ [Oc]" and "CL = ls1" and "r = rev CL @ Oc # Bk \<up> Suc rex" by auto
                (*  new invariant for s11:
                    YYYY1'  (\<exists>rex. l = []  \<and> r = Bk# rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc))
           *)
            with A_case \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            have "\<exists>rex'. [] = []  \<and> Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex = Bk#rev CL @ Oc # Bk \<up> Suc rex' \<and> (CL = [] \<or> last CL = Oc)"              
              by simp
            with A_case \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
              by force
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 11\<close> and A_case and \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = []\<close>
            by simp
        next     
          assume "ls2 = [Bk]"
            (* A_case: l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [] 

              l = [Bk]
              r = rev ls1          @ Oc # Bk \<up> Suc rex
              r = Oc#(rev bs)@[Oc] @ Oc # Bk \<up> Suc rex

              l' = []
              r' = Bk#Oc#(rev bs)@[Oc] @ Oc # Bk \<up> Suc rex

              ls1 = Oc # bs @ [Oc]
              rev ls1 = Oc#(rev bs)@[Oc]
              
              rev ls1' =  Bk#Oc#(rev bs)@[Oc]

              ls1' = Oc # bs @ [Oc] @ [Bk] = ls1 @ [Bk]

              ls2' = []

              CL = ls1 @ ls2 = (Oc # bs @ [Oc]) @ [Bk] = ls1 @ [Bk] = ls1'


              list functions (hd ls) and (last ls) are only usefull if ls \<noteq> [] is known! 

              new invariant for s11:
              YYYY2'    (\<exists>rex.         l =        []  \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> []  \<and> last CL = Bk) \<or>  (s11 \<longrightarrow> s11)
              YYYY2''   (\<exists>rex.         l =        []  \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> []  \<and> last CL = Oc) \<or>  (s11 \<longrightarrow> s11)
             
           *)
          with A_case have "step0 (11, [Bk] , Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
          proof -
            from A_case \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = [Bk]\<close>
            have "ls1 = z # bs @ [Oc]" and "CL = ls1@[Bk]" by auto
                (*  new invariant for s11:
                    YYYY2'   (\<exists>rex.         l =        []  \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> []  \<and> last CL = Bk)
           *)
            with A_case \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = [Bk]\<close>
            have "\<exists>rex'. [] = []  \<and> Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex = rev CL @ Oc # Bk \<up> Suc rex' \<and> CL \<noteq> [] \<and> last CL = Bk"              
              by simp

            with A_case \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = [Bk]\<close> and \<open>CL = ls1@[Bk]\<close>
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"

              by force
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 11\<close> and A_case and \<open>rev ls1 = Oc#(rev bs)@[z]\<close> and \<open>ls2 = [Bk]\<close>
            by simp
        next     
          fix C3
          assume minor: "ls2 = Bk # Oc # C3"

(* thm A_case: l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> []
             thm major1: ls1 = Oc # bs @ [Oc]
             thm major2: rev ls1 = Oc # rev bs @ [Oc]

              minor1: "ls2 = Bk # Oc # C3"
    
                      l = Bk # Oc # C3
                      r = Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex
    
              thus: s11 \<longrightarrow> s11
                      (11, Oc # C3, Bk#Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex )
                 
                      l' = Oc # C3
                      r' = Bk#Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex
                      
                      ls2' = Oc # C3
                      
                      rev ls1' = Bk#Oc#(rev bs)@[Oc]
    
                      ls1' = Oc# bs @ [Oc] @ [Bk] = ls1@[Bk]
    
                      CL = ls1 @ ls2 = ls1 @ Bk # Oc # C3 = ls1 @ [Bk] @ [Oc ,C3] = ls1' @ ls2'
    
                          \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> []
    
                       (\<exists>rex' ls1' ls2'. Oc # C3 = ls2'  \<and> Bk#Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and>
                                                     CL =  ls1' @ ls2'  \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> [])
    
              again  YYYY8    (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [])
           *)

          with A_case have "step0 (11, Bk # Oc # C3 , Oc # rev bs @ [z]  @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (11, Oc # C3, Bk#Oc # rev bs @ [z]  @ Oc # Bk \<up> Suc rex )"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, Oc # C3, Bk#Oc # rev bs @ [z]  @ Oc # Bk \<up> Suc rex )"
          proof -
            from A_case and \<open>rev ls1 = Oc # rev bs @ [z]\<close> and \<open>ls2 = Bk # Oc # C3\<close> and \<open>ls1 = z # bs @ [Oc]\<close>
            have "\<exists>rex' ls1' ls2'. Oc # C3 = ls2'  \<and> Bk#Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and>
                                                     CL =  ls1' @ ls2'  \<and> hd ls1' = z \<and> tl ls1' \<noteq> [] "
              by simp

            with A_case \<open>rev ls1 = Oc # rev bs @ [z]\<close> and \<open>ls2 = Bk # Oc # C3\<close> and \<open>ls1 = z # bs @ [Oc]\<close>
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, Oc # C3, Bk#Oc # rev bs @ [z]  @ Oc # Bk \<up> Suc rex )"         
              by simp
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 11\<close> and A_case and \<open>rev ls1 = Oc # rev bs @ [z]\<close> and \<open>ls2 = Bk # Oc # C3\<close>
            by simp      
        next
          fix C3
          assume minor: "ls2 = Oc # C3"
            (*
               A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> []"
                  major1: "ls1 = Oc # bs @ [Oc]"
                  major2: "rev ls1 = Oc # rev bs @ [Oc]"
        
                  minor1: "ls2 = Oc # C3"
        
                          l =  Oc # C3
        
                          r = rev ls1           @ Oc # Bk \<up> Suc rex
        
                          r = Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex
        
                  thus: s11 \<longrightarrow> s11
        
                          (11, C3, Oc#Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex )

                          l' = C3
                          r' = Oc#Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex
        
                          ls2' = C3
                          
                          rev ls1' = Oc#Oc#(rev bs)@[Oc]
        
                          ls1' = Oc# bs @ [Oc] @ [Oc] = ls1@[Oc]
        
                          CL = ls1 @ ls2 = ls1 @ Oc # C3 = ls1 @ [Oc] @ [C3] = ls1' @ ls2'
        
                              \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> []
        
                           (\<exists>rex' ls1' ls2'. C3 = ls2'  \<and> Oc#Oc#(rev bs)@[Oc]  @ Oc # Bk \<up> Suc rex = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and>
                                                         CL =  ls1' @ ls2'  \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> [])
        
               again       YYYY8    (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [])
             *)

          with A_case have "step0 (11, Oc # C3 , Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (11, C3, Oc#Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex)"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

          moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, C3, Oc#Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex )"
          proof -
            from A_case and \<open>rev ls1 = Oc # rev bs @ [z]\<close> and \<open>ls2 = Oc # C3\<close> and \<open>ls1 = z # bs @ [Oc]\<close>
            have "\<exists>rex' ls1' ls2'. C3 = ls2'  \<and> Oc#Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex = rev ls1'       @ Oc # Bk \<up> Suc rex' \<and>
                                                         CL =  ls1' @ ls2'  \<and> hd ls1' = z \<and> tl ls1' \<noteq> []"            
              by simp

            with A_case \<open>rev ls1 = Oc # rev bs @ [z]\<close> and \<open>ls2 = Oc # C3\<close> and \<open>ls1 = z # bs @ [Oc]\<close>
            show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, C3, Oc#Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex )"          
              by simp
          qed
          ultimately show ?thesis
            using  assms and cf_cases and \<open>s = 11\<close> and A_case and \<open>rev ls1 = Oc # rev bs @ [z]\<close> and  \<open>ls2 = Oc # C3\<close>
            by simp      
        qed
      qed
    next
      (* YYYY3 *)
      assume "\<exists>rex ls1 ls2. l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Bk]"
      then obtain rex ls1 ls2 where
        A_case: "l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Bk]" by blast
      then have major2: "rev ls1 = [Bk]" by auto
          (* "l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Bk]"

              l = Oc # ls2
              r = rev ls1          @ Oc # Bk \<up> Suc rex
              r = [Bk] @ Oc # Bk \<up> Suc rex

              l' = ls2
              r' = Oc#[Bk] @ Oc # Bk \<up> Suc rex

              \<longrightarrow> s12: (12, ls2, Oc#[Bk] @ Oc # Bk \<up> Suc rex )

              ls1 = [Bk]
              rev ls1 = [Bk]
              
              rev ls1' =   Oc#[Bk]

              ls1' = Bk#[Oc]
              ls2' = ls2

              CL =  ls1 @ Oc # ls2 = [Bk] @ Oc # ls2 =  (ls1 @ [Oc]) @ ls2 = ls1'@ls2'

              \<and> ls1' = Bk#[Oc]

              r' = Oc#[Bk] @ Oc # Bk \<up> Suc rex = rev ls1'  @ Oc # Bk \<up> Suc rex

               \<exists>rex' ls1' ls2'. ls2 = ls2'  \<and> Oc#[Bk] @ Oc # Bk \<up> Suc rex = rev ls1'  @ Oc # Bk \<up> Suc rex' \<and> CL = ls1' @ ls2' \<and>  ls1' = [Bk,Oc]

              YYYY4  (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc)

           *)
      with A_case have "step0 (11, Oc # ls2 , [Bk] @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (12, ls2, Oc#[Bk] @ Oc # Bk \<up> Suc rex )"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

      moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, ls2, Oc#[Bk] @ Oc # Bk \<up> Suc rex )"
      proof -
        from A_case and \<open>rev ls1 = [Bk]\<close> 
        have "\<exists>rex' ls1' ls2'. ls2 = ls2'  \<and> Oc#[Bk] @ Oc # Bk \<up> Suc rex = rev ls1'  @ Oc # Bk \<up> Suc rex' \<and>
                               CL = ls1' @ ls2' \<and> tl ls1' \<noteq> [] \<and> last ls1' = Oc" (* YYYY4 *)           
          by simp

        with A_case \<open>rev ls1 = [Bk]\<close>
        show "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, ls2, Oc#[Bk] @ Oc # Bk \<up> Suc rex )"         
          by simp
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 11\<close> and A_case and \<open>rev ls1 = [Bk]\<close> 
        by simp
    next
      assume "\<exists>rex. l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)"  (* YYYY1' *)
      then obtain rex where
        A_case: "l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)" by blast
      then have "step0 (11, [] , Bk # rev CL @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (12, [], Bk#Bk # rev CL @ Oc # Bk \<up> Suc rex )"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, [], Bk#Bk # rev CL @ Oc # Bk \<up> Suc rex )"
      proof -
        from A_case
        have "\<exists>rex'. [] = [] \<and> Bk#Bk # rev CL @ Oc # Bk \<up> Suc rex  = Bk# Bk # rev CL @ Oc # Bk \<up> Suc rex' \<and> (CL = [] \<or> last CL = Oc)"  (* YYYY9 *)
          by simp

        with A_case
        show "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, [], Bk#Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by force
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 11\<close> and A_case
        by simp
    next
      assume "\<exists>rex. l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk" (* YYYY2' *)
      then obtain rex where
        A_case: "l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk" by blast
      then have "hd (rev CL) = Bk"
        by (simp add: hd_rev)
      with A_case  have "step0 (11, [] , rev CL @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (12, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
      proof -
        from A_case 
        have "\<exists>rex'. [] = [] \<and> Bk # rev CL @ Oc # Bk \<up> Suc rex  = Bk # rev CL @ Oc # Bk \<up> Suc rex' \<and> CL \<noteq> [] \<and> last CL = Bk" (*  YYYY6''' *)
          by simp

        with A_case
        show "inv_tm_erase_right_then_dblBk_left_erp CL CR (12, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by force
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 11\<close> and A_case
        by simp
    next
      assume "\<exists>rex. l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc" (* YYYY2'' *)
      then obtain rex where
        A_case: "l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc" by blast
      then have "hd (rev CL) = Oc"
        by (simp add: hd_rev)
      with A_case  have "step0 (11, [] , rev CL @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                          = (11, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
      proof -
        from A_case
        have "\<exists>rex'. [] = [] \<and> Bk # rev CL @ Oc # Bk \<up> Suc rex  = Bk # rev CL @ Oc # Bk \<up> Suc rex' \<and> (CL = [] \<or> last CL = Oc)" (*  YYYY1' *)
          by simp

        with A_case
        show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by force
      qed
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 11\<close> and A_case
        by simp

    qed
  next
    assume "s = 12"
    with cf_cases and assms
    have "
          (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc) \<or>
          (\<exists>rex.         l = []  \<and> r = Bk#rev CL    @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk) \<or>
          (\<exists>rex.         l = []  \<and> r = Bk#Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc))"
      by auto

    then have s12_cases:
      "\<And>P. \<lbrakk> \<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc \<Longrightarrow> P;
             \<exists>rex. l = []  \<and> r = Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk \<Longrightarrow> P;
             \<exists>rex. l = []  \<and> r = Bk#Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc) \<Longrightarrow> P \<rbrakk>
        \<Longrightarrow> P"
      by blast

    show ?thesis
    proof (rule s12_cases)
      (* YYYY4 *)
      assume "\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc"
      then obtain rex ls1 ls2 where
        A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2\<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc" by blast
      then have "ls1 \<noteq> []" by auto 
      with A_case have major: "hd (rev ls1) = Oc"
        by (simp add: hd_rev)
      show ?thesis
      proof (rule noDblBk_cases)
        from \<open>noDblBk CL\<close> show "noDblBk CL" .
      next
        from A_case show "CL = ls1 @ ls2" by auto
      next
        assume "ls2 = []"
          (*
          A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc"
          major: "hd (rev ls1) = Oc
          ls1 \<noteq> []

          ass: ls2 = []

          l = []
          r = rev ls1 @ Oc # Bk \<up> Suc rex   where "hd (rev ls1) = Oc"
          
          \<longrightarrow> s11
 
          l' = []
          r' = Bk#rev ls1 @ Oc # Bk \<up> Suc rex

         *)
        from A_case have "step0 (12, [] ,   Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left
                              = (11, [], Bk#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

        moreover from  A_case and major have "r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)"
          by (metis Nil_is_append_conv \<open>ls1 \<noteq> []\<close> hd_Cons_tl hd_append2 list.simps(3) rev_is_Nil_conv)

        ultimately have "step0 (12, [] , rev ls1 @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                             = (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
          by (simp add: A_case)
            (* 
            CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []
            CL = ls1

            l' = []
            r' = Bk# (rev CL) @ Oc # Bk \<up> Suc rex 
         *)
        moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
        proof -
          from A_case and \<open>ls2 = []\<close> have "rev ls1 = rev CL" by auto
          with  A_case and \<open>ls2 = []\<close> have "\<exists>rex'. [] = []  \<and> Bk# rev ls1 @ Oc # Bk \<up> Suc rex = Bk# rev CL    @ Oc # Bk \<up> Suc rex' \<and> (CL = [] \<or> last CL = Oc)" (* YYYY1' *)
            by simp
          with A_case \<open>r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)\<close> and \<open>ls2 = []\<close>
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
            by force
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 12\<close> and A_case and \<open>ls2 = []\<close>
          by simp
      next
        assume "ls2 = [Bk]"
        from A_case have "step0 (12, [Bk] ,   Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left
                              = (11, [], Bk#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

        moreover from  A_case and major have "r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)"
          by (metis Nil_is_append_conv \<open>ls1 \<noteq> []\<close> hd_Cons_tl hd_append2 list.simps(3) rev_is_Nil_conv)

        ultimately have "step0 (12, [Bk] , rev ls1 @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                             = (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
          by (simp add: A_case)
            (* 
            CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []
            CL = ls1 @ [Bk] = (ls1 @ [Bk]) = ls1'

            l' = []
            r' = rev ls1' = rev CL

            l' = []
            r' = rev CL @ Oc # Bk \<up> Suc rex 
         *)
        moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
        proof -
          from A_case and \<open>ls2 = [Bk]\<close> have "CL = ls1 @ [Bk]" by auto
          then have "\<exists>rex'. [] = []  \<and> Bk#rev ls1 @ Oc # Bk \<up> Suc rex = rev CL    @ Oc # Bk \<up> Suc rex' \<and> CL \<noteq> []  \<and> last CL = Bk" (* YYYY2' *)
            by simp
          with A_case \<open>r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)\<close> and \<open>ls2 = [Bk]\<close>
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
            by force
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 12\<close> and A_case and \<open>ls2 = [Bk]\<close>
          by simp
      next
        fix C3
        assume minor: "ls2 = Bk # Oc # C3"
          (*
          A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc"
          major: "hd (rev ls1) = Oc
          ls1 \<noteq> []

          ass: ls2 = Bk # Oc # C3

          l = Bk # Oc # C3
          r = rev ls1 @ Oc # Bk \<up> Suc rex   where "hd (rev ls1) = Oc"
          
          \<longrightarrow> s11
 
          l' = Oc # C3
          r' = Bk#rev ls1 @ Oc # Bk \<up> Suc rex

         *)
        from A_case have "step0 (12, Bk # Oc # C3 ,   Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left
                              = (11, Oc # C3, Bk#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

        moreover from  A_case and major have "r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)"
          by (metis Nil_is_append_conv \<open>ls1 \<noteq> []\<close> hd_Cons_tl hd_append2 list.simps(3) rev_is_Nil_conv)

        ultimately have "step0 (12, Bk # Oc # C3 , rev ls1 @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                             = (11, Oc # C3, Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
          by (simp add: A_case)
            (* 
            CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []
            CL = ls1 @ (Bk # Oc # C3) = ls1 @ [Bk] @ (Oc # C3)

            ls1' = ls1 @ [Bk]
            ls2' = Oc # C3

            rev ls1' = Bk# (rev ls1)

            l' =  Oc # C3
            r' = rev ls1' @ Oc # Bk \<up> Suc rex \<and>

            CL = ls1' @ ls2'  \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> []

            YYYY8
              (\<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [])
         *)
        moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, Oc # C3, Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
        proof -
          from A_case and \<open>ls2 = Bk # Oc # C3\<close> have "CL = ls1 @ [Bk] @ (Oc # C3)" and "rev (ls1 @ [Bk]) = Bk # rev ls1" by auto
          with  \<open>ls1 \<noteq> []\<close>
          have "\<exists>rex' ls1' ls2'. Oc # C3 = ls2'  \<and> Bk# rev ls1 @ Oc # Bk \<up> Suc rex = rev ls1' @ Oc # Bk \<up> Suc rex' \<and> CL = ls1' @ ls2' \<and> tl ls1' \<noteq> []" (* YYYY8 *)          
            by (simp add: A_case )
          with A_case \<open>r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)\<close> and \<open>ls2 = Bk # Oc # C3\<close>
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, Oc # C3, Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
            by force
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 12\<close> and A_case and \<open>ls2 = Bk # Oc # C3\<close>
          by simp
      next
        fix C3
        assume minor: "ls2 = Oc # C3"
          (*
          A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc"
          major: "hd (rev ls1) = Oc
          ls1 \<noteq> []

          ass: ls2 = Bk # Oc # C3

          l = ls2 = Oc # C3
          r = rev ls1 @ Oc # Bk \<up> Suc rex   where "hd (rev ls1) = Oc"
          
          \<longrightarrow> s11
 
          l' = C3
          r' = Oc#rev ls1 @ Oc # Bk \<up> Suc rex

         *)
        from A_case have "step0 (12, Oc # C3 ,   Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left
                              = (11, C3, Oc#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
          by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)

        moreover from  A_case and major have "r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)"
          by (metis Nil_is_append_conv \<open>ls1 \<noteq> []\<close> hd_Cons_tl hd_append2 list.simps(3) rev_is_Nil_conv)

        ultimately have "step0 (12, Oc # C3 , rev ls1 @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                             = (11, C3, Oc# rev ls1 @ Oc # Bk \<up> Suc rex )"
          by (simp add: A_case)
            (* 
            CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []
            CL = ls1 @ (Oc # C3) = ls1 @ [Oc] @ (C3)

            ls1' = ls1 @ [Oc]
            ls2' = C3

            rev ls1' = Oc# (rev ls1)

            l' = C3
            r' = rev ls1' @ Oc # Bk \<up> Suc rex \<and>

            CL = ls1' @ ls2'  \<and> hd ls1' = Oc \<and> tl ls1' \<noteq> []

            YYYY8
              (\<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> hd ls1 = Oc \<and> tl ls1 \<noteq> [])
         *)
        moreover have "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, C3, Oc# rev ls1 @ Oc # Bk \<up> Suc rex )"
        proof -
          from A_case and \<open>ls2 = Oc # C3\<close> have "CL = ls1 @ [Oc] @ (C3)" and "rev (ls1 @ [Oc]) = Oc # rev ls1" by auto
          with  \<open>ls1 \<noteq> []\<close>
          have "\<exists>rex' ls1' ls2'. C3 = ls2'  \<and> Oc# rev ls1 @ Oc # Bk \<up> Suc rex = rev ls1' @ Oc # Bk \<up> Suc rex' \<and> CL = ls1' @ ls2'  \<and> tl ls1' \<noteq> []" (* YYYY8 *)          
            by (simp add: A_case )
          with A_case \<open>r = Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)\<close> and \<open>ls2 = Oc # C3\<close>
          show "inv_tm_erase_right_then_dblBk_left_erp CL CR (11, C3, Oc# rev ls1 @ Oc # Bk \<up> Suc rex )"
            by force
        qed
        ultimately show ?thesis
          using  assms and cf_cases and \<open>s = 12\<close> and A_case and \<open>ls2 = Oc # C3\<close>
          by simp
      qed
    next
      (* YYYY6''' *)
      assume "\<exists>rex. l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk"
      then obtain rex where
        A_case: "l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk" by blast
      then have "step0 (12, [] , Bk # rev CL @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                              = (0, [], Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover with A_case have "inv_tm_erase_right_then_dblBk_left_erp CL CR (0, [], Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by auto
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 12\<close> and A_case 
        by simp
    next
      (* YYYY9 *)
      assume "\<exists>rex. l = [] \<and> r = Bk # Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)"
      then obtain rex where
        A_case: "l = [] \<and> r = Bk # Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)" by blast
      then have "step0 (12, [] , Bk # Bk # rev CL @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                              = (0, [], Bk# Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover with A_case have "inv_tm_erase_right_then_dblBk_left_erp CL CR (0, [], Bk# Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by auto
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 12\<close> and A_case 
        by simp
    qed
  next
    assume "s = 0"
    with cf_cases and assms
    have "(\<exists>rex. l = [] \<and>  r = [Bk, Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex \<and> (CL = [] \<or> last CL = Oc) ) \<or>
          (\<exists>rex. l = [] \<and>  r = [Bk]     @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex \<and> CL \<noteq> [] \<and> last CL = Bk)"
      by auto
    then have s0_cases:
      "\<And>P. \<lbrakk> \<exists>rex. l = [] \<and>  r = [Bk, Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex \<and> (CL = [] \<or> last CL = Oc) \<Longrightarrow> P;
             \<exists>rex. l = [] \<and>  r = [Bk]     @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex \<and> CL \<noteq> [] \<and> last CL = Bk \<Longrightarrow> P \<rbrakk>
        \<Longrightarrow> P"
      by blast

    show ?thesis
    proof (rule s0_cases)
      assume "\<exists>rex. l = [] \<and> r = [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex \<and> (CL = [] \<or> last CL = Oc)"
      then obtain rex where
        A_case: "l = [] \<and> r = [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex \<and> (CL = [] \<or> last CL = Oc)" by blast
      then have "step0 (0, [] , [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex) tm_erase_right_then_dblBk_left
                              = (0, [], Bk# Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover with A_case have "inv_tm_erase_right_then_dblBk_left_erp CL CR (0, [], Bk# Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by auto
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 0\<close> and A_case 
        by simp
    next
      assume "\<exists>rex. l = [] \<and> r = [Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex \<and> CL \<noteq> [] \<and> last CL = Bk"
      then obtain rex where
        A_case: "l = [] \<and> r = [Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex \<and> CL \<noteq> [] \<and> last CL = Bk" by blast
      then have "step0 (0, [] , [Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex) tm_erase_right_then_dblBk_left
                              = (0, [], Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
      moreover with A_case have "inv_tm_erase_right_then_dblBk_left_erp CL CR (0, [], Bk # rev CL @ Oc # Bk \<up> Suc rex)"
        by auto
      ultimately show ?thesis
        using  assms and cf_cases and \<open>s = 0\<close> and A_case 
        by simp
    qed
  qed
qed

(* -------------- steps - lemma for the invariants of the ERASE path of tm_erase_right_then_dblBk_left ------------------ *)

lemma inv_tm_erase_right_then_dblBk_left_erp_steps: 
  assumes "inv_tm_erase_right_then_dblBk_left_erp CL CR cf"
  and "noDblBk CL" and "noDblBk CR"
  shows "inv_tm_erase_right_then_dblBk_left_erp CL CR (steps0 cf tm_erase_right_then_dblBk_left stp)"
proof (induct stp)
  case 0
  with assms show ?case
    by (auto simp add: inv_tm_erase_right_then_dblBk_left_erp_step step.simps steps.simps)
next
  case (Suc stp)
  with assms show ?case
    using inv_tm_erase_right_then_dblBk_left_erp_step step_red by auto 
qed


(* -------------- Partial correctness for the ERASE path of tm_erase_right_then_dblBk_left ------------------ *)

lemma tm_erase_right_then_dblBk_left_erp_partial_correctness_CL_is_Nil:
  assumes "\<exists>stp. is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
  and "noDblBk CL"
  and "noDblBk CR"
  and "CL = []"
  shows "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
proof (rule Hoare_consequence)
  show "( \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) ) \<mapsto> ( \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) )"
    by auto
next
  from assms show "inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                    \<mapsto> ( \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex) )"
    by (simp add: assert_imp_def  tape_of_list_def tape_of_nat_def)
next
  show " \<lbrace>\<lambda>tap. tap = ([Bk, Oc] @ CL, CR)\<rbrace>
           tm_erase_right_then_dblBk_left
         \<lbrace>inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR\<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r:: "cell list"
    assume major: "(l, r) = ([Bk, Oc] @ CL, CR)"
    show "\<exists>n. is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left n) \<and>
                inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                 holds_for steps0 (1, l, r) tm_erase_right_then_dblBk_left n"
    proof -
      from major and assms
      have "\<exists>stp. is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)"
        by blast
      then obtain stp where
        w_stp: "is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)" by blast
      moreover have "inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                       holds_for steps0 (1, l, r) tm_erase_right_then_dblBk_left stp"
      proof -
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (1, l, r)"
          by (simp add: major tape_of_list_def tape_of_nat_def)
        with assms
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)"
          using inv_tm_erase_right_then_dblBk_left_erp_steps by auto
        then show ?thesis
          by (smt holds_for.elims(3) inv_tm_erase_right_then_dblBk_left_erp.simps is_final_eq w_stp)
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma tm_erase_right_then_dblBk_left_erp_partial_correctness_CL_ew_Bk:
  assumes "\<exists>stp. is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
  and "noDblBk CL"
  and "noDblBk CR"
  and "CL \<noteq> []"
  and "last CL = Bk"   
  shows "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
proof (rule Hoare_consequence)
  show "( \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) ) \<mapsto> ( \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) )"
    by auto
next
  from assms show "inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                    \<mapsto> ( \<lambda>tap. \<exists>rex. tap = ([], [Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex) )"
    by (simp add: assert_imp_def  tape_of_list_def tape_of_nat_def)
next
  show " \<lbrace>\<lambda>tap. tap = ([Bk, Oc] @ CL, CR)\<rbrace>
           tm_erase_right_then_dblBk_left
         \<lbrace>inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR\<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r:: "cell list"
    assume major: "(l, r) = ([Bk, Oc] @ CL, CR)"
    show "\<exists>n. is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left n) \<and>
                inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                 holds_for steps0 (1, l, r) tm_erase_right_then_dblBk_left n"
    proof -
      from major and assms
      have "\<exists>stp. is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)"
        by blast
      then obtain stp where
        w_stp: "is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)" by blast
      moreover have "inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                       holds_for steps0 (1, l, r) tm_erase_right_then_dblBk_left stp"
      proof -
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (1, l, r)"
          by (simp add: major tape_of_list_def tape_of_nat_def)
        with assms
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)"
          using inv_tm_erase_right_then_dblBk_left_erp_steps by auto
        then show ?thesis
          by (smt holds_for.elims(3) inv_tm_erase_right_then_dblBk_left_erp.simps is_final_eq w_stp)
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma tm_erase_right_then_dblBk_left_erp_partial_correctness_CL_ew_Oc:
  assumes "\<exists>stp. is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
    and "noDblBk CL"
    and "noDblBk CR"
    and "CL \<noteq> []"
    and "last CL = Oc"   
  shows "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
proof (rule Hoare_consequence)
  show "( \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) ) \<mapsto> ( \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) )"
    by auto
next
  from assms show "inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                    \<mapsto> ( \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex) )"
    by (simp add: assert_imp_def  tape_of_list_def tape_of_nat_def)
next
  show " \<lbrace>\<lambda>tap. tap = ([Bk, Oc] @ CL, CR)\<rbrace>
           tm_erase_right_then_dblBk_left
         \<lbrace>inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR\<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r:: "cell list"
    assume major: "(l, r) = ([Bk, Oc] @ CL, CR)"
    show "\<exists>n. is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left n) \<and>
                inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                 holds_for steps0 (1, l, r) tm_erase_right_then_dblBk_left n"
    proof -
      from major and assms
      have "\<exists>stp. is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)"
        by blast
      then obtain stp where
        w_stp: "is_final (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)" by blast
      moreover have "inv_tm_erase_right_then_dblBk_left_erp_s0 CL CR
                       holds_for steps0 (1, l, r) tm_erase_right_then_dblBk_left stp"
      proof -
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (1, l, r)"
          by (simp add: major tape_of_list_def tape_of_nat_def)
        with assms
        have "inv_tm_erase_right_then_dblBk_left_erp CL CR (steps0 (1, l, r) tm_erase_right_then_dblBk_left stp)"
          using inv_tm_erase_right_then_dblBk_left_erp_steps by auto
        then show ?thesis
          by (smt holds_for.elims(3) inv_tm_erase_right_then_dblBk_left_erp.simps is_final_eq w_stp)
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed


(* -------------- Termination for the ERASE path of tm_erase_right_then_dblBk_left ------------------ *)
(* 
    Lexicographic orders (See List.measures)
    quote: "These are useful for termination proofs"
    
    lemma in_measures[simp]:
      "(x, y) \<in> measures [] = False"
      "(x, y) \<in> measures (f # fs)
             = (f x < f y \<or> (f x = f y \<and> (x, y) \<in> measures fs))"
*)

(* Assemble a lexicographic measure function for the ERASE path *)

definition measure_tm_erase_right_then_dblBk_left_erp :: "(config \<times> config) set"
  where
    "measure_tm_erase_right_then_dblBk_left_erp = measures [
         \<lambda>(s, l, r). (
              if s = 0
              then 0
              else if s < 6
                   then 13 - s
                   else 1),

         \<lambda>(s, l, r). (
              if s = 6
              then if r = [] \<or> (hd r) = Bk
                   then 1
                   else 2
              else 0 ),

         \<lambda>(s, l, r). (
              if 7 \<le> s \<and> s \<le> 9
              then 2+ length r
              else 1), 

         \<lambda>(s, l, r). (
              if 7 \<le> s \<and> s \<le> 9
              then  
                if r = [] \<or> hd r = Bk
                then 2
                else 3
              else 1),

         \<lambda>(s, l, r).(
              if 7 \<le> s \<and> s \<le> 10
              then 13 - s
              else 1),

         \<lambda>(s, l, r). (
              if 10 \<le> s 
              then 2+ length l
              else 1),


         \<lambda>(s, l, r). (
              if 11 \<le> s
              then if hd r = Oc
                   then 3
                   else 2
              else 1),

         \<lambda>(s, l, r).(
              if 11 \<le> s
              then 13 - s
              else 1)

      ]"

lemma wf_measure_tm_erase_right_then_dblBk_left_erp: "wf measure_tm_erase_right_then_dblBk_left_erp"
  unfolding measure_tm_erase_right_then_dblBk_left_erp_def
  by (auto)

lemma measure_tm_erase_right_then_dblBk_left_erp_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_tm_erase_right_then_dblBk_left_erp\<rbrakk>
   \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_tm_erase_right_then_dblBk_left_erp
  by (metis wf_iff_no_infinite_down_chain)

lemma spike_erp_cases:
"CL \<noteq> [] \<and> last CL = Bk \<or> CL \<noteq> [] \<and> last CL = Oc \<or> CL = []"
  using cell.exhaust by blast

lemma tm_erase_right_then_dblBk_left_erp_halts:
  assumes "noDblBk CL"
    and "noDblBk CR"
  shows
    "\<exists>stp. is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
proof (induct rule: measure_tm_erase_right_then_dblBk_left_erp_induct)
  case (Step stp)
  then have not_final: "\<not> is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)" .

  have INV: "inv_tm_erase_right_then_dblBk_left_erp CL CR (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
  proof (rule_tac inv_tm_erase_right_then_dblBk_left_erp_steps)
    show  "inv_tm_erase_right_then_dblBk_left_erp CL CR (1, [Bk,Oc] @ CL, CR)"
      by (simp add: tape_of_list_def tape_of_nat_def )
  next
    from assms show "noDblBk CL" by auto
  next
    from assms show "noDblBk CR" by auto
  qed
  have SUC_STEP_RED: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
        step0 (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp) tm_erase_right_then_dblBk_left"
    by (rule step_red)
  show "( steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp),
          steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp
        ) \<in> measure_tm_erase_right_then_dblBk_left_erp"
  proof (cases "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp")
    case (fields s l r)
    then have
      cf_at_stp: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (s, l, r)" .
    show ?thesis
    proof (rule tm_erase_right_then_dblBk_left_erp_cases)
      from INV and cf_at_stp
      show "inv_tm_erase_right_then_dblBk_left_erp CL CR (s, l, r)" by auto
    next
      assume "s=0" (* not possible *)
      with cf_at_stp not_final
      show ?thesis by auto
    next
      assume "s=1"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (1, l, r)"
        by auto
      with cf_at_stp  and \<open>s=1\<close> and INV
      have unpacked_INV: "(l = [Bk,Oc] @ CL \<and> r = CR)"
        by auto      
          (* compute the next state *)
      show ?thesis
      proof (cases CR)
        case Nil
        then have minor: "CR = []" .

        with unpacked_INV cf_at_stp and \<open>s=1\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left"
          by auto
        also with minor and unpacked_INV
        have "... = (2,Oc#CL, Bk#CR)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (2,Oc#CL, Bk#CR)"
          by auto
            (* establish measure *)
        with cf_at_current show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        case (Cons a rs)
        then have major: "CR = a # rs" .
        then show ?thesis
        proof (cases a)
          case Bk
          with major have minor: "CR = Bk#rs" by auto
          with unpacked_INV cf_at_stp and \<open>s=1\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left"
            by auto
          also with minor and unpacked_INV
          have "... = (2,Oc#CL, Bk#CR)"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (2,Oc#CL, Bk#CR)"
            by auto
              (* establish measure *)
          with cf_at_current show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          case Oc
          with major have minor: "CR = Oc#rs" by auto
          with unpacked_INV cf_at_stp and \<open>s=1\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left"
            by auto
          also with minor and unpacked_INV
          have "... = (2,Oc#CL, Bk#CR)"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (2,Oc#CL, Bk#CR)"
            by auto
              (* establish measure *)
          with cf_at_current show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        qed
      qed
    next
      assume "s=2"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (2, l, r)"
        by auto
      with cf_at_stp  and \<open>s=2\<close> and INV
      have unpacked_INV: "(l = [Oc]    @ CL \<and> r = Bk#CR)"
        by auto
          (* compute the next state *)
      then have minor: "r = Bk#CR" by auto
      with unpacked_INV cf_at_stp and \<open>s=2\<close> and SUC_STEP_RED
      have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (2, [Oc] @ CL, Bk#CR) tm_erase_right_then_dblBk_left"
        by auto
      also with minor and unpacked_INV
      have "... = (3,CL, Oc#Bk#CR)"
        by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
      finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (3,CL, Oc#Bk#CR)"
        by auto
          (* establish measure *)
      with cf_at_current show ?thesis
        by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
    next
      assume "s=3"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (3, l, r)"
        by auto
      with cf_at_stp  and \<open>s=3\<close> and INV
      have unpacked_INV: "(l =           CL \<and> r = Oc#Bk#CR)"
        by auto
          (* compute the next state *)
      then have minor: "r = Oc#Bk#CR" by auto
      with unpacked_INV cf_at_stp and \<open>s=3\<close> and SUC_STEP_RED
      have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (3, CL, Oc#Bk#CR) tm_erase_right_then_dblBk_left"
        by auto
      also with minor and unpacked_INV
      have "... = (5,[Oc] @ CL, Bk#CR)"
        by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
      finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (5,[Oc] @ CL, Bk#CR)"
        by auto
          (* establish measure *)
      with cf_at_current show ?thesis
        by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
    next
      assume "s=5"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (5, l, r)"
        by auto
      with cf_at_stp  and \<open>s=5\<close> and INV
      have unpacked_INV: "(l = [Oc]    @ CL \<and> r = Bk#CR)"
        by auto
          (* compute the next state *)
      then have minor: "r = Bk#CR" by auto
      with unpacked_INV cf_at_stp and \<open>s=5\<close> and SUC_STEP_RED
      have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (5, [Oc]    @ CL, Bk#CR) tm_erase_right_then_dblBk_left"
        by auto
      also with minor and unpacked_INV
      have "... = (6, [Bk,Oc] @ CL, CR)"
        by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
      finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (6, [Bk,Oc] @ CL, CR)"
        by auto
          (* establish measure *)
      with cf_at_current show ?thesis
        by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
    next
      assume "s=6"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (6, l, r)"
        by auto
      with cf_at_stp  and \<open>s=6\<close> and INV
      have unpacked_INV: "(l = [Bk,Oc] @ CL \<and> ( (CR = [] \<and> r = CR) \<or>
                                                (CR \<noteq> [] \<and> (r = CR \<or> r = Bk # tl CR))
                                               ))"
        by auto
      then have unpacked_INV': "l = [Bk,Oc] @ CL \<and> CR = [] \<and> r = CR \<or>
                               l = [Bk,Oc] @ CL \<and> CR \<noteq> [] \<and> r = Oc # tl CR \<or>
                               l = [Bk,Oc] @ CL \<and> CR \<noteq> [] \<and> r = Bk # tl CR"
        by (metis (full_types) cell.exhaust list.sel(3) neq_Nil_conv)
      then show ?thesis
      proof
        assume minor: "l = [Bk, Oc] @ CL \<and> CR = [] \<and> r = CR"
        with unpacked_INV cf_at_stp and \<open>s=6\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (6, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left"
          by auto
        also with minor and unpacked_INV
        have "... = (7,Bk#[Bk, Oc] @ CL, CR)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (7,Bk#[Bk, Oc] @ CL, CR)"
          by auto
            (* establish measure *)
        with cf_at_current show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        assume "l = [Bk, Oc] @ CL \<and> CR \<noteq> [] \<and> r = Oc # tl CR \<or> l = [Bk, Oc] @ CL \<and> CR \<noteq> [] \<and> r = Bk # tl CR"
        then show ?thesis
        proof
          assume minor: "l = [Bk, Oc] @ CL \<and> CR \<noteq> [] \<and> r = Bk # tl CR"
          with unpacked_INV cf_at_stp and \<open>s=6\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (6, [Bk, Oc] @ CL, Bk # tl CR) tm_erase_right_then_dblBk_left"
            by auto
          also with minor
          have "... = (7,Bk#[Bk, Oc] @ CL, tl CR)"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (7,Bk#[Bk, Oc] @ CL, tl CR)"
            by auto
              (* establish measure *)
          with cf_at_current show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          assume minor: "l = [Bk, Oc] @ CL \<and> CR \<noteq> [] \<and> r = Oc # tl CR"
          with unpacked_INV cf_at_stp and \<open>s=6\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (6, [Bk, Oc] @ CL, Oc # tl CR) tm_erase_right_then_dblBk_left"
            by auto
          also with minor
          have "... = (6, [Bk, Oc] @ CL, Bk # tl CR)"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (6, [Bk, Oc] @ CL, Bk # tl CR)"
            by auto
              (* establish measure *)
          with cf_at_current and minor show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        qed
      qed
    next
      assume "s=7"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (7, l, r)"
        by auto
      with cf_at_stp  and \<open>s=7\<close> and INV
      have  "(\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs. CR = rs @ r)"
        by auto
      then obtain lex rs where
        unpacked_INV: "l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> CR = rs @ r" by blast
          (* compute the next state *)
      show ?thesis
      proof (cases r)
        case Nil
        then have minor: "r = []" .
        with unpacked_INV cf_at_stp and \<open>s=7\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (7, Bk \<up> Suc lex @ [Bk,Oc] @ CL, r) tm_erase_right_then_dblBk_left"
          by auto
        also with minor and unpacked_INV
        have "... = (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, r)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, r)"
          by auto
            (* establish measure *)
        with cf_at_current and minor show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        case (Cons a rs')
        then have major: "r = a # rs'" .
        then show ?thesis
        proof (cases a)
          case Bk
          with major have minor: "r = Bk#rs'" by auto

          with unpacked_INV cf_at_stp and \<open>s=7\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (7,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, r) tm_erase_right_then_dblBk_left"
            by auto
          also with minor and unpacked_INV
          have "... = (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs')"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (9, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs')"
            by auto
              (* establish measure *)
          with cf_at_current and minor show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          case Oc
          with major have minor: "r = Oc#rs'" by auto

          with unpacked_INV cf_at_stp and \<open>s=7\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (7,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, Oc#rs') tm_erase_right_then_dblBk_left"
            by auto
          also with minor and unpacked_INV
          have "... = (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (8, Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
            by auto
              (* establish measure *)
          with cf_at_current and minor show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        qed
      qed
    next
      assume "s=8"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (8, l, r)"
        by auto
      with cf_at_stp  and \<open>s=8\<close> and INV
      have  "(\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs1 rs2. CR = rs1 @ [Oc] @ rs2 \<and> r = Bk#rs2)"
        by auto
      then obtain lex rs1 rs2 where
        unpacked_INV: "l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> CR = rs1 @ [Oc] @ rs2 \<and> r = Bk#rs2 " by blast
          (* compute the next state *)
      with  cf_at_stp and \<open>s=8\<close> and SUC_STEP_RED
      have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (8,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs2) tm_erase_right_then_dblBk_left"
        by auto
      also with unpacked_INV
      have "... = (7, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs2)"
        by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
      finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                      = (7, Bk \<up> Suc (Suc lex) @ [Bk,Oc] @ CL, rs2)"
        by auto
          (* establish measure *)
      with cf_at_current and unpacked_INV show ?thesis
        by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
    next
      assume "s=9"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (9, l, r)"
        by auto
      with cf_at_stp  and \<open>s=9\<close> and INV
      have  "(\<exists>lex. l = Bk \<up> Suc lex @ [Bk,Oc] @ CL) \<and> (\<exists>rs. CR = rs @ [Bk] @ r \<or> CR = rs \<and> r = [])"
        by auto
      then obtain lex rs where
        "l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> (CR = rs @ [Bk] @ r \<or> CR = rs \<and> r = [])" by blast
      then have unpacked_INV: "l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> CR = rs @ [Bk] @ r \<or>
                               l = Bk \<up> Suc lex @ [Bk,Oc] @ CL \<and> CR = rs \<and> r = []" by auto
      then show ?thesis
      proof
        (* compute the next state *)
        assume major: "l = Bk \<up> Suc lex @ [Bk, Oc] @ CL \<and> CR = rs @ [Bk] @ r"
        show ?thesis
        proof (cases r)
          case Nil
          then have minor: "r = []" .
          with unpacked_INV cf_at_stp and \<open>s=9\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (9, Bk \<up> Suc lex @ [Bk,Oc] @ CL, r) tm_erase_right_then_dblBk_left"
            by auto
          also with minor and unpacked_INV
          have "... = (10, Bk \<up> lex @ [Bk,Oc] @ CL, Bk#r)"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (10, Bk \<up> lex @ [Bk,Oc] @ CL, Bk#r)"
            by auto
              (* establish measure *)
          with cf_at_current and minor show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          case (Cons a rs')
          then have major2: "r = a # rs'" .
          then show ?thesis
          proof (cases a)
            case Bk
            with major2 have minor: "r = Bk#rs'" by auto
            with unpacked_INV cf_at_stp and \<open>s=9\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (9,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs') tm_erase_right_then_dblBk_left"
              by auto
            also with minor and unpacked_INV
            have "... = (10, Bk \<up> lex @ [Bk,Oc] @ CL, Bk#Bk#rs')"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (10, Bk \<up> lex @ [Bk,Oc] @ CL, Bk#Bk#rs')"
              by auto
                (* establish measure *)
            with cf_at_current and minor show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          next
            case Oc
            with major2 have minor: "r = Oc#rs'" by auto
            with unpacked_INV cf_at_stp and \<open>s=9\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (9,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, Oc#rs') tm_erase_right_then_dblBk_left"
              by auto
            also with minor and unpacked_INV
            have "... = (8,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (8,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, Bk#rs')"
              by auto
                (* establish measure *)
            with cf_at_current and minor show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          qed
        qed
      next
        (* compute the next state *)
        assume major: "l = Bk \<up> Suc lex @ [Bk, Oc] @ CL \<and> CR = rs \<and> r = []"
        with unpacked_INV cf_at_stp and \<open>s=9\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (9,  Bk \<up> Suc lex @ [Bk,Oc] @ CL, []) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV
        have "... = (10,  Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (10,  Bk \<up> lex @ [Bk,Oc] @ CL, [Bk])"
          by auto
            (* establish measure *)
        with cf_at_current show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      qed
    next
      assume "s=10"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (10, l, r)"
        by auto
      with cf_at_stp  and \<open>s=10\<close> and INV
      have  "(\<exists>lex rex. l = Bk \<up> lex @ [Bk,Oc] @ CL \<and> r = Bk \<up> Suc rex) \<or>
             (\<exists>rex. l = [Oc] @ CL \<and> r = Bk \<up> Suc rex) \<or>
             (\<exists>rex. l = CL \<and> r = Oc # Bk \<up> Suc rex)"
        by auto
      then have s10_cases:
        "\<And>P. \<lbrakk> \<exists>lex rex. l = Bk \<up> lex @ [Bk,Oc] @ CL \<and> r = Bk \<up> Suc rex \<Longrightarrow> P;
             \<exists>rex. l = [Oc] @ CL \<and> r = Bk \<up> Suc rex \<Longrightarrow> P;
             \<exists>rex. l = CL \<and> r = Oc # Bk \<up> Suc rex \<Longrightarrow> P
            \<rbrakk> \<Longrightarrow> P"
        by blast
      show ?thesis
      proof (rule s10_cases)
        assume "\<exists>lex rex. l = Bk \<up> lex @ [Bk, Oc] @ CL \<and> r = Bk \<up> Suc rex"
        then obtain lex rex where
          unpacked_INV: "l = Bk \<up> lex @ [Bk, Oc] @ CL \<and> r = Bk \<up> Suc rex" by blast
        with unpacked_INV cf_at_stp and \<open>s=10\<close> and SUC_STEP_RED
        have todo_step: "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (10, Bk \<up> lex @ [Bk, Oc] @ CL, Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
          by auto
        show ?thesis
        proof (cases lex)
          case 0
          then have "lex = 0" .
              (* compute the next state *)
          then have "step0 (10, Bk \<up> lex @ [Bk, Oc] @ CL, Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                     = (10, [Oc] @ CL, Bk \<up> Suc (Suc rex))"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
          with todo_step 
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (10, [Oc] @ CL, Bk \<up> Suc (Suc rex))"
            by auto
              (* establish measure *)
          with \<open>lex = 0\<close> and cf_at_current and unpacked_INV show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          case (Suc nat)
          then have "lex = Suc nat" .
              (* compute the next state *)
          then have "step0 (10, Bk \<up> lex @ [Bk, Oc] @ CL, Bk \<up> Suc rex) tm_erase_right_then_dblBk_left
                     = (10, Bk \<up> nat @ [Bk, Oc] @ CL, Bk \<up> Suc (Suc rex))"
            by (simp add:  tm_erase_right_then_dblBk_left_def step.simps steps.simps numeral_eqs_upto_12)
          with todo_step 
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (10, Bk \<up> nat @ [Bk, Oc] @ CL, Bk \<up> Suc (Suc rex))"
            by auto
              (* establish measure *)
          with \<open>lex = Suc nat\<close> cf_at_current and unpacked_INV show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        qed
      next
        assume "\<exists>rex. l = [Oc] @ CL \<and> r = Bk \<up> Suc rex"
        then obtain rex where
          unpacked_INV: "l = [Oc] @ CL \<and> r = Bk \<up> Suc rex" by blast
            (* compute the next state *)
        with unpacked_INV cf_at_stp and \<open>s=10\<close> and SUC_STEP_RED
        have todo_step: "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (10, [Oc] @ CL, Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV
        have "... = (10, CL, Oc# Bk \<up> (Suc rex))"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (10, CL, Oc# Bk \<up> (Suc rex))"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        assume "\<exists>rex. l = CL \<and> r = Oc # Bk \<up> Suc rex"
        then obtain rex where
          unpacked_INV: "l = CL \<and> r = Oc # Bk \<up> Suc rex" by blast
        show ?thesis
        proof (cases CL) (* here, we start decomposing CL in the loop 'move to left until Oc *)
          case Nil
          then have minor: "CL = []" .
          with unpacked_INV cf_at_stp and \<open>s=10\<close> and SUC_STEP_RED
            (* compute the next state *)
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (10, [], Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
            by auto
          also with minor and unpacked_INV
          have "... = (11, [], Bk#Oc# Bk \<up> (Suc rex))"  (* YYYY1' *)
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, [], Bk#Oc# Bk \<up> (Suc rex))"
            by auto
              (* establish measure *)
          with cf_at_current show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          case (Cons a rs')
          then have major2: "CL = a # rs'" .
          then show ?thesis
          proof (cases a)
            case Bk
            with major2 have minor: "CL = Bk#rs'" by auto
            with unpacked_INV cf_at_stp and \<open>s=10\<close> and SUC_STEP_RED
              (* compute the next state *)
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (10,  Bk#rs', Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also with minor and unpacked_INV
            have "... = (11, rs', Bk# Oc # Bk \<up> Suc rex)" (* YYYY2',YYYY3 *)
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, rs', Bk# Oc # Bk \<up> Suc rex)"
              by auto
                (* establish measure *)
            with cf_at_current and minor show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          next
            case Oc
            with major2 have minor: "CL = Oc#rs'" by auto
            with unpacked_INV cf_at_stp and \<open>s=10\<close> and SUC_STEP_RED
              (* compute the next state *)
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (10,  Oc#rs', Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also with minor and unpacked_INV
            have "... = (11, rs', Oc# Oc # Bk \<up> Suc rex)" (* YYYY2'', YYYY5, YYYY6, YYYY7 *)
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, rs', Oc# Oc # Bk \<up> Suc rex)"
              by auto
                (* establish measure *)
            with cf_at_current and minor show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          qed
        qed
      qed
    next
      assume "s=11"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (11, l, r)"
        by auto
      with cf_at_stp  and \<open>s=11\<close> and INV
      have "(\<exists>rex.         l = []         \<and> r = Bk# rev CL    @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc))              \<or>
          (\<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk ) \<or>
          (\<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc ) \<or>

          (\<exists>rex.         l = [Bk]       \<and> r = rev [Oc]      @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]) \<or>

          (\<exists>rex ls1 ls2. l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc] ) \<or>
          (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk] ) \<or>
          (\<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc] ) \<or>
 
          (\<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> tl ls1 \<noteq> [])"
        by auto

      then have s11_cases:
        "\<And>P. \<lbrakk> \<exists>rex.         l = []         \<and> r = Bk# rev CL    @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc) \<Longrightarrow> P;
             \<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk \<Longrightarrow> P;
             \<exists>rex.         l = []         \<and> r = rev CL        @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc \<Longrightarrow> P;

             \<exists>rex.         l = [Bk]       \<and> r = rev [Oc]      @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk] \<Longrightarrow> P;

             \<exists>rex ls1 ls2. l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc] \<Longrightarrow> P;
             \<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Bk] \<Longrightarrow> P;
             \<exists>rex ls1 ls2. l =    Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc#ls2    \<and> ls1 = [Oc] \<Longrightarrow> P;

             \<exists>rex ls1 ls2. l =       ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2       \<and> tl ls1 \<noteq> [] \<Longrightarrow> P
            \<rbrakk> \<Longrightarrow> P"
        by blast
      show ?thesis
      proof (rule s11_cases)
        assume "\<exists>rex ls1 ls2. l = Bk # Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk # Oc # ls2 \<and> ls1 = [Oc]" (* YYYY6 *)
        then obtain rex ls1 ls2 where
          unpacked_INV: "l = Bk#Oc#ls2  \<and> r = rev ls1       @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Bk#Oc#ls2 \<and> ls1 = [Oc]" by blast
        from unpacked_INV cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
        have todo_step: "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (11, Bk#Oc#ls2, r) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV
        have "... = (11, Oc # ls2, Bk # r)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, Oc # ls2, Bk # r)"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        assume "\<exists>rex ls1 ls2. l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Oc]" (* YYYY7 *)
        then obtain rex ls1 ls2 where
          unpacked_INV: "l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Oc]" by blast
        from unpacked_INV cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
        have todo_step: "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (11, l, r) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV
        have "... = (11, ls2, Oc#r)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, ls2, Oc#r)"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        assume "\<exists>rex. l = [Bk] \<and> r = rev [Oc] @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]" (* YYYY5 *)
        then obtain rex where
          unpacked_INV: "l = [Bk] \<and> r = rev [Oc] @ Oc # Bk \<up> Suc rex \<and> CL = [Oc, Bk]" by blast
            (* compute the next state *)
        from unpacked_INV cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (11, l, r) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV
        have "... = (11, [], Bk#r)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, [], Bk#r)"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        assume "\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []" (* YYYY8 *)
        then obtain rex ls1 ls2 where
          A_case: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> tl ls1 \<noteq> []" by blast
            (* we have to decompose both ls1 and ls2 in order to predict the next step *)
        then have "\<exists>z b bs. ls1 = z#bs@[b]"  (* the symbol z does not matter *) 
          by (metis Nil_tl list.exhaust_sel rev_exhaust)
        then have "\<exists>z bs. ls1 = z#bs@[Bk] \<or> ls1 = z#bs@[Oc]"
          using cell.exhaust by blast
        then obtain z bs where w_z_bs: "ls1 = z#bs@[Bk] \<or> ls1 = z#bs@[Oc]" by blast
        then show ?thesis
        proof
          assume major1: "ls1 = z # bs @ [Bk]"
          then have major2: "rev ls1 = Bk#(rev bs)@[z]" by auto  (* in this case all transitions will be s11 \<longrightarrow> s12 *)
          show ?thesis
          proof  (rule noDblBk_cases)
            from \<open>noDblBk CL\<close> show "noDblBk CL" .
          next
            from A_case show "CL = ls1 @ ls2" by auto
          next
            assume minor: "ls2 = []"
              (* compute the next state *)
            with A_case major2 cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (11, [], Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also 
            have "... = (12, [], Bk#Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (12, [], Bk#Bk#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
              by auto
                (* establish measure *)
            with cf_at_current show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          next
            assume "ls2 = [Bk]"
            with A_case \<open>rev ls1 = Bk#(rev bs)@[z]\<close> and \<open>ls2 = [Bk]\<close>
            have "ls1 = z#bs@[Bk]" and "CL = z#bs@[Bk]@[Bk]" by auto
            with \<open>noDblBk CL\<close> have False               
              by (metis A_case  \<open>ls2 = [Bk]\<close> append_Cons hasDblBk_L5 major2)
            then show ?thesis by auto
          next
            fix C3
            assume minor: "ls2 = Bk # Oc # C3"
            with A_case and major2 have "CL = z # bs @ [Bk] @ Bk # Oc # C3" by auto
            with \<open>noDblBk CL\<close> have False
              by (metis append.left_neutral append_Cons append_assoc hasDblBk_L1 major1 minor)
            then show ?thesis by auto     
          next
            fix C3
            assume minor: "ls2 = Oc # C3"
              (* compute the next state *)
            with A_case major2 cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (11, Oc # C3 , Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also 
            have "... = (12, C3, Oc#Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex )"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (12, C3, Oc#Bk#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex )"
              by auto
                (* establish measure *)
            with A_case minor cf_at_current  show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          qed
        next
          assume major1: "ls1 = z # bs @ [Oc]"
          then have major2: "rev ls1 = Oc#(rev bs)@[z]" by auto (* in this case all transitions will be s11 \<longrightarrow> s11 *)
          show ?thesis
          proof  (rule noDblBk_cases)
            from \<open>noDblBk CL\<close> show "noDblBk CL" .
          next
            from A_case show "CL = ls1 @ ls2" by auto
          next
            assume minor: "ls2 = []"
              (* compute the next state *)
            with A_case major2 cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (11, [] , Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also 
            have "... = (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex)"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex)"
              by auto
                (* establish measure *)
            with A_case minor major2 cf_at_current show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          next
            assume minor: "ls2 = [Bk]"
              (* compute the next state *)
            with A_case major2 cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (11, [Bk] , Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also 
            have "... = (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, [], Bk#Oc#(rev bs)@[z] @ Oc # Bk \<up> Suc rex )"
              by auto
                (* establish measure *)
            with A_case minor major2 cf_at_current show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          next
            fix C3
            assume minor: "ls2 = Bk # Oc # C3"
              (* compute the next state *)
            with A_case major2 cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (11, Bk # Oc # C3 , Oc # rev bs @ [z]  @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also 
            have "... = (11, Oc # C3, Bk#Oc # rev bs @ [z]  @ Oc # Bk \<up> Suc rex )"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) = (11, Oc # C3, Bk#Oc # rev bs @ [z]  @ Oc # Bk \<up> Suc rex )"
              by auto
                (* establish measure *)
            with A_case minor major2 cf_at_current show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          next
            fix C3
            assume minor: "ls2 = Oc # C3"
              (* compute the next state *)
            with A_case major2 cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
            have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (11, Oc # C3 , Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
              by auto
            also 
            have "... = (11, C3, Oc#Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex)"
              by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
            finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                        = (11, C3, Oc#Oc#(rev bs)@[z]  @ Oc # Bk \<up> Suc rex)"
              by auto
                (* establish measure *)
            with A_case minor major2 cf_at_current show ?thesis
              by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
          qed
        qed
      next
        assume "\<exists>rex ls1 ls2. l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Bk]" (* YYYY3 *)
        then obtain rex ls1 ls2 where
          unpacked_INV: "l = Oc # ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ Oc # ls2 \<and> ls1 = [Bk]" by blast
            (* compute the next state *)
        from unpacked_INV cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (11, l, r) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV
        have "... = (12, ls2, Oc#[Bk] @ Oc # Bk \<up> Suc rex )"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                    = (12, ls2, Oc#[Bk] @ Oc # Bk \<up> Suc rex )"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        assume "\<exists>rex. l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)"  (* YYYY1' *)
        then obtain rex where
          unpacked_INV: "l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)" by blast
            (* compute the next state *)
        from unpacked_INV cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (11, l, r) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV
        have "... = (12, [], Bk#Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                    = (12, [], Bk#Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next      
        assume "\<exists>rex. l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk" (* YYYY2' *)
        then obtain rex where
          unpacked_INV: "l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk" by blast
        then have "hd (rev CL) = Bk"
          by (simp add: hd_rev)
            (* compute the next state *)
        from unpacked_INV cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (11, l, r) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV and \<open>hd (rev CL) = Bk\<close>
        have "... = (12, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                    = (12, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next      
        assume "\<exists>rex. l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc" (* YYYY2'' *)
        then obtain rex where
          unpacked_INV: "l = [] \<and> r = rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Oc" by blast
        then have "hd (rev CL) = Oc"
          by (simp add: hd_rev)
            (* compute the next state *)
        from unpacked_INV cf_at_stp and \<open>s=11\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                         step0 (11, l, r) tm_erase_right_then_dblBk_left"
          by auto
        also with unpacked_INV and \<open>hd (rev CL) = Oc\<close>
        have "... = (11, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                    = (11, [], Bk # rev CL @ Oc # Bk \<up> Suc rex )"
          by auto
            (* establish measure *)
        with cf_at_current and unpacked_INV and \<open>hd (rev CL) = Oc\<close> show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      qed
    next
      assume "s=12"
        (* get the invariant of the state *)
      with cf_at_stp
      have cf_at_current: "steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp = (12, l, r)"
        by auto
      with cf_at_stp  and \<open>s=12\<close> and INV
      have "
          (\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc) \<or>
          (\<exists>rex.         l = []  \<and> r = Bk#rev CL    @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk) \<or>
          (\<exists>rex.         l = []  \<and> r = Bk#Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc))"
        by auto

      then have s12_cases:
        "\<And>P. \<lbrakk> \<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2  \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc \<Longrightarrow> P;
             \<exists>rex. l = []  \<and> r = Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk \<Longrightarrow> P;
             \<exists>rex. l = []  \<and> r = Bk#Bk#rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc) \<Longrightarrow> P \<rbrakk>
        \<Longrightarrow> P"
        by blast
      show ?thesis
      proof (rule s12_cases)
        (* YYYY4 *)
        assume "\<exists>rex ls1 ls2. l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2 \<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc"
        then obtain rex ls1 ls2 where
          unpacked_INV: "l = ls2 \<and> r = rev ls1 @ Oc # Bk \<up> Suc rex \<and> CL = ls1 @ ls2\<and> tl ls1 \<noteq> [] \<and> last ls1 = Oc" by blast
        then have "ls1 \<noteq> []" by auto 
        with unpacked_INV have major: "hd (rev ls1) = Oc"
          by (simp add: hd_rev)
        with unpacked_INV and major have minor2: "r = Oc#tl ((rev ls1) @ Oc # Bk \<up> Suc rex)"
          by (metis Nil_is_append_conv \<open>ls1 \<noteq> []\<close> hd_Cons_tl hd_append2 list.simps(3) rev_is_Nil_conv)

        show ?thesis
        proof  (rule noDblBk_cases)
          from \<open>noDblBk CL\<close> show "noDblBk CL" .
        next
          from unpacked_INV show "CL = ls1 @ ls2" by auto
        next
          assume minor: "ls2 = []"
            (* compute the next state *)
          with unpacked_INV minor minor2 major cf_at_stp and \<open>s=12\<close> and \<open>ls1 \<noteq> []\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (12, [] ,   Oc#tl ((rev ls1) @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left"
            by auto
          also 
          have "... = (11, [], Bk#Oc#tl ((rev ls1) @ Oc # Bk \<up> Suc rex))"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          also with unpacked_INV and minor2 have "... =  (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
            by auto
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                 = (11, [], Bk# rev ls1 @ Oc # Bk \<up> Suc rex )"
            by auto
              (* establish measure *)
          with unpacked_INV minor major minor2 cf_at_current \<open>ls1 \<noteq> []\<close> show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          assume minor: "ls2 = [Bk]"
            (* compute the next state *)
          with unpacked_INV minor minor2 major cf_at_stp and \<open>s=12\<close> and \<open>ls1 \<noteq> []\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (12, [Bk] ,   Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left"
            by auto
          also have "... =  (11, [], Bk#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                 = (11, [], Bk#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
            by auto
              (* establish measure *)
          with unpacked_INV minor major minor2 cf_at_current \<open>ls1 \<noteq> []\<close> show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          fix C3
          assume minor: "ls2 = Bk # Oc # C3"
            (* compute the next state *)
          with unpacked_INV minor minor2 major cf_at_stp and \<open>s=12\<close> and \<open>ls1 \<noteq> []\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (12, Bk # Oc # C3 ,   Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left"
            by auto
          also have "... =  (11, Oc # C3, Bk#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                 = (11, Oc # C3, Bk#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
            by auto
              (* establish measure *)
          with unpacked_INV minor major minor2 cf_at_current \<open>ls1 \<noteq> []\<close> show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        next
          fix C3
          assume minor: "ls2 = Oc # C3"
            (* compute the next state *)
          with unpacked_INV minor minor2 major cf_at_stp and \<open>s=12\<close> and \<open>ls1 \<noteq> []\<close> and SUC_STEP_RED
          have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (12, Oc # C3 ,   Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex)) tm_erase_right_then_dblBk_left"
            by auto
          also have "... =  (11, C3, Oc#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
            by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                 = (11, C3, Oc#Oc#tl (rev ls1 @ Oc # Bk \<up> Suc rex ))"
            by auto
              (* establish measure *)
          with unpacked_INV minor major minor2 cf_at_current \<open>ls1 \<noteq> []\<close> show ?thesis
            by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
        qed
      next
        (* YYYY6''' *)
        assume "\<exists>rex. l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk"
        then obtain rex where
          unpacked_INV: "l = [] \<and> r = Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> CL \<noteq> [] \<and> last CL = Bk" by blast
            (* compute the next state *)
        with cf_at_stp and \<open>s=12\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (12, [] , Bk # rev CL @ Oc # Bk \<up> Suc rex)  tm_erase_right_then_dblBk_left"
          by auto

        also
        have "... = (0, [], Bk # rev CL @ Oc # Bk \<up> Suc rex)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                    = (0, [], Bk # rev CL @ Oc # Bk \<up> Suc rex)"
          by auto
            (* establish measure *)
        with cf_at_current  show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      next
        (* YYYY9 *)
        assume "\<exists>rex. l = [] \<and> r = Bk # Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)"
        then obtain rex where
          unpacked_INV: "l = [] \<and> r = Bk # Bk # rev CL @ Oc # Bk \<up> Suc rex \<and> (CL = [] \<or> last CL = Oc)" by blast
            (* compute the next state *)
        with cf_at_stp and \<open>s=12\<close> and SUC_STEP_RED
        have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp) =
                step0 (12, [] , Bk # Bk # rev CL @ Oc # Bk \<up> Suc rex) tm_erase_right_then_dblBk_left"
          by auto

        also
        have "... = (0, [], Bk# Bk # rev CL @ Oc # Bk \<up> Suc rex)"
          by (auto simp add: tm_erase_right_then_dblBk_left_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [Bk, Oc] @ CL, CR) tm_erase_right_then_dblBk_left (Suc stp)
                    = (0, [], Bk# Bk # rev CL @ Oc # Bk \<up> Suc rex)"
          by auto
            (* establish measure *)
        with cf_at_current  show ?thesis
          by (auto simp add: measure_tm_erase_right_then_dblBk_left_erp_def)
      qed
    qed
  qed
qed


(* -------------- Total correctness for the ERASE path of tm_erase_right_then_dblBk_left ------------------ *)

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_CL_is_Nil:
  assumes "noDblBk CL"
  and "noDblBk CR"
  and "CL = []"
  shows "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
proof (rule tm_erase_right_then_dblBk_left_erp_partial_correctness_CL_is_Nil)
  from assms show "\<exists>stp. is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
    using  tm_erase_right_then_dblBk_left_erp_halts by auto
next
  from assms show "noDblBk CL" by auto
next
  from assms show "noDblBk CR" by auto
next
  from assms show "CL = []" by auto
qed

lemma tm_erase_right_then_dblBk_left_correctness_CL_ew_Bk:
  assumes "noDblBk CL"
  and "noDblBk CR"
  and "CL \<noteq> []"
  and "last CL = Bk"   
  shows "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
proof (rule tm_erase_right_then_dblBk_left_erp_partial_correctness_CL_ew_Bk)
  from assms show "\<exists>stp. is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
    using  tm_erase_right_then_dblBk_left_erp_halts by auto
next
  from assms show "noDblBk CL" by auto
next
  from assms show "noDblBk CR" by auto
next
  from assms show "CL \<noteq> []" by auto
next
  from assms show "last CL = Bk" by auto
qed

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_CL_ew_Oc:
  assumes "noDblBk CL"
    and "noDblBk CR"
    and "CL \<noteq> []"
    and "last CL = Oc"   
  shows "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
proof (rule tm_erase_right_then_dblBk_left_erp_partial_correctness_CL_ew_Oc)
  from assms show "\<exists>stp. is_final (steps0 (1, [Bk,Oc] @ CL, CR) tm_erase_right_then_dblBk_left stp)"
    using  tm_erase_right_then_dblBk_left_erp_halts by auto
next
  from assms show "noDblBk CL" by auto
next
  from assms show "noDblBk CR" by auto
next
  from assms show "CL \<noteq> []" by auto
next
  from assms show "last CL = Oc" by auto
qed

(* --- prove some helper theorems to convert results to lists of numeral        --- *)

(*--------------------------------------------------------------------------------- *)
(* simple case, where we tried to check for exactly one argument and failed         *)
(*--------------------------------------------------------------------------------- *)

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_eq_Nil_n_eq_1_last_eq_0:
  assumes "(nl::nat list) \<noteq> []"
    and "n=1"
    and "n \<le> length nl"
    and "last (take n nl) = 0"
  shows "\<exists>CL CR.
           [Oc] @ CL = rev(<take n nl>) \<and> noDblBk CL \<and> CL = [] \<and>
                  CR = (<drop n nl>)    \<and> noDblBk CR"
proof -
  have "rev(<take n nl>) = <rev(take n nl)>"
    by (rule rev_numeral_list)
  also with assms have "... = <rev( butlast (take n nl) @ [last (take n nl)] )>"
    by (metis append_butlast_last_id take_eq_Nil zero_neq_one)
  also have "... = < (rev[(last (take n nl))]) @ (rev ( butlast (take n nl)))>"
    by simp
  also with assms have "... = < (rev [0]) @ (rev ( butlast (take n nl)))>" by auto
  finally have major: "rev(<take n nl>) = <(rev [0]) @ (rev ( butlast (take n nl)))>" by auto
  with assms have "butlast (take n nl) = []"
    by (simp add: butlast_take)
  then have "<(rev [0::nat]) @ (rev ( butlast (take n nl)))> = <(rev [0::nat]) @ (rev [])>"
    by auto
  also have "... = <(rev [0::nat])>" by auto
  also have "... = <[0::nat]>" by auto
  also have "... = [Oc]"
    by (simp add: tape_of_list_def tape_of_nat_def )
  finally have "<(rev [0::nat]) @ (rev ( butlast (take n nl)))> =  [Oc]" by auto
  with major have "rev(<take n nl>) = [Oc]" by auto
  then have "[Oc] @ [] = rev(<take n nl>) \<and> noDblBk [] \<and> ([] = [] \<or> [] \<noteq> [] \<and> last [] = Oc) \<and>
                  (<drop n nl>) = (<drop n nl>)    \<and> noDblBk (<drop n nl>)"
    by (simp add: noDblBk_Nil noDblBk_tape_of_nat_list)
  then show ?thesis
    by blast
qed

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_n_eq_1_last_neq_0:
  assumes "(nl::nat list) \<noteq> []"
    and "n=1"
    and "n \<le> length nl"
    and "0 < last (take n nl)"
  shows "\<exists>CL CR.
           [Oc] @ CL = rev(<take n nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<drop n nl>)    \<and> noDblBk CR"
proof -
  have minor: "rev(<take n nl>) = <rev(take n nl)>"
    by (rule rev_numeral_list)
  also with assms have "... = <rev( butlast (take n nl) @ [last (take n nl)] )>"
    by simp
  also have "... = <(rev[last (take n nl)]) @ (rev (butlast (take n nl)))>"
    by simp
  finally have major: "rev(<take n nl>) = <(rev[(last (take n nl))]) @ (rev ( butlast (take n nl)))>"
    by auto

  moreover from assms have "[last (take n nl)] \<noteq> []" by auto
  moreover from  assms have "butlast (take n nl) = []"
    by (simp add: butlast_take)
  ultimately have "rev(<take n nl>) = <(rev[(last (take n nl))])>"
    by auto

  also have "<(rev[(last (take n nl))])> = Oc\<up> Suc  (last (take n nl))"
  proof -
    from assms have "<[(last (take n nl))]> = Oc\<up> Suc  (last (take n nl))"
      by (simp add: tape_of_list_def tape_of_nat_def)
    then show "<(rev[(last (take n nl))])> = Oc\<up> Suc  (last (take n nl))"
      by simp
  qed
  also have "... = Oc# Oc\<up> (last (take n nl))" by auto
  finally have "rev(<take n nl>) = Oc# Oc\<up> (last (take n nl))" by auto

  moreover from assms have "Oc\<up> (last (take n nl)) \<noteq> []"
    by auto

  ultimately have "[Oc] @ (Oc\<up> (last (take n nl))) = rev(<take n nl>) \<and>
                   noDblBk (Oc\<up> (last (take n nl))) \<and> (Oc\<up> (last (take n nl))) \<noteq> [] \<and> last (Oc\<up> (last (take n nl))) = Oc \<and>
                  (<drop n nl>) = (<drop n nl>)    \<and> noDblBk (<drop n nl>)" using assms
    by (simp add: noDblBk_Bk_Oc_rep noDblBk_tape_of_nat_list)
  then show ?thesis by auto
qed

(* convenient versions using hd and tl for tm_skip_first_arg *)

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_eq_Nil_last_eq_0':
  assumes "1 \<le> length (nl:: nat list)"
    and "hd nl = 0"
  shows "\<exists>CL CR.
           [Oc] @ CL = rev(<hd nl>)  \<and> noDblBk CL \<and> CL = [] \<and>
                  CR = (<tl nl>) \<and> noDblBk CR"
proof -
  from assms
  have  "(nl::nat list) \<noteq> [] \<and> (1::nat)=1 \<and> 1 \<le> length nl \<and> 0 = last (take 1 nl)"
    by (metis One_nat_def append.simps(1) append_butlast_last_id butlast_take diff_Suc_1 
        hd_take   le_numeral_extra(4) length_0_conv less_numeral_extra(1) list.sel(1)
        not_one_le_zero take_eq_Nil zero_less_one)
  then have  "\<exists>n. (nl::nat list) \<noteq> [] \<and> n=1 \<and> n \<le> length nl \<and> 0 = last (take n nl)"
    by blast
  then obtain n where
    w_n: "(nl::nat list) \<noteq> [] \<and> n=1 \<and> n \<le> length nl \<and> 0 = last (take n nl)" by blast
  then have "\<exists>CL CR.
           [Oc] @ CL = rev(<take n nl>) \<and> noDblBk CL \<and> CL = [] \<and>
                  CR = (<drop n nl>)    \<and> noDblBk CR"
    using tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_eq_Nil_n_eq_1_last_eq_0
    by auto
  then obtain CL CR where
    w_CL_CR: "[Oc] @ CL = rev (<take n nl>) \<and> noDblBk CL \<and> CL = [] \<and> CR = <drop n nl> \<and> noDblBk CR" by blast
  with assms w_n show ?thesis
    by (simp add:  noDblBk_Nil noDblBk_tape_of_nat_list   rev_numeral tape_of_nat_def)
qed

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_last_neq_0':
  assumes "1 \<le> length (nl::nat list)"
    and "0 < hd nl"
  shows "\<exists>CL CR.
           [Oc] @ CL = rev(<hd nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<tl nl>)    \<and> noDblBk CR"
proof -
  from assms
  have  "(nl::nat list) \<noteq> [] \<and> (1::nat)=1 \<and> 1 \<le> length nl \<and> 0 < last (take 1 nl)"
    by (metis append.simps(1) append_butlast_last_id butlast_take cancel_comm_monoid_add_class.diff_cancel
        ex_least_nat_le hd_take le_trans list.sel(1) list.size(3)
        neq0_conv not_less not_less_zero take_eq_Nil zero_less_one zero_neq_one)
  then have  "\<exists>n. (nl::nat list) \<noteq> [] \<and> n=1 \<and> n \<le> length nl \<and> 0 < last (take n nl)"
    by blast
  then obtain n where
    w_n: "(nl::nat list) \<noteq> [] \<and> n=1 \<and> n \<le> length nl \<and> 0 < last (take n nl)" by blast
  then have "\<exists>CL CR.
           [Oc] @ CL = rev(<take n nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<drop n nl>)    \<and> noDblBk CR"
    using tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_n_eq_1_last_neq_0
    by auto
  with assms w_n show ?thesis 
    by (simp add: drop_Suc take_Suc tape_of_list_def )
qed

(*--------------------------------------------------------------------------------- *)
(* generic case , where we tried to check for more than one one argument and failed *)
(*--------------------------------------------------------------------------------- *)

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_n_gt_1_last_eq_0:
  assumes "(nl::nat list) \<noteq> []"
    and "1<n"
    and "n \<le> length nl"
    and "last (take n nl) = 0"
  shows "\<exists>CL CR.
           [Oc] @ CL = rev(<take n nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<drop n nl>) \<and> noDblBk CR"
proof -
  have minor: "rev(<take n nl>) = <rev(take n nl)>"
    by (rule rev_numeral_list)
  also with assms have "... = <rev( butlast (take n nl) @ [last (take n nl)] )>"   
    by (metis append_butlast_last_id not_one_less_zero take_eq_Nil)
  also have "... = < (rev [(last (take n nl))]) @ (rev ( butlast (take n nl)))>"
    by simp
  also with assms have "... = <(rev [0]) @ (rev ( butlast (take n nl)))>" by auto
  finally have major: "rev(<take n nl>) = <(rev [0]) @ (rev ( butlast (take n nl)))>" by auto

  moreover have "<(rev [0::nat])> = [Oc]"
    by (simp add: tape_of_list_def tape_of_nat_def )
  moreover with assms have not_Nil: "rev (butlast (take n nl)) \<noteq> []"
    by (simp add: butlast_take)
  ultimately have "rev(<take n nl>) = [Oc] @ [Bk] @ <rev (butlast (take n nl))>"
    using  tape_of_nat_def tape_of_nat_list_cons_eq by auto

  then show ?thesis
    using major and minor and not_Nil
    by (metis append_Nil append_is_Nil_conv append_is_Nil_conv  last_append last_appendR  list.sel(3)
        noDblBk_tape_of_nat_list noDblBk_tape_of_nat_list_imp_noDblBk_tl 
        numeral_list_last_is_Oc rev.simps(1) rev_append snoc_eq_iff_butlast tl_append2)
qed

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_n_gt_1_last_neq_0:
  assumes "(nl::nat list) \<noteq> []"
    and "1 < n"
    and "n \<le> length nl"
    and "0 < last (take n nl)"
  shows "\<exists>CL CR.
           [Oc] @ CL = rev(<take n nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<drop n nl>)    \<and> noDblBk CR"
proof -
  have minor: "rev(<take n nl>) = <rev(take n nl)>"
    by (rule rev_numeral_list)
  also with assms have "... = <rev( butlast (take n nl) @ [last (take n nl)] )>"   
    by (metis append_butlast_last_id not_one_less_zero take_eq_Nil)
  also have "... = <(rev [(last (take n nl))]) @ (rev ( butlast (take n nl)))>"
    by simp
  finally have major: "rev(<take n nl>) = <(rev[(last (take n nl))]) @ (rev ( butlast (take n nl)))>"
    by auto

  moreover from assms have "[last (take n nl)] \<noteq> []" by auto
  moreover from  assms have "butlast (take n nl) \<noteq> []"
    by (simp add: butlast_take)
  ultimately have "rev(<take n nl>) = <(rev[(last (take n nl))])> @[Bk] @ <(rev ( butlast (take n nl)))>"
    by (metis append_numeral_list rev.simps(1) rev_rev_ident rev_singleton_conv)

  also have "<(rev[(last (take n nl))])> = Oc\<up> Suc  (last (take n nl))"
  proof -
    from assms have "<[(last (take n nl))]> = Oc\<up> Suc  (last (take n nl))"
      by (simp add: tape_of_list_def tape_of_nat_def)
    then show "<(rev[(last (take n nl))])> = Oc\<up> Suc  (last (take n nl))"
      by simp
  qed
  also have "... = Oc# Oc\<up> (last (take n nl))" by auto
  finally have "rev(<take n nl>) = Oc# Oc\<up> (last (take n nl))  @[Bk] @ <(rev ( butlast (take n nl)))>"
    by auto

  moreover from assms have "Oc\<up> (last (take n nl)) \<noteq> []"
    by auto

  ultimately have "[Oc] @ (Oc\<up> (last (take n nl))  @[Bk] @ <(rev ( butlast (take n nl)))>)
                    = rev(<take n nl>) \<and> noDblBk (Oc\<up> (last (take n nl))  @[Bk] @ <(rev ( butlast (take n nl)))>) \<and>
                    (Oc\<up> (last (take n nl))  @[Bk] @ <(rev ( butlast (take n nl)))>) \<noteq> [] \<and>
                     last (Oc\<up> (last (take n nl))  @[Bk] @ <(rev ( butlast (take n nl)))>) = Oc \<and>
                  (<drop n nl>) = (<drop n nl>)    \<and> noDblBk (<drop n nl>)"

    using assms 
      \<open><rev [last (take n nl)]> = Oc \<up> Suc (last (take n nl))\<close>
      \<open>Oc \<up> Suc (last (take n nl)) = Oc # Oc \<up> last (take n nl)\<close>
      \<open>butlast (take n nl) \<noteq> []\<close> \<open>rev (<take n nl>) = <rev [last (take n nl)]> @ [Bk] @ <rev (butlast (take n nl))>\<close>
    by (smt
        append_Cons append_Nil append_Nil2 append_eq_Cons_conv butlast.simps(1) butlast.simps(2)
        butlast_append last_ConsL last_append last_appendR  list.sel(3) list.simps(3) minor noDblBk_tape_of_nat_list
        noDblBk_tape_of_nat_list_imp_noDblBk_tl numeral_list_last_is_Oc rev_is_Nil_conv self_append_conv)
  then show ?thesis by auto
qed

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_n_gt_1:
  assumes "(nl::nat list) \<noteq> []"
    and "1<n"
    and "n \<le> length nl"
  shows "\<exists>CL CR.
           [Oc] @ CL = rev(<take n nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<drop n nl>) \<and> noDblBk CR"
proof (cases  "last (take n nl)")
  case 0
  with assms show ?thesis
    using tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_n_gt_1_last_eq_0
    by auto
next
  case (Suc nat)
  with assms show ?thesis
    using tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_n_gt_1_last_neq_0
    by auto
qed

(*--------------------------------------------------------------------------------- *)
(* For now, we only proof a result for n = 1 supporting tm_check_for_one_arg        *)
(*--------------------------------------------------------------------------------- *)

(*----------------------------------------------------------------------------------------------------- *)
(* ENHANCE: formalise generic tm_skip_n_args                                                            *)
(* ENHANCE: formalise matching results for tm_erase_right_then_dblBk_left_erp_total_correctness_one_arg *)
(*----------------------------------------------------------------------------------------------------- *)

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_one_arg:
  assumes "1 \<le> length (nl::nat list)"
  shows "\<lbrace> \<lambda>tap. tap = (Bk# rev(<hd nl>), <tl nl>) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (<hd nl>) @ [Bk] @ Bk \<up> rex ) \<rbrace>"
proof (cases "hd nl")
  case 0
  then have "hd nl = 0" .
  with assms
  have "\<exists>CL CR.
           [Oc] @ CL = rev(<hd nl>)  \<and> noDblBk CL \<and> CL = [] \<and>
                  CR = (<tl nl>) \<and> noDblBk CR"
    using tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_eq_Nil_last_eq_0'
    by blast
  then obtain CL CR where
    w_CL_CR: "[Oc] @ CL = rev(<hd nl>)  \<and> noDblBk CL \<and> CL = [] \<and>
                  CR = (<tl nl>) \<and> noDblBk CR" by blast

  show ?thesis
  proof (rule Hoare_consequence)
    (*  1. \<lambda>tap. tap = (Bk # rev (<hd nl>), <tl nl>) \<mapsto> ?P *)
    from assms and w_CL_CR  show "(\<lambda>tap. tap = (Bk # rev (<hd nl>), <tl nl>)) \<mapsto> (\<lambda>tap. tap = ([Bk,Oc] @ CL, CR))"
      using Cons_eq_appendI append_self_conv assert_imp_def by auto
  next
    (*  1. \<lbrace>\<lambda>tap. tap = ([Bk, Oc] @ CL, CR)\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>?Q\<rbrace> *)
    from assms and w_CL_CR
      show "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
      using tm_erase_right_then_dblBk_left_erp_total_correctness_CL_is_Nil
      by blast
  next
    (*  1. \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex) \<mapsto> \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ <hd nl> @ [Bk] @ Bk \<up> rex) *)
    show "(\<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex)) \<mapsto> (\<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ <hd nl> @ [Bk] @ Bk \<up> rex))"  
      using Cons_eq_append_conv   assert_imp_def rev_numeral  w_CL_CR by fastforce
  qed

next
  case (Suc nat)
  then have "0 < hd nl" by auto
  with assms
  have "\<exists>CL CR.
           [Oc] @ CL = rev(<hd nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<tl nl>)    \<and> noDblBk CR"
    using tm_erase_right_then_dblBk_left_erp_total_correctness_helper_CL_neq_Nil_last_neq_0'
    by auto
  then obtain CL CR where
    w_CL_CR: "[Oc] @ CL = rev(<hd nl>) \<and> noDblBk CL \<and> CL \<noteq> [] \<and> last CL = Oc \<and>
                  CR = (<tl nl>)    \<and> noDblBk CR" by blast
  show ?thesis
  proof (rule Hoare_consequence)
    (* 1. \<lambda>tap. tap = (Bk # rev (<hd nl>), <tl nl>) \<mapsto> ?P *)
    from assms and w_CL_CR show "(\<lambda>tap. tap = (Bk # rev (<hd nl>), <tl nl>)) \<mapsto> (\<lambda>tap. tap = ([Bk,Oc] @ CL, CR))"
      by (simp add: w_CL_CR assert_imp_def)
  next
    (* \<lbrace>\<lambda>tap. tap = ([Bk, Oc] @ CL, CR)\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>?Q\<rbrace> *)
    from assms and w_CL_CR
    show "\<lbrace> \<lambda>tap. tap = ([Bk,Oc] @ CL, CR) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ (rev CL) @ [Oc, Bk] @ Bk \<up> rex ) \<rbrace>"
      using tm_erase_right_then_dblBk_left_erp_total_correctness_CL_ew_Oc
      by blast
  next
    (* \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex) \<mapsto> \<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ <hd nl> @ [Bk] @ Bk \<up> rex) *)
    show "(\<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ rev CL @ [Oc, Bk] @ Bk \<up> rex)) \<mapsto> (\<lambda>tap. \<exists>rex. tap = ([], [Bk, Bk] @ <hd nl> @ [Bk] @ Bk \<up> rex))"
      using Cons_eq_append_conv   assert_imp_def rev_numeral  w_CL_CR  
      by (simp add: assert_imp_def rev_numeral replicate_app_Cons_same  tape_of_nat_def)
  qed
qed


(* ----------------------- tm_check_for_one_arg ----------------------- 
 * Prove total correctness for COMPOSED machine tm_check_for_one_arg
 * This is done via the rules for the composition operator seq_tm
 * -------------------------------------------------------------------- *)

(* we have

DO_NOTHING path

corollary tm_skip_first_arg_correct_Nil':
  "length nl = 0
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_skip_first_arg \<lbrace>\<lambda>tap.       tap = ( []           , [Bk] ) \<rbrace>"

lemma tm_skip_first_arg_len_eq_1_total_correctness':
  "length nl = 1
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = ([Bk],  <[hd nl]> @[Bk])\<rbrace>"

lemma tm_erase_right_then_dblBk_left_dnp_total_correctness:
 "\<lbrace> \<lambda>tap. tap = ([], r ) \<rbrace> 
    tm_erase_right_then_dblBk_left
  \<lbrace> \<lambda>tap. tap = ([Bk,Bk], r ) \<rbrace>"

---

ERASE path

lemma tm_skip_first_arg_len_gt_1_total_correctness:
  assumes "1 < length (nl::nat list)"
  shows "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = (Bk# <rev [hd nl]>, <tl nl>) \<rbrace>"

lemma tm_erase_right_then_dblBk_left_erp_total_correctness_one_arg:
  assumes "1 \<le> length (nl::nat list)"
  shows "\<lbrace> \<lambda>tap. tap = (Bk# rev(<hd nl>), <tl nl>) \<rbrace> 
           tm_erase_right_then_dblBk_left
         \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (<hd nl>) @ [Bk] @ Bk \<up> rex ) \<rbrace>"

*)

(*
let tm_check_for_one_arg = foldl1' seqcomp_tm [ tm_skip_first_arg, tm_erase_right_then_dblBk_left ]
*)

definition 
  tm_check_for_one_arg :: "instr list"
  where
    "tm_check_for_one_arg \<equiv> tm_skip_first_arg |+| tm_erase_right_then_dblBk_left"


lemma tm_check_for_one_arg_total_correctness_Nil:
  "length nl = 0
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_check_for_one_arg \<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk] ) \<rbrace>"
proof -
  assume major: "length nl = 0"
  have "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> (tm_skip_first_arg |+| tm_erase_right_then_dblBk_left) \<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk] ) \<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 tm_skip_first_arg"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_skip_first_arg_def tm_erase_right_then_dblBk_left_def)
  next
    from major show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_skip_first_arg \<lbrace>\<lambda>tap. tap = ( [] , [Bk] ) \<rbrace>"
      using tm_skip_first_arg_correct_Nil'
      by simp
  next
    from major show "\<lbrace>\<lambda>tap. tap = ([], [Bk])\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>\<lambda>tap. tap = ([Bk, Bk], [Bk])\<rbrace>"
      using tm_erase_right_then_dblBk_left_dnp_total_correctness
      by simp
  qed
  then show ?thesis
    unfolding tm_check_for_one_arg_def
    by auto
qed

lemma tm_check_for_one_arg_total_correctness_len_eq_1:
  "length nl = 1
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_check_for_one_arg \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl> @ [Bk])\<rbrace>"
proof -
  assume major: "length nl = 1"
  have " \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
          (tm_skip_first_arg |+| tm_erase_right_then_dblBk_left)
         \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl> @ [Bk])\<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 tm_skip_first_arg"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_skip_first_arg_def tm_erase_right_then_dblBk_left_def)
  next
    from major have "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = ([Bk],  <[hd nl]> @[Bk])\<rbrace>"
      using tm_skip_first_arg_len_eq_1_total_correctness'
      by simp
    moreover from major have  "(nl::nat list) = [hd nl]"
      by (metis diff_self_eq_0 length_0_conv length_tl list.exhaust_sel zero_neq_one)
    ultimately
    show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = ([Bk],  <nl> @[Bk])\<rbrace>" using major
      by auto
  next
    from major
    have "\<lbrace>\<lambda>tap. tap = ([], <nl> @ [Bk])\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>\<lambda>tap. tap = ([Bk, Bk], <nl> @ [Bk])\<rbrace>"
      using tm_erase_right_then_dblBk_left_dnp_total_correctness
      by simp
        (* Add a blank on the initial left tape *)
    with major have "\<exists>stp. is_final (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
                           (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, [Bk, Bk], <nl> @ [Bk]))"
      unfolding Hoare_halt_def
      by (smt Hoare_halt_def Pair_inject  holds_for.elims(2) is_final.elims(2))
    then obtain stp where
      w_stp: "is_final (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
               (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, [Bk, Bk], <nl> @ [Bk]))" by blast

    then have "is_final (steps0 (1, Bk \<up> 0,<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
               (steps0 (1, Bk \<up> 0,<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, Bk \<up> 2, <nl> @ [Bk]))"
      by (simp add: is_finalI numeral_eqs_upto_12(1))
    then have "\<exists>z3. z3 \<le> 0 + 1 \<and>
                is_final (steps0 (1, Bk \<up> (0+1),<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
                 (steps0 (1, Bk \<up> (0+1),<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, Bk \<up> (2+z3), <nl> @ [Bk]))"
      by (metis is_finalI  steps_left_tape_EnlargeBkCtx)
    then have "is_final (steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
                   (\<exists>z4. steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, Bk \<up> z4, <nl> @ [Bk]))"
      by (metis One_nat_def add.left_neutral replicate_0 replicate_Suc)
    then have "\<exists>n. is_final (steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left n) \<and>
                   (\<exists>z4. steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left n = (0, Bk \<up> z4, <nl> @ [Bk]))"
      by blast
    then show "\<lbrace>\<lambda>tap. tap = ([Bk], <nl::nat list> @ [Bk])\<rbrace>
                 tm_erase_right_then_dblBk_left
               \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl::nat list> @ [Bk])\<rbrace>"
      using Hoare_halt_def Hoare_unhalt_def holds_for.simps by auto
  qed
  then show ?thesis
    unfolding tm_check_for_one_arg_def
    by auto
qed

(* Old version of tm_check_for_one_arg_total_correctness_len_eq_1:
 * Keep this proof as an example
 * The proof shows how to add blanks on the initial left tape, if you need some for composition with some predecessor tm
 *)

(*
lemma tm_check_for_one_arg_total_correctness_len_eq_1:
  "length nl = 1
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_check_for_one_arg \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl> @ [Bk])\<rbrace>"
proof -
  assume major: "length nl = 1"
  have " \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
          (tm_skip_first_arg |+| tm_erase_right_then_dblBk_left)
         \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl> @ [Bk])\<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 tm_skip_first_arg"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_skip_first_arg_def tm_erase_right_then_dblBk_left_def)
  next
    from major have "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = ([Bk],  <[hd nl]> @[Bk])\<rbrace>"
      using tm_skip_first_arg_len_eq_1_total_correctness'
      by simp
    moreover from major have  "(nl::nat list) = [hd nl]"
      by (metis diff_self_eq_0 length_0_conv length_tl list.exhaust_sel zero_neq_one)
    ultimately
    show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = ([Bk],  <nl> @[Bk])\<rbrace>" using major
      by auto
  next
    from major
    have "\<lbrace>\<lambda>tap. tap = ([], <nl> @ [Bk])\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>\<lambda>tap. tap = ([Bk, Bk], <nl> @ [Bk])\<rbrace>"
      using tm_erase_right_then_dblBk_left_dnp_total_correctness
      by simp
        (* Add a blank on the initial left tape *)
        (* Note: since we proved 

              \<lbrace>\<lambda>tap. tap = ([], <nl> @ [Bk])\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>\<lambda>tap. tap = ([Bk, Bk], <nl> @ [Bk])\<rbrace>

           we need to add a blank on the left tape.
           This is no problem, since blanks on the left tape do not matter.
           However, adding blanks also changes the resulting left tape.
           Instead of      \<lbrace>\<lambda>tap. tap = ([Bk, Bk], <nl> @ [Bk])\<rbrace>
           we end up with  \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl> @ [Bk])\<rbrace>

           If we had proved  
              \<lbrace>\<lambda>tap. tap = ([Bk], <nl> @ [Bk])\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>\<lambda>tap. tap = ([Bk, Bk], <nl> @ [Bk])\<rbrace>

           in the first place, there would be no need for this weakened result.

           But since trailing blanks on the final left tape do not matter either, this is no real problem.
        *)
    with major have "\<exists>stp. is_final (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
                           (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, [Bk, Bk], <nl> @ [Bk]))"
      unfolding Hoare_halt_def
      by (smt Hoare_halt_def Pair_inject  holds_for.elims(2) is_final.elims(2))
    then obtain stp where
      w_stp: "is_final (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
               (steps0 (1, [],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, [Bk, Bk], <nl> @ [Bk]))" by blast

    then have "is_final (steps0 (1, Bk \<up> 0,<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
               (steps0 (1, Bk \<up> 0,<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, Bk \<up> 2, <nl> @ [Bk]))"
      by (simp add: is_finalI numeral_eqs_upto_12(1))
    then have "\<exists>z3. z3 \<le> 0 + 1 \<and>
                is_final (steps0 (1, Bk \<up> (0+1),<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
                 (steps0 (1, Bk \<up> (0+1),<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, Bk \<up> (2+z3), <nl> @ [Bk]))"
      by (metis is_finalI  steps_left_tape_EnlargeBkCtx)
    then have "is_final (steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp) \<and>
                   (\<exists>z4. steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left stp = (0, Bk \<up> z4, <nl> @ [Bk]))"
      by (metis One_nat_def add.left_neutral replicate_0 replicate_Suc)
    then have "\<exists>n. is_final (steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left n) \<and>
                   (\<exists>z4. steps0 (1, [Bk],<nl::nat list>@ [Bk]) tm_erase_right_then_dblBk_left n = (0, Bk \<up> z4, <nl> @ [Bk]))"
      by blast
    then show "\<lbrace>\<lambda>tap. tap = ([Bk], <nl::nat list> @ [Bk])\<rbrace>
                 tm_erase_right_then_dblBk_left
               \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl::nat list> @ [Bk])\<rbrace>"
      using Hoare_halt_def Hoare_unhalt_def holds_for.simps by auto
  qed
  then show ?thesis
    unfolding tm_check_for_one_arg_def
    by auto
qed

*)
lemma tm_check_for_one_arg_total_correctness_len_gt_1:
  "length nl > 1
   \<Longrightarrow>  \<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace> tm_check_for_one_arg \<lbrace> \<lambda>tap. \<exists> l. tap = ( [],  [Bk,Bk] @ <[hd nl]> @ Bk \<up> l) \<rbrace>"
proof -
  assume major: "length nl > 1"
  have " \<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace>
          (tm_skip_first_arg |+| tm_erase_right_then_dblBk_left)
         \<lbrace> \<lambda>tap. \<exists> l. tap = ( [],  [Bk,Bk] @ <[hd nl]> @ Bk \<up> l) \<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 tm_skip_first_arg"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_skip_first_arg_def tm_erase_right_then_dblBk_left_def)
  next
    from major show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list> )\<rbrace> tm_skip_first_arg \<lbrace> \<lambda>tap. tap = (Bk# <rev [hd nl]>, <tl nl>) \<rbrace>"
      using tm_skip_first_arg_len_gt_1_total_correctness
      by simp
  next
    from major
    have "\<lbrace> \<lambda>tap. tap = (Bk# rev(<hd nl>), <tl nl>) \<rbrace> tm_erase_right_then_dblBk_left \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ (<hd nl>) @ [Bk] @ Bk \<up> rex ) \<rbrace>"
      using tm_erase_right_then_dblBk_left_erp_total_correctness_one_arg
      by simp
    then have "\<lbrace> \<lambda>tap. tap = (Bk# <rev [hd nl]>, <tl nl>) \<rbrace> tm_erase_right_then_dblBk_left \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ <[hd nl]> @ [Bk] @ Bk \<up> rex ) \<rbrace>"
      by (simp add:  rev_numeral rev_numeral_list tape_of_list_def )
    then have "\<lbrace> \<lambda>tap. tap = (Bk# <rev [hd nl]>, <tl nl>) \<rbrace> tm_erase_right_then_dblBk_left \<lbrace> \<lambda>tap. \<exists>rex. tap = ([], [Bk,Bk] @ <[hd nl]> @ Bk \<up> (Suc rex) ) \<rbrace>"
      by force
    then show "\<lbrace>\<lambda>tap. tap = (Bk # <rev [hd nl]>, <tl nl>)\<rbrace> tm_erase_right_then_dblBk_left \<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Bk, Bk] @ <[hd nl]> @ Bk \<up> l)\<rbrace>"
      by (smt Hoare_haltI Hoare_halt_def holds_for.elims(2) holds_for.simps)
  qed
  then show ?thesis
    unfolding tm_check_for_one_arg_def
    by auto
qed

(* ---------- tm_strong_copy ---------- *)

definition
  tm_strong_copy :: "instr list"
  where
    "tm_strong_copy \<equiv> tm_check_for_one_arg |+| tm_weak_copy"

(* Prove total correctness for COMPOSED machine tm_strong_copy.
 * This is done via the rules for the composition operator seq_tm.
 *)

lemma tm_strong_copy_total_correctness_Nil:
  "length nl = 0
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_strong_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk,Bk,Bk],[]) \<rbrace>"
proof -
  assume major: "length nl = 0"
  have " \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
          tm_check_for_one_arg |+| tm_weak_copy
         \<lbrace>\<lambda>tap. tap = ([Bk,Bk,Bk,Bk],[]) \<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 tm_check_for_one_arg"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_weak_copy_def
          tm_check_for_one_arg_def
          tm_skip_first_arg_def
          tm_erase_right_then_dblBk_left_def)
  next
    from major show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_check_for_one_arg \<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk] ) \<rbrace>"
      using tm_check_for_one_arg_total_correctness_Nil
      by simp
  next
    from major show "\<lbrace>\<lambda>tap. tap = ([Bk, Bk], [Bk])\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk, Bk, Bk, Bk], [])\<rbrace>"
      using tm_weak_copy_correct11'
      by simp
  qed
  then show ?thesis
    unfolding tm_strong_copy_def
    by auto
qed

lemma tm_strong_copy_total_correctness_len_gt_1:
  "1 < length nl
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_strong_copy \<lbrace> \<lambda>tap. \<exists>l. tap = ([Bk,Bk], <[hd nl]> @ Bk \<up> l) \<rbrace>"
proof -
  assume major: "1 < length nl"
  have " \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
          tm_check_for_one_arg |+| tm_weak_copy
         \<lbrace> \<lambda>tap. \<exists> l. tap = ([Bk,Bk], <[hd nl]> @ Bk \<up> l) \<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 tm_check_for_one_arg"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_weak_copy_def
          tm_check_for_one_arg_def
          tm_skip_first_arg_def
          tm_erase_right_then_dblBk_left_def)
  next
    from major show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_check_for_one_arg \<lbrace> \<lambda>tap. \<exists> l. tap = ( [],  [Bk,Bk] @ <[hd nl]> @ Bk \<up> l) \<rbrace>"
      using tm_check_for_one_arg_total_correctness_len_gt_1
      by simp
  next
    show "\<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Bk, Bk] @ <[hd nl]> @ Bk \<up> l)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>l. tap = ([Bk, Bk], <[hd nl]> @ Bk \<up> l)\<rbrace>"
    proof -
      have "\<And>r.\<lbrace>\<lambda>tap. tap = ([], [Bk,Bk]@r) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk], r) \<rbrace>"
        using tm_weak_copy_correct13' by simp
      then have "\<And>r. \<exists>stp. is_final (steps0 (1, [],[Bk,Bk]@r) tm_weak_copy stp) \<and>
                           (steps0 (1, [],[Bk,Bk]@r) tm_weak_copy stp = (0, [Bk, Bk], r))"
        unfolding Hoare_halt_def
        by (smt Hoare_halt_def Pair_inject  holds_for.elims(2) is_final.elims(2))
      then have "\<And>l. \<exists>stp. is_final (steps0 (1, [],[Bk,Bk]@<[hd nl]> @ Bk \<up> l) tm_weak_copy stp) \<and>
                           (steps0 (1, [],[Bk,Bk]@<[hd nl]> @ Bk \<up> l) tm_weak_copy stp = (0, [Bk, Bk], <[hd nl]> @ Bk \<up> l))"
        by blast
      then show ?thesis
        using Hoare_halt_def holds_for.simps by fastforce
    qed
  qed
  then show ?thesis
    unfolding tm_strong_copy_def
    by auto
qed

lemma tm_strong_copy_total_correctness_len_eq_1:
  "1 = length nl
   \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_strong_copy \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd nl, hd nl]> @ Bk \<up> l) \<rbrace>"
proof -
  assume major: "1 = length nl"
  have " \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
           tm_check_for_one_arg |+| tm_weak_copy
         \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd nl, hd nl]> @ Bk \<up> l) \<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 tm_check_for_one_arg"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_weak_copy_def
          tm_check_for_one_arg_def
          tm_skip_first_arg_def
          tm_erase_right_then_dblBk_left_def)
  next
    from major show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_check_for_one_arg \<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl> @ [Bk])\<rbrace>"
      using tm_check_for_one_arg_total_correctness_len_eq_1
      by simp
  next
    have "\<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <[hd nl]> @[Bk])\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd nl, hd nl]> @ Bk \<up> l) \<rbrace>"
      using tm_weak_copy_correct6
      by simp
    moreover from major have "<nl> = <[hd nl]>" 
      by (metis diff_self_eq_0 length_0_conv length_tl list.exhaust_sel zero_neq_one)
    ultimately show "\<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <nl> @ [Bk])\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd nl, hd nl]> @ Bk \<up> l)\<rbrace>"
      by auto
  qed
  then show ?thesis
    unfolding tm_strong_copy_def
    by auto
qed

end
