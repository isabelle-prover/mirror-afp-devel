(* Title: thys/SimpleGoedelEncoding.thy
   Author: Franz Regensburger (FABR) 02/2022

   - For the proof of the undecidability of the special halting problems K1 and K0
     we need some arbitrary injective encoding from Turing machines into the
     natural numbers.
 *)

section \<open>Halting Problems: do Turing Machines for deciding Termination exist?\<close>

text \<open>In this section we will show that there cannot exist Turing Machines that are able
to decide the termination of some other arbitrary Turing Machine.\<close>

subsection \<open>A simple Gödel Encoding for Turing machines\<close>

theory SimpleGoedelEncoding
  imports
     Turing_HaltingConditions
    "HOL-Library.Nat_Bijection"
begin

(* -------------------------------------------------------------------------- *)

declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]

subsubsection \<open>Some general results on injective functions and their inversion\<close>

lemma dec_is_inv_on_A:
   "dec = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w) then (THE t. t\<in>A \<and> enc t = w) else (SOME t. t \<in> A)))
    \<Longrightarrow> dec = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w) then (the_inv_into A enc) w else (SOME t. t \<in> A)))"
  by (auto simp add: the_inv_into_def)

lemma encode_decode_A_eq:
  "\<lbrakk> inj_on (enc::'a \<Rightarrow>'b) (A::'a set);
     (dec::'b \<Rightarrow> 'a) = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w)
                             then (THE t. t\<in>A \<and> enc t = w)
                             else (SOME t. t \<in> A)))
   \<rbrakk> \<Longrightarrow> \<forall>M\<in>A. dec(enc M) = M"
proof
  fix M
  assume inj_enc: "inj_on enc A"
    and dec_def: "dec = (\<lambda>w. if \<exists>t\<in>A. enc t = w then THE t. t \<in> A \<and> enc t = w else SOME t. t \<in> A)"
    and M_in_A: "M \<in> A"
  show "dec (enc M) = M"
  proof -
    from dec_def have
      dec_def': "dec = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w) then (the_inv_into A enc) w else (SOME t. t \<in> A)))"
      by (rule dec_is_inv_on_A)
    from M_in_A have "\<exists>t\<in>A. enc t = (enc M)" by auto
    with M_in_A inj_enc and dec_def' show "dec (enc M) = M" by (auto simp add: the_inv_into_f_f)
  qed
qed

lemma decode_encode_A_eq:
  "\<lbrakk> inj_on (enc::'a \<Rightarrow>'b) (A::'a set);
    dec = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w) then (THE t. t\<in>A \<and> enc t = w) else (SOME t. t \<in> A)))\<rbrakk>
  \<Longrightarrow> \<forall>w. w \<in> enc`A \<longrightarrow> enc(dec(w)) = w"
proof 
  fix w
  assume inj_enc: "inj_on enc A"
    and dec_def: "dec = (\<lambda>w. if \<exists>t\<in>A. enc t = w then THE t. t \<in> A \<and> enc t = w else SOME t. t \<in> A)"
  show "w \<in> enc ` A \<longrightarrow> enc (dec w) = w"
  proof
    assume "w \<in> enc ` A"
    from dec_def have
      dec_def': "dec = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w) then (the_inv_into A enc) w else (SOME t. t \<in> A)))"
      by (rule dec_is_inv_on_A)
    with \<open>w \<in> enc ` A\<close> and inj_enc
    show "enc (dec w) = w" 
      by (auto simp add: the_inv_into_f_f)
  qed
qed

lemma dec_in_A:
  "\<lbrakk>inj_on (enc::'a \<Rightarrow>'b) (A::'a set);
   dec = (\<lambda>w. if \<exists>t\<in>A. enc t = w then THE t. t \<in> A \<and> enc t = w else SOME t. t \<in> A);
   A \<noteq> {} \<rbrakk>
  \<Longrightarrow> \<forall>w. dec w \<in> A"
proof
  fix w
  assume inj_enc: "inj_on enc A"
    and dec_def: "dec = (\<lambda>w. if \<exists>t\<in>A. enc t = w then THE t. t \<in> A \<and> enc t = w else SOME t. t \<in> A)"
    and not_empty_A: "A \<noteq> {}"
  show "dec w \<in> A"
  proof (cases "\<exists>t\<in>A. enc t = w")
    assume "\<exists>t\<in>A. enc t = w"
    from dec_def have
      dec_def': "dec = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w) then (the_inv_into A enc) w else (SOME t. t \<in> A)))"
      by (rule dec_is_inv_on_A)
    with \<open>\<exists>t\<in>A. enc t = w\<close> inj_enc show ?thesis by (auto simp add: the_inv_into_f_f)
  next
    assume "\<not>(\<exists>t\<in>A. enc t = w)"
    from dec_def have
      dec_def': "dec = (\<lambda>w. (if (\<exists>t\<in>A. enc t = w) then (the_inv_into A enc) w else (SOME t. t \<in> A)))"
      by (rule dec_is_inv_on_A)
    with \<open>\<not>(\<exists>t\<in>A. enc t = w)\<close> have "dec w = (SOME t. t \<in> A)" by auto
    from not_empty_A have "\<exists>x. x \<in> A" by auto
    then have "(SOME t. t \<in> A) \<in> A" by (rule someI_ex)
    with \<open>dec w = (SOME t. t \<in> A)\<close> show ?thesis by auto
  qed
qed

subsubsection \<open>An injective encoding of Turing Machines into the natural number\<close>

text \<open>
  We define an injective encoding function from Turing machines to natural numbers.
  This encoding function is only used for the proof of the undecidability of
  the special halting problem K where we use a locale that postulates the existence of
  some injective encoding of the Turing machines into the natural numbers.
\<close>

fun tm_to_nat_list ::  "tprog0 \<Rightarrow> nat list"
  where
    "tm_to_nat_list []              = []" |
    "tm_to_nat_list ((WB  ,s) # is) = 0 # s #  tm_to_nat_list is" |
    "tm_to_nat_list ((WO  ,s) # is) = 1 # s #  tm_to_nat_list is" |
    "tm_to_nat_list ((L   ,s) # is) = 2 # s #  tm_to_nat_list is" |
    "tm_to_nat_list ((R   ,s) # is) = 3 # s #  tm_to_nat_list is" |
    "tm_to_nat_list ((Nop ,s) # is) = 4 # s #  tm_to_nat_list is"

lemma prefix_tm_to_nat_list_cons:
 "\<exists>u v. tm_to_nat_list (x#xs) = u # v # tm_to_nat_list xs"
proof (cases x)
  case (Pair a b)
  then show ?thesis by (cases a)(auto)
qed

lemma tm_to_nat_list_cons_is_not_nil: "tm_to_nat_list (x#xs) \<noteq> tm_to_nat_list []"
proof
  assume "tm_to_nat_list (x # xs) = tm_to_nat_list []"
  moreover have "\<exists>u v. tm_to_nat_list (x#xs) = u # v # tm_to_nat_list xs"
    by (rule prefix_tm_to_nat_list_cons)
  ultimately show False by auto
qed

lemma inj_in_fst_arg_tm_to_nat_list:
 "tm_to_nat_list (x # xs) = tm_to_nat_list (y # xs) \<Longrightarrow> x = y"
proof (cases x, cases y)
  case (Pair a b)
  fix a1 s1 a2 s2
  assume "tm_to_nat_list (x # xs) = tm_to_nat_list (y # xs)"
  and "x = (a1, s1)" and "y = (a2, s2)"
  then show ?thesis by  (cases a1; cases a2)(auto)
qed

lemma inj_tm_to_nat_list: "tm_to_nat_list xs = tm_to_nat_list ys \<longrightarrow> xs = ys"
proof (induct xs ys rule:  list_induct2')
  case 1
  then show ?case by blast
next
  case (2 x xs)
  then show ?case
  proof
    assume "tm_to_nat_list (x # xs) = tm_to_nat_list []"
    then have False using tm_to_nat_list_cons_is_not_nil by auto
    then show "x # xs = []" by auto
  qed
next
  case (3 y ys)
  then show ?case
  proof
    assume "tm_to_nat_list [] = tm_to_nat_list (y # ys)"
    then have "tm_to_nat_list (y # ys) = tm_to_nat_list []" by (rule sym)
    then have False using tm_to_nat_list_cons_is_not_nil by auto
    then show "[] = y # ys" by auto
  qed
next
  case (4 x xs y ys)
  then have IH: "tm_to_nat_list xs = tm_to_nat_list ys \<longrightarrow> xs = ys" .
  show ?case
  proof
    assume A: "tm_to_nat_list (x # xs) = tm_to_nat_list (y # ys)"
    have "\<exists>u v. tm_to_nat_list (x#xs) = u # v # tm_to_nat_list xs"
      by (rule prefix_tm_to_nat_list_cons)
    then obtain u1 v1 where w_u1_v1: "tm_to_nat_list (x#xs) = u1 # v1 # tm_to_nat_list xs"
      by blast
    have "\<exists>u v. tm_to_nat_list (y#ys) = u # v # tm_to_nat_list ys"
      by (rule prefix_tm_to_nat_list_cons)
    then obtain u2 v2 where w_u2_v2: "tm_to_nat_list (y#ys) = u2 # v2 # tm_to_nat_list ys"
      by blast
    from A and w_u1_v1 and w_u2_v2 have "tm_to_nat_list xs = tm_to_nat_list ys" by auto
    with IH have "xs = ys" by auto
    moreover with A have "x=y" using inj_in_fst_arg_tm_to_nat_list by auto
    ultimately show "x # xs = y # ys" by auto
  qed
qed

definition tm_to_nat ::  "tprog0 \<Rightarrow> nat"
  where "tm_to_nat = (list_encode \<circ> tm_to_nat_list)"

theorem inj_tm_to_nat: "inj tm_to_nat"
  unfolding tm_to_nat_def
proof  (rule inj_compose)
  show "inj list_encode" by (rule inj_list_encode)
next
  show "inj tm_to_nat_list"
    unfolding inj_def by (auto simp add: inj_tm_to_nat_list)
qed

(* --- For demo purposes in classes we provide some inverse functions, explicitly --- *)

(* Note:
 * For cases where we argument list cannot be the image of nat_list_to_tm
 * we choose some arbitrary but fixed value.
 * Here we choose [(Nop, 0)].
 * However, any instruction list would do the job, we.g. [].
 *)

fun nat_list_to_tm      :: "nat list \<Rightarrow> tprog0"
  where
    "nat_list_to_tm  [] =  []"
  | "nat_list_to_tm  [ac] = [(Nop, 0)]"
  | "nat_list_to_tm  (ac # s # ns) = (
           if ac < 5
           then ([WB,WO,L,R,Nop]!ac ,s) # nat_list_to_tm ns
           else [(Nop, 0)])"

(* -- *)

lemma  nat_list_to_tm_is_inv_of_tm_to_nat_list: "nat_list_to_tm (tm_to_nat_list ns) = ns"
proof (induct ns)
  case Nil
  then show ?case by auto
next
  case (Cons a ns)
  fix instr ns
  assume IV: "nat_list_to_tm (tm_to_nat_list ns) = ns"
  show "nat_list_to_tm (tm_to_nat_list (instr # ns)) = instr # ns"
  proof (cases instr)
    case (Pair ac s)
    then have "instr = (ac, s)" .
    with Pair IV show "nat_list_to_tm (tm_to_nat_list (instr # ns)) = instr # ns"
      by (cases ac; cases s) auto
  qed
qed

definition nat_to_tm ::  "nat \<Rightarrow> tprog0"
  where "nat_to_tm = (nat_list_to_tm \<circ> list_decode)"

(* The function nat_to_tm is an explicit witness for the function ct2,
   which we define by non-constructive logic in theory HaltingProblems_K_H
   by

    definition c2t :: "nat \<Rightarrow> instr list"
      where
        "c2t = (\<lambda>n. if (\<exists>p. t2c p = n)
                   then (THE  p. t2c p = n)
                   else (SOME p. True) )"  <-- some arbitrary but fixed value
*)    
   
(* Compare the next lemma to
    lemma c2t_comp_t2c_eq: "c2t (t2c p) = p"
   in theory HaltingProblems_K_H
 *)

lemma nat_to_tm_is_inv_of_tm_to_nat: "nat_to_tm (tm_to_nat tm) = tm"
  by (simp add: nat_list_to_tm_is_inv_of_tm_to_nat_list nat_to_tm_def tm_to_nat_def)

end
