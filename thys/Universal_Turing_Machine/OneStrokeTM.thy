(* Title: thys/OnetrokeTM.thy
   Author: Franz Regensburger (FABR) 03/2022
 *)

subsection \<open>tm\_onestroke: A Machine for deciding the empty set\<close>

theory OneStrokeTM
  imports
    Turing_Hoare
begin

declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]

subsubsection \<open>Definition of the machine tm\_onestroke\<close>

text \<open>We can rely on the fact, that on the initial tape,
two consecutive blanks mean end of input
(see theorem @{thm "noDblBk_tape_of_nat_list"}).

Thus, the machine can check both ends of the (initial) tape.
Note however, that this is just a convention for encoding arguments for functions.
Nevertheless, the tape is (potentially) infinite on both sides.
\<close>

definition tm_onestroke :: "instr list"
  where
    "tm_onestroke \<equiv> [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2)]"

subsubsection \<open>The machine tm\_onestroke in action\<close>

(* <[]> *)
value "steps0 (1, [], <([]::nat list)>) tm_onestroke 0" (* "(1, [], [])" *)
value "steps0 (1, [], <([]::nat list)>) tm_onestroke 1" (* "(3, [Bk], [])" *)
value "steps0 (1, [], <([]::nat list)>) tm_onestroke 2" (* "(0, [Bk], [Oc])" *)

lemma "steps0 (1, [], <([]::nat list)>) tm_onestroke 2 = (0, [Bk], [Oc])"
  by (simp add: tape_of_nat_def tape_of_list_def
                tm_onestroke_def
                numeral_eqs_upto_12
                step.simps steps.simps)

(*  <[0]> *)
value "steps0 (1, [], <[0::nat]>) tm_onestroke 0"  (* "(1, [], [Oc])" *)
value "steps0 (1, [], <[0::nat]>) tm_onestroke 1"  (* "(2, [], [Bk])" *)
value "steps0 (1, [], <[0::nat]>) tm_onestroke 2"  (* "(1, [Bk], [])" *)
value "steps0 (1, [], <[0::nat]>) tm_onestroke 3"  (* "(3, [Bk, Bk], [])" *)
value "steps0 (1, [], <[0::nat]>) tm_onestroke 4"  (* "(0, [Bk, Bk], [Oc])" *)

lemma "steps0 (1, [], <[0::nat]>) tm_onestroke 4 = (0, [Bk, Bk], [Oc])"
  by (simp add: tape_of_nat_def tape_of_list_def
                tm_onestroke_def
                numeral_eqs_upto_12
                step.simps steps.simps)

(*  <[0,0]> *)
lemma "steps0 (1, [], <[0::nat,0]>) tm_onestroke 7 = (0, [Bk, Bk, Bk, Bk], [Oc])"
  by (simp add: tape_of_nat_def tape_of_list_def
                tm_onestroke_def
                numeral_eqs_upto_12
                step.simps steps.simps)

(*  <[1,1]> *)
lemma "steps0 (1, [], <[1::nat,1]>) tm_onestroke 11 = (0, [Bk, Bk, Bk, Bk, Bk, Bk], [Oc])"
  by (simp add: tape_of_nat_def tape_of_list_def
                tm_onestroke_def
                numeral_eqs_upto_12
                step.simps steps.simps)

subsubsection \<open>Partial and Total Correctness of machine tm\_onestroke\<close>

(* Assemble an invariant for the Hoare style proofs:

value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 0"    (* "(1, [], [Oc, Oc, Bk, Oc, Oc])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 1"    (* "(2, [], [Bk, Oc, Bk, Oc, Oc])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 2"    (* "(1, [Bk], [Oc, Bk, Oc, Oc])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 3"    (* "(2, [Bk], [Bk, Bk, Oc, Oc])" <== DblBk in r *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 4"    (* "(1, [Bk, Bk], [Bk, Oc, Oc])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 5"    (* "(3, [Bk, Bk, Bk], [Oc, Oc])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 6"    (* "(2, [Bk, Bk, Bk], [Bk, Oc])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 7"    (* "(1, [Bk, Bk, Bk, Bk], [Oc])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 8"    (* "(2, [Bk, Bk, Bk, Bk], [Bk])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 9"    (* "(1, [Bk, Bk, Bk, Bk, Bk], [])" *)

value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 10"   (* "(3, [Bk, Bk, Bk, Bk, Bk, Bk], [])" *)
value "steps0 (1, [], <[1::nat,1]>) tm_onestroke 11"   (* "(0, [Bk, Bk, Bk, Bk, Bk, Bk], [Oc])" *)

*)

fun 
  inv_tm_onestroke1 :: "tape \<Rightarrow> bool" and
  inv_tm_onestroke2 :: "tape \<Rightarrow> bool" and
  inv_tm_onestroke3 :: "tape \<Rightarrow> bool" and
  inv_tm_onestroke0 :: "tape \<Rightarrow> bool"
  where
    "inv_tm_onestroke1 (l, r) = 
        (noDblBk r \<and> l = Bk\<up> (length l) )"
  | "inv_tm_onestroke2 (l, r) =
        (noDblBk (tl r) \<and> l = Bk\<up> (length l) \<and> (\<exists>rs. r = Bk#rs))"
  | "inv_tm_onestroke3 (l, r) =
        (noDblBk r \<and> l = Bk\<up> (length l) \<and> (r= [] \<or> (\<exists>rs. r = Oc#rs)) )"
  | "inv_tm_onestroke0 (l, r) =
         (noDblBk r \<and> l = Bk\<up> (length l) \<and> (r = [Oc]))"

fun inv_tm_onestroke :: "config \<Rightarrow> bool"
  where
    "inv_tm_onestroke (s, tap) = 
        (if s = 0 then inv_tm_onestroke0 tap else
         if s = 1 then inv_tm_onestroke1 tap else
         if s = 2 then inv_tm_onestroke2 tap else
         if s = 3 then inv_tm_onestroke3 tap 
         else False)"

lemma tm_onestroke_cases: 
  fixes s::nat
  assumes "inv_tm_onestroke (s,l,r)"
    and "s=0 \<Longrightarrow> P"
    and "s=1 \<Longrightarrow> P"
    and "s=2 \<Longrightarrow> P"
    and "s=3 \<Longrightarrow> P"
  shows "P"
proof -
  have "s < 4"
  proof (rule ccontr)
    assume "\<not> s < 4"
    with \<open>inv_tm_onestroke (s,l,r)\<close> show False by auto
  qed
  then have "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3" by auto
  with assms show ?thesis by auto
qed

lemma inv_tm_onestroke_step: 
  assumes "inv_tm_onestroke cf" 
  shows "inv_tm_onestroke (step0 cf tm_onestroke)"
proof (cases cf)
  case (fields s l r)
  then have cf_cases: "cf = (s, l, r)" .
  show "inv_tm_onestroke (step0 cf tm_onestroke)"
  proof (rule tm_onestroke_cases)
    from cf_cases and assms
    show "inv_tm_onestroke (s, l, r)" by auto
  next
    assume "s = 0"
    with cf_cases and assms
    show ?thesis by (auto simp add: tm_onestroke_def)
  next
    assume "s = 1"
    show ?thesis
    proof -
      have "inv_tm_onestroke (step0 (1, l, r) tm_onestroke)"
      proof (cases r)
        case Nil
        then have "r = []" .
        with assms and cf_cases and \<open>s = 1\<close> show ?thesis
          by (auto simp add: tm_onestroke_def step.simps steps.simps)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases a)
        next
          case Oc
          then have "a = Oc" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 1\<close>
          show ?thesis 
            by (auto simp add: tm_onestroke_def noDblBk_def
                               step.simps steps.simps)
        next
          case Bk
          then have "a = Bk" .

          from assms and cf_cases  and \<open>s = 1\<close> have "noDblBk r" by auto
          with \<open>r = a # rs\<close> have "noDblBk rs" by (auto simp add: noDblBk_def)

          from \<open>r = a # rs\<close> and \<open>a = Bk\<close> and \<open>noDblBk r\<close>          
          have "r!0 = Bk \<and> (rs = [] \<or> r!(Suc 0) = Oc)"
            using noDblBk_def by fastforce
          with \<open>r = a # rs\<close> have  "(rs = [] \<or> rs!0 = Oc)" by auto
          then have "(rs = [] \<or> (\<exists>rs'. rs = Oc#rs'))"
            by (metis hd_conv_nth list.collapse)

          from \<open>a = Bk\<close> and \<open>r = a # rs\<close> and cf_cases and \<open>s = 1\<close>
          have "inv_tm_onestroke (step0 (1, l, r) tm_onestroke) =
                  inv_tm_onestroke (step0 (1, l, Bk#rs) tm_onestroke)" by auto
          also have "... = inv_tm_onestroke (3, Bk#l,rs)"
            by (auto simp add: tm_onestroke_def step.simps steps.simps)

          also with assms and \<open>r = a # rs\<close>  and \<open>a = Bk\<close> and \<open>a = Bk\<close>
            and cf_cases and \<open>s = 1\<close> and \<open>noDblBk rs\<close>
            and \<open>(rs = [] \<or> (\<exists>rs'. rs = Oc#rs'))\<close>
          have "... = True"
            by (auto simp add: tm_onestroke_def numeral_eqs_upto_12)
          finally show ?thesis by auto
        qed
      qed
      with cf_cases and \<open>s=1\<close> show ?thesis by auto
    qed
  next
    assume "s = 2"
    show "inv_tm_onestroke (step0 cf tm_onestroke)"
    proof -
      have "inv_tm_onestroke (step0 (2, l, r) tm_onestroke)"
      proof (cases r)
        case Nil
        with assms and cf_cases and \<open>s = 2\<close> show ?thesis
          by (auto simp add: tm_onestroke_def numeral_eqs_upto_12)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases a)
          case Bk
          then have "a = Bk" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 2\<close>
          show ?thesis
            by (auto simp add: tm_onestroke_def numeral_eqs_upto_12
                               step.simps steps.simps)
        next
          case Oc
          then have "a = Oc" .
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 2\<close>
          show ?thesis by (auto simp add: tm_onestroke_def numeral_eqs_upto_12)
        qed
      qed
      with cf_cases and \<open>s=2\<close> show ?thesis by auto
    qed
  next
    assume "s = 3"
    show "inv_tm_onestroke (step0 cf tm_onestroke)"
    proof -
      have "inv_tm_onestroke (step0 (3, l, r) tm_onestroke)"
      proof (cases r)
        case Nil
        with assms and cf_cases and \<open>s = 3\<close> show ?thesis
          by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 noDblBk_def
                             step.simps steps.simps)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases a)
          case Oc
          with assms and \<open>r = a # rs\<close> and cf_cases and \<open>s = 3\<close>
          show ?thesis
            by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 noDblBk_def
                               step.simps steps.simps)
        next
          case Bk
          then have "a = Bk" .
          from assms and cf_cases and \<open>s = 3\<close>
          have "(r= [] \<or> (\<exists>rs. r = Oc#rs))" by auto
          with \<open>a = Bk\<close> and  \<open>r = a # rs\<close> have False by auto
          then show ?thesis by auto
        qed
      qed
      with cf_cases and \<open>s=3\<close> show ?thesis by auto
    qed
  qed
qed

lemma inv_tm_onestroke_steps: 
  assumes "inv_tm_onestroke cf" 
  shows "inv_tm_onestroke (steps0 cf tm_onestroke stp)"
proof (induct stp)
  case 0
  with assms show ?case
    by (auto simp add: inv_tm_onestroke_step step.simps steps.simps)
next
  case (Suc stp)
  with assms show ?case
    using inv_tm_onestroke_step step_red by auto 
qed

lemma tm_onestroke_partial_correctness:
  assumes "\<exists>stp. is_final (steps0 (1, [], <nl:: nat list>) tm_onestroke stp)"
  shows "\<lbrace> \<lambda>tap. tap = ([], <nl:: nat list>) \<rbrace> 
           tm_onestroke
         \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc]  @ Bk \<up>l) \<rbrace>"
proof (rule Hoare_consequence)
  show "(\<lambda>tap. tap = ([], <nl>)) \<mapsto> (\<lambda>tap. tap = ([], <nl>))" by auto
next
  show "inv_tm_onestroke0 \<mapsto> (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc]  @ Bk \<up>l))"
    using assert_imp_def by auto
next
  show "\<lbrace> \<lambda>tap. tap = ([], <nl:: nat list>) \<rbrace> tm_onestroke \<lbrace> inv_tm_onestroke0 \<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r:: "cell list"
    assume "(l, r) = ([], <nl:: nat list>)"
    with assms have "\<exists>n. is_final (steps0 (1, l, r) tm_onestroke n)" by auto
    then obtain stp where w_n: "is_final (steps0 (1, l, r) tm_onestroke stp)" by blast

    moreover have "inv_tm_onestroke0 holds_for steps0 (1, l, r) tm_onestroke stp"
    proof -
      have h: "inv_tm_onestroke (steps0 (1, [], <nl:: nat list>) tm_onestroke stp)"
        by  (rule inv_tm_onestroke_steps)(auto simp add: noDblBk_tape_of_nat_list)
      with  \<open>(l, r) = ([], <nl:: nat list>)\<close> show ?thesis
        by (metis Pair_inject holds_for.elims(3) inv_tm_onestroke.elims(2) is_final_eq w_n)
    qed
    ultimately 
    show "\<exists>n. is_final (steps0 (1, l, r) tm_onestroke n) \<and>
              inv_tm_onestroke0 holds_for steps0 (1, l, r) tm_onestroke n"
      by auto
  qed
qed

(* --- now, we prove termination of tm_onestroke and thus total correctness --- *)
(* 
    Lexicographic orders (See List.measures)
    quote: "These are useful for termination proofs"
    
    lemma in_measures[simp]:
      "(x, y) \<in> measures [] = False"
      "(x, y) \<in> measures (f # fs)
             = (f x < f y \<or> (f x = f y \<and> (x, y) \<in> measures fs))"
*)

(* Assemble a lexicographic measure function *)

definition measure_tm_onestroke :: "(config \<times> config) set"
  where
    "measure_tm_onestroke = measures [
      \<lambda>(s, l, r). (if s = 0 then 0 else 1),
      \<lambda>(s, l, r). length r,
      \<lambda>(s, l, r). count_list r Oc,
      \<lambda>(s, l, r). (if s = 3 then 0 else 1)      
      ]"

lemma wf_measure_tm_onestroke: "wf measure_tm_onestroke"
  unfolding measure_tm_onestroke_def
  by (auto)

lemma measure_tm_onestroke_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_tm_onestroke\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_tm_onestroke
  by (metis wf_iff_no_infinite_down_chain)

(* Machine tm_onestroke always halts *)

lemma tm_onestroke_induct_halts: "\<exists> stp. is_final (steps0 (1, [], <nl:: nat list>) tm_onestroke stp)"
proof (induct rule: measure_tm_onestroke_induct)
  case (Step stp)
  then have "\<not>is_final (steps0 (1, [], <nl>) tm_onestroke stp)" .

  have "inv_tm_onestroke (steps0 (1, [], <nl>) tm_onestroke stp)"
  proof (rule_tac inv_tm_onestroke_steps)
    show "inv_tm_onestroke (1, [], <nl>)"
      by (auto simp add: noDblBk_tape_of_nat_list)
  qed

  show "(steps0 (1, [], <nl>) tm_onestroke (Suc stp), steps0 (1, [], <nl>) tm_onestroke stp)
         \<in> measure_tm_onestroke"
  proof (cases "steps0 (1, [], <nl>) tm_onestroke stp")
    case (fields s l r)
    then have cf_cases: "steps0 (1, [], <nl>) tm_onestroke stp = (s, l, r)" .

    show ?thesis
    proof (rule tm_onestroke_cases)
      from \<open>inv_tm_onestroke (steps0 (1, [], <nl>) tm_onestroke stp)\<close> and cf_cases
      show "inv_tm_onestroke (s, l, r)" by auto
    next
      assume "s=0"
      with cf_cases \<open>\<not>is_final (steps0 (1, [], <nl>) tm_onestroke stp)\<close> show ?thesis by auto
    next
      assume "s=1"
      show ?thesis
      proof (cases r)
        case Nil
        then have "r = []" .
        with cf_cases and \<open>s=1\<close> have "steps0 (1, [], <nl>) tm_onestroke stp = (1, l, [])" by auto       
        have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) =
              step0 (steps0 (1,[], <nl>) tm_onestroke stp) tm_onestroke"
          by (rule step_red)
        also with cf_cases and \<open>s=1\<close> and \<open>r = []\<close> have "... = step0 (1,l,[]) tm_onestroke" by auto
        also have "... = (3,Bk#l,[])"
          by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) = (3,Bk#l,[])" by auto

        with \<open>steps0 (1, [], <nl>) tm_onestroke stp = (1, l, [])\<close>
        show ?thesis by (auto simp add: measure_tm_onestroke_def)
      next
        case (Cons a rs)
        then have "r = a # rs" .
        show ?thesis
        proof (cases "a")
          case Bk
          then have "a=Bk" .
          with cf_cases and \<open>s=1\<close> and \<open>r = a # rs\<close>
          have "steps0 (1, [], <nl>) tm_onestroke stp = (1, l, Bk#rs)" by auto       

          have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) =
                step0 (steps0 (1, [], <nl>) tm_onestroke stp) tm_onestroke"
            by (rule step_red)
          also  with cf_cases and \<open>s=1\<close> and \<open>r = a # rs\<close> and \<open>a=Bk\<close>
          have "... = step0 ((1, l, Bk#rs)) tm_onestroke" by auto
          also have "... = (3,Bk#l,rs)"
            by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) = (3,Bk#l,rs)" by auto

          with \<open>steps0 (1, [], <nl>) tm_onestroke stp = (1, l, Bk#rs)\<close>
          show ?thesis by (auto simp add: measure_tm_onestroke_def)
        next
          case Oc
          then have "a=Oc" .
          with cf_cases and \<open>s=1\<close> and \<open>r = a # rs\<close>
          have "steps0 (1, [], <nl>) tm_onestroke stp = (1, l, Oc#rs)"  by auto   

          have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) =
                step0 (steps0 (1, [], <nl>) tm_onestroke stp) tm_onestroke"
            by (rule step_red)
          also  with cf_cases and \<open>s=1\<close> and \<open>r = a # rs\<close> and \<open>a=Oc\<close>
          have "... = step0 ((1, l, Oc#rs)) tm_onestroke" by auto
          also have "... = (2,l,Bk#rs)"
            by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) = (2,l,Bk#rs)" by auto

          with \<open>steps0 (1, [], <nl>) tm_onestroke stp = (1, l, Oc#rs)\<close>
          show ?thesis by (auto simp add: measure_tm_onestroke_def)
        qed         
      qed
    next
      assume "s=2"
      show ?thesis
      proof -
        from cf_cases and \<open>s=2\<close> have "steps0 (1, [], <nl>) tm_onestroke stp = (2, l, r)" by auto
        with \<open>inv_tm_onestroke (steps0 (1, [], <nl>) tm_onestroke stp)\<close> have "(\<exists>rs. r = Bk#rs)" by auto
        then obtain rs where "r = Bk#rs" by blast
        with \<open>steps0 (1, [], <nl>) tm_onestroke stp = (2, l, r)\<close>
        have "steps0 (1, [], <nl>) tm_onestroke stp = (2, l, Bk#rs)" by auto

        have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) =
              step0 (steps0 (1, [], <nl>) tm_onestroke stp) tm_onestroke"
          by (rule step_red)
        also with cf_cases and \<open>s=2\<close> and \<open>r = Bk#rs\<close>
        have "... = step0 (2,l,Bk#rs) tm_onestroke" by auto
        also have "... = (1,Bk#l,rs)"
          by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 step.simps steps.simps)
        finally have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) = (1,Bk#l,rs)" by auto

        with \<open>steps0 (1, [], <nl>) tm_onestroke stp = (2, l, Bk#rs)\<close>
        show ?thesis by (auto simp add: measure_tm_onestroke_def)
      qed
    next
      assume "s=3"
      show ?thesis
      proof -
        from cf_cases and \<open>s=3\<close> have "steps0 (1, [], <nl>) tm_onestroke stp = (3, l, r)" by auto
        with \<open>inv_tm_onestroke (steps0 (1,[], <nl>) tm_onestroke stp)\<close> have "(r= [] \<or> (\<exists>rs. r = Oc#rs))" by auto
        then show ?thesis
        proof
          assume "r = []"
          with cf_cases and \<open>s=3\<close> have "steps0 (1, [], <nl>) tm_onestroke stp = (3, l, [])" by auto       
          have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) =
                step0 (steps0 (1, [], <nl>) tm_onestroke stp) tm_onestroke"
            by (rule step_red)
          also with cf_cases and \<open>s=3\<close> and \<open>r = []\<close>
          have "... = step0 (3,l,[]) tm_onestroke" by auto
          also have "... = (0,l,[Oc])"
            by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) = (0,l,[Oc])" by auto

          with \<open>steps0 (1, [], <nl>) tm_onestroke stp = (3, l, [])\<close>
          show ?thesis by (auto simp add: measure_tm_onestroke_def)
        next
          assume "\<exists>rs. r = Oc # rs"
          then obtain rs where "r = Oc # rs" by blast
          with cf_cases and \<open>s=3\<close> have "steps0 (1, [], <nl>) tm_onestroke stp = (3, l,Oc # rs)" by auto       
          have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) =
                step0 (steps0 (1, [], <nl>) tm_onestroke stp) tm_onestroke"
            by (rule step_red)
          also with cf_cases and \<open>s=3\<close> and \<open>r = Oc # rs\<close>
          have "... = step0 (3,l,Oc # rs) tm_onestroke" by auto
          also have "... = (2,l,Bk#rs)"
            by (auto simp add: tm_onestroke_def numeral_eqs_upto_12 step.simps steps.simps)
          finally have "steps0 (1, [], <nl>) tm_onestroke (Suc stp) = (2,l,Bk#rs)" by auto

          with \<open>steps0 (1, [], <nl>) tm_onestroke stp = (3, l,Oc # rs)\<close>
          show ?thesis by (auto simp add: measure_tm_onestroke_def)
        qed
      qed
    qed
  qed
qed

lemma tm_onestroke_total_correctness:
  "\<lbrace> \<lambda>tap. tap = ([], <nl:: nat list>) \<rbrace> tm_onestroke \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc]  @ Bk \<up>l) \<rbrace>"
proof (rule tm_onestroke_partial_correctness)
  show "\<exists>stp. is_final (steps0 (1, [], <nl>) tm_onestroke stp)"
    using  tm_onestroke_induct_halts by auto
qed

end
