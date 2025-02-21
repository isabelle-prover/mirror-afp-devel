section \<open> Key algorithms for WEST \<close>

theory WEST_Algorithms

imports Mission_Time_LTL.MLTL_Properties

begin

subsection \<open>Custom Types\<close>

datatype WEST_bit = Zero | One | S
type_synonym state = "nat set"
type_synonym trace = "nat set list"
type_synonym state_regex = "WEST_bit list"
type_synonym trace_regex = "WEST_bit list list"
type_synonym WEST_regex = "WEST_bit list list list"

subsection \<open>Trace Regular Expressions\<close>

fun WEST_get_bit:: "trace_regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WEST_bit"
  where "WEST_get_bit regex timestep var = (
  if timestep \<ge> length regex then S
  else let regex_index = regex ! timestep in
  if var \<ge> length regex_index then S
  else regex_index ! var
  )"

text \<open> Returns the state at time i, list of variable states \<close>
fun WEST_get_state:: "trace_regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state_regex"
  where "WEST_get_state regex time num_vars = (
  if time \<ge> length regex then (map (\<lambda> k. S) [0 ..< num_vars])
  else regex ! time
  )"


text \<open> Checks if one state of a trace matches one timeslice of a WEST regex \<close>
definition match_timestep:: "nat set \<Rightarrow> state_regex \<Rightarrow> bool"
  where "match_timestep state regex_state = (\<forall> x::nat. x < length regex_state \<longrightarrow> (
  ((regex_state ! x = One) \<longrightarrow> x \<in> state) \<and>
  ((regex_state ! x = Zero) \<longrightarrow> x \<notin> state)))"

fun trim_reversed_regex:: "trace_regex \<Rightarrow> trace_regex"
  where "trim_reversed_regex [] = []"
  | "trim_reversed_regex (h#t) = (if (\<forall>i<length h. (h!i) = S)
  then (trim_reversed_regex t) else (h#t))"

fun trim_regex:: "trace_regex \<Rightarrow> trace_regex"
  where "trim_regex regex = rev (trim_reversed_regex (rev regex))"

definition match_regex:: "nat set list \<Rightarrow> trace_regex \<Rightarrow> bool"
  where "match_regex trace regex =  ((\<forall> time<length regex.
  (match_timestep (trace ! time) (regex ! time)))
  \<and>(length trace \<ge> length regex))"

definition match:: "nat set list \<Rightarrow> WEST_regex \<Rightarrow> bool"
  where "match trace regex_list = (\<exists> i. i < length regex_list \<and>
  (match_regex trace (regex_list ! i)))"

lemma match_example:
  shows "match [{0::nat,1}, {1}, {0}]
  [
    [[Zero,Zero]],
    [[S,S], [S,One]]
  ] = True"
proof-
  let ?regexList = "[[[Zero,Zero]],[[S,S], [S,One]]]"
  let ?trace = "[{0::nat,1}, {1}, {0}]"
  have "(match_regex ?trace (?regexList!1))"
    unfolding match_regex_def
    by (simp add: match_timestep_def nth_Cons')
  then show ?thesis
    by (metis One_nat_def add.commute le_imp_less_Suc le_numeral_extra(4) list.size(3) list.size(4) match_def plus_1_eq_Suc)
qed


definition regex_equiv:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow> bool"
  where "regex_equiv rl1 rl2 = (
  \<forall> \<pi>::nat set list. (match \<pi> rl1) \<longleftrightarrow> (match \<pi> rl2))"


lemma "(regex_equiv [[[S,S]]]
  [[[S,One]],
    [[One,S]],
    [[Zero,Zero]]]) = True"
proof -
  have d1: "match \<pi> [[[S, One]], [[One, S]], [[Zero, Zero]]]" if match: "match \<pi> [[[S, S]]]" for \<pi>
  proof -
    have match_ss: "match_regex \<pi> [[S, S]]"
      using match unfolding match_def
      by (metis One_nat_def length_Cons less_one list.size(3) nth_Cons_0)
    {assume *: "\<not> (match_regex \<pi> [[S, One]]) \<and> \<not> (match_regex \<pi> [[One, S]])"
      have "match_regex \<pi> [[Zero, Zero]]"
        using match_ss unfolding match_regex_def
        by (smt (verit) "*" One_nat_def WEST_bit.simps(2) length_Cons less_2_cases less_one list.size(3) match_regex_def match_timestep_def nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
    }
    then show ?thesis
      unfolding match_def
      by (metis length_Cons less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc)
  qed
  have d2: "match \<pi> [[[S, S]]]" if match: "match \<pi> [[[S, One]], [[One, S]], [[Zero, Zero]]]" for \<pi>
  proof -
    {assume *: "match_regex \<pi> [[S, One]]"
      then have "match_regex \<pi> [[S, S]]"
        unfolding  match_regex_def
        by (smt (verit, ccfv_SIG) One_nat_def WEST_bit.simps(4) length_Cons less_2_cases less_one list.size(3) match_timestep_def nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
      then have "match \<pi> [[[S, S]]]"
        unfolding match_def by simp
    } moreover {assume *: "match_regex \<pi> [[One, S]]"
      then have "match_regex \<pi> [[S, S]]"
        unfolding  match_regex_def
        by (smt (verit, ccfv_SIG) One_nat_def WEST_bit.simps(4) length_Cons less_2_cases less_one list.size(3) match_timestep_def nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
      then have "match \<pi> [[[S, S]]]"
        unfolding match_def by simp
    } moreover {assume *: "match_regex \<pi> [[Zero, Zero]]"
      then have "match_regex \<pi> [[S, S]]"
        unfolding  match_regex_def
        by (smt (verit) One_nat_def WEST_bit.distinct(5) length_Cons less_2_cases_iff less_one list.size(3) match_timestep_def nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
      then have "match \<pi> [[[S, S]]]"
        unfolding match_def by simp
    }
    ultimately show ?thesis using match unfolding regex_equiv_def
      by (smt (verit, del_insts) length_Cons less_Suc_eq_0_disj match_def nth_Cons_0 nth_Cons_Suc)
  qed
  show ?thesis using d1 d2
    unfolding regex_equiv_def by metis
qed


subsection \<open> WEST Operations \<close>

subsubsection \<open> AND \<close>


fun WEST_and_bitwise::"WEST_bit \<Rightarrow>
                       WEST_bit \<Rightarrow>
                       WEST_bit option"
  where "WEST_and_bitwise b One = (if b = Zero then None else Some One)"
  | "WEST_and_bitwise b Zero = (if b = One then None else Some Zero)"
  | "WEST_and_bitwise b S = Some b"



fun WEST_and_state:: "state_regex \<Rightarrow> state_regex \<Rightarrow> state_regex option"
  where "WEST_and_state [] [] = Some []"
  | "WEST_and_state (h1#t1) (h2#t2) =
  (case WEST_and_bitwise h1 h2 of
    None \<Rightarrow> None
    | Some b \<Rightarrow> (case WEST_and_state t1 t2 of
                  None \<Rightarrow> None
                  | Some L \<Rightarrow> Some (b#L)))"
  | "WEST_and_state _ _ = None"



fun WEST_and_trace:: "trace_regex \<Rightarrow> trace_regex \<Rightarrow> trace_regex option"
  where "WEST_and_trace trace [] = Some trace"
  | "WEST_and_trace [] trace = Some trace"
  | "WEST_and_trace (h1#t1) (h2#t2) =
  (case WEST_and_state h1 h2 of
    None \<Rightarrow> None
    | Some state \<Rightarrow> (case WEST_and_trace t1 t2 of
                      None \<Rightarrow> None
                      | Some trace \<Rightarrow> Some (state#trace)))"


fun WEST_and_helper:: "trace_regex \<Rightarrow> WEST_regex \<Rightarrow> WEST_regex"
  where "WEST_and_helper trace [] = []"
  | "WEST_and_helper trace (t#traces) =
  (case WEST_and_trace trace t of
    None \<Rightarrow> WEST_and_helper trace traces
    | Some res \<Rightarrow> res#(WEST_and_helper trace traces))"


fun WEST_and:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow> WEST_regex"
  where "WEST_and traceList [] = []"
  | "WEST_and [] traceList = []"
  | "WEST_and (trace#traceList1) traceList2 =
  (case WEST_and_helper trace traceList2 of
    [] \<Rightarrow> WEST_and traceList1 traceList2
    | traceList \<Rightarrow> traceList@(WEST_and traceList1 traceList2))"

subsubsection \<open>Simp\<close>

paragraph \<open>Bitwise simplification operation\<close>

fun WEST_simp_bitwise:: "WEST_bit \<Rightarrow> WEST_bit \<Rightarrow> WEST_bit"
  where "WEST_simp_bitwise b S = S"
  | "WEST_simp_bitwise b Zero = (if b = Zero then Zero else S)"
  | "WEST_simp_bitwise b One = (if b = One then One else S)"

fun WEST_simp_state:: "state_regex \<Rightarrow> state_regex \<Rightarrow> state_regex"
  where "WEST_simp_state s1 s2 = (
  map (\<lambda> k. WEST_simp_bitwise (s1 ! k) (s2 ! k)) [0 ..< (length s1)])"


fun WEST_simp_trace:: "trace_regex \<Rightarrow> trace_regex \<Rightarrow> nat => trace_regex"
  where "WEST_simp_trace trace1 trace2 num_vars = (
  map (\<lambda> k. (WEST_simp_state (WEST_get_state trace1 k num_vars) (WEST_get_state trace2 k num_vars)))
  [0 ..< (Max {(length trace1), (length trace2)})])"


paragraph \<open> Helper functions for defining WEST-simp \<close>

fun count_nonS_trace:: "state_regex \<Rightarrow> nat"
  where "count_nonS_trace [] = 0"
  | "count_nonS_trace (h#t) = (if (h \<noteq> S) then (1 + (count_nonS_trace t)) else (count_nonS_trace t))"

fun count_diff_state:: "state_regex \<Rightarrow> state_regex \<Rightarrow> nat"
  where "count_diff_state [] [] = 0"
  | "count_diff_state trace [] = count_nonS_trace trace"
  | "count_diff_state [] trace = count_nonS_trace trace"
  | "count_diff_state (h1#t1) (h2#t2) = (if (h1 = h2) then (count_diff_state t1 t2) else (1 + (count_diff_state t1 t2)))"

fun count_diff:: "trace_regex \<Rightarrow> trace_regex \<Rightarrow> nat"
  where "count_diff [] [] = 0"
  | "count_diff [] (h#t) = (count_diff_state [] h) + (count_diff [] t)"
  | "count_diff (h#t) [] = (count_diff_state [] h) + (count_diff [] t)"
  | "count_diff (h1#t1) (h2#t2) = (count_diff_state h1 h2) + (count_diff t1 t2)"

fun check_simp:: "trace_regex \<Rightarrow> trace_regex \<Rightarrow> bool"
  where "check_simp trace1 trace2 = ((count_diff trace1 trace2) \<le> 1 \<and> length trace1 = length trace2)"

fun enumerate_pairs :: "nat list \<Rightarrow> (nat * nat) list" where
  "enumerate_pairs [] = []" |
  "enumerate_pairs (x#xs) = map (\<lambda>y. (x, y)) xs @ enumerate_pairs xs"

fun enum_pairs:: "'a list \<Rightarrow> (nat * nat) list"
  where "enum_pairs L = enumerate_pairs [0 ..< length L]"

fun remove_element_at_index:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "remove_element_at_index n L = (take n L)@(drop (n+1) L)"

text \<open> This assumes (fst h) < (snd h) \<close>
fun update_L:: "WEST_regex \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "update_L L h num_vars =
(remove_element_at_index (fst h) (remove_element_at_index (snd h) L))@[WEST_simp_trace (L!(fst h)) (L!(snd h)) num_vars]"

paragraph \<open> Defining and Proving Termination of WEST-simp \<close>

lemma length_enumerate_pairs:
  shows "length (enumerate_pairs L) \<le> (length L)^2"
proof (induction L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  have length_L: "(length (a # L))\<^sup>2 = (1 + (length L))^2" by auto
  then have length_L: "(length (a # L))\<^sup>2 = 1 + 2*(length L) + (length L)^2" by algebra
  have "length (map (Pair a) L) \<le> length L"
    by simp
  then show ?case
    unfolding enumerate_pairs.simps using Cons length_L by simp
qed

lemma length_enum_pairs:
  shows "length (enum_pairs L) \<le> (length L)^2"
proof-
  show ?thesis unfolding enum_pairs.simps using length_enumerate_pairs
    by (metis length_upt minus_nat.diff_0)
qed

lemma enumerate_pairs_fact:
  assumes "\<forall> i j. (i < j \<and> i < length L \<and> j < length L) \<longrightarrow> (L!i) < (L!j)"
  shows "\<forall> pair \<in> set (enumerate_pairs L). (fst pair) < (snd pair)"
  using assms
proof(induct "length L" arbitrary:L)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain h T where obt_hT: "L = h#T"
    by (metis length_Suc_conv)
  then have enum_L: "enumerate_pairs L = map (Pair h) T @ enumerate_pairs T"
    using enumerate_pairs.simps obt_hT by blast
  then have "\<And> pair. pair \<in> set (enumerate_pairs L) \<Longrightarrow> fst pair < snd pair"
  proof-
    fix pair
    assume "pair \<in> set (enumerate_pairs L)"
    then have "pair \<in> set (map (Pair h) T @ enumerate_pairs T)" using enum_L by auto
    then have pair_or: "pair \<in> set (map (Pair h) T) \<or> pair \<in> set(enumerate_pairs T)"
      by auto
    {assume in_base: "pair \<in> set (map (Pair h) T)"
      have "\<forall>j. 0 < j \<and> j < length L \<longrightarrow> h < L ! j"
        using Suc.prems obt_hT by force
      then have "\<forall>j < length T. h < T!j"
        using obt_hT by force
      then have "\<forall>t \<in> set T. h < t"
        using obt_hT by (metis in_set_conv_nth)
      then have "fst pair < snd pair"
        using in_base by auto
    } moreover {
      assume in_rec: "pair \<in> set(enumerate_pairs T)"
      have "fst pair < snd pair"
        using Suc.hyps(1)[of T] Suc.prems obt_hT in_rec
        by (smt (verit, ccfv_SIG) Ex_less_Suc Suc.hyps(1) Suc.hyps(2) length_Cons less_trans_Suc nat.inject nth_Cons_Suc)
    }
    ultimately show "fst pair < snd pair" using enum_L obt_hT pair_or by blast
  qed
  then show ?case by blast
qed

lemma enum_pairs_fact:
  shows "\<forall> pair \<in> set (enum_pairs L). (fst pair) < (snd pair)"
  unfolding enum_pairs.simps using enumerate_pairs_fact[of "[0..<length L]"]
  by simp

lemma enum_pairs_bound_snd:
  assumes " pair \<in> set (enumerate_pairs L)"
  shows "(snd pair) \<in> set L"
  using assms
proof (induct "length L" arbitrary: L)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain h T where ht: "L = h#T"
    by (metis enumerate_pairs.cases enumerate_pairs.simps(1) in_set_member member_rec(2))
  then have eo: "pair \<in> set (map (Pair h) T) \<or> pair \<in> set (enumerate_pairs T)"
    using Suc by simp
  {assume *: "pair \<in> set (map (Pair h) T)"
    then have ?case
      using ht
      using imageE by auto
  } moreover {assume *: "pair \<in> set (enumerate_pairs T)"
    then have "snd pair \<in> set T"
      using Suc(1)[of T] ht
      using Suc.hyps(2) by fastforce
    then have ?case using ht
      by simp
  }
  ultimately show ?case using eo by blast
qed


lemma enum_pairs_bound:
  shows "\<forall> pair \<in> set (enum_pairs L). (snd pair) < length L"
  unfolding enum_pairs.simps enumerate_pairs.simps
proof(induct "length L" arbitrary: L)
  case 0
  then show ?case by simp
next
  case (Suc x)
  then have enum_L: "enumerate_pairs ([0..<length L]) =
    map (Pair 0) [1..<length L] @ enumerate_pairs [1..<length L]"
    using enumerate_pairs.simps(2)[of 0 "[1 ..< length L]"]
    by (metis One_nat_def upt_conv_Cons zero_less_Suc)
  then have "pair\<in>set (enumerate_pairs [0..<length L]) \<Longrightarrow> snd pair < length L" for pair
    using enum_pairs_bound_snd[of pair "[0..<length L]"]
    by auto
  then show ?case unfolding enum_pairs.simps by blast
qed

lemma WEST_simp_termination1_bound:
  fixes a::"nat"
  shows "a^3+a^2 < (a+1)^3"
proof-
  have cubed: "(a+1)^3 = a^3 + 3*a^2 + 3*a + 1"
  proof-
    have "(a+1)^3 = (a+1)*(a+1)*(a+1)"
      by algebra
    then show ?thesis
      by (simp add: add.commute add_mult_distrib2 mult.commute power2_eq_square power3_eq_cube)
  qed
  have "0 < 2*a^2 + 2*a + 1" by simp
  then have "a^3 + a^2 < a^3 + 3*a^2 + 3*a + 1" by simp
  then show ?thesis using cubed
    by simp
qed

lemma WEST_simp_termination1:
  fixes L::"WEST_regex"
  assumes "\<not> (idx_pairs \<noteq> enum_pairs L \<or> length idx_pairs \<le> i)"
  assumes "check_simp (L ! fst (idx_pairs ! i)) (L ! snd (idx_pairs ! i))"
  assumes "x = update_L L (idx_pairs ! i) num_vars"
  shows "((x, enum_pairs x, 0, num_vars), L, idx_pairs, i, num_vars)
       \<in> measure (\<lambda>(L, idx_list, i, num_vars). length L ^ 3 + length idx_list - i)"
proof-
  let ?i = "fst (idx_pairs ! i)"
  let ?j = "snd (idx_pairs ! i)"
  have i_le_j: "?i < ?j" using enum_pairs_fact assms
    by (metis linorder_le_less_linear nth_mem)
  have j_bound: "?j < length L"
    using assms(1) enum_pairs_bound[of L]
    by simp
  then have i_bound: "?i < (length L)-1"
    using i_le_j by auto
  have len_orsimp: "length [WEST_simp_trace (L ! ?i) (L ! ?j) num_vars] = 1"
    by simp
  have "length (remove_element_at_index ?j L) = length L - 1"
    using assms(3) j_bound by auto
  then have "length (remove_element_at_index ?i (remove_element_at_index ?j L)) = length L - 2"
    using assms(3) i_bound j_bound by simp
  then have length_x: "length x = (length L) - 1"
    using assms(3) len_orsimp
    unfolding update_L.simps[of L "idx_pairs ! i" num_vars]
    by (metis (no_types, lifting) add.commute add_diff_inverse_nat diff_diff_left gr_implies_not0 i_bound length_append less_one nat_1_add_1)
  have i_bound: "i < length idx_pairs" using assms by force

  { assume short_L: "length L = 0"
    then have ?thesis using assms
      using j_bound by linarith
  } moreover {
    assume long_L: "length L \<ge> 1"
    then have "length L - 1 \<ge> 0" by blast
    then have "(length L - 1) ^ 3 + (length L - 1) ^ 2 < length L ^ 3"
      using WEST_simp_termination1_bound[of "length L-1"]
      by (metis long_L ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add)
    then have "(length L - 1) ^ 3 + length (enumerate_pairs [0..<length x]) < length L ^ 3"
      using length_enumerate_pairs[of "[0..<length x]"] length_x by auto
    then have "length x ^ 3 + length (enumerate_pairs [0..<length x])
      < length L ^ 3 + length idx_pairs - i"
      using i_bound length_x by simp
    then have ?thesis by simp
  }
  ultimately show ?thesis by linarith
qed


function WEST_simp_helper:: "WEST_regex \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_simp_helper L idx_pairs i num_vars =
  (if (idx_pairs \<noteq> enum_pairs L \<or> i \<ge> length idx_pairs) then L else
    (if (check_simp (L!(fst (idx_pairs!i))) (L!(snd (idx_pairs!i)))) then
    (let newL = update_L L (idx_pairs!i) num_vars in
    WEST_simp_helper newL (enum_pairs newL) 0 num_vars)
    else WEST_simp_helper L idx_pairs (i+1) num_vars))"
  apply fast by blast
termination
  apply (relation "measure (\<lambda>(L , idx_list, i, num_vars). (length L^3 + length idx_list - i))")
    apply simp using WEST_simp_termination1 apply blast by auto

declare WEST_simp_helper.simps[simp del]

fun WEST_simp:: "WEST_regex \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_simp L num_vars =
  WEST_simp_helper L (enum_pairs L) 0 num_vars"

value "WEST_simp [[[S, S, One]],[[S, One, S]], [[S, S, Zero]]] 3"
value "WEST_simp [[[S, One]],[[One, S]], [[Zero, Zero]]] 2"
value "WEST_simp [[[One, One]],[[Zero, Zero]], [[One, Zero]], [[Zero, One]]] 2"


subsubsection \<open> AND and OR operations with WEST-simp \<close>

fun WEST_and_simp:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_and_simp L1 L2 num_vars = WEST_simp (WEST_and L1 L2) num_vars"

fun WEST_or_simp:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_or_simp L1 L2 num_vars = WEST_simp (L1@L2) num_vars"

subsubsection \<open> Useful Helper Functions \<close>

fun arbitrary_state::"nat \<Rightarrow> state_regex"
  where "arbitrary_state num_vars = map (\<lambda> k. S) [0 ..< num_vars]"

fun arbitrary_trace::"nat \<Rightarrow> nat \<Rightarrow> trace_regex"
  where "arbitrary_trace num_vars num_pad = map (\<lambda> k. (arbitrary_state num_vars)) [0 ..< num_pad]"

fun shift:: "WEST_regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "shift traceList num_vars num_pad = map (\<lambda> trace. (arbitrary_trace num_vars num_pad)@trace) traceList"

fun pad:: "trace_regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> trace_regex"
  where "pad trace num_vars num_pad = trace@(arbitrary_trace num_vars num_pad)"


subsubsection \<open> WEST Temporal Operations \<close>

fun WEST_global:: "WEST_regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WEST_regex"
where "WEST_global L a b num_vars = (
if (a = b) then (shift L num_vars a)
   else ( if (a < b) then (WEST_and_simp (shift L num_vars b)
                 (WEST_global L a (b-1) num_vars) num_vars)
      else []))"


fun WEST_future:: "WEST_regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_future L a b num_vars = (
  if (a = b)
  then (shift L num_vars a)
  else (
    if (a < b)
    then WEST_or_simp (shift L num_vars b) (WEST_future L a (b-1) num_vars) num_vars
    else []))"


fun WEST_until:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow> nat \<Rightarrow>
                  nat \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_until L_\<phi> L_\<psi> a b num_vars = (
  if (a=b)
  then (WEST_global L_\<psi> a a num_vars)
  else (
    if (a < b)
    then WEST_or_simp (WEST_until L_\<phi> L_\<psi> a (b-1) num_vars)
         (WEST_and_simp (WEST_global L_\<phi> a (b-1) num_vars)
                    (WEST_global L_\<psi> b b num_vars) num_vars) num_vars
    else []))"


fun WEST_release_helper:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow>
                   nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_release_helper L_\<phi> L_\<psi> a ub num_vars = (
  if (a=ub)
  then (WEST_and_simp (WEST_global L_\<phi> a a num_vars) (WEST_global L_\<psi> a a num_vars) num_vars)
  else (
    if (a < ub)
    then WEST_or_simp (WEST_release_helper L_\<phi> L_\<psi> a (ub-1) num_vars)
         (WEST_and_simp (WEST_global L_\<psi> a ub num_vars)
                    (WEST_global L_\<phi> ub ub num_vars) num_vars) num_vars
    else []))"

fun WEST_release:: "WEST_regex \<Rightarrow> WEST_regex \<Rightarrow> nat
                    \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_release L_\<phi> L_\<psi> a b num_vars = (
  if (b > a)
  then (WEST_or_simp (WEST_global L_\<psi> a b num_vars) (WEST_release_helper L_\<phi> L_\<psi> a (b-1) num_vars) num_vars)
  else (WEST_global L_\<psi> a b num_vars))"


subsubsection \<open> WEST recursive reg Function \<close>
lemma exhaustive:
  shows "\<And>x:: nat mltl \<times> nat. \<And>P::bool. (\<And>num_vars::nat. x = (True_mltl, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>num_vars::nat. x = (False_mltl, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>p num_vars::nat. x = (Prop_mltl p, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>p num_vars::nat. x = (Not_mltl (Prop_mltl p), num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> num_vars. x = (Or_mltl \<phi> \<psi>, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> num_vars. x = (And_mltl \<phi> \<psi>, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> a b num_vars. x = (Future_mltl \<phi> a b, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> a b num_vars. x = (Global_mltl \<phi> a b, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> a b num_vars. x = (Until_mltl \<phi> \<psi> a b, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> a b num_vars. x = (Release_mltl \<phi> \<psi> a b, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>num_vars. x = (Not_mltl True_mltl, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>num_vars. x = (Not_mltl False_mltl, num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> num_vars. x = (Not_mltl (And_mltl \<phi> \<psi>), num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> num_vars. x = (Not_mltl (Or_mltl \<phi> \<psi>), num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> a b num_vars. x = (Not_mltl (Future_mltl \<phi> a b), num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> a b num_vars. x = (Not_mltl (Global_mltl \<phi> a b), num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> a b num_vars. x = (Not_mltl (Until_mltl \<phi> \<psi> a b), num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> \<psi> a b num_vars. x = (Not_mltl (Release_mltl \<phi> \<psi> a b), num_vars) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<phi> num_vars. x = (Not_mltl (Not_mltl \<phi>), num_vars) \<Longrightarrow> P) \<Longrightarrow> P"
proof -
  fix x::"nat mltl \<times> nat"
  fix P:: "bool"
  assume t: "(\<And>num_vars::nat. x = (True_mltl, num_vars) \<Longrightarrow> P)"
  assume fa: "(\<And>num_vars::nat. x = (False_mltl, num_vars) \<Longrightarrow> P)"
  assume p: "(\<And>p num_vars::nat. x = (Prop_mltl p, num_vars) \<Longrightarrow> P) "
  assume n1: "(\<And>p num_vars::nat. x = (Not_mltl (Prop_mltl p), num_vars) \<Longrightarrow> P) "
  assume o: "(\<And>\<phi> \<psi> num_vars. x = (Or_mltl \<phi> \<psi>, num_vars) \<Longrightarrow> P) "
  assume a: "(\<And>\<phi> \<psi> num_vars. x = (And_mltl \<phi> \<psi>, num_vars) \<Longrightarrow> P) "
  assume f: "(\<And>\<phi> a b num_vars. x = (Future_mltl \<phi> a b, num_vars) \<Longrightarrow> P) "
  assume g: "(\<And>\<phi> a b num_vars. x = (Global_mltl \<phi> a b, num_vars) \<Longrightarrow> P) "
  assume u: "(\<And>\<phi> \<psi> a b num_vars. x = (Until_mltl \<phi> \<psi> a b, num_vars) \<Longrightarrow> P) "
  assume r: "(\<And>\<phi> \<psi> a b num_vars. x = (Release_mltl \<phi> \<psi> a b, num_vars) \<Longrightarrow> P) "
  assume n2: "(\<And>num_vars. x = (Not_mltl True_mltl, num_vars) \<Longrightarrow> P) "
  assume n3: "(\<And>num_vars. x = (Not_mltl False_mltl, num_vars) \<Longrightarrow> P) "
  assume n4: "(\<And>\<phi> \<psi> num_vars. x = (Not_mltl (And_mltl \<phi> \<psi>), num_vars) \<Longrightarrow> P) "
  assume n5: "(\<And>\<phi> \<psi> num_vars. x = (Not_mltl (Or_mltl \<phi> \<psi>), num_vars) \<Longrightarrow> P) "
  assume n6: "(\<And>\<phi> a b num_vars. x = (Not_mltl (Future_mltl \<phi> a b), num_vars) \<Longrightarrow> P) "
  assume n7: "(\<And>\<phi> a b num_vars. x = (Not_mltl (Global_mltl \<phi> a b), num_vars) \<Longrightarrow> P) "
  assume n8: "(\<And>\<phi> \<psi> a b num_vars. x = (Not_mltl (Until_mltl \<phi> \<psi> a b), num_vars) \<Longrightarrow> P) "
  assume n9: "(\<And>\<phi> \<psi> a b num_vars. x = (Not_mltl (Release_mltl \<phi> \<psi> a b), num_vars) \<Longrightarrow> P) "
  assume n10: "(\<And>\<phi> num_vars. x = (Not_mltl (Not_mltl \<phi>), num_vars) \<Longrightarrow> P)"
  show "P" proof (cases "fst x")
    case True_mltl
    then show ?thesis using t
      by (metis eq_fst_iff)
  next
    case False_mltl
    then show ?thesis using fa eq_fst_iff by metis
  next
    case (Prop_mltl p)
    then show ?thesis using p
      by (metis prod.collapse)
  next
    case (Not_mltl \<phi>)
    then have fst_x: "fst x = Not_mltl \<phi>"
      by auto
    then show ?thesis proof (cases \<phi>)
      case True_mltl
      then show ?thesis using n2
        by (metis Not_mltl split_pairs)
    next
      case False_mltl
      then show ?thesis using n3
        by (metis Not_mltl prod.collapse)
    next
      case (Prop_mltl p)
      then show ?thesis using n1
        by (metis Not_mltl split_pairs)
    next
      case (Not_mltl \<phi>1)
      then show ?thesis using n10 fst_x
        by (metis prod.collapse)
    next
      case (And_mltl \<phi>1 \<phi>2)
      then show ?thesis
        by (metis Not_mltl n4 prod.collapse)
    next
      case (Or_mltl \<phi>1 \<phi>2)
      then show ?thesis using n5 Not_mltl
        by (metis prod.collapse)
    next
      case (Future_mltl a b \<phi>1)
      then show ?thesis  using n6 Not_mltl
        by (metis prod.collapse)
    next
      case (Global_mltl a b \<phi>1)
      then show ?thesis  using n7 Not_mltl
        by (metis prod.collapse)
    next
      case (Until_mltl \<phi>1 a b \<phi>2)
      then show ?thesis  using n8 Not_mltl
        by (metis prod.collapse)
    next
      case (Release_mltl \<phi>1 a b \<phi>2)
      then show ?thesis  using n9 Not_mltl
        by (metis prod.collapse)
    qed
  next
    case (And_mltl \<phi>1 \<phi>2)
    then show ?thesis using a
      by (metis prod.collapse)
  next
    case (Or_mltl \<phi>1 \<phi>2)
    then show ?thesis using o
      by (metis prod.collapse)
  next
    case (Future_mltl a b \<phi>1)
    then show ?thesis using f
      by (metis split_pairs)
  next
    case (Global_mltl a b \<phi>1)
    then show ?thesis using g
      by (metis prod.collapse)
  next
    case (Until_mltl \<phi>1 a b \<phi>2)
    then show ?thesis using u
      by (metis split_pairs)
  next
    case (Release_mltl \<phi>1 a b \<phi>2)
    then show ?thesis using r
      by (metis split_pairs)
  qed
qed


fun WEST_termination_measure:: "(nat) mltl \<Rightarrow> nat"
  where "WEST_termination_measure True\<^sub>m = 1"
  | "WEST_termination_measure (Not\<^sub>m True\<^sub>m) = 4"
  | "WEST_termination_measure False\<^sub>m = 1"
  | "WEST_termination_measure (Not\<^sub>m False\<^sub>m) = 4"
  | "WEST_termination_measure (Prop\<^sub>m (p)) = 1"
  | "WEST_termination_measure (Not\<^sub>m (Prop\<^sub>m (p))) = 4"
  | "WEST_termination_measure (\<phi> Or\<^sub>m \<psi>) = 1 + (WEST_termination_measure \<phi>) + (WEST_termination_measure \<psi>)"
  | "WEST_termination_measure (\<phi> And\<^sub>m \<psi>) = 1 + (WEST_termination_measure \<phi>) + (WEST_termination_measure \<psi>)"
  | "WEST_termination_measure (F\<^sub>m [a,b] \<phi>) = 1 + (WEST_termination_measure \<phi>)"
  | "WEST_termination_measure (G\<^sub>m [a,b] \<phi>) = 1 + (WEST_termination_measure \<phi>)"
  | "WEST_termination_measure (\<phi> U\<^sub>m[a,b] \<psi>) = 1 + (WEST_termination_measure \<phi>) + (WEST_termination_measure \<psi>)"
  | "WEST_termination_measure (\<phi> R\<^sub>m[a,b] \<psi>) = 1 + (WEST_termination_measure \<phi>) + (WEST_termination_measure \<psi>)"
  | "WEST_termination_measure (Not\<^sub>m (\<phi> Or\<^sub>m \<psi>)) = 1 + 3 * (WEST_termination_measure (\<phi> Or\<^sub>m \<psi>))"
  | "WEST_termination_measure (Not\<^sub>m (\<phi> And\<^sub>m \<psi>)) = 1 + 3 * (WEST_termination_measure (\<phi> And\<^sub>m \<psi>))"
  | "WEST_termination_measure (Not\<^sub>m (F\<^sub>m[a,b] \<phi>)) = 1 + 3 * (WEST_termination_measure (F\<^sub>m[a,b] \<phi>))"
  | "WEST_termination_measure (Not\<^sub>m (G\<^sub>m[a,b] \<phi>)) = 1 + 3 * (WEST_termination_measure (G\<^sub>m[a,b] \<phi>))"
  | "WEST_termination_measure (Not\<^sub>m (\<phi> U\<^sub>m[a,b] \<psi>)) = 1 + 3 * (WEST_termination_measure (\<phi> U\<^sub>m[a,b] \<psi>))"
  | "WEST_termination_measure (Not\<^sub>m (\<phi> R\<^sub>m[a,b] \<psi>)) = 1 + 3 * (WEST_termination_measure (\<phi> R\<^sub>m[a,b] \<psi>))"
  | "WEST_termination_measure (Not\<^sub>m (Not\<^sub>m \<phi>)) = 1 + 3 * (WEST_termination_measure (Not\<^sub>m \<phi>))"

lemma WEST_termination_measure_not:
  fixes \<phi>::"(nat) mltl"
  shows "WEST_termination_measure (Not_mltl \<phi>) = 1 + 3 * (WEST_termination_measure \<phi>)"
  apply (induction \<phi>) by simp_all


function WEST_reg_aux:: "(nat) mltl \<Rightarrow> nat \<Rightarrow> WEST_regex"
  where "WEST_reg_aux True\<^sub>m num_vars = [[(map (\<lambda> j. S) [0 ..< num_vars])]]"
  | "WEST_reg_aux False\<^sub>m num_vars = []"
  | "WEST_reg_aux (Prop\<^sub>m (p)) num_vars = [[(map (\<lambda> j. (if (p=j) then One else S)) [0 ..< num_vars])]]"
  | "WEST_reg_aux (Not\<^sub>m (Prop\<^sub>m (p))) num_vars = [[(map (\<lambda> j. (if (p=j) then Zero else S)) [0 ..< num_vars])]]"
  | "WEST_reg_aux (\<phi> Or\<^sub>m \<psi>) num_vars = WEST_or_simp (WEST_reg_aux \<phi> num_vars) (WEST_reg_aux \<psi> num_vars) num_vars"
  | "WEST_reg_aux (\<phi> And\<^sub>m \<psi>) num_vars = (WEST_and_simp (WEST_reg_aux \<phi> num_vars) (WEST_reg_aux \<psi> num_vars) num_vars)"
  | "WEST_reg_aux (F\<^sub>m[a,b] \<phi>) num_vars = (WEST_future (WEST_reg_aux \<phi> num_vars) a b num_vars)"
  | "WEST_reg_aux (G\<^sub>m[a,b] \<phi>) num_vars = (WEST_global (WEST_reg_aux \<phi> num_vars) a b num_vars)"
  | "WEST_reg_aux (\<phi> U\<^sub>m[a,b] \<psi>) num_vars = (WEST_until (WEST_reg_aux \<phi> num_vars) (WEST_reg_aux \<psi> num_vars) a b num_vars)"
  | "WEST_reg_aux (\<phi> R\<^sub>m[a,b] \<psi>) num_vars = WEST_release (WEST_reg_aux \<phi> num_vars) (WEST_reg_aux \<psi> num_vars) a b num_vars"
  | "WEST_reg_aux (Not\<^sub>m True\<^sub>m) num_vars = WEST_reg_aux False\<^sub>m num_vars"
  | "WEST_reg_aux (Not\<^sub>m False\<^sub>m) num_vars = WEST_reg_aux True\<^sub>m num_vars"
  | "WEST_reg_aux (Not\<^sub>m (\<phi> And\<^sub>m \<psi>)) num_vars = WEST_reg_aux ((Not\<^sub>m \<phi>) Or\<^sub>m (Not\<^sub>m \<psi>)) num_vars"
  | "WEST_reg_aux (Not\<^sub>m (\<phi> Or\<^sub>m \<psi>)) num_vars = WEST_reg_aux ((Not\<^sub>m \<phi>) And\<^sub>m (Not\<^sub>m \<psi>)) num_vars"
  | "WEST_reg_aux (Not\<^sub>m (F\<^sub>m[a,b] \<phi>)) num_vars = WEST_reg_aux (G\<^sub>m[a,b] (Not\<^sub>m \<phi>)) num_vars"
  | "WEST_reg_aux (Not\<^sub>m (G\<^sub>m[a,b] \<phi>)) num_vars = WEST_reg_aux (F\<^sub>m[a,b] (Not\<^sub>m \<phi>)) num_vars"
  | "WEST_reg_aux (Not\<^sub>m (\<phi> U\<^sub>m[a,b] \<psi>)) num_vars = WEST_reg_aux ((Not\<^sub>m \<phi>) R\<^sub>m[a,b] (Not\<^sub>m \<psi>)) num_vars"
  | "WEST_reg_aux (Not\<^sub>m (\<phi> R\<^sub>m[a,b] \<psi>)) num_vars = WEST_reg_aux ((Not\<^sub>m \<phi>) U\<^sub>m[a,b] (Not\<^sub>m \<psi>)) num_vars"
  | "WEST_reg_aux (Not\<^sub>m (Not\<^sub>m \<phi>)) num_vars = WEST_reg_aux \<phi> num_vars"
   using exhaustive convert_nnf.cases using exhaustive apply (smt (z3)) (* May take a second to load *)
  defer apply blast apply simp_all .
termination
  apply (relation "measure (\<lambda>(F,num_vars). (WEST_termination_measure F))")
  using WEST_termination_measure_not by simp_all


fun WEST_num_vars:: "(nat) mltl \<Rightarrow> nat"
  where "WEST_num_vars True\<^sub>m = 1"
  | "WEST_num_vars False\<^sub>m = 1"
  | "WEST_num_vars (Prop\<^sub>m (p)) = p+1"
  | "WEST_num_vars (Not\<^sub>m \<phi>) = WEST_num_vars \<phi>"
  | "WEST_num_vars (\<phi> And\<^sub>m \<psi>) = Max {(WEST_num_vars \<phi>), (WEST_num_vars \<psi>)}"
  | "WEST_num_vars (\<phi> Or\<^sub>m \<psi>) = Max {(WEST_num_vars \<phi>), (WEST_num_vars \<psi>)}"
  | "WEST_num_vars (F\<^sub>m[a,b] \<phi>) = WEST_num_vars \<phi>"
  | "WEST_num_vars (G\<^sub>m[a,b] \<phi>) = WEST_num_vars \<phi>"
  | "WEST_num_vars (\<phi> U\<^sub>m[a,b] \<psi>) = Max {(WEST_num_vars \<phi>), (WEST_num_vars \<psi>)}"
  | "WEST_num_vars (\<phi> R\<^sub>m[a,b] \<psi>) = Max {(WEST_num_vars \<phi>), (WEST_num_vars \<psi>)}"


fun WEST_reg:: "(nat) mltl \<Rightarrow> WEST_regex"
  where "WEST_reg F = (let nnf_F = convert_nnf F in WEST_reg_aux nnf_F (WEST_num_vars F))"

subsubsection \<open> Adding padding \<close>
fun pad_WEST_reg:: "nat mltl \<Rightarrow> WEST_regex"
  where "pad_WEST_reg \<phi> = (let unpadded = WEST_reg \<phi> in
                               (let complen = complen_mltl \<phi> in
                                (let num_vars = WEST_num_vars \<phi> in
                                (map (\<lambda> L. (if (length L < complen)then (pad L num_vars (complen-(length L))) else L))) unpadded)))"

fun simp_pad_WEST_reg:: "nat mltl \<Rightarrow> WEST_regex"
  where "simp_pad_WEST_reg \<phi> = WEST_simp (pad_WEST_reg \<phi>) (WEST_num_vars \<phi>)"


section \<open> Some examples and Code Export \<close>

text \<open> Base cases \<close>
value "WEST_reg True\<^sub>m"
value "WEST_reg False\<^sub>m"
value "WEST_reg (Prop\<^sub>m (1))"
value "WEST_reg (Not\<^sub>m (Prop\<^sub>m (0)))"

text \<open> Test cases for recursion \<close>
value "WEST_reg ((Not\<^sub>m (Prop\<^sub>m (0))) And\<^sub>m (Prop\<^sub>m (1)))"
value "WEST_reg (F\<^sub>m[0,2] (Prop\<^sub>m (1)))"
value "WEST_reg ((Not\<^sub>m (Prop\<^sub>m (0))) Or\<^sub>m (Prop\<^sub>m (0)))"

value "pad_WEST_reg ((Prop\<^sub>m (0)) U\<^sub>m[0,2] (Prop\<^sub>m (0)))"
value "simp_pad_WEST_reg ((Prop_mltl 0) U\<^sub>m[0,2] (Prop_mltl 0))"

export_code WEST_reg in Haskell module_name WEST
export_code simp_pad_WEST_reg in Haskell module_name WEST_simp_pad

end