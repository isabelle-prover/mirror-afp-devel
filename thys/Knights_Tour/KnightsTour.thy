(* Author: Lukas Koller *)

theory KnightsTour
  imports Main
begin

section \<open>Introduction and Definitions\<close>

text \<open>A Knight's path is a sequence of moves on a chessboard s.t.\ every step in sequence is a 
valid move for a Knight and that the Knight visits every square on the boards exactly once. 
A Knight is a chess figure that is only able to move two squares vertically and one square 
horizontally or two squares horizontally and one square vertically. Finding a Knight's path is an 
instance of the Hamiltonian Path Problem. A Knight's circuit is a Knight's path, where additionally 
the Knight can move from the last square to the first square of the path, forming a loop.

Cull and De Curtins \<^cite>\<open>"cull_decurtins_1987"\<close> prove the existence of a Knight's path on a \<open>n\<times>m\<close>-board for
sufficiently large \<open>n\<close> and \<open>m\<close>. The main idea for the proof is to inductivly construct a Knight's 
path for the \<open>n\<times>m\<close>-board from a few pre-computed Knight's paths for small boards, i.e. \<open>5\<times>5\<close>, 
\<open>8\<times>6\<close>, ..., \<open>8\<times>9\<close>. The paths for small boards are transformed (i.e. transpose, mirror, translate) 
and concatenated to create paths for larger boards.

While formalizing the proofs I discovered two mistakes in the original proof in 
\<^cite>\<open>"cull_decurtins_1987"\<close>: (i) the pre-computed path for the \<open>6\<times>6\<close>-board that ends in 
the upper-left (in Figure 2) and (ii) the pre-computed path for the \<open>8\<times>8\<close>-board that ends in 
the upper-left (in Figure 5) are incorrect: on the \<open>6\<times>6\<close>-board the Knight cannot step 
from square 26 to square 27; in the \<open>8\<times>8\<close>-board the Knight cannot step from square 27 to 
square 28. In this formalization I have replaced the two incorrect paths with correct paths.\<close>

text \<open>A square on a board is identified by its coordinates.\<close>
type_synonym square = "int \<times> int"
text \<open>A board is represented as a set of squares. Note, that this allows boards to have an 
arbitrary shape and do not necessarily need to be rectangular.\<close>
type_synonym board = "square set"

text \<open>A (rectangular) \<open>(n\<times>m)\<close>-board is the set of all squares \<open>(i,j)\<close> where \<open>1 \<le> i \<le> n\<close> 
and \<open>1 \<le> j \<le> m\<close>. \<open>(1,1)\<close> is the lower-left corner, and \<open>(n,m)\<close> is the upper-right corner.\<close>
definition board :: "nat \<Rightarrow> nat \<Rightarrow> board" where
  "board n m = {(i,j) |i j. 1 \<le> i \<and> i \<le> int n \<and> 1 \<le> j \<and> j \<le> int m}"

text \<open>A path is a sequence of steps on a board. A path is represented by the list of visited 
squares on the board. Each square on the \<open>(n\<times>m)\<close>-board is identified by its coordinates \<open>(i,j)\<close>.\<close>
type_synonym path = "square list"

text \<open>A Knight can only move two squares vertically and one square horizontally or two squares 
horizontally and one square vertically. Thus, a knight at position \<open>(i,j)\<close> can only move 
to \<open>(i\<plusminus>1,j\<plusminus>2)\<close> or \<open>(i\<plusminus>2,j\<plusminus>1)\<close>.\<close>
definition valid_step :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "valid_step s\<^sub>i s\<^sub>j \<equiv> (case s\<^sub>i of (i,j) \<Rightarrow> s\<^sub>j \<in> {(i+1,j+2),(i-1,j+2),(i+1,j-2),(i-1,j-2),
                                                (i+2,j+1),(i-2,j+1),(i+2,j-1),(i-2,j-1)})"

text \<open>Now we define an inductive predicate that characterizes a Knight's path. A square \<open>s\<^sub>i\<close> can be
pre-pended to a current Knight's path \<open>s\<^sub>j#ps\<close> if (i) there is a valid step from the square \<open>s\<^sub>i\<close> to 
the first square \<open>s\<^sub>j\<close> of the current path and (ii) the square \<open>s\<^sub>i\<close> has not been visited yet.\<close>
inductive knights_path :: "board \<Rightarrow> path \<Rightarrow> bool" where
  "knights_path {s\<^sub>i} [s\<^sub>i]"
| "s\<^sub>i \<notin> b \<Longrightarrow> valid_step s\<^sub>i s\<^sub>j \<Longrightarrow> knights_path b (s\<^sub>j#ps) \<Longrightarrow> knights_path (b \<union> {s\<^sub>i}) (s\<^sub>i#s\<^sub>j#ps)"

code_pred knights_path .

text \<open>A sequence is a Knight's circuit iff the sequence if a Knight's path and there is a valid 
step from the last square to the first square.\<close>
definition "knights_circuit b ps \<equiv> (knights_path b ps \<and> valid_step (last ps) (hd ps))"

section \<open>Executable Checker for a Knight's Path\<close>

text \<open>This section gives the implementation and correctness-proof for an executable checker for a
knights-path w.r.t.\ the definition @{const knights_path}.\<close>

subsection \<open>Implementation of an Executable Checker\<close>

fun row_exec :: "nat \<Rightarrow> int set" where
  "row_exec 0 = {}"
| "row_exec m = insert (int m) (row_exec (m-1))"

fun board_exec_aux :: "nat \<Rightarrow> int set \<Rightarrow> board" where
  "board_exec_aux 0 M = {}"  
| "board_exec_aux k M = {(int k,j) |j. j \<in> M} \<union> board_exec_aux (k-1) M"

text \<open>Compute a board.\<close>
fun board_exec :: "nat \<Rightarrow> nat \<Rightarrow> board" where
  "board_exec n m = board_exec_aux n (row_exec m)"

fun step_checker :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "step_checker (i,j) (i',j') = 
    ((i+1,j+2) = (i',j') \<or> (i-1,j+2) = (i',j') \<or> (i+1,j-2) = (i',j') \<or> (i-1,j-2) = (i',j') 
     \<or> (i+2,j+1) = (i',j') \<or> (i-2,j+1) = (i',j') \<or> (i+2,j-1) = (i',j') \<or> (i-2,j-1) = (i',j'))"

fun path_checker :: "board \<Rightarrow> path \<Rightarrow> bool" where
  "path_checker b [] = False"
| "path_checker b [s\<^sub>i] = ({s\<^sub>i} = b)"
| "path_checker b (s\<^sub>i#s\<^sub>j#ps) = (s\<^sub>i \<in> b \<and> step_checker s\<^sub>i s\<^sub>j \<and> path_checker (b - {s\<^sub>i}) (s\<^sub>j#ps))"

fun circuit_checker :: "board \<Rightarrow> path \<Rightarrow> bool" where
  "circuit_checker b ps = (path_checker b ps \<and> step_checker (last ps) (hd ps))"

subsection \<open>Correctness Proof of the Executable Checker\<close>

lemma row_exec_leq: "j \<in> row_exec m \<longleftrightarrow> 1 \<le> j \<and> j \<le> int m"
  by (induction m) auto

lemma board_exec_aux_leq_mem: "(i,j) \<in> board_exec_aux k M \<longleftrightarrow> 1 \<le> i \<and> i \<le> int k \<and> j \<in> M"
  by (induction k M rule: board_exec_aux.induct) auto

lemma board_exec_leq: "(i,j) \<in> board_exec n m \<longleftrightarrow> 1 \<le> i \<and> i \<le> int n \<and> 1 \<le> j \<and> j \<le> int m"
  using board_exec_aux_leq_mem row_exec_leq by auto

lemma board_exec_correct: "board n m = board_exec n m"
  unfolding board_def using board_exec_leq by auto

lemma step_checker_correct: "step_checker s\<^sub>i s\<^sub>j \<longleftrightarrow> valid_step s\<^sub>i s\<^sub>j"
proof
  assume "step_checker s\<^sub>i s\<^sub>j"
  then show "valid_step s\<^sub>i s\<^sub>j"
    unfolding valid_step_def 
    apply (cases s\<^sub>i)
    apply (cases s\<^sub>j)
    apply auto
    done
next
  assume assms: "valid_step s\<^sub>i s\<^sub>j"
  then show "step_checker s\<^sub>i s\<^sub>j"
    unfolding valid_step_def by auto
qed

lemma step_checker_rev: "step_checker (i,j) (i',j') \<Longrightarrow> step_checker (i',j') (i,j)"
  apply (simp only: step_checker.simps)
  by (elim disjE) auto

lemma knights_path_intro_rev: 
  assumes "s\<^sub>i \<in> b" "valid_step s\<^sub>i s\<^sub>j" "knights_path (b - {s\<^sub>i}) (s\<^sub>j#ps)" 
  shows "knights_path b (s\<^sub>i#s\<^sub>j#ps)"
  using assms
proof -
  assume assms: "s\<^sub>i \<in> b" "valid_step s\<^sub>i s\<^sub>j" "knights_path (b - {s\<^sub>i}) (s\<^sub>j#ps)"
  then have "s\<^sub>i \<notin> (b - {s\<^sub>i})" "b - {s\<^sub>i} \<union> {s\<^sub>i} = b"
    by auto
  then show ?thesis
    using assms knights_path.intros(2)[of s\<^sub>i "b - {s\<^sub>i}"] by auto
qed

text \<open>Final correctness corollary for the executable checker @{const path_checker}.\<close>
lemma path_checker_correct: "path_checker b ps \<longleftrightarrow> knights_path b ps"
proof
  assume "path_checker b ps"
  then show "knights_path b ps"
  proof (induction rule: path_checker.induct)
    case (3 s\<^sub>i s\<^sub>j xs b)
    then show ?case using step_checker_correct knights_path_intro_rev by auto
  qed (auto intro: knights_path.intros)
next
  assume "knights_path b ps"
  then show "path_checker b ps"                  
    using step_checker_correct 
    by (induction rule: knights_path.induct) (auto elim: knights_path.cases)
qed

corollary knights_path_exec_simp: "knights_path (board n m) ps \<longleftrightarrow> path_checker (board_exec n m) ps"
  using board_exec_correct path_checker_correct[symmetric] by simp

lemma circuit_checker_correct: "circuit_checker b ps \<longleftrightarrow> knights_circuit b ps"
  unfolding knights_circuit_def using path_checker_correct step_checker_correct by auto

corollary knights_circuit_exec_simp: 
  "knights_circuit (board n m) ps \<longleftrightarrow> circuit_checker (board_exec n m) ps"
  using board_exec_correct circuit_checker_correct[symmetric] by simp

section \<open>Basic Properties of @{const knights_path} and @{const knights_circuit}\<close>

lemma board_leq_subset: "n\<^sub>1 \<le> n\<^sub>2 \<and> m\<^sub>1 \<le> m\<^sub>2 \<Longrightarrow> board n\<^sub>1 m\<^sub>1 \<subseteq> board n\<^sub>2 m\<^sub>2"
  unfolding board_def by auto

lemma finite_row_exec: "finite (row_exec m)"
  by (induction m) auto

lemma finite_board_exec_aux: "finite M \<Longrightarrow> finite (board_exec_aux n M)"
  by (induction n) auto

lemma board_finite: "finite (board n m)"
  using finite_board_exec_aux finite_row_exec by (simp only: board_exec_correct) auto

lemma card_row_exec: "card (row_exec m) = m"
proof (induction m)
  case (Suc m)
  have "int (Suc m) \<notin> row_exec m"
    using row_exec_leq by auto
  then have "card (insert (int (Suc m)) (row_exec m)) = 1 + card (row_exec m)"
    using card_Suc_eq by (metis Suc plus_1_eq_Suc row_exec.simps(1))
  then have "card (row_exec (Suc m)) = 1 + card (row_exec m)"
    by auto
  then show ?case using Suc.IH by auto 
qed auto

lemma set_comp_ins: 
  "{(k,j) |j. j \<in> insert x M} = insert (k,x) {(k,j) |j. j \<in> M}" (is "?Mi = ?iM")
proof
  show "?Mi \<subseteq> ?iM"
  proof
    fix y assume "y \<in> ?Mi"
    then obtain j where [simp]: "y = (k,j)" and "j \<in> insert x M" by blast
    then have "j = x \<or> j \<in> M" by auto
    then show "y \<in> ?iM" by (elim disjE) auto
  qed
next
  show "?iM \<subseteq> ?Mi"
  proof
    fix y assume "y \<in> ?iM"
    then obtain j where [simp]: "y = (k,j)" and "j \<in> insert x M" by blast
    then have "j = x \<or> j \<in> M" by auto
    then show "y \<in> ?Mi" by (elim disjE) auto
  qed
qed

lemma finite_card_set_comp: "finite M \<Longrightarrow> card {(k,j) |j. j \<in> M} = card M"
proof (induction M rule: finite_induct)
  case (insert x M)
  then show ?case using set_comp_ins[of k x M] by auto
qed auto

lemma card_board_exec_aux: "finite M \<Longrightarrow> card (board_exec_aux k M) = k * card M"
proof (induction k)
  case (Suc k)
  let ?M'="{(int (Suc k),j) |j. j \<in> M}"
  let ?rec_k="board_exec_aux k M"

  have finite: "finite ?M'" "finite ?rec_k"
    using Suc finite_board_exec_aux by auto
  then have card_Un_simp: "card (?M' \<union> ?rec_k) = card ?M' + card ?rec_k"
    using board_exec_aux_leq_mem card_Un_Int[of ?M' ?rec_k] by auto
  
  have card_M: "card ?M' = card M"
    using Suc finite_card_set_comp by auto
  
  have "card (board_exec_aux (Suc k) M) = card ?M' + card ?rec_k"
    using card_Un_simp by auto
  also have "... = card M + k * card M"
    using Suc card_M by auto
  also have "... = (Suc k) * card M"
    by auto
  finally show ?case .
qed auto

lemma card_board: "card (board n m) = n * m"
proof -
  have "card (board n m) = card (board_exec_aux n (row_exec m))"
    using board_exec_correct by auto
  also have "... = n * m"
    using card_row_exec card_board_exec_aux finite_row_exec by auto
  finally show ?thesis .
qed

lemma knights_path_board_non_empty: "knights_path b ps \<Longrightarrow> b \<noteq> {}"
  by (induction arbitrary: ps rule: knights_path.induct) auto

lemma knights_path_board_m_n_geq_1: "knights_path (board n m) ps \<Longrightarrow> min n m \<ge> 1"
  unfolding board_def using knights_path_board_non_empty by fastforce

lemma knights_path_non_nil: "knights_path b ps \<Longrightarrow> ps \<noteq> []"
  by (induction arbitrary: b rule: knights_path.induct) auto

lemma knights_path_set_eq: "knights_path b ps \<Longrightarrow> set ps = b"
  by (induction rule: knights_path.induct) auto

lemma knights_path_subset: 
  "knights_path b\<^sub>1 ps\<^sub>1 \<Longrightarrow> knights_path b\<^sub>2 ps\<^sub>2 \<Longrightarrow> set ps\<^sub>1 \<subseteq> set ps\<^sub>2 \<longleftrightarrow> b\<^sub>1 \<subseteq> b\<^sub>2"
  using knights_path_set_eq by auto

lemma knights_path_board_unique: "knights_path b\<^sub>1 ps \<Longrightarrow> knights_path b\<^sub>2 ps \<Longrightarrow> b\<^sub>1 = b\<^sub>2"
  using knights_path_set_eq by auto

lemma valid_step_neq: "valid_step s\<^sub>i s\<^sub>j \<Longrightarrow> s\<^sub>i \<noteq> s\<^sub>j"
  unfolding valid_step_def by auto

lemma valid_step_non_transitive: "valid_step s\<^sub>i s\<^sub>j \<Longrightarrow> valid_step s\<^sub>j s\<^sub>k \<Longrightarrow> \<not>valid_step s\<^sub>i s\<^sub>k"
proof -
  assume assms: "valid_step s\<^sub>i s\<^sub>j" "valid_step s\<^sub>j s\<^sub>k"
  obtain i\<^sub>i j\<^sub>i i\<^sub>j j\<^sub>j i\<^sub>k j\<^sub>k where [simp]: "s\<^sub>i = (i\<^sub>i,j\<^sub>i)" "s\<^sub>j = (i\<^sub>j,j\<^sub>j)" "s\<^sub>k = (i\<^sub>k,j\<^sub>k)" by force
  then have "step_checker (i\<^sub>i,j\<^sub>i) (i\<^sub>j,j\<^sub>j)" "step_checker (i\<^sub>j,j\<^sub>j) (i\<^sub>k,j\<^sub>k)" 
    using assms step_checker_correct by auto
  then show "\<not>valid_step s\<^sub>i s\<^sub>k"
    apply (simp add: step_checker_correct[symmetric])
    apply (elim disjE)
    apply auto
    done
qed

lemma knights_path_distinct: "knights_path b ps \<Longrightarrow> distinct ps"
proof (induction rule: knights_path.induct)
  case (2 s\<^sub>i b s\<^sub>j ps)
  then have "s\<^sub>i \<notin> set (s\<^sub>j # ps)"
    using knights_path_set_eq valid_step_neq by blast
  then show ?case using 2 by auto
qed auto

lemma knights_path_length: "knights_path b ps \<Longrightarrow> length ps = card b"
  using knights_path_set_eq knights_path_distinct by (metis distinct_card)

lemma knights_path_take: 
  assumes "knights_path b ps" "0 < k" "k < length ps"
  shows "knights_path (set (take k ps)) (take k ps)"
  using assms 
proof (induction arbitrary: k rule: knights_path.induct)
  case (2 s\<^sub>i b s\<^sub>j ps)
  then have "k = 1 \<or> k = 2 \<or> 2 < k" by force
  then show ?case
    using 2
  proof (elim disjE)
    assume "k = 2"
    then have "take k (s\<^sub>i#s\<^sub>j#ps) = [s\<^sub>i,s\<^sub>j]" "s\<^sub>i \<notin> {s\<^sub>j}" using 2 valid_step_neq by auto
    then show ?thesis using 2 knights_path.intros by auto
  next
    assume "2 < k"
    then have k_simps: "k-2 = k-1-1" "0 < k-2" "k-2 < length ps" and
        take_simp1: "take k (s\<^sub>i#s\<^sub>j#ps) = s\<^sub>i#take (k-1) (s\<^sub>j#ps)" and
        take_simp2: "take k (s\<^sub>i#s\<^sub>j#ps) = s\<^sub>i#s\<^sub>j#take (k-1-1) ps"
      using assms 2 take_Cons'[of k s\<^sub>i "s\<^sub>j#ps"] take_Cons'[of "k-1" s\<^sub>j ps] by auto
    then have "knights_path (set (take (k-1) (s\<^sub>j#ps))) (take (k-1) (s\<^sub>j#ps))"
      using 2 k_simps by auto
    then have kp: "knights_path (set (take (k-1) (s\<^sub>j#ps))) (s\<^sub>j#take (k-2) ps)"
      using take_Cons'[of "k-1" s\<^sub>j ps] by (auto simp: k_simps elim: knights_path.cases)

    have no_mem: "s\<^sub>i \<notin> set (take (k-1) (s\<^sub>j#ps))"
      using 2 set_take_subset[of "k-1" "s\<^sub>j#ps"] knights_path_set_eq by blast
    have "knights_path (set (take (k-1) (s\<^sub>j#ps)) \<union> {s\<^sub>i}) (s\<^sub>i#s\<^sub>j#take (k-2) ps)"
      using knights_path.intros(2)[OF no_mem \<open>valid_step s\<^sub>i s\<^sub>j\<close> kp] by auto
    then show ?thesis using k_simps take_simp2 knights_path_set_eq by metis
  qed (auto intro: knights_path.intros)
qed auto

lemma knights_path_drop: 
  assumes "knights_path b ps" "0 < k" "k < length ps"
  shows "knights_path (set (drop k ps)) (drop k ps)"
  using assms
proof (induction arbitrary: k rule: knights_path.induct)
  case (2 s\<^sub>i b s\<^sub>j ps)
  then have "(k = 1 \<and> ps = []) \<or> (k = 1 \<and> ps \<noteq> []) \<or> 1 < k" by force
  then show ?case
    using 2
  proof (elim disjE)
    assume "k = 1 \<and> ps \<noteq> []"
    then show ?thesis using 2 knights_path_set_eq by force
  next
    assume "1 < k"
    then have "0 < k-1" "k-1 < length (s\<^sub>j#ps)" "drop k (s\<^sub>i#s\<^sub>j#ps) = drop (k-1) (s\<^sub>j#ps)" 
      using assms 2 drop_Cons'[of k s\<^sub>i "s\<^sub>j#ps"] by auto
    then show ?thesis
      using 2 by auto
  qed (auto intro: knights_path.intros)
qed auto

text \<open>A Knight's path can be split to form two new disjoint Knight's paths.\<close>
corollary knights_path_split:             
  assumes "knights_path b ps" "0 < k" "k < length ps"
  shows 
    "\<exists>b\<^sub>1 b\<^sub>2. knights_path b\<^sub>1 (take k ps) \<and> knights_path b\<^sub>2 (drop k ps) \<and> b\<^sub>1 \<union> b\<^sub>2 = b \<and> b\<^sub>1 \<inter> b\<^sub>2 = {}"
  using assms
proof -
  let ?b\<^sub>1="set (take k ps)" 
  let ?b\<^sub>2="set (drop k ps)"
  have kp1: "knights_path ?b\<^sub>1 (take k ps)" and kp2: "knights_path ?b\<^sub>2 (drop k ps)"
    using assms knights_path_take knights_path_drop by auto
  have union: "?b\<^sub>1 \<union> ?b\<^sub>2 = b"
    using assms knights_path_set_eq by (metis append_take_drop_id set_append)
  have inter: "?b\<^sub>1 \<inter> ?b\<^sub>2 = {}"
    using assms knights_path_distinct by (metis append_take_drop_id distinct_append)
  show ?thesis using kp1 kp2 union inter by auto
qed

text \<open>Append two disjoint Knight's paths.\<close>
corollary knights_path_append:             
  assumes "knights_path b\<^sub>1 ps\<^sub>1" "knights_path b\<^sub>2 ps\<^sub>2" "b\<^sub>1 \<inter> b\<^sub>2 = {}" "valid_step (last ps\<^sub>1) (hd ps\<^sub>2)"
  shows "knights_path (b\<^sub>1 \<union> b\<^sub>2) (ps\<^sub>1 @ ps\<^sub>2)"
  using assms
proof (induction arbitrary: ps\<^sub>2 b\<^sub>2 rule: knights_path.induct)
  case (1 s\<^sub>i)
  then have "s\<^sub>i \<notin> b\<^sub>2" "ps\<^sub>2 \<noteq> []" "valid_step s\<^sub>i (hd ps\<^sub>2)" "knights_path b\<^sub>2 (hd ps\<^sub>2#tl ps\<^sub>2)" 
    using knights_path_non_nil by auto
  then have "knights_path (b\<^sub>2 \<union> {s\<^sub>i}) (s\<^sub>i#hd ps\<^sub>2#tl ps\<^sub>2)"
    using knights_path.intros by blast
  then show ?case using \<open>ps\<^sub>2 \<noteq> []\<close> by auto
next
  case (2 s\<^sub>i b\<^sub>1 s\<^sub>j ps\<^sub>1)
  then have "s\<^sub>i \<notin> b\<^sub>1 \<union> b\<^sub>2" "valid_step s\<^sub>i s\<^sub>j" "knights_path (b\<^sub>1 \<union> b\<^sub>2) (s\<^sub>j#ps\<^sub>1@ps\<^sub>2)" by auto
  then have "knights_path (b\<^sub>1 \<union> b\<^sub>2 \<union> {s\<^sub>i}) (s\<^sub>i#s\<^sub>j#ps\<^sub>1@ps\<^sub>2)"
    using knights_path.intros by auto
  then show ?case by auto
qed

lemma valid_step_rev: "valid_step s\<^sub>i s\<^sub>j \<Longrightarrow> valid_step s\<^sub>j s\<^sub>i"
  using step_checker_correct step_checker_rev by (metis prod.exhaust_sel)

text \<open>Reverse a Knight's path.\<close>
corollary knights_path_rev:
  assumes "knights_path b ps"
  shows "knights_path b (rev ps)"
  using assms
proof (induction rule: knights_path.induct)
  case (2 s\<^sub>i b s\<^sub>j ps)
  then have "knights_path {s\<^sub>i} [s\<^sub>i]" "b \<inter> {s\<^sub>i} = {}" "valid_step (last (rev (s\<^sub>j # ps))) (hd [s\<^sub>i])"
    using valid_step_rev by (auto intro: knights_path.intros)
  then have "knights_path (b \<union> {s\<^sub>i}) ((rev (s\<^sub>j#ps))@[s\<^sub>i])"
    using 2 knights_path_append by blast
  then show ?case by auto
qed (auto intro: knights_path.intros)

text \<open>Reverse a Knight's circuit.\<close>
corollary knights_circuit_rev:
  assumes "knights_circuit b ps"
  shows "knights_circuit b (rev ps)"
  using assms knights_path_rev valid_step_rev
  unfolding knights_circuit_def by (auto simp: hd_rev last_rev)

(* Function to rotate a Knight's circuit to start with (1,1),(3,2),... *)
(* fun rot_c_acc :: "path \<Rightarrow> path \<Rightarrow> path" where
  "rot_c_acc (s\<^sub>i#s\<^sub>j#ps) acc = 
    (if s\<^sub>i = (1,1) then 
      if s\<^sub>j = (3,2) then s\<^sub>i#rev (s\<^sub>j#ps@acc) else s\<^sub>i#s\<^sub>j#ps@acc
    else rot_c_acc (s\<^sub>j#ps) (s\<^sub>i#acc))"
| "rot_c_acc _ acc = []"

definition "rot_c ps \<equiv> rot_c_acc ps []" *)

lemma knights_circuit_rotate1:
  assumes "knights_circuit b (s\<^sub>i#ps)"
  shows "knights_circuit b (ps@[s\<^sub>i])"
proof (cases "ps = []")
  case True
  then show ?thesis using assms by auto
next
  case False
  have kp1: "knights_path b (s\<^sub>i#ps)" "valid_step (last (s\<^sub>i#ps)) (hd (s\<^sub>i#ps))"
    using assms unfolding knights_circuit_def by auto
  then have kp_elim: "s\<^sub>i \<notin> (b - {s\<^sub>i})" "valid_step s\<^sub>i (hd ps)" "knights_path (b - {s\<^sub>i}) ps"
    using \<open>ps \<noteq> []\<close> by (auto elim: knights_path.cases)
  then have vs': "valid_step (last (ps@[s\<^sub>i])) (hd (ps@[s\<^sub>i]))"
    using \<open>ps \<noteq> []\<close> valid_step_rev by auto

  have kp2: "knights_path {s\<^sub>i} [s\<^sub>i]" "(b - {s\<^sub>i}) \<inter> {s\<^sub>i} = {}"
    by (auto intro: knights_path.intros)

  have vs: "valid_step (last ps) (hd [s\<^sub>i])"
    using \<open>ps \<noteq> []\<close> \<open>valid_step (last (s\<^sub>i#ps)) (hd (s\<^sub>i#ps))\<close> by auto

  have "(b - {s\<^sub>i}) \<union> {s\<^sub>i} = b"
    using kp1 kp_elim knights_path_set_eq by force
  then show ?thesis
    unfolding knights_circuit_def
    using vs knights_path_append[OF \<open>knights_path (b - {s\<^sub>i}) ps\<close> kp2] vs' by auto
qed

text \<open>A Knight's circuit can be rotated to start at any square on the board.\<close>
lemma knights_circuit_rotate_to:
  assumes "knights_circuit b ps" "hd (drop k ps) = s\<^sub>i" "k < length ps"
  shows "\<exists>ps'. knights_circuit b ps' \<and> hd ps' = s\<^sub>i"
  using assms
proof (induction k arbitrary: b ps)
  case (Suc k)
  let ?s\<^sub>j="hd ps"
  let ?ps'="tl ps"           
  show ?case
  proof (cases "s\<^sub>i = ?s\<^sub>j")
    case True
    then show ?thesis using Suc by auto
  next
    case False
    then have "?ps' \<noteq> []"
      using Suc by (metis drop_Nil drop_Suc drop_eq_Nil2 le_antisym nat_less_le)
    then have "knights_circuit b (?s\<^sub>j#?ps')"
      using Suc by (metis list.exhaust_sel tl_Nil)
    then have "knights_circuit b (?ps'@[?s\<^sub>j])" "hd (drop k (?ps'@[?s\<^sub>j])) = s\<^sub>i" 
      using Suc knights_circuit_rotate1 by (auto simp: drop_Suc)
    then show ?thesis using Suc by auto
  qed
qed auto

text \<open>For positive boards (1,1) can only have (2,3) and (3,2) as a neighbour.\<close>
lemma valid_step_1_1:
  assumes "valid_step (1,1) (i,j)" "i > 0" "j > 0"
  shows "(i,j) = (2,3) \<or> (i,j) = (3,2)"
  using assms unfolding valid_step_def by auto

lemma list_len_g_1_split: "length xs > 1 \<Longrightarrow> \<exists>x\<^sub>1 x\<^sub>2 xs'. xs = x\<^sub>1#x\<^sub>2#xs'"
proof (induction xs)
  case (Cons x xs)
  then have "length xs > 0" by auto
  then have "length xs \<ge> 1" by presburger
  then have "length xs = 1 \<or> length xs > 1" by auto
  then show ?case 
  proof (elim disjE)
    assume "length xs = 1"
    then obtain x\<^sub>1 where [simp]: "xs = [x\<^sub>1]"
      using length_Suc_conv[of xs 0] by auto
    then show ?thesis by auto
  next
    assume "1 < length xs"
    then show ?thesis using Cons by auto
  qed
qed auto

lemma list_len_g_3_split: "length xs > 3 \<Longrightarrow> \<exists>x\<^sub>1 x\<^sub>2 xs' x\<^sub>3. xs = x\<^sub>1#x\<^sub>2#xs'@[x\<^sub>3]"
proof (induction xs)
  case (Cons x xs)
  then have "length xs = 3 \<or> length xs > 3" by auto
  then show ?case 
  proof (elim disjE)
    assume "length xs = 3"
    then obtain x\<^sub>1 xs\<^sub>1 where [simp]: "xs = x\<^sub>1#xs\<^sub>1" "length xs\<^sub>1 = 2"
      using length_Suc_conv[of xs 2] by auto
    then obtain x\<^sub>2 xs\<^sub>2 where [simp]: "xs\<^sub>1 = x\<^sub>2#xs\<^sub>2" "length xs\<^sub>2 = 1"
      using length_Suc_conv[of xs\<^sub>1 1] by auto
    then obtain x\<^sub>3 where [simp]: "xs\<^sub>2 = [x\<^sub>3]"
      using length_Suc_conv[of xs\<^sub>2 0] by auto
    then show ?thesis by auto
  next
    assume "length xs > 3"
    then show ?thesis using Cons by auto
  qed
qed auto

text \<open>Any Knight's circuit on a positive board can be rotated to start with (1,1) and 
end with (3,2).\<close>
corollary rotate_knights_circuit:
  assumes "knights_circuit (board n m) ps" "min n m \<ge> 5"
  shows "\<exists>ps. knights_circuit (board n m) ps \<and> hd ps = (1,1) \<and> last ps = (3,2)"
  using assms
proof -
  let ?b="board n m"
  have "knights_path ?b ps"
    using assms unfolding knights_circuit_def by auto
  then have "(1,1) \<in> set ps"
    using assms knights_path_set_eq by (auto simp: board_def)
  then obtain k where "hd (drop k ps) = (1,1)" "k < length ps"
    by (metis hd_drop_conv_nth in_set_conv_nth)
  then obtain ps\<^sub>r where ps\<^sub>r_prems: "knights_circuit ?b ps\<^sub>r" "hd ps\<^sub>r = (1,1)"
    using assms knights_circuit_rotate_to by blast
  then have kp: "knights_path ?b ps\<^sub>r" and "valid_step (last ps\<^sub>r) (1,1)"
    unfolding knights_circuit_def by auto

  have "(1,1) \<in> ?b" "(1,2) \<in> ?b" "(1,3) \<in> ?b"
    using assms unfolding board_def by auto
  then have "(1,1) \<in> set ps\<^sub>r" "(1,2) \<in> set ps\<^sub>r" "(1,3) \<in> set ps\<^sub>r"
    using kp knights_path_set_eq by auto

  have "3 < card ?b"
    using assms board_leq_subset card_board[of 5 5]
          card_mono[OF board_finite[of n m], of "board 5 5"] by auto
  then have "3 < length ps\<^sub>r"
    using knights_path_length kp by auto
  then obtain s\<^sub>j ps' s\<^sub>k where [simp]: "ps\<^sub>r = (1,1)#s\<^sub>j#ps'@[s\<^sub>k]"
    using \<open>hd ps\<^sub>r = (1,1)\<close> list_len_g_3_split[of ps\<^sub>r] by auto
  have "s\<^sub>j \<noteq> s\<^sub>k"
    using kp knights_path_distinct by force

  have vs_s\<^sub>k: "valid_step s\<^sub>k (1,1)"
    using \<open>valid_step (last ps\<^sub>r) (1,1)\<close> by simp

  have vs_s\<^sub>j: "valid_step (1,1) s\<^sub>j" and kp': "knights_path (?b - {(1,1)}) (s\<^sub>j#ps'@[s\<^sub>k])"
    using kp by (auto elim: knights_path.cases)

  have "s\<^sub>j \<in> set ps\<^sub>r" "s\<^sub>k \<in> set ps\<^sub>r" by auto
  then have "s\<^sub>j \<in> ?b" "s\<^sub>k \<in> ?b"
    using kp knights_path_set_eq by blast+
  then have "0 < fst s\<^sub>j \<and> 0 < snd s\<^sub>j" "0 < fst s\<^sub>k \<and> 0 < snd s\<^sub>k"
    unfolding board_def by auto
  then have "s\<^sub>k = (2,3) \<or> s\<^sub>k = (3,2)" "s\<^sub>j = (2,3) \<or> s\<^sub>j = (3,2)"
    using vs_s\<^sub>k vs_s\<^sub>j valid_step_1_1 valid_step_rev by (metis prod.collapse)+
  then have "s\<^sub>k = (3,2) \<or> s\<^sub>j = (3,2)"
    using \<open>s\<^sub>j \<noteq> s\<^sub>k\<close> by auto
  then show ?thesis
  proof (elim disjE)
    assume "s\<^sub>k = (3,2)"
    then have "last ps\<^sub>r = (3,2)" by auto
    then show ?thesis using ps\<^sub>r_prems by auto
  next
    assume "s\<^sub>j = (3,2)"
    then have vs: "valid_step (last ((1,1)#rev (s\<^sub>j#ps'@[s\<^sub>k]))) (hd ((1,1)#rev (s\<^sub>j#ps'@[s\<^sub>k])))"
      unfolding valid_step_def by auto

    have rev_simp: "rev (s\<^sub>j#ps'@[s\<^sub>k]) = s\<^sub>k#(rev ps')@[s\<^sub>j]" by auto

    have "knights_path (?b - {(1,1)}) (rev (s\<^sub>j#ps'@[s\<^sub>k]))"
      using knights_path_rev[OF kp'] by auto
    then have "(1,1) \<notin> (?b - {(1,1)})" "valid_step (1,1) s\<^sub>k" 
         "knights_path (?b - {(1,1)}) (s\<^sub>k#(rev ps')@[s\<^sub>j])"
      using assms vs_s\<^sub>k valid_step_rev by (auto simp: rev_simp)
    then have "knights_path (?b - {(1, 1)} \<union> {(1, 1)}) ((1,1)#s\<^sub>k#(rev ps')@[s\<^sub>j])"
      using knights_path.intros(2)[of "(1,1)" "?b - {(1,1)}" s\<^sub>k "(rev ps')@[s\<^sub>j]"] by auto
    then have "knights_path ?b ((1,1)#rev (s\<^sub>j#ps'@[s\<^sub>k]))"
      using assms by (simp add: board_def insert_absorb rev_simp)
    then have "knights_circuit ?b ((1,1)#rev (s\<^sub>j#ps'@[s\<^sub>k]))"
      unfolding knights_circuit_def using vs by auto
    then show ?thesis
      using \<open>s\<^sub>j = (3,2)\<close> by auto
  qed
qed

section \<open>Transposing Paths and Boards\<close>

subsection \<open>Implementation of Path and Board Transposition\<close>

definition "transpose_square s\<^sub>i = (case s\<^sub>i of (i,j) \<Rightarrow> (j,i))"

fun transpose :: "path \<Rightarrow> path" where
  "transpose [] = []"
| "transpose (s\<^sub>i#ps) = (transpose_square s\<^sub>i)#transpose ps"

definition transpose_board :: "board \<Rightarrow> board" where
  "transpose_board b \<equiv> {(j,i) |i j. (i,j) \<in> b}"

subsection \<open>Correctness of Path and Board Transposition\<close>

lemma transpose2: "transpose_square (transpose_square s\<^sub>i) = s\<^sub>i"
  unfolding transpose_square_def by (auto split: prod.splits)

lemma transpose_nil: "ps = [] \<longleftrightarrow> transpose ps = []"
  using transpose.elims by blast

lemma transpose_length: "length ps = length (transpose ps)"
  by (induction ps) auto

lemma hd_transpose: "ps \<noteq>[] \<Longrightarrow> hd (transpose ps) = transpose_square (hd ps)"
  by (induction ps) (auto simp: transpose_square_def)

lemma last_transpose: "ps \<noteq>[] \<Longrightarrow> last (transpose ps) = transpose_square (last ps)"
proof (induction ps)
  case (Cons s\<^sub>i ps)
  then show ?case
  proof (cases "ps = []")
    case True
    then show ?thesis using Cons by (auto simp: transpose_square_def)      
  next
    case False
    then show ?thesis using Cons transpose_nil by auto
  qed
qed auto

lemma take_transpose: 
  shows "take k (transpose ps) = transpose (take k ps)"
proof (induction ps arbitrary: k)
  case Nil
  then show ?case by auto
next
  case (Cons s\<^sub>i ps)
  then obtain i j where "s\<^sub>i = (i,j)" by force
  then have "k = 0 \<or> k > 0" by auto
  then show ?case 
  proof (elim disjE)
    assume "k > 0"
    then show ?thesis using Cons.IH by (auto simp: \<open>s\<^sub>i = (i,j)\<close> take_Cons')
  qed auto
qed

lemma drop_transpose: 
  shows "drop k (transpose ps) = transpose (drop k ps)"
proof (induction ps arbitrary: k)
  case Nil
  then show ?case by auto
next
  case (Cons s\<^sub>i ps)
  then obtain i j where "s\<^sub>i = (i,j)" by force
  then have "k = 0 \<or> k > 0" by auto
  then show ?case 
  proof (elim disjE)
    assume "k > 0"
    then show ?thesis using Cons.IH by (auto simp: \<open>s\<^sub>i = (i,j)\<close> drop_Cons')
  qed auto
qed

lemma transpose_board_correct: "s\<^sub>i \<in> b \<longleftrightarrow> (transpose_square s\<^sub>i) \<in> transpose_board b"
  unfolding transpose_board_def transpose_square_def by (auto split: prod.splits)

lemma transpose_board: "transpose_board (board n m) = board m n"
  unfolding board_def using transpose_board_correct by (auto simp: transpose_square_def)

lemma insert_transpose_board: 
  "insert (transpose_square s\<^sub>i) (transpose_board b) = transpose_board (insert s\<^sub>i b)"
  unfolding transpose_board_def transpose_square_def by (auto split: prod.splits)

lemma transpose_board2: "transpose_board (transpose_board b) = b"
  unfolding transpose_board_def by auto

lemma transpose_union: "transpose_board (b\<^sub>1 \<union> b\<^sub>2) = transpose_board b\<^sub>1 \<union> transpose_board b\<^sub>2"
  unfolding transpose_board_def by auto

lemma transpose_valid_step: 
  "valid_step s\<^sub>i s\<^sub>j \<longleftrightarrow> valid_step (transpose_square s\<^sub>i) (transpose_square s\<^sub>j)"
  unfolding valid_step_def transpose_square_def by (auto split: prod.splits)

lemma transpose_knights_path':  
  assumes "knights_path b ps" 
  shows "knights_path (transpose_board b) (transpose ps)"
  using assms
proof (induction rule: knights_path.induct)
  case (1 s\<^sub>i)
  then have "transpose_board {s\<^sub>i} = {transpose_square s\<^sub>i}" "transpose [s\<^sub>i] = [transpose_square s\<^sub>i]"
    using transpose_board_correct by (auto simp: transpose_square_def split: prod.splits)
  then show ?case by (auto intro: knights_path.intros)
next
  case (2 s\<^sub>i b s\<^sub>j ps)
  then have prems: "transpose_square s\<^sub>i \<notin> transpose_board b" 
            "valid_step (transpose_square s\<^sub>i) (transpose_square s\<^sub>j)" 
            and "transpose (s\<^sub>j#ps) = transpose_square s\<^sub>j#transpose ps"
    using 2 transpose_board_correct transpose_valid_step by auto
  then show ?case 
    using 2 knights_path.intros(2)[OF prems] insert_transpose_board by auto
qed

corollary transpose_knights_path: 
  assumes "knights_path (board n m) ps" 
  shows "knights_path (board m n) (transpose ps)"
  using assms transpose_knights_path'[of "board n m" ps] by (auto simp: transpose_board) 

corollary transpose_knights_circuit: 
  assumes "knights_circuit (board n m) ps" 
  shows "knights_circuit (board m n) (transpose ps)"
  using assms 
proof -
  have "knights_path (board n m) ps" and vs: "valid_step (last ps) (hd ps)"
    using assms unfolding knights_circuit_def by auto
  then have kp_t: "knights_path (board m n) (transpose ps)" and "ps \<noteq> []"
    using transpose_knights_path knights_path_non_nil by auto
  then have "valid_step (last (transpose ps)) (hd (transpose ps))"
    using vs hd_transpose last_transpose transpose_valid_step by auto
  then show ?thesis using kp_t by (auto simp: knights_circuit_def)
qed

section \<open>Mirroring Paths and Boards\<close>

subsection \<open>Implementation of Path and Board Mirroring\<close>

abbreviation "min1 ps \<equiv> Min ((fst) ` set ps)"
abbreviation "max1 ps \<equiv> Max ((fst) ` set ps)"
abbreviation "min2 ps \<equiv> Min ((snd) ` set ps)"
abbreviation "max2 ps \<equiv> Max ((snd) ` set ps)"

definition mirror1_square :: "int \<Rightarrow> square \<Rightarrow> square" where 
  "mirror1_square n s\<^sub>i = (case s\<^sub>i of (i,j) \<Rightarrow> (n-i,j))"

fun mirror1_aux :: "int \<Rightarrow> path \<Rightarrow> path" where
  "mirror1_aux n [] = []"
| "mirror1_aux n (s\<^sub>i#ps) = (mirror1_square n s\<^sub>i)#mirror1_aux n ps"

definition "mirror1 ps = mirror1_aux (max1 ps + min1 ps) ps"

definition mirror1_board :: "int \<Rightarrow> board \<Rightarrow> board" where
  "mirror1_board n b \<equiv> {mirror1_square n s\<^sub>i |s\<^sub>i. s\<^sub>i \<in> b}"

definition mirror2_square :: "int \<Rightarrow> square \<Rightarrow> square" where 
  "mirror2_square m s\<^sub>i = (case s\<^sub>i of (i,j) \<Rightarrow> (i,m-j))"

fun mirror2_aux :: "int \<Rightarrow> path \<Rightarrow> path" where
  "mirror2_aux m [] = []"
| "mirror2_aux m (s\<^sub>i#ps) = (mirror2_square m s\<^sub>i)#mirror2_aux m ps"

definition "mirror2 ps = mirror2_aux (max2 ps + min2 ps) ps"

definition mirror2_board :: "int \<Rightarrow> board \<Rightarrow> board" where
  "mirror2_board m b \<equiv> {mirror2_square m s\<^sub>i |s\<^sub>i. s\<^sub>i \<in> b}"

subsection \<open>Correctness of Path and Board Mirroring\<close>

lemma mirror1_board_id: "mirror1_board (int n+1) (board n m) = board n m" (is "_ = ?b")
proof
  show "mirror1_board (int n+1) ?b \<subseteq> ?b"
  proof
    fix s\<^sub>i'
    assume assms: "s\<^sub>i' \<in> mirror1_board (int n+1) ?b"
    then obtain i' j' where [simp]: "s\<^sub>i' = (i',j')" by force
    then have "(i',j') \<in> mirror1_board (int n+1) ?b"
      using assms by auto
    then obtain i j where "(i,j) \<in> ?b" "mirror1_square (int n+1) (i,j) = (i',j')"
      unfolding mirror1_board_def by auto
    then have "1 \<le> i \<and> i \<le> int n" "1 \<le> j \<and> j \<le> int m" "i'=(int n+1)-i" "j'=j"
      unfolding board_def mirror1_square_def by auto
    then have "1 \<le> i' \<and> i' \<le> int n" "1 \<le> j' \<and> j' \<le> int m"
      by auto
    then show "s\<^sub>i' \<in> ?b"
      unfolding board_def by auto
  qed
next
  show "?b \<subseteq> mirror1_board (int n+1) ?b"
  proof
    fix s\<^sub>i
    assume assms: "s\<^sub>i \<in> ?b"
    then obtain i j where [simp]: "s\<^sub>i = (i,j)" by force
    then have "(i,j) \<in> ?b"
      using assms by auto
    then have "1 \<le> i \<and> i \<le> int n" "1 \<le> j \<and> j \<le> int m"
      unfolding board_def by auto
    then obtain i' j' where "i'=(int n+1)-i" "j'=j" by auto
    then have "(i',j') \<in> ?b" "mirror1_square (int n+1) (i',j') = (i,j)" 
      using \<open>1 \<le> i \<and> i \<le> int n\<close> \<open>1 \<le> j \<and> j \<le> int m\<close> 
      unfolding mirror1_square_def by (auto simp: board_def)
    then show "s\<^sub>i \<in> mirror1_board (int n+1) ?b"
      unfolding mirror1_board_def by force
  qed
qed

lemma mirror2_board_id: "mirror2_board (int m+1) (board n m) = board n m" (is "_ = ?b")
proof
  show "mirror2_board (int m+1) ?b \<subseteq> ?b"
  proof
    fix s\<^sub>i'
    assume assms: "s\<^sub>i' \<in> mirror2_board (int m+1) ?b"
    then obtain i' j' where [simp]: "s\<^sub>i' = (i',j')" by force
    then have "(i',j') \<in> mirror2_board (int m+1) ?b"
      using assms by auto
    then obtain i j where "(i,j) \<in> ?b" "mirror2_square (int m+1) (i,j) = (i',j')"
      unfolding mirror2_board_def by auto
    then have "1 \<le> i \<and> i \<le> int n" "1 \<le> j \<and> j \<le> int m" "i'=i" "j'=(int m+1)-j"
      unfolding board_def mirror2_square_def by auto
    then have "1 \<le> i' \<and> i' \<le> int n" "1 \<le> j' \<and> j' \<le> int m"
      by auto
    then show "s\<^sub>i' \<in> ?b"
      unfolding board_def by auto
  qed
next
  show "?b \<subseteq> mirror2_board (int m+1) ?b"
  proof
    fix s\<^sub>i
    assume assms: "s\<^sub>i \<in> ?b"
    then obtain i j where [simp]: "s\<^sub>i = (i,j)" by force
    then have "(i,j) \<in> ?b"
      using assms by auto
    then have "1 \<le> i \<and> i \<le> int n" "1 \<le> j \<and> j \<le> int m"
      unfolding board_def by auto
    then obtain i' j' where "i'=i" "j'=(int m+1)-j" by auto
    then have "(i',j') \<in> ?b" "mirror2_square (int m+1) (i',j') = (i,j)" 
      using \<open>1 \<le> i \<and> i \<le> int n\<close> \<open>1 \<le> j \<and> j \<le> int m\<close> 
      unfolding mirror2_square_def by (auto simp: board_def)
    then show "s\<^sub>i \<in> mirror2_board (int m+1) ?b"
      unfolding mirror2_board_def by force
  qed
qed

lemma knights_path_min1: "knights_path (board n m) ps \<Longrightarrow> min1 ps = 1"
proof -
  assume assms: "knights_path (board n m) ps"
  then have "min n m \<ge> 1"
    using knights_path_board_m_n_geq_1 by auto
  then have "(1,1) \<in> board n m" and ge_1: "\<forall>(i,j) \<in> board n m. i \<ge> 1"
    unfolding board_def by auto
  then have finite: "finite ((fst) ` board n m)" and 
          non_empty: "(fst) ` board n m \<noteq> {}" and
          mem_1: "1 \<in> (fst) ` board n m"
    using board_finite by auto (metis fstI image_eqI)
  then have "Min ((fst) ` board n m) = 1"
    using ge_1 by (auto simp: Min_eq_iff)
  then show ?thesis
    using assms knights_path_set_eq by auto
qed

lemma knights_path_min2: "knights_path (board n m) ps \<Longrightarrow> min2 ps = 1"
proof -
  assume assms: "knights_path (board n m) ps"
  then have "min n m \<ge> 1"
    using knights_path_board_m_n_geq_1 by auto
  then have "(1,1) \<in> board n m" and ge_1: "\<forall>(i,j) \<in> board n m. j \<ge> 1"
    unfolding board_def by auto
  then have finite: "finite ((snd) ` board n m)" and 
          non_empty: "(snd) ` board n m \<noteq> {}" and
          mem_1: "1 \<in> (snd) ` board n m"
    using board_finite by auto (metis sndI image_eqI)
  then have "Min ((snd) ` board n m) = 1"
    using ge_1 by (auto simp: Min_eq_iff)
  then show ?thesis
    using assms knights_path_set_eq by auto
qed

lemma knights_path_max1: "knights_path (board n m) ps \<Longrightarrow> max1 ps = int n"
proof -
  assume assms: "knights_path (board n m) ps"
  then have "min n m \<ge> 1"
    using knights_path_board_m_n_geq_1 by auto
  then have "(int n,1) \<in> board n m" and leq_n: "\<forall>(i,j) \<in> board n m. i \<le> int n"
    unfolding board_def by auto
  then have finite: "finite ((fst) ` board n m)" and 
          non_empty: "(fst) ` board n m \<noteq> {}" and
          mem_1: "int n \<in> (fst) ` board n m"
    using board_finite by auto (metis fstI image_eqI)
  then have "Max ((fst) ` board n m) = int n"
    using leq_n by (auto simp: Max_eq_iff)
  then show ?thesis
    using assms knights_path_set_eq by auto
qed

lemma knights_path_max2: "knights_path (board n m) ps \<Longrightarrow> max2 ps = int m"
proof -
  assume assms: "knights_path (board n m) ps"
  then have "min n m \<ge> 1"
    using knights_path_board_m_n_geq_1 by auto
  then have "(1,int m) \<in> board n m" and leq_m: "\<forall>(i,j) \<in> board n m. j \<le> int m"
    unfolding board_def by auto
  then have finite: "finite ((snd) ` board n m)" and 
          non_empty: "(snd) ` board n m \<noteq> {}" and
          mem_1: "int m \<in> (snd) ` board n m"
    using board_finite by auto (metis sndI image_eqI)
  then have "Max ((snd) ` board n m) = int m"
    using leq_m by (auto simp: Max_eq_iff)
  then show ?thesis
    using assms knights_path_set_eq by auto
qed

lemma mirror1_aux_nil: "ps = [] \<longleftrightarrow> mirror1_aux m ps = []"
  using mirror1_aux.elims by blast

lemma mirror1_nil: "ps = [] \<longleftrightarrow> mirror1 ps = []"
  unfolding mirror1_def using mirror1_aux_nil by blast

lemma mirror2_aux_nil: "ps = [] \<longleftrightarrow> mirror2_aux m ps = []"
  using mirror2_aux.elims by blast

lemma mirror2_nil: "ps = [] \<longleftrightarrow> mirror2 ps = []"
  unfolding mirror2_def using mirror2_aux_nil by blast

lemma length_mirror1_aux: "length ps = length (mirror1_aux n ps)"
  by (induction ps) auto

lemma length_mirror1: "length ps = length (mirror1 ps)"
  unfolding mirror1_def using length_mirror1_aux by auto

lemma length_mirror2_aux: "length ps = length (mirror2_aux n ps)"
  by (induction ps) auto

lemma length_mirror2: "length ps = length (mirror2 ps)"
  unfolding mirror2_def using length_mirror2_aux by auto

lemma mirror1_board_iff:"s\<^sub>i \<notin> b \<longleftrightarrow> mirror1_square n s\<^sub>i \<notin> mirror1_board n b"
  unfolding mirror1_board_def mirror1_square_def by (auto split: prod.splits)

lemma mirror2_board_iff:"s\<^sub>i \<notin> b \<longleftrightarrow> mirror2_square n s\<^sub>i \<notin> mirror2_board n b"
  unfolding mirror2_board_def mirror2_square_def by (auto split: prod.splits)

lemma insert_mirror1_board: 
  "insert (mirror1_square n s\<^sub>i) (mirror1_board n b) = mirror1_board n (insert s\<^sub>i b)"
  unfolding mirror1_board_def mirror1_square_def by (auto split: prod.splits)

lemma insert_mirror2_board: 
  "insert (mirror2_square n s\<^sub>i) (mirror2_board n b) = mirror2_board n (insert s\<^sub>i b)"
  unfolding mirror2_board_def mirror2_square_def by (auto split: prod.splits)

lemma valid_step_mirror1: 
  "valid_step s\<^sub>i s\<^sub>j \<longleftrightarrow> valid_step (mirror1_square n s\<^sub>i) (mirror1_square n s\<^sub>j)" 
proof
  assume assms: "valid_step s\<^sub>i s\<^sub>j"
  obtain i j i' j' where [simp]: "s\<^sub>i = (i,j)" "s\<^sub>j = (i',j')" by force
  then have "valid_step (n-i,j) (n-i',j')"
    using assms unfolding valid_step_def
    apply simp
    apply (elim disjE)
    apply auto
    done
  then show "valid_step (mirror1_square n s\<^sub>i) (mirror1_square n s\<^sub>j)"
    unfolding mirror1_square_def by auto
next
  assume assms: "valid_step (mirror1_square n s\<^sub>i) (mirror1_square n s\<^sub>j)"
  obtain i j i' j' where [simp]: "s\<^sub>i = (i,j)" "s\<^sub>j = (i',j')" by force
  then have "valid_step (i,j) (i',j')"
    using assms unfolding valid_step_def mirror1_square_def
    apply simp
    apply (elim disjE)
    apply auto
    done
  then show "valid_step s\<^sub>i s\<^sub>j"
    unfolding mirror1_square_def by auto
qed

lemma valid_step_mirror2: 
  "valid_step s\<^sub>i s\<^sub>j \<longleftrightarrow> valid_step (mirror2_square m s\<^sub>i) (mirror2_square m s\<^sub>j)"
proof
  assume assms: "valid_step s\<^sub>i s\<^sub>j"
  obtain i j i' j' where [simp]: "s\<^sub>i = (i,j)" "s\<^sub>j = (i',j')" by force
  then have "valid_step (i,m-j) (i',m-j')"
    using assms unfolding valid_step_def
    apply simp
    apply (elim disjE)
    apply auto
    done
  then show "valid_step (mirror2_square m s\<^sub>i) (mirror2_square m s\<^sub>j)"
    unfolding mirror2_square_def by auto
next
  assume assms: "valid_step (mirror2_square m s\<^sub>i) (mirror2_square m s\<^sub>j)"
  obtain i j i' j' where [simp]: "s\<^sub>i = (i,j)" "s\<^sub>j = (i',j')" by force
  then have "valid_step (i,j) (i',j')"
    using assms unfolding valid_step_def mirror2_square_def
    apply simp
    apply (elim disjE)
    apply auto
    done
  then show "valid_step s\<^sub>i s\<^sub>j"
    unfolding mirror1_square_def by auto
qed

lemma hd_mirror1:
  assumes "knights_path (board n m) ps" "hd ps = (i,j)"
  shows "hd (mirror1 ps) = (int n+1-i,j)"
  using assms
proof -
  have "hd (mirror1 ps) = hd (mirror1_aux (int n+1) ps)"
    unfolding mirror1_def using assms knights_path_min1 knights_path_max1 by auto
  also have "... = hd (mirror1_aux (int n+1) ((hd ps)#(tl ps)))"
    using assms knights_path_non_nil by (metis list.collapse)
  also have "... = (int n+1-i,j)"
    using assms by (auto simp: mirror1_square_def)
  finally show ?thesis .
qed

lemma last_mirror1_aux:
  assumes "ps \<noteq> []" "last ps = (i,j)"
  shows "last (mirror1_aux n ps) = (n-i,j)"
  using assms
proof (induction ps)
  case (Cons s\<^sub>i ps)
  then show ?case 
    using mirror1_aux_nil Cons by (cases "ps = []") (auto simp: mirror1_square_def)
qed auto

lemma last_mirror1:
  assumes "knights_path (board n m) ps" "last ps = (i,j)"
  shows "last (mirror1 ps) = (int n+1-i,j)"
  unfolding mirror1_def using assms last_mirror1_aux knights_path_non_nil
  by (simp add: knights_path_max1 knights_path_min1)

lemma hd_mirror2:
  assumes "knights_path (board n m) ps" "hd ps = (i,j)"
  shows "hd (mirror2 ps) = (i,int m+1-j)"
  using assms
proof -
  have "hd (mirror2 ps) = hd (mirror2_aux (int m+1) ps)"
    unfolding mirror2_def using assms knights_path_min2 knights_path_max2 by auto
  also have "... = hd (mirror2_aux (int m+1) ((hd ps)#(tl ps)))"
    using assms knights_path_non_nil by (metis list.collapse)
  also have "... = (i,int m+1-j)"
    using assms by (auto simp: mirror2_square_def)
  finally show ?thesis .
qed

lemma last_mirror2_aux:
  assumes "ps \<noteq> []" "last ps = (i,j)"
  shows "last (mirror2_aux m ps) = (i,m-j)"
  using assms
proof (induction ps)
  case (Cons s\<^sub>i ps)
  then show ?case 
    using mirror2_aux_nil Cons by (cases "ps = []") (auto simp: mirror2_square_def)
qed auto

lemma last_mirror2:
  assumes "knights_path (board n m) ps" "last ps = (i,j)"
  shows "last (mirror2 ps) = (i,int m+1-j)"
  unfolding mirror2_def using assms last_mirror2_aux knights_path_non_nil
  by (simp add: knights_path_max2 knights_path_min2)

lemma mirror1_aux_knights_path:
  assumes "knights_path b ps" 
  shows "knights_path (mirror1_board n b) (mirror1_aux n ps)"
  using assms
proof (induction rule: knights_path.induct)
  case (1 s\<^sub>i)
  then have "mirror1_board n {s\<^sub>i} = {mirror1_square n s\<^sub>i}" 
    unfolding mirror1_board_def by blast
  then show ?case by (auto intro: knights_path.intros)
next
  case (2 s\<^sub>i b s\<^sub>j ps)
  then have prems: "mirror1_square n s\<^sub>i \<notin> mirror1_board n b" 
            "valid_step (mirror1_square n s\<^sub>i) (mirror1_square n s\<^sub>j)" 
            and "mirror1_aux n (s\<^sub>j#ps) = mirror1_square n s\<^sub>j#mirror1_aux n ps"
    using 2 mirror1_board_iff valid_step_mirror1 by auto
  then show ?case 
    using 2 knights_path.intros(2)[OF prems] insert_mirror1_board by auto
qed

corollary mirror1_knights_path:
  assumes "knights_path (board n m) ps" 
  shows "knights_path (board n m) (mirror1 ps)"
  using assms
proof -
  have [simp]: "min1 ps = 1" "max1 ps = int n"
    using assms knights_path_min1 knights_path_max1 by auto
  then have "mirror1_board (int n+1) (board n m) = (board n m)"
    using mirror1_board_id by auto
  then have "knights_path (board n m) (mirror1_aux (int n+1) ps)"
    using assms mirror1_aux_knights_path[of "board n m" ps "int n+1"] by auto
  then show ?thesis unfolding mirror1_def by auto
qed

lemma mirror2_aux_knights_path:
  assumes "knights_path b ps" 
  shows "knights_path (mirror2_board n b) (mirror2_aux n ps)"
  using assms
proof (induction rule: knights_path.induct)
  case (1 s\<^sub>i)
  then have "mirror2_board n {s\<^sub>i} = {mirror2_square n s\<^sub>i}" 
    unfolding mirror2_board_def by blast
  then show ?case by (auto intro: knights_path.intros)
next
  case (2 s\<^sub>i b s\<^sub>j ps)
  then have prems: "mirror2_square n s\<^sub>i \<notin> mirror2_board n b" 
            "valid_step (mirror2_square n s\<^sub>i) (mirror2_square n s\<^sub>j)" 
            and "mirror2_aux n (s\<^sub>j#ps) = mirror2_square n s\<^sub>j#mirror2_aux n ps"
    using 2 mirror2_board_iff valid_step_mirror2 by auto
  then show ?case 
    using 2 knights_path.intros(2)[OF prems] insert_mirror2_board by auto
qed

corollary mirror2_knights_path:
  assumes "knights_path (board n m) ps" 
  shows "knights_path (board n m) (mirror2 ps)"
proof -
  have [simp]: "min2 ps = 1" "max2 ps = int m"
    using assms knights_path_min2 knights_path_max2 by auto
  then have "mirror2_board (int m+1) (board n m) = (board n m)"
    using mirror2_board_id by auto
  then have "knights_path (board n m) (mirror2_aux (int m+1) ps)"
    using assms mirror2_aux_knights_path[of "board n m" ps "int m+1"] by auto
  then show ?thesis unfolding mirror2_def by auto
qed

subsection \<open>Rotate Knight's Paths\<close>

text \<open>Transposing (@{const transpose}) and mirroring (along first axis \<open>mirror1\<close>) a Knight's path 
preserves the Knight's path's property. Tranpose+Mirror1 equals a 90deg-clockwise turn.\<close>
corollary rot90_knights_path:
  assumes "knights_path (board n m) ps" 
  shows "knights_path (board m n) (mirror1 (transpose ps))"
  using assms transpose_knights_path mirror1_knights_path by auto

lemma hd_rot90_knights_path: 
  assumes "knights_path (board n m) ps" "hd ps = (i,j)"
  shows "hd (mirror1 (transpose ps)) = (int m+1-j,i)"
  using assms
proof -
  have "hd (transpose ps) = (j,i)" "knights_path (board m n) (transpose ps)"
    using assms knights_path_non_nil hd_transpose transpose_knights_path 
    by (auto simp: transpose_square_def)
  then show ?thesis using hd_mirror1 by auto
qed

lemma last_rot90_knights_path: 
  assumes "knights_path (board n m) ps" "last ps = (i,j)"
  shows "last (mirror1 (transpose ps)) = (int m+1-j,i)"
  using assms
proof -
  have "last (transpose ps) = (j,i)" "knights_path (board m n) (transpose ps)"
    using assms knights_path_non_nil last_transpose transpose_knights_path 
    by (auto simp: transpose_square_def)
  then show ?thesis using last_mirror1 by auto
qed

section \<open>Translating Paths and Boards\<close>

text \<open>When constructing knight's paths for larger boards multiple knight's paths for smaller boards
are concatenated. To concatenate paths the the coordinates in the path need to be translated. 
Therefore, simple auxiliary functions are provided.\<close>

subsection \<open>Implementation of Path and Board Translation\<close>

text \<open>Translate the coordinates for a path by \<open>(k\<^sub>1,k\<^sub>2)\<close>.\<close>
fun trans_path :: "int \<times> int \<Rightarrow> path \<Rightarrow> path" where
  "trans_path (k\<^sub>1,k\<^sub>2) [] = []"
| "trans_path (k\<^sub>1,k\<^sub>2) ((i,j)#xs) = (i+k\<^sub>1,j+k\<^sub>2)#(trans_path (k\<^sub>1,k\<^sub>2) xs)"

text \<open>Translate the coordinates of a board by \<open>(k\<^sub>1,k\<^sub>2)\<close>.\<close>
definition trans_board :: "int \<times> int \<Rightarrow> board \<Rightarrow> board" where 
  "trans_board t b \<equiv> (case t of (k\<^sub>1,k\<^sub>2) \<Rightarrow> {(i+k\<^sub>1,j+k\<^sub>2)|i j. (i,j) \<in> b})"

subsection \<open>Correctness of Path and Board Translation\<close>

lemma trans_path_length: "length ps = length (trans_path (k\<^sub>1,k\<^sub>2) ps)"
  by (induction ps) auto

lemma trans_path_non_nil: "ps \<noteq> [] \<Longrightarrow> trans_path (k\<^sub>1,k\<^sub>2) ps \<noteq> []"
  by (induction ps) auto

lemma trans_path_correct: "(i,j) \<in> set ps \<longleftrightarrow> (i+k\<^sub>1,j+k\<^sub>2) \<in> set (trans_path (k\<^sub>1,k\<^sub>2) ps)"
proof (induction ps)
  case (Cons s\<^sub>i ps)
  then show ?case by (cases s\<^sub>i) auto
qed auto

lemma trans_path_non_nil_last: 
  "ps \<noteq> [] \<Longrightarrow> last (trans_path (k\<^sub>1,k\<^sub>2) ps) = last (trans_path (k\<^sub>1,k\<^sub>2) ((i,j)#ps))"
  using trans_path_non_nil by (induction ps) auto

lemma hd_trans_path:
  assumes "ps \<noteq> []" "hd ps = (i,j)"
  shows "hd (trans_path (k\<^sub>1,k\<^sub>2) ps) = (i+k\<^sub>1,j+k\<^sub>2)"
  using assms by (induction ps) auto

lemma last_trans_path:
  assumes "ps \<noteq> []" "last ps = (i,j)"
  shows "last (trans_path (k\<^sub>1,k\<^sub>2) ps) = (i+k\<^sub>1,j+k\<^sub>2)"
  using assms
proof (induction ps)
  case (Cons s\<^sub>i ps)
  then show ?case 
    using trans_path_non_nil_last[symmetric] 
    apply (cases s\<^sub>i) 
    apply (cases "ps = []")
    apply auto
    done
qed (auto)

lemma take_trans: 
  shows "take k (trans_path (k\<^sub>1,k\<^sub>2) ps) = trans_path (k\<^sub>1,k\<^sub>2) (take k ps)"
proof (induction ps arbitrary: k)
  case Nil
  then show ?case by auto
next
  case (Cons s\<^sub>i ps)
  then obtain i j where "s\<^sub>i = (i,j)" by force
  then have "k = 0 \<or> k > 0" by auto
  then show ?case 
  proof (elim disjE)
    assume "k > 0"
    then show ?thesis using Cons.IH by (auto simp: \<open>s\<^sub>i = (i,j)\<close> take_Cons')
  qed auto
qed

lemma drop_trans: 
  shows "drop k (trans_path (k\<^sub>1,k\<^sub>2) ps) = trans_path (k\<^sub>1,k\<^sub>2) (drop k ps)"
proof (induction ps arbitrary: k)
  case Nil
  then show ?case by auto
next
  case (Cons s\<^sub>i ps)
  then obtain i j where "s\<^sub>i = (i,j)" by force
  then have "k = 0 \<or> k > 0" by auto
  then show ?case 
  proof (elim disjE)
    assume "k > 0"
    then show ?thesis using Cons.IH by (auto simp: \<open>s\<^sub>i = (i,j)\<close> drop_Cons')
  qed auto
qed

lemma trans_board_correct: "(i,j) \<in> b \<longleftrightarrow> (i+k\<^sub>1,j+k\<^sub>2) \<in> trans_board (k\<^sub>1,k\<^sub>2) b"
  unfolding trans_board_def by auto

lemma board_subset: "n\<^sub>1 \<le> n\<^sub>2 \<Longrightarrow> m\<^sub>1 \<le> m\<^sub>2 \<Longrightarrow> board n\<^sub>1 m\<^sub>1 \<subseteq> board n\<^sub>2 m\<^sub>2"
  unfolding board_def by auto

text \<open>Board concatenation\<close>
corollary board_concat: 
  shows "board n m\<^sub>1 \<union> trans_board (0,int m\<^sub>1) (board n m\<^sub>2) = board n (m\<^sub>1+m\<^sub>2)" (is "?b1 \<union> ?b2 = ?b")
proof
  show "?b1 \<union> ?b2 \<subseteq> ?b" unfolding board_def trans_board_def by auto
next
  show "?b \<subseteq> ?b1 \<union> ?b2"
  proof
    fix x
    assume "x \<in> ?b"
    then obtain i j where x_split: "x = (i,j)" "1 \<le> i \<and> i \<le> int n" "1 \<le> j \<and> j \<le> int (m\<^sub>1+m\<^sub>2)" 
      unfolding board_def by auto
    then have "j \<le> int m\<^sub>1 \<or> (int m\<^sub>1 < j \<and> j \<le> int (m\<^sub>1+m\<^sub>2))" by auto
    then show "x \<in> ?b1 \<union> ?b2"
    proof
      assume "j \<le> int m\<^sub>1"
      then show "x \<in> ?b1 \<union> ?b2" using x_split unfolding board_def by auto
    next
      assume asm: "int m\<^sub>1 < j \<and> j \<le> int (m\<^sub>1+m\<^sub>2)"
      then have "(i,j-int m\<^sub>1) \<in> board n m\<^sub>2" using x_split unfolding board_def by auto
      then show "x \<in> ?b1 \<union> ?b2" 
        using x_split asm trans_board_correct[of i "j-int m\<^sub>1" "board n m\<^sub>2" 0 "int m\<^sub>1"] by auto
    qed
  qed
qed

lemma transpose_trans_board: 
  "transpose_board (trans_board (k\<^sub>1,k\<^sub>2) b) = trans_board (k\<^sub>2,k\<^sub>1) (transpose_board b)"
  unfolding transpose_board_def trans_board_def by blast

corollary board_concatT: 
  shows "board n\<^sub>1 m \<union> trans_board (int n\<^sub>1,0) (board n\<^sub>2 m) = board (n\<^sub>1+n\<^sub>2) m" (is "?b\<^sub>1 \<union> ?b\<^sub>2 = ?b")
proof -
  let ?b\<^sub>1T="board m n\<^sub>1"
  let ?b\<^sub>2T="trans_board (0,int n\<^sub>1) (board m n\<^sub>2)"
  have "?b\<^sub>1 \<union> ?b\<^sub>2 = transpose_board (?b\<^sub>1T \<union> ?b\<^sub>2T) "
    using transpose_board2 transpose_union transpose_board transpose_trans_board by auto
  also have "... = transpose_board (board m (n\<^sub>1+n\<^sub>2))"
    using board_concat by auto
  also have "... = board (n\<^sub>1+n\<^sub>2) m"
    using transpose_board by auto
  finally show ?thesis .
qed

lemma trans_valid_step: 
  "valid_step (i,j) (i',j') \<Longrightarrow> valid_step (i+k\<^sub>1,j+k\<^sub>2) (i'+k\<^sub>1,j'+k\<^sub>2)"
  unfolding valid_step_def by auto

text \<open>Translating a path and a boards preserves the validity.\<close>
lemma trans_knights_path:
  assumes "knights_path b ps"
  shows "knights_path (trans_board (k\<^sub>1,k\<^sub>2) b) (trans_path (k\<^sub>1,k\<^sub>2) ps)"
  using assms
proof (induction rule: knights_path.induct)
  case (2 s\<^sub>i b s\<^sub>j xs)
  then obtain i j i' j' where split: "s\<^sub>i = (i,j)" "s\<^sub>j = (i',j')" by force
  let ?s\<^sub>i="(i+k\<^sub>1,j+k\<^sub>2)"
  let ?s\<^sub>j="(i'+k\<^sub>1,j'+k\<^sub>2)"
  let ?xs="trans_path (k\<^sub>1,k\<^sub>2) xs"
  let ?b="trans_board (k\<^sub>1,k\<^sub>2) b"
  have simps: "trans_path (k\<^sub>1,k\<^sub>2) (s\<^sub>i#s\<^sub>j#xs) = ?s\<^sub>i#?s\<^sub>j#?xs" 
              "?b \<union> {?s\<^sub>i} = trans_board (k\<^sub>1,k\<^sub>2) (b \<union> {s\<^sub>i})"
    unfolding trans_board_def using split by auto
  have "?s\<^sub>i \<notin> ?b" "valid_step ?s\<^sub>i ?s\<^sub>j" "knights_path ?b (?s\<^sub>j#?xs)"
    using 2 split trans_valid_step by (auto simp: trans_board_def)
  then have "knights_path (?b \<union> {?s\<^sub>i}) (?s\<^sub>i#?s\<^sub>j#?xs)"
    using knights_path.intros by auto
  then show ?case using simps by auto
qed (auto simp: trans_board_def intro: knights_path.intros)

text \<open>Predicate that indicates if two squares \<open>s\<^sub>i\<close> and \<open>s\<^sub>j\<close> are adjacent in \<open>ps\<close>.\<close>
definition step_in :: "path \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "step_in ps s\<^sub>i s\<^sub>j \<equiv> (\<exists>k. 0 < k \<and> k < length ps \<and> last (take k ps) = s\<^sub>i \<and> hd (drop k ps) = s\<^sub>j)"

lemma step_in_Cons: "step_in ps s\<^sub>i s\<^sub>j \<Longrightarrow> step_in (s\<^sub>k#ps) s\<^sub>i s\<^sub>j"
proof -
  assume "step_in ps s\<^sub>i s\<^sub>j"
  then obtain k where "0 < k \<and> k < length ps" "last (take k ps) = s\<^sub>i" "hd (drop k ps) = s\<^sub>j"
    unfolding step_in_def by auto 
  then have "0 < k+1 \<and> k+1 < length (s\<^sub>k#ps)" 
      "last (take (k+1) (s\<^sub>k#ps)) = s\<^sub>i" "hd (drop (k+1) (s\<^sub>k#ps)) = s\<^sub>j"
    by auto
  then show ?thesis
    by (auto simp: step_in_def)
qed

lemma step_in_append: "step_in ps s\<^sub>i s\<^sub>j \<Longrightarrow> step_in (ps@ps') s\<^sub>i s\<^sub>j"
proof -
  assume "step_in ps s\<^sub>i s\<^sub>j"
  then obtain k where "0 < k \<and> k < length ps" "last (take k ps) = s\<^sub>i" "hd (drop k ps) = s\<^sub>j"
    unfolding step_in_def by auto 
  then have "0 < k \<and> k < length (ps@ps')" 
      "last (take k (ps@ps')) = s\<^sub>i" "hd (drop k (ps@ps')) = s\<^sub>j"
    by auto
  then show ?thesis
    by (auto simp: step_in_def)
qed

lemma step_in_prepend: "step_in ps s\<^sub>i s\<^sub>j \<Longrightarrow> step_in (ps'@ps) s\<^sub>i s\<^sub>j"
  using step_in_Cons by (induction ps' arbitrary: ps) auto

lemma step_in_valid_step: "knights_path b ps \<Longrightarrow> step_in ps s\<^sub>i s\<^sub>j \<Longrightarrow> valid_step s\<^sub>i s\<^sub>j"
proof -
  assume assms: "knights_path b ps" "step_in ps s\<^sub>i s\<^sub>j"
  then obtain k where k_prems: "0 < k \<and> k < length ps" "last (take k ps) = s\<^sub>i" "hd (drop k ps) = s\<^sub>j"
    unfolding step_in_def by auto
  then have "k = 1 \<or> k > 1" by auto
  then show ?thesis
  proof (elim disjE)
    assume "k = 1"
    then obtain ps' where "ps = s\<^sub>i#s\<^sub>j#ps'"
      using k_prems list_len_g_1_split by fastforce
    then show ?thesis
      using assms by (auto elim: knights_path.cases)
  next
    assume "k > 1"
    then have "0 < k-1 \<and> k-1 < length ps"
      using k_prems by auto
    then obtain b where "knights_path b (drop (k-1) ps)"
      using assms knights_path_split by blast

    obtain ps' where "drop (k-1) ps = s\<^sub>i#s\<^sub>j#ps'"
      using k_prems \<open>0 < k - 1 \<and> k - 1 < length ps\<close>
      by (metis Cons_nth_drop_Suc Suc_diff_1 hd_drop_conv_nth last_snoc take_hd_drop)
    then show ?thesis
      using \<open>knights_path b (drop (k-1) ps)\<close> by (auto elim: knights_path.cases)
  qed
qed

lemma trans_step_in: 
  "step_in ps (i,j) (i',j') \<Longrightarrow> step_in (trans_path (k\<^sub>1,k\<^sub>2) ps) (i+k\<^sub>1,j+k\<^sub>2) (i'+k\<^sub>1,j'+k\<^sub>2)"
proof -
  let ?ps'="trans_path (k\<^sub>1,k\<^sub>2) ps"
  assume "step_in ps (i,j) (i',j')"
  then obtain k where "0 < k \<and> k < length ps" "last (take k ps) = (i,j)" "hd (drop k ps) = (i',j')"
    unfolding step_in_def by auto
  then have "take k ps \<noteq> []" "drop k ps \<noteq> []" by fastforce+
  then have "0 < k \<and> k < length ?ps'" 
      "last (take k ?ps') = (i+k\<^sub>1,j+k\<^sub>2)" "hd (drop k ?ps') = (i'+k\<^sub>1,j'+k\<^sub>2)"
    using trans_path_length
          last_trans_path[OF \<open>take k ps \<noteq> []\<close> \<open>last (take k ps) = (i,j)\<close>] take_trans 
          hd_trans_path[OF \<open>drop k ps \<noteq> []\<close> \<open>hd (drop k ps) = (i',j')\<close>] drop_trans
    by auto
  then show ?thesis
    by (auto simp: step_in_def) 
qed

lemma transpose_step_in: 
  "step_in ps s\<^sub>i s\<^sub>j \<Longrightarrow> step_in (transpose ps) (transpose_square s\<^sub>i) (transpose_square s\<^sub>j)"
  (is "_ \<Longrightarrow> step_in ?psT ?s\<^sub>iT ?s\<^sub>jT")
proof -
  assume "step_in ps s\<^sub>i s\<^sub>j"
  then obtain k where 
      k_prems: "0 < k" "k < length ps" "last (take k ps) = s\<^sub>i" "hd (drop k ps) = s\<^sub>j"
    unfolding step_in_def by auto
  then have non_nil: "take k ps \<noteq> []" "drop k ps \<noteq> []" by fastforce+
  have "take k ?psT = transpose (take k ps)" "drop k ?psT = transpose (drop k ps)"
    using take_transpose drop_transpose by auto
  then have "last (take k ?psT) = ?s\<^sub>iT" "hd (drop k ?psT) = ?s\<^sub>jT"
    using non_nil k_prems hd_transpose last_transpose by auto
  then show "step_in ?psT ?s\<^sub>iT ?s\<^sub>jT"
    unfolding step_in_def using k_prems transpose_length by auto
qed
  
lemma hd_take: "0 < k \<Longrightarrow> hd xs = hd (take k xs)"
  by (induction xs) auto

lemma last_drop: "k < length xs \<Longrightarrow> last xs = last (drop k xs)"
  by (induction xs) auto

subsection \<open>Concatenate Knight's Paths and Circuits\<close>

text \<open>Concatenate two knight's path on a \<open>n\<times>m\<close>-board along the 2nd axis if the first path contains
the step \<open>s\<^sub>i \<rightarrow> s\<^sub>j\<close> and there are valid steps \<open>s\<^sub>i \<rightarrow> hd ps\<^sub>2'\<close> and \<open>s\<^sub>j \<rightarrow> last ps\<^sub>2'\<close>, where 
\<open>ps\<^sub>2'\<close> is \<open>ps\<^sub>2\<close> is translated by \<open>m\<^sub>1\<close>. An arbitrary step in \<open>ps\<^sub>2\<close> is preserved.\<close>
corollary knights_path_split_concat_si_prev:
  assumes "knights_path (board n m\<^sub>1) ps\<^sub>1" "knights_path (board n m\<^sub>2) ps\<^sub>2" 
          "step_in ps\<^sub>1 s\<^sub>i s\<^sub>j" "hd ps\<^sub>2 = (i\<^sub>h,j\<^sub>h)" "last ps\<^sub>2 = (i\<^sub>l,j\<^sub>l)" "step_in ps\<^sub>2 (i,j) (i',j')"
          "valid_step s\<^sub>i (i\<^sub>h,int m\<^sub>1+j\<^sub>h)" "valid_step (i\<^sub>l,int m\<^sub>1+j\<^sub>l) s\<^sub>j"
  shows "\<exists>ps. knights_path (board n (m\<^sub>1+m\<^sub>2)) ps \<and> hd ps = hd ps\<^sub>1  
    \<and> last ps = last ps\<^sub>1 \<and> step_in ps (i,int m\<^sub>1+j) (i',int m\<^sub>1+j')"
  using assms
proof -
  let ?b\<^sub>1="board n m\<^sub>1"
  let ?b\<^sub>2="board n m\<^sub>2"
  let ?ps\<^sub>2'="trans_path (0,int m\<^sub>1) ps\<^sub>2"
  let ?b'="trans_board (0,int m\<^sub>1) ?b\<^sub>2"
  have kp2': "knights_path ?b' ?ps\<^sub>2'" using assms trans_knights_path by auto
  then have "?ps\<^sub>2' \<noteq> []" using knights_path_non_nil by auto

  obtain k where k_prems: 
    "0 < k" "k < length ps\<^sub>1" "last (take k ps\<^sub>1) = s\<^sub>i" "hd (drop k ps\<^sub>1) = s\<^sub>j"
    using assms unfolding step_in_def by auto
  let ?ps="(take k ps\<^sub>1) @ ?ps\<^sub>2' @ (drop k ps\<^sub>1)"
  obtain b\<^sub>1 b\<^sub>2 where b_prems: "knights_path b\<^sub>1 (take k ps\<^sub>1)" "knights_path b\<^sub>2 (drop k ps\<^sub>1)" 
      "b\<^sub>1 \<union> b\<^sub>2 = ?b\<^sub>1" "b\<^sub>1 \<inter> b\<^sub>2 = {}"
    using assms \<open>0 < k\<close> \<open>k < length ps\<^sub>1\<close> knights_path_split by blast

  have "hd ?ps\<^sub>2' = (i\<^sub>h,int m\<^sub>1+j\<^sub>h)" "last ?ps\<^sub>2' = (i\<^sub>l,int m\<^sub>1+j\<^sub>l)"
    using assms knights_path_non_nil hd_trans_path last_trans_path by auto
  then have "hd ?ps\<^sub>2' = (i\<^sub>h,int m\<^sub>1+j\<^sub>h)" "last ((take k ps\<^sub>1) @ ?ps\<^sub>2') = (i\<^sub>l,int m\<^sub>1+j\<^sub>l)"
    using \<open>?ps\<^sub>2' \<noteq> []\<close> by auto
  then have vs: "valid_step (last (take k ps\<^sub>1)) (hd ?ps\<^sub>2')" 
      "valid_step (last ((take k ps\<^sub>1) @ ?ps\<^sub>2')) (hd (drop k ps\<^sub>1))"
    using assms k_prems by auto

  have "?b\<^sub>1 \<inter> ?b' = {}" unfolding board_def trans_board_def by auto
  then have "b\<^sub>1 \<inter> ?b' = {} \<and> (b\<^sub>1 \<union> ?b') \<inter> b\<^sub>2 = {}" using b_prems by blast
  then have inter_empty: "b\<^sub>1 \<inter> ?b' = {}" "(b\<^sub>1 \<union> ?b') \<inter> b\<^sub>2 = {}" by auto

  have "knights_path (b\<^sub>1 \<union> ?b') ((take k ps\<^sub>1) @ ?ps\<^sub>2')"
    using kp2' b_prems inter_empty vs knights_path_append by auto
  then have "knights_path (b\<^sub>1 \<union> ?b' \<union> b\<^sub>2) ?ps"
    using b_prems inter_empty vs knights_path_append[where ps\<^sub>1="(take k ps\<^sub>1) @ ?ps\<^sub>2'"] by auto
  then have "knights_path (?b\<^sub>1 \<union> ?b') ?ps" 
    using b_prems Un_commute Un_assoc by metis
  then have kp: "knights_path (board n (m\<^sub>1+m\<^sub>2)) ?ps"
    using board_concat[of n m\<^sub>1 m\<^sub>2] by auto

  have hd: "hd ?ps = hd ps\<^sub>1"
    using assms \<open>0 < k\<close> knights_path_non_nil hd_take by auto

  have last: "last ?ps = last ps\<^sub>1"
    using assms \<open>k < length ps\<^sub>1\<close> knights_path_non_nil last_drop by auto

  have m_simps: "j+int m\<^sub>1 = int m\<^sub>1+j" "j'+int m\<^sub>1 = int m\<^sub>1+j'" by auto
  have si: "step_in ?ps (i,int m\<^sub>1+j) (i',int m\<^sub>1+j')"
    using assms step_in_append[OF step_in_prepend[OF trans_step_in], 
                  of ps\<^sub>2 i j i' j' "take k ps\<^sub>1" 0 "int m\<^sub>1" "drop k ps\<^sub>1"] 
    by (auto simp: m_simps)
  
  show ?thesis using kp hd last si by auto
qed

lemma len1_hd_last: "length xs = 1 \<Longrightarrow> hd xs = last xs"
  by (induction xs) auto

text \<open>Weaker version of @{thm knights_path_split_concat_si_prev}.\<close>
corollary knights_path_split_concat:
  assumes "knights_path (board n m\<^sub>1) ps\<^sub>1" "knights_path (board n m\<^sub>2) ps\<^sub>2" 
          "step_in ps\<^sub>1 s\<^sub>i s\<^sub>j" "hd ps\<^sub>2 = (i\<^sub>h,j\<^sub>h)" "last ps\<^sub>2 = (i\<^sub>l,j\<^sub>l)"
          "valid_step s\<^sub>i (i\<^sub>h,int m\<^sub>1+j\<^sub>h)" "valid_step (i\<^sub>l,int m\<^sub>1+j\<^sub>l) s\<^sub>j"
  shows "\<exists>ps. knights_path (board n (m\<^sub>1+m\<^sub>2)) ps \<and> hd ps = hd ps\<^sub>1 \<and> last ps = last ps\<^sub>1"
proof -
  have "length ps\<^sub>2 = 1 \<or> length ps\<^sub>2 > 1"
    using assms knights_path_non_nil by (meson length_0_conv less_one linorder_neqE_nat)
  then show ?thesis
  proof (elim disjE)
    let ?s\<^sub>k="(i\<^sub>h,int m\<^sub>1+j\<^sub>h)"
    assume "length ps\<^sub>2 = 1"
    (* contradiction *)
    then have "(i\<^sub>h,j\<^sub>h) = (i\<^sub>l,j\<^sub>l)"
      using assms len1_hd_last by metis
    then have "valid_step s\<^sub>i ?s\<^sub>k" "valid_step ?s\<^sub>k s\<^sub>j" "valid_step s\<^sub>i s\<^sub>j"
      using assms step_in_valid_step by auto
    then show ?thesis
      using valid_step_non_transitive by blast
  next
    assume "length ps\<^sub>2 > 1"
    then obtain i\<^sub>1 j\<^sub>1 i\<^sub>2 j\<^sub>2 ps\<^sub>2' where "ps\<^sub>2 = (i\<^sub>1,j\<^sub>1)#(i\<^sub>2,j\<^sub>2)#ps\<^sub>2'"
      using list_len_g_1_split by fastforce
    then have "last (take 1 ps\<^sub>2) = (i\<^sub>1,j\<^sub>1)" "hd (drop 1 ps\<^sub>2) = (i\<^sub>2,j\<^sub>2)" by auto
    then have "step_in ps\<^sub>2 (i\<^sub>1,j\<^sub>1) (i\<^sub>2,j\<^sub>2)" using \<open>length ps\<^sub>2 > 1\<close> by (auto simp: step_in_def)
    then show ?thesis
      using assms knights_path_split_concat_si_prev by blast
  qed
qed

text \<open>Concatenate two knight's path on a \<open>n\<times>m\<close>-board along the 1st axis.\<close>
corollary knights_path_split_concatT:
  assumes "knights_path (board n\<^sub>1 m) ps\<^sub>1" "knights_path (board n\<^sub>2 m) ps\<^sub>2" 
          "step_in ps\<^sub>1 s\<^sub>i s\<^sub>j" "hd ps\<^sub>2 = (i\<^sub>h,j\<^sub>h)" "last ps\<^sub>2 = (i\<^sub>l,j\<^sub>l)"
          "valid_step s\<^sub>i (int n\<^sub>1+i\<^sub>h,j\<^sub>h)" "valid_step (int n\<^sub>1+i\<^sub>l,j\<^sub>l) s\<^sub>j"
  shows "\<exists>ps. knights_path (board (n\<^sub>1+n\<^sub>2) m) ps \<and> hd ps = hd ps\<^sub>1 \<and> last ps = last ps\<^sub>1"
  using assms
proof -
  let ?ps\<^sub>1T="transpose ps\<^sub>1"
  let ?ps\<^sub>2T="transpose ps\<^sub>2"
  have kps: "knights_path (board m n\<^sub>1) ?ps\<^sub>1T" "knights_path (board m n\<^sub>2) ?ps\<^sub>2T"
    using assms transpose_knights_path by auto

  let ?s\<^sub>iT="transpose_square s\<^sub>i"
  let ?s\<^sub>jT="transpose_square s\<^sub>j"
  have si: "step_in ?ps\<^sub>1T ?s\<^sub>iT ?s\<^sub>jT"
    using assms transpose_step_in by auto

  have "ps\<^sub>1 \<noteq> []" "ps\<^sub>2 \<noteq> []"
    using assms knights_path_non_nil by auto
  then have hd_last2: "hd ?ps\<^sub>2T = (j\<^sub>h,i\<^sub>h)" "last ?ps\<^sub>2T = (j\<^sub>l,i\<^sub>l)"
    using assms hd_transpose last_transpose by (auto simp: transpose_square_def)

  have vs: "valid_step ?s\<^sub>iT (j\<^sub>h,int n\<^sub>1+i\<^sub>h)" "valid_step (j\<^sub>l,int n\<^sub>1+i\<^sub>l) ?s\<^sub>jT"
    using assms transpose_valid_step by (auto simp: transpose_square_def split: prod.splits)

  then obtain ps where 
    ps_prems: "knights_path (board m (n\<^sub>1+n\<^sub>2)) ps" "hd ps = hd ?ps\<^sub>1T" "last ps = last ?ps\<^sub>1T"
    using knights_path_split_concat[OF kps si hd_last2 vs] by auto
  then have "ps \<noteq> []" using knights_path_non_nil by auto
  let ?psT="transpose ps"
  have "knights_path (board (n\<^sub>1+n\<^sub>2) m) ?psT" "hd ?psT = hd ps\<^sub>1" "last ?psT = last ps\<^sub>1"
    using \<open>ps\<^sub>1 \<noteq> []\<close> \<open>ps \<noteq> []\<close> ps_prems transpose_knights_path hd_transpose last_transpose 
    by (auto simp: transpose2)
  then show ?thesis by auto
qed

text \<open>Concatenate two Knight's path along the 2nd axis. There is a valid step from the last square 
in the first Knight's path \<open>ps\<^sub>1\<close> to the first square in the second Knight's path \<open>ps\<^sub>2\<close>.\<close>
corollary knights_path_concat:
  assumes "knights_path (board n m\<^sub>1) ps\<^sub>1" "knights_path (board n m\<^sub>2) ps\<^sub>2" 
          "hd ps\<^sub>2 = (i\<^sub>h,j\<^sub>h)" "valid_step (last ps\<^sub>1) (i\<^sub>h,int m\<^sub>1+j\<^sub>h)"
  shows "knights_path (board n (m\<^sub>1+m\<^sub>2)) (ps\<^sub>1 @ (trans_path (0,int m\<^sub>1) ps\<^sub>2))"
proof -
  let ?ps\<^sub>2'="trans_path (0,int m\<^sub>1) ps\<^sub>2"
  let ?b="trans_board (0,int m\<^sub>1) (board n m\<^sub>2)"
  have inter_empty: "board n m\<^sub>1 \<inter> ?b = {}"
    unfolding board_def trans_board_def by auto
  have "hd ?ps\<^sub>2' = (i\<^sub>h,int m\<^sub>1+j\<^sub>h)"
    using assms knights_path_non_nil hd_trans_path by auto
  then have kp: "knights_path (board n m\<^sub>1) ps\<^sub>1" "knights_path ?b ?ps\<^sub>2'" and 
        vs: "valid_step (last ps\<^sub>1) (hd ?ps\<^sub>2')"
    using assms trans_knights_path by auto
  then show "knights_path (board n (m\<^sub>1+m\<^sub>2)) (ps\<^sub>1 @ ?ps\<^sub>2')"
    using knights_path_append[OF kp inter_empty vs] board_concat by auto
qed

text \<open>Concatenate two Knight's path along the 2nd axis. The first Knight's path end in 
\<open>(2,m\<^sub>1-1)\<close> (lower-right) and the second Knight's paths start in \<open>(1,1)\<close> (lower-left).\<close>
corollary knights_path_lr_concat:
  assumes "knights_path (board n m\<^sub>1) ps\<^sub>1" "knights_path (board n m\<^sub>2) ps\<^sub>2" 
          "last ps\<^sub>1 = (2,int m\<^sub>1-1)" "hd ps\<^sub>2 = (1,1)"
  shows "knights_path (board n (m\<^sub>1+m\<^sub>2)) (ps\<^sub>1 @ (trans_path (0,int m\<^sub>1) ps\<^sub>2))"
proof -
  have "valid_step (last ps\<^sub>1) (1,int m\<^sub>1+1)"
    using assms unfolding valid_step_def by auto
  then show ?thesis
    using assms knights_path_concat by auto
qed

text \<open>Concatenate two Knight's circuits along the 2nd axis. In the first Knight's path the 
squares \<open>(2,m\<^sub>1-1)\<close> and \<open>(4,m\<^sub>1)\<close> are adjacent and the second Knight's cirucit starts in \<open>(1,1)\<close> 
(lower-left) and end in \<open>(3,2)\<close>.\<close>
corollary knights_circuit_lr_concat:
  assumes "knights_circuit (board n m\<^sub>1) ps\<^sub>1" "knights_circuit (board n m\<^sub>2) ps\<^sub>2"
          "step_in ps\<^sub>1 (2,int m\<^sub>1-1) (4,int m\<^sub>1)" 
          "hd ps\<^sub>2 = (1,1)" "last ps\<^sub>2 = (3,2)" "step_in ps\<^sub>2 (2,int m\<^sub>2-1) (4,int m\<^sub>2)"
  shows "\<exists>ps. knights_circuit (board n (m\<^sub>1+m\<^sub>2)) ps \<and> step_in ps (2,int (m\<^sub>1+m\<^sub>2)-1) (4,int (m\<^sub>1+m\<^sub>2))"
proof -
  have kp1: "knights_path (board n m\<^sub>1) ps\<^sub>1" and kp2: "knights_path (board n m\<^sub>2) ps\<^sub>2" 
    and vs: "valid_step (last ps\<^sub>1) (hd ps\<^sub>1)"
    using assms unfolding knights_circuit_def by auto

  have m_simps: "int m\<^sub>1 + (int m\<^sub>2-1) = int (m\<^sub>1+m\<^sub>2)-1" "int m\<^sub>1 + int m\<^sub>2 = int (m\<^sub>1+m\<^sub>2)" by auto

  have "valid_step (2,int m\<^sub>1-1) (1,int m\<^sub>1+1)" "valid_step (3,int m\<^sub>1+2) (4,int m\<^sub>1)"
    unfolding valid_step_def by auto
  then obtain ps where "knights_path (board n (m\<^sub>1+m\<^sub>2)) ps" "hd ps = hd ps\<^sub>1" "last ps = last ps\<^sub>1" and 
      si: "step_in ps (2,int (m\<^sub>1+m\<^sub>2)-1) (4,int (m\<^sub>1+m\<^sub>2))"
    using assms kp1 kp2 
          knights_path_split_concat_si_prev[of n m\<^sub>1 ps\<^sub>1 m\<^sub>2 ps\<^sub>2 "(2,int m\<^sub>1-1)" 
                                              "(4,int m\<^sub>1)" 1 1 3 2 2 "int m\<^sub>2-1" 4 "int m\<^sub>2"] 
    by (auto simp only: m_simps)
  then have "knights_circuit (board n (m\<^sub>1+m\<^sub>2)) ps"
    using vs by (auto simp: knights_circuit_def)
  then show ?thesis
    using si by auto
qed

section \<open>Parsing Paths\<close>

text \<open>In this section functions are implemented to parse and construct paths. The parser converts 
the matrix representation (\<open>(nat list) list\<close>) used in \<^cite>\<open>"cull_decurtins_1987"\<close> to a path 
(\<open>path\<close>).\<close>

text \<open>for debugging\<close>
fun test_path :: "path \<Rightarrow> bool" where
  "test_path (s\<^sub>i#s\<^sub>j#xs) = (step_checker s\<^sub>i s\<^sub>j \<and> test_path (s\<^sub>j#xs))"
| "test_path _ = True"

fun f_opt :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "f_opt _ None = None"
| "f_opt f (Some a) = Some (f a)"

fun add_opt_fst_sq :: "int \<Rightarrow> square option \<Rightarrow> square option" where
  "add_opt_fst_sq _ None = None"
| "add_opt_fst_sq k (Some (i,j)) = Some (k+i,j)"

fun find_k_in_col :: "nat \<Rightarrow> nat list \<Rightarrow> int option" where
  "find_k_in_col k [] = None"
| "find_k_in_col k (c#cs) = (if c = k then Some 1 else f_opt ((+) 1) (find_k_in_col k cs))"

fun find_k_sqr :: "nat \<Rightarrow> (nat list) list \<Rightarrow> square option" where
  "find_k_sqr k [] = None"
| "find_k_sqr k (r#rs) = (case find_k_in_col k r of 
      None \<Rightarrow> f_opt (\<lambda>(i,j). (i+1,j)) (find_k_sqr k rs)
    | Some j \<Rightarrow> Some (1,j))"

text \<open>Auxiliary function to easily parse pre-computed boards from paper.\<close>
fun to_sqrs :: "nat \<Rightarrow> (nat list) list \<Rightarrow> path option" where
  "to_sqrs 0 rs = Some []"
| "to_sqrs k rs = (case find_k_sqr k rs of
      None \<Rightarrow> None
    | Some s\<^sub>i \<Rightarrow> f_opt (\<lambda>ps. ps@[s\<^sub>i]) (to_sqrs (k-1) rs))"

fun num_elems :: "(nat list) list \<Rightarrow> nat" where
  "num_elems (r#rs) = length r * length (r#rs)"

text \<open>Convert a matrix (\<open>nat list list\<close>) to a path (\<open>path\<close>). With this function we implicitly 
define the lower-left corner to be \<open>(1,1)\<close> and the upper-right corner to be \<open>(n,m)\<close>.\<close>
definition "to_path rs \<equiv> to_sqrs (num_elems rs) (rev rs)"

text \<open>Example\<close>
value "to_path 
  [[3,22,13,16,5],
  [12,17,4,21,14],
  [23,2,15,6,9],
  [18,11,8,25,20],
  [1,24,19,10,7::nat]]"

section \<open>Knight's Paths for \<open>5\<times>m\<close>-Boards\<close>

text \<open>Given here are knight's paths, \<open>kp5xmlr\<close> and \<open>kp5xmur\<close>, for the \<open>(5\<times>m)\<close>-board that start 
in the lower-left corner for \<open>m\<in>{5,6,7,8,9}\<close>. The path \<open>kp5xmlr\<close> ends in the lower-right corner, 
whereas the path \<open>kp5xmur\<close> ends in the upper-right corner. 
The tables show the visited squares numbered in ascending order.\<close>

abbreviation "b5x5 \<equiv> board 5 5"

text \<open>A Knight's path for the \<open>(5\<times>5)\<close>-board that starts in the lower-left and ends in the 
lower-right.
  \begin{table}[H]
    \begin{tabular}{lllll}
       3 & 22 & 13 & 16 &  5 \\
      12 & 17 &  4 & 21 & 14 \\
      23 &  2 & 15 &  6 &  9 \\
      18 & 11 &  8 & 25 & 20 \\
       1 & 24 & 19 & 10 &  7
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x5lr \<equiv> the (to_path 
  [[3,22,13,16,5],
  [12,17,4,21,14],
  [23,2,15,6,9],
  [18,11,8,25,20],
  [1,24,19,10,7]])"
lemma kp_5x5_lr: "knights_path b5x5 kp5x5lr"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x5_lr_hd: "hd kp5x5lr = (1,1)" by eval

lemma kp_5x5_lr_last: "last kp5x5lr = (2,4)" by eval

lemma kp_5x5_lr_non_nil: "kp5x5lr \<noteq> []" by eval

text \<open>A Knight's path for the \<open>(5\<times>5)\<close>-board that starts in the lower-left and ends in the 
upper-right.
  \begin{table}[H]
    \begin{tabular}{lllll}
       7 & 12 & 15 & 20 &  5 \\
      16 & 21 &  6 & 25 & 14 \\
      11 &  8 & 13 &  4 & 19 \\
      22 & 17 &  2 &  9 & 24 \\
       1 & 10 & 23 & 18 &  3
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x5ur \<equiv> the (to_path 
  [[7,12,15,20,5],
  [16,21,6,25,14],
  [11,8,13,4,19],
  [22,17,2,9,24],
  [1,10,23,18,3]])"
lemma kp_5x5_ur: "knights_path b5x5 kp5x5ur"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x5_ur_hd: "hd kp5x5ur = (1,1)" by eval

lemma kp_5x5_ur_last: "last kp5x5ur = (4,4)" by eval

lemma kp_5x5_ur_non_nil: "kp5x5ur \<noteq> []" by eval

abbreviation "b5x6 \<equiv> board 5 6"

text \<open>A Knight's path for the \<open>(5\<times>6)\<close>-board that starts in the lower-left and ends in the 
lower-right.
  \begin{table}[H]
    \begin{tabular}{llllll}
       7 & 14 & 21 & 28 &  5 & 12 \\
      22 & 27 &  6 & 13 & 20 & 29 \\
      15 &  8 & 17 & 24 & 11 &  4 \\
      26 & 23 &  2 &  9 & 30 & 19 \\
       1 & 16 & 25 & 18 &  3 & 10
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x6lr \<equiv> the (to_path 
  [[7,14,21,28,5,12],
  [22,27,6,13,20,29],
  [15,8,17,24,11,4],
  [26,23,2,9,30,19],
  [1,16,25,18,3,10]])"
lemma kp_5x6_lr: "knights_path b5x6 kp5x6lr"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x6_lr_hd: "hd kp5x6lr = (1,1)" by eval

lemma kp_5x6_lr_last: "last kp5x6lr = (2,5)" by eval

lemma kp_5x6_lr_non_nil: "kp5x6lr \<noteq> []" by eval

text \<open>A Knight's path for the \<open>(5\<times>6)\<close>-board that starts in the lower-left and ends in the 
upper-right.
  \begin{table}[H]
    \begin{tabular}{llllll}
       3 & 10 & 29 & 20 &  5 & 12 \\
      28 & 19 &  4 & 11 & 30 & 21 \\
       9 &  2 & 17 & 24 & 13 &  6 \\
      18 & 27 &  8 & 15 & 22 & 25 \\
       1 & 16 & 23 & 26 &  7 & 14
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x6ur \<equiv> the (to_path 
  [[3,10,29,20,5,12],
  [28,19,4,11,30,21],
  [9,2,17,24,13,6],
  [18,27,8,15,22,25],
  [1,16,23,26,7,14]])"
lemma kp_5x6_ur: "knights_path b5x6 kp5x6ur"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x6_ur_hd: "hd kp5x6ur = (1,1)" by eval

lemma kp_5x6_ur_last: "last kp5x6ur = (4,5)" by eval

lemma kp_5x6_ur_non_nil: "kp5x6ur \<noteq> []" by eval

abbreviation "b5x7 \<equiv> board 5 7"

text \<open>A Knight's path for the \<open>(5\<times>7)\<close>-board that starts in the lower-left and ends in the 
lower-right.
  \begin{table}[H]
    \begin{tabular}{lllllll}
       3 & 12 & 21 & 30 &  5 & 14 & 23 \\
      20 & 29 &  4 & 13 & 22 & 31 &  6 \\
      11 &  2 & 19 & 32 &  7 & 24 & 15 \\
      28 & 33 & 10 & 17 & 26 & 35 &  8 \\
       1 & 18 & 27 & 34 &  9 & 16 & 25
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x7lr \<equiv> the (to_path 
  [[3,12,21,30,5,14,23],
  [20,29,4,13,22,31,6],
  [11,2,19,32,7,24,15],
  [28,33,10,17,26,35,8],
  [1,18,27,34,9,16,25]])"
lemma kp_5x7_lr: "knights_path b5x7 kp5x7lr"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x7_lr_hd: "hd kp5x7lr = (1,1)" by eval

lemma kp_5x7_lr_last: "last kp5x7lr = (2,6)" by eval

lemma kp_5x7_lr_non_nil: "kp5x7lr \<noteq> []" by eval

text \<open>A Knight's path for the \<open>(5\<times>7)\<close>-board that starts in the lower-left and ends in the 
upper-right.
  \begin{table}[H]
    \begin{tabular}{lllllll}
       3 & 32 & 11 & 34 &  5 & 26 & 13 \\
      10 & 19 &  4 & 25 & 12 & 35 &  6 \\
      31 &  2 & 33 & 20 & 23 & 14 & 27 \\
      18 &  9 & 24 & 29 & 16 &  7 & 22 \\
       1 & 30 & 17 &  8 & 21 & 28 & 15
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x7ur \<equiv> the (to_path 
  [[3,32,11,34,5,26,13],
  [10,19,4,25,12,35,6],
  [31,2,33,20,23,14,27],
  [18,9,24,29,16,7,22],
  [1,30,17,8,21,28,15]])"
lemma kp_5x7_ur: "knights_path b5x7 kp5x7ur"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x7_ur_hd: "hd kp5x7ur = (1,1)" by eval

lemma kp_5x7_ur_last: "last kp5x7ur = (4,6)" by eval

lemma kp_5x7_ur_non_nil: "kp5x7ur \<noteq> []" by eval

abbreviation "b5x8 \<equiv> board 5 8"

text \<open>A Knight's path for the \<open>(5\<times>8)\<close>-board that starts in the lower-left and ends in the 
lower-right.
  \begin{table}[H]
    \begin{tabular}{llllllll}
       3 & 12 & 37 & 26 &  5 & 14 & 17 & 28 \\
      34 & 23 &  4 & 13 & 36 & 27 &  6 & 15 \\
      11 &  2 & 35 & 38 & 25 & 16 & 29 & 18 \\
      22 & 33 & 24 &  9 & 20 & 31 & 40 &  7 \\
       1 & 10 & 21 & 32 & 39 &  8 & 19 & 30
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x8lr \<equiv> the (to_path 
  [[3,12,37,26,5,14,17,28],
  [34,23,4,13,36,27,6,15],
  [11,2,35,38,25,16,29,18],
  [22,33,24,9,20,31,40,7],
  [1,10,21,32,39,8,19,30]])"
lemma kp_5x8_lr: "knights_path b5x8 kp5x8lr"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x8_lr_hd: "hd kp5x8lr = (1,1)" by eval

lemma kp_5x8_lr_last: "last kp5x8lr = (2,7)" by eval

lemma kp_5x8_lr_non_nil: "kp5x8lr \<noteq> []" by eval

text \<open>A Knight's path for the \<open>(5\<times>8)\<close>-board that starts in the lower-left and ends in the 
upper-right.
  \begin{table}[H]
    \begin{tabular}{llllllll}
      33 &  8 & 17 & 38 & 35 &  6 & 15 & 24 \\
      18 & 37 & 34 &  7 & 16 & 25 & 40 &  5 \\
       9 & 32 & 29 & 36 & 39 & 14 & 23 & 26 \\
      30 & 19 &  2 & 11 & 28 & 21 &  4 & 13 \\
       1 & 10 & 31 & 20 &  3 & 12 & 27 & 22
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x8ur \<equiv> the (to_path 
  [[33,8,17,38,35,6,15,24],
  [18,37,34,7,16,25,40,5],
  [9,32,29,36,39,14,23,26],
  [30,19,2,11,28,21,4,13],
  [1,10,31,20,3,12,27,22]])"
lemma kp_5x8_ur: "knights_path b5x8 kp5x8ur"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x8_ur_hd: "hd kp5x8ur = (1,1)" by eval

lemma kp_5x8_ur_last: "last kp5x8ur = (4,7)" by eval

lemma kp_5x8_ur_non_nil: "kp5x8ur \<noteq> []" by eval

abbreviation "b5x9 \<equiv> board 5 9"

text \<open>
  A Knight's path for the \<open>(5\<times>9)\<close>-board that starts in the lower-left and ends in the lower-right.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
       9 &  4 & 11 & 16 & 23 & 42 & 33 & 36 & 25 \\
      12 & 17 &  8 &  3 & 32 & 37 & 24 & 41 & 34 \\
       5 & 10 & 15 & 20 & 43 & 22 & 35 & 26 & 29 \\
      18 & 13 &  2 &  7 & 38 & 31 & 28 & 45 & 40 \\
       1 &  6 & 19 & 14 & 21 & 44 & 39 & 30 & 27
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x9lr \<equiv> the (to_path 
  [[9,4,11,16,23,42,33,36,25],
  [12,17,8,3,32,37,24,41,34],
  [5,10,15,20,43,22,35,26,29],
  [18,13,2,7,38,31,28,45,40],
  [1,6,19,14,21,44,39,30,27]])"
lemma kp_5x9_lr: "knights_path b5x9 kp5x9lr"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x9_lr_hd: "hd kp5x9lr = (1,1)" by eval

lemma kp_5x9_lr_last: "last kp5x9lr = (2,8)" by eval

lemma kp_5x9_lr_non_nil: "kp5x9lr \<noteq> []" by eval

text \<open>
  A Knight's path for the \<open>(5\<times>9)\<close>-board that starts in the lower-left and ends in the upper-right.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
       9 &  4 & 11 & 16 & 27 & 32 & 35 & 40 & 25 \\
      12 & 17 &  8 &  3 & 36 & 41 & 26 & 45 & 34 \\
       5 & 10 & 15 & 20 & 31 & 28 & 33 & 24 & 39 \\
      18 & 13 &  2 &  7 & 42 & 37 & 22 & 29 & 44 \\
       1 &  6 & 19 & 14 & 21 & 30 & 43 & 38 & 23
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x9ur \<equiv> the (to_path 
  [[9,4,11,16,27,32,35,40,25],
  [12,17,8,3,36,41,26,45,34],
  [5,10,15,20,31,28,33,24,39],
  [18,13,2,7,42,37,22,29,44],
  [1,6,19,14,21,30,43,38,23]])"
lemma kp_5x9_ur: "knights_path b5x9 kp5x9ur"
  by (simp only: knights_path_exec_simp) eval

lemma kp_5x9_ur_hd: "hd kp5x9ur = (1,1)" by eval

lemma kp_5x9_ur_last: "last kp5x9ur = (4,8)" by eval

lemma kp_5x9_ur_non_nil: "kp5x9ur \<noteq> []" by eval

lemmas kp_5xm_lr = 
  kp_5x5_lr kp_5x5_lr_hd kp_5x5_lr_last kp_5x5_lr_non_nil
  kp_5x6_lr kp_5x6_lr_hd kp_5x6_lr_last kp_5x6_lr_non_nil
  kp_5x7_lr kp_5x7_lr_hd kp_5x7_lr_last kp_5x7_lr_non_nil
  kp_5x8_lr kp_5x8_lr_hd kp_5x8_lr_last kp_5x8_lr_non_nil
  kp_5x9_lr kp_5x9_lr_hd kp_5x9_lr_last kp_5x9_lr_non_nil

lemmas kp_5xm_ur = 
  kp_5x5_ur kp_5x5_ur_hd kp_5x5_ur_last kp_5x5_ur_non_nil
  kp_5x6_ur kp_5x6_ur_hd kp_5x6_ur_last kp_5x6_ur_non_nil
  kp_5x7_ur kp_5x7_ur_hd kp_5x7_ur_last kp_5x7_ur_non_nil
  kp_5x8_ur kp_5x8_ur_hd kp_5x8_ur_last kp_5x8_ur_non_nil
  kp_5x9_ur kp_5x9_ur_hd kp_5x9_ur_last kp_5x9_ur_non_nil

text \<open>For every \<open>5\<times>m\<close>-board with \<open>m \<ge> 5\<close> there exists a knight's path that starts in 
\<open>(1,1)\<close> (bottom-left) and ends in \<open>(2,m-1)\<close> (bottom-right).\<close>
lemma knights_path_5xm_lr_exists: 
  assumes "m \<ge> 5" 
  shows "\<exists>ps. knights_path (board 5 m) ps \<and> hd ps = (1,1) \<and> last ps = (2,int m-1)"
  using assms
proof (induction m rule: less_induct)
  case (less m)
  then have "m \<in> {5,6,7,8,9} \<or> 5 \<le> m-5" by auto
  then show ?case
  proof (elim disjE)
    assume "m \<in> {5,6,7,8,9}"
    then show ?thesis using kp_5xm_lr by fastforce
  next
    assume m_ge: "5 \<le> m-5" (* \<longleftrightarrow> 10 \<le> m *)
    then obtain ps\<^sub>1 where ps\<^sub>1_IH: "knights_path (board 5 (m-5)) ps\<^sub>1" "hd ps\<^sub>1 = (1,1)" 
                                "last ps\<^sub>1 = (2,int (m-5)-1)" "ps\<^sub>1 \<noteq> []"
      using less.IH[of "m-5"] knights_path_non_nil by auto

    let ?ps\<^sub>2="kp5x5lr"
    let ?ps\<^sub>2'="ps\<^sub>1 @ trans_path (0,int (m-5)) ?ps\<^sub>2"
    have "knights_path b5x5 ?ps\<^sub>2" "hd ?ps\<^sub>2 = (1, 1)" "?ps\<^sub>2 \<noteq> []" "last ?ps\<^sub>2 = (2,4)"
      using kp_5xm_lr by auto
    then have 1: "knights_path (board 5 m) ?ps\<^sub>2'"         
      using m_ge ps\<^sub>1_IH knights_path_lr_concat[of 5 "m-5" ps\<^sub>1 5 ?ps\<^sub>2] by auto

    have 2: "hd ?ps\<^sub>2' = (1,1)" using ps\<^sub>1_IH by auto

    have "last (trans_path (0,int (m-5)) ?ps\<^sub>2) = (2,int m-1)"
      using m_ge last_trans_path[OF \<open>?ps\<^sub>2 \<noteq> []\<close> \<open>last ?ps\<^sub>2 = (2,4)\<close>] by auto
    then have 3: "last ?ps\<^sub>2' = (2,int m-1)"
      using last_appendR[OF trans_path_non_nil[OF \<open>?ps\<^sub>2 \<noteq> []\<close>],symmetric] by metis
    
    show ?thesis using 1 2 3 by auto
  qed
qed

text \<open>For every \<open>5\<times>m\<close>-board with \<open>m \<ge> 5\<close> there exists a knight's path that starts in 
\<open>(1,1)\<close> (bottom-left) and ends in \<open>(4,m-1)\<close> (top-right).\<close>
lemma knights_path_5xm_ur_exists: 
  assumes "m \<ge> 5" 
  shows "\<exists>ps. knights_path (board 5 m) ps \<and> hd ps = (1,1) \<and> last ps = (4,int m-1)"
  using assms
proof -
  have "m \<in> {5,6,7,8,9} \<or> 5 \<le> m-5" using assms by auto
  then show ?thesis
  proof (elim disjE)
    assume "m \<in> {5,6,7,8,9}"
    then show ?thesis using kp_5xm_ur by fastforce
  next
    assume m_ge: "5 \<le> m-5" (* \<longleftrightarrow> 10 \<le> m *)
    then obtain ps\<^sub>1 where ps_prems: "knights_path (board 5 (m-5)) ps\<^sub>1" "hd ps\<^sub>1 = (1,1)" 
                                   "last ps\<^sub>1 = (2,int (m-5)-1)" "ps\<^sub>1 \<noteq> []"
      using knights_path_5xm_lr_exists[of "(m-5)"] knights_path_non_nil by auto
    let ?ps\<^sub>2="kp5x5ur"
    let ?ps'="ps\<^sub>1 @ trans_path (0,int (m-5)) ?ps\<^sub>2"
    have "knights_path b5x5 ?ps\<^sub>2" "hd ?ps\<^sub>2 = (1, 1)" "?ps\<^sub>2 \<noteq> []" 
         "last ?ps\<^sub>2 = (4,4)"
      using kp_5xm_ur by auto
    then have 1: "knights_path (board 5 m) ?ps'"              
      using m_ge ps_prems knights_path_lr_concat[of 5 "m-5" ps\<^sub>1 5 ?ps\<^sub>2] by auto

    have 2: "hd ?ps' = (1,1)" using ps_prems by auto

    have "last (trans_path (0,int (m-5)) ?ps\<^sub>2) = (4,int m-1)"
      using m_ge last_trans_path[OF \<open>?ps\<^sub>2 \<noteq> []\<close> \<open>last ?ps\<^sub>2 = (4,4)\<close>] by auto
    then have 3: "last ?ps' = (4,int m-1)"
      using last_appendR[OF trans_path_non_nil[OF \<open>?ps\<^sub>2 \<noteq> []\<close>],symmetric] by metis
    
    show ?thesis using 1 2 3 by auto
  qed
qed

text \<open>@{thm knights_path_5xm_lr_exists} and @{thm knights_path_5xm_lr_exists} formalize Lemma 1 
from \<^cite>\<open>"cull_decurtins_1987"\<close>.\<close>
lemmas knights_path_5xm_exists = knights_path_5xm_lr_exists knights_path_5xm_ur_exists

section \<open>Knight's Paths and Circuits for \<open>6\<times>m\<close>-Boards\<close>

abbreviation "b6x5 \<equiv> board 6 5"

text \<open>
  A Knight's path for the \<open>(6\<times>5)\<close>-board that starts in the lower-left and ends in the upper-left.
  \begin{table}[H]
    \begin{tabular}{lllll}
      10 & 19 &  4 & 29 & 12 \\
       3 & 30 & 11 & 20 &  5 \\
      18 &  9 & 24 & 13 & 28 \\
      25 &  2 & 17 &  6 & 21 \\
      16 & 23 &  8 & 27 & 14 \\
       1 & 26 & 15 & 22 &  7
    \end{tabular}
  \end{table}\<close>
abbreviation "kp6x5ul \<equiv> the (to_path 
  [[10,19,4,29,12],
  [3,30,11,20,5],
  [18,9,24,13,28],
  [25,2,17,6,21],
  [16,23,8,27,14],
  [1,26,15,22,7]])"
lemma kp_6x5_ul: "knights_path b6x5 kp6x5ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_6x5_ul_hd: "hd kp6x5ul = (1,1)" by eval

lemma kp_6x5_ul_last: "last kp6x5ul = (5,2)" by eval

lemma kp_6x5_ul_non_nil: "kp6x5ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(6\<times>5)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{lllll}
      16 &  9 &  6 & 27 & 18 \\
       7 & 26 & 17 & 14 &  5 \\
      10 & 15 &  8 & 19 & 28 \\
      25 & 30 & 23 &  4 & 13 \\
      22 & 11 &  2 & 29 & 20 \\
       1 & 24 & 21 & 12 &  3
    \end{tabular}
  \end{table}\<close>
abbreviation "kc6x5 \<equiv> the (to_path 
  [[16,9,6,27,18],
  [7,26,17,14,5],
  [10,15,8,19,28],
  [25,30,23,4,13],
  [22,11,2,29,20],
  [1,24,21,12,3]])"
lemma kc_6x5: "knights_circuit b6x5 kc6x5"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_6x5_hd: "hd kc6x5 = (1,1)" by eval

lemma kc_6x5_non_nil: "kc6x5 \<noteq> []" by eval

abbreviation "b6x6 \<equiv> board 6 6"

text \<open>The path given for the \<open>6\<times>6\<close>-board that ends in the upper-left is wrong. The Knight cannot 
move from square 26 to square 27.
  \begin{table}[H]
    \begin{tabular}{llllll}
      14 & 23 &  6 & 28 & 12 & 21 \\
       7 & 36 & 13 & 22 &  5 & \color{red}{27} \\
      24 & 15 & 29 & 35 & 20 & 11 \\
      30 &  8 & 17 & \color{red}{26} & 34 &  4 \\
      16 & 25 &  2 & 32 & 10 & 19 \\
       1 & 31 &  9 & 18 &  3 & 33
    \end{tabular}
  \end{table}\<close>
abbreviation "kp6x6ul_false \<equiv> the (to_path 
  [[14,23,6,28,12,21],
  [7,36,13,22,5,27],
  [24,15,29,35,20,11],
  [30,8,17,26,34,4],
  [16,25,2,32,10,19],
  [1,31,9,18,3,33]])"

lemma "\<not>knights_path b6x6 kp6x6ul_false"
  by (simp only: knights_path_exec_simp) eval

text \<open>I have computed a correct Knight's path for the \<open>6\<times>6\<close>-board that ends in the upper-left.
A Knight's path for the \<open>(6\<times>6)\<close>-board that starts in the lower-left and ends in the upper-left.
  \begin{table}[H]
    \begin{tabular}{llllll}
       8 & 25 & 10 & 21 &  6 & 23 \\
      11 & 36 &  7 & 24 & 33 & 20 \\
      26 &  9 & 34 &  3 & 22 &  5 \\
      35 & 12 & 15 & 30 & 19 & 32 \\
      14 & 27 &  2 & 17 &  4 & 29 \\
       1 & 16 & 13 & 28 & 31 & 18
    \end{tabular}
  \end{table}\<close>
abbreviation "kp6x6ul \<equiv> the (to_path 
  [[8,25,10,21,6,23],
  [11,36,7,24,33,20],
  [26,9,34,3,22,5],
  [35,12,15,30,19,32],
  [14,27,2,17,4,29],
  [1,16,13,28,31,18]])"
lemma kp_6x6_ul: "knights_path b6x6 kp6x6ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_6x6_ul_hd: "hd kp6x6ul = (1,1)" by eval

lemma kp_6x6_ul_last: "last kp6x6ul = (5,2)" by eval

lemma kp_6x6_ul_non_nil: "kp6x6ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(6\<times>6)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{llllll}
       4 & 25 & 34 & 15 & 18 &  7 \\
      35 & 14 &  5 &  8 & 33 & 16 \\
      24 &  3 & 26 & 17 &  6 & 19 \\
      13 & 36 & 23 & 30 &  9 & 32 \\
      22 & 27 &  2 & 11 & 20 & 29 \\
       1 & 12 & 21 & 28 & 31 & 10
    \end{tabular}
  \end{table}\<close>
abbreviation "kc6x6 \<equiv> the (to_path 
  [[4,25,34,15,18,7],
  [35,14,5,8,33,16],
  [24,3,26,17,6,19],
  [13,36,23,30,9,32],
  [22,27,2,11,20,29],
  [1,12,21,28,31,10]])"
lemma kc_6x6: "knights_circuit b6x6 kc6x6"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_6x6_hd: "hd kc6x6 = (1,1)" by eval

lemma kc_6x6_non_nil: "kc6x6 \<noteq> []" by eval

abbreviation "b6x7 \<equiv> board 6 7"

text \<open>A Knight's path for the \<open>(6\<times>7)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllll}
      18 & 23 &  8 & 39 & 16 & 25 &  6 \\
       9 & 42 & 17 & 24 &  7 & 40 & 15 \\
      22 & 19 & 32 & 41 & 38 &  5 & 26 \\
      33 & 10 & 21 & 28 & 31 & 14 & 37 \\
      20 & 29 &  2 & 35 & 12 & 27 &  4 \\
       1 & 34 & 11 & 30 &  3 & 36 & 13
    \end{tabular}
  \end{table}\<close>
abbreviation "kp6x7ul \<equiv> the (to_path 
  [[18,23,8,39,16,25,6],
  [9,42,17,24,7,40,15],
  [22,19,32,41,38,5,26],
  [33,10,21,28,31,14,37],
  [20,29,2,35,12,27,4],
  [1,34,11,30,3,36,13]])"
lemma kp_6x7_ul: "knights_path b6x7 kp6x7ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_6x7_ul_hd: "hd kp6x7ul = (1,1)" by eval

lemma kp_6x7_ul_last: "last kp6x7ul = (5,2)" by eval

lemma kp_6x7_ul_non_nil: "kp6x7ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(6\<times>7)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{lllllll}
      26 & 37 &  8 & 17 & 28 & 31 &  6 \\
       9 & 18 & 27 & 36 &  7 & 16 & 29 \\
      38 & 25 & 10 & 19 & 30 &  5 & 32 \\
      11 & 42 & 23 & 40 & 35 & 20 & 15 \\
      24 & 39 &  2 & 13 & 22 & 33 &  4 \\
       1 & 12 & 41 & 34 &  3 & 14 & 21
    \end{tabular}
  \end{table}\<close>
abbreviation "kc6x7 \<equiv> the (to_path 
  [[26,37,8,17,28,31,6],
  [9,18,27,36,7,16,29],
  [38,25,10,19,30,5,32],
  [11,42,23,40,35,20,15],
  [24,39,2,13,22,33,4],
  [1,12,41,34,3,14,21]])"
lemma kc_6x7: "knights_circuit b6x7 kc6x7"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_6x7_hd: "hd kc6x7 = (1,1)" by eval

lemma kc_6x7_non_nil: "kc6x7 \<noteq> []" by eval

abbreviation "b6x8 \<equiv> board 6 8"

text \<open>A Knight's path for the \<open>(6\<times>8)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{llllllll}
      18 & 31 &  8 & 35 & 16 & 33 &  6 & 45 \\
       9 & 48 & 17 & 32 &  7 & 46 & 15 & 26 \\
      30 & 19 & 36 & 47 & 34 & 27 & 44 &  5 \\
      37 & 10 & 21 & 28 & 43 & 40 & 25 & 14 \\
      20 & 29 &  2 & 39 & 12 & 23 &  4 & 41 \\
       1 & 38 & 11 & 22 &  3 & 42 & 13 & 24
    \end{tabular}
  \end{table}\<close>
abbreviation "kp6x8ul \<equiv> the (to_path 
  [[18,31,8,35,16,33,6,45],
  [9,48,17,32,7,46,15,26],
  [30,19,36,47,34,27,44,5],
  [37,10,21,28,43,40,25,14],
  [20,29,2,39,12,23,4,41],
  [1,38,11,22,3,42,13,24]])"
lemma kp_6x8_ul: "knights_path b6x8 kp6x8ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_6x8_ul_hd: "hd kp6x8ul = (1,1)" by eval

lemma kp_6x8_ul_last: "last kp6x8ul = (5,2)" by eval

lemma kp_6x8_ul_non_nil: "kp6x8ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(6\<times>8)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{llllllll}
      30 & 35 &  8 & 15 & 28 & 39 &  6 & 13 \\
       9 & 16 & 29 & 36 &  7 & 14 & 27 & 38 \\
      34 & 31 & 10 & 23 & 40 & 37 & 12 &  5 \\
      17 & 48 & 33 & 46 & 11 & 22 & 41 & 26 \\
      32 & 45 &  2 & 19 & 24 & 43 &  4 & 21 \\
       1 & 18 & 47 & 44 &  3 & 20 & 25 & 42
    \end{tabular}
  \end{table}\<close>
abbreviation "kc6x8 \<equiv> the (to_path 
  [[30,35,8,15,28,39,6,13],
  [9,16,29,36,7,14,27,38],
  [34,31,10,23,40,37,12,5],
  [17,48,33,46,11,22,41,26],
  [32,45,2,19,24,43,4,21],
  [1,18,47,44,3,20,25,42]])"
lemma kc_6x8: "knights_circuit b6x8 kc6x8"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_6x8_hd: "hd kc6x8 = (1,1)" by eval

lemma kc_6x8_non_nil: "kc6x8 \<noteq> []" by eval

abbreviation "b6x9 \<equiv> board 6 9"

text \<open>A Knight's path for the \<open>(6\<times>9)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
      22 & 45 & 10 & 53 & 20 & 47 &  8 & 35 & 18 \\
      11 & 54 & 21 & 46 &  9 & 36 & 19 & 48 &  7 \\
      44 & 23 & 42 & 37 & 52 & 49 & 32 & 17 & 34 \\
      41 & 12 & 25 & 50 & 27 & 38 & 29 &  6 & 31 \\
      24 & 43 &  2 & 39 & 14 & 51 &  4 & 33 & 16 \\
       1 & 40 & 13 & 26 &  3 & 28 & 15 & 30 &  5
    \end{tabular}
  \end{table}\<close>
abbreviation "kp6x9ul \<equiv> the (to_path 
  [[22,45,10,53,20,47,8,35,18],
  [11,54,21,46,9,36,19,48,7],
  [44,23,42,37,52,49,32,17,34],
  [41,12,25,50,27,38,29,6,31],
  [24,43,2,39,14,51,4,33,16],
  [1,40,13,26,3,28,15,30,5]])"
lemma kp_6x9_ul: "knights_path b6x9 kp6x9ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_6x9_ul_hd: "hd kp6x9ul = (1,1)" by eval

lemma kp_6x9_ul_last: "last kp6x9ul = (5,2)" by eval

lemma kp_6x9_ul_non_nil: "kp6x9ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(6\<times>9)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
      14 & 49 &  4 & 51 & 24 & 39 &  6 & 29 & 22 \\
       3 & 52 & 13 & 40 &  5 & 32 & 23 & 42 &  7 \\
      48 & 15 & 50 & 25 & 38 & 41 & 28 & 21 & 30 \\
      53 &  2 & 37 & 12 & 33 & 26 & 31 &  8 & 43 \\
      16 & 47 & 54 & 35 & 18 & 45 & 10 & 27 & 20 \\
       1 & 36 & 17 & 46 & 11 & 34 & 19 & 44 &  9
    \end{tabular}
  \end{table}\<close>
abbreviation "kc6x9 \<equiv> the (to_path 
  [[14,49,4,51,24,39,6,29,22],
  [3,52,13,40,5,32,23,42,7],
  [48,15,50,25,38,41,28,21,30],
  [53,2,37,12,33,26,31,8,43],
  [16,47,54,35,18,45,10,27,20],
  [1,36,17,46,11,34,19,44,9]])"
lemma kc_6x9: "knights_circuit b6x9 kc6x9"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_6x9_hd: "hd kc6x9 = (1,1)" by eval

lemma kc_6x9_non_nil: "kc6x9 \<noteq> []" by eval

lemmas kp_6xm_ul = 
  kp_6x5_ul kp_6x5_ul_hd kp_6x5_ul_last kp_6x5_ul_non_nil
  kp_6x6_ul kp_6x6_ul_hd kp_6x6_ul_last kp_6x6_ul_non_nil
  kp_6x7_ul kp_6x7_ul_hd kp_6x7_ul_last kp_6x7_ul_non_nil
  kp_6x8_ul kp_6x8_ul_hd kp_6x8_ul_last kp_6x8_ul_non_nil
  kp_6x9_ul kp_6x9_ul_hd kp_6x9_ul_last kp_6x9_ul_non_nil

lemmas kc_6xm = 
  kc_6x5 kc_6x5_hd kc_6x5_non_nil
  kc_6x6 kc_6x6_hd kc_6x6_non_nil
  kc_6x7 kc_6x7_hd kc_6x7_non_nil
  kc_6x8 kc_6x8_hd kc_6x8_non_nil
  kc_6x9 kc_6x9_hd kc_6x9_non_nil

text \<open>For every \<open>6\<times>m\<close>-board with \<open>m \<ge> 5\<close> there exists a knight's path that starts in 
\<open>(1,1)\<close> (bottom-left) and ends in \<open>(5,2)\<close> (top-left).\<close>
lemma knights_path_6xm_ul_exists: 
  assumes "m \<ge> 5" 
  shows "\<exists>ps. knights_path (board 6 m) ps \<and> hd ps = (1,1) \<and> last ps = (5,2)"
  using assms
proof (induction m rule: less_induct)
  case (less m)
  then have "m \<in> {5,6,7,8,9} \<or> 5 \<le> m-5" by auto
  then show ?case
  proof (elim disjE)
    assume "m \<in> {5,6,7,8,9}"
    then show ?thesis using kp_6xm_ul by fastforce
  next
    let ?ps\<^sub>1="kp6x5ul"
    let ?b\<^sub>1="board 6 5"
    have ps\<^sub>1_prems: "knights_path ?b\<^sub>1 ?ps\<^sub>1" "hd ?ps\<^sub>1 = (1,1)" "last ?ps\<^sub>1 = (5,2)" 
      using kp_6xm_ul by auto
    assume m_ge: "5 \<le> m-5" (* \<longleftrightarrow> 10 \<le> m *)
    then obtain ps\<^sub>2 where ps\<^sub>2_IH: "knights_path (board 6 (m-5)) ps\<^sub>2" "hd ps\<^sub>2 = (1,1)" 
                                "last ps\<^sub>2 = (5,2)"
      using less.IH[of "m-5"] knights_path_non_nil by auto

    have "27 < length ?ps\<^sub>1" "last (take 27 ?ps\<^sub>1) = (2,4)" "hd (drop 27 ?ps\<^sub>1) = (4,5)" by eval+
    then have "step_in ?ps\<^sub>1 (2,4) (4,5)"
      unfolding step_in_def using zero_less_numeral by blast
    then have "step_in ?ps\<^sub>1 (2,4) (4,5)" 
              "valid_step (2,4) (1,int 5+1)" 
              "valid_step (5,int 5+2) (4,5)"
      unfolding valid_step_def by auto
    then show ?thesis
      using \<open>5 \<le> m-5\<close> ps\<^sub>1_prems ps\<^sub>2_IH knights_path_split_concat[of 6 5 ?ps\<^sub>1 "m-5" ps\<^sub>2] by auto
  qed
qed

text \<open>For every \<open>6\<times>m\<close>-board with \<open>m \<ge> 5\<close> there exists a knight's circuit.\<close>
lemma knights_circuit_6xm_exists: 
  assumes "m \<ge> 5" 
  shows "\<exists>ps. knights_circuit (board 6 m) ps"
  using assms
proof -
  have "m \<in> {5,6,7,8,9} \<or> 5 \<le> m-5" using assms by auto
  then show ?thesis
  proof (elim disjE)
    assume "m \<in> {5,6,7,8,9}"
    then show ?thesis using kc_6xm by fastforce
  next
    let ?ps\<^sub>1="rev kc6x5"
    have "knights_circuit b6x5 ?ps\<^sub>1" "last ?ps\<^sub>1 = (1,1)"
      using kc_6xm knights_circuit_rev by (auto simp: last_rev)
    then have ps\<^sub>1_prems: "knights_path b6x5 ?ps\<^sub>1" "valid_step (last ?ps\<^sub>1) (hd ?ps\<^sub>1)"
      unfolding knights_circuit_def using valid_step_rev by auto
    assume m_ge: "5 \<le> m-5" (* \<longleftrightarrow> 10 \<le> m *)
    then obtain ps\<^sub>2 where ps2_prems: "knights_path (board 6 (m-5)) ps\<^sub>2" "hd ps\<^sub>2 = (1,1)" 
                                   "last ps\<^sub>2 = (5,2)"
      using knights_path_6xm_ul_exists[of "(m-5)"] knights_path_non_nil by auto

    have "2 < length ?ps\<^sub>1" "last (take 2 ?ps\<^sub>1) = (2,4)" "hd (drop 2 ?ps\<^sub>1) = (4,5)" by eval+
    then have "step_in ?ps\<^sub>1 (2,4) (4,5)"
      unfolding step_in_def using zero_less_numeral by blast
    then have "step_in ?ps\<^sub>1 (2,4) (4,5)" 
              "valid_step (2,4) (1,int 5+1)" 
              "valid_step (5,int 5+2) (4,5)"
      unfolding valid_step_def by auto
    then have "\<exists>ps. knights_path (board 6 m) ps \<and> hd ps = hd ?ps\<^sub>1 \<and> last ps = last ?ps\<^sub>1"              
      using m_ge ps\<^sub>1_prems ps2_prems knights_path_split_concat[of 6 5 ?ps\<^sub>1 "m-5" ps\<^sub>2] by auto
    then show ?thesis using ps\<^sub>1_prems by (auto simp: knights_circuit_def)
  qed
qed

text \<open>@{thm knights_path_6xm_ul_exists} and @{thm knights_circuit_6xm_exists} formalize Lemma 2 
from \<^cite>\<open>"cull_decurtins_1987"\<close>.\<close>
lemmas knights_path_6xm_exists = knights_path_6xm_ul_exists knights_circuit_6xm_exists

section \<open>Knight's Paths and Circuits for \<open>8\<times>m\<close>-Boards\<close>

abbreviation "b8x5 \<equiv> board 8 5"

text \<open>A Knight's path for the \<open>(8\<times>5)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllll}
      28 &  7 & 22 & 39 & 26 \\
      23 & 40 & 27 &  6 & 21 \\
       8 & 29 & 38 & 25 & 14 \\
      37 & 24 & 15 & 20 &  5 \\
      16 &  9 & 30 & 13 & 34 \\
      31 & 36 & 33 &  4 & 19 \\
      10 & 17 &  2 & 35 & 12 \\
       1 & 32 & 11 & 18 &  3
    \end{tabular}
  \end{table}\<close>
abbreviation "kp8x5ul \<equiv> the (to_path 
  [[28,7,22,39,26],
  [23,40,27,6,21],
  [8,29,38,25,14],
  [37,24,15,20,5],
  [16,9,30,13,34],
  [31,36,33,4,19],
  [10,17,2,35,12],
  [1,32,11,18,3]])"
lemma kp_8x5_ul: "knights_path b8x5 kp8x5ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_8x5_ul_hd: "hd kp8x5ul = (1,1)" by eval

lemma kp_8x5_ul_last: "last kp8x5ul = (7,2)" by eval

lemma kp_8x5_ul_non_nil: "kp8x5ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(8\<times>5)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{lllll}
      26 &  7 & 28 & 15 & 24 \\
      31 & 16 & 25 &  6 & 29 \\
       8 & 27 & 30 & 23 & 14 \\
      17 & 32 & 39 & 34 &  5 \\
      38 &  9 & 18 & 13 & 22 \\
      19 & 40 & 33 &  4 & 35 \\
      10 & 37 &  2 & 21 & 12 \\
       1 & 20 & 11 & 36 &  3
    \end{tabular}
  \end{table}\<close>
abbreviation "kc8x5 \<equiv> the (to_path 
  [[26,7,28,15,24],
  [31,16,25,6,29],
  [8,27,30,23,14],
  [17,32,39,34,5],
  [38,9,18,13,22],
  [19,40,33,4,35],
  [10,37,2,21,12],
  [1,20,11,36,3]])"
lemma kc_8x5: "knights_circuit b8x5 kc8x5"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_8x5_hd: "hd kc8x5 = (1,1)" by eval

lemma kc_8x5_last: "last kc8x5 = (3,2)" by eval

lemma kc_8x5_non_nil: "kc8x5 \<noteq> []" by eval

lemma kc_8x5_si: "step_in kc8x5 (2,4) (4,5)"  (is "step_in ?ps _ _")
proof -
  have "0 < (21::nat)" "21 < length ?ps" "last (take 21 ?ps) = (2,4)" "hd (drop 21 ?ps) = (4,5)" 
    by eval+
  then show ?thesis unfolding step_in_def by blast
qed

abbreviation "b8x6 \<equiv> board 8 6"

text \<open>A Knight's path for the \<open>(8\<times>6)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{llllll}
      42 & 11 & 26 &  9 & 34 & 13 \\
      25 & 48 & 43 & 12 & 27 &  8 \\
      44 & 41 & 10 & 33 & 14 & 35 \\
      47 & 24 & 45 & 20 &  7 & 28 \\
      40 & 19 & 32 &  3 & 36 & 15 \\
      23 & 46 & 21 &  6 & 29 &  4 \\
      18 & 39 &  2 & 31 & 16 & 37 \\
       1 & 22 & 17 & 38 &  5 & 30
    \end{tabular}
  \end{table}\<close>
abbreviation "kp8x6ul \<equiv> the (to_path 
  [[42,11,26,9,34,13],
  [25,48,43,12,27,8],
  [44,41,10,33,14,35],
  [47,24,45,20,7,28],
  [40,19,32,3,36,15],
  [23,46,21,6,29,4],
  [18,39,2,31,16,37],
  [1,22,17,38,5,30]])"
lemma kp_8x6_ul: "knights_path b8x6 kp8x6ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_8x6_ul_hd: "hd kp8x6ul = (1,1)" by eval

lemma kp_8x6_ul_last: "last kp8x6ul = (7,2)" by eval

lemma kp_8x6_ul_non_nil: "kp8x6ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(8\<times>6)\<close>-board. I have reversed circuit s.t. the circuit steps 
from \<open>(2,5)\<close> to \<open>(4,6)\<close> and not the other way around. This makes the proofs easier.
  \begin{table}[H]
    \begin{tabular}{llllll}
       8 & 29 & 24 & 45 & 12 & 37 \\
      25 & 46 &  9 & 38 & 23 & 44 \\
      30 &  7 & 28 & 13 & 36 & 11 \\
      47 & 26 & 39 & 10 & 43 & 22 \\
       6 & 31 &  4 & 27 & 14 & 35 \\
       3 & 48 & 17 & 40 & 21 & 42 \\
      32 &  5 &  2 & 19 & 34 & 15 \\
       1 & 18 & 33 & 16 & 41 & 20
    \end{tabular}
  \end{table}\<close>
abbreviation "kc8x6 \<equiv> the (to_path 
  [[8,29,24,45,12,37],
  [25,46,9,38,23,44],
  [30,7,28,13,36,11],
  [47,26,39,10,43,22],
  [6,31,4,27,14,35],
  [3,48,17,40,21,42],
  [32,5,2,19,34,15],
  [1,18,33,16,41,20]])"
lemma kc_8x6: "knights_circuit b8x6 kc8x6"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_8x6_hd: "hd kc8x6 = (1,1)" by eval

lemma kc_8x6_non_nil: "kc8x6 \<noteq> []" by eval

lemma kc_8x6_si: "step_in kc8x6 (2,5) (4,6)" (is "step_in ?ps _ _")
proof -
  have "0 < (34::nat)" "34 < length ?ps" 
        "last (take 34 ?ps) = (2,5)" "hd (drop 34 ?ps) = (4,6)" by eval+
  then show ?thesis unfolding step_in_def by blast
qed

abbreviation "b8x7 \<equiv> board 8 7"

text \<open>A Knight's path for the \<open>(8\<times>7)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllll}
      38 & 19 &  6 & 55 & 46 & 21 &  8 \\
       5 & 56 & 39 & 20 &  7 & 54 & 45 \\
      18 & 37 &  4 & 47 & 34 &  9 & 22 \\
       3 & 48 & 35 & 40 & 53 & 44 & 33 \\
      36 & 17 & 52 & 49 & 32 & 23 & 10 \\
      51 &  2 & 29 & 14 & 41 & 26 & 43 \\
      16 & 13 & 50 & 31 & 28 & 11 & 24 \\
       1 & 30 & 15 & 12 & 25 & 42 & 27
    \end{tabular}
  \end{table}\<close>
abbreviation "kp8x7ul \<equiv> the (to_path 
  [[38,19,6,55,46,21,8],
  [5,56,39,20,7,54,45],
  [18,37,4,47,34,9,22],
  [3,48,35,40,53,44,33],
  [36,17,52,49,32,23,10],
  [51,2,29,14,41,26,43],
  [16,13,50,31,28,11,24],
  [1,30,15,12,25,42,27]])"
lemma kp_8x7_ul: "knights_path b8x7 kp8x7ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_8x7_ul_hd: "hd kp8x7ul = (1,1)" by eval

lemma kp_8x7_ul_last: "last kp8x7ul = (7,2)" by eval

lemma kp_8x7_ul_non_nil: "kp8x7ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(8\<times>7)\<close>-board. I have reversed circuit s.t. the circuit steps 
from \<open>(2,6)\<close> to \<open>(4,7)\<close> and not the other way around. This makes the proofs easier.
  \begin{table}[H]
    \begin{tabular}{lllllll}
      36 & 31 & 18 & 53 & 20 & 29 & 44 \\
      17 & 54 & 35 & 30 & 45 & 52 & 21 \\
      32 & 37 & 46 & 19 &  8 & 43 & 28 \\
      55 & 16 &  7 & 34 & 27 & 22 & 51 \\
      38 & 33 & 26 & 47 &  6 &  9 & 42 \\
       3 & 56 & 15 & 12 & 25 & 50 & 23 \\
      14 & 39 &  2 &  5 & 48 & 41 & 10 \\
       1 &  4 & 13 & 40 & 11 & 24 & 49 
    \end{tabular}
  \end{table}\<close>
abbreviation "kc8x7 \<equiv> the (to_path 
  [[36,31,18,53,20,29,44],
  [17,54,35,30,45,52,21],
  [32,37,46,19,8,43,28],
  [55,16,7,34,27,22,51],
  [38,33,26,47,6,9,42],
  [3,56,15,12,25,50,23],
  [14,39,2,5,48,41,10],
  [1,4,13,40,11,24,49]])"
lemma kc_8x7: "knights_circuit b8x7 kc8x7"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_8x7_hd: "hd kc8x7 = (1,1)" by eval

lemma kc_8x7_non_nil: "kc8x7 \<noteq> []" by eval

lemma kc_8x7_si: "step_in kc8x7 (2,6) (4,7)" (is "step_in ?ps _ _")
proof -
  have "0 < (41::nat)" "41 < length ?ps" 
        "last (take 41 ?ps) = (2,6)" "hd (drop 41 ?ps) = (4,7)" by eval+
  then show ?thesis unfolding step_in_def by blast
qed

abbreviation "b8x8 \<equiv> board 8 8"

text \<open>The path given for the \<open>8\<times>8\<close>-board that ends in the upper-left is wrong. The Knight cannot 
move from square 27 to square 28.
  \begin{table}[H]
    \begin{tabular}{llllllll}
      24 & 11 & 37 &  9 & 26 & 21 & 39 &  7 \\
      36 & 64 & 24 & 22 & 38 &  8 & \color{red}{27} & 20 \\
      12 & 23 & 10 & 53 & 58 & 49 &  6 & \color{red}{28} \\
      63 & 35 & 61 & 50 & 55 & 52 & 19 & 40 \\
      46 & 13 & 54 & 57 & 48 & 59 & 29 &  5 \\
      34 & 62 & 47 & 60 & 51 & 56 & 41 & 18 \\
      14 & 45 &  2 & 32 & 16 & 43 &  4 & 30 \\
       1 & 33 & 15 & 44 &  3 & 31 & 17 & 42
    \end{tabular}
  \end{table}\<close>
abbreviation "kp8x8ul_false \<equiv> the (to_path 
  [[24,11,37,9,26,21,39,7],
  [36,64,25,22,38,8,27,20],
  [12,23,10,53,58,49,6,28],
  [63,35,61,50,55,52,19,40],
  [46,13,54,57,48,59,29,5],
  [34,62,47,60,51,56,41,18],
  [14,45,2,32,16,43,4,30],
  [1,33,15,44,3,31,17,42]])"

lemma "\<not>knights_path b8x8 kp8x8ul_false"
  by (simp only: knights_path_exec_simp) eval

text \<open>I have computed a correct Knight's path for the \<open>8\<times>8\<close>-board that ends in the upper-left.
  \begin{table}[H]
    \begin{tabular}{llllllll}
      38 & 41 & 36 & 27 & 32 & 43 & 20 & 25 \\
      35 & 64 & 39 & 42 & 21 & 26 & 29 & 44 \\
      40 & 37 &  6 & 33 & 28 & 31 & 24 & 19 \\
       5 & 34 & 63 & 14 &  7 & 22 & 45 & 30 \\
      62 & 13 &  4 &  9 & 58 & 49 & 18 & 23 \\
       3 & 10 & 61 & 52 & 15 &  8 & 57 & 46 \\
      12 & 53 &  2 & 59 & 48 & 55 & 50 & 17 \\
       1 & 60 & 11 & 54 & 51 & 16 & 47 & 56
    \end{tabular}
  \end{table}\<close>
abbreviation "kp8x8ul \<equiv> the (to_path 
  [[38,41,36,27,32,43,20,25],
  [35,64,39,42,21,26,29,44],
  [40,37,6,33,28,31,24,19],
  [5,34,63,14,7,22,45,30],
  [62,13,4,9,58,49,18,23],
  [3,10,61,52,15,8,57,46],
  [12,53,2,59,48,55,50,17],
  [1,60,11,54,51,16,47,56]])" 

lemma kp_8x8_ul: "knights_path b8x8 kp8x8ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_8x8_ul_hd: "hd kp8x8ul = (1,1)" by eval

lemma kp_8x8_ul_last: "last kp8x8ul = (7,2)" by eval

lemma kp_8x8_ul_non_nil: "kp8x8ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(8\<times>8)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{llllllll}
      48 & 13 & 30 &  9 & 56 & 45 & 28 &  7 \\
      31 & 10 & 47 & 50 & 29 &  8 & 57 & 44 \\
      14 & 49 & 12 & 55 & 46 & 59 &  6 & 27 \\
      11 & 32 & 37 & 60 & 51 & 54 & 43 & 58 \\
      36 & 15 & 52 & 63 & 38 & 61 & 26 &  5 \\
      33 & 64 & 35 & 18 & 53 & 40 & 23 & 42 \\
      16 & 19 &  2 & 39 & 62 & 21 &  4 & 25 \\
       1 & 34 & 17 & 20 &  3 & 24 & 41 & 22
    \end{tabular}
  \end{table}\<close>
abbreviation "kc8x8 \<equiv> the (to_path 
  [[48,13,30,9,56,45,28,7],
  [31,10,47,50,29,8,57,44],
  [14,49,12,55,46,59,6,27],
  [11,32,37,60,51,54,43,58],
  [36,15,52,63,38,61,26,5],
  [33,64,35,18,53,40,23,42],
  [16,19,2,39,62,21,4,25],
  [1,34,17,20,3,24,41,22]])"
lemma kc_8x8: "knights_circuit b8x8 kc8x8"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_8x8_hd: "hd kc8x8 = (1,1)" by eval

lemma kc_8x8_non_nil: "kc8x8 \<noteq> []" by eval

lemma kc_8x8_si: "step_in kc8x8 (2,7) (4,8)" (is "step_in ?ps _ _")
proof -
  have "0 < (4::nat)" "4 < length ?ps" 
        "last (take 4 ?ps) = (2,7)" "hd (drop 4 ?ps) = (4,8)" by eval+
  then show ?thesis unfolding step_in_def by blast
qed

abbreviation "b8x9 \<equiv> board 8 9"

text \<open>A Knight's path for the \<open>(8\<times>9)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
      32 & 47 &  6 & 71 & 30 & 45 &  8 & 43 & 26 \\
       5 & 72 & 31 & 46 &  7 & 70 & 27 & 22 &  9 \\
      48 & 33 &  4 & 29 & 64 & 23 & 44 & 25 & 42 \\
       3 & 60 & 35 & 62 & 69 & 28 & 41 & 10 & 21 \\
      34 & 49 & 68 & 65 & 36 & 63 & 24 & 55 & 40 \\
      59 &  2 & 61 & 16 & 67 & 56 & 37 & 20 & 11 \\
      50 & 15 & 66 & 57 & 52 & 13 & 18 & 39 & 54 \\
       1 & 58 & 51 & 14 & 17 & 38 & 53 & 12 & 19
    \end{tabular}
  \end{table}\<close>
abbreviation "kp8x9ul \<equiv> the (to_path 
  [[32,47,6,71,30,45,8,43,26],
  [5,72,31,46,7,70,27,22,9],
  [48,33,4,29,64,23,44,25,42],
  [3,60,35,62,69,28,41,10,21],
  [34,49,68,65,36,63,24,55,40],
  [59,2,61,16,67,56,37,20,11],
  [50,15,66,57,52,13,18,39,54],
  [1,58,51,14,17,38,53,12,19]])"
lemma kp_8x9_ul: "knights_path b8x9 kp8x9ul"
  by (simp only: knights_path_exec_simp) eval

lemma kp_8x9_ul_hd: "hd kp8x9ul = (1,1)" by eval

lemma kp_8x9_ul_last: "last kp8x9ul = (7,2)" by eval

lemma kp_8x9_ul_non_nil: "kp8x9ul \<noteq> []" by eval

text \<open>A Knight's circuit for the \<open>(8\<times>9)\<close>-board.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
      42 & 19 & 38 &  5 & 36 & 21 & 34 &  7 & 60 \\
      39 &  4 & 41 & 20 & 63 &  6 & 59 & 22 & 33 \\
      18 & 43 & 70 & 37 & 58 & 35 & 68 & 61 &  8 \\
       3 & 40 & 49 & 64 & 69 & 62 & 57 & 32 & 23 \\
      50 & 17 & 44 & 71 & 48 & 67 & 54 &  9 & 56 \\
      45 &  2 & 65 & 14 & 27 & 12 & 29 & 24 & 31 \\
      16 & 51 & 72 & 47 & 66 & 53 & 26 & 55 & 10 \\
       1 & 46 & 15 & 52 & 13 & 28 & 11 & 30 & 25
    \end{tabular}
  \end{table}\<close>
abbreviation "kc8x9 \<equiv> the (to_path 
  [[42,19,38,5,36,21,34,7,60],
  [39,4,41,20,63,6,59,22,33],
  [18,43,70,37,58,35,68,61,8],
  [3,40,49,64,69,62,57,32,23],
  [50,17,44,71,48,67,54,9,56],
  [45,2,65,14,27,12,29,24,31],
  [16,51,72,47,66,53,26,55,10],
  [1,46,15,52,13,28,11,30,25]])"
lemma kc_8x9: "knights_circuit b8x9 kc8x9"
  by (simp only: knights_circuit_exec_simp) eval

lemma kc_8x9_hd: "hd kc8x9 = (1,1)" by eval

lemma kc_8x9_non_nil: "kc8x9 \<noteq> []" by eval

lemma kc_8x9_si: "step_in kc8x9 (2,8) (4,9)" (is "step_in ?ps _ _")
proof -
  have "0 < (55::nat)" "55 < length ?ps" 
        "last (take 55 ?ps) = (2,8)" "hd (drop 55 ?ps) = (4,9)" by eval+
  then show ?thesis unfolding step_in_def by blast
qed

lemmas kp_8xm_ul = 
  kp_8x5_ul kp_8x5_ul_hd kp_8x5_ul_last kp_8x5_ul_non_nil
  kp_8x6_ul kp_8x6_ul_hd kp_8x6_ul_last kp_8x6_ul_non_nil
  kp_8x7_ul kp_8x7_ul_hd kp_8x7_ul_last kp_8x7_ul_non_nil
  kp_8x8_ul kp_8x8_ul_hd kp_8x8_ul_last kp_8x8_ul_non_nil
  kp_8x9_ul kp_8x9_ul_hd kp_8x9_ul_last kp_8x9_ul_non_nil

lemmas kc_8xm = 
  kc_8x5 kc_8x5_hd kc_8x5_last kc_8x5_non_nil kc_8x5_si
  kc_8x6 kc_8x6_hd kc_8x6_non_nil kc_8x6_si
  kc_8x7 kc_8x7_hd kc_8x7_non_nil kc_8x7_si
  kc_8x8 kc_8x8_hd kc_8x8_non_nil kc_8x8_si
  kc_8x9 kc_8x9_hd kc_8x9_non_nil kc_8x9_si

text \<open>For every \<open>8\<times>m\<close>-board with \<open>m \<ge> 5\<close> there exists a knight's circuit.\<close>
lemma knights_circuit_8xm_exists: 
  assumes "m \<ge> 5" 
  shows "\<exists>ps. knights_circuit (board 8 m) ps \<and> step_in ps (2,int m-1) (4,int m)"
  using assms
proof (induction m rule: less_induct)
  case (less m)
  then have "m \<in> {5,6,7,8,9} \<or> 5 \<le> m-5" by auto
  then show ?case
  proof (elim disjE)
    assume "m \<in> {5,6,7,8,9}"
    then show ?thesis using kc_8xm by fastforce
  next
    let ?ps\<^sub>2="kc8x5"
    let ?b\<^sub>2="board 8 5"
    have ps\<^sub>2_prems: "knights_circuit ?b\<^sub>2 ?ps\<^sub>2" "hd ?ps\<^sub>2 = (1,1)" "last ?ps\<^sub>2 = (3,2)"
      using kc_8xm by auto
    have "21 < length ?ps\<^sub>2" "last (take 21 ?ps\<^sub>2) = (2,int 5-1)" "hd (drop 21 ?ps\<^sub>2) = (4,int 5)" 
      by eval+
    then have si: "step_in ?ps\<^sub>2 (2,int 5-1) (4,int 5)"
      unfolding step_in_def using zero_less_numeral by blast
    assume m_ge: "5 \<le> m-5" (* \<longleftrightarrow> 10 \<le> m *)
    then obtain ps\<^sub>1 where ps\<^sub>1_IH: "knights_circuit (board 8 (m-5)) ps\<^sub>1"
                                "step_in ps\<^sub>1 (2,int (m-5)-1) (4,int (m-5))"
      using less.IH[of "m-5"] knights_path_non_nil by auto
    then show ?thesis
      using m_ge ps\<^sub>2_prems si knights_circuit_lr_concat[of 8 "m-5" ps\<^sub>1 5 ?ps\<^sub>2] by auto
  qed
qed

text \<open>For every \<open>8\<times>m\<close>-board with \<open>m \<ge> 5\<close> there exists a knight's path that starts in 
\<open>(1,1)\<close> (bottom-left) and ends in \<open>(7,2)\<close> (top-left).\<close>
lemma knights_path_8xm_ul_exists: 
  assumes "m \<ge> 5" 
  shows "\<exists>ps. knights_path (board 8 m) ps \<and> hd ps = (1,1) \<and> last ps = (7,2)"
  using assms
proof -
  have "m \<in> {5,6,7,8,9} \<or> 5 \<le> m-5" using assms by auto
  then show ?thesis
  proof (elim disjE)
    assume "m \<in> {5,6,7,8,9}"
    then show ?thesis using kp_8xm_ul by fastforce
  next
    let ?ps\<^sub>1="kp8x5ul"
    have ps\<^sub>1_prems: "knights_path b8x5 ?ps\<^sub>1" "hd ?ps\<^sub>1 = (1,1)" "last ?ps\<^sub>1 = (7,2)"
      using kp_8xm_ul by auto
    assume m_ge: "5 \<le> m-5" (* \<longleftrightarrow> 10 \<le> m *)
    then have b_prems: "5 \<le> min 8 (m-5)"
      unfolding board_def by auto

    obtain ps\<^sub>2 where "knights_circuit (board 8 (m-5)) ps\<^sub>2"
      using m_ge knights_circuit_8xm_exists[of "(m-5)"] knights_path_non_nil by auto
    then obtain ps\<^sub>2' where ps\<^sub>2'_prems': "knights_circuit (board 8 (m-5)) ps\<^sub>2'" 
        "hd ps\<^sub>2' = (1,1)" "last ps\<^sub>2' = (3,2)"
      using b_prems \<open>5 \<le> min 8 (m-5)\<close> rotate_knights_circuit by blast
    then have ps\<^sub>2'_path: "knights_path (board 8 (m-5)) (rev ps\<^sub>2')" 
      "valid_step (last ps\<^sub>2') (hd ps\<^sub>2')" "hd (rev ps\<^sub>2') = (3,2)" "last (rev ps\<^sub>2') = (1,1)"
      unfolding knights_circuit_def using knights_path_rev by (auto simp: hd_rev last_rev)

    have "34 < length ?ps\<^sub>1" "last (take 34 ?ps\<^sub>1) = (4,5)" "hd (drop 34 ?ps\<^sub>1) = (2,4)" by eval+
    then have "step_in ?ps\<^sub>1 (4,5) (2,4)"
      unfolding step_in_def using zero_less_numeral by blast
    then have "step_in ?ps\<^sub>1 (4,5) (2,4)" 
              "valid_step (4,5) (3,int 5+2)" 
              "valid_step (1,int 5+1) (2,4)"
      unfolding valid_step_def by auto
    then have "\<exists>ps. knights_path (board 8 m) ps \<and> hd ps = hd ?ps\<^sub>1 \<and> last ps = last ?ps\<^sub>1"              
      using m_ge ps\<^sub>1_prems ps\<^sub>2'_prems' ps\<^sub>2'_path 
            knights_path_split_concat[of 8 5 ?ps\<^sub>1 "m-5" "rev ps\<^sub>2'"] by auto
    then show ?thesis using ps\<^sub>1_prems by auto
  qed
qed

text \<open>@{thm knights_circuit_8xm_exists} and @{thm knights_path_8xm_ul_exists} formalize Lemma 3 
from \<^cite>\<open>"cull_decurtins_1987"\<close>.\<close>
lemmas knights_path_8xm_exists = knights_circuit_8xm_exists knights_path_8xm_ul_exists

section \<open>Knight's Paths and Circuits for \<open>n\<times>m\<close>-Boards\<close>

text \<open>In this section the desired theorems are proved. The proof uses the previous lemmas to 
construct paths and circuits for arbitrary \<open>n\<times>m\<close>-boards.\<close>

text \<open>A Knight's path for the \<open>(5\<times>5)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllll}
       7 & 20 &  9 & 14 &  5 \\
      10 & 25 &  6 & 21 & 16 \\
      19 &  8 & 15 &  4 & 13 \\
      24 & 11 &  2 & 17 & 22 \\
       1 & 18 & 23 & 12 &  3
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x5ul \<equiv> the (to_path 
  [[7,20,9,14,5],
  [10,25,6,21,16],
  [19,8,15,4,13],
  [24,11,2,17,22],
  [1,18,23,12,3]])"
lemma kp_5x5_ul: "knights_path b5x5 kp5x5ul"
  by (simp only: knights_path_exec_simp) eval

text \<open>A Knight's path for the \<open>(5\<times>7)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllll}
      17 & 14 & 25 &  6 & 19 &  8 & 29 \\
      26 & 35 & 18 & 15 & 28 &  5 & 20 \\
      13 & 16 & 27 & 24 &  7 & 30 &  9 \\
      34 & 23 &  2 & 11 & 32 & 21 &  4 \\
       1 & 12 & 33 & 22 &  3 & 10 & 31
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x7ul \<equiv> the (to_path 
  [[17,14,25,6,19,8,29],
  [26,35,18,15,28,5,20],
  [13,16,27,24,7,30,9],
  [34,23,2,11,32,21,4],
  [1,12,33,22,3,10,31]])"
lemma kp_5x7_ul: "knights_path b5x7 kp5x7ul"
  by (simp only: knights_path_exec_simp) eval

text \<open>A Knight's path for the \<open>(5\<times>9)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
       7 & 12 & 37 & 42 &  5 & 18 & 23 & 32 & 27 \\
      38 & 45 &  6 & 11 & 36 & 31 & 26 & 19 & 24 \\
      13 &  8 & 43 &  4 & 41 & 22 & 17 & 28 & 33 \\
      44 & 39 &  2 & 15 & 10 & 35 & 30 & 25 & 20 \\
       1 & 14 &  9 & 40 &  3 & 16 & 21 & 34 & 29
    \end{tabular}
  \end{table}\<close>
abbreviation "kp5x9ul \<equiv> the (to_path 
  [[7,12,37,42,5,18,23,32,27],
  [38,45,6,11,36,31,26,19,24],
  [13,8,43,4,41,22,17,28,33],
  [44,39,2,15,10,35,30,25,20],
  [1,14,9,40,3,16,21,34,29]])"
lemma kp_5x9_ul: "knights_path b5x9 kp5x9ul"
  by (simp only: knights_path_exec_simp) eval

abbreviation "b7x7 \<equiv> board 7 7"

text \<open>A Knight's path for the \<open>(7\<times>7)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllll}
       9 & 30 & 19 & 42 &  7 & 32 & 17 \\
      20 & 49 &  8 & 31 & 18 & 43 &  6 \\
      29 & 10 & 41 & 36 & 39 & 16 & 33 \\
      48 & 21 & 38 & 27 & 34 &  5 & 44 \\
      11 & 28 & 35 & 40 & 37 & 26 & 15 \\
      22 & 47 &  2 & 13 & 24 & 45 &  4 \\
       1 & 12 & 23 & 46 &  3 & 14 & 25
    \end{tabular}
  \end{table}\<close>
abbreviation "kp7x7ul \<equiv> the (to_path 
  [[9,30,19,42,7,32,17],
  [20,49,8,31,18,43,6],
  [29,10,41,36,39,16,33],
  [48,21,38,27,34,5,44],
  [11,28,35,40,37,26,15],
  [22,47,2,13,24,45,4],
  [1,12,23,46,3,14,25]])"
lemma kp_7x7_ul: "knights_path b7x7 kp7x7ul"
  by (simp only: knights_path_exec_simp) eval

abbreviation "b7x9 \<equiv> board 7 9"

text \<open>A Knight's path for the \<open>(7\<times>9)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
      59 &  4 & 17 & 50 & 37 &  6 & 19 & 30 & 39 \\
      16 & 63 & 58 &  5 & 18 & 51 & 38 &  7 & 20 \\
       3 & 60 & 49 & 36 & 57 & 42 & 29 & 40 & 31 \\
      48 & 15 & 62 & 43 & 52 & 35 & 56 & 21 &  8 \\
      61 &  2 & 13 & 26 & 45 & 28 & 41 & 32 & 55 \\
      14 & 47 & 44 & 11 & 24 & 53 & 34 &  9 & 22 \\
       1 & 12 & 25 & 46 & 27 & 10 & 23 & 54 & 33
    \end{tabular}
  \end{table}\<close>
abbreviation "kp7x9ul \<equiv> the (to_path 
  [[59,4,17,50,37,6,19,30,39],
  [16,63,58,5,18,51,38,7,20],
  [3,60,49,36,57,42,29,40,31],
  [48,15,62,43,52,35,56,21,8],
  [61,2,13,26,45,28,41,32,55],
  [14,47,44,11,24,53,34,9,22],
  [1,12,25,46,27,10,23,54,33]])"
lemma kp_7x9_ul: "knights_path b7x9 kp7x9ul"
  by (simp only: knights_path_exec_simp) eval

abbreviation "b9x7 \<equiv> board 9 7"

text \<open>A Knight's path for the \<open>(9\<times>7)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllll}
       5 & 20 & 53 & 48 &  7 & 22 & 31 \\
      52 & 63 &  6 & 21 & 32 & 55 &  8 \\
      19 &  4 & 49 & 54 & 47 & 30 & 23 \\
      62 & 51 & 46 & 33 & 56 &  9 & 58 \\
       3 & 18 & 61 & 50 & 59 & 24 & 29 \\
      14 & 43 & 34 & 45 & 28 & 57 & 10 \\
      17 &  2 & 15 & 60 & 35 & 38 & 25 \\
      42 & 13 & 44 & 27 & 40 & 11 & 36 \\
       1 & 16 & 41 & 12 & 37 & 26 & 39
    \end{tabular}
  \end{table}\<close>
abbreviation "kp9x7ul \<equiv> the (to_path 
  [[5,20,53,48,7,22,31],
  [52,63,6,21,32,55,8],
  [19,4,49,54,47,30,23],
  [62,51,46,33,56,9,58],
  [3,18,61,50,59,24,29],
  [14,43,34,45,28,57,10],
  [17,2,15,60,35,38,25],
  [42,13,44,27,40,11,36],
  [1,16,41,12,37,26,39]])"
lemma kp_9x7_ul: "knights_path b9x7 kp9x7ul"
  by (simp only: knights_path_exec_simp) eval

abbreviation "b9x9 \<equiv> board 9 9"

text \<open>A Knight's path for the \<open>(9\<times>9)\<close>-board that starts in the lower-left and ends in the 
upper-left.
  \begin{table}[H]
    \begin{tabular}{lllllllll}
      13 & 26 & 39 & 52 & 11 & 24 & 37 & 50 &  9 \\
      40 & 81 & 12 & 25 & 38 & 51 & 10 & 23 & 36 \\
      27 & 14 & 53 & 58 & 63 & 68 & 73 &  8 & 49 \\
      80 & 41 & 64 & 67 & 72 & 57 & 62 & 35 & 22 \\
      15 & 28 & 59 & 54 & 65 & 74 & 69 & 48 &  7 \\
      42 & 79 & 66 & 71 & 76 & 61 & 56 & 21 & 34 \\
      29 & 16 & 77 & 60 & 55 & 70 & 75 &  6 & 47 \\
      78 & 43 &  2 & 31 & 18 & 45 &  4 & 33 & 20 \\
       1 & 30 & 17 & 44 &  3 & 32 & 19 & 46 &  5
    \end{tabular}
  \end{table}\<close>
abbreviation "kp9x9ul \<equiv> the (to_path 
  [[13,26,39,52,11,24,37,50,9],
  [40,81,12,25,38,51,10,23,36],
  [27,14,53,58,63,68,73,8,49],
  [80,41,64,67,72,57,62,35,22],
  [15,28,59,54,65,74,69,48,7],
  [42,79,66,71,76,61,56,21,34],
  [29,16,77,60,55,70,75,6,47],
  [78,43,2,31,18,45,4,33,20],
  [1,30,17,44,3,32,19,46,5]])"
lemma kp_9x9_ul: "knights_path b9x9 kp9x9ul"
  by (simp only: knights_path_exec_simp) eval 

text \<open>The following lemma is a sub-proof used in Lemma 4 in \<^cite>\<open>"cull_decurtins_1987"\<close>. 
I moved the sub-proof out to a separate lemma.\<close>
lemma knights_circuit_exists_even_n_gr10:
  assumes "even n" "n \<ge> 10" "m \<ge> 5"
          "\<exists>ps. knights_path (board (n-5) m) ps \<and> hd ps = (int (n-5),1) 
            \<and> last ps = (int (n-5)-1,int m-1)"
  shows "\<exists>ps. knights_circuit (board m n) ps"
  using assms
proof -
  let ?b\<^sub>2="board (n-5) m"
  assume "n \<ge> 10"
  then obtain ps\<^sub>2 where ps\<^sub>2_prems: "knights_path ?b\<^sub>2 ps\<^sub>2" "hd ps\<^sub>2 = (int (n-5),1)" 
      "last ps\<^sub>2 = (int (n-5)-1,int m-1)"
    using assms by auto
  let ?ps\<^sub>2_m2="mirror2 ps\<^sub>2"
  have ps\<^sub>2_m2_prems: "knights_path ?b\<^sub>2 ?ps\<^sub>2_m2" "hd ?ps\<^sub>2_m2 = (int (n-5),int m)" 
      "last ?ps\<^sub>2_m2 = (int (n-5)-1,2)"
    using ps\<^sub>2_prems mirror2_knights_path hd_mirror2 last_mirror2 by auto

  obtain ps\<^sub>1 where ps\<^sub>1_prems: "knights_path (board 5 m) ps\<^sub>1" "hd ps\<^sub>1 = (1,1)""last ps\<^sub>1 = (2,int m-1)"
    using assms knights_path_5xm_exists by auto
  let ?ps\<^sub>1'="trans_path (int (n-5),0) ps\<^sub>1"
  let ?b\<^sub>1'="trans_board (int (n-5),0) (board 5 m)"
  have ps\<^sub>1'_prems: "knights_path ?b\<^sub>1' ?ps\<^sub>1'" "hd ?ps\<^sub>1' = (int (n-5)+1,1)" 
      "last ?ps\<^sub>1' = (int (n-5)+2,int m-1)"
    using ps\<^sub>1_prems trans_knights_path knights_path_non_nil hd_trans_path last_trans_path by auto

  let ?ps="?ps\<^sub>1'@?ps\<^sub>2_m2"
  let ?psT="transpose ?ps"

  have "n-5 \<ge> 5" using \<open>n \<ge> 10\<close> by auto
  have inter: "?b\<^sub>1' \<inter> ?b\<^sub>2 = {}"
    unfolding trans_board_def board_def using \<open>n-5 \<ge> 5\<close> by auto
  have union: "?b\<^sub>1' \<union> ?b\<^sub>2 = board n m"
    using \<open>n-5 \<ge> 5\<close> board_concatT[of "n-5" m 5] by auto

  have vs: "valid_step (last ?ps\<^sub>1') (hd ?ps\<^sub>2_m2)" and "valid_step (last ?ps\<^sub>2_m2) (hd ?ps\<^sub>1')"
    unfolding valid_step_def using ps\<^sub>1'_prems ps\<^sub>2_m2_prems by auto
  then have vs_c: "valid_step (last ?ps) (hd ?ps)"
    using ps\<^sub>1'_prems ps\<^sub>2_m2_prems knights_path_non_nil by auto

  have "knights_path (board n m) ?ps"
    using ps\<^sub>1'_prems ps\<^sub>2_m2_prems inter vs union knights_path_append[of ?b\<^sub>1' ?ps\<^sub>1' ?b\<^sub>2 ?ps\<^sub>2_m2] 
    by auto
  then have "knights_circuit (board n m) ?ps"
    unfolding knights_circuit_def using vs_c by auto
  then show ?thesis using transpose_knights_circuit by auto
qed

text \<open>For every \<open>n\<times>m\<close>-board with \<open>min n m \<ge> 5\<close> and odd \<open>n\<close> there exists a Knight's path that 
starts in \<open>(n,1)\<close> (top-left) and ends in \<open>(n-1,m-1)\<close> (top-right).\<close>
text \<open>This lemma formalizes Lemma 4 from \<^cite>\<open>"cull_decurtins_1987"\<close>. Formalizing the proof of 
this lemma was quite challenging as a lot of details on how to exactly combine the boards are 
left out in the original proof in \<^cite>\<open>"cull_decurtins_1987"\<close>.\<close>
lemma knights_path_odd_n_exists:
  assumes "odd n" "min n m \<ge> 5"
  shows "\<exists>ps. knights_path (board n m) ps \<and> hd ps = (int n,1) \<and> last ps = (int n-1,int m-1)"
  using assms
proof -
  obtain x where "x = n + m" by auto
  then show ?thesis
    using assms
  proof (induction x arbitrary: n m rule: less_induct)
    case (less x)
    then have "m = 5 \<or> m = 6 \<or> m = 7 \<or> m = 8 \<or> m = 9 \<or> m \<ge> 10" by auto
    then show ?case
    proof (elim disjE)
      assume [simp]: "m = 5"
      have "odd n" "n \<ge> 5" using less by auto
      then have "n = 5 \<or> n = 7 \<or> n = 9 \<or> n-5 \<ge> 5" by presburger
      then show ?thesis
      proof (elim disjE)
        assume [simp]: "n = 5"
        let ?ps="mirror1 (transpose kp5x5ul)"
        have kp: "knights_path (board n m) ?ps"
          using kp_5x5_ul rot90_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 5\<close> \<open>n = 5\<close> | eval)+
        then show ?thesis using kp by auto
      next
        assume [simp]: "n = 7"
        let ?ps="mirror1 (transpose kp5x7ul)"
        have kp: "knights_path (board n m) ?ps"
          using kp_5x7_ul rot90_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 5\<close> \<open>n = 7\<close> | eval)+
        then show ?thesis using kp by auto
      next
        assume [simp]: "n = 9"
        let ?ps="mirror1 (transpose kp5x9ul)"
        have kp: "knights_path (board n m) ?ps"
          using kp_5x9_ul rot90_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 5\<close> \<open>n = 9\<close> | eval)+
        then show ?thesis using kp by auto
      next
        let ?b\<^sub>2="board m (n-5)"
        assume "n-5 \<ge> 5"
        then have "\<exists>ps. knights_circuit ?b\<^sub>2 ps"
        proof -
          have "n-5 = 6 \<or> n-5 = 8 \<or> n-5 \<ge> 10" 
            using \<open>n-5 \<ge> 5\<close> less by presburger
          then show ?thesis
          proof (elim disjE)
            assume "n-5 = 6"
            then obtain ps where "knights_circuit (board (n-5) m) ps"
              using knights_path_6xm_exists[of m] by auto
            then show ?thesis 
              using transpose_knights_circuit by auto
          next
            assume "n-5 = 8"
            then obtain ps where "knights_circuit (board (n-5) m) ps"
              using knights_path_8xm_exists[of m] by auto
            then show ?thesis 
              using transpose_knights_circuit by auto
          next
            assume "n-5 \<ge> 10"
            then show ?thesis 
              using less less.IH[of "n-10+m" "n-10" m]
                    knights_circuit_exists_even_n_gr10[of "n-5" m] by auto
          qed
        qed
        then obtain ps\<^sub>2 where "knights_circuit ?b\<^sub>2 ps\<^sub>2" "hd ps\<^sub>2 = (1,1)" "last ps\<^sub>2 = (3,2)"
          using \<open>n-5 \<ge> 5\<close> rotate_knights_circuit[of m "n-5"] by auto
        then have rev_ps\<^sub>2_prems: "knights_path ?b\<^sub>2 (rev ps\<^sub>2)" "valid_step (last ps\<^sub>2) (hd ps\<^sub>2)"
            "hd (rev ps\<^sub>2) = (3,2)" "last (rev ps\<^sub>2) = (1,1)"
          unfolding knights_circuit_def using knights_path_rev by (auto simp: hd_rev last_rev)

        let ?ps\<^sub>1="kp5x5ul"
        have ps\<^sub>1_prems: "knights_path (board 5 5) ?ps\<^sub>1" "hd ?ps\<^sub>1 = (1,1)" "last ?ps\<^sub>1 = (4,2)"
          using kp_5x5_ul by simp eval+

        have "16 < length ?ps\<^sub>1" "last (take 16 ?ps\<^sub>1) = (4,5)" "hd (drop 16 ?ps\<^sub>1) = (2,4)" by eval+
        then have si: "step_in ?ps\<^sub>1 (4,5) (2,4)"
          unfolding step_in_def using zero_less_numeral by blast

        have vs: "valid_step (4,5) (3,int 5+2)" "valid_step (1,int 5+1) (2,4)"
          unfolding valid_step_def by auto

        obtain ps where "knights_path (board m n) ps" "hd ps = (1,1)" "last ps = (4,2)"
          using \<open>n-5 \<ge> 5\<close> ps\<^sub>1_prems rev_ps\<^sub>2_prems si vs
              knights_path_split_concat[of 5 5 ?ps\<^sub>1 "n-5" "rev ps\<^sub>2" "(4,5)" "(2,4)"] by auto
        then show ?thesis
          using rot90_knights_path hd_rot90_knights_path last_rot90_knights_path by fastforce
      qed
    next
      assume [simp]: "m = 6"
      then obtain ps where 
          ps_prems: "knights_path (board m n) ps" "hd ps = (1,1)" "last ps = (int m-1,2)"
        using less knights_path_6xm_exists[of n] by auto
      let ?ps'="mirror1 (transpose ps)"
      have "knights_path (board n m) ?ps'" "hd ?ps' = (int n,1)" "last ?ps' = (int n-1,int m-1)"
        using ps_prems rot90_knights_path hd_rot90_knights_path last_rot90_knights_path by auto
      then show ?thesis by auto
    next
      assume [simp]: "m = 7"
      have "odd n" "n \<ge> 5" using less by auto
      then have "n = 5 \<or> n = 7 \<or> n = 9 \<or> n-5 \<ge> 5" by presburger
      then show ?thesis
      proof (elim disjE)
        assume [simp]: "n = 5"
        let ?ps="mirror1 kp5x7lr"
        have kp: "knights_path (board n m) ?ps"
          using kp_5x7_lr mirror1_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 7\<close> \<open>n = 5\<close> | eval)+
        then show ?thesis using kp by auto
      next
        assume [simp]: "n = 7"
        let ?ps="mirror1 (transpose kp7x7ul)"
        have kp: "knights_path (board n m) ?ps"
          using kp_7x7_ul rot90_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 7\<close> \<open>n = 7\<close> | eval)+
        then show ?thesis using kp by auto
      next
        assume [simp]: "n = 9"
        let ?ps="mirror1 (transpose kp7x9ul)"
        have kp: "knights_path (board n m) ?ps"
          using kp_7x9_ul rot90_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 7\<close> \<open>n = 9\<close> | eval)+
        then show ?thesis using kp by auto
      next
        let ?b\<^sub>2="board m (n-5)"
        let ?b\<^sub>2T="board (n-5) m"
        assume "n-5 \<ge> 5"
        then have "\<exists>ps. knights_circuit ?b\<^sub>2 ps"
        proof -
          have "n-5 = 6 \<or> n-5 = 8 \<or> n-5 \<ge> 10" 
            using \<open>n-5 \<ge> 5\<close> less by presburger
          then show ?thesis
          proof (elim disjE)
            assume "n-5 = 6"
            then obtain ps where "knights_circuit (board (n-5) m) ps"
              using knights_path_6xm_exists[of m] by auto
            then show ?thesis 
              using transpose_knights_circuit by auto
          next
            assume "n-5 = 8"
            then obtain ps where "knights_circuit (board (n-5) m) ps"
              using knights_path_8xm_exists[of m] by auto
            then show ?thesis 
              using transpose_knights_circuit by auto
          next
            assume "n-5 \<ge> 10"
            then show ?thesis 
              using less less.IH[of "n-10+m" "n-10" m]
                    knights_circuit_exists_even_n_gr10[of "n-5" m] by auto
          qed
        qed
        then obtain ps\<^sub>2 where ps\<^sub>2_prems: "knights_circuit ?b\<^sub>2 ps\<^sub>2" "hd ps\<^sub>2 = (1,1)" 
            "last ps\<^sub>2 = (3,2)"
          using \<open>n-5 \<ge> 5\<close> rotate_knights_circuit[of m "n-5"] by auto
        let ?ps\<^sub>2T="transpose ps\<^sub>2"
        have ps\<^sub>2T_prems: "knights_path ?b\<^sub>2T ?ps\<^sub>2T" "hd ?ps\<^sub>2T = (1,1)" "last ?ps\<^sub>2T = (2,3)"
          using ps\<^sub>2_prems transpose_knights_path knights_path_non_nil hd_transpose last_transpose 
          unfolding knights_circuit_def transpose_square_def by auto

        let ?ps\<^sub>1="kp5x7lr"
        have ps\<^sub>1_prems: "knights_path b5x7 ?ps\<^sub>1" "hd ?ps\<^sub>1 = (1,1)" "last ?ps\<^sub>1 = (2,6)"
          using kp_5x7_lr by simp eval+

        have "29 < length ?ps\<^sub>1" "last (take 29 ?ps\<^sub>1) = (4,2)" "hd (drop 29 ?ps\<^sub>1) = (5,4)" by eval+
        then have si: "step_in ?ps\<^sub>1 (4,2) (5,4)"
          unfolding step_in_def using zero_less_numeral by blast

        have vs: "valid_step (4,2) (int 5+1,1)" "valid_step (int 5+2,3) (5,4)"
          unfolding valid_step_def by auto

        obtain ps where "knights_path (board n m) ps" "hd ps = (1,1)" "last ps = (2,6)"
          using \<open>n-5 \<ge> 5\<close> ps\<^sub>1_prems ps\<^sub>2T_prems si vs
              knights_path_split_concatT[of 5 m ?ps\<^sub>1 "n-5" ?ps\<^sub>2T "(4,2)" "(5,4)"] by auto
        then show ?thesis
          using mirror1_knights_path hd_mirror1 last_mirror1 by fastforce
      qed
    next
      assume [simp]: "m = 8"
      then obtain ps where ps_prems: "knights_path (board m n) ps" "hd ps = (1,1)" 
          "last ps = (int m-1,2)"
        using less knights_path_8xm_exists[of n] by auto
      let ?ps'="mirror1 (transpose ps)"
      have "knights_path (board n m) ?ps'" "hd ?ps' = (int n,1)" "last ?ps' = (int n-1,int m-1)"
        using ps_prems rot90_knights_path hd_rot90_knights_path last_rot90_knights_path by auto
      then show ?thesis by auto
    next
      assume [simp]: "m = 9"
      have "odd n" "n \<ge> 5" using less by auto
      then have "n = 5 \<or> n = 7 \<or> n = 9 \<or> n-5 \<ge> 5" by presburger
      then show ?thesis
      proof (elim disjE)
        assume [simp]: "n = 5"
        let ?ps="mirror1 kp5x9lr"
        have kp: "knights_path (board n m) ?ps"
          using kp_5x9_lr mirror1_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 9\<close> \<open>n = 5\<close> | eval)+
        then show ?thesis using kp by auto
      next
        assume [simp]: "n = 7"
        let ?ps="mirror1 (transpose kp9x7ul)"
        have kp: "knights_path (board n m) ?ps"
          using kp_9x7_ul rot90_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 9\<close> \<open>n = 7\<close> | eval)+
        then show ?thesis using kp by auto
      next
        assume [simp]: "n = 9"
        let ?ps="mirror1 (transpose kp9x9ul)"
        have kp: "knights_path (board n m) ?ps"
          using kp_9x9_ul rot90_knights_path by auto
        have "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
          by (simp only: \<open>m = 9\<close> \<open>n = 9\<close> | eval)+
        then show ?thesis using kp by auto
      next
        let ?b\<^sub>2="board m (n-5)"
        let ?b\<^sub>2T="board (n-5) m"
        assume "n-5 \<ge> 5"
        then have "\<exists>ps. knights_circuit ?b\<^sub>2 ps"
        proof -
          have "n-5 = 6 \<or> n-5 = 8 \<or> n-5 \<ge> 10" 
            using \<open>n-5 \<ge> 5\<close> less by presburger
          then show ?thesis
          proof (elim disjE)
            assume "n-5 = 6"
            then obtain ps where "knights_circuit (board (n-5) m) ps"
              using knights_path_6xm_exists[of m] by auto
            then show ?thesis 
              using transpose_knights_circuit by auto
          next
            assume "n-5 = 8"
            then obtain ps where "knights_circuit (board (n-5) m) ps"
              using knights_path_8xm_exists[of m] by auto
            then show ?thesis 
              using transpose_knights_circuit by auto
          next
            assume "n-5 \<ge> 10"
            then show ?thesis 
              using less less.IH[of "n-10+m" "n-10" m]
                    knights_circuit_exists_even_n_gr10[of "n-5" m] by auto
          qed
        qed
        then obtain ps\<^sub>2 where ps\<^sub>2_prems: "knights_circuit ?b\<^sub>2 ps\<^sub>2" "hd ps\<^sub>2 = (1,1)" 
            "last ps\<^sub>2 = (3,2)"
          using \<open>n-5 \<ge> 5\<close> rotate_knights_circuit[of m "n-5"] by auto
        let ?ps\<^sub>2T="transpose (rev ps\<^sub>2)"
        have ps\<^sub>2T_prems: "knights_path ?b\<^sub>2T ?ps\<^sub>2T" "hd ?ps\<^sub>2T = (2,3)" "last ?ps\<^sub>2T = (1,1)"
          using ps\<^sub>2_prems knights_path_rev transpose_knights_path knights_path_non_nil 
                hd_transpose last_transpose 
          unfolding knights_circuit_def transpose_square_def by (auto simp: hd_rev last_rev)

        let ?ps\<^sub>1="kp5x9lr"
        have ps\<^sub>1_prems: "knights_path b5x9 ?ps\<^sub>1" "hd ?ps\<^sub>1 = (1,1)" "last ?ps\<^sub>1 = (2,8)"
          using kp_5x9_lr by simp eval+

        have "16 < length ?ps\<^sub>1" "last (take 16 ?ps\<^sub>1) = (5,4)" "hd (drop 16 ?ps\<^sub>1) = (4,2)" by eval+
        then have si: "step_in ?ps\<^sub>1 (5,4) (4,2)"
          unfolding step_in_def using zero_less_numeral by blast

        have vs: "valid_step (5,4) (int 5+2,3)" "valid_step (int 5+1,1) (4,2)"
          unfolding valid_step_def by auto

        obtain ps where "knights_path (board n m) ps" "hd ps = (1,1)" "last ps = (2,8)"
          using \<open>n-5 \<ge> 5\<close> ps\<^sub>1_prems ps\<^sub>2T_prems si vs
              knights_path_split_concatT[of 5 m ?ps\<^sub>1 "n-5" ?ps\<^sub>2T "(5,4)" "(4,2)"] by auto
        then show ?thesis
          using mirror1_knights_path hd_mirror1 last_mirror1 by fastforce
      qed
    next
      let ?b\<^sub>1="board n 5"
      let ?b\<^sub>2="board n (m-5)"
      assume "m \<ge> 10"
      then have "n+5 < x" "5 \<le> min n 5" "n+(m-5) < x" "5 \<le> min n (m-5)" 
        using less by auto
      then obtain ps\<^sub>1 ps\<^sub>2 where kp_prems: 
          "knights_path ?b\<^sub>1 ps\<^sub>1" "hd ps\<^sub>1 = (int n,1)" "last ps\<^sub>1 = (int n-1,4)"
          "knights_path (board n (m-5)) ps\<^sub>2" "hd ps\<^sub>2 = (int n,1)" "last ps\<^sub>2 = (int n-1,int (m-5)-1)"
        using less.prems less.IH[of "n+5" n "5"] less.IH[of "n+(m-5)" n "m-5"] by auto
      let ?ps="ps\<^sub>1@trans_path (0,int 5) ps\<^sub>2"
      have "valid_step (last ps\<^sub>1) (int n,int 5+1)" 
        unfolding valid_step_def using kp_prems by auto
      then have "knights_path (board n m) ?ps" "hd ?ps = (int n,1)" "last ?ps = (int n-1,int m-1)"
        using \<open>m \<ge> 10\<close> kp_prems knights_path_concat[of n 5 ps\<^sub>1 "m-5" ps\<^sub>2] 
              knights_path_non_nil trans_path_non_nil last_trans_path by auto
      then show ?thesis by auto
    qed
  qed
qed

text \<open>Auxiliary lemma that constructs a Knight's circuit if \<open>m \<ge> 5\<close> and \<open>n \<ge> 10 \<and> even n\<close>.\<close>
lemma knights_circuit_exists_n_even_gr_10: 
  assumes "n \<ge> 10 \<and> even n" "m \<ge> 5"
  shows "\<exists>ps. knights_circuit (board n m) ps"
  using assms
proof -
  obtain ps\<^sub>1 where ps\<^sub>1_prems: "knights_path (board 5 m) ps\<^sub>1" "hd ps\<^sub>1 = (1,1)" 
      "last ps\<^sub>1 = (2,int m-1)"
    using assms knights_path_5xm_exists by auto
  let ?ps\<^sub>1'="trans_path (int (n-5),0) ps\<^sub>1"
  let ?b5xm'="trans_board (int (n-5),0) (board 5 m)"
  have ps\<^sub>1'_prems: "knights_path ?b5xm' ?ps\<^sub>1'" "hd ?ps\<^sub>1' = (int (n-5)+1,1)" 
      "last ?ps\<^sub>1' = (int (n-5)+2,int m-1)"
    using ps\<^sub>1_prems trans_knights_path knights_path_non_nil hd_trans_path last_trans_path by auto
    
  assume "n \<ge> 10 \<and> even n"
  then have "odd (n-5)" "min (n-5) m \<ge> 5" using assms by auto
  then obtain ps\<^sub>2 where ps\<^sub>2_prems: "knights_path (board (n-5) m) ps\<^sub>2" "hd ps\<^sub>2 = (int (n-5),1)" 
      "last ps\<^sub>2 = (int (n-5)-1,int m-1)"
    using knights_path_odd_n_exists[of "n-5" m] by auto
  let ?ps\<^sub>2'="mirror2 ps\<^sub>2"
  have ps\<^sub>2'_prems: "knights_path (board (n-5) m) ?ps\<^sub>2'" "hd ?ps\<^sub>2' = (int (n-5),int m)" 
      "last ?ps\<^sub>2' = (int (n-5)-1,2)"
    using ps\<^sub>2_prems mirror2_knights_path hd_mirror2 last_mirror2 by auto

  have inter: "?b5xm' \<inter> board (n-5) m = {}" 
    unfolding trans_board_def board_def by auto 

  have union: "board n m = ?b5xm' \<union> board (n-5) m"
    using \<open>n \<ge> 10 \<and> even n\<close> board_concatT[of "n-5" m 5] by auto

  have vs: "valid_step (last ?ps\<^sub>1') (hd ?ps\<^sub>2')" "valid_step (last ?ps\<^sub>2') (hd ?ps\<^sub>1')"
    using ps\<^sub>1'_prems ps\<^sub>2'_prems unfolding valid_step_def by auto

  let ?ps="?ps\<^sub>1' @ ?ps\<^sub>2'"
  have "last ?ps = last ?ps\<^sub>2'" "hd ?ps = hd ?ps\<^sub>1'"
    using ps\<^sub>1'_prems ps\<^sub>2'_prems knights_path_non_nil by auto
  then have vs_c: "valid_step (last ?ps) (hd ?ps)"
    using vs by auto

  have "knights_path (board n m) ?ps"
    using ps\<^sub>1'_prems ps\<^sub>2'_prems inter union vs knights_path_append by auto
  then show ?thesis
    using vs_c unfolding knights_circuit_def by blast
qed

text \<open>Final Theorem 1: For every \<open>n\<times>m\<close>-board with \<open>min n m \<ge> 5\<close> and \<open>n*m\<close> even there exists a 
Knight's circuit.\<close>
theorem knights_circuit_exists: 
  assumes "min n m \<ge> 5" "even (n*m)"
  shows "\<exists>ps. knights_circuit (board n m) ps"
  using assms
proof -
  have "n = 6 \<or> m = 6 \<or> n = 8 \<or> m = 8 \<or> (n \<ge> 10 \<and> even n) \<or> (m \<ge> 10 \<and> even m)"
    using assms by auto
  then show ?thesis
  proof (elim disjE)
    assume "n = 6"
    then show ?thesis
      using assms knights_path_6xm_exists by auto
  next
    assume "m = 6"
    then obtain ps where "knights_circuit (board m n) ps"
      using assms knights_path_6xm_exists by auto
    then show ?thesis
      using transpose_knights_circuit by auto
  next
    assume "n = 8"
    then show ?thesis
      using assms knights_path_8xm_exists by auto
  next
    assume "m = 8"
    then obtain ps where "knights_circuit (board m n) ps"
      using assms knights_path_8xm_exists by auto
    then show ?thesis
      using transpose_knights_circuit by auto
  next
    assume "n \<ge> 10 \<and> even n"
    then show ?thesis
      using assms knights_circuit_exists_n_even_gr_10 by auto
  next
    assume "m \<ge> 10 \<and> even m"
    then obtain ps where "knights_circuit (board m n) ps"
      using assms knights_circuit_exists_n_even_gr_10 by auto
    then show ?thesis
      using transpose_knights_circuit by auto
  qed
qed

text \<open>Final Theorem 2: for every \<open>n\<times>m\<close>-board with \<open>min n m \<ge> 5\<close> there exists a Knight's path.\<close>
theorem knights_path_exists: 
  assumes "min n m \<ge> 5"
  shows "\<exists>ps. knights_path (board n m) ps"
  using assms
proof -
  have "odd n \<or> odd m \<or> even (n*m)" by simp
  then show ?thesis
  proof (elim disjE)
    assume "odd n"
    then show ?thesis
      using assms knights_path_odd_n_exists by auto
  next
    assume "odd m"
    then obtain ps where "knights_path (board m n) ps"
      using assms knights_path_odd_n_exists by auto
    then show ?thesis
      using transpose_knights_path by auto
  next
    assume "even (n*m)"
    then show ?thesis
      using assms knights_circuit_exists by (auto simp: knights_circuit_def)
  qed
qed

text \<open>THE END\<close>

end