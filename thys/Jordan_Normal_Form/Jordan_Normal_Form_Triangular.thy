(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Computing Jordan Normal Forms from Upper-Triangular Matrices\<close>

theory Jordan_Normal_Form_Triangular
imports 
  Jordan_Normal_Form
  Column_Operations
begin

subsection \<open>Pseudo Code Algorithm\<close>

text \<open>The following algorithm is used to compute JNFs from upper-triangular matrices.
It was generalized from \cite[Sect.~11.1.4]{PO07} where this algorithm was not
explicitly specified but only applied on an example. We further introduced step 2
which does not occur in the textbook description.

\begin{enumerate} 
\item[1.] Eliminate entries within blocks besides EV $a$ and above EV $b$ for $a \neq b$:
    for $A_{ij}$ with EV $a$ left of it, and EV $b$ below of it, perform
      @{term "add_col_sub_row (A\<^sub>i\<^sub>j / (b - a)) i j"}.
    The iteration should be by first increasing $j$ and the inner loop by decreasing $i$.
      
\item[2.] Move rows of same EV together, can only be done after 1., 
    otherwise triangular-property is lost.
    Say both rows $i$ and $j$ ($i < j$) contain EV $a$, but all rows between $i$ and $j$ have different EV.
    Then perform
      @{term "swap_cols_rows (i+1) j"}, 
      @{term "swap_cols_rows (i+2) j"}, 
      \ldots
      @{term "swap_cols_rows (j-1) j"}.
    Afterwards row $j$ will be at row $i+1$, and rows $i+1,\ldots,j-1$ will be moved to $i+2,\ldots,j$.
    The global iteration works by increasing $j$.

\item[3.] Transform each EV-block into JNF, do this for increasing upper $n \times k$ matrices, 
    where each new column $k$ will be treated as follows.
\begin{enumerate}
 \item[a)] Eliminate entries $A_{ik}$ in rows of form $0 \ldots 0\ ev\ 1\ 0 \ldots 0\ A_{ik}$:
         @{term "add_col_sub_row (-A\<^sub>i\<^sub>k) (i+1) k"}.
       Perform elimination by increasing $i$.
\item[b)] Figure out largest JB (of $n-1 \times n-1$ sub-matrix) with lowest row of form $0 \ldots 0\ ev\ 0 \ldots 0\ A_{lk}$
       where $A_{lk} \neq 0$, and set $x := A_{lk}$.
\item[c)] If such a JB does not exist, continue with next column.
  Otherwise, eliminate all other non-zero-entries $y := A_{ik}$ via row $l$:
         @{term "add_col_sub_row (y/x) i l"},
         @{term "add_col_sub_row (y/x) (i-1) (l-1)"},
         @{term "add_col_sub_row (y/x) (i-2) (l-2)"}, \ldots
         where the number of steps is determined by the size of the JB left-above of $A_{ik}$.
         Perform an iteration over $i$.
\item[d)] Normalize value in row $l$ to 1:
         @{term "mult_col_div_row (1/x) k"}.
\item[e)] Move the 1 down from row $l$ to row $k-1$:
         @{term "swap_cols_rows (l+1) k"},
         @{term "swap_cols_rows (l+2) k"},
         \ldots,
         @{term "swap_cols_rows (k-1) k"}.
\end{enumerate}
\end{enumerate}
\<close>


subsection \<open>Real Algorithm\<close>

fun lookup_ev :: "'a \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> nat option" where
  "lookup_ev ev 0 A = None"
| "lookup_ev ev (Suc i) A = (if A $$ (i,i) = ev then Some i else lookup_ev ev i A)"

function swap_cols_rows_block :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "swap_cols_rows_block i j A = (if i < j then
    swap_cols_rows_block (Suc i) j (swap_cols_rows i j A) else A)"
  by pat_completeness auto
termination by (relation "measure (\<lambda> (i,j,A). j - i)") auto

fun identify_block_main :: "'a :: one \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat" where
  "identify_block_main ev A 0 = 0"
| "identify_block_main ev A (Suc i) = (if A $$ (i,i) = ev \<and> A $$ (i,Suc i) = 1 then
    identify_block_main ev A i else (Suc i))"

definition identify_block :: "'a :: one mat \<Rightarrow> nat \<Rightarrow> 'a \<times> nat" where
  "identify_block A i = (let ev = A $$ (i,i) in (ev, identify_block_main ev A i))"

function identify_blocks_main :: "'a :: ring_1 \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list" where
  "identify_blocks_main ev A 0 list = list"
| "identify_blocks_main ev A (Suc i_end) list = (
    let (ev', i_begin) = identify_block A i_end
    in (if ev' = ev then  
      identify_blocks_main ev A i_begin ((i_begin, i_end) # list)
    else list))"
  by pat_completeness auto

definition identify_blocks :: "'a :: ring_1 mat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)list" where
  "identify_blocks A i = identify_blocks_main (A $$ (i,i)) A i []"

fun find_largest_block :: "nat \<times> nat \<Rightarrow> (nat \<times> nat)list \<Rightarrow> nat \<times> nat" where
  "find_largest_block block [] = block"
| "find_largest_block (m_start,m_end) ((i_start,i_end) # blocks) = 
    (if i_end - i_start \<ge> m_end - m_start then
      find_largest_block (i_start,i_end) blocks else
      find_largest_block (m_start,m_end) blocks)"

context 
  fixes n :: nat
  and ty :: "'a :: field itself"
begin

function step_1_main :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "step_1_main i j A = (if j \<ge> n then A else if i = 0 then step_1_main (j+1) (j+1) A
    else let 
      i' = i - 1;
      ev_left = A $$ (i',i');
      ev_below = A $$ (j,j);
      aij = A $$ (i',j);
      B = if (ev_left \<noteq> ev_below \<and> aij \<noteq> 0) then add_col_sub_row (aij / (ev_below - ev_left)) i' j A else A
     in step_1_main i' j B)"
  by pat_completeness auto
termination by (relation "measures [\<lambda> (i,j,A). n - j, \<lambda> (i,j,A). i]") auto

function step_2_main :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "step_2_main j A = (if j \<ge> n then A 
    else 
      let ev = A $$ (j,j);
        B = (case lookup_ev ev j A of 
          None \<Rightarrow> A
        | Some i \<Rightarrow> swap_cols_rows_block (Suc i) j A
          )
     in step_2_main (Suc j) B)"
  by pat_completeness auto
termination by (relation "measure (\<lambda> (j,A). n - j)") auto

fun step_3_a :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where 
  "step_3_a 0 j A = A"
| "step_3_a (Suc i) j A = (let 
    aij = A $$ (i,j);
    B = (if A $$ (i,i) = A $$ (j,j) \<and> A $$ (i,i+1) = 1 \<and> aij \<noteq> 0 
    then add_col_sub_row (- aij) (Suc i) j A else A)
    in step_3_a i j B)"

fun step_3_c_inner_loop :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "step_3_c_inner_loop val l i 0 A = A"
| "step_3_c_inner_loop val l i (Suc k) A = step_3_c_inner_loop val (l - 1) (i - 1) k 
     (add_col_sub_row val i l A)"

fun step_3_c :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)list \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "step_3_c x l k [] A = A"
| "step_3_c x l k ((i_begin,i_end) # blocks) A = (
    let 
      B = (if i_end = l then A else 
        step_3_c_inner_loop (A $$ (i_end,k) / x) l i_end (Suc i_end - i_begin) A)
      in step_3_c x l k blocks B)"

function step_3_main :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "step_3_main k A = (if k \<ge> n then A 
    else let 
      B = step_3_a (k-1) k A; (* 3_a *)
      all_blocks = identify_blocks B k;
      blocks = filter (\<lambda> block. B $$ (snd block,k) \<noteq> 0) all_blocks;
      F = (if blocks = [] (* column k has only 0s *)
        then B
        else let          
          (l_start,l) = find_largest_block (hd blocks) (tl blocks); (* 3_b *)
          x = B $$ (l,k); 
          C = step_3_c x l k blocks B; (* 3_c *)
          D = mult_col_div_row (inverse x) k C; (* 3_d *)
          E = swap_cols_rows_block (Suc l) k D (* 3_e *)
        in E)
      in step_3_main (Suc k) F)"
  by pat_completeness auto
termination by (relation "measure (\<lambda> (k,A). n - k)") auto

end

definition step_1 :: "'a :: field mat \<Rightarrow> 'a mat" where
  "step_1 A = step_1_main (dim\<^sub>r A) 0 0 A"

definition step_2 :: "'a :: field mat \<Rightarrow> 'a mat" where
  "step_2 A = step_2_main (dim\<^sub>r A) 0 A"

definition step_3 :: "'a :: field mat \<Rightarrow> 'a mat" where
  "step_3 A = step_3_main (dim\<^sub>r A) 1 A"

definition triangular_to_jnf :: "'a :: field mat \<Rightarrow> 'a mat" where
  "triangular_to_jnf = step_3 o step_2 o step_1"  

declare swap_cols_rows_block.simps[simp del]
declare step_1_main.simps[simp del]
declare step_2_main.simps[simp del]
declare step_3_main.simps[simp del]

subsection \<open>Algorithm to extract JNF vector from matrix in JNF\<close>

function jnf_vector_main :: "nat \<Rightarrow> 'a :: one mat \<Rightarrow> (nat \<times> 'a) list" where
  "jnf_vector_main 0 A = []"
| "jnf_vector_main (Suc i_end) A = (let 
    (ev,i_start) = identify_block A i_end 
    in jnf_vector_main i_start A @ [(Suc i_end - i_start, ev)])"
  by pat_completeness auto

definition jnf_vector :: "'a :: one mat \<Rightarrow> (nat \<times> 'a) list" where
  "jnf_vector A = jnf_vector_main (dim\<^sub>r A) A"

definition triangular_to_jnf_vector :: "'a :: field mat \<Rightarrow> (nat \<times> 'a) list" where
  "triangular_to_jnf_vector A = (jnf_vector (triangular_to_jnf A))" 

subsection \<open>Preservation of Dimensions\<close>

lemma swap_cols_rows_block_dims_main: 
  "dim\<^sub>r (swap_cols_rows_block i j A) = dim\<^sub>r A \<and> dim\<^sub>c (swap_cols_rows_block i j A) = dim\<^sub>c A"
proof (induct i j A rule: swap_cols_rows_block.induct)
  case (1 i j A)
  thus ?case unfolding swap_cols_rows_block.simps[of i j A]
    by (auto split: if_splits)
qed

lemma swap_cols_rows_block_dims[simp]: 
  "dim\<^sub>r (swap_cols_rows_block i j A) = dim\<^sub>r A"
  "dim\<^sub>c (swap_cols_rows_block i j A) = dim\<^sub>c A"
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> swap_cols_rows_block i j A \<in> carrier\<^sub>m n n"
  using swap_cols_rows_block_dims_main unfolding mat_carrier_def by auto

lemma step_1_main_dims_main: 
  "dim\<^sub>r (step_1_main n i j A) = dim\<^sub>r A \<and> dim\<^sub>c (step_1_main n i j A) = dim\<^sub>c A"
proof (induct i j A taking: n rule: step_1_main.induct)
  case (1 i j A)
  thus ?case unfolding step_1_main.simps[of n i j A]
    by (auto split: if_splits simp: Let_def)
qed

lemma step_1_main_dims[simp]: 
  "dim\<^sub>r (step_1_main n i j A) = dim\<^sub>r A"
  "dim\<^sub>c (step_1_main n i j A) = dim\<^sub>c A"
  using step_1_main_dims_main by blast+

lemma step_2_main_dims_main: 
  "dim\<^sub>r (step_2_main n j A) = dim\<^sub>r A \<and> dim\<^sub>c (step_2_main n j A) = dim\<^sub>c A"
proof (induct j A taking: n rule: step_2_main.induct)
  case (1 j A)
  thus ?case unfolding step_2_main.simps[of n j A]
    by (auto split: if_splits option.splits simp: Let_def)
qed

lemma step_2_main_dims[simp]: 
  "dim\<^sub>r (step_2_main n j A) = dim\<^sub>r A"
  "dim\<^sub>c (step_2_main n j A) = dim\<^sub>c A"
  using step_2_main_dims_main by blast+

lemma step_3_a_dims_main: 
  "dim\<^sub>r (step_3_a i j A) = dim\<^sub>r A \<and> dim\<^sub>c (step_3_a i j A) = dim\<^sub>c A"
  by (induct i j A rule: step_3_a.induct, auto split: if_splits simp: Let_def)

lemma step_3_a_dims[simp]: 
  "dim\<^sub>r (step_3_a i j A) = dim\<^sub>r A"
  "dim\<^sub>c (step_3_a i j A) = dim\<^sub>c A"
  using step_3_a_dims_main by blast+

lemma step_3_c_inner_loop_dims_main: 
  "dim\<^sub>r (step_3_c_inner_loop val l i j A) = dim\<^sub>r A \<and> dim\<^sub>c (step_3_c_inner_loop val l i j A) = dim\<^sub>c A"
  by (induct val l i j A rule: step_3_c_inner_loop.induct, auto)

lemma step_3_c_inner_loop_dims[simp]: 
  "dim\<^sub>r (step_3_c_inner_loop val l i j A) = dim\<^sub>r A"
  "dim\<^sub>c (step_3_c_inner_loop val l i j A) = dim\<^sub>c A"
  using step_3_c_inner_loop_dims_main by blast+

lemma step_3_c_dims_main: 
  "dim\<^sub>r (step_3_c x l k i A) = dim\<^sub>r A \<and> dim\<^sub>c (step_3_c x l k i A) = dim\<^sub>c A"
  by (induct x l k i A rule: step_3_c.induct, auto simp: Let_def)

lemma step_3_c_dims[simp]: 
  "dim\<^sub>r (step_3_c x l k i A) = dim\<^sub>r A"
  "dim\<^sub>c (step_3_c x l k i A) = dim\<^sub>c A"
  using step_3_c_dims_main by blast+
  
lemma step_3_main_dims_main: 
  "dim\<^sub>r (step_3_main n k A) = dim\<^sub>r A \<and> dim\<^sub>c (step_3_main n k A) = dim\<^sub>c A"
proof (induct k A taking: n rule: step_3_main.induct)
  case (1 k A)
  thus ?case unfolding step_3_main.simps[of n k A]
    by (auto split: if_splits prod.splits option.splits simp: Let_def)
qed

lemma step_3_main_dims[simp]: 
  "dim\<^sub>r (step_3_main n j A) = dim\<^sub>r A"
  "dim\<^sub>c (step_3_main n j A) = dim\<^sub>c A"
  using step_3_main_dims_main by blast+

lemma triangular_to_jnf_steps_dims[simp]: 
  "dim\<^sub>r (step_1 A) = dim\<^sub>r A"
  "dim\<^sub>c (step_1 A) = dim\<^sub>c A"
  "dim\<^sub>r (step_2 A) = dim\<^sub>r A"
  "dim\<^sub>c (step_2 A) = dim\<^sub>c A"
  "dim\<^sub>r (step_3 A) = dim\<^sub>r A"
  "dim\<^sub>c (step_3 A) = dim\<^sub>c A"
  "dim\<^sub>r (triangular_to_jnf A) = dim\<^sub>r A"
  "dim\<^sub>c (triangular_to_jnf A) = dim\<^sub>c A"
  unfolding step_1_def step_2_def step_3_def triangular_to_jnf_def o_def by auto

subsection \<open>Properties of Auxiliary Algorithms\<close>

lemma lookup_ev_Some: 
  "lookup_ev ev j A = Some i \<Longrightarrow> 
  i < j \<and> A $$ (i,i) = ev \<and> (\<forall> k. i < k \<longrightarrow> k < j \<longrightarrow> A $$ (k,k) \<noteq> ev)"
  by (induct j, auto split: if_splits, case_tac "k = j", auto)

lemma lookup_ev_None: "lookup_ev ev j A = None \<Longrightarrow> i < j \<Longrightarrow> A $$ (i,i) \<noteq> ev"
  by (induct j, auto split: if_splits, case_tac "i = j", auto)

lemma swap_cols_rows_block_index[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> i < dim\<^sub>c A \<Longrightarrow> j < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A 
  \<Longrightarrow> low \<le> high \<Longrightarrow> high < dim\<^sub>r A \<Longrightarrow> high < dim\<^sub>c A  
  \<Longrightarrow> swap_cols_rows_block low high A $$ (i,j) = A $$ 
    (if i = low then high else if i > low \<and> i \<le> high then i - 1 else i,
     if j = low then high else if j > low \<and> j \<le> high then j - 1 else j)"
proof (induct low high A rule: swap_cols_rows_block.induct)
  case (1 low high A)
  let ?r = "dim\<^sub>r A" let ?c = "dim\<^sub>c A"
  let ?A = "swap_cols_rows_block low high A"
  let ?B = "swap_cols_rows low high A"
  let ?C = "swap_cols_rows_block (Suc low) high ?B"
  note [simp] = swap_cols_rows_block.simps[of low high A]
  from 1(2-) have lh: "low \<le> high" by simp
  show ?case
  proof (cases "low < high")
    case False
    with lh have lh: "low = high" by auto
    from False have "?A = A" by simp
    with lh show ?thesis by auto
  next
    case True
    hence A: "?A = ?C" by simp
    from True lh have "Suc low \<le> high" by simp
    note IH = 1(1)[unfolded swap_cols_rows_dims, OF True 1(2-5) this 1(7-)]
    note * = 1(2-)
    let ?i = "if i = Suc low then high else if Suc low < i \<and> i \<le> high then i - 1 else i"
    let ?j = "if j = Suc low then high else if Suc low < j \<and> j \<le> high then j - 1 else j"
    have cong: "\<And> i j i' j'. i = i' \<Longrightarrow> j = j' \<Longrightarrow> A $$ (i,j) = A $$ (i',j')" by auto
    have ij: "?i < ?r" "?i < ?c" "?j < ?r" "?j < ?c" "low < ?r" "high < ?r" using * True by auto
    show ?thesis unfolding A IH
      by (subst swap_cols_rows_index[OF ij], rule cong, insert * True, auto)
  qed
qed
  
lemma find_largest_block_main: assumes "find_largest_block block blocks = (m_b, m_e)"
  shows "(m_b, m_e) \<in> insert block (set blocks)
  \<and> (\<forall> b \<in> insert block (set blocks). m_e - m_b \<ge> snd b - fst b)"
  using assms
proof (induct block blocks rule: find_largest_block.induct)
  case (2 m_start m_end i_start i_end blocks)  
  let ?res = "find_largest_block (m_start,m_end) ((i_start,i_end) # blocks)"
  show ?case
  proof (cases "i_end - i_start \<ge> m_end - m_start")
    case True
    with 2(3-) have "find_largest_block (i_start,i_end) blocks = (m_b, m_e)" by auto
    note IH = 2(1)[OF True this]
    thus ?thesis using True by auto
  next
    case False
    with 2(3-) have "find_largest_block (m_start,m_end) blocks = (m_b, m_e)" by auto
    note IH = 2(2)[OF False this]
    thus ?thesis using False by auto
  qed
qed simp

lemma find_largest_block: assumes bl: "blocks \<noteq> []"
  and find: "find_largest_block (hd blocks) (tl blocks) = (m_begin, m_end)"
  shows "(m_begin,m_end) \<in> set blocks"
  "\<And> i_begin i_end. (i_begin,i_end) \<in> set blocks \<Longrightarrow> m_end - m_begin \<ge> i_end - i_begin"
proof -
  from bl have id: "insert (hd blocks) (set (tl blocks)) = set blocks" by (cases blocks, auto)
  from find_largest_block_main[OF find, unfolded id] 
  show "(m_begin,m_end) \<in> set blocks"
    "\<And> i_begin i_end. (i_begin,i_end) \<in> set blocks \<Longrightarrow> m_end - m_begin \<ge> i_end - i_begin" by auto
qed

context 
  fixes ev :: "'a :: one"
  and A :: "'a mat"
begin

lemma identify_block_main: assumes "identify_block_main ev A j = i"
  shows "i \<le> j \<and> (i = 0 \<or> A $$ (i - 1, i - 1) \<noteq> ev \<or> A $$ (i - 1, i) \<noteq> 1) \<and> (\<forall> k. i \<le> k \<longrightarrow> k < j \<longrightarrow> A $$ (k,k) = ev \<and> A $$ (k, Suc k) = 1)"
    (is "?P j")
  using assms
proof (induct j)
  case (Suc j)
  show ?case
  proof (cases "A $$ (j,j) = ev \<and> A $$ (j, Suc j) = 1")
    case False
    with Suc(2) show ?thesis by auto
  next
    case True
    with Suc(2) have "identify_block_main ev A j = i" by simp
    note IH = Suc(1)[OF this] 
    {
      fix k
      assume "k \<ge> i" and "k < Suc j"      
      hence "A $$ (k, k) = ev \<and> A $$ (k, Suc k) = 1"
      proof (cases "k < j")
        case True
        with IH `k \<ge> i` show ?thesis by auto
      next
        case False
        with `k < Suc j` have "k = j" by auto
        with True show ?thesis by auto
      qed
    }
    with IH show ?thesis by auto
  qed
qed simp


lemma identify_block_main_le: "identify_block_main ev A i \<le> i"
  using identify_block_main[OF refl] by blast
end


lemma identify_block: assumes "identify_block A j = (ev,i)"
  shows "i \<le> j"
  "ev = A $$ (j,j)"
  "A $$ (i,i) = A $$ (j,j)"
  "i = 0 \<or> A $$ (i - 1, i - 1) \<noteq> A $$ (j,j) \<or> A $$ (i - 1, i) \<noteq> 1"
  "i \<le> k \<Longrightarrow> k < j \<Longrightarrow> A $$ (k, Suc k) = 1"
  "i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> A $$ (k,k) = A $$ (j,j)"
proof -
  let ?ev = "A $$ (j,j)"
  from assms[unfolded identify_block_def Let_def] have main: "identify_block_main ?ev A j = i"
    and "ev = ?ev" by auto
  show "ev = ?ev" by fact
  note main = identify_block_main[OF main]
  from main show "i \<le> j" by blast
  from main show "i = 0 \<or> A $$ (i - 1, i - 1) \<noteq> ?ev \<or> A $$ (i - 1, i) \<noteq> 1" by blast
  from main have "i < j \<Longrightarrow> A $$ (i,i) = ?ev" by auto
  thus "A $$ (i,i) = ?ev" using `i \<le> j` by (cases "i = j", auto)
  assume "i \<le> k"
  with main have main: "k < j \<Longrightarrow> A $$ (k, k) = ?ev \<and> A $$ (k, Suc k) = 1" by blast
  thus "k < j \<Longrightarrow> A $$ (k, Suc k) = 1" by blast
  from main show "k \<le> j \<Longrightarrow> A $$ (k,k) = ?ev" by (cases "k = j", auto)
qed
    
lemmas identify_block_le = identify_block(1)

lemma identify_block_le_rev: "(ev,j) = identify_block A i \<Longrightarrow> j \<le> i"
  using identify_block_le[of A i ev j] by auto
  
termination identify_blocks_main by (relation "measure (\<lambda> (_,_,i,list). i)", auto dest: identify_block_le_rev)
termination jnf_vector_main by (relation "measure (\<lambda> (i,A). i)", auto dest: identify_block_le_rev)

lemma identify_blocks_main: assumes "(i_start,i_end) \<in> set (identify_blocks_main ev A i list)" 
  and "\<And> i_s i_e. (i_s, i_e) \<in> set list \<Longrightarrow> i_s \<le> i_e \<and> i_e < k"
  and "i \<le> k"
  shows "i_start \<le> i_end \<and> i_end < k" using assms
proof (induct ev A i list rule: identify_blocks_main.induct)
  case (2 ev A i_e list)
  obtain ev' i_b where id: "identify_block A i_e = (ev', i_b)" by force
  note IH = 2(1)[OF id[symmetric] refl]
  let ?res = "identify_blocks_main ev A (Suc i_e) list"  
  let ?rec = "identify_blocks_main ev A i_b ((i_b, i_e) # list)"
  show ?case
  proof (cases "ev' = ev")
    case False
    hence res: "?res = list" using id by simp
    from 2 show ?thesis unfolding res by auto
  next
    case True
    hence res: "?res = ?rec" using id by simp
    from 2(2)[unfolded res] have "(i_start, i_end) \<in> set ?rec" .
    note IH = IH[OF True this]
    from 2(3-) have iek: "i_e < k" by simp
    from identify_block_le[OF id] have ibe: "i_b \<le> i_e" .
    from ibe iek have "i_b \<le> k" by simp
    note IH = IH[OF _ this]
    show ?thesis
      by (rule IH, insert ibe iek 2(3-), auto)
  qed
qed simp

lemma identify_blocks: assumes "(i_start,i_end) \<in> set (identify_blocks B k)" 
  shows "i_start \<le> i_end \<and> i_end < k"
  using identify_blocks_main[OF assms[unfolded identify_blocks_def]] by auto

subsection \<open>Proving Similarity\<close>

context
begin
private lemma swap_cols_rows_block_similar: assumes "A \<in> carrier\<^sub>m n n"
  and "j < n" and "i \<le> j"
  shows "mat_similar (swap_cols_rows_block i j A) A"
  using assms
proof (induct i j A rule: swap_cols_rows_block.induct)
  case (1 i j A)
  hence A: "A \<in> carrier\<^sub>m n n"
    and jn: "j < n" and ij: "i \<le> j" by auto
  note [simp] = swap_cols_rows_block.simps[of i j]
  show ?case
  proof (cases "i < j")
    case False
    thus ?thesis using mat_similar_refl[OF A] by simp
  next
    case True note ij = this
    let ?B = "swap_cols_rows i j A"
    let ?C = "swap_cols_rows_block (Suc i) j ?B"
    from swap_cols_rows_similar[OF A _ jn, of i] ij jn
    have BA: "mat_similar ?B A" by auto
    have CB: "mat_similar ?C ?B"
      by (rule 1(1)[OF ij _ jn], insert ij A, auto)
    from mat_similar_trans[OF CB BA] show ?thesis using ij by simp
  qed
qed

private lemma step_1_main_similar: "i \<le> j \<Longrightarrow> A \<in> carrier\<^sub>m n n \<Longrightarrow> mat_similar (step_1_main n i j A) A"
proof (induct i j A taking: n rule: step_1_main.induct)
  case (1 i j A)
  note [simp] = step_1_main.simps[of n i j A]
  from 1(3-) have ij: "i \<le> j" and A: "A \<in> carrier\<^sub>m n n" by auto
  show ?case
  proof (cases "j \<ge> n")
    case True
    thus ?thesis using mat_similar_refl[OF A] by simp
  next
    case False 
    hence jn: "j < n" by simp
    note IH = 1(1-2)[OF False]
    show ?thesis
    proof (cases "i = 0")
      case True
      from IH(1)[OF this _ A]
      show ?thesis using jn by (simp, simp add: True)
    next
      case False
      let ?evi = "A $$ (i - 1, i - 1)"
      let ?evj = "A $$ (j,j)"
      let ?B = "if ?evi \<noteq> ?evj \<and> A $$ (i - 1, j) \<noteq> 0 then 
        add_col_sub_row (A $$ (i - 1, j) / (?evj - ?evi)) (i - 1) j A else A"
      obtain B where B: "B = ?B" by auto
      have Bn: "B \<in> carrier\<^sub>m n n" unfolding B using A by simp
      from False ij jn have *: "i - 1 < n" "j < n" "i - 1 \<noteq> j" by auto
      have BA: "mat_similar B A" unfolding B using mat_similar_refl[OF A]
        add_col_sub_row_similar[OF A *] by auto
      from ij have "i - 1 \<le> j" by simp
      note IH = IH(2)[OF False refl refl refl refl B this Bn]
      from False jn have id: "step_1_main n i j A = step_1_main n (i - 1) j B"
        unfolding B by (simp add: Let_def)
      show ?thesis unfolding id
        by (rule mat_similar_trans[OF IH BA])
    qed
  qed
qed

private lemma step_2_main_similar: "A \<in> carrier\<^sub>m n n \<Longrightarrow> mat_similar (step_2_main n j A) A"
proof (induct j A taking: n rule: step_2_main.induct)
  case (1 j A)
  note [simp] = step_2_main.simps[of n j A]
  from 1(2) have A: "A \<in> carrier\<^sub>m n n" .
  show ?case
  proof (cases "j \<ge> n")
    case True
    thus ?thesis using mat_similar_refl[OF A] by simp
  next
    case False 
    hence jn: "j < n" by simp
    note IH = 1(1)[OF False]
    let ?look = "lookup_ev (A $$ (j,j)) j A"
    let ?B = "case ?look of 
          None \<Rightarrow> A
        | Some i \<Rightarrow> swap_cols_rows_block (Suc i) j A"
    obtain B where B: "B = ?B" by auto
    have id: "step_2_main n j A = step_2_main n (Suc j) B" unfolding B using False by simp
    have Bn: "B \<in> carrier\<^sub>m n n" unfolding B using A by (auto split: option.splits)
    have BA: "mat_similar B A" 
    proof (cases ?look)
      case None
      thus ?thesis unfolding B using mat_similar_refl[OF A] by simp
    next
      case (Some i)
      from lookup_ev_Some[OF this]
      show ?thesis unfolding B Some
        by (auto intro: swap_cols_rows_block_similar[OF A jn])
    qed
    show ?thesis unfolding id
      by (rule mat_similar_trans[OF IH[OF refl B Bn] BA])
  qed
qed

private lemma step_3_a_similar: "A \<in> carrier\<^sub>m n n \<Longrightarrow> i < j \<Longrightarrow> j < n \<Longrightarrow> mat_similar (step_3_a i j A) A"
proof (induct i j A rule: step_3_a.induct)
  case (1 j A)
  thus ?case by (simp add: mat_similar_refl)
next
  case (2 i j A)
  from 2(2-) have A: "A \<in> carrier\<^sub>m n n" and ij: "Suc i < j" and j: "j < n" by auto
  let ?B = "if A $$ (i,i) = A $$ (j,j) \<and> A $$ (i, i + 1) = 1 \<and> A $$ (i, j) \<noteq> 0 
    then add_col_sub_row (- A $$ (i, j)) (Suc i) j A else A"
  obtain B where B: "B = ?B" by auto
  from A have Bn: "B \<in> carrier\<^sub>m n n" unfolding B by simp
  note IH = 2(1)[OF refl B Bn _ j]
  have id: "step_3_a (Suc i) j A = step_3_a i j B" unfolding B by (simp add: Let_def)
  from ij j have *: "Suc i < n" "j < n" "Suc i \<noteq> j" by auto
  have BA: "mat_similar B A" unfolding B
    using mat_similar_refl[OF A] add_col_sub_row_similar[OF A *] by auto
  show ?case unfolding id
    by (rule mat_similar_trans[OF IH BA], insert ij, auto)
qed

private lemma step_3_c_inner_loop_similar: 
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> l \<noteq> i \<Longrightarrow> k - 1 \<le> l \<Longrightarrow> k - 1 \<le> i \<Longrightarrow> l < n \<Longrightarrow> i < n \<Longrightarrow> 
  mat_similar (step_3_c_inner_loop val l i k A) A"
proof (induct val l i k A rule: step_3_c_inner_loop.induct)
  case (1 val l i A)
  thus ?case using mat_similar_refl[of A] by simp
next
  case (2 val l i k A)
  let ?res = "step_3_c_inner_loop val l i (Suc k) A"
  from 2(2-) have A: "A \<in> carrier\<^sub>m n n" and 
    *: "l \<noteq> i" "k \<le> l" "k \<le> i" "l < n" "i < n" by auto
  let ?B = "add_col_sub_row val i l A"
  have BA: "mat_similar ?B A"
    by (rule add_col_sub_row_similar[OF A], insert *, auto)
  have B: "?B \<in> carrier\<^sub>m n n" using A unfolding mat_carrier_def by simp
  show ?case
  proof (cases k)
    case 0
    hence id: "?res = ?B" by simp
    thus ?thesis using BA by simp
  next
    case (Suc kk)
    with * have "l - 1 \<noteq> i - 1" "k - 1 \<le> l - 1" "k - 1 \<le> i - 1" "l - 1 < n" "i - 1 < n" by auto
    note IH = 2(1)[OF B this]
    show ?thesis unfolding step_3_c_inner_loop.simps
      by (rule mat_similar_trans[OF IH BA])
  qed
qed

private lemma step_3_c_similar: 
  "A \<in> carrier\<^sub>m n n \<Longrightarrow> l < k \<Longrightarrow> k < n 
  \<Longrightarrow> (\<And> i_begin i_end. (i_begin, i_end) \<in> set blocks \<Longrightarrow>  i_end \<le> k \<and> i_end - i_begin \<le> l)
  \<Longrightarrow> mat_similar (step_3_c x l k blocks A) A"
proof (induct x l k blocks A rule: step_3_c.induct)
  case (1 x l k A)
  thus ?case using mat_similar_refl[OF 1(1)] by simp
next
  case (2 x l k i_begin i_end blocks A)
  let ?res = "step_3_c x l k ((i_begin,i_end) # blocks) A"
  from 2(2-4) have A: "A \<in> carrier\<^sub>m n n" and lki: "l < k" "k < n" by auto
  from 2(5) have i: "i_end \<le> k" "i_end - i_begin \<le> l" by auto
  let ?y = "A $$ (i_end,k)"
  let ?inner = "step_3_c_inner_loop (?y / x) l i_end (Suc i_end - i_begin) A"
  obtain B where B: 
    "B = (if i_end = l then A else ?inner)" by auto    
  hence id: "?res = step_3_c x l k blocks B"
    by simp
  have BA: "mat_similar B A" 
  proof (cases "i_end = l")
    case True
    thus ?thesis unfolding B using mat_similar_refl[OF A] by simp
  next
    case False
    hence B: "B = ?inner" and li: "l \<noteq> i_end" by (auto simp: B)      
    show ?thesis unfolding B 
      by (rule step_3_c_inner_loop_similar[OF A li], insert lki i, auto)
  qed
  have Bn: "B \<in> carrier\<^sub>m n n" using A unfolding B mat_carrier_def by simp
  note IH = 2(1)[OF B Bn lki(1-2) 2(5)]
  show ?case unfolding id
    by (rule mat_similar_trans[OF IH BA], auto)
qed

private lemma step_3_main_similar: "A \<in> carrier\<^sub>m n n \<Longrightarrow> k > 0 \<Longrightarrow> mat_similar (step_3_main n k A) A"
proof (induct k A taking: n rule: step_3_main.induct)
  case (1 k A)
  from 1(2-) have A: "A \<in> carrier\<^sub>m n n" and k: "k > 0" by auto
  note [simp] = step_3_main.simps[of n k A]
  show ?case
  proof (cases "k \<ge> n")
    case True
    thus ?thesis using mat_similar_refl[OF A] by simp
  next
    case False
    hence kn: "k < n" by simp
    obtain B where B: "B = step_3_a (k - 1) k A" by auto
    note IH = 1(1)[OF False B]
    from A have Bn: "B \<in> carrier\<^sub>m n n" unfolding B mat_carrier_def by simp
    from k have "k - 1 < k" by simp
    from step_3_a_similar[OF A this kn] have BA: "mat_similar B A" unfolding B .
    obtain all_blocks where ab: "all_blocks = identify_blocks B k" by simp
    obtain blocks where blocks: "blocks = filter (\<lambda> block. B $$ (snd block, k) \<noteq> 0) all_blocks" by simp
    obtain F where F: "F = (if blocks = [] then B
       else let (l_begin,l) = find_largest_block (hd blocks) (tl blocks); x = B $$ (l, k); C = step_3_c x l k blocks B;
            D = mult_col_div_row (inverse x) k C; E = swap_cols_rows_block (Suc l) k D
        in E)" by simp
    note IH = IH[OF ab blocks F]
    have Fn: "F \<in> carrier\<^sub>m n n" unfolding F Let_def mat_carrier_def using Bn 
      by (simp split: prod.splits)
    have FB: "mat_similar F B" 
    proof (cases "blocks = []")
      case True
      thus ?thesis unfolding F using mat_similar_refl[OF Bn] by simp
    next
      case False
      obtain l_start l where l: "find_largest_block (hd blocks) (tl blocks) = (l_start, l)" by force
      obtain x where x: "x = B $$ (l,k)" by simp
      obtain C where C: "C = step_3_c x l k blocks B" by simp
      obtain D where D: "D = mult_col_div_row (inverse x) k C" by auto
      obtain E where E: "E = swap_cols_rows_block (Suc l) k D" by auto
      from find_largest_block[OF False l] have lb: "(l_start,l) \<in> set blocks"
        and llarge: "\<And> i_begin i_end. (i_begin,i_end) \<in> set blocks \<Longrightarrow> l - l_start \<ge> i_end - i_begin" by auto
      from lb have x0: "x \<noteq> 0" unfolding blocks x by simp
      {
        fix i_start i_end
        assume "(i_start,i_end) \<in> set blocks"
        hence "(i_start,i_end) \<in> set (identify_blocks B k)" unfolding blocks ab by simp
        from identify_blocks[OF this]
        have "i_end < k" by simp
      } note block_bound = this
      from block_bound[OF lb]
      have lk: "l < k" .
      from False have F: "F = E" unfolding E D C x F l Let_def by simp
      from Bn have Cn: "C \<in> carrier\<^sub>m n n" unfolding C mat_carrier_def by simp
      have CB: "mat_similar C B" unfolding C
      proof (rule step_3_c_similar[OF Bn lk kn])
        fix i_begin i_end
        assume i: "(i_begin, i_end) \<in> set blocks"
        from llarge[OF i] block_bound[OF i] 
        show "i_end \<le> k \<and> i_end - i_begin \<le> l" by auto
      qed
      from x0 have "inverse x \<noteq> 0" by simp
      from mult_col_div_row_similar[OF Cn kn this] 
      have DC: "mat_similar D C" unfolding D .
      from Cn have Dn: "D \<in> carrier\<^sub>m n n" unfolding D mat_carrier_def by simp
      from lk have "Suc l \<le> k" by auto
      from swap_cols_rows_block_similar[OF Dn kn this] 
      have ED: "mat_similar E D" unfolding E .
      from mat_similar_trans[OF ED mat_similar_trans[OF DC 
        mat_similar_trans[OF CB mat_similar_refl[OF Bn]]]]
      show ?thesis unfolding F .
    qed
    have "0 < Suc k" by simp
    note IH = IH[OF Fn this]
    have id: "step_3_main n k A = step_3_main n (Suc k) F" using kn 
      by (simp add: F Let_def blocks ab B)
    show ?thesis unfolding id
      by (rule mat_similar_trans[OF IH mat_similar_trans[OF FB BA]])
  qed
qed

private lemma step_1_similar: "A \<in> carrier\<^sub>m n n \<Longrightarrow> mat_similar (step_1 A) A"
  unfolding step_1_def by (rule step_1_main_similar, auto)

private lemma step_2_similar: "A \<in> carrier\<^sub>m n n \<Longrightarrow> mat_similar (step_2 A) A"
  unfolding step_2_def by (rule step_2_main_similar, auto)

private lemma step_3_similar: "A \<in> carrier\<^sub>m n n \<Longrightarrow> mat_similar (step_3 A) A"
  unfolding step_3_def by (rule step_3_main_similar, auto)

lemma triangular_to_jnf_similar: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "mat_similar (triangular_to_jnf A) A"
  unfolding triangular_to_jnf_def o_def
proof (rule mat_similar_trans[OF step_3_similar 
  mat_similar_trans[OF step_2_similar
  mat_similar_trans[OF step_1_similar[OF A]
  mat_similar_refl[OF A]]]])
  show "step_1 A \<in> carrier\<^sub>m n n" using A unfolding mat_carrier_def by simp
  show "step_2 (step_1 A) \<in> carrier\<^sub>m n n" using A unfolding mat_carrier_def by simp
qed

end


subsection \<open>Invariants for Proving that Result is in JNF\<close>
context 
  fixes n :: nat
  and ty :: "'a :: field itself"
begin

(* upper triangular, ensured by precondition and then maintained *)
private definition uppert :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "uppert A i j \<equiv> j < i \<longrightarrow> A $$ (i,j) = 0" 

(* zeros at places where EVs differ, ensured by step 1 and then maintained *)
private definition diff_ev :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "diff_ev A i j \<equiv> i < j \<longrightarrow> A $$ (i,i) \<noteq> A $$ (j,j) \<longrightarrow> A $$ (i,j) = 0"

(* same EVs are grouped together, ensured by step 2 and then maintained *)
private definition ev_blocks_part :: "nat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "ev_blocks_part m A \<equiv> \<forall> i j k. i < j \<longrightarrow> j < k \<longrightarrow> k < m \<longrightarrow> A $$ (k,k) = A $$ (i,i) \<longrightarrow> A $$ (j,j) = A $$ (i,i)"

private definition ev_blocks :: "'a mat \<Rightarrow> bool" where
  "ev_blocks \<equiv> ev_blocks_part n"

text \<open>In step 3, there is a separation at which iteration we are.
  The columns left of $k$ will be in JNF, the columns right of $k$ or equal to $k$ will satisfy @{const uppert}, @{const diff_ev}, 
  and @{const ev_blocks}, and the column at $k$ will have one of the following properties, which are ensured in the
  different phases of step 3.\<close>

(* Left of a one is a zero: In a row of shape 0 ... 0 ev 1 0 ... 0 entry, the entry will be 0,
   ensured by step 3 a and then maintained *)
private definition one_zero :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "one_zero A i j \<equiv> 
    (Suc i < j \<longrightarrow> A $$ (i,Suc i) = 1 \<longrightarrow> A $$ (i,j) = 0) \<and> 
    (j < i \<longrightarrow> A $$ (i,j) = 0) \<and>
    (i < j \<longrightarrow> A $$ (i,i) \<noteq> A $$ (j,j) \<longrightarrow> A $$ (i,j) = 0)"

(* There is exactly one row   0 ... 0 ev 0 ... 0 entry with entry != 0 and that entry is x,
   ensured by step 3 c and then maintained *)
private definition single_non_zero :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "single_non_zero \<equiv> \<lambda> l k x. (\<lambda> A i j. (i \<notin> {k,l} \<longrightarrow> A $$ (i,k) = 0) \<and> A $$ (l,k) = x)"

(* There is at exactly one row   0 ... 0 ev 0 ... 0 entry with entry != 0 and that entry is 1,
   ensured by step 3 d and then maintained *)
private definition single_one :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "single_one \<equiv> \<lambda> l k. (\<lambda> A i j. (i \<notin> {k,l} \<longrightarrow> A $$ (i,k) = 0) \<and> A $$ (l,k) = 1)"

(* there is at most one row   0 ... 0 ev 0 ... 0 entry with entry != 0 and that entry is 1 and there
   are no zeros between ev and the entry, ensured by step 3 e *)
private definition lower_one :: "nat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lower_one k A i j = (j = k \<longrightarrow> 
    (A $$ (i,j) = 0 \<or> i = j \<or> (A $$ (i,j) = 1 \<and> j = Suc i \<and> A $$ (i,i) = A $$ (j,j))))"

(* the desired property: we have a jordan block matrix *)
qualified definition jb :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "jb A i j \<equiv> (Suc i = j \<longrightarrow> A $$ (i,j) \<in> {0,1}) 
  \<and> (i \<noteq> j \<longrightarrow> (Suc i \<noteq> j \<or> A $$ (i,i) \<noteq> A $$ (j,j)) \<longrightarrow> A $$ (i,j) = 0)"

text \<open>The following properties are useful to easily ensure the above invariants 
  just from invariants of other matrices. The properties are essential in showing
  that the blocks identified in step 3b are the same as one would identify for
  the matrices in the upcoming steps 3c and 3d.\<close>
 
private definition same_diag :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "same_diag A B \<equiv> \<forall> i < n. A $$ (i,i) = B $$ (i,i)"

private definition same_upto :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "same_upto j A B \<equiv> \<forall> i' j'. i' < n \<longrightarrow> j' < j \<longrightarrow> A $$ (i',j') = B $$ (i',j')"

text \<open>Definitions stating where the properties hold\<close>

private definition inv_all :: "('a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "inv_all p A \<equiv> \<forall> i j. i < n \<longrightarrow> j < n \<longrightarrow> p A i j"

private definition inv_part :: "('a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "inv_part p A m_i m_j \<equiv> \<forall> i j. i < n \<longrightarrow> j < n \<longrightarrow> j < m_j \<or> j = m_j \<and> i \<ge> m_i \<longrightarrow> p A i j"

private definition inv_upto :: "('a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> bool" where
  "inv_upto p A m \<equiv> \<forall> i j. i < n \<longrightarrow> j < n \<longrightarrow> j < m \<longrightarrow> p A i j"

private definition inv_from :: "('a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> bool" where
  "inv_from p A m \<equiv> \<forall> i j. i < n \<longrightarrow> j < n \<longrightarrow> j > m \<longrightarrow> p A i j"

private definition inv_at :: "('a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> bool" where
  "inv_at p A m \<equiv> \<forall> i. i < n \<longrightarrow> p A i m"

private definition inv_from_bot :: "('a mat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> bool" where
  "inv_from_bot p A mi \<equiv> \<forall> i. i \<ge> mi \<longrightarrow> i < n \<longrightarrow> p A i"

text \<open>Auxiliary Lemmas on Handling, Comparing, and Accessing Invariants\<close>

private lemma jb_imp_uppert: "jb A i j \<Longrightarrow> uppert A i j"
  unfolding jb_def uppert_def by auto

private lemma ev_blocks_partD:
  "ev_blocks_part m A \<Longrightarrow> i < j \<Longrightarrow> j < k \<Longrightarrow> k < m \<Longrightarrow> A $$ (k,k) = A $$ (i,i) \<Longrightarrow> A $$ (j,j) = A $$ (i,i)"
  unfolding ev_blocks_part_def by auto

private lemma ev_blocks_partI:
  assumes "\<And> i j k. i < j \<Longrightarrow> j < k \<Longrightarrow> k < m \<Longrightarrow> A $$ (k,k) = A $$ (i,i) \<Longrightarrow> A $$ (j,j) = A $$ (i,i)"
  shows "ev_blocks_part m A"
  using assms unfolding ev_blocks_part_def by blast

private lemma ev_blocksD:
  "ev_blocks A \<Longrightarrow> i < j \<Longrightarrow> j < k \<Longrightarrow> k < n \<Longrightarrow> A $$ (k,k) = A $$ (i,i) \<Longrightarrow> A $$ (j,j) = A $$ (i,i)"
  unfolding ev_blocks_def by (rule ev_blocks_partD)

private lemma ev_blocks_leD:
  assumes "ev_blocks A"
  "i \<le> j" "j \<le> k" "k < n" "A $$ (k,k) = A $$ (i,i)" 
  shows "A $$ (j,j) = A $$ (i,i)"
proof -  
  show ?thesis
  proof (cases "i = j \<or> j = k")
    case False
    with assms(2-3) have "i < j" "j < k" by auto
    from ev_blocksD[OF assms(1) this assms(4-)] show ?thesis .
  next
    case True
    thus ?thesis using assms(5) by auto
  qed
qed

lemma inv_allD: "inv_all p A \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow> p A i j"
  unfolding inv_all_def by auto

private lemma inv_allI: assumes "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> p A i j"
  shows "inv_all p A" 
  using assms unfolding inv_all_def by blast

private lemma inv_partI: assumes "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> j < m_j \<or> j = m_j \<and> i \<ge> m_i \<Longrightarrow> p A i j"
  shows "inv_part p A m_i m_j"
  using assms unfolding inv_part_def by auto

private lemma inv_partD: assumes "inv_part p A m_i m_j" "i < n" "j < n" 
  shows "j < m_j \<Longrightarrow> p A i j"
  and "j = m_j \<Longrightarrow> i \<ge> m_i \<Longrightarrow> p A i j"
  and "j < m_j \<or> j = m_j \<and> i \<ge> m_i \<Longrightarrow> p A i j"
  using assms unfolding inv_part_def by auto

private lemma inv_uptoI: assumes "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> j < m \<Longrightarrow> p A i j"
  shows "inv_upto p A m"
  using assms unfolding inv_upto_def by auto

private lemma inv_uptoD: assumes "inv_upto p A m" "i < n" "j < n" "j < m"
  shows "p A i j"
  using assms unfolding inv_upto_def by auto

private lemma inv_upto_Suc: assumes "inv_upto p A m"
  and "\<And> i. i < n \<Longrightarrow> p A i m"
  shows "inv_upto p A (Suc m)"
proof (intro inv_uptoI)
  fix i j
  assume "i < n" "j < n" "j < Suc m"
  thus "p A i j" using inv_uptoD[OF assms(1), of i j] assms(2)[of i] by (cases "j = m", auto)
qed

private lemma inv_upto_mono: assumes "\<And> i j. i < n \<Longrightarrow> j < k \<Longrightarrow> p A i j \<Longrightarrow> q A i j"
  shows "inv_upto p A k \<Longrightarrow> inv_upto q A k"
  using assms unfolding inv_upto_def by auto

private lemma inv_fromI: assumes "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> j > m \<Longrightarrow> p A i j"
  shows "inv_from p A m"
  using assms unfolding inv_from_def by auto

private lemma inv_fromD: assumes "inv_from p A m" "i < n" "j < n" "j > m"
  shows "p A i j"
  using assms unfolding inv_from_def by auto

private lemma inv_atI[intro]: assumes "\<And> i. i < n \<Longrightarrow> p A i m"
  shows "inv_at p A m"
  using assms unfolding inv_at_def by auto

private lemma inv_atD: assumes "inv_at p A m" "i < n"
  shows "p A i m"
  using assms unfolding inv_at_def by auto
  
private lemma inv_all_imp_inv_part: "m i \<le> n \<Longrightarrow> m_j \<le> n \<Longrightarrow> inv_all p A \<Longrightarrow> inv_part p A m_i m_j"
  unfolding inv_all_def inv_part_def by auto

private lemma inv_all_eq_inv_part: "inv_all p A = inv_part p A n n"
  unfolding inv_all_def inv_part_def by auto

private lemma inv_part_0_Suc: "m_j < n \<Longrightarrow> inv_part p A 0 m_j = inv_part p A n (Suc m_j)"
  unfolding inv_part_def by (auto, case_tac "j = m_j", auto)

private lemma inv_all_uppertD: "inv_all uppert A \<Longrightarrow> j < i \<Longrightarrow> i < n \<Longrightarrow> A $$ (i,j) = 0"
  unfolding inv_all_def uppert_def by auto

private lemma inv_all_diff_evD: "inv_all diff_ev A \<Longrightarrow> i < j \<Longrightarrow> j < n 
  \<Longrightarrow> A $$ (i, i) \<noteq> A $$ (j, j) \<Longrightarrow> A $$ (i,j) = 0"
  unfolding inv_all_def diff_ev_def by auto

private lemma inv_all_diff_ev_uppertD: assumes "inv_all diff_ev A"
  "inv_all uppert A"
  "i < n" "j < n"
  and neg: "A $$ (i, i) \<noteq> A $$ (j, j)"
  shows "A $$ (i,j) = 0"
proof -
  from neg have "i \<noteq> j" by auto
  hence "i < j \<or> j < i" by arith
  thus ?thesis
  proof 
    assume "i < j"
    from inv_all_diff_evD[OF assms(1) this `j < n` neg] show ?thesis .
  next
    assume "j < i"
    from inv_all_uppertD[OF assms(2) this `i < n`] show ?thesis .
  qed
qed

private lemma inv_from_bot_step: "p A i \<Longrightarrow> inv_from_bot p A (Suc i) \<Longrightarrow> inv_from_bot p A i"
  unfolding inv_from_bot_def by (auto, case_tac "ia = i", auto)

private lemma same_diag_refl[simp]: "same_diag A A" unfolding same_diag_def by auto
private lemma same_diag_trans: "same_diag A B \<Longrightarrow> same_diag B C \<Longrightarrow> same_diag A C" 
  unfolding same_diag_def by auto

private lemma same_diag_ev_blocks: "same_diag A B \<Longrightarrow> ev_blocks A \<Longrightarrow> ev_blocks B"
  unfolding same_diag_def ev_blocks_def ev_blocks_part_def by auto

private lemma same_uptoI[intro]: assumes "\<And> i' j'. i' < n \<Longrightarrow> j' < j \<Longrightarrow> A $$ (i',j') = B $$ (i',j')"
  shows "same_upto j A B"
  using assms unfolding same_upto_def by blast

private lemma same_uptoD[dest]: assumes "same_upto j A B" "i' < n" "j' < j" 
  shows "A $$ (i',j') = B $$ (i',j')"
  using assms unfolding same_upto_def by blast

private lemma same_upto_refl[simp]: "same_upto j A A" unfolding same_upto_def by auto

private lemma same_upto_trans: "same_upto j A B \<Longrightarrow> same_upto j B C \<Longrightarrow> same_upto j A C" 
  unfolding same_upto_def by auto

private lemma same_upto_inv_upto_jb: "same_upto j A B \<Longrightarrow> inv_upto jb A j \<Longrightarrow> inv_upto jb B j"
  unfolding inv_upto_def same_upto_def jb_def by auto

private lemma jb_imp_diff_ev: "jb A i j \<Longrightarrow> diff_ev A i j"
  unfolding jb_def diff_ev_def by auto

private lemma ev_blocks_diag: 
  "same_diag A B \<Longrightarrow> ev_blocks B \<Longrightarrow> ev_blocks A"
  using assms unfolding ev_blocks_def ev_blocks_part_def same_diag_def by auto

private lemma inv_all_imp_inv_from: "inv_all p A \<Longrightarrow> inv_from p A k"
  unfolding inv_all_def inv_from_def by auto

private lemma inv_all_imp_inv_at: "inv_all p A \<Longrightarrow> k < n \<Longrightarrow> inv_at p A k"
  unfolding inv_all_def inv_at_def by auto

private lemma inv_from_upto_at_all: 
  assumes "inv_upto jb A k" "inv_from diff_ev A k" "inv_from uppert A k" "inv_at p A k"
  and "\<And> i. i < n \<Longrightarrow> p A i k \<Longrightarrow> diff_ev A i k \<and> uppert A i k"
  shows "inv_all diff_ev A" "inv_all uppert A"
proof -
  {
    fix i j
    assume ij: "i < n" "j < n"
    have "diff_ev A i j \<and> uppert A i j"
    proof (cases "j < k")
      case True
      with assms(1) ij have "jb A i j" unfolding inv_upto_def by auto
      thus ?thesis using ij unfolding jb_def diff_ev_def uppert_def by auto
    next
      case False note ge = this
      show ?thesis
      proof (cases "j = k")
        case True
        with assms(4-) ij show ?thesis unfolding inv_at_def by auto
      next
        case False
        with ge have "j > k" by auto
        with assms(2-3) ij show ?thesis unfolding inv_from_def by auto
      qed
    qed
  }
  thus "inv_all diff_ev A" "inv_all uppert A" unfolding inv_all_def by auto
qed

private lemma lower_one_diff_uppert:
  "i < n \<Longrightarrow> lower_one k B i k \<Longrightarrow> diff_ev B i k \<and> uppert B i k"
   unfolding lower_one_def diff_ev_def uppert_def by auto


subsection \<open>Alternative Characterization of @{const identify_blocks} in Presence of @{const ev_blocks}\<close>

private lemma identify_blocks_main_iff: assumes *: "ev_blocks A" "k \<le> k'" "A $$ (k',k') = ev" 
  "k' \<noteq> k \<longrightarrow> k > 0 \<longrightarrow> A $$ (k - 1, k - 1) = ev \<longrightarrow> A $$ (k - 1, k) \<noteq> 1" and "k' < n"
  shows "set (identify_blocks_main ev A k list) = 
  set list \<union> {(i,j) | i j. A $$ (i,i) = ev \<and> A $$ (j,j) = ev \<and> i \<le> j \<and> j < k \<and> (\<forall> l. i \<le> l \<longrightarrow> l < j \<longrightarrow> A $$ (l, Suc l) = 1)
  \<and> (Suc j \<noteq> k' \<longrightarrow> A $$ (j, Suc j) \<noteq> 1) \<and> (i > 0 \<longrightarrow> A $$ (i - 1, i - 1) \<noteq> ev \<or> A $$ (i - 1, i) \<noteq> 1)}" (is "_ = _ \<union> ?ss ev A k")
  using *
proof (induct ev A k list rule: identify_blocks_main.induct)
  case 1
  show ?case unfolding identify_blocks_main.simps by auto
next
  case (2 ev A i_e list)
  let ?s = "?ss ev A"
  obtain ev' i_b where id: "identify_block A i_e = (ev', i_b)" by force
  note IH = 2(1)[OF id[symmetric] refl _ 2(2)]
  note blocks = ev_blocks_leD[OF 2(2) _ _ `k' < n`, unfolded 2(4)]
  let ?res = "identify_blocks_main ev A (Suc i_e) list"  
  let ?rec = "identify_blocks_main ev A i_b ((i_b, i_e) # list)"
  note idb = identify_block[OF id]
  have Aie: "A $$ (i_e, i_e) = ev'" using idb by blast
  show ?case
  proof (cases "ev' = ev")
    case False
    hence res: "?res = list" using id by simp
    have "?s (Suc i_e) = {}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain j where "j < Suc i_e" and ev: "A $$ (j,j) = ev" by auto
      with 2 have "j \<le> i_e" "i_e \<le> k'" by auto
      from blocks[OF this] ev have "ev = A $$ (i_e,i_e)" by auto
      thus False using Aie False by simp
    qed    
    thus ?thesis unfolding res by auto
  next
    case True
    hence res: "?res = ?rec" using id by simp
    from True idb have Aie: "A $$ (i_e, i_e) = ev" by blast
    from True idb have Aib: "A $$ (i_b, i_b) = ev" by blast
    note IH = IH[OF True]
    from 2(3-) have iek: "i_e < k'" by simp
    from identify_block_le[OF id] have ibe: "i_b \<le> i_e" .
    from ibe iek have "i_b \<le> k'" by simp
    have "k' \<noteq> i_b \<longrightarrow> 0 < i_b \<longrightarrow> A $$ (i_b - 1, i_b - 1) = ev \<longrightarrow> A $$ (i_b - 1, i_b) \<noteq> 1" 
      using idb(4) Aie by auto
    note IH = IH[OF `i_b \<le> k'` `A $$ (k',k') = ev` this]
    have cong: "\<And> a b c d. insert a c = d \<Longrightarrow> set (a # b) \<union> c = set b \<union> d" by auto
    show ?thesis unfolding res IH
    proof (rule cong)
      from ibe have "?s i_b \<subseteq> ?s (Suc i_e)" by auto
      moreover 
      have inter: "\<And>l. i_b \<le> l \<Longrightarrow> l < i_e \<Longrightarrow> A $$ (l, Suc l) = 1" using idb by blast
      have last: "Suc i_e \<noteq> k' \<Longrightarrow> A $$ (i_e, Suc i_e) \<noteq> 1" using 2(5) Aie by auto
      have "(i_b, i_e) \<in> ?s (Suc i_e)" using ibe idb(4) Aie
        by (auto simp: Aie Aib inter last)
      ultimately have "insert (i_b, i_e) (?s i_b) \<subseteq> ?s (Suc i_e)" by auto
      moreover  
      {
        fix i j
        assume ij: "(i,j) \<in> ?s (Suc i_e)"
        hence "(i,j) \<in> insert (i_b, i_e) (?s i_b)"
        proof (cases "j < i_b")
          case True
          with ij show ?thesis by blast
        next
          case False
          with ij have "i_b \<le> j" "j \<le> i_e" "A $$ (i,i) = ev" by auto
          {
            assume j: "j < i_e"
            from idb(5)[OF `i_b \<le> j` this] have 1: "A $$ (j, Suc j) = 1" .
            from j `Suc i_e \<le> k'` have "Suc j \<noteq> k'" by auto
            with ij 1 have False by auto
          }
          with `j \<le> i_e` have j: "j = i_e" by (cases "j = i_e", auto)
          {
            assume i: "i < i_b \<or> i > i_b"
            hence False
            proof
              assume "i < i_b"
              hence "i_b > 0" by auto
              with idb(4) Aie have *: "A $$ (i_b - 1, i_b - 1) \<noteq> ev \<or> A $$ (i_b - 1, i_b) \<noteq> 1" by auto
              from `i < i_b` `i_b \<le> i_e` `i_e < k'` have "i \<le> i_b - 1" "i_b - 1 \<le> k'" by auto
              from blocks[OF this] * `A $$ (i,i) = ev` have *: "A $$ (i_b - 1, i_b) \<noteq> 1" by auto
              from `i < i_b` `i_b \<le> i_e` j have **: "i \<le> i_b - 1" "i_b - 1 < j" "Suc (i_b - 1) = i_b" by auto
              from ij have "\<And> l. l\<ge>i \<Longrightarrow> l < j \<Longrightarrow> A $$ (l, Suc l) = 1" by auto
              from this[OF **(1-2)] **(3) * show False by auto
            next
              assume "i > i_b"
              with ij j have "A $$ (i - 1, i - 1) \<noteq> ev \<or> A $$ (i - 1, i) \<noteq> 1" and 
                *: "i - 1 \<ge> i_b" "i - 1 \<le> i_e" "i - 1 < i_e" "Suc (i - 1) = i" by auto
              with idb(6)[OF this(2-3)] Aie have "A $$ (i - 1, i) \<noteq> 1" by auto
              with idb(5)[OF `i - 1 \<ge> i_b` `i - 1 < i_e`] * 
              show False by auto
            qed
          }
          hence i: "i = i_b" by arith
          show ?thesis unfolding i j by simp
        qed
      }
      hence "?s (Suc i_e) \<subseteq> insert (i_b, i_e) (?s i_b)" by blast
      ultimately 
      show "insert (i_b, i_e) (?s i_b) = ?s (Suc i_e)" by blast
    qed
  qed
qed
  

private lemma identify_blocks_iff: assumes "ev_blocks A" "k < n"
  shows "set (identify_blocks A k) = 
  {(i,j) | i j. A $$ (i,i) = A $$ (k,k) \<and> A $$ (j,j) = A $$ (k,k) \<and> i \<le> j \<and> j < k \<and> (\<forall> l. i \<le> l \<longrightarrow> l < j \<longrightarrow> A $$ (l, Suc l) = 1)
  \<and> (Suc j \<noteq> k \<longrightarrow> A $$ (j, Suc j) \<noteq> 1) \<and> (i > 0 \<longrightarrow> A $$ (i - 1, i - 1) \<noteq> A $$ (k,k) \<or> A $$ (i - 1, i) \<noteq> 1)}" 
  unfolding identify_blocks_def using identify_blocks_main_iff[OF assms(1) le_refl refl _ `k < n`] by auto

private lemma identify_blocksD: assumes "ev_blocks A" "k < n" and "(i,j) \<in> set (identify_blocks A k)"
  shows "A $$ (i,i) = A $$ (k,k)" "A $$ (j,j) = A $$ (k,k)" "i \<le> j" "j < k" 
  "\<And> l. i \<le> l \<Longrightarrow> l < j \<Longrightarrow> A $$ (l, Suc l) = 1"
  "Suc j \<noteq> k \<Longrightarrow> A $$ (j, Suc j) \<noteq> 1"
  "i > 0 \<Longrightarrow> A $$ (i - 1, i - 1) \<noteq> A $$ (k,k) \<or> A $$ (i - 1, i) \<noteq> 1" 
  using assms unfolding identify_blocks_iff[OF assms(1-2)] by auto

private lemma identify_blocksI: assumes inv: "ev_blocks A" "k < n" and *: "A $$ (i,i) = A $$ (k,k)" "A $$ (j,j) = A $$ (k,k)"
  "i \<le> j" "j < k" "\<And> l. i \<le> l \<Longrightarrow> l < j \<Longrightarrow> A $$ (l, Suc l) = 1"
  "Suc j \<noteq> k \<Longrightarrow> A $$ (j, Suc j) \<noteq> 1" "i > 0 \<Longrightarrow> A $$ (i - 1, i - 1) \<noteq> A $$ (k,k) \<or> A $$ (i - 1, i) \<noteq> 1"
  shows "(i,j) \<in> set (identify_blocks A k)"
  unfolding identify_blocks_iff[OF inv] using assms by blast

private lemma identify_blocks_rev: assumes "A $$ (i, Suc i) = 0 \<and> Suc i < k \<or> Suc i = k"
  and ev: "A $$ (i, i) = A $$ (k, k)"
  and inv: "ev_blocks A" "k < n"
  shows "(snd (identify_block A i), i) \<in> set (identify_blocks A k)"
proof -
  obtain ev j where id: "identify_block A i = (ev,j)" by force
  note idb = identify_block[OF this]
  show ?thesis unfolding id snd_conv
    by (rule identify_blocksI[OF inv], insert idb assms, auto)
qed


subsection \<open>Proving the Invariants\<close>

private lemma add_col_sub_row_diag: assumes A: "A \<in> carrier\<^sub>m n n"
  and ut: "inv_all uppert A"
  and ijk: "i < j" "j < n" "k < n"
  shows "add_col_sub_row a i j A $$ (k,k) = A $$ (k,k)"
proof -
  from inv_all_uppertD[OF ut]
  show ?thesis
    by (subst add_col_sub_row_index, insert A ijk, auto)
qed

private lemma add_col_sub_row_diff_ev_part_old: assumes A: "A \<in> carrier\<^sub>m n n"
  and ij: "i \<le> j" "i \<noteq> 0" "i < n" "j < n" "i' < n" "j' < n"
  and choice: "j' < j \<or> j' = j \<and> i' \<ge> i"
  and old: "inv_part diff_ev A i j"
  and ut: "inv_all uppert A"
  shows "diff_ev (add_col_sub_row a (i - 1) j A) i' j'"
  unfolding diff_ev_def
proof (intro impI)
  assume ij': "i' < j'"
  let ?A = "add_col_sub_row a (i - 1) j A"
  assume neq: "?A $$ (i',i') \<noteq> ?A $$ (j',j')"
  from A have dim: "dim\<^sub>r A = n" "dim\<^sub>c A = n" by auto
  note utd = inv_all_uppertD[OF ut]
  let ?i = "i - 1"
  have "?i < j" using `i \<le> j` `i \<noteq> 0` `i < n` by auto
  from utd[OF this `j < n`] have Aji: "A $$ (j,?i) = 0" by simp
  from add_col_sub_row_diag[OF A ut `?i < j` `j < n`]
  have diag: "\<And> k. k < n \<Longrightarrow> ?A $$ (k,k) = A $$ (k,k)" .
  from neq[unfolded diag[OF `i' < n`] diag[OF `j' < n`]] 
  have neq: "A $$ (i',i') \<noteq> A $$ (j',j')" by auto
  {
    from inv_partD(3)[OF old `i' < n` `j' < n` choice]
    have "diff_ev A i' j'" by auto
    with neq ij' have "A $$ (i',j') = 0" unfolding diff_ev_def by auto
  } note zero = this
  {
    assume "i' \<noteq> ?i" "j' = j"
    with ij' ij(1) choice have "i' > ?i" by auto
    from utd[OF this] ij
    have "A $$ (i', ?i) = 0" by auto
  } note 1 = this
  {
    assume "j' \<noteq> j" "i' = ?i"
    with ij' ij(1) choice have "j > j'" by auto
    from utd[OF this] ij
    have "A $$ (j, j') = 0" by auto
  } note 2 = this
  from ij' ij choice have "(i' = ?i \<and> j' = j) = False" by arith
  note id = add_col_sub_row_index[of i' A j' j a ?i, unfolded dim this if_False, 
    OF `i' < n` `i' < n` `j' < n` `j' < n` `j < n`]
  show "?A $$ (i',j') = 0" unfolding id zero using 1 2 by auto
qed

private lemma add_col_sub_row_uppert: assumes "A \<in> carrier\<^sub>m n n"
  and "i < j"
  and "j < n"
  and inv: "inv_all uppert (A :: 'a mat)"
  shows "inv_all uppert (add_col_sub_row a i j A)"
  unfolding inv_all_def uppert_def
proof (intro allI impI)
  fix i' j'
  assume *: "i' < n" "j' < n" "j' < i'"
  note inv = inv_allD[OF inv, unfolded uppert_def]
  show "add_col_sub_row a i j A $$ (i', j') = 0"
    by (subst add_col_sub_row_index, insert assms * inv, auto)
qed

private lemma step_1_main_inv: "i \<le> j 
  \<Longrightarrow> A \<in> carrier\<^sub>m n n 
  \<Longrightarrow> inv_all uppert A 
  \<Longrightarrow> inv_part diff_ev A i j 
  \<Longrightarrow> inv_all uppert (step_1_main n i j A) \<and> inv_all diff_ev (step_1_main n i j A)"
proof (induct i j A taking: n rule: step_1_main.induct)
  case (1 i j A)
  let ?i = "i - 1"
  note [simp] = step_1_main.simps[of n i j A]
  from 1(3-) have ij: "i \<le> j" and A: "A \<in> carrier\<^sub>m n n" and inv: "inv_all uppert A" 
    "inv_part diff_ev A i j" by auto
  show ?case
  proof (cases "j \<ge> n")
    case True
    thus ?thesis using inv by (simp add: inv_all_eq_inv_part, auto simp: inv_part_def)
  next
    case False 
    hence jn: "j < n" by simp
    note IH = 1(1-2)[OF False]
    show ?thesis
    proof (cases "i = 0")
      case True
      from inv[unfolded True inv_part_0_Suc[OF jn]]
      have inv2: "inv_part diff_ev A n (j + 1)" by simp
      have "inv_part diff_ev A (j + 1) (j + 1)" 
      proof (intro inv_partI)
        fix i' j'
        assume ij: "i' < n" "j' < n" and choice: "j' < j + 1 \<or> j' = j + 1 \<and> j + 1 \<le> i'"
        from inv_partD[OF inv2 ij] choice
        show "diff_ev A i' j'" using jn unfolding diff_ev_def by auto
      qed
      from IH(1)[OF True _ A inv(1) this]
      show ?thesis using jn by (simp, simp add: True)
    next
      case False 
      let ?evi = "A $$ (?i,?i)"
      let ?evj = "A $$ (j,j)"
      let ?choice = "?evi \<noteq> ?evj \<and> A $$ (?i, j) \<noteq> 0"
      let ?A = "add_col_sub_row (A $$ (?i, j) / (?evj - ?evi)) ?i j A"
      let ?B = "if ?choice then ?A else A"
      obtain B where B: "B = ?B" by auto
      have Bn: "B \<in> carrier\<^sub>m n n" unfolding B using A by simp
      from False ij jn have *: "?i < j" "j < n" "?i < n" by auto
      have inv1: "inv_all uppert B" unfolding B using inv add_col_sub_row_uppert[OF A *(1-2) inv(1)]
        by auto
      note inv2 = inv_partD[OF inv(2)]
      have inv2: "inv_part diff_ev B ?i j"
      proof (cases ?choice)
        case False
        hence B: "B = A" unfolding B by auto
        show ?thesis unfolding B
        proof (rule inv_partI)
          fix i' j'
          assume ij: "i' < n" "j' < n" and "j' < j \<or> j' = j \<and> ?i \<le> i'"
          hence choice: "(j' < j \<or> j' = j \<and> i \<le> i') \<or> j' = j \<and> i' = ?i" by auto
          note inv2 = inv2[OF ij]
          from choice
          show "diff_ev A i' j'"
          proof
            assume "j' < j \<or> j' = j \<and> i \<le> i'"
            from inv2(3)[OF this] show ?thesis .
          next
            assume "j' = j \<and> i' = ?i"
            thus ?thesis using False unfolding diff_ev_def by auto
          qed
        qed
      next
        case True
        hence B: "B = ?A" unfolding B by auto
        from * True have "i < n" by auto
        note old = add_col_sub_row_diff_ev_part_old[OF A `i \<le> j` `i \<noteq> 0` `i < n` `j < n` 
          _ _ _ inv(2) inv(1)]
        show ?thesis unfolding B
        proof (rule inv_partI)
          fix i' j'
          assume ij: "i' < n" "j' < n" and "j' < j \<or> j' = j \<and> ?i \<le> i'"
          hence choice: "(j' < j \<or> j' = j \<and> i \<le> i') \<or> j' = j \<and> i' = ?i" by auto
          note inv2 = inv2[OF ij]
          from choice
          show "diff_ev ?A i' j'"
          proof
            assume "j' < j \<or> j' = j \<and> i \<le> i'"
            from old[OF ij this] show ?thesis .
          next
            assume "j' = j \<and> i' = ?i"
            hence ij': "j' = j" "i' = ?i" by auto
            note diag = add_col_sub_row_diag[OF A inv(1) `?i < j` `j < n`]
            show ?thesis unfolding ij' diff_ev_def diag[OF `j < n`] diag[OF `?i < n`]
            proof (intro impI)
              from True have neq: "?evi \<noteq> ?evj" by simp
              note ut = inv_all_uppertD[OF inv(1)]
              obtain i' where i': "i' = i - Suc 0" by auto
              obtain diff where diff: "diff = ?evj - A $$ (i',i')" by auto
              from neq have [simp]: "diff \<noteq> 0" unfolding diff i' by auto
              from ut[OF `?i < j` `j < n`] have [simp]: "A $$ (j,i') = 0" unfolding diff i' by simp
              have "?A $$ (?i, j) = 
                A $$ (i', j) + (A $$ (i', j) * A $$ (i', i') -
                A $$ (i', j) * A $$ (j, j)) / diff"
                by (subst add_col_sub_row_index, insert A *, auto simp: diff[symmetric] i'[symmetric] field_simps)
              also have "A $$ (i', j) * A $$ (i', i') - A $$ (i', j) * A $$ (j, j)
                = - A $$ (i',j) * diff" by (simp add: diff i' field_simps)
              also have "\<dots> / diff = - A $$ (i',j)" by simp
              finally show "?A $$ (?i,j) = 0" by simp
            qed
          qed
        qed
      qed
      from ij have "i - 1 \<le> j" by simp
      note IH = IH(2)[OF False refl refl refl refl B this Bn inv1 inv2]
      from False jn have id: "step_1_main n i j A = step_1_main n (i - 1) j B"
        unfolding B by (simp add: Let_def)
      show ?thesis unfolding id by (rule IH)
    qed
  qed
qed

private lemma step_2_main_inv: "A \<in> carrier\<^sub>m n n 
  \<Longrightarrow> inv_all uppert A 
  \<Longrightarrow> inv_all diff_ev A 
  \<Longrightarrow> ev_blocks_part j A 
  \<Longrightarrow> inv_all uppert (step_2_main n j A) \<and> inv_all diff_ev (step_2_main n j A) 
    \<and> ev_blocks (step_2_main n j A)"
proof (induct j A taking: n rule: step_2_main.induct)
  case (1 j A)
  note [simp] = step_2_main.simps[of n j A]
  from 1(2-) have A: "A \<in> carrier\<^sub>m n n" 
    and inv: "inv_all uppert A" "inv_all diff_ev A" "ev_blocks_part j A" by auto
  show ?case
  proof (cases "j \<ge> n")
    case True
    with inv(3) have "ev_blocks A" unfolding ev_blocks_def ev_blocks_part_def by auto
    thus ?thesis using True inv(1-2) by auto
  next
    case False 
    hence jn: "j < n" by simp
    note intro = ev_blocks_partI
    note dest = ev_blocks_partD
    note IH = 1(1)[OF False]
    let ?look = "lookup_ev (A $$ (j,j)) j A"
    let ?B = "case ?look of 
          None \<Rightarrow> A
        | Some i \<Rightarrow> swap_cols_rows_block (Suc i) j A"
    obtain B where B: "B = ?B" by auto
    have id: "step_2_main n j A = step_2_main n (Suc j) B" unfolding B using False by simp
    have Bn: "B \<in> carrier\<^sub>m n n" unfolding B using A by (auto split: option.splits)
    have "inv_all uppert B \<and> inv_all diff_ev B \<and> ev_blocks_part (Suc j) B"
    proof (cases ?look)
      case None
      have "ev_blocks_part (Suc j) A"
      proof (intro intro)
        fix i' j' k'
        assume *: "i' < j'" "j' < k'" "k' < Suc j" "A $$ (k',k') = A $$ (i',i')"
        show "A $$ (j',j') = A $$ (i',i')"
        proof (cases "j = k'")
          case False
          with * have "k' < j" by auto
          from dest[OF inv(3) *(1-2) this *(4)]
          show ?thesis .
        next
          case True
          with lookup_ev_None[OF None, of i'] * have False by simp
          thus ?thesis ..
        qed
      qed
      with None show ?thesis unfolding B using inv by auto
    next
      case (Some i)
      from lookup_ev_Some[OF Some] 
      have ij: "i < j" and id: "A $$ (i, i) = A $$ (j, j)" 
        and neq: "\<And> k. i < k \<Longrightarrow> k < j \<Longrightarrow> A $$ (k,k) \<noteq> A $$ (j,j)" by auto
      let ?A = "swap_cols_rows_block (Suc i) j A"
      let ?perm = "\<lambda> i'. if i' = Suc i then j else if Suc i < i' \<and> i' \<le> j then i' - 1 else i'"
      from Some have B: "B = ?A" unfolding B by simp
      have Aind: "\<And> i' j'. i' < n \<Longrightarrow> j' < n \<Longrightarrow> ?A $$ (i', j') = A $$ (?perm i', ?perm j')"
        by (subst swap_cols_rows_block_index, insert False A ij, auto)
      have inv_ev: "ev_blocks_part (Suc j) ?A"
      proof (intro intro)
        fix i' j' k        
        assume *: "i' < j'" "j' < k" "k < Suc j" and ki: "?A $$ (k,k) = ?A $$ (i',i')" 
        from * jn have "j' < n" "i' < n" "k < n" by auto
        note id' = Aind[OF `j' < n` `j' < n`] Aind[OF `i' < n` `i' < n`] Aind[OF `k < n` `k < n`]
        note inv_ev = dest[OF inv(3)]
        show "?A $$ (j',j') = ?A $$ (i',i')"
        proof (cases "i' < Suc i")
          case True note i' = this
          hence pi: "?perm i' = i'" by simp
          show ?thesis
          proof (cases "j' < Suc i")
            case True note j' = this
            hence pj: "?perm j' = j'" by simp
            show ?thesis
            proof (cases "k < Suc i")
              case True note k = this
              hence pk: "?perm k = k" by simp
              from True ij have "k < j" by simp
              from inv_ev[OF *(1-2) this] ki
              show ?thesis unfolding id' pi pj pk by auto
            next
              case False note kf1 = this
              show ?thesis
              proof (cases "k = Suc i")
                case True note k = this
                hence pk: "?perm k = j" by simp
                from ki id have ii': "A $$ (i, i) = A $$ (i', i')" unfolding id' pi pj pk by simp
                have ji: "A $$ (j',j') = A $$ (i',i')"
                proof (cases "j' = i")
                  case True
                  with ii' show ?thesis by simp
                next
                  case False
                  with `j' < Suc i` have "j' < i" by auto
                  from ki id inv_ev[OF `i' < j'` this ij] show ?thesis
                    unfolding id' pi pj pk by simp
                qed
                thus ?thesis unfolding id' pi pj pk .
              next
                case False note kf2 = this
                with kf1 have k: "k > Suc i" by auto
                hence pk: "?perm k = k - 1" and kj: "k - 1 < j"
                  using * `k < Suc j` by auto
                from k j' have "j' < k - 1" by auto
                from inv_ev[OF *(1) this kj] ki
                show ?thesis unfolding id' pi pj pk by simp
              qed
            qed
          next
            case False note j'f1 = this
            show ?thesis
            proof (cases "j' = Suc i")
              case True note j' = this
              hence pj: "?perm j' = j" by simp
              from j' * have k: "k > Suc i" by auto
              hence pk: "?perm k = k - 1" and kj: "k - 1 < j"
                using * `k < Suc j` by auto
              from ki[unfolded id' pi pj pk] have eq: "A $$ (k - 1, k - 1) = A $$ (i', i')" .
              from * i' k have le: "i' \<le> i" and lt: "i < k - 1" "k - 1 < j" by auto
              from inv_ev[OF _ lt eq] le have "A $$ (i, i) = A $$ (i', i')" 
                by (cases "i = i'", auto)
              with id show ?thesis unfolding id' pi pj pk by simp
            next
              case False note j'f2 = this
              with j'f1 have "j' > Suc i" by auto
              hence pj: "?perm j' = j' - 1" and pk: "?perm k = k - 1"   
                and kj: "i' < j' - 1" "j' - 1 < k - 1" "k - 1 < j"
                using * i' `k < Suc j` by auto
              from inv_ev[OF kj] ki
              show ?thesis unfolding id' pi pj pk by simp
            qed
          qed
        next
          case False note i'f1 = this
          show ?thesis
          proof (cases "i' = Suc i")
            case True note i' = this
            with * have gt: "i < k - 1" "k - 1 < j" 
              and perm: "?perm i' = j" "?perm k = k - 1" by auto
            from ki[unfolded id' perm] neq[OF gt] have False by auto
            thus ?thesis ..
          next
            case False note i'f2 = this
            with i'f1 have "i' > Suc i" by auto
            with * have gt: "i' - 1 < j' - 1"  "j' - 1 < k - 1" "k - 1 < j"
              and perm: "?perm i' = i' - 1" "?perm j' = j' - 1" "?perm k = k - 1" by auto
            show ?thesis using inv_ev[OF gt] ki
              unfolding id' perm by simp
          qed
        qed
      qed
      let ?both = "\<lambda> A i j. uppert A i j \<and> diff_ev A i j"
      have "inv_all ?both ?A" 
      proof (intro inv_allI)
        fix ii jj
        assume ii: "ii < n" and jj: "jj < n"
        note id = Aind[OF ii ii] Aind[OF jj jj] Aind[OF ii jj]
        note ut = inv_all_uppertD[OF inv(1)]
        note diff = inv_all_diff_evD[OF inv(2)]
        have upper: "uppert ?A ii jj" unfolding uppert_def
        proof
          assume ji: "jj < ii"
          show "?A $$ (ii,jj) = 0" 
          proof (cases "ii < Suc i")
            case True note i = this
            with ji have perm: "?perm ii = ii" "?perm jj = jj" by auto
            show ?thesis unfolding id perm using ut[OF ji ii] .
          next
            case False note if1 = this
            show ?thesis
            proof (cases "ii = Suc i")
              case True note i = this
              with ji ij have perm: "?perm ii = j" "?perm jj = jj" and jj: "jj < j" by auto
              show ?thesis unfolding id perm 
                by (rule ut[OF jj jn])
            next
              case False 
              with if1 have if1: "ii > Suc i" by auto
              show ?thesis
              proof (cases "ii \<le> j")
                case True note i = this
                with if1 have pi: "?perm ii = ii - 1" by auto
                show ?thesis
                proof (cases "jj = Suc i")
                  case True note j = this
                  hence pj: "?perm jj = j" by simp
                  from i ji if1 ii j have ij: "ii - 1 < j" and ii: "i < ii - 1" by auto
                  show ?thesis unfolding id pi pj
                    by (rule diff[OF ij jn neq[OF ii ij]])
                next
                  case False
                  with i ji if1 ii have "?perm jj < ii - 1" "ii - 1 < n" by auto
                  from ut[OF this]
                  show ?thesis unfolding id pi .
                qed
              next
                case False 
                hence i: "ii > j" by auto
                with if1 have pi: "?perm ii = ii" by simp
                from i ji if1 ii have "?perm jj < ii" by auto
                from ut[OF this ii]
                show ?thesis unfolding id pi .
              qed
            qed
          qed
        qed
        have diff: "diff_ev ?A ii jj" unfolding diff_ev_def
        proof (intro impI)
          assume ij': "ii < jj" and neq: "?A $$ (ii,ii) \<noteq> ?A $$ (jj,jj)"
          show "?A $$ (ii,jj) = 0" 
          proof (cases "jj < Suc i")
            case True note j = this
            with ij' have perm: "?perm ii = ii" "?perm jj = jj" by auto
            show ?thesis using neq unfolding id perm using diff[OF ij' jj] by simp
          next
            case False note jf1 = this
            show ?thesis
            proof (cases "jj = Suc i")
              case True note j = this
              with ij' ij have perm: "?perm jj = j" "?perm ii = ii" and ii: "ii < j" by auto
              show ?thesis using neq unfolding id perm 
                by (intro diff[OF ii jn])
            next
              case False 
              with jf1 have jf1: "jj > Suc i" by auto
              show ?thesis
              proof (cases "jj \<le> j")
                case True note j = this
                with jf1 have pj: "?perm jj = jj - 1" by auto
                show ?thesis
                proof (cases "ii = Suc i")
                  case True note i = this
                  hence pi: "?perm ii = j" by simp
                  from i ij' jf1 jj j have ij: "jj - 1 < j" by auto
                  show ?thesis unfolding id pi pj
                    by (rule ut[OF ij jn])
                next
                  case False
                  with j ij' jf1 jj have "?perm ii < jj - 1" "jj - 1 < n" by auto
                  from diff[OF this] neq
                  show ?thesis unfolding id pj .
                qed
              next
                case False 
                hence j: "jj > j" by auto
                with jf1 have pj: "?perm jj = jj" by simp
                from j ij' jf1 jj have "?perm ii < jj" by auto
                from diff[OF this jj] neq
                show ?thesis unfolding id pj .
              qed
            qed
          qed
        qed
        from upper diff
        show "?both ?A ii jj" ..
      qed
      hence "inv_all diff_ev ?A" "inv_all uppert ?A"
        unfolding inv_all_def by blast+
      with inv_ev show ?thesis unfolding B by auto
    qed
    with IH[OF refl B Bn]
    show ?thesis unfolding id by auto
  qed
qed


private lemma add_col_sub_row_same_upto: assumes "i < j" "j < n" "A \<in> carrier\<^sub>m n n" "inv_upto uppert A j"
  shows "same_upto j A (add_col_sub_row v i j A)"
  by (intro same_uptoI, subst add_col_sub_row_index, insert assms, auto simp: uppert_def inv_upto_def)

private lemma add_col_sub_row_inv_from: assumes *: "inv_from uppert A j"
  "inv_from diff_ev A j" and diag: "same_diag A (add_col_sub_row v i j A)"
  and **: "A \<in> carrier\<^sub>m n n" "i < n" "i < j" "j < n" 
  and ev: "A $$ (i,i) = A $$ (j,j)"
  shows 
  "inv_from uppert (add_col_sub_row v i j A) j"
  "inv_from diff_ev (add_col_sub_row v i j A) j"
proof -
  note * = * **
  let ?A = "add_col_sub_row v i j A"
  let ?I = "\<lambda> A i j. uppert A i j \<and> diff_ev A i j"
  have "inv_from ?I ?A j" unfolding inv_from_def
  proof (intro allI impI)
    fix i' j'
    assume **: "i' < n" "j' < n" "j < j'"
    with diag have id: "(?A $$ (i',i') = ?A $$ (j',j')) = (A $$ (i',i') = A $$ (j',j'))"
      unfolding same_diag_def by auto
    from * ** have "i' < dim\<^sub>r A" "i' < dim\<^sub>c A" "j' < dim\<^sub>r A" "j' < dim\<^sub>c A" "j < dim\<^sub>r A" by auto
    note id2 = add_col_sub_row_index[OF this]
    show "?I ?A i' j'" unfolding uppert_def diff_ev_def id
    proof (intro conjI impI)
      assume "j' < i'"
      with inv_fromD[OF `inv_from uppert A j`, unfolded uppert_def, of i' j'] * ** 
      show "?A $$ (i',j') = 0" unfolding id2 using * ** `j' < i'` by simp
    next
      assume ***: "i' < j'" "A $$ (i', i') \<noteq> A $$ (j', j')"
      note diff_ev = inv_fromD[OF `inv_from diff_ev A j`, unfolded diff_ev_def]
      from diff_ev[of i' j'] *** * **
      have 0: "A $$ (i',j') = 0" by auto
      {
        assume "i = i'"
        with *** ev have "A $$ (j,j) \<noteq> A $$ (j',j')" by simp
        with diff_ev[of j j'] ** * have "A $$ (j,j') = 0" by simp
      }
      thus "?A $$ (i',j') = 0" unfolding id2 0 using * ** by auto
    qed
  qed
  thus 
  "inv_from uppert (add_col_sub_row v i j A) j"
  "inv_from diff_ev (add_col_sub_row v i j A) j"
    unfolding inv_from_def by blast+
qed
  
private lemma step_3_a_inv: "A \<in> carrier\<^sub>m n n 
  \<Longrightarrow> i < j \<Longrightarrow> j < n 
  \<Longrightarrow> inv_upto jb A j 
  \<Longrightarrow> inv_from uppert A j 
  \<Longrightarrow> inv_from diff_ev A j
  \<Longrightarrow> inv_at diff_ev A j
  \<Longrightarrow> inv_from_bot (\<lambda> A i. one_zero A i j) A i 
  \<Longrightarrow> ev_blocks A
  \<Longrightarrow> inv_from uppert (step_3_a i j A) j \<and> inv_from diff_ev (step_3_a i j A) j
    \<and> inv_upto jb (step_3_a i j A) j 
    \<and> inv_at one_zero (step_3_a i j A) j \<and> ev_blocks (step_3_a i j A)"
proof (induct i j A rule: step_3_a.induct)
  case (1 j A)
  thus ?case by (simp add: inv_from_bot_def inv_at_def)
next
  case (2 i j A)
  from 2(2-) have A: "A \<in> carrier\<^sub>m n n" and ij: "Suc i < j" "i < j" and j: "j < n" by auto
  let ?cond = "A $$ (i,i) = A $$ (j,j) \<and> A $$ (i, i + 1) = 1 \<and> A $$ (i, j) \<noteq> 0"
  let ?B = "add_col_sub_row (- A $$ (i, j)) (Suc i) j A"
  obtain B where B: "B = (if ?cond then ?B else A)" by auto
  from A have Bn: "B \<in> carrier\<^sub>m n n" unfolding B by simp
  note IH = 2(1)[OF refl B Bn ij(2) j]
  have id: "step_3_a (Suc i) j A = step_3_a i j B" unfolding B by (simp add: Let_def)
  from ij j have *: "Suc i < n" "j < n" "Suc i \<noteq> j" by auto
  from 2(2-) have inv: "inv_upto jb A j" "inv_from uppert A j" "inv_from diff_ev A j"
    "inv_from_bot (\<lambda>A i. one_zero A i j) A (Suc i)" "ev_blocks A" "inv_at diff_ev A j" by auto
  show ?case
  proof (cases ?cond)
    case False
    hence B: "B = A" unfolding B by auto
    have inv2: "inv_from_bot (\<lambda>A i. one_zero A i j) A i"
      by (rule inv_from_bot_step[OF _ inv(4)],
      insert False ij inv_atD[OF inv(6), of i] *, auto simp: one_zero_def diff_ev_def)
    show ?thesis unfolding id B
      by (rule IH[unfolded B], insert inv inv2, auto)
  next
    case True
    hence B: "B = ?B" unfolding B by auto
    from True have ev1: "A $$ (j,j) = A $$ (i,i)" by auto
    with ev_blocksD[OF inv(5) _ _ _ this, of "Suc i"]
    have ev: "A $$ (Suc i, Suc i) = A $$ (j,j)" using * ij by auto
    let ?C = "step_3_a i j B"
    from inv_uptoD[OF inv(1) j *(1) ij(1), unfolded jb_def] ij 
    have Aji: "A $$ (j, Suc i) = 0" by auto
    have diag: "same_diag A B" unfolding same_diag_def
      by (intro allI impI, insert ij j A Aji B, auto)
    have upto: "same_upto j A B" unfolding B
      by (rule add_col_sub_row_same_upto[OF `Suc i < j` `j < n` A inv_upto_mono[OF jb_imp_uppert inv(1)]])
    from add_col_sub_row_inv_from[OF inv(2-3) diag[unfolded B] A `Suc i < n` `Suc i < j` `j < n` ev, folded B]
    have from_j: "inv_from uppert B j" "inv_from diff_ev B j" by blast+
    show ?thesis unfolding id 
    proof (rule IH[OF same_upto_inv_upto_jb[OF upto inv(1)]
      from_j _ _ 
      same_diag_ev_blocks[OF diag inv(5)]])
      {
        fix k
        assume "k < n"
        with A * have k: "k < dim\<^sub>r A" "k < dim\<^sub>c A" "j < dim\<^sub>r A" "j < dim\<^sub>c A" "j < dim\<^sub>r A" by auto
        note id = B add_col_sub_row_index[OF k]
        have "B $$ (k,j) = (if k = i then 0 else A $$ (k,j))" unfolding id
          using inv_uptoD[OF inv(1), of k "Suc i", unfolded jb_def]
          by (insert * Aji True ij `k < n`, auto simp: ev)
      } note id = this
      show "inv_at diff_ev B j" 
      proof (intro inv_atI, unfold diff_ev_def, intro impI)
        fix k 
        assume **: "k < n" "k < j" "B $$ (k,k) \<noteq> B $$ (j,j)"
        with diag * have "A $$ (k,k) \<noteq> A $$ (j,j)" by (auto simp: same_diag_def)
        with inv_atD[OF inv(6) `k < n`, unfolded diff_ev_def] ** have Akj: "A $$ (k,j) = 0" by auto
        show "B $$ (k,j) = 0" unfolding id[OF `k < n`] Akj by simp
      qed
      show "inv_from_bot (\<lambda>A i. one_zero A i j) B i" unfolding inv_from_bot_def
      proof (intro allI impI)
        fix k
        assume "i \<le> k" "k < n"
        thus "one_zero B k j" using inv(4)[unfolded inv_from_bot_def]
          upto[unfolded same_upto_def] inv_atD[OF `inv_at diff_ev B j` `k < n`, unfolded diff_ev_def]
          unfolding one_zero_def id[OF `k < n`] by auto
      qed
    qed
  qed
qed

private lemma identify_block_main_cong: assumes sd: "same_diag A B" and su: "same_upto k A B" and kn: "k < n"
  shows "i < k \<Longrightarrow> identify_block_main ev A i = identify_block_main ev B i"
proof (induct i)
  case (Suc i)
  hence "i < k" by auto
  note IH = Suc(1)[OF this]
  let ?c = "\<lambda> A. A $$ (i,i) = ev \<and> A $$ (i,Suc i) = 1"
  from same_uptoD[OF su, of i "Suc i"] kn Suc(2) have 1: "A $$ (i, Suc i) = B $$ (i, Suc i)" by auto
  from sd kn Suc(2) have 2: "A $$ (i,i) = B $$ (i,i)" by (auto simp: same_diag_def)
  from 1 2 have id: "?c A = ?c B" by simp
  show ?case
  proof (cases "?c A")
    case True
    with True[unfolded id] IH show ?thesis by simp
  next
    case False
    with False[unfolded id] show ?thesis by auto
  qed
qed simp

private lemma identify_block_cong: assumes sd: "same_diag A B" and "same_upto k A B"
    "k < n" "l < k" 
  shows "identify_block A l = identify_block B l"
  unfolding identify_block_def Let_def
    identify_block_main_cong[OF assms]
  using assms(1,3,4) by (auto simp: same_diag_def)

private lemma identify_blocks_main_cong: assumes "ev2 = ev" and sd: "same_diag A B"
  shows "k < n \<Longrightarrow> same_upto k A B \<Longrightarrow> identify_blocks_main ev A k xs = identify_blocks_main ev2 B k xs"
  unfolding assms
proof (induct k arbitrary: xs rule: less_induct)
  case (less k list)
  show ?case
  proof (cases "k = 0")
    case False
    then obtain i_e where k: "k = Suc i_e" by (cases k, auto)
    obtain ev' i_b where idA: "identify_block A i_e = (ev', i_b)" by force
    from identify_block_le[OF idA] have ibe: "i_b \<le> i_e" .
    have idB: "identify_block B i_e = (ev', i_b)" unfolding idA[symmetric]
      by (rule sym, rule identify_block_cong[OF sd], insert k less(2-3), auto)
    let ?I = "identify_blocks_main ev"
    let ?resA = "?I A (Suc i_e) list"  
    let ?recA = "?I A i_b ((i_b, i_e) # list)"
    let ?resB = "?I B (Suc i_e) list"  
    let ?recB = "?I B i_b ((i_b, i_e) # list)"
    show ?thesis
    proof (cases "ev' = ev")
      case False
      hence res: "?resA = ?resB" using idA idB by simp
      thus ?thesis unfolding k by simp
    next
      case True
      hence res: "?resA = ?recA" "?resB = ?recB" using idA idB by auto
      from k ibe have ibk: "i_b < k" by simp
      with less(3) have "same_upto i_b A B" unfolding same_upto_def by auto
      from less(1)[OF ibk _ this] ibk `k < n` have "?recA = ?recB" by auto
      thus ?thesis unfolding k res by simp
    qed
  qed simp
qed

private lemma identify_blocks_cong: 
  "k < n \<Longrightarrow> same_diag A B \<Longrightarrow> same_upto k A B \<Longrightarrow> identify_blocks A k = identify_blocks B k"
  unfolding identify_blocks_def
  by (intro identify_blocks_main_cong, auto simp: same_diag_def)

text \<open>For step 3c, during the inner loop, the invariants are NOT preserved. 
  However, at the end of the inner loop, the invariants are again preserved.
  Therefore, for the inner loop we prove how the resulting matrix looks like in
  each iteration.\<close>
 
private lemma step_3_c_inner_result: assumes inv:
  "inv_upto jb A k"
  "inv_from uppert A k"
  "inv_from diff_ev A k"
  "inv_at one_zero A k"
  "ev_blocks A"
  and k: "k < n"
  and A: "A \<in> carrier\<^sub>m n n"
  and lbl: "(lb,l) \<in> set (identify_blocks A k)"
  and ib_block: "(i_begin,i_end) \<in> set (identify_blocks A k)"
  and il: "i_end \<noteq> l"
  and large: "l - lb \<ge> i_end - i_begin"
  and Alk: "A $$ (l,k) \<noteq> 0"
  shows "step_3_c_inner_loop (A $$ (i_end, k) / A $$ (l,k)) l i_end (Suc i_end - i_begin) A =
    mat n n
     (\<lambda>(i, j). if (i, j) = (i_end, k) then 0
               else if i_begin \<le> i \<and> i \<le> i_end \<and> k < j then A $$ (i, j) - A $$ (i_end, k) / A $$ (l,k) * A $$ (l + i - i_end, j)
                    else A $$ (i, j))" (is "?L = ?R")
proof -
  let ?Alk = "A $$ (l,k)"
  let ?Aik = "A $$ (i_end,k)"
  def quot \<equiv> "?Aik / ?Alk"
  let ?idiff = "i_end - i_begin"
  let ?m = "\<lambda> iter diff i j. if (i,j) = (i_end,k) then if diff = (Suc ?idiff) then ?Aik else 0
    else if i \<ge> i_begin + diff \<and> i \<le> i_end \<and> k < j then A $$ (i, j) - quot * A $$ (l + i - i_end, j)
    else if (i,j) = (i_end - iter, Suc l - iter) \<and> iter \<notin> {0, Suc ?idiff} then quot 
    else A $$ (i,j)"
  let ?mm = "\<lambda> iter diff i j. if (i,j) = (i_end,k) then 0
    else if i \<ge> i_begin + diff \<and> i \<le> i_end \<and> k < j then A $$ (i, j) - quot * A $$ (l + i - i_end, j)
    else if (i,j) = (i_end - Suc iter, l - iter) \<and> iter \<noteq> ?idiff then quot 
    else A $$ (i,j)"
  let ?mat = "\<lambda> iter diff. mat n n (\<lambda> (i,j). ?m iter diff i j)"
  from identify_blocks[OF ib_block] have ib: "i_begin \<le> i_end" "i_end < k" by auto
  from identify_blocks[OF lbl] have lb: "lb \<le> l" "l < k" by auto
  have mend: "?mat 0 (Suc ?idiff) = A"
    by (rule mat_eqI, insert A ib, auto)
  {
    fix ll ii diff iter 
    assume "diff \<noteq> 0 \<Longrightarrow> ii + iter = i_end" "diff \<noteq> 0 \<Longrightarrow> ll + iter = l" "diff + iter = Suc ?idiff"
    hence "step_3_c_inner_loop quot ll ii diff (?mat iter diff) = ?R"
    proof (induct diff arbitrary: ii ll iter)
      case 0
      hence iter: "iter = Suc ?idiff" by auto
      have "step_3_c_inner_loop quot ll ii 0 (?mat iter 0) = ?mat (Suc ?idiff) 0" 
        unfolding iter step_3_c_inner_loop.simps ..
      also have "\<dots> = ?R"
        by (rule mat_eqI, insert ib, auto simp: quot_def)
      finally show ?case .
    next
      case (Suc diff ii ll)
      note prems = Suc(2-)
      let ?B = "?mat iter (Suc diff)"
      have "step_3_c_inner_loop quot ll ii (Suc diff) ?B
      = step_3_c_inner_loop quot (ll - 1) (ii - 1) diff (add_col_sub_row quot ii ll ?B)"
        by simp
      also have "add_col_sub_row quot ii ll ?B
        = ?mat (Suc iter) diff" (is "?C = ?D") 
      proof (rule mat_eqI, unfold mat_dim_row_mat mat_dim_col_mat)
        fix i j
        assume i: "i < n" and j: "j < n"
        have ll: "ll < n" using prems lb k by auto
        from prems ib k have ii: "ii \<ge> i_begin" "ii < n" "ii < k" "ii \<le> i_end"
          and eqs: "ii + iter = i_end" "ll + iter = l" "Suc diff + iter = Suc ?idiff" by auto
        from eqs have diff: "diff < Suc ?idiff" by auto
        from eqs lb `k < n` have "ll < k" "l < n" by auto
        note index = ib lb k i j ll il large ii this
        let ?Aij = "A $$ (i,j)"
        have D: "?D $$ (i,j) = ?mm iter diff i j" using diff i j by (auto split: if_splits)
        def B \<equiv> ?B
        have BB: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> B $$ (i,j) = ?m iter (Suc diff) i j" unfolding B_def by auto
        have B: "B $$ (i,j) = ?m iter (Suc diff) i j" by (rule BB[OF i j])
        have C: "?C $$ (i, j) =  
         (if i = ii \<and> j = ll then B $$ (i, j) + quot * B $$ (i, i) - quot * quot * B $$ (j, i) - quot * B $$ (j, j)
          else if i = ii \<and> j \<noteq> ll then B $$ (i, j) - quot * B $$ (ll, j) 
          else if i \<noteq> ii \<and> j = ll then B $$ (i, j) + quot * B $$ (i, ii) 
          else B $$ (i, j))" unfolding B_def
          by (rule add_col_sub_row_index(1), insert i j ll, auto)

        from inv_from_upto_at_all[OF inv(1,3,2,4)] have invA: "inv_all diff_ev A" "inv_all uppert A"
          unfolding one_zero_def diff_ev_def uppert_def by auto
        note ut = inv_all_uppertD[OF invA(2)]
        note de = inv_all_diff_evD[OF invA(1)]
        note jb = inv_uptoD[OF inv(1), unfolded jb_def]
        note oz = inv_atD[OF inv(4), unfolded one_zero_def]
        note iblock = identify_blocksD[OF inv(5) `k < n`]
        note ibe = iblock[OF ib_block]
        let ?ev = "\<lambda> i. A $$ (i,i)"

        {
          fix i ib ie
          assume "(ib,ie) \<in> set (identify_blocks A k)" and i: "ib \<le> i" "i < ie"
          note ibe = iblock[OF this(1)]
          from ibe(5)[OF i] have id: "A $$ (i, Suc i) = 1" by auto
          from i ibe `k < n` have "i < n" "Suc i < k" by auto
          with oz[OF this(1)] id
          have "A $$ (i,k) = 0" by auto
        } note A_ik = this

        {
          fix i 
          assume i: "i < n" and "\<not> (i \<ge> i_begin \<and> i \<le> i_end)"
          hence choice: "i > i_end \<or> i < i_begin" by auto
          note index = index i 
          from index eqs choice have "i \<noteq> ii" by auto
          {
            assume 0: "A $$ (i,ii) \<noteq> 0"
            from 0 ut[of ii, OF _ i] `i \<noteq> ii` have "i < ii" by force
            from choice index eqs this have "i < i_begin" by auto
            with index have "i < k" by auto
            from jb[OF i `ii < n` `ii < k`] 0 `i \<noteq> ii` 
            have *: "Suc i = ii" "A $$ (i,ii) = 1" "?ev i = ?ev ii" by auto
            with index `i < i_begin` have "ii = i_begin" by auto
            with ibe(1,7) * have False by auto
          }
          hence Aii: "A $$ (i,ii) = 0" by auto
          {
            fix j assume j: "j < n"
            have B: "B $$ (i,j) = ?m iter (Suc diff) i j" using i j unfolding B_def by simp
            from choice have id: "((i, j) = (i_end - iter, Suc l - iter) \<and> iter \<notin> {0, Suc ?idiff}) = False" 
              using ib index eqs by auto
            have "B $$ (i,j) = A $$ (i,j)" unfolding B id using choice ib index by auto
          }
          note Aii this
        }                     
        hence A_outside_ii: "\<And> i. i < n \<Longrightarrow> \<not> (i_begin \<le> i \<and> i \<le> i_end) \<Longrightarrow> A $$ (i, ii) = 0" 
        and B_outside: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> \<not> (i_begin \<le> i \<and> i \<le> i_end) \<Longrightarrow> B $$ (i, j) = A $$ (i, j)" by auto

        from diff eqs have iter: "iter \<noteq> Suc ?idiff" by auto
        {
          fix ib ie jb je
          assume i: "(ib,ie) \<in> set (identify_blocks A k)" and 
            j: "(jb,je) \<in> set (identify_blocks A k)" and lt: "ie < je"
          note i = iblock[OF i]
          note j = iblock[OF j]
          from i j lt have "Suc ie < k" by auto
          with i have Aie: "A $$ (ie, Suc ie) \<noteq> 1" by auto
          have "ie < jb" 
          proof (rule ccontr)
            assume "\<not> ie < jb"
            hence "ie \<ge> jb" by auto
            from j(5)[OF this lt] Aie show False by auto
          qed
        } note block_bounds = this
        {
          assume "i_end < l"
          from block_bounds[OF ib_block lbl this]
          have "i_end < lb" .
        } note i_less_l = this 
        {
          assume "l < i_end"
          from block_bounds[OF lbl ib_block this]
          have "l < i_begin" .
        } note l_less_i = this
        {
          assume "i_end - iter = Suc l - iter"
          with iter large eqs have "i_end = Suc l" by auto
          with l_less_i have "l < i_begin" by auto
          with index `i_end = Suc l` have "i_begin = i_end" by auto
        } note block = this
        have Alie: "A $$ (l, i_end) = 0" 
        proof (cases "l < i_end")
          case True
          {
            assume nz: "A $$ (l, i_end) \<noteq> 0"
            from l_less_i[OF True] index have "0 < i_begin" "l < i_begin" "i_end < n" "i_end < k" by auto
            from jb[OF `l < n` this(3-4)] il nz
            have "i_end = Suc l" "A $$ (l, Suc l) = 1" by auto
            with iblock[OF lbl] have "k = Suc l" by auto
            with `i_end = Suc l` `i_end < k` have False by auto
          }           
          thus ?thesis by auto
        next
          case False
          with il have "i_end < l" by auto
          from ut[OF this `l < n`] show ?thesis .
        qed          
        show "?C $$ (i,j) = ?D $$ (i,j)" 
        proof (cases "i \<ge> i_begin \<and> i \<le> i_end")
          case False
          hence choice: "i > i_end \<or> i < i_begin" by auto
          from choice have id: "((i, j) = (i_end - Suc iter, l - iter) \<and> iter \<noteq> ?idiff) = False" 
            using ib index eqs by auto
          have D: "?D $$ (i,j) = ?Aij" unfolding D id using choice ib index by auto
          have B: "B $$ (i,j) = ?Aij" unfolding B_outside[OF i j False] ..
          from index eqs False have "i \<noteq> ii" by auto
          have Bii: "B $$ (i, ii) = A $$ (i,ii)" unfolding B_outside[OF i `ii < n` False] ..
          hence C: "?C $$ (i,j) = ?Aij" unfolding C B Bii using `i \<noteq> ii` A_outside_ii[OF i False] by auto
          show ?thesis unfolding D C ..
        next
          case True
          with index have "i_begin \<le> i" "i \<le> i_end" "i < k" by auto
          note index = index this
          show ?thesis
          proof (cases "j > k")
            case True 
            note index = index this
            have D: "?D $$ (i,j) = (if i_begin + diff \<le> i then ?Aij - quot * A $$ (l + i - i_end, j) else ?Aij)" unfolding D
              using index by auto
            have B: "B $$ (i,j) = (if i_begin + Suc diff \<le> i then ?Aij - quot * A $$ (l + i - i_end, j) else ?Aij)" unfolding B
              using index by auto
            from index eqs have "j > ll" by auto
            hence C: "?C $$ (i,j) = (if i = ii then B $$ (i, j) - quot * B $$ (ll, j) else B $$ (i, j))" unfolding C
              using index by auto
            show ?thesis
            proof (cases "i_begin + Suc diff \<le> i \<or> \<not> (i_begin + diff \<le> i)")
              case True
              from True eqs index have "i \<noteq> ii" by auto
              from True have "?D $$ (i,j) = B $$ (i,j)" unfolding D B by auto
              also have "B $$ (i,j) = ?C $$ (i,j)" unfolding C using `i \<noteq> ii` by auto
              finally show ?thesis ..
            next
              case False
              hence i: "i = i_begin + diff" by simp
              with eqs index have ii: "ii = i" by auto
              from index eqs i ii have ll: "ll = l + i - i_end" by auto              
              have not: "\<not> (i_begin + Suc diff \<le> ll \<and> ll \<le> i_end)" 
              proof
                from eqs have "ll \<le> l" by auto
                assume "i_begin + Suc diff \<le> ll \<and> ll \<le> i_end"
                hence "i_begin < ll" "ll \<le> i_end" by auto
                with `ll \<le> l` have "i_begin < l" by auto
                with l_less_i have "\<not> l < i_end" by auto
                hence "l \<ge> i_end" by simp
                with il i_less_l have "i_end < lb" by auto
                from index large eqs have "lb \<le> ll" by auto
                with `i_end < lb` have "i_end < ll" by auto
                with `ll \<le> i_end` 
                show False by auto
              qed
              have D: "?D $$ (i,j) = ?Aij - quot * A $$ (ll, j)" unfolding D unfolding i ll by simp
              have C: "?C $$ (i,j) = ?Aij - quot * B $$ (ll, j)" unfolding C B unfolding ii i by simp
              have B: "B $$ (ll, j) = A $$ (ll, j)" unfolding BB[OF `ll < n` j] using index not by auto
              show ?thesis unfolding C D B unfolding ii i by (simp split: if_splits)
            qed
          next 
            case False
            hence "j < k \<or> j = k" by auto
            thus ?thesis
            proof
              assume jk: "j = k"
              hence "j \<noteq> Suc l - Suc iter" using index by auto
              hence "?D $$ (i,j) = (if i = i_end then 0 else ?Aij)" unfolding D using jk by auto
              also have "\<dots> = 0" using A_ik[OF ib_block `i_begin \<le> i`] `i \<le> i_end`  unfolding jk by auto
              finally have D: "?D $$ (i,j) = 0" .
              from jk index have "j \<noteq> ll" by auto
              hence C: "?C $$ (i,j) = (if i = ii then B $$ (i, j) - quot * B $$ (ll, j) else B $$ (i, j))" 
                unfolding C unfolding jk by simp
              have C: "?C $$ (i,j) = 0"
              proof (cases "i = i_end")
                case False
                with index ii jk have i: "i_begin \<le> i" "i < i_end" by auto
                from A_ik[OF ib_block this] have Aij: "A $$ (i,j) = 0" unfolding jk .
                from index i jk have "\<not> ((i, j) = (i_end - iter, Suc l - iter) \<and> iter \<notin> {0, Suc ?idiff})" by auto
                hence Bij: "B $$ (i,j) = 0" 
                  unfolding B Aij using i jk by auto
                hence C: "?C $$ (i,j) = (if i = ii then - quot * B $$ (ll,j) else 0)" unfolding C by auto
                let ?l = "l - iter"
                from index eqs have ll: "ll = ?l" by auto
                show "?C $$ (i,j) = 0"
                proof (cases "i = ii")
                  case True
                  with index eqs i have l: "lb \<le> ?l" "?l < l" and diff: "Suc diff \<noteq> Suc ?idiff" by auto
                  from A_ik[OF lbl l] have Alj: "A $$ (ll,j) = 0" unfolding jk ll .
                  from index l jk eqs have "\<not> ((ll, j) = (i_end - iter, Suc l - iter) \<and> iter \<notin> {0, Suc ?idiff})" by auto
                  hence Bij: "B $$ (ll,j) = 0" unfolding BB[OF `ll < n` j] Alj
                    using l jk diff by auto
                  thus ?thesis unfolding C by simp
                next
                  case False
                  thus ?thesis unfolding C by simp
                qed
              next
                case True note i = this
                hence Bij: "B $$ (i,j) = (if diff = ?idiff then A $$ (i_end, k) else 0)" unfolding B unfolding jk by auto
                show ?thesis
                proof (cases "i = ii")
                  case True
                  with i eqs have "diff = ?idiff" "ll = l" "iter = 0" by auto
                  hence B: "B $$ (i,j) = A $$ (i_end,k)" unfolding Bij by auto
                  have C: "?C $$ (i,j) = A $$ (i_end,k) - quot * B $$ (l, k)" 
                    unfolding C B unfolding True `ll =l` jk by simp
                  also have "B $$ (l,k) = A $$ (l,k)"
                    unfolding BB[OF `l < n` `k < n`] using il `iter = 0` by auto
                  also have "A $$ (i_end,k) - quot * \<dots> = 0" unfolding quot_def using Alk by auto
                  finally show ?thesis .
                next
                  case False
                  with i eqs have "diff \<noteq> ?idiff" by auto
                  thus ?thesis unfolding C Bij using False by auto
                qed
              qed
              show ?thesis unfolding C D ..
            next
              assume jk: "j < k"
              from eqs il have "ii \<noteq> ll" by auto
              show ?thesis
              proof (cases "diff = 0 \<or> (i,j) \<noteq> (ii - 1,ll)")
                case False
                with eqs have **: "i = i_end - Suc iter" "j = l - iter" "iter \<noteq> ?idiff" 
                  and *: "diff \<noteq> 0" "i = ii - 1" "j = ll" "ii \<noteq> 0" "i \<noteq> ii" by auto
                hence D: "?D $$ (i,j) = quot" unfolding D using jk index by auto
                from * index eqs False jk have i: "ii = Suc i" "i < i_end" by auto
                from iblock(5)[OF ib_block `i_begin \<le> i` `i < i_end`] 
                have Ai: "A $$ (i, ii) = 1" unfolding i .
                have "ii < k" "i \<noteq> i_end - iter" using index * ** eqs by auto
                hence Bi: "B $$ (i,ii) = 1" unfolding BB[OF `i < n` `ii < n`] Ai by auto
                have "B $$ (i,ll) = A $$ (i,ll)" unfolding BB[OF `i < n` `ll < n`] 
                  using `i \<noteq> i_end - iter` `ll < k` by auto
                also have "A $$ (i,ll) = 0"
                proof (rule ccontr)
                  assume nz: "A $$ (i,ll) \<noteq> 0"
                  from i eqs il have neq: "Suc i \<noteq> ll" by auto
                  from jb[OF `i < n` `ll < n` `ll < k`] nz neq 
                  have "i = ll" by auto
                  with i have "ii = Suc ll" by simp
                  hence "i_end - iter = Suc l - iter" using eqs by auto
                  from block[OF this] have "i_begin = i_end" by auto
                  with large ib lb index have "i = ii" by auto
                  with * show False by auto
                qed
                finally have C: "?C $$ (i,j) = quot" unfolding C using * Bi by auto
                show ?thesis unfolding C D ..
              next
                case True
                with eqs have "\<not> ((i, j) = (i_end - Suc iter, l - iter) \<and> iter \<noteq> ?idiff)" 
                  and not: "\<not> (i = ii - 1 \<and> j = ll \<and> iter \<noteq> ?idiff)" by auto
                from this(1) have D: "?D $$ (i,j) = ?Aij" unfolding D using jk index by auto
                {
                  fix i
                  assume "i < n"
                  with index have id: "((i,i) = (i_end,k)) = False" "(i_begin + Suc diff \<le> i \<and> i \<le> i_end \<and> k < i) = False" by auto
                  {
                    assume *: "(i, i) = (i_end - iter, Suc l - iter) \<and> iter \<notin> {0, Suc ?idiff}"
                    hence "i_end - iter = Suc l - iter" by auto
                    from block[OF this] * index large eqs have False by auto
                  }                    
                  hence "B $$ (i,i) = ?ev i" unfolding BB[OF `i < n` `i < n`] id if_False by auto
                } note Bdiag = this
                from eqs have ii: "ii = i_end - iter" "Suc l - iter = Suc ll" by auto
                have B: "B $$ (i,j) = 
                  (if (i, j) = (ii, Suc ll) \<and> iter \<noteq> 0 then quot else A $$ (i, j))" 
                  unfolding B using ii jk iter by auto
                have ll_i: "ll \<noteq> i_end - iter" using `ii \<noteq> ll` eqs by auto
                have "B $$ (ll,ii) = A $$ (ll,ii)" unfolding BB[OF `ll < n` `ii < n`]
                  using `ii < k` ll_i by auto
                also have "\<dots> = 0"
                proof (rule ccontr)
                  assume nz: "A $$ (ll,ii) \<noteq> 0"
                  with jb[OF `ll < n` `ii < n` `ii < k`] `ii \<noteq> ll` have "Suc ll = ii" by auto
                  with eqs have "i_end - iter = Suc l - iter" by auto
                  from block[OF this] index eqs have "iter = 0" by auto
                  with ii have "ll = l" "ii = i_end" by auto
                  with Alie nz show False by auto
                qed
                finally have Bli: "B $$ (ll,ii) = 0" .
                have C: "?C $$ (i,j) = ?Aij" 
                proof (cases "i = j")
                  case True
                  show ?thesis unfolding C unfolding Bdiag[OF `j < n`] True using `ii \<noteq> ll` Bli
                    by auto
                next
                  case False
                  from lb eqs index large have "lb \<le> ll" "ll \<le> l" by auto
                  note C = C[unfolded Bdiag[OF `i < n`] Bdiag[OF `j < n`]]
                  show ?thesis 
                  proof (cases "(i, j) = (ii, Suc ll) \<and> iter \<noteq> 0")
                    case True
                    hence *: "i = ii" "j = Suc ll" "iter \<noteq> 0" by auto
                    from * eqs index have "ll < l" "Suc ll < k" "Suc ll < n" by auto
                    have B: "B $$ (i,j) = quot" unfolding B using * by auto
                    have "\<not> ((ll, j) = (i_end - iter, Suc l - iter) \<and> iter \<notin> {0, Suc ?idiff})"
                      using * index eqs by auto
                    hence B': "B $$ (ll, j) = A $$ (ll, j)" 
                      unfolding BB[OF `ll < n` `j < n`] using jk by auto
                    have "?C $$ (i,j) = quot - quot * A $$ (ll, Suc ll)" unfolding C B using * B' by auto
                    with iblock(5)[OF lbl `lb \<le> ll` `ll < l`] have C: "?C $$ (i,j) = 0" by simp
                    {
                      assume "A $$ (ii, Suc ll) \<noteq> 0"
                      with jb[OF `ii < n` `Suc ll < n` `Suc ll < k`] `ii \<noteq> ll`
                      have "ii = Suc ll" by auto
                      with eqs have "i_end - iter = Suc l - iter" by auto
                      from block[OF this] `iter \<noteq> 0` `iter \<noteq> Suc ?idiff` eqs large have False by auto
                    }
                    hence "A $$ (ii,Suc ll) = 0" by auto
                    thus ?thesis unfolding C unfolding * by simp
                  next
                    case False
                    hence B: "B $$ (i,j) = ?Aij" unfolding B by auto
                    from iblock(1-2)[OF ib_block] ev_blocks_leD[OF inv(5), of i_begin _ i_end] ib `k < n`
                    have ev_i: "\<And> i. i_begin \<le> i \<Longrightarrow> i \<le> i_end \<Longrightarrow> ?ev i = ?ev k" by auto
                    from iblock(1-2)[OF lbl] ev_blocks_leD[OF inv(5), of lb _ l] lb `k < n`
                    have ev_l: "\<And> i. lb \<le> i \<Longrightarrow> i \<le> l \<Longrightarrow> ?ev i = ?ev k" by auto
                    from eqs index have "lb \<le> ll" "ll \<le> l" by auto
                    note index = index this ll_i
                    from ev_l[of ll] index have evl: "?ev ll = ?ev k" by auto
                    from ev_i[of i] index have evi: "?ev i = ?ev k" by auto
                    from not have not: "i \<noteq> ii - 1 \<or> j \<noteq> ll \<or> iter = ?idiff" by auto
                    from False have not2: "i \<noteq> ii \<or> j \<noteq> Suc ll \<or> iter = 0" by auto
                    show ?thesis
                    proof (cases "i = ii")
                      case True
                      let ?diff = "if j = ll then 0 else - quot * A $$ (ll, j)"
                      have Bli: "B $$ (ll, i) = 0" using True Bli by simp
                      have Blj: "B $$ (ll, j) = A $$ (ll,j)" unfolding BB[OF `ll < n` `j < n`] 
                        using index jk by auto
                      from True have C: "?C $$ (i,j) = ?Aij + ?diff" 
                        unfolding C B evi using Bli Blj evl by auto
                      also have "?diff = 0" 
                      proof (rule ccontr)
                        assume "?diff \<noteq> 0"
                        hence jl: "j \<noteq> ll" and Alj: "A $$ (ll,j) \<noteq> 0" by (auto split: if_splits)
                        with jb[OF `ll < n` `j < n` jk] have "j = Suc ll" "?ev ll = ?ev j" by auto
                        with not2 True have "iter = 0" by auto
                        with eqs index jk have id: "A $$ (ll, j) = A $$ (l, Suc l)" and 
                          "j = Suc l" "Suc l < k" "ll = l" 
                          unfolding `j = Suc ll` by auto
                        from iblock[OF lbl] `Suc l < k` have "A $$ (l, Suc l) \<noteq> 1" by auto
                        from jb[OF `l < n` `j < n` jk] Alj this show False unfolding `j = Suc l` `ll = l` by auto
                      qed
                      finally show ?thesis by simp
                    next
                      case False
                      let ?diff = "if j = ll then quot * B $$ (i, ii) else 0"
                      from False have C: "?C $$ (i,j) = ?Aij + ?diff"
                        unfolding C B by auto
                      also have "?diff = 0" 
                      proof (rule ccontr)
                        assume "?diff \<noteq> 0"
                        hence j: "j = ll" and Bi: "B $$ (i, ii) \<noteq> 0" by (auto split: if_splits)
                        from eqs have ii: "i_end - iter = ii" by auto
                        have Bii: "B $$ (i,ii) = A $$ (i, ii)"
                          unfolding BB[OF `i < n` `ii < n`] using `ii < k` iter ii False by auto
                        from Bi Bii have Ai: "A $$ (i,ii) \<noteq> 0" by auto
                        from jb[OF `i < n` `ii < n` `ii < k`] False Ai have ii: "ii = Suc i" 
                          and Ai: "A $$ (i,ii) = 1" by auto
                        from not ii j have iter: "iter = ?idiff" by auto
                        with eqs index have "ii = i_begin" by auto
                        with ii `i \<ge> i_begin` 
                        show False by auto
                      qed
                      finally show ?thesis by simp
                    qed
                  qed
                qed    
                show ?thesis unfolding D C ..
              qed
            qed
          qed
        qed
      qed auto
      also have "step_3_c_inner_loop quot (ll - 1) (ii - 1) diff \<dots> = ?R"
        by (rule Suc(1), insert prems large, auto)
      finally show ?case .
    qed
  }
  note main = this[of "Suc ?idiff" i_end 0 l]
  from ib have suc: "Suc i_end - i_begin = Suc ?idiff" by simp
  have "step_3_c_inner_loop (A $$ (i_end, k) / A $$ (l, k)) l i_end (Suc ?idiff) A
    = step_3_c_inner_loop quot l i_end (Suc ?idiff) (?mat 0 (Suc ?idiff))"
    unfolding mend unfolding quot_def ..
  also have "\<dots> = ?R" by (rule main, auto)
  finally show ?thesis unfolding suc .
qed

private lemma step_3_c_inv: "A \<in> carrier\<^sub>m n n 
  \<Longrightarrow> k < n 
  \<Longrightarrow> (lb,l) \<in> set (identify_blocks A k)
  \<Longrightarrow> inv_upto jb A k
  \<Longrightarrow> inv_from uppert A k
  \<Longrightarrow> inv_from diff_ev A k
  \<Longrightarrow> inv_at one_zero A k
  \<Longrightarrow> ev_blocks A
  \<Longrightarrow> set bs \<subseteq> set (identify_blocks A k)
  \<Longrightarrow> (\<And> be. be \<notin> snd ` set bs \<Longrightarrow> be \<notin> {l,k} \<Longrightarrow> be < n \<Longrightarrow> A $$ (be,k) = 0)
  \<Longrightarrow> (\<And> bb be. (bb,be) \<in> set bs \<Longrightarrow> be - bb \<le> l - lb) (* largest block *)
  \<Longrightarrow> x = A $$ (l,k)
  \<Longrightarrow> x \<noteq> 0
  \<Longrightarrow> inv_all uppert (step_3_c x l k bs A) \<and> inv_all diff_ev (step_3_c x l k bs A)
    \<and> same_diag A (step_3_c x l k bs A) 
    \<and> same_upto k A (step_3_c x l k bs A)
    \<and> inv_at (single_non_zero l k x) (step_3_c x l k bs A) k"
proof (induct bs arbitrary: A) 
  case (Nil A)
  note inv = Nil(4-8)
  from inv_from_upto_at_all[OF inv(1,3,2,4)] 
  have "inv_all diff_ev A" and "inv_all uppert A" unfolding one_zero_def diff_ev_def uppert_def by auto
  moreover 
  have "inv_at (single_non_zero l k x) A k" unfolding single_non_zero_def inv_at_def
    by (intro allI impI conjI, insert Nil, auto)
  ultimately show ?case by auto
next
  case (Cons p bs A)
  obtain i_begin i_end where p: "p = (i_begin, i_end)" by force
  note Cons = Cons[unfolded p]
  note IH = Cons(1)
  note A = Cons(2)
  note kn = Cons(3)
  note lbl = Cons(4)
  note inv = Cons(5-9)
  note blocks = Cons(10-12)
  note x = Cons(13-14)
  from identify_blocks[OF lbl] kn have lk: "l < k" and ln: "l < n" and "lb \<le> l" by auto
  def B \<equiv> "step_3_c_inner_loop (A $$ (i_end,k) / x) l i_end (Suc i_end - i_begin) A"
  show ?case 
  proof (cases "i_end = l")
    case True
    hence id: "step_3_c x l k (p # bs) A = step_3_c x l k bs A" unfolding p by simp
    show ?thesis unfolding id
      by (rule IH[OF A kn lbl inv _ blocks(2-3) x], insert blocks(1), auto simp: p True)
  next
    case False note il = this
    hence id: "step_3_c x l k (p # bs) A = step_3_c x l k bs B" unfolding B_def p by simp
    from blocks[unfolded p] have 
      ib_block: "(i_begin,i_end) \<in> set (identify_blocks A k)" and large: "i_end - i_begin \<le> l - lb" by auto
    from identify_blocks[OF this(1)] 
    have ibe: "i_begin \<le> i_end" "i_end < k" by auto
    have B: "B = mat n n (\<lambda> (i,j). if (i,j) = (i_end,k) then 0 else 
      if i_begin \<le> i \<and> i \<le> i_end \<and> j > k then A $$ (i,j) - A $$ (i_end,k) / x * A $$ (l + i - i_end,j) else A $$ (i,j))"
      unfolding B_def x
      by (rule step_3_c_inner_result[OF inv kn A lbl ib_block il large], insert x, auto)
    have Bn: "B \<in> carrier\<^sub>m n n" unfolding B by auto
    have sdAB: "same_diag A B" unfolding B same_diag_def using ibe by auto
    have suAB: "same_upto k A B" using A kn unfolding B same_upto_def by auto
    have inv_ev: "ev_blocks B" using same_diag_ev_blocks[OF sdAB inv(5)] .
    have inv_jb: "inv_upto jb B k" using same_upto_inv_upto_jb[OF suAB inv(1)] .
    have ib: "identify_blocks A k = identify_blocks B k" using identify_blocks_cong[OF kn sdAB suAB] .
    have inv_ut: "inv_from uppert B k" using inv(2) ibe unfolding B inv_from_def uppert_def by auto
    from x il ibe kn lk have xB: "x = B $$ (l,k)" by (auto simp: B)
    {
      fix be
      assume *: "be \<notin> snd ` set bs" "be \<notin> {l, k}" "be < n" 
      hence "B $$ (be, k) = 0" using kn blocks(2)[of be] unfolding B
        by (cases "be = i_end", auto)
    } note blocksB = this
    have bs: "set bs \<subseteq> set (identify_blocks A k)" using blocks(1) by auto
    have inv_oz: "inv_at one_zero B k" using inv(4) ibe kn unfolding B inv_at_def one_zero_def by auto
    have inv_diff: "inv_from diff_ev B k"
    proof (intro inv_fromI)
      fix i j      
      assume *: "i < n" "j < n" "k < j"
      have diff: "diff_ev A i j" using inv_fromD[OF inv(3) *] .
      show "diff_ev B i j" unfolding diff_ev_def
      proof (intro impI)
        assume "i < j" "B $$ (i,i) \<noteq> B $$ (j,j)"
        with sdAB * have diff_ev: "A $$ (i,i) \<noteq> A $$ (j,j)" unfolding same_diag_def by auto
        with diff `i < j` have Aij: "A $$ (i,j) = 0" unfolding diff_ev_def by auto
        let ?i = "l + i - i_end"
        {
          assume "B $$ (i,j) \<noteq> 0"
          hence **: "i_begin \<le> i" "i \<le> i_end" "A $$ (?i, j) \<noteq> 0" 
            using ibe * Aij unfolding B by (auto split: if_splits)
          note ev = ev_blocks_leD[OF inv(5)]
          note ib = identify_blocks_iff[OF inv(5) kn]
          let ?ev = "A $$ (k,k)"
          from lbl[unfolded ib] have evl: "A $$ (lb,lb) = ?ev" "A $$ (l,l) = ?ev" by auto
          from ib_block[unfolded ib] have ev_i: "A $$ (i_begin,i_begin) = ?ev" "A $$ (i_end,i_end) = ?ev" by auto
          from large `lb \<le> l` ** ln have "lb \<le> ?i" "?i \<le> l" "?i < n" by auto
          from ev[OF this(1-2) ln] evl have Ai: "A $$ (?i,?i) = ?ev" by auto
          from ev[OF **(1-2)] ibe kn ev_i have A_i: "A $$ (i,i) = ?ev" by auto
          with diff_ev Ai have Aj: "A $$ (j,j) \<noteq> A $$ (?i,?i)" by auto
          from inv_fromD[OF inv(3) `?i < n` `j < n` `k < j`] have "diff_ev A ?i j" .
          from this[unfolded diff_ev_def] Aj `k < j` `?i \<le> l` `l < k` have "A $$ (?i,j) = 0" by auto
          with ** have False by auto
        }
        thus "B $$ (i,j) = 0" by auto
      qed
    qed
    show ?thesis unfolding id 
      using IH[OF Bn kn, folded ib, OF lbl inv_jb inv_ut inv_diff inv_oz inv_ev bs blocksB blocks(3) xB x(2)]
      using same_diag_trans[OF sdAB] same_upto_trans[OF suAB]
      by auto
  qed
qed

private lemma step_3_main_inv: "A \<in> carrier\<^sub>m n n 
  \<Longrightarrow> k > 0
  \<Longrightarrow> inv_all uppert A 
  \<Longrightarrow> inv_all diff_ev A 
  \<Longrightarrow> ev_blocks A 
  \<Longrightarrow> inv_upto jb A k
  \<Longrightarrow> inv_all jb (step_3_main n k A)"
proof (induct k A taking: n rule: step_3_main.induct)
  case (1 k A)
  from 1(2-) have A: "A \<in> carrier\<^sub>m n n" and k: "k > 0" and
    inv: "inv_all uppert A" "inv_all diff_ev A" "ev_blocks A" "inv_upto jb A k" by auto
  note [simp] = step_3_main.simps[of n k A]
  show ?case
  proof (cases "k \<ge> n")
    case True
    thus ?thesis using inv_uptoD[OF inv(4)]
      by (intro inv_allI, auto)
  next
    case False
    hence kn: "k < n" by simp
    obtain B where B: "B = step_3_a (k - 1) k A" by auto
    note IH = 1(1)[OF False B]
    from A have Bn: "B \<in> carrier\<^sub>m n n" unfolding B mat_carrier_def by simp
    from k have "k - 1 < k" by simp    
    have "inv_from_bot (\<lambda>A i. one_zero A i k) A (k - 1)"
      using inv_all_uppertD[OF inv(1), of k] inv_all_diff_evD[OF inv(2), OF _ `k < n`]
      unfolding inv_from_bot_def one_zero_def by auto
    from step_3_a_inv[OF A `k - 1 < k` `k < n` 
      inv(4) inv_all_imp_inv_from[OF inv(1)]
      inv_all_imp_inv_from[OF inv(2)] inv_all_imp_inv_at[OF inv(2) `k < n`] this inv(3)] 
    have inv: "inv_from uppert B k" "inv_from diff_ev B k"  
      "ev_blocks B" "inv_upto jb B k" 
      "inv_at one_zero B k" unfolding B by auto
    obtain all_blocks where ab: "all_blocks = identify_blocks B k" by simp
    obtain blocks where blocks: "blocks = filter (\<lambda> block. B $$ (snd block, k) \<noteq> 0) all_blocks" by simp
    obtain F where F: "F = (if blocks = [] then B
       else let (l_begin,l) = find_largest_block (hd blocks) (tl blocks); x = B $$ (l, k); C = step_3_c x l k blocks B;
            D = mult_col_div_row (inverse x) k C; E = swap_cols_rows_block (Suc l) k D
        in E)" by simp
    note IH = IH[OF ab blocks F]
    have Fn: "F \<in> carrier\<^sub>m n n" unfolding F Let_def mat_carrier_def using Bn 
      by (simp split: prod.splits)
    have inv: "inv_all uppert F \<and> inv_all diff_ev F \<and> ev_blocks F 
      \<and> inv_upto jb F (Suc k)" 
    proof (cases "blocks = []")
      case True
      hence F: "F = B" unfolding F by simp
      have lo: "inv_at (lower_one k) B k" 
      proof
        fix i
        assume i: "i < n"
        note lower_one_def[simp]
        show "lower_one k B i k" 
        proof (cases "B $$ (i,k) = 0")
          case False note nz = this
          note oz = inv_atD[OF inv(5) i, unfolded one_zero_def]
          from nz oz have "i \<le> k" by auto
          show ?thesis 
          proof (cases "i = k")
            case False
            with `i \<le> k` have "i < k" by auto
            with nz oz have ev: "B $$ (i,i) = B $$ (k,k)" unfolding diff_ev_def by auto
            have "(snd (identify_block B i), i) \<in> set all_blocks" unfolding ab
            proof (rule identify_blocks_rev[OF _ ev inv(3) `k < n`]) 
              show "B $$ (i, Suc i) = 0 \<and> Suc i < k \<or> Suc i = k"
              proof (cases "Suc i = k")
                case False
                with `i < k` `k < n` have "Suc i < k" "Suc i < n" by simp_all
                with nz oz have "B $$ (i, Suc i) \<noteq> 1" by simp
                with inv_uptoD[OF inv(4) `i < n` `Suc i < n` `Suc i < k`, unfolded jb_def]
                have "B $$ (i, Suc i) = 0" by simp
                thus ?thesis using `Suc i < k` by simp
              qed simp
            qed
            with arg_cong[OF `blocks = []`[unfolded blocks], of set] have "B $$ (i,k) = 0" by auto
            with nz show ?thesis by auto
          qed auto
        qed auto
      qed
      have inv_jb: "inv_upto jb B (Suc k)"
      proof (rule inv_upto_Suc[OF inv(4)])
        fix i
        assume "i < n"
        from inv_atD[OF lo `i < n`, unfolded lower_one_def]
        show "jb B i k" unfolding jb_def by auto
      qed
      with inv inv_from_upto_at_all[OF inv(4) inv(2) inv(1) lo lower_one_diff_uppert] 
      show ?thesis unfolding F by simp
    next
      case False
      obtain l_start l where l: "find_largest_block (hd blocks) (tl blocks) = (l_start, l)" by force
      obtain x where x: "x = B $$ (l,k)" by simp
      obtain C where C: "C = step_3_c x l k blocks B" by simp
      obtain D where D: "D = mult_col_div_row (inverse x) k C" by auto
      obtain E where E: "E = swap_cols_rows_block (Suc l) k D" by auto
      from find_largest_block[OF False l] have lb: "(l_start,l) \<in> set blocks"
        and llarge: "\<And> i_begin i_end. (i_begin,i_end) \<in> set blocks \<Longrightarrow> l - l_start \<ge> i_end - i_begin" by auto
      from lb have x0: "x \<noteq> 0" unfolding blocks x by simp
      {
        fix i_start i_end
        assume "(i_start,i_end) \<in> set blocks"
        hence "(i_start,i_end) \<in> set (identify_blocks B k)" unfolding blocks ab by simp
        with identify_blocks[OF this]
        have "i_end < k" "(i_start,i_end) \<in> set (identify_blocks B k)" by auto
      } note block_bound = this
      from block_bound[OF lb]
      have lk: "l < k" and lblock: "(l_start, l) \<in> set (identify_blocks B k)" by auto
      from lk `k < n` have ln: "l < n" by simp
      from lblock[unfolded identify_blocks_iff[OF inv(3) `k < n`]] 
      have Bll: "B $$ (l,l) = B $$ (k,k)" by simp
      from False have F: "F = E" unfolding E D C x F l Let_def by simp
      from Bn have Cn: "C \<in> carrier\<^sub>m n n" unfolding C mat_carrier_def by simp
      {
        fix be
        assume nmem: "be \<notin> snd ` set blocks" and belk: "be \<notin> {l, k}" and be: "be < n"
        have "B $$ (be, k) = 0"
        proof (rule ccontr)
          assume nz: "\<not> ?thesis"
          note oz = inv_atD[OF inv(5) be, unfolded one_zero_def]
          from belk oz be nz have "be < k" and bek: "B $$ (be,be) = B $$ (k,k)" by auto
          obtain ev bb where ib: "identify_block B be = (ev,bb)" by force
          note ib_inv = identify_block[OF ib]
          have "B $$ (be, Suc be) = 0 \<and> Suc be < k \<or> Suc be = k"
          proof (cases "Suc be = k")
            case False
            with `be < k` have sbek: "Suc be < k" by auto
            from inv_uptoD[OF inv(4) `be < n` _ sbek] sbek kn have "jb B be (Suc be)" by auto
            from this[unfolded jb_def] have 01: "B $$ (be, Suc be) \<in> {0,1}" by auto
            from 01 oz sbek nz have "B $$ (be, Suc be) = 0" by auto
            with sbek show ?thesis by auto
          qed auto
          from identify_blocks_rev[OF this bek inv(3) kn] 
             nz nmem show False unfolding ab blocks by force 
        qed
      }
      note inv3 = step_3_c_inv[OF Bn `k < n` lblock inv(4,1,2,5,3) _ this llarge x x0, of blocks, folded C,
        unfolded ab blocks]
      from inv3 have sdC: "same_diag B C" and suC: "same_upto k B C" by auto
      from Bll sdC ln `k < n` 
      have Cll: "C $$ (l,l) = C $$ (k,k)" unfolding same_diag_def by auto
      from same_diag_ev_blocks[OF sdC inv(3)] same_upto_inv_upto_jb[OF suC inv(4)] inv3 
      have inv: "inv_all uppert C" "inv_all diff_ev C" "ev_blocks C"
        "inv_upto jb C k" "inv_at (single_non_zero l k x) C k" by auto
      from x0 have "inverse x \<noteq> 0" by simp
      from Cn have Dn: "D \<in> carrier\<^sub>m n n" unfolding D mat_carrier_def by simp
      {
        fix i j
        assume i: "i < n" and j: "j < n"
        with Cn have dC: "i < dim\<^sub>r C" "i < dim\<^sub>c C" "j < dim\<^sub>r C" "j < dim\<^sub>c C" by auto
        let ?c = "C $$ (i,j)"
        let ?x = "inverse x"
        have "D $$ (i,j) = (if i = l \<and> j = k then 1 else if i = k \<and> j \<noteq> k then x * ?c else ?c)"
          unfolding D
        proof (subst mult_col_div_row_index[OF dC `inverse x \<noteq> 0`], unfold inverse_inverse_eq)
          note at = inv_atD[OF inv(5) `i < n`, unfolded single_non_zero_def]
          show "(if i = k \<and> j \<noteq> i then x * ?c 
            else if j = k \<and> j \<noteq> i then ?x * ?c else ?c) =
            (if i = l \<and> j = k then 1 else if i = k \<and> j \<noteq> k then x * ?c else ?c)" (is "?l = ?r")
          proof (cases "(i,j) = (l,k)")
            case True
            with lk have "?l = ?x * ?c" by auto
            also have "\<dots> = 1" using at True `inverse x \<noteq> 0` by auto
            finally show ?thesis using True by simp
          next
            case False note neq = this
            have "?l = (if i = k \<and> j \<noteq> k then x * ?c else ?c)"
            proof (cases "i = k \<and> j \<noteq> k \<or> j = k \<and> i \<noteq> k")
              case True
              thus ?thesis
              proof
                assume *: "i = k \<and> j \<noteq> k"
                hence l: "?l = x * ?c" by simp
                show ?thesis using * neq unfolding l by simp
              next
                assume *: "j = k \<and> i \<noteq> k"
                hence "?l = ?x * ?c" using lk by auto
                from * neq have "i \<noteq> l" and **: "\<not> (i = k \<and> j \<noteq> k)" by auto
                from at `i \<noteq> l` * have "?c = 0" by auto
                with `?l = ?x * ?c` ** show ?thesis by auto
              qed
            qed auto
            also have "\<dots> = ?r" using False by auto
            finally show ?thesis .
          qed
        qed
      } note D = this 
      have sD[simp]: "\<And> i. i < n \<Longrightarrow> D $$ (i,i) = C $$ (i,i)" using lk by (auto simp: D)
      from `C $$ (l,l) = C $$ (k,k)` `l < n` `k < n`
      have Dll: "D $$ (l,l) = D $$ (k,k)" by simp      
      have sd: "same_diag C D" unfolding same_diag_def by simp
      from same_diag_ev_blocks[OF this inv(3)] have invD: "ev_blocks D" .
      note inv = inv_uptoD[OF inv(4), unfolded jb_def] inv_all_uppertD[OF inv(1)] inv_all_diff_evD[OF inv(2)]
        inv_atD[OF inv(5), unfolded single_non_zero_def]
      have "inv_all diff_ev D"
        by (intro inv_allI, insert inv(3), auto simp: diff_ev_def D Cll)
      moreover have "inv_all uppert D"
        by (intro inv_allI, insert inv(2) lk, auto simp: uppert_def D)
      moreover have suD: "same_upto k C D" 
      proof 
        fix i j
        assume i: "i < n" and j: "j < k"
        with kn have jn: "j < n" by simp
        show "C $$ (i, j) = D $$ (i, j)"  
          unfolding D[OF i jn] using j k
           inv(1)[OF i jn j] i j by auto
      qed
      from same_upto_inv_upto_jb[OF suD `inv_upto jb C k`]
      have "inv_upto jb D k" .
      moreover 
      let ?single_one = "single_one l k"
      have "inv_at ?single_one D k" 
        by (intro inv_atI, insert inv(4) D[OF _ `k < n`] ln, auto simp: single_one_def)
      ultimately
      have inv: "inv_all uppert D" "inv_all diff_ev D" "ev_blocks D"
        "inv_upto jb D k" "inv_at ?single_one D k" using invD by blast+
      note inv = inv_uptoD[OF inv(4), unfolded jb_def] 
        inv_all_uppertD[OF inv(1)] inv_all_diff_ev_uppertD[OF inv(2) inv(1)]
        inv_atD[OF inv(5), unfolded single_one_def]
        ev_blocks_leD[OF inv(3)]
      from suC suD have suD: "same_upto k B D" unfolding same_upto_def by auto
      let ?I = "\<lambda> j. if j = Suc l then k else if Suc l < j \<and> j \<le> k then j - 1 else j"
      let ?I' = "\<lambda> j. if j = Suc l then k else j - 1"
      {
        fix i j
        assume i: "i < n" and j: "j < n"
        with Dn lk `k < n`
        have dims: "i < dim\<^sub>r D" "i < dim\<^sub>c D" "j < dim\<^sub>r D" "j < dim\<^sub>c D" 
          "Suc l \<le> k" "k < dim\<^sub>r D" "k < dim\<^sub>c D" by auto
        have "E $$ (i,j) = D $$ (?I i, ?I j)" 
          unfolding E by (rule subst swap_cols_rows_block_index[OF dims])
      } note E = this
      {
        fix i
        assume i: "i < n"
        from `l < k` have "l \<le> Suc l" "Suc l \<le> k" by auto
        from inv(5)[OF this `k < n`] Dll 
          inv(5)[of l i k, OF _ _ `k < n`] inv(5)[of l "i - 1" k, OF _ _ `k < n`]
        have "E $$ (i,i) = D $$ (i,i)" unfolding E[OF i i] using lk by auto
      } note Ed = this
      {
        fix i
        assume "l \<le> i" "i \<le> k"
        from inv(5)[OF this `k < n`] Dll have "D $$ (i,i) = D $$ (k,k)" by auto
      } note Dik = this
      from Ed have ed: "same_diag D E" unfolding same_diag_def by auto
      have "ev_blocks E" using same_diag_ev_blocks[OF ed `ev_blocks D`] by auto
      moreover 
      {
        fix i j
        assume i: "i < n" and j: "j < n" and neg: "D $$ (i,i) \<noteq> D $$ (j,j)" 
        from inv(3)[OF i j neg] have Dij: "D $$ (i,j) = 0" .
        have "E $$ (i,j) = 0"
        proof (cases "E $$ (i,j) = D $$ (i,j)")
          case True
          with Dij show ?thesis by simp
        next
          case False
          from this[unfolded E[OF i j]] 
          have "(i = Suc l \<or> Suc l < i \<and> i \<le> k) \<or> (j = Suc l \<or> Suc l < j \<and> j \<le> k)"
            by (auto split: if_splits)
          thus ?thesis
          proof
            assume *: "i = Suc l \<or> Suc l < i \<and> i \<le> k"
            with Dik[of i] lk have "D $$ (i,i) = D $$ (k,k)" by auto
            with neg have neg: "D $$ (j,j) \<noteq> D $$ (k,k)" by simp
            with Dik[of j] lk have "\<not> l \<le> j \<or> \<not> j \<le> k" by auto
            with lk * have E: "E $$ (i,j) = D $$ (?I' i, j)" unfolding E[OF i j] by auto
            from * lk `k < n` have "l \<le> ?I' i" "?I' i \<le> k" "?I' i < n" by auto
            from Dik[OF this(1-2)] neg have neg: "D $$ (?I' i, ?I' i) \<noteq> D $$ (j,j)" by auto
            from inv(3)[OF `?I' i < n` `j < n` neg] show ?thesis unfolding E .
          next
            assume *: "j = Suc l \<or> Suc l < j \<and> j \<le> k"
            with Dik[of j] lk have "D $$ (j,j) = D $$ (k,k)" by auto
            with neg have neg: "D $$ (i,i) \<noteq> D $$ (k,k)" by simp
            with Dik[of i] lk have "\<not> l \<le> i \<or> \<not> i \<le> k" by auto
            with lk * have E: "E $$ (i,j) = D $$ (i, ?I' j)" unfolding E[OF i j] by auto
            from * lk `k < n` have "l \<le> ?I' j" "?I' j \<le> k" "?I' j < n" by auto
            from Dik[OF this(1-2)] neg have neg: "D $$ (i,i) \<noteq> D $$ (?I' j, ?I' j)" by auto
            from inv(3)[OF `i < n` `?I' j < n` neg] show ?thesis unfolding E .
          qed
        qed
      } note diff_ev = this
      have Eed: "inv_all diff_ev E"
        by (intro inv_allI, unfold diff_ev_def, intro impI, rule diff_ev, auto simp: Ed)
      moreover have Eut: "inv_all uppert E" 
      proof (intro inv_allI, unfold uppert_def, intro impI)
        fix i j 
        assume i: "i < n" and j: "j < n" and ji: "j < i"
        have "?I i < n" using i `k < n` by auto
        show "E $$ (i,j) = 0"
        proof (cases "?I j < ?I i")
          case True
          from inv(2)[OF this `?I i < n`] show ?thesis unfolding E[OF i j] .
        next
          case False
          have "?I i \<noteq> ?I j" using ji lk by (auto split: if_splits)
          with False have ij: "?I i < ?I j" by simp
          from ij ji have jl: "j = Suc l" using lk by (auto split: if_splits)
          with ji ij have il: "i > Suc l" "i \<le> k" by (auto split: if_splits)
          from jl il have Eij: "E $$ (i,j) = D $$ (i-1,k)" unfolding E[OF i j] by simp
          have "i - 1 < n" "i - 1 \<notin> {k, l}" using i il by auto
          with inv(4)[of "i-1"] have D: "D $$ (i-1,k) = 0" by auto
          show ?thesis unfolding Eij D by simp
        qed
      qed
      moreover 
      from same_diag_trans[OF `same_diag B C` `same_diag C D`] have "same_diag B D" .
      from identify_blocks_cong[OF `k < n` this suD] 
      have idb: "identify_blocks B k = identify_blocks D k" .
      have "inv_upto jb E (Suc k)" 
      proof (intro inv_uptoI)
        fix i j
        assume i: "i < n" and j: "j < n" and "j < Suc k"
        hence jk: "j \<le> k" by simp
        show "jb E i j"
        proof (cases "E $$ (i,j) = 0 \<or> j = i")
          case True
          thus ?thesis unfolding jb_def by auto
        next
          case False note enz = this
          note inv2 = diff_ev[OF i j] inv_all_uppertD[OF Eut _ i, of j]
          from False inv2 have "\<not> j < i" and same_ev: "D $$ (i,i) = D $$ (j,j)" by auto
          with False have ji: "j > i" by auto
          have "E $$ (i,j) \<in> {0,1} \<and> (j \<noteq> Suc i \<longrightarrow> E $$ (i,j) = 0)"
          proof (cases "j \<le> l")
            case True note jl = this
            with ji lk have il: "i \<le> l" and jk: "j < k" by auto
            have id: "E $$ (i,j) = D $$ (i,j)" unfolding E[OF i j] using jl il by simp
            from inv(1)[OF i j jk] ji
            show ?thesis unfolding id by auto
          next
            case False note jl = this
            show ?thesis
            proof (cases "j = Suc l")
              case True note jl = this
              with ji lk have il: "i \<le> l" "i \<noteq> k" by auto
              have id: "E $$ (i,j) = D $$ (i,k)" unfolding E[OF i j] using jl il by auto
              from inv(4)[OF i] jl il
              show ?thesis unfolding id by (cases "i = l", auto)
            next
              case False
              with jl jk kn have jl: "j > Suc l" and jk: "j - 1 < k" and jn: "j - 1 < n" by auto
              with jk have id: "?I j = j - 1" by auto
              note jb = inv(1)[OF _ jn jk]
              show ?thesis
              proof (cases "i < Suc l")
                case True note il = this
                with id have id: "E $$ (i,j) = D $$ (i,j - 1)" unfolding E[OF i j] by auto
                show ?thesis 
                proof (cases "i = j - 2")
                  case False
                  thus ?thesis unfolding id using jb[OF i] il jl by auto
                next
                  case True
                  with il jl have *: "j = Suc (Suc l)" "i = l" by auto
                  with id have id: "E $$ (i,j) = D $$ (l,Suc l)" by auto
                  from * jl jk have neq: "Suc l \<noteq> k" by auto
                  from lblock[unfolded idb] have "(l_start, l) \<in> set (identify_blocks D k)" .
                  from this[unfolded identify_blocks_iff[OF `ev_blocks D` kn]] neq
                  have "D $$ (l, Suc l) \<noteq> 1" by auto
                  with jb[OF i] il jl ji * have "D $$ (l, Suc l) = 0" by auto
                  thus ?thesis unfolding id by simp
                qed
              next
                case False note il = this
                show ?thesis
                proof (cases "i = Suc l")
                  case True 
                  with id have id: "E $$ (i,j) = D $$ (k,j - 1)" unfolding E[OF i j] by auto
                  from inv(2)[OF jk kn] show ?thesis unfolding id by simp
                next
                  case False
                  with il jl ji jk kn have il: "i > Suc l" and ik: "i < k" and i_n: "i - 1 < n" by auto
                  with id have id: "E $$ (i,j) = D $$ (i - 1, j - 1)" unfolding E[OF i j] by auto
                  show ?thesis unfolding id using jb[OF i_n] il jl ji by auto
                qed
              qed
            qed
          qed
          thus "jb E i j" unfolding jb_def Ed[OF i] Ed[OF j] same_ev by auto
        qed
      qed
      ultimately show ?thesis unfolding F by simp
    qed
    hence inv: "inv_all uppert F" "inv_all diff_ev F" "ev_blocks F"
      "inv_upto jb F (Suc k)" by auto
    have "0 < Suc k" by simp
    note IH = IH[OF Fn this]
    have id: "step_3_main n k A = step_3_main n (Suc k) F" using kn 
      by (simp add: F Let_def blocks ab B)
    show ?thesis unfolding id
      by (rule IH, insert inv, auto)
  qed
qed

text \<open>The desired result: @{const triangular_to_jnf} results in a JNF\<close>

lemma triangular_to_jnf_inv: 
  assumes A: "A \<in> carrier\<^sub>m n n"
  and upper_t: "upper_triangular A"
  shows "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> jb (triangular_to_jnf A) i j"
proof -
  from A have d: "dim\<^sub>r A = n" by simp
  let ?B = "step_2 (step_1 A)"
  let ?C = "step_3 ?B"
  from upper_triangularD[OF upper_t] have inv: "inv_all uppert A"
    unfolding inv_all_def uppert_def using A by auto
  from upper_t have inv2: "inv_part diff_ev A 0 0"
    unfolding inv_part_def diff_ev_def by auto
  have inv3: "ev_blocks_part 0 (step_1 A)"
    by (rule ev_blocks_partI, auto)
  have A1: "step_1 A \<in> carrier\<^sub>m n n" using A unfolding mat_carrier_def by auto
  from A1 have d1: "dim\<^sub>r (step_1 A) = n" unfolding mat_carrier_def by simp
  have B: "?B \<in> carrier\<^sub>m n n" using A unfolding mat_carrier_def by auto
  from B have d2: "dim\<^sub>r ?B = n" unfolding mat_carrier_def by simp
  have "inv_all uppert (step_1 A) \<and> inv_all diff_ev (step_1 A)" unfolding step_1_def d
    by (rule step_1_main_inv[OF _ A inv inv2], simp)
  hence "inv_all uppert (step_1 A)" and "inv_all diff_ev (step_1 A)" by auto
  from step_2_main_inv[OF A1 this inv3]
  have inv: "inv_all uppert ?B" "inv_all diff_ev ?B" "ev_blocks ?B" 
    unfolding step_2_def d d1 by auto
  have inv4: "inv_upto jb (step_2 (step_1 A)) 1"
  proof (rule inv_uptoI)
    fix i j
    assume "i < n" "j < n" and "j < 1"
    hence j: "j = 0" and jn: "0 < n" by auto
    show "jb ?B i j" unfolding jb_def j using inv_all_uppertD[OF inv(1) _ `i < n`, of 0]
      by auto
  qed
  from step_3_main_inv[OF B _ inv inv4]
  have "inv_all jb (triangular_to_jnf A)" unfolding triangular_to_jnf_def o_def step_3_def d2 by simp
  thus "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> jb (triangular_to_jnf A) i j" unfolding inv_all_def by auto
qed

subsection \<open>A Combination with JNF Represented as Vectors\<close>

lemma jnf_vector: assumes A: "A \<in> carrier\<^sub>m n n"
  and jb: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> jb A i j"
  shows "jordan_matrix (jnf_vector A) = (A :: 'a :: field mat)"
proof -
  from A have "dim\<^sub>r A = n" by simp
  hence id: "jnf_vector A = jnf_vector_main n A" unfolding jnf_vector_def by auto
  let ?map = "map (\<lambda>(n, a). jordan_block n (a :: 'a))"
  let ?B = "\<lambda> k. diag_block_mat (?map (jnf_vector_main k A))"
  {
    fix k
    assume "k \<le> n"
    hence "(\<forall> i j. i < k \<longrightarrow> j < k \<longrightarrow> ?B k $$ (i,j) = A $$ (i,j))
      \<and> diag_block_mat (?map (jnf_vector_main k A)) \<in> carrier\<^sub>m k k"
    proof (induct k rule: less_induct)
      case (less sk)
      show ?case
      proof (cases sk)
        case (Suc k)
        obtain ev b where ib: "identify_block A k = (ev,b)" by force
        hence id: "jnf_vector_main sk A = jnf_vector_main b A @ [(Suc k - b, ev)]" unfolding Suc by simp
        let ?c = "Suc k - b"
        def B \<equiv> "?B b"
        def C \<equiv> "jordan_block ?c ev"
        have C: "C \<in> carrier\<^sub>m ?c ?c" unfolding C_def by auto
        let ?FB = "\<lambda> Bb Cc. four_block_mat Bb (\<zero>\<^sub>m (dim\<^sub>r Bb) (dim\<^sub>c Cc)) (\<zero>\<^sub>m (dim\<^sub>r Cc) (dim\<^sub>c Bb)) Cc"
        from identify_block_le[OF ib] have bk: "b \<le> k" .
        with Suc less(2) have "b < sk" "b \<le> n" by auto
        note IH = less(1)[OF this, folded B_def]
        have B: "B \<in> carrier\<^sub>m b b" using IH by simp
        from bk Suc have sk: "sk = b + ?c" by auto
        show ?thesis unfolding id map_append list.simps diag_block_mat_last split B_def[symmetric] C_def[symmetric] Let_def
        proof (intro allI conjI impI)
          show "?FB B C \<in> carrier\<^sub>m sk sk" unfolding sk using four_block_mat_carrier[OF B C] .
          fix i j
          assume i: "i < sk" and j: "j < sk"
          with jb `sk \<le> n` 
          have jb: "jb A i j" by auto
          have ut: "uppert A i j" by (rule jb_imp_uppert[OF jb])
          have de: "diff_ev A i j" by (rule jb_imp_diff_ev[OF jb])
          from B C have dim: "dim\<^sub>r B = b" "dim\<^sub>c B = b" "dim\<^sub>c C = ?c" "dim\<^sub>r C = ?c" by auto
          from sk B C i j have "i < dim\<^sub>r B + dim\<^sub>r C" "j < dim\<^sub>c B + dim\<^sub>c C" by auto
          note id = four_block_mat_index(1)[OF this, unfolded dim]
          have id: "?FB B C $$ (i,j) = 
          (if i < b then if j < b then B $$ (i, j) else 0 
            else if j < b then 0 else C $$ (i - b, j - b))" 
            unfolding id dim using i j sk by auto
          show "?FB B C $$ (i,j) = A $$ (i,j)" 
          proof (cases "i < b \<and> j < b")
            case True (* upper left *)
            hence "?FB B C $$ (i,j) = B $$ (i,j)" unfolding id by auto
            with IH True show ?thesis by auto
          next
            case False note not_ul = this
            note ib = identify_block[OF ib]
            show ?thesis
            proof (cases "\<not> i < b \<and> j < b \<or> i < b \<and> \<not> j < b")
              case True (* not on main diagonal *)
              hence id: "?FB B C $$ (i,j) = 0" unfolding id by auto
              show ?thesis
              proof (cases "j < i") 
                case True (* lower left *)
                with ut show ?thesis unfolding id uppert_def by auto
              next
                case False (* upper right *)
                with True have *: "j \<ge> b" "i < b" "j > i" by auto
                have "A $$ (i,j) = 0" 
                proof (rule ccontr)
                  assume "A $$ (i,j) \<noteq> 0"
                  with jb[unfolded jb_def] *
                  have ji: "j = b" "i = b - 1" "b > 0" and no_border: "A $$ (i, i) = A $$ (j, j)" "A $$ (i,j) = 1" by auto
                  from no_border[unfolded ji] ib(3-4) `b > 0` show False by auto                
                qed
                thus ?thesis unfolding id by simp
              qed
            next
              case False (* lower right *)
              with not_ul have *: "\<not> i < b" "\<not> j < b" by auto
              hence id: "?FB B C $$ (i,j) = C $$ (i - b, j - b)" unfolding id by auto
              from * i j have ijc: "i - b < ?c" "j - b < ?c" unfolding sk by auto
              have id: "?FB B C $$ (i,j) = (if i - b = j - b then ev else if Suc (i - b) = j - b then 1 else 0)"
                unfolding id unfolding C_def jordan_block_index(1)[OF ijc] ..
              show ?thesis 
              proof (cases "i - b = j - b")
                case True
                hence id: "?FB B C $$ (i,j) = ev" unfolding id by simp
                from True * have ij: "j = i" by auto
                from ib(6)[of i] True * i j Suc have "A $$ (i,j) = ev" unfolding ib(2) ij by auto
                with id show ?thesis by simp
              next
                case False note neq = this
                show ?thesis
                proof (cases "j - b = Suc (i - b)")
                  case True
                  hence id: "?FB B C $$ (i,j) = 1" unfolding id by simp
                  from True * have ij: "j = Suc i" by auto
                  from ib(5)[of i] True * i j Suc have "A $$ (i,j) = 1" unfolding ij by auto
                  with id show ?thesis by simp
                next
                  case False
                  with neq have id: "?FB B C $$ (i,j) = 0" unfolding id by simp
                  from * neq False have "i \<noteq> j" "Suc i \<noteq> j" by auto
                  with jb[unfolded jb_def] have "A $$ (i,j) = 0" by auto
                  with id show ?thesis by simp
                qed
              qed
            qed
          qed
        qed        
      qed auto
    qed
  }
  from this[OF le_refl] A
  show ?thesis unfolding id jordan_matrix_def by auto
qed

lemma triangular_to_jnf_vector: assumes A: "(A :: 'a mat) \<in> carrier\<^sub>m n n"
  and ut: "upper_triangular A"
  shows "jordan_nf A (triangular_to_jnf_vector A)"
proof -
  let ?B = "triangular_to_jnf A"
  let ?n_as = "jnf_vector ?B"  
  have id: "triangular_to_jnf_vector A = ?n_as" unfolding triangular_to_jnf_vector_def by auto
  show ?thesis unfolding id jordan_nf_def
  proof (rule mat_similar_sym, subst jnf_vector[OF _ triangular_to_jnf_inv[OF A ut]])
    show "mat_similar ?B A" by (rule triangular_to_jnf_similar[OF A])
    show "triangular_to_jnf A \<in> carrier\<^sub>m n n" using A unfolding mat_carrier_def by auto
  qed
qed
end

(* main theorems *)
thm 
  triangular_to_jnf_similar
  triangular_to_jnf_inv
  triangular_to_jnf_vector
  jnf_vector

export_code triangular_to_jnf_vector checking

(* hide auxiliary definitions and functions *)
hide_const 
  lookup_ev
  find_largest_block
  swap_cols_rows_block
  identify_block_main
  identify_block
  identify_blocks_main
  identify_blocks
  step_1_main 
  step_1 
  step_2_main
  step_2 
  step_3_a
  step_3_c
  step_3_c_inner_loop
  step_3 
  jnf_vector_main

subsection \<open>Application for Complexity\<close>

text \<open>If we have an upper triangular matrix $A$ where the entries on the diagonal
  do not exceed 1, then the growth rate of $A^k$ can be restricted by ${\cal O}(k^{N-1})$
  where $N$ is the maximal multiplicity of an Eigenvalue with norm 1.\<close>
lemma counting_ones_complexity: (* approximation, but does not involve JNF computation *)
  fixes A :: "'a :: real_normed_field mat"
  assumes A: "A \<in> carrier\<^sub>m n n"
  and upper_t: "upper_triangular A"
  and le_1: "\<And> a. a \<in> set (mat_diag A) \<Longrightarrow> norm a \<le> 1"
  and le_N: "\<And> a. a \<in> set (mat_diag A) \<Longrightarrow> norm a = 1 \<Longrightarrow> length (filter (op = a) (mat_diag A)) \<le> N"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (N - 1))"
proof -
  from triangular_to_jnf_vector[OF A upper_t] have jnf: "\<exists> n_as. jordan_nf A n_as" ..
  show ?thesis
    by (rule factored_char_poly_norm_bound[OF A char_poly_upper_triangular[OF A upper_t] jnf le_1 le_N])
qed

text \<open>If we have an upper triangular matrix $A$ then we can compute a JNF-vector of it.
  If this vector does not contain entries $(n,ev)$ with $ev$ being larger 1,
  then the growth rate of $A^k$ can be restricted by ${\cal O}(k^{N-1})$ 
  where $N$ is the maximal value for $n$, where $(n,|ev| = 1)$ occurs in the vector, i.e.,
  the size of the largest Jordan Block with Eigenvalue of norm 1.\<close>
lemma compute_jnf_complexity: (* exact, requires JNF computation *)
  assumes A: "A \<in> carrier\<^sub>m n n"
  and upper_t: "upper_triangular (A :: 'a :: real_normed_field mat)"
  and le_1: "\<And> n a. (n,a) \<in> set (triangular_to_jnf_vector A) \<Longrightarrow> norm a \<le> 1"
  and le_N: "\<And> n a. (n,a) \<in> set (triangular_to_jnf_vector A) \<Longrightarrow> norm a = 1 \<Longrightarrow> n \<le> N"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (N - 1))"
proof -
  let ?jnf = "triangular_to_jnf_vector A"
  from triangular_to_jnf_vector[OF A upper_t] have jnf: "jordan_nf A ?jnf" .
  show ?thesis
    by (rule jordan_nf_matrix_poly_bound[OF A le_1 le_N jnf])
qed

end
