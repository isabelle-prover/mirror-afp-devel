(* -----------------------------------------------------------------------------------------------
-- Quantum Fourier Transform

-- Author: Pablo Manrique Merchán < pabmanmer at alum.us.es >
-- Universidad de Sevilla
-- -----------------------------------------------------------------------------------------------*)

theory QFT

imports
  Isabelle_Marries_Dirac.Deutsch
begin

section \<open>Some useful lemmas\<close>

lemma gate_carrier_mat[simp]:
  assumes "gate n U"
  shows "U \<in> carrier_mat (2^n) (2^n)"
proof
  show "dim_row U = 2^n" using gate_def assms by auto
next
  show "dim_col U = 2^n" using gate_def assms by auto
qed

lemma state_carrier_mat[simp]:
  assumes "state n \<psi>"
  shows "\<psi> \<in> carrier_mat (2^n) 1"
proof
  show "dim_row \<psi> = 2^n" using state_def assms by auto
next
  show "dim_col \<psi> = 1" using state_def assms by auto
qed

lemma state_basis_carrier_mat[simp]:
  "|state_basis n j\<rangle> \<in> carrier_mat (2^n) 1"
  by (simp add: ket_vec_def state_basis_def)

lemma left_tensor_id[simp]:
  assumes "A \<in> carrier_mat nr nc"
  shows "(1\<^sub>m 1) \<Otimes> A = A"
  by auto

lemma right_tensor_id[simp]:
  assumes "A \<in> carrier_mat nr nc"
  shows "A \<Otimes> (1\<^sub>m 1) = A"
  by auto

lemma tensor_carrier_mat[simp]:
  assumes "A \<in> carrier_mat ra ca"
    and "B \<in> carrier_mat rb cb"
  shows "A \<Otimes> B \<in> carrier_mat (ra*rb) (ca*cb)"
proof
  show "dim_row (A \<Otimes> B) = ra * rb" using dim_row_tensor_mat assms by auto
  show "dim_col (A \<Otimes> B) = ca * cb" using dim_col_tensor_mat assms by auto
qed

lemma smult_tensor[simp]:
  assumes "dim_col A > 0" and "dim_col B > 0"
  shows "(a \<cdot>\<^sub>m A) \<Otimes> (b \<cdot>\<^sub>m B) = (a*b) \<cdot>\<^sub>m (A \<Otimes> B)"
proof
  fix i j::nat
  assume ai:"i < dim_row (a * b \<cdot>\<^sub>m (A \<Otimes> B))" and aj:"j < dim_col (a * b \<cdot>\<^sub>m (A \<Otimes> B))"
  show "(a \<cdot>\<^sub>m A \<Otimes> b \<cdot>\<^sub>m B) $$ (i, j) = ((a * b) \<cdot>\<^sub>m (A \<Otimes> B)) $$ (i, j)"
  proof -
    define rA cA rB cB where "rA = dim_row A" and "cA = dim_col A" and "rB = dim_row B" 
      and "cB = dim_col B"
    have "(a \<cdot>\<^sub>m A \<Otimes> b \<cdot>\<^sub>m B)$$(i, j) = (a \<cdot>\<^sub>m A)$$(i div rB, j div cB)*(b \<cdot>\<^sub>m B)$$(i mod rB, j mod cB)"
    proof (rule index_tensor_mat)
      show "dim_row (a \<cdot>\<^sub>m A) = rA" using rA_def by simp
      show "dim_col (a \<cdot>\<^sub>m A) = cA" using cA_def by simp
      show "dim_row (b \<cdot>\<^sub>m B) = rB" using rB_def by simp
      show "dim_col (b \<cdot>\<^sub>m B) = cB" using cB_def by simp
      show "i < rA * rB" using ai rA_def rB_def smult_carrier_mat tensor_carrier_mat by auto
      show "j < cA * cB" using aj cA_def cB_def smult_carrier_mat tensor_carrier_mat by auto
      show "0 < cA" using cA_def assms(1) by simp
      show "0 < cB" using cB_def assms(2) by simp
    qed
    also have "\<dots> = a*A$$(i div rB, j div cB)*b*B$$(i mod rB, j mod cB)"
      using index_smult_mat by (smt (verit) Euclidean_Rings.div_eq_0_iff 
          ab_semigroup_mult_class.mult_ac(1) ai aj cB_def dim_col_tensor_mat dim_row_tensor_mat 
          less_mult_imp_div_less mod_less_divisor mult_0_right not_gr0 rB_def)
    also have "\<dots> = (a*b)*(A$$(i div rB, j div cB)*B$$(i mod rB, j mod cB))" by auto
    also have "\<dots> = (a*b)*((A \<Otimes> B) $$ (i,j))"
    proof -
      have "(A \<Otimes> B) $$ (i,j) = A$$(i div rB, j div cB)*B$$(i mod rB, j mod cB)"
        using index_tensor_mat rA_def cA_def rB_def cB_def ai aj smult_carrier_mat 
          tensor_carrier_mat assms by auto
      thus ?thesis by simp
    qed
    also have "\<dots> = ((a*b) \<cdot>\<^sub>m (A \<Otimes> B)) $$ (i,j)" using index_smult_mat(1)
      by (metis ai aj index_smult_mat(2) index_smult_mat(3))
    finally show ?thesis by this
  qed
next
  show "dim_row (a \<cdot>\<^sub>m A \<Otimes> b \<cdot>\<^sub>m B) = dim_row (a * b \<cdot>\<^sub>m (A \<Otimes> B))" by simp
next
  show "dim_col (a \<cdot>\<^sub>m A \<Otimes> b \<cdot>\<^sub>m B) = dim_col (a * b \<cdot>\<^sub>m (A \<Otimes> B))" by simp
qed

lemma smult_tensor1[simp]:
  assumes "dim_col A > 0" and "dim_col B > 0"
  shows "a \<cdot>\<^sub>m (A \<Otimes> B) = (a \<cdot>\<^sub>m A) \<Otimes> B"
proof -
  have "a \<cdot>\<^sub>m (A \<Otimes> B) = (a*1) \<cdot>\<^sub>m (A \<Otimes> B)" by auto
  also have "\<dots> = (a \<cdot>\<^sub>m A) \<Otimes> (1 \<cdot>\<^sub>m B)" using assms smult_tensor by simp
  also have "\<dots> = (a \<cdot>\<^sub>m A) \<Otimes> B" 
    by (metis eq_matI index_smult_mat(1) index_smult_mat(2) index_smult_mat(3) mult_cancel_right1)
  finally show ?thesis by this
qed

lemma set_list:
  "set [m..<n] = {m..<n}"
  by auto

lemma sumof2:
  "(\<Sum>k<(2::nat). f k) = f 0 + f 1"
  by (metis One_nat_def Suc_1 add.left_neutral lessThan_0 sum.empty sum.lessThan_Suc)

lemma sumof4:
  "(\<Sum>k<(4::nat). f k) = f 0 + f 1 + f 2 + f 3"
proof -
  have "(\<Sum>k<(4::nat). f k) = sum f (set [0..<4])" using set_list atLeast_upt by presburger
  also have "\<dots> = f 0 + (f (Suc 0) + (f 2 + f 3))" by simp
  also have "\<dots> = f 0 + f 1 + f 2 + f 3" by (simp add: add.commute add.left_commute)
  finally show ?thesis by this
qed



section \<open>The operator $R_k$\<close>

definition R:: "nat \<Rightarrow> complex Matrix.mat" where
  "R k = mat_of_cols_list 2 [[1, 0],
                            [0, exp(2*pi*\<i>/2^k)]]"


section \<open>The SWAP gate:\<close>

definition SWAP:: "complex Matrix.mat" where
  "SWAP \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else
                                  if i=1 \<and> j=2 then 1 else
                                  if i=2 \<and> j=1 then 1 else
                                  if i=3 \<and> j=3 then 1 else 0)"

lemma SWAP_index:
  "SWAP $$ (0,0) = 1 \<and>
   SWAP $$ (0,1) = 0 \<and>
   SWAP $$ (0,2) = 0 \<and>
   SWAP $$ (0,3) = 0 \<and>
   SWAP $$ (1,0) = 0 \<and>
   SWAP $$ (1,1) = 0 \<and>
   SWAP $$ (1,2) = 1 \<and>
   SWAP $$ (1,3) = 0 \<and>
   SWAP $$ (2,0) = 0 \<and>
   SWAP $$ (2,1) = 1 \<and>
   SWAP $$ (2,2) = 0 \<and>
   SWAP $$ (2,3) = 0 \<and>
   SWAP $$ (3,0) = 0 \<and>
   SWAP $$ (3,1) = 0 \<and>
   SWAP $$ (3,2) = 0 \<and>
   SWAP $$ (3,3) = 1"
  by (simp add: SWAP_def)

lemma SWAP_nrows:
  "dim_row SWAP = 4"
  by (simp add: SWAP_def)

lemma SWAP_ncols:
  "dim_col SWAP = 4"
  by (simp add: SWAP_def)

lemma SWAP_carrier_mat[simp]:
  "SWAP \<in> carrier_mat 4 4"
  using SWAP_nrows SWAP_ncols by auto


text \<open>The SWAP gate indeed swaps the states of two qubits (it is not necessary to assume unitarity)\<close>

lemma SWAP_tensor:
  assumes "u \<in> carrier_mat 2 1"
    and "v \<in> carrier_mat 2 1"
  shows "SWAP * (u \<Otimes> v) = v \<Otimes> u"
proof
  show "dim_row (SWAP * (u \<Otimes> v)) = dim_row (v \<Otimes> u)"
    using SWAP_nrows assms(1) assms(2) by auto
next
  show "dim_col (SWAP * (u \<Otimes> v)) = dim_col (v \<Otimes> u)"
    using SWAP_ncols assms by auto
next
  fix i j::nat assume "i < dim_row (v \<Otimes> u)" and "j < dim_col (v \<Otimes> u)"
  hence a3:"i < 4" and a4:"j = 0" using assms by auto
  thus "(SWAP * (u \<Otimes> v)) $$ (i, j) = (v \<Otimes> u) $$ (i, j)"
  proof -
    define u0 where "u0 = u $$ (0,0)"
    define u1 where "u1 = u $$ (1,0)"
    define v0 where "v0 = v $$ (0,0)"
    define v1 where "v1 = v $$ (1,0)"
    have vu0:"(v \<Otimes> u) $$ (0,0) = v0*u0" using index_tensor_mat assms u0_def v0_def by auto
    have vu1:"(v \<Otimes> u) $$ (1,0) = v0*u1" using index_tensor_mat assms u1_def v0_def by auto
    have vu2:"(v \<Otimes> u) $$ (2,0) = v1*u0" using index_tensor_mat assms u0_def v1_def by auto
    have vu3:"(v \<Otimes> u) $$ (3,0) = v1*u1" using index_tensor_mat assms u1_def v1_def by auto
    have uv0:"(u \<Otimes> v) $$ (0,0) = u0*v0" using index_tensor_mat assms u0_def v0_def by auto
    have uv1:"(u \<Otimes> v) $$ (1,0) = u0*v1" using index_tensor_mat assms u0_def v1_def by auto
    have uv2:"(u \<Otimes> v) $$ (2,0) = u1*v0" using index_tensor_mat assms u1_def v0_def by auto
    have uv3:"(u \<Otimes> v) $$ (3,0) = u1*v1" using index_tensor_mat assms u1_def v1_def by auto

    have uvi:"Matrix.vec 4 (\<lambda> i. (u \<Otimes> v) $$ (i,0)) $ i = (u \<Otimes> v) $$ (i,0)"
      using a3 index_vec by blast
    have sw:"\<forall>k<4. Matrix.vec 4 (\<lambda> j. SWAP $$ (i,j)) $ k = SWAP $$ (i,k)"
      using a3 index_vec by auto 

    have s0:"(SWAP * (u \<Otimes> v)) $$ (i,0) = Matrix.vec (dim_col SWAP) (\<lambda> j. SWAP $$ (i,j)) \<bullet> 
              Matrix.vec (dim_row (u \<Otimes> v)) (\<lambda> i. (u \<Otimes> v) $$ (i,0))"
      by (metis Matrix.col_def Matrix.row_def SWAP_nrows \<open>i < 4\<close> \<open>j < dim_col (v \<Otimes> u)\<close> \<open>j = 0\<close> 
          dim_col_tensor_mat index_mult_mat(1) mult.commute)
    also have "\<dots> = Matrix.vec 4 (\<lambda> j. SWAP $$ (i,j)) \<bullet> Matrix.vec 4 (\<lambda> i. (u \<Otimes> v) $$ (i,0))"
      using SWAP_ncols assms(1) assms(2) by fastforce
    also have "\<dots> =  (\<Sum>k<4. ((Matrix.vec 4 (\<lambda> j. SWAP $$ (i,j))) $ k) * 
                              ((Matrix.vec 4 (\<lambda> i. (u \<Otimes> v) $$ (i,0))) $ k))"
      using scalar_prod_def by (metis calculation dim_vec lessThan_atLeast0)
    also have "\<dots> = SWAP $$ (i,0) * (u \<Otimes> v) $$ (0,0) +
                    SWAP $$ (i,1) * (u \<Otimes> v) $$ (1,0) +
                    SWAP $$ (i,2) * (u \<Otimes> v) $$ (2,0) +
                    SWAP $$ (i,3) * (u \<Otimes> v) $$ (3,0)"
      using sumof4 by auto
    also have "\<dots> = SWAP $$ (i,0) * u0 * v0 +
                    SWAP $$ (i,1) * u0 * v1 +
                    SWAP $$ (i,2) * u1 * v0 +
                    SWAP $$ (i,3) * u1 * v1"
      using uv0 uv1 uv2 uv3 by simp
    also have "\<dots> = (v \<Otimes> u) $$ (i,j)"
    proof (rule disjE)
      show "i=0 \<or> i=1 \<or> i=2 \<or> i=3" using a3 by auto
    next
      assume i0:"i=0"
      hence "SWAP $$ (i,0) * u0 * v0 +
             SWAP $$ (i,1) * u0 * v1 +
             SWAP $$ (i,2) * u1 * v0 +
             SWAP $$ (i,3) * u1 * v1 =
             SWAP $$ (0,0) * u0 * v0 +
             SWAP $$ (0,1) * u0 * v1 +
             SWAP $$ (0,2) * u1 * v0 +
             SWAP $$ (0,3) * u1 * v1" by simp
      also have "\<dots> = (v \<Otimes> u) $$ (i, j)" using i0 vu0 SWAP_index a4 by simp
      finally show ?thesis by this
    next
      assume disj3:"i = 1 \<or> i = 2 \<or> i = 3"
      show ?thesis
      proof (rule disjE)
        show "i = 1 \<or> i = 2 \<or> i = 3" using disj3 by this
      next
        assume i1:"i=1"
        hence "SWAP $$ (i,0) * u0 * v0 +
               SWAP $$ (i,1) * u0 * v1 +
               SWAP $$ (i,2) * u1 * v0 +
               SWAP $$ (i,3) * u1 * v1 =
               SWAP $$ (1,0) * u0 * v0 +
               SWAP $$ (1,1) * u0 * v1 +
               SWAP $$ (1,2) * u1 * v0 +
               SWAP $$ (1,3) * u1 * v1" by simp
        also have "\<dots> = (v \<Otimes> u) $$ (i, j)" using i1 vu1 SWAP_index a4 by simp
        finally show ?thesis by this
      next
        assume disj2:"i = 2 \<or> i = 3"
        show ?thesis
        proof (rule disjE)
          show "i = 2 \<or> i = 3" using disj2 by this
        next
          assume i2:"i=2"
          hence "SWAP $$ (i,0) * u0 * v0 +
                 SWAP $$ (i,1) * u0 * v1 +
                 SWAP $$ (i,2) * u1 * v0 +
                 SWAP $$ (i,3) * u1 * v1 =
                 SWAP $$ (2,0) * u0 * v0 +
                 SWAP $$ (2,1) * u0 * v1 +
                 SWAP $$ (2,2) * u1 * v0 +
                 SWAP $$ (2,3) * u1 * v1" by simp
          also have "\<dots> = (v \<Otimes> u) $$ (i, j)" using i2 vu2 SWAP_index a4 by simp
          finally show ?thesis by this
        next
          assume i3:"i=3"
          hence "SWAP $$ (i,0) * u0 * v0 +
               SWAP $$ (i,1) * u0 * v1 +
               SWAP $$ (i,2) * u1 * v0 +
               SWAP $$ (i,3) * u1 * v1 =
               SWAP $$ (3,0) * u0 * v0 +
               SWAP $$ (3,1) * u0 * v1 +
               SWAP $$ (3,2) * u1 * v0 +
               SWAP $$ (3,3) * u1 * v1" by simp
          also have "\<dots> = (v \<Otimes> u) $$ (i, j)" using i3 vu3 SWAP_index a4 by simp
          finally show ?thesis by this
        qed
      qed
    qed
    finally show ?thesis using a4 by simp
  qed
qed

subsection \<open>Downwards SWAP cascade\<close>

fun SWAP_down:: "nat \<Rightarrow> complex Matrix.mat" where
  "SWAP_down 0 = 1\<^sub>m 1"
| "SWAP_down (Suc 0) = 1\<^sub>m 2"
| "SWAP_down (Suc (Suc 0)) = SWAP"
| "SWAP_down (Suc (Suc n)) = ((1\<^sub>m (2^n)) \<Otimes> SWAP) * ((SWAP_down (Suc n)) \<Otimes> (1\<^sub>m 2))"

lemma SWAP_down_carrier_mat[simp]:
  shows "SWAP_down n \<in> carrier_mat (2^n) (2^n)" (is "?P n")
proof (induct n rule: SWAP_down.induct)
  show "?P 0" by auto
next
  show "?P (Suc 0)" by auto
next
  show "?P (Suc (Suc 0))" using SWAP_carrier_mat by auto
next
  fix n::nat
  define k::nat where "k = Suc n"
  assume HI:"SWAP_down (Suc k) \<in> carrier_mat (2^(Suc k)) (2^(Suc k))"
  show "?P (Suc (Suc k))"
  proof
    have "dim_row (SWAP_down (Suc (Suc k))) = 
          dim_row (((1\<^sub>m (2^k)) \<Otimes> SWAP) * ((SWAP_down (Suc k)) \<Otimes> (1\<^sub>m 2)))"
      using SWAP_down.simps(4) k_def by simp
    also have "\<dots> = dim_row (((1\<^sub>m (2^k)) \<Otimes> SWAP))" by simp
    also have "\<dots> = (dim_row ((1\<^sub>m (2^k)))) * (dim_row SWAP)" by simp
    thus "dim_row (SWAP_down (Suc (Suc k))) = 2 ^ Suc (Suc k)" using SWAP_nrows index_one_mat
      by (simp add: calculation)
  next
    have "dim_col (SWAP_down (Suc (Suc k))) =
          dim_col (((1\<^sub>m (2^k)) \<Otimes> SWAP) * ((SWAP_down (Suc k)) \<Otimes> (1\<^sub>m 2)))"
      using SWAP_down.simps(4) k_def by simp
    also have "\<dots> = dim_col ((SWAP_down (Suc k)) \<Otimes> (1\<^sub>m 2))" by simp
    also have "\<dots> = dim_col (SWAP_down (Suc k)) * dim_col (1\<^sub>m 2)" by simp
    thus "dim_col (SWAP_down (Suc (Suc k))) = 2 ^ Suc (Suc k)"
      using SWAP_ncols index_one_mat calculation HI by simp
  qed
qed


subsection \<open>Upwards SWAP cascade\<close>

fun SWAP_up:: "nat \<Rightarrow> complex Matrix.mat" where
  "SWAP_up 0 = 1\<^sub>m 1"
| "SWAP_up (Suc 0) = 1\<^sub>m 2"
| "SWAP_up (Suc (Suc 0)) = SWAP"
| "SWAP_up (Suc (Suc n)) = (SWAP \<Otimes> (1\<^sub>m (2^n))) * ((1\<^sub>m 2) \<Otimes> (SWAP_up (Suc n)))"

lemma SWAP_up_carrier_mat[simp]:
  shows "SWAP_up n \<in> carrier_mat (2^n) (2^n)" (is "?P n")
proof (induct n rule: SWAP_up.induct)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case by auto
next
  case 3
  then show ?case by auto
next
  case (4 v)
  then show ?case using SWAP_nrows by fastforce
qed


section \<open>Reversing qubits\<close>

text \<open>In order to reverse the order of n qubits, we iteratively swap opposite qubits (swap 0th
and (n-1)th qubits, 1st and (n-2)th qubits, and so on).\<close>

fun reverse_qubits:: "nat \<Rightarrow> complex Matrix.mat" where
  "reverse_qubits 0 = 1\<^sub>m 1"
| "reverse_qubits (Suc 0) = (1\<^sub>m 2)"
| "reverse_qubits (Suc (Suc 0)) = SWAP"
| "reverse_qubits (Suc n) = ((reverse_qubits n) \<Otimes> (1\<^sub>m 2)) * (SWAP_down (Suc n))"


lemma reverse_qubits_carrier_mat[simp]:
  "(reverse_qubits n) \<in> carrier_mat (2^n) (2^n)"
proof (induct n rule: reverse_qubits.induct)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case by auto
next
  case 3
  then show ?case by auto
next
  case (4 va)
  then show ?case
    by (metis SWAP_down_carrier_mat carrier_matD(1) carrier_matD(2) carrier_matI dim_row_tensor_mat
        index_mult_mat(2) index_mult_mat(3) index_one_mat(2) power_Suc2 reverse_qubits.simps(4))
qed



section \<open>Controlled operations\<close>

text \<open>The two-qubit gate control2 performs a controlled U operation on the first qubit with the 
second qubit as control\<close>

definition control2:: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "control2 U \<equiv> mat_of_cols_list 4 [[1, 0, 0, 0],
                                    [0, U$$(0,0), 0, U$$(1,0)],
                                    [0, 0, 1, 0],
                                    [0, U$$(0,1), 0, U$$(1,1)]]"

lemma control2_carrier_mat[simp]:
  shows "control2 U \<in> carrier_mat 4 4"
  by (simp add: Tensor.mat_of_cols_list_def control2_def numeral_Bit0)


lemma control2_zero:
  assumes "dim_row v = 2" and "dim_col v = 1"
  shows "control2 U * (v \<Otimes> |zero\<rangle>) = v \<Otimes> |zero\<rangle>"
proof 
  fix i j::nat
  assume "i < dim_row (v \<Otimes> |zero\<rangle>)"
  hence i4:"i < 4" using assms tensor_carrier_mat ket_vec_def by auto
  assume "j < dim_col (v \<Otimes> |zero\<rangle>)"
  hence j0:"j = 0" using assms tensor_carrier_mat ket_vec_def by auto
  show "(control2 U * (v \<Otimes> |zero\<rangle>)) $$ (i,j) = (v \<Otimes> |zero\<rangle>) $$ (i,j)"
  proof -
    have "(control2 U * (v \<Otimes> |zero\<rangle>)) $$ (i,j) = 
          (\<Sum>k<dim_row (v \<Otimes> |zero\<rangle>). control2 U $$ (i, k) * (v \<Otimes> |zero\<rangle>) $$ (k, j))"
      using assms index_matrix_prod 
      by (smt (z3) One_nat_def Suc_1 Tensor.mat_of_cols_list_def \<open>i < dim_row (v \<Otimes> |Deutsch.zero\<rangle>)\<close>
          \<open>j < dim_col (v \<Otimes> |Deutsch.zero\<rangle>)\<close> add.commute add_Suc_right control2_def dim_col_mat(1)
          dim_row_mat(1) dim_row_tensor_mat ket_zero_to_mat_of_cols_list list.size(3) list.size(4) 
          mult_2 numeral_Bit0 plus_1_eq_Suc sum.cong)
    also have "\<dots> = (\<Sum>k<4. control2 U $$ (i, k) * (v \<Otimes> |zero\<rangle>) $$ (k, j))"
      using assms tensor_carrier_mat ket_vec_def by auto
    also have "\<dots> = control2 U $$ (i, 0) * (v \<Otimes> |zero\<rangle>) $$ (0, 0) +
                    control2 U $$ (i, 1) * (v \<Otimes> |zero\<rangle>) $$ (1, 0) +
                    control2 U $$ (i, 2) * (v \<Otimes> |zero\<rangle>) $$ (2, 0) +
                    control2 U $$ (i, 3) * (v \<Otimes> |zero\<rangle>) $$ (3, 0)"
      using sumof4 j0 by blast
    also have "\<dots> = (v \<Otimes> |zero\<rangle>) $$ (i,0)"
    proof (rule disjE)
      show "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" using i4 by auto
    next
      assume i0:"i = 0"
      have c00:"control2 U $$ (0,0) = 1"
        by (simp add: control2_def one_complex.code)
      have c01:"control2 U $$ (0,1) = 0"
        by (simp add: control2_def zero_complex.code)
      have c02:"control2 U $$ (0,2) = 0"
        by (simp add: control2_def zero_complex.code)
      have c03:"control2 U $$ (0,3) = 0"
        by (simp add: control2_def zero_complex.code)
      have "control2 U $$ (0, 0) * (v \<Otimes> |zero\<rangle>) $$ (0, 0) +
             control2 U $$ (0, 1) * (v \<Otimes> |zero\<rangle>) $$ (1, 0) +
             control2 U $$ (0, 2) * (v \<Otimes> |zero\<rangle>) $$ (2, 0) +
             control2 U $$ (0, 3) * (v \<Otimes> |zero\<rangle>) $$ (3, 0) =
             1 * (v \<Otimes> |zero\<rangle>) $$ (0, 0) +
             0 * (v \<Otimes> |zero\<rangle>) $$ (1, 0) +
             0 * (v \<Otimes> |zero\<rangle>) $$ (2, 0) +
             0 * (v \<Otimes> |zero\<rangle>) $$ (3, 0)"
        using c00 c01 c02 c03 by simp
      also have "\<dots> = (v \<Otimes> |zero\<rangle>) $$ (0, 0)" by auto
      finally show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (0, 0) +
                    control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (1, 0) +
                    control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (2, 0) +
                    control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (3, 0) =
                    (v \<Otimes> |Deutsch.zero\<rangle>) $$ (i, 0)"
        using i0 by simp
    next
      assume id:"i = 1 \<or> i = 2 \<or> i = 3"
      show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (0, 0) +
            control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (1, 0) +
            control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (2, 0) +
            control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (3, 0) =
            (v \<Otimes> |Deutsch.zero\<rangle>) $$ (i, 0)"
      proof (rule disjE)
        show "i = 1 \<or> i = 2 \<or> i = 3" using id by this
      next
        assume i1:"i = 1"
        have c10:"control2 U $$ (1,0) = 0"
          by (simp add: control2_def zero_complex.code)
        have t10:"(v \<Otimes> |zero\<rangle>) $$ (1,0) = 0"
          using index_tensor_mat ket_vec_def Tensor.mat_of_cols_list_def 
            \<open>i < dim_row (v \<Otimes> |Deutsch.zero\<rangle>)\<close> \<open>j < dim_col (v \<Otimes> |Deutsch.zero\<rangle>)\<close> i1 
          by fastforce
        have c12:"control2 U $$ (1,2) = 0"
          by (simp add: control2_def zero_complex.code)
        have t30:"(v \<Otimes> |zero\<rangle>) $$ (3,0) = 0"
        proof -
          have "(v \<Otimes> |zero\<rangle>) $$ (3,0) = v $$ (1,0) * |zero\<rangle> $$ (1,0)"
            using index_tensor_mat
            by (smt (verit) Euclidean_Rings.div_eq_0_iff H_on_ket_zero_is_state 
                H_without_scalar_prod One_nat_def Suc_1 \<open>j < dim_col (v \<Otimes> |Deutsch.zero\<rangle>)\<close> 
                add.commute assms(1) dim_col_tensor_mat dim_row_mat(1) index_mult_mat(2) j0 
                ket_zero_is_state mod_less mod_less_divisor mod_mult2_eq mult_2 nat_0_less_mult_iff 
                numeral_3_eq_3 plus_1_eq_Suc pos2 state.dim_row three_div_two three_mod_two)
          also have "\<dots> = 0" by auto
          finally show ?thesis by this
        qed
        show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (0, 0) +
              control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (1, 0) +
              control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (2, 0) +
              control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (3, 0) =
              (v \<Otimes> |Deutsch.zero\<rangle>) $$ (i, 0)"
          using i1 c10 t10 c12 t30 by auto
      next
        assume id2:"i = 2 \<or> i = 3"
        show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (0, 0) +
              control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (1, 0) +
              control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (2, 0) +
              control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (3, 0) =
              (v \<Otimes> |Deutsch.zero\<rangle>) $$ (i, 0)"
        proof (rule disjE)
          show "i = 2 \<or> i = 3"
            using id2 by this
        next
          assume i2:"i = 2"
          have c20:"control2 U $$ (2,0) = 0"
            by (simp add: control2_def zero_complex.code)
          have c21:"control2 U $$ (2,1) = 0"
            by (simp add: control2_def zero_complex.code)
          have c22:"control2 U $$ (2,2) = 1"
            by (simp add: control2_def one_complex.code)
          have c23:"control2 U $$ (2,3) = 0"
            by (simp add: control2_def zero_complex.code)
          show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (0, 0) +
                control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (1, 0) +
                control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (2, 0) +
                control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (3, 0) =
                (v \<Otimes> |Deutsch.zero\<rangle>) $$ (i, 0)"
            using i2 c20 c21 c22 c23 by auto
        next
          assume i3:"i = 3"
          have c30:"control2 U $$ (3,0) = 0"
            by (simp add: control2_def zero_complex.code)
          have t10:"(v \<Otimes> |zero\<rangle>) $$ (1,0) = 0"
            using index_tensor_mat ket_vec_def Tensor.mat_of_cols_list_def 
              \<open>i < dim_row (v \<Otimes> |Deutsch.zero\<rangle>)\<close> \<open>j < dim_col (v \<Otimes> |Deutsch.zero\<rangle>)\<close> i3
            by fastforce
          have c32:"control2 U $$ (3,2) = 0"
            by (simp add: control2_def zero_complex.code)
          have t30:"(v \<Otimes> |zero\<rangle>) $$ (3,0) = 0"
          proof -
            have "(v \<Otimes> |zero\<rangle>) $$ (3,0) = v $$ (1,0) * |zero\<rangle> $$ (1,0)"
              using index_tensor_mat
              by (smt (verit) Euclidean_Rings.div_eq_0_iff H_on_ket_zero_is_state 
                  H_without_scalar_prod One_nat_def Suc_1 \<open>j < dim_col (v \<Otimes> |Deutsch.zero\<rangle>)\<close> 
                  add.commute assms(1) dim_col_tensor_mat dim_row_mat(1) index_mult_mat(2) j0 
                  ket_zero_is_state mod_less mod_less_divisor mod_mult2_eq mult_2 nat_0_less_mult_iff 
                  numeral_3_eq_3 plus_1_eq_Suc pos2 state.dim_row three_div_two three_mod_two)
            also have "\<dots> = 0" by auto
            finally show ?thesis by this
          qed
          show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (0, 0) +
                control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (1, 0) +
                control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (2, 0) +
                control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.zero\<rangle>) $$ (3, 0) =
                (v \<Otimes> |Deutsch.zero\<rangle>) $$ (i, 0)"
            using i3 c30 t10 c32 t30 by auto
        qed
      qed
    qed
    finally show ?thesis using j0 by simp
  qed
next
  show "dim_row (control2 U * (v \<Otimes> |Deutsch.zero\<rangle>)) = dim_row (v \<Otimes> |Deutsch.zero\<rangle>)"
    by (metis assms(1) carrier_matD(1) control2_carrier_mat dim_row_mat(1) dim_row_tensor_mat 
        index_mult_mat(2) index_unit_vec(3) ket_vec_def num_double numeral_times_numeral)
next
  show "dim_col (control2 U * (v \<Otimes> |Deutsch.zero\<rangle>)) = dim_col (v \<Otimes> |Deutsch.zero\<rangle>)"
    using index_mult_mat(3) by blast
qed


lemma vtensorone_index[simp]:
  assumes "dim_row v = 2" and "dim_col v = 1"
  shows "(v \<Otimes> |one\<rangle>) $$ (0,0) = 0 \<and>
         (v \<Otimes> |one\<rangle>) $$ (1,0) = v $$ (0,0) \<and>
         (v \<Otimes> |one\<rangle>) $$ (2,0) = 0 \<and>
         (v \<Otimes> |one\<rangle>) $$ (3,0) = v $$ (1,0)"
  by (simp add: assms(1) assms(2) ket_vec_def)

lemma control2_one:
  assumes "dim_row v = 2" and "dim_col v = 1" and "dim_row U = 2" and "dim_col U = 2"
  shows "control2 U * (v \<Otimes> |one\<rangle>) = (U*v) \<Otimes> |one\<rangle>"
proof
  fix i j::nat
  assume "i < dim_row ((U*v) \<Otimes> |one\<rangle>)"
  hence il4:"i < 4" by (simp add: assms(3) ket_vec_def)
  assume "j < dim_col ((U*v) \<Otimes> |one\<rangle>)"
  hence j0:"j = 0" using assms ket_vec_def by simp
  show "(control2 U * (v \<Otimes> |Deutsch.one\<rangle>)) $$ (i, j) = (U * v \<Otimes> |Deutsch.one\<rangle>) $$ (i, j)"
  proof -
    have "(control2 U * (v \<Otimes> |one\<rangle>)) $$ (i,j) = 
          (\<Sum>k<dim_row (v \<Otimes> |one\<rangle>). (control2 U) $$ (i, k) * (v \<Otimes> |one\<rangle>) $$ (k, j))"
      using assms index_matrix_prod tensor_carrier_mat
    proof -
      have "\<And>m. dim_col (v \<Otimes> m) = dim_col m"
        by (simp add: assms(2))
      then have "i < dim_row (control2 U) \<and> 0 < dim_col (v \<Otimes> Matrix.mat 2 1 (\<lambda>(n, n). Deutsch.one $ n)) \<and> dim_row (v \<Otimes> Matrix.mat 2 1 (\<lambda>(n, n). Deutsch.one $ n)) = dim_col (control2 U)"
        by (smt (z3) assms(1) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_mat(1) dim_row_mat(1) dim_row_tensor_mat il4 mult_2 numeral_Bit0 zero_less_one_class.zero_less_one)
      then show ?thesis
        by (simp add: j0 ket_vec_def)
    qed
    also have "\<dots> = (\<Sum>k<4. control2 U $$ (i, k) * (v \<Otimes> |one\<rangle>) $$ (k, j))"
      using assms tensor_carrier_mat ket_vec_def by auto
    also have "\<dots> = control2 U $$ (i, 0) * (v \<Otimes> |one\<rangle>) $$ (0, 0) +
                    control2 U $$ (i, 1) * (v \<Otimes> |one\<rangle>) $$ (1, 0) +
                    control2 U $$ (i, 2) * (v \<Otimes> |one\<rangle>) $$ (2, 0) +
                    control2 U $$ (i, 3) * (v \<Otimes> |one\<rangle>) $$ (3, 0)"
      using sumof4 j0 by blast
    also have "\<dots> = ((U*v) \<Otimes> |one\<rangle>) $$ (i,0)"
    proof (rule disjE)
      show "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" using il4 by auto
    next
      assume i0:"i = 0"
      thus "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (0, 0) +
            control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (1, 0) +
            control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (2, 0) +
            control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (3, 0) =
            (U * v \<Otimes> |Deutsch.one\<rangle>) $$ (i, 0)"
        using j0 control2_def zero_complex.code one_complex.code vtensorone_index assms by auto
    next
      assume id3:"i = 1 \<or> i = 2 \<or> i = 3"
      show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (0, 0) +
            control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (1, 0) +
            control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (2, 0) +
            control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (3, 0) =
            (U * v \<Otimes> |Deutsch.one\<rangle>) $$ (i, 0)"
      proof (rule disjE)
        show "i = 1 \<or> i = 2 \<or> i = 3" using id3 by this
      next
        assume i1:"i = 1"
        thus "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (0, 0) +
            control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (1, 0) +
            control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (2, 0) +
            control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (3, 0) =
            (U * v \<Otimes> |Deutsch.one\<rangle>) $$ (i, 0)"
          using j0 control2_def zero_complex.code one_complex.code vtensorone_index assms
          by (simp add: sumof2)
      next
        assume il2:"i = 2 \<or> i = 3"
        show "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (0, 0) +
            control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (1, 0) +
            control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (2, 0) +
            control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (3, 0) =
            (U * v \<Otimes> |Deutsch.one\<rangle>) $$ (i, 0)"
        proof (rule disjE)
          show "i = 2 \<or> i = 3" using il2 by this
        next
          assume i2:"i = 2"
          thus "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (0, 0) +
                control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (1, 0) +
                control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (2, 0) +
                control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (3, 0) =
                (U * v \<Otimes> |Deutsch.one\<rangle>) $$ (i, 0)"
            using j0 control2_def zero_complex.code one_complex.code vtensorone_index assms by auto
        next
          assume i3:"i = 3"
          thus "control2 U $$ (i, 0) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (0, 0) +
                control2 U $$ (i, 1) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (1, 0) +
                control2 U $$ (i, 2) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (2, 0) +
                control2 U $$ (i, 3) * (v \<Otimes> |Deutsch.one\<rangle>) $$ (3, 0) =
                (U * v \<Otimes> |Deutsch.one\<rangle>) $$ (i, 0)"
            using j0 control2_def zero_complex.code one_complex.code vtensorone_index assms
            by (simp add: sumof2)
        qed
      qed
    qed
    finally show ?thesis using j0 by simp
  qed
next
  show "dim_row (control2 U * (v \<Otimes> |Deutsch.one\<rangle>)) = dim_row (U * v \<Otimes> |Deutsch.one\<rangle>)"
    by (metis assms(3) carrier_matD(1) control2_carrier_mat dim_row_mat(1) dim_row_tensor_mat 
        index_mult_mat(2) index_unit_vec(3) ket_vec_def mult_2_right numeral_Bit0)
next
  show "dim_col (control2 U * (v \<Otimes> |Deutsch.one\<rangle>)) = dim_col (U * v \<Otimes> |Deutsch.one\<rangle>)"
    by simp
qed


text \<open>Given a single qubit gate U, control n U creates a quantum n-qubit gate that performs
a controlled-U operation on the first qubit using the last qubit as control.\<close>

fun control:: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "control 0 U = 1\<^sub>m 1"
| "control (Suc 0) U = 1\<^sub>m 2"
| "control (Suc (Suc 0)) U = control2 U"
| "control (Suc (Suc n)) U = 
   ((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (control2 U \<Otimes> (1\<^sub>m (2^n))) * ((1\<^sub>m 2) \<Otimes> SWAP_up (Suc n))"

lemma control_carrier_mat[simp]:
  shows "control n U \<in> carrier_mat (2^n) (2^n)"
proof (cases n)
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then show ?thesis
    by (smt (verit, best) One_nat_def SWAP_down_carrier_mat SWAP_up.simps(2) SWAP_up.simps(4) 
        SWAP_up_carrier_mat Suc_1 Zero_not_Suc carrier_matD(1) carrier_matD(2) carrier_matI 
        control.elims control2_carrier_mat dim_col_tensor_mat dim_row_tensor_mat index_mult_mat(2)
        index_mult_mat(3) mult_2 numeral_Bit0 power2_eq_square)
qed



section \<open>Quantum Fourier Transform Circuit\<close>

subsection \<open>QFT definition\<close>

text \<open>The function kron is the generalization of the Kronecker product to a finite number of qubits\<close>

fun kron:: "(nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat list \<Rightarrow> complex Matrix.mat" where
  "kron f [] = 1\<^sub>m 1"
| "kron f (x#xs) = (f x) \<Otimes> (kron f xs)"


lemma kron_carrier_mat[simp]:
  assumes "\<forall>m. dim_row (f m) = 2 \<and> dim_col (f m) = 1" 
  shows "kron f xs \<in> carrier_mat (2^(length xs)) 1"
proof (induct xs)
  case Nil
  show ?case
  proof
    have "dim_row (kron f []) = dim_row (1\<^sub>m 1)" using kron.simps(1) by simp
    then show "dim_row (kron f []) = 2 ^ length []" by simp
  next
    have "dim_col (kron f []) = dim_col (1\<^sub>m 1)" using kron.simps(1) by simp
    then show "dim_col (kron f []) = 1" by simp
  qed
next
  case (Cons x xs)
  assume HI:"kron f xs \<in> carrier_mat (2 ^ length xs) 1"
  have "f x \<in> carrier_mat 2 1" using assms by auto
  moreover have "(f x) \<Otimes> (kron f xs) \<in> carrier_mat ((2 ^ length xs) * 2) 1"
    using tensor_carrier_mat HI calculation by auto
  moreover have "kron f (x#xs) \<in> carrier_mat (2 ^ (length (x#xs))) 1"
    using kron.simps(2) length_Cons by (metis calculation(2) power_Suc2)
  thus ?case by this
qed

lemma kron_cons_right:
  shows "kron f (xs@[x]) = kron f xs \<Otimes> f x"
proof (induct xs)
  case Nil
  have "kron f ([]@[x]) = kron f [x]" by simp
  also have "\<dots> = f x" using kron.simps by auto
  also have "\<dots> = kron f [] \<Otimes> f x" by auto
  finally show ?case by this
next
  case (Cons a xs)
  assume IH:"kron f (xs@[x]) = kron f xs \<Otimes> f x"
  have "kron f ((a#xs)@[x]) = f a \<Otimes> (kron f (xs@[x]))" using kron.simps by auto
  also have "\<dots> = f a \<Otimes> (kron f xs \<Otimes> f x)" using IH by simp
  also have "\<dots> = kron f (a#xs) \<Otimes> f x" using kron.simps tensor_mat_is_assoc by auto
  finally show ?case by this
qed


text \<open>We define the QFT product representation\<close>

definition QFT_product_representation:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "QFT_product_representation j n \<equiv> 1/(sqrt (2^n)) \<cdot>\<^sub>m 
                                    (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                                    (map nat [1..n]))"


text \<open>We also define the reverse version of the QFT product representation, which is the output
state of the QFT circuit alone\<close>

definition reverse_QFT_product_representation:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "reverse_QFT_product_representation j n \<equiv> 1/(sqrt (2^n)) \<cdot>\<^sub>m 
                                            (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                                            (map nat (rev [1..n])))"


subsection \<open>QFT circuit\<close>

text \<open>The recursive function controlled$\_$rotations computes the controlled-$R_k$ gates subcircuit
 of the QFT circuit at each stage (i.e. for each qubit).\<close>

fun controlled_rotations:: "nat \<Rightarrow> complex Matrix.mat" where
  "controlled_rotations 0 = 1\<^sub>m 1"
| "controlled_rotations (Suc 0) = 1\<^sub>m 2"
| "controlled_rotations (Suc n) = (control (Suc n) (R (Suc n))) *
                                  ((controlled_rotations n) \<Otimes> (1\<^sub>m 2))"


lemma controlled_rotations_carrier_mat[simp]:
  "controlled_rotations n \<in> carrier_mat (2^n) (2^n)"
proof (induct n rule: controlled_rotations.induct)
  case 1
  then show ?case by auto
next
  case 2 
  then show ?case by auto
next
  case 3
  then show ?case 
    by (smt (verit, del_insts) carrier_matD(1) carrier_matD(2) carrier_mat_triv control_carrier_mat
        controlled_rotations.simps(3) dim_col_tensor_mat index_mult_mat(2) index_mult_mat(3)
        index_one_mat(3) mult.commute power_Suc)
qed


text \<open>The recursive function QFT computes the Quantum Fourier Transform circuit.\<close>

fun QFT:: "nat \<Rightarrow> complex Matrix.mat" where
  "QFT 0 = 1\<^sub>m 1"
| "QFT (Suc 0) = H"
| "QFT (Suc n) =  ((1\<^sub>m 2) \<Otimes> (QFT n)) * (controlled_rotations (Suc n)) * (H \<Otimes> ((1\<^sub>m (2^n))))"


lemma QFT_carrier_mat[simp]:
  "QFT n \<in> carrier_mat (2^n) (2^n)"
proof (induct n rule: QFT.induct)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case
    using H_is_gate One_nat_def QFT.simps(2) gate_carrier_mat by presburger
next
  case 3
  then show ?case
    by (metis H_inv QFT.simps(3) carrier_matD(1) carrier_mat_triv dim_col_tensor_mat
        dim_row_tensor_mat index_mult_mat(2) index_mult_mat(3) index_one_mat(2) index_one_mat(3) 
        power.simps(2))
qed


text \<open>ordered$\_$QFT reverses the order of the qubits at the end of the QFT circuit\<close>

definition ordered_QFT:: "nat \<Rightarrow> complex Matrix.mat" where
  "ordered_QFT n \<equiv> (reverse_qubits n) * (QFT n)"



section \<open>QFT circuit correctness\<close>

text \<open>Some useful lemmas:\<close>

lemma state_basis_dec:
  assumes "j < 2 ^ Suc n"
  shows "|state_basis 1 (j div 2^n)\<rangle> \<Otimes> |state_basis n (j mod 2^n)\<rangle> = |state_basis (Suc n) j\<rangle>"
proof -
  define jd jm where "jd = j div 2^n" and "jm = j mod 2^n"
  hence jml:"jm < 2^n" by auto
  have j_dec:"j = jd*(2^n) + jm" using jd_def jm_def by presburger
  show ?thesis
  proof (rule disjE)
    show "jd = 0 \<or> jd = 1" using jd_def assms
      by (metis One_nat_def less_2_cases less_power_add_imp_div_less plus_1_eq_Suc power_one_right)
  next
    assume jd0:"jd = 0"
    hence jjm:"j = jm" using j_dec by auto
    show "|state_basis 1 (j div 2^n)\<rangle> \<Otimes> |state_basis n (j mod 2^n)\<rangle> = |state_basis (Suc n) j\<rangle>"
    proof
      fix i ja
      assume "i < dim_row ( |state_basis (Suc n) j\<rangle>)"
        and ja_dim:"ja < dim_col ( |state_basis (Suc n) j\<rangle>)"
      hence il:"i < 2^Suc n" using state_basis_carrier_mat ket_vec_def state_basis_def by simp
      have jal:"ja < 1" using ja_dim state_basis_carrier_mat state_basis_def ket_vec_def by simp
      hence ja0:"ja = 0" by auto
      show "( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) $$ (i, ja) =
              |state_basis (Suc n) j\<rangle> $$ (i, ja)"
      proof -
        have "( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) $$ (i, ja) =
              ( |state_basis 1 0\<rangle> \<Otimes> |state_basis n jm\<rangle>) $$ (i,0)"
          using jm_def jd0 ja0 jd_def by auto
        also have "\<dots> = |state_basis 1 0\<rangle> $$ 
                        (i div (dim_row |state_basis n jm\<rangle>), 0 div (dim_col |state_basis n jm\<rangle>)) *
                        |state_basis n jm\<rangle> $$ 
                        (i mod (dim_row |state_basis n jm\<rangle>), 0 mod (dim_col |state_basis n jm\<rangle>))"
        proof (rule index_tensor_mat)
          show "dim_row |state_basis 1 0\<rangle> = 2" 
            using state_basis_carrier_mat state_basis_def ket_vec_def by simp
          show "dim_col |state_basis 1 0\<rangle> = 1"
            using state_basis_carrier_mat state_basis_def ket_vec_def by simp
          show "dim_row |state_basis n jm\<rangle> = dim_row |state_basis n jm\<rangle>" by auto
          show "dim_col |state_basis n jm\<rangle> = dim_col |state_basis n jm\<rangle>" by auto
          show "i < 2 * dim_row |state_basis n jm\<rangle>" 
            using il state_basis_def state_basis_carrier_mat ket_vec_def by simp
          show "0 < 1 * dim_col |state_basis n jm\<rangle>"
            using state_basis_def state_basis_carrier_mat ket_vec_def by simp
          show "0 < (1::nat)" using zero_less_Suc One_nat_def by blast
          show "0 < dim_col |state_basis n jm\<rangle>"
            using state_basis_def state_basis_carrier_mat ket_vec_def by simp
        qed
        also have "\<dots> = |state_basis 1 0\<rangle> $$ (i div 2^n, 0) * |state_basis n jm\<rangle> $$ (i mod 2^n, 0)"
          using state_basis_def state_basis_carrier_mat ket_vec_def by auto
        also have "\<dots> = (mat_of_cols_list 2 [[1,0]]) $$ (i div 2^n, 0) * 
                        |state_basis n jm\<rangle> $$ (i mod 2^n, 0)"
          using state_basis_def unit_vec_def by auto
        also have "\<dots> = |state_basis (Suc n) j\<rangle> $$ (i,0)"
        proof -
          define id im where "id = i div 2^n" and "im = i mod 2^n"
          have i_dec:"i = id*(2^n) + im" using id_def im_def by presburger
          show ?thesis
          proof (rule disjE)
            show "id = 0 \<or> id = 1" using id_def by (metis One_nat_def il less_2_cases 
                  less_power_add_imp_div_less plus_1_eq_Suc power_one_right)
          next
            assume id0:"id = 0"
            hence iim:"i = im" using i_dec by presburger
            have "mat_of_cols_list 2 [[1,0]] $$ (i div 2^n,0) * |state_basis n jm\<rangle> $$ (i mod 2^n, 0)
                = mat_of_cols_list 2 [[1,0]] $$ (0,0) * |state_basis n jm\<rangle> $$ (im,0)"
              using id_def id0 im_def by simp
            also have "\<dots> = 1 * |state_basis n jm\<rangle> $$ (im,0)" using mat_of_cols_list_def by auto
            also have "\<dots> = |state_basis (Suc n) jm\<rangle> $$ (im,0)" using iim jjm state_basis_def
              by (smt (verit, best) il im_def index_unit_vec(3) index_vec ket_vec_index lambda_one 
                  mod_less_divisor pos2 unit_vec_def zero_less_power)
            also have "\<dots> = |state_basis (Suc n) j\<rangle> $$ (i,0)" using iim jjm by simp
            finally show ?thesis by this
          next
            assume id1:"id = 1"
            hence iid:"i = 2^n + im" using i_dec by simp
            have jma:"jm \<noteq> 2^n + im" using jml iid by auto
            have "mat_of_cols_list 2 [[1,0]] $$ (i div 2^n,0) * |state_basis n jm\<rangle> $$ (i mod 2^n,0)
                = mat_of_cols_list 2 [[1,0]] $$ (1,0) * |state_basis n jm\<rangle> $$ (im,0)"
              using id1 id_def im_def by simp
            also have "\<dots> = 0" using mat_of_cols_list_def by auto
            also have "\<dots> = |state_basis (Suc n) jm\<rangle> $$ (2^n + im,0)" 
            proof -
              have "|state_basis (Suc n) jm\<rangle> $$ (2^n + im,0) = 
                    |unit_vec (2^(Suc n)) jm\<rangle> $$ (2^n+im,0)"
                using state_basis_def by simp
              also have "\<dots> = Matrix.mat (2^(Suc n)) 1 (\<lambda>(i, j). (unit_vec (2^(Suc n)) jm) $ i)
                              $$ (2^n+im,0)"
                using ket_vec_def by simp
              also have "\<dots> = Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). Matrix.vec (2^(Suc n)) 
                              (\<lambda>j'. if j'=jm then 1 else 0) $ i) $$ (2^n+im,0)"
                using unit_vec_def by metis
              also have "\<dots> = 0" using iid il jma by fastforce
              finally show ?thesis by auto
            qed
            also have "\<dots> = |state_basis (Suc n) j\<rangle> $$ (i,0)" using jjm iid by simp
            finally show ?thesis by this
          qed
        qed
        finally show ?thesis using ja0 by auto
      qed
    next
      show "dim_row ( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) =
            dim_row |state_basis (Suc n) j\<rangle>" 
        using state_basis_def state_basis_carrier_mat ket_vec_def by auto
    next
      show "dim_col ( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) =
            dim_col |state_basis (Suc n) j\<rangle>"
        using state_basis_def state_basis_carrier_mat ket_vec_def by auto
    qed
  next
    assume jd1:"jd = 1"
    hence j_dec2:"j = 2^n + jm" using j_dec by auto
    show "|state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle> = |state_basis (Suc n) j\<rangle>"
    proof
      fix i ja
      assume "i < dim_row |state_basis (Suc n) j\<rangle>"
      hence il:"i < 2^(Suc n)" using state_basis_def state_basis_carrier_mat ket_vec_def by simp
      assume "ja < dim_col |state_basis (Suc n) j\<rangle>"
      hence jal:"ja < 1" using state_basis_def state_basis_carrier_mat ket_vec_def by simp
      hence ja0:"ja = 0" by auto
      show "( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) $$ (i, ja) =
              |state_basis (Suc n) j\<rangle> $$ (i, ja)"
      proof -
        have "( |state_basis 1 jd\<rangle> \<Otimes> |state_basis n jm\<rangle>) $$ (i, 0) =
              ( |state_basis 1 1\<rangle> \<Otimes> |state_basis n jm\<rangle>) $$ (i, 0)"
          using jd1 by simp
        also have "\<dots> = |state_basis 1 1\<rangle> $$ 
                        (i div (dim_row |state_basis n jm\<rangle>), 0 div (dim_col |state_basis n jm\<rangle>)) *
                        |state_basis n jm\<rangle> $$ 
                        (i mod (dim_row |state_basis n jm\<rangle>), 0 mod (dim_col |state_basis n jm\<rangle>))"
        proof (rule index_tensor_mat)
          show "dim_row |state_basis 1 1\<rangle> = 2" 
            using state_basis_carrier_mat state_basis_def ket_vec_def by simp
          show "dim_col |state_basis 1 1\<rangle> = 1"
            using state_basis_carrier_mat state_basis_def ket_vec_def by simp
          show "dim_row |state_basis n jm\<rangle> = dim_row |state_basis n jm\<rangle>" by auto
          show "dim_col |state_basis n jm\<rangle> = dim_col |state_basis n jm\<rangle>" by auto
          show "i < 2 * dim_row |state_basis n jm\<rangle>"
            using state_basis_carrier_mat state_basis_def ket_vec_def il by auto
          show "0 < 1 * dim_col |state_basis n jm\<rangle>"
            using state_basis_carrier_mat state_basis_def ket_vec_def by auto
          show "0 < (1::nat)" by simp
          show "0 < dim_col |state_basis n jm\<rangle>"
            using state_basis_carrier_mat state_basis_def ket_vec_def by auto
        qed
        also have "\<dots> = (mat_of_cols_list 2 [[0,1]]) $$ (i div 2^n,0) *
                        |state_basis n jm\<rangle> $$ (i mod 2^n,0)"
          using state_basis_carrier_mat state_basis_def ket_vec_def mat_of_cols_list_def 
            ket_one_to_mat_of_cols_list
          by auto
        also have "\<dots> = |state_basis (Suc n) j\<rangle> $$ (i,0)"
        proof -
          define id im where "id = i div 2^n" and "im = i mod 2^n"
          have i_dec:"i = id*(2^n) + im" using id_def im_def by presburger
          show ?thesis
          proof (rule disjE)
            show "id = 0 \<or> id = 1" using id_def il
              by (metis One_nat_def less_2_cases less_power_add_imp_div_less plus_1_eq_Suc 
                  power_one_right)
          next
            assume id0:"id = 0"
            hence iim:"i = im" using i_dec by presburger
            have "mat_of_cols_list 2 [[0,1]] $$ (i div 2^n,0) * |state_basis n jm\<rangle> $$ (i mod 2^n,0)
                = mat_of_cols_list 2 [[0,1]] $$ (0,0) * |state_basis n jm\<rangle> $$ (im,0)"
              using id0 id_def im_def by simp
            also have "\<dots> = 0" using mat_of_cols_list_def by auto
            also have "\<dots> = |state_basis (Suc n) j\<rangle> $$ (im,0)"
              using state_basis_def ket_vec_def j_dec2 assms id0 iim il local.id_def by force
            also have "\<dots> = |state_basis (Suc n) j\<rangle> $$ (i,0)" using iim by simp
            finally show ?thesis by this
          next
            assume id1:"id = 1"
            hence i2m:"i = 2^n + im" using i_dec by presburger
            have "mat_of_cols_list 2 [[0,1]] $$ (i div 2^n,0) * |state_basis n jm\<rangle> $$ (i mod 2^n,0)
                = mat_of_cols_list 2 [[0,1]] $$ (1,0) * |state_basis n jm\<rangle> $$ (im,0)"
              using id1 id_def im_def by simp
            also have "\<dots> = |state_basis n jm\<rangle> $$ (im,0)" using mat_of_cols_list_def by auto
            also have "\<dots> = |state_basis (Suc n) j\<rangle> $$ (i,0)"
              using i2m j_dec2 il assms state_basis_def by auto
            finally show ?thesis by this
          qed
        qed
        finally show "( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) $$ (i, ja) =
                      |state_basis (Suc n) j\<rangle> $$ (i, ja)" 
          using ja0 jd_def jm_def by auto
      qed
    next
      show "dim_row ( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) =
            dim_row |state_basis (Suc n) j\<rangle>"
        using state_basis_def state_basis_carrier_mat ket_vec_def by simp
    next
      show "dim_col ( |state_basis 1 (j div 2 ^ n)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ n)\<rangle>) =
            dim_col |state_basis (Suc n) j\<rangle>"
        using state_basis_def state_basis_carrier_mat ket_vec_def by simp
    qed
  qed
qed

lemma state_basis_dec':
  "\<forall>j. j < 2 ^ Suc n \<longrightarrow> 
    |state_basis n (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> = |state_basis (Suc n) j\<rangle>"
proof (induct n)
  case 0
  show ?case
  proof 
    fix j::nat
    show "j < 2 ^ Suc 0 \<longrightarrow>
         |state_basis 0 (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> = |state_basis (Suc 0) j\<rangle>"
    proof
      assume "j < 2 ^ Suc 0"
      hence j2:"j < 2" by auto
      hence jd0:"j div 2 = 0" by auto
      have jmj:"j mod 2 = j" using j2 by auto
      have "|state_basis 0 (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> =
            |state_basis 0 0\<rangle> \<Otimes> |state_basis 1 j\<rangle>"
        using jmj jd0 by simp
      also have "\<dots> = (1\<^sub>m 1) \<Otimes> |state_basis 1 j\<rangle>"
        using state_basis_def unit_vec_def ket_vec_def by auto
      also have "\<dots> = |state_basis 1 j\<rangle>" using left_tensor_id by blast
      finally show "|state_basis 0 (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> = |state_basis (Suc 0) j\<rangle>"
        by auto
    qed
  qed
next
  case (Suc n)
  assume HI:"\<forall>j<2 ^ Suc n. |state_basis n (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> =
                           |state_basis (Suc n) j\<rangle>"
  define m where "m = Suc n"
  show ?case
  proof 
    fix j::nat
    show "j < 2 ^ Suc (Suc n) \<longrightarrow>
       |state_basis (Suc n) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> = |state_basis (Suc (Suc n)) j\<rangle>"
    proof 
      assume jleq:"j < 2 ^ Suc (Suc n)"
      define jd2 where "jd2 = j div 2"
      define jm2 where "jm2 = j mod 2"
      define jd2m where "jd2m = j div 2^m"
      define jm2m where "jm2m = j mod 2^m"
      define jmm where "jmm = jd2 mod 2^n"
      have "|state_basis m jd2\<rangle> \<Otimes> |state_basis 1 jm2\<rangle> =
            ( |state_basis 1 jd2m\<rangle> \<Otimes> |state_basis n jmm\<rangle>) \<Otimes> |state_basis 1 jm2\<rangle>"
        using jleq state_basis_dec m_def jd2_def jm2_def jd2m_def jmm_def jm2_def
        by (metis Suc_eq_plus1 div_exp_eq less_power_add_imp_div_less plus_1_eq_Suc power_one_right)
      also have "\<dots> = |state_basis 1 jd2m\<rangle> \<Otimes> ( |state_basis n jmm\<rangle> \<Otimes> |state_basis 1 jm2\<rangle>)"
        using tensor_mat_is_assoc by presburger
      also have "\<dots> = |state_basis 1 jd2m\<rangle> \<Otimes> |state_basis m jm2m\<rangle>"
        using HI jm2m_def jmm_def jm2_def 
        by (metis Suc_eq_plus1 div_exp_mod_exp_eq jd2_def le_simps(2) less_add_same_cancel2 m_def 
            mod_less_divisor mod_mod_power_cancel plus_1_eq_Suc pos2 power_one_right zero_less_Suc 
            zero_less_power)
      also have "\<dots> = |state_basis (Suc m) j\<rangle>"
        using state_basis_dec m_def jleq jd2m_def jm2m_def by presburger
      finally show "|state_basis (Suc n) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> =
                    |state_basis (Suc (Suc n)) j\<rangle>"
        using jd2_def jm2_def m_def by simp
    qed
  qed
qed


text \<open>Action of the H gate in the circuit\<close>

lemma H_on_first_qubit:
  assumes "j < 2 ^ Suc n"
  shows "((H \<Otimes> ((1\<^sub>m (2^n))))) * |state_basis (Suc n) j\<rangle> = 
         1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat (j div 2^n))/2) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> 
         |state_basis n (j mod 2^n)\<rangle>"
proof -
  define jd jm where "jd = j div 2^n" and "jm = j mod 2^n"
  have "((H \<Otimes> ((1\<^sub>m (2^n))))) * |state_basis (Suc n) j\<rangle> = 
        ((H \<Otimes> ((1\<^sub>m (2^n))))) * ( |state_basis 1 jd\<rangle> \<Otimes> |state_basis n jm\<rangle>)"
    using jd_def jm_def state_basis_dec assms by simp
  also have "\<dots> = (H * |state_basis 1 jd\<rangle>) \<Otimes> ((1\<^sub>m (2^n)) * |state_basis n jm\<rangle>)"
    using H_def state_basis_carrier_mat state_basis_def ket_vec_def mult_distr_tensor 
    by (metis (no_types, lifting) H_without_scalar_prod carrier_matD(1) dim_col_mat(1) 
        index_one_mat(3) pos2 power_one_right zero_less_one_class.zero_less_one zero_less_power)
  also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat jd)/2) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> 
                  |state_basis n jm\<rangle>"
  proof -
    have 0:"1\<^sub>m (2 ^ n) * |state_basis n jm\<rangle> = |state_basis n jm\<rangle>" 
      using left_mult_one_mat state_basis_carrier_mat by metis
    have "H * |state_basis 1 jd\<rangle> =
          1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat jd)/2) \<cdot>\<^sub>m |one\<rangle>)"
    proof (rule disjE)
      show "jd = 0 \<or> jd = 1" using jd_def assms by (metis One_nat_def less_2_cases 
            less_power_add_imp_div_less plus_1_eq_Suc power_one_right)
    next
      assume jd0:"jd = 0"
      have "H * |state_basis 1 0\<rangle> = 
            mat_of_cols_list 2 (map (map complex_of_real) [[1 / sqrt 2, 1 / sqrt 2]])" 
        using H_on_ket_zero state_basis_def by auto
      also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat 0)/2) \<cdot>\<^sub>m |one\<rangle>)"
      proof 
        fix i j
        assume ai:"i < dim_row ((1/sqrt 2) \<cdot>\<^sub>m ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat 0/2) \<cdot>\<^sub>m |one\<rangle>))"
        hence "i < 2" using mat_of_cols_list_def smult_carrier_mat ket_vec_def by simp
        hence i2:"i \<in> {0,1}" by auto
        assume aj:"j < dim_col ((1/sqrt 2) \<cdot>\<^sub>m ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat 0/2) \<cdot>\<^sub>m |one\<rangle>))"
        hence j0:"j = 0" using mat_of_cols_list_def smult_carrier_mat ket_vec_def by simp
        have "(mat_of_cols_list 2 (map (map complex_of_real) [[1 / sqrt 2, 1 / sqrt 2]])) $$ (i,0) =
              (mat_of_cols_list 2 [[1/sqrt 2, 1/sqrt 2]]) $$ (i,0)"
          using map_def by simp
        also have "\<dots> = 1/sqrt 2" using i2 index_mat_of_cols_list by auto
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,1]])) $$ (i,0)"
          using smult_mat_def mat_of_cols_list_def index_mat_of_cols_list 
          by (smt (verit, best) Suc_1 \<open>i < 2\<close> dim_col_mat(1) dim_row_mat(1) index_smult_mat(1) 
              ket_one_is_state ket_one_to_mat_of_cols_list less_Suc_eq_0_disj less_one list.size(4) 
              mult.right_neutral nth_Cons_0 nth_Cons_Suc state_def)
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + |one\<rangle>)) $$ (i,0)"
        proof -
          have "mat_of_cols_list 2 [[1,1]] = |zero\<rangle> + |one\<rangle>"
          proof 
            fix i j::nat 
            define s1 s2 where "s1 = mat_of_cols_list 2 [[1,1]]" and "s2 = |zero\<rangle> + |one\<rangle>"
            assume "i < dim_row s2" and "j < dim_col s2"
            hence "i \<in> {0,1} \<and> j = 0" using index_add_mat 
              by (simp add: ket_vec_def less_Suc_eq numerals(2) s2_def)
            thus "s1 $$ (i,j) = s2 $$ (i,j)" using s1_def s2_def mat_of_cols_list_def 
                \<open>i < dim_row s2\<close> ket_one_to_mat_of_cols_list by force
          next
            define s1 s2 where "s1 = mat_of_cols_list 2 [[1,1]]" and "s2 = |zero\<rangle> + |one\<rangle>"
            thus "dim_row s1 = dim_row s2" using mat_of_cols_list_def by (simp add: ket_vec_def)
          next
            define s1 s2 where "s1 = mat_of_cols_list 2 [[1,1]]" and "s2 = |zero\<rangle> + |one\<rangle>"
            thus "dim_col s1 = dim_col s2" using mat_of_cols_list_def by (simp add: ket_vec_def)
          qed
          thus ?thesis by simp
        qed
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + 1 \<cdot>\<^sub>m |one\<rangle>)) $$ (i,0)"
          using smult_mat_def \<open>i < 2\<close> ket_one_is_state state_def by force
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp (2*\<i>*pi*(complex_of_nat 0)/2) \<cdot>\<^sub>m |one\<rangle>)) $$ (i,0)"
          by auto
        finally show "Tensor.mat_of_cols_list 2 (map (map complex_of_real) 
                      [[1 / sqrt 2, 1 / sqrt 2]]) $$ (i, j) =
                      (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m ( |Deutsch.zero\<rangle> + 
                       exp (2 * \<i> * complex_of_real pi * complex_of_nat 0 / 2) \<cdot>\<^sub>m |Deutsch.one\<rangle>)) $$
                       (i, j)" 
          using j0 i2 ai aj by auto
      next
        show "dim_row (Tensor.mat_of_cols_list 2 (map (map complex_of_real)
              [[1 / sqrt 2, 1 / sqrt 2]])) = dim_row (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m
              ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat 0 /2) \<cdot>\<^sub>m
                |Deutsch.one\<rangle>))" 
          using mat_of_cols_list_def index_mat_of_cols_list smult_carrier_mat ket_vec_def by auto
      next
        show "dim_col (Tensor.mat_of_cols_list 2 (map (map complex_of_real)
              [[1 / sqrt 2, 1 / sqrt 2]])) = dim_col (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m
              ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat 0 /2) \<cdot>\<^sub>m
                |Deutsch.one\<rangle>))"
          using mat_of_cols_list_def index_mat_of_cols_list smult_carrier_mat ket_vec_def by auto
      qed
      finally show ?thesis using jd0 by simp
    next
      assume jd1:"jd = 1"
      have "H * |state_basis 1 1\<rangle> = 
            mat_of_cols_list 2 (map (map complex_of_real) [[1 / sqrt 2, - 1 / sqrt 2]])"
        using H_on_ket_one map_def by (simp add: state_basis_def)
      also have "\<dots> = (1 / sqrt 2) \<cdot>\<^sub>m ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat 1 / 2) \<cdot>\<^sub>m |one\<rangle>)"
      proof 
        fix i j
        assume ai:"i < dim_row (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m ( |zero\<rangle> + 
                       exp (2*\<i>*complex_of_real pi *complex_of_nat 1 /2) \<cdot>\<^sub>m |one\<rangle>))"
        hence "i < 2" using mat_of_cols_list_def smult_carrier_mat ket_vec_def by simp
        hence i2:"i \<in> {0,1}" by auto
        assume aj:"j < dim_col (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m ( |zero\<rangle> + 
                       exp (2*\<i>*complex_of_real pi *complex_of_nat 1 /2) \<cdot>\<^sub>m |one\<rangle>))"
        hence j0:"j = 0" using mat_of_cols_list_def smult_carrier_mat ket_vec_def by simp
        have "(mat_of_cols_list 2 (map (map complex_of_real) [[1 / sqrt 2,-1 / sqrt 2]])) $$ (i,0) =
              (mat_of_cols_list 2 [[1/sqrt 2,- 1/sqrt 2]]) $$ (i,0)"
          using map_def by simp
        also have "\<dots> = ((1/sqrt 2) \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,-1]])) $$ (i,0)"
          using i2 smult_mat_def index_mat_of_cols_list mat_of_cols_list_def Suc_1 \<open>i < 2\<close> 
            dim_col_mat(1) dim_row_mat(1) index_smult_mat(1) nth_Cons_0 nth_Cons_Suc
            ket_one_is_state ket_one_to_mat_of_cols_list
          by (smt (z3) One_nat_def \<psi>\<^sub>0_to_\<psi>\<^sub>1 bot_nat_0.not_eq_extremum dim_col_tensor_mat 
              less_2_cases_iff list.map(2) list.size(4) mult_0_right mult_1 of_real_1 
              of_real_divide of_real_minus state_def times_divide_eq_left)
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> - |one\<rangle>)) $$ (i,0)"
        proof -
          define r1 r2 where "r1 = mat_of_cols_list 2 [[1,-1]]" and "r2 = |zero\<rangle> - |one\<rangle>"
          have "r1 $$ (0,0) = r2 $$ (0,0)" using r1_def r2_def mat_of_cols_list_def
            by (smt (verit, ccfv_threshold) One_nat_def add.commute diff_zero dim_row_mat(1) 
                index_mat(1) index_mat_of_cols_list ket_one_is_state ket_one_to_mat_of_cols_list 
                ket_zero_to_mat_of_cols_list list.size(3) list.size(4) minus_mat_def nth_Cons_0 
                plus_1_eq_Suc pos2 state_def zero_less_one_class.zero_less_one)
          moreover have "r1 $$ (1,0) = r2 $$ (1,0)" 
            using r1_def r2_def mat_of_cols_list_def ket_vec_def by simp
          ultimately show ?thesis using r1_def r2_def i2 
            by (smt (verit) One_nat_def Tensor.mat_of_cols_list_def \<open>i < 2\<close> add.commute 
                dim_col_mat(1) dim_row_mat(1) empty_iff index_smult_mat(1) index_unit_vec(3) 
                insert_iff ket_vec_def list.size(3) list.size(4) minus_mat_def plus_1_eq_Suc 
                zero_less_one_class.zero_less_one)
        qed
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + (-1) \<cdot>\<^sub>m |one\<rangle>)) $$ (i,0)"
          using smult_mat_def \<open>i < 2\<close> ket_one_is_state state_def by force
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat 1 / 2) \<cdot>\<^sub>m |one\<rangle>)) $$ (i,0)"
          using exp_pi_i' by auto
        finally show "mat_of_cols_list 2 (map (map complex_of_real) [[1/sqrt 2,-1/sqrt 2]]) $$ (i,j)
                   = (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat 1 /2) \<cdot>\<^sub>m
                     |one\<rangle>)) $$ (i, j)" using i2 ai aj j0 by auto
      next
        show "dim_row (Tensor.mat_of_cols_list 2 (map (map complex_of_real)
              [[1 / sqrt 2,- 1 / sqrt 2]])) = dim_row (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m
              ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat 1 /2) \<cdot>\<^sub>m
                |Deutsch.one\<rangle>))" 
          using mat_of_cols_list_def index_mat_of_cols_list smult_carrier_mat ket_vec_def by auto
      next
        show "dim_col (Tensor.mat_of_cols_list 2 (map (map complex_of_real)
              [[1 / sqrt 2,- 1 / sqrt 2]])) = dim_col (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m
              ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat 1 /2) \<cdot>\<^sub>m
                |Deutsch.one\<rangle>))"
          using mat_of_cols_list_def index_mat_of_cols_list smult_carrier_mat ket_vec_def by auto
      qed
      finally show ?thesis using jd1 by simp
    qed
    hence "(H * |state_basis 1 jd\<rangle>) \<Otimes> |state_basis n jm\<rangle> = 
          (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat jd)/2) \<cdot>\<^sub>m |one\<rangle>))) \<Otimes> |state_basis n jm\<rangle>"
      by simp
    thus ?thesis using 0 by presburger
  qed
  finally show ?thesis using jm_def jd_def by auto
qed


text \<open>Action of the R gate in the circuit\<close>

lemma R_action:
  assumes "j < 2 ^ Suc n" and "j mod 2 = 1"
  shows "(R (Suc n)) * ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) \<cdot>\<^sub>m |one\<rangle>) =
         |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^(Suc n)) \<cdot>\<^sub>m |one\<rangle>"
proof 
  fix i ja::nat
  assume "i < dim_row ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^(Suc n)) \<cdot>\<^sub>m |one\<rangle>)"
  hence il2:"i < 2" by (simp add: ket_vec_def)
  assume "ja < dim_col ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^(Suc n)) \<cdot>\<^sub>m |one\<rangle>)"
  hence ja0:"ja = 0" by (simp add: ket_vec_def)
  have "(R (Suc n)) * ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) \<cdot>\<^sub>m |one\<rangle>) =
        (mat_of_cols_list 2 [[1, 0],[0, exp(2*pi*\<i>/2^(Suc n))]]) *
        ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) \<cdot>\<^sub>m |one\<rangle>)"
    using R_def by simp
  also have "\<dots> = (mat_of_cols_list 2 [[1, 0],[0, exp(2*pi*\<i>/2^(Suc n))]]) *
                  (mat_of_cols_list 2 [[1,0]] + 
                   exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) \<cdot>\<^sub>m mat_of_cols_list 2 [[0,1]])"
    using ket_one_to_mat_of_cols_list ket_zero_to_mat_of_cols_list by presburger
  also have "\<dots> = (mat_of_cols_list 2 [[1, 0],[0, exp(2*pi*\<i>/2^(Suc n))]]) *
                  (mat_of_cols_list 2 [[1,0]] + 
                   mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]])"
  proof -
    have "exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) \<cdot>\<^sub>m mat_of_cols_list 2 [[0,1]] =
          mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]"
    proof 
      fix a b::nat
      assume "a < dim_row (mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]])"
      hence a2:"a < 2" by (simp add: Tensor.mat_of_cols_list_def)
      assume "b < dim_col (mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]])"
      hence b0:"b = 0" 
        by (metis One_nat_def Suc_eq_plus1 Tensor.mat_of_cols_list_def dim_col_mat(1) less_Suc0 
            list.size(3) list.size(4))
      have "(exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) \<cdot>\<^sub>m mat_of_cols_list 2 [[0,1]]) $$ (a,0) =
            exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) * (mat_of_cols_list 2 [[0,1]] $$ (a,0))"
        using index_smult_mat a2 ket_one_is_state ket_one_to_mat_of_cols_list state_def by force
      also have "\<dots> = (mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,0)"
      proof (rule disjE)
        show "a = 0 \<or> a = 1" using a2 by auto
      next
        assume a0:"a = 0"
        have "exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) * (mat_of_cols_list 2 [[0,1]] $$ (0,0)) =
              exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) * 0"
          using index_mat_of_cols_list by auto
        thus "exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) * (mat_of_cols_list 2 [[0,1]] $$ (a,0)) =
              (mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,0)"
          using a0 by auto
      next
        assume a1:"a = 1"
        have "exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) * (mat_of_cols_list 2 [[0,1]] $$ (1,0)) =
              exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) * 1"
          using index_mat_of_cols_list by auto
        thus "exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) * (mat_of_cols_list 2 [[0,1]] $$ (a,0)) =
              (mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,0)"
          using a1 by auto
      qed
      finally show "(exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n) \<cdot>\<^sub>m mat_of_cols_list 2 [[0,1]]) 
        $$ (a,b) = (mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,b)"
        using b0 by simp
    next
      show "dim_row (exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ n) \<cdot>\<^sub>m
            Tensor.mat_of_cols_list 2 [[0, 1]]) =
            dim_row (Tensor.mat_of_cols_list 2 [[0, exp (2 * \<i> * complex_of_real pi *
                      complex_of_nat (j div 2) / 2 ^ n)]])" 
        by (simp add: Tensor.mat_of_cols_list_def)
    next
      show "dim_col (exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ n) \<cdot>\<^sub>m
            Tensor.mat_of_cols_list 2 [[0, 1]]) =
            dim_col (Tensor.mat_of_cols_list 2 [[0, exp (2 * \<i> * complex_of_real pi *
                      complex_of_nat (j div 2) / 2 ^ n)]])"
        by (simp add: mat_of_cols_list_def)
    qed
    thus ?thesis by auto
  qed
  also have "\<dots> = (mat_of_cols_list 2 [[1, 0],[0, exp(2*pi*\<i>/2^(Suc n))]]) *
                  (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]])"
  proof -
    have "mat_of_cols_list 2 [[1,0]] + 
          mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]] = 
          mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]"
    proof 
      fix a b::nat
      assume "a < dim_row (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]])"
      hence a2:"a < 2" using mat_of_cols_list_def by simp 
      assume "b < dim_col (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]])"
      hence b0:"b = 0" using mat_of_cols_list_def by auto
      show "(mat_of_cols_list 2 [[1,0]] + 
             mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,b) = 
            (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,b)"
      proof (rule disjE)
        show "a = 0 \<or> a = 1" using a2 by auto
      next
        assume a0:"a = 0"
        have "(mat_of_cols_list 2 [[1,0]] + 
               mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (0,0) = 
              (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (0,0)"
          using index_mat_of_cols_list by (simp add: Tensor.mat_of_cols_list_def)
        thus "(mat_of_cols_list 2 [[1,0]] + 
               mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,b) = 
              (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,b)"
          using a0 b0 by simp
      next
        assume a1:"a = 1"
        show "(mat_of_cols_list 2 [[1,0]] + 
               mat_of_cols_list 2 [[0,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,b) = 
              (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^n)]]) $$ (a,b)"
          using a1 b0 index_mat_of_cols_list mat_of_cols_list_def by simp
      qed
    next
      show "dim_row (Tensor.mat_of_cols_list 2 [[1, 0]] + Tensor.mat_of_cols_list 2
            [[0, exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ n)]]) =
            dim_row (Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi *
                    complex_of_nat (j div 2) / 2 ^ n)]])"
        by (simp add: Tensor.mat_of_cols_list_def)
    next 
      show "dim_col (Tensor.mat_of_cols_list 2 [[1, 0]] + Tensor.mat_of_cols_list 2
            [[0, exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ n)]]) =
            dim_col (Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi *
                    complex_of_nat (j div 2) / 2 ^ n)]])"
        by (simp add: mat_of_cols_list_def)
    qed
    thus ?thesis by simp
  qed
  finally have 1:"R (Suc n) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi *
                  complex_of_nat (j div 2) / 2 ^ n) \<cdot>\<^sub>m |Deutsch.one\<rangle>) =
                  Tensor.mat_of_cols_list 2 [[1, 0], [0, exp (complex_of_real (2 * pi) * \<i> /
                  2 ^ Suc n)]] * Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi *
                  complex_of_nat (j div 2) / 2 ^ n)]]"
    by this
  show "(R (Suc n) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi *  complex_of_nat (j div 2) /  2 ^ n) \<cdot>\<^sub>m
        |Deutsch.one\<rangle>)) $$ (i, ja) =
       ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc n) \<cdot>\<^sub>m
        |Deutsch.one\<rangle>) $$ (i, ja)"
  proof -
    have "((R (Suc n) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi *  complex_of_nat (j div 2) /  2 ^ n) \<cdot>\<^sub>m
          |Deutsch.one\<rangle>))) $$ (i, ja) = 
          (Tensor.mat_of_cols_list 2 [[1, 0], [0, exp (complex_of_real (2 * pi) * \<i> /
                  2 ^ Suc n)]] * Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi *
                  complex_of_nat (j div 2) / 2 ^ n)]]) $$ (i,ja)"
      using 1 by simp
    also have "\<dots> = mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]] $$ (i,ja)"
    proof (rule disjE)
      show "i = 0 \<or> i = 1" using il2 by auto
    next
      assume i0:"i = 0"
      have "(Tensor.mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]]
             * Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
             complex_of_nat (j div 2) / 2 ^ n)]]) $$ (0, 0) = 
           (\<Sum>k<2. (mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]])
            $$ (0,k) * (mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
             complex_of_nat (j div 2) / 2 ^ n)]]) $$ (k,0))"
        using index_mult_mat mat_of_cols_list_def by auto
      also have "\<dots> = (mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]])
                      $$ (0,0) * (mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
                       complex_of_nat (j div 2) / 2 ^ n)]]) $$ (0,0) +
                      (mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]])
                      $$ (0,1) * (mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
                       complex_of_nat (j div 2) / 2 ^ n)]]) $$ (1,0)"
        by (simp only:sumof2)
      also have "\<dots> = 1" by auto
      also have "\<dots> = mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]] $$ (0,0)"
        using index_mat_of_cols_list by simp
      finally show "(Tensor.mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 
                    2 ^ Suc n)]] * Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
                    complex_of_nat (j div 2) / 2 ^ n)]]) $$ (i, ja) = 
                    (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]]) $$ (i,ja)"
        using i0 ja0 by simp
    next
      assume i1:"i = 1"
      have "(Tensor.mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]]
             * Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
             complex_of_nat (j div 2) / 2 ^ n)]]) $$ (1, 0) = 
           (\<Sum>k<2. (mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]])
            $$ (1,k) * (mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
             complex_of_nat (j div 2) / 2 ^ n)]]) $$ (k,0))"
        using index_mult_mat mat_of_cols_list_def by auto
      also have "\<dots> = (mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]])
                      $$ (1,0) * (mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
                       complex_of_nat (j div 2) / 2 ^ n)]]) $$ (0,0) +
                      (mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n)]])
                      $$ (1,1) * (mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
                       complex_of_nat (j div 2) / 2 ^ n)]]) $$ (1,0)"
        by (simp only: sumof2)
      also have "\<dots> = exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n) *
                      exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ n)"
        using index_mat_of_cols_list by auto
      also have "\<dots> = exp (complex_of_real (2 * pi) * \<i> / 2 ^ Suc n +
                          2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ n)"
        using mult_exp_exp by simp
      also have "\<dots> = exp (2 * \<i> * pi / 2 ^ Suc n +
                          2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ n)"
        by (simp add: mult.commute)
      also have "\<dots> = exp (2*\<i>*pi*(1/2^Suc n + complex_of_nat (j div 2)/2^n))"
        by (simp add: distrib_left)
      also have "\<dots> = exp (2*\<i>*pi*((1 + 2*(j div 2))/2^Suc n))" 
        by (simp add: add_divide_distrib)
      also have "\<dots> = exp (2*\<i>*pi*(j)/2^Suc n)"
        using assms
        by (smt (verit, ccfv_threshold) Suc_eq_plus1 div_mult_mod_eq mult.commute of_real_1 
            of_real_add of_real_divide of_real_of_nat_eq of_real_power one_add_one plus_1_eq_Suc 
            times_divide_eq_right)
      also have "\<dots> = (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]]) $$ (1,0)"
        using index_mat_of_cols_list by simp
      finally show "(Tensor.mat_of_cols_list 2 [[1, 0],[0, exp (complex_of_real (2 * pi) * \<i> / 
                    2 ^ Suc n)]] * Tensor.mat_of_cols_list 2 [[1, exp (2 * \<i> * complex_of_real pi * 
                    complex_of_nat (j div 2) / 2 ^ n)]]) $$ (i, ja) = 
                    (mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]]) $$ (i,ja)"
        using i1 ja0 by simp
    qed
    also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (i,ja)"
    proof (rule disjE)
      show "i = 0 \<or> i = 1" using il2 by auto
    next
      assume i0:"i = 0"
      have "(mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]]) $$ (0,0) = 1"
        by auto
      also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (0,0)"
      proof -
        have "|zero\<rangle> $$ (0,0) = 1" by auto
        moreover have "(exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (0,0) = 0"
        proof -
          have "(exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (0,0) =
                exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) * |one\<rangle> $$ (0,0)"
            using index_smult_mat using ket_one_is_state state_def by auto
          also have "\<dots> = 0" by auto
          finally show ?thesis by this
        qed
        ultimately show ?thesis by (simp add: ket_vec_def)
      qed
      finally show "(mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]]) $$ (i,ja) =
                    ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (i,ja)"
        using i0 ja0 by simp
    next
      assume i1:"i = 1"
      have "(mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]]) $$ (1,0) =
            exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)" by auto
      also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (1,0)"
      proof -
        have "|zero\<rangle> $$ (1,0) = 0" by auto
        moreover have "(exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (1,0) =
                        exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)"
        proof -
          have "(exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (1,0) =
                exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) * |one\<rangle> $$ (1,0)"
            using index_smult_mat ket_one_is_state state_def by auto
          also have "\<dots> = exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)" by auto
          finally show ?thesis by this
        qed
        ultimately show ?thesis by (simp add: ket_vec_def)
      qed
      finally show "(mat_of_cols_list 2 [[1,exp (2*\<i>*pi*complex_of_nat j / 2^Suc n)]]) $$ (i,ja) =
                    ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) $$ (i,ja)"
        using i1 ja0 by simp
    qed
    finally show ?thesis by this
  qed
next
  show "dim_row (R (Suc n) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi *
        complex_of_nat (j div 2) / 2 ^ n) \<cdot>\<^sub>m |Deutsch.one\<rangle>)) =
        dim_row ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc n) \<cdot>\<^sub>m
        |Deutsch.one\<rangle>)" 
    by (simp add: R_def Tensor.mat_of_cols_list_def ket_vec_def)
next
  show "dim_col (R (Suc n) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi *
        complex_of_nat (j div 2) / 2 ^ n) \<cdot>\<^sub>m |Deutsch.one\<rangle>)) =
        dim_col ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc n) \<cdot>\<^sub>m
        |Deutsch.one\<rangle>)"
    by (simp add: R_def Tensor.mat_of_cols_list_def ket_vec_def)
qed


text \<open>Action of the SWAP cascades in the circuit\<close>

lemma SWAP_up_action:
  "\<forall>j. j < 2 ^(Suc (Suc n)) \<longrightarrow> 
    SWAP_up (Suc (Suc n)) * ( |state_basis (Suc n) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) =
    |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc n) (j div 2)\<rangle>"
proof (induct n)
  case 0
  show ?case
  proof
    fix j
    show "j < 2 ^ Suc (Suc 0) \<longrightarrow> SWAP_up (Suc (Suc 0)) * ( |state_basis (Suc 0) (j div 2)\<rangle> \<Otimes>
          |state_basis 1 (j mod 2)\<rangle>) =
          |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc 0) (j div 2)\<rangle>"
    proof
      assume "j < 2^ Suc (Suc 0)"
      show "SWAP_up (Suc (Suc 0)) * ( |state_basis (Suc 0) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) 
            = |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc 0) (j div 2)\<rangle>"
      proof -
        have "SWAP_up (Suc (Suc 0))*( |state_basis (Suc 0) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)
              = SWAP * ( |state_basis (Suc 0) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)"
          using SWAP_up.simps by simp
        also have "\<dots> = |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc 0) (j div 2)\<rangle>"
          using SWAP_tensor
          by (metis One_nat_def power_one_right state_basis_carrier_mat)
        finally show ?thesis by this
      qed
    qed
  qed
next
  case (Suc n)
  assume HI:"\<forall>j<2 ^ Suc (Suc n).
            SWAP_up (Suc (Suc n)) * ( |state_basis (Suc n) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)
            = |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc n) (j div 2)\<rangle>"
  show "\<forall>j<2 ^ Suc (Suc (Suc n)).
         SWAP_up (Suc (Suc (Suc n))) * ( |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes> 
         |state_basis 1 (j mod 2)\<rangle>) =
         |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n)) (j div 2)\<rangle>"
  proof 
    fix j::nat
    show "j < 2 ^ Suc (Suc (Suc n)) \<longrightarrow>
         SWAP_up (Suc (Suc (Suc n))) * ( |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes>
          |state_basis 1 (j mod 2)\<rangle>) =
         |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n)) (j div 2)\<rangle>"
    proof 
      assume jl:"j < 2 ^ Suc (Suc (Suc n))"
      show "SWAP_up (Suc (Suc (Suc n))) * ( |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes>
            |state_basis 1 (j mod 2)\<rangle>) =
            |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n)) (j div 2)\<rangle>"
      proof -
        have "SWAP_up (Suc (Suc (Suc n))) * ( |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes>
              |state_basis 1 (j mod 2)\<rangle>) =
              ((SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) * ((1\<^sub>m 2) \<Otimes> (SWAP_up (Suc (Suc n))))) *
              ( |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)"
          using SWAP_up.simps by simp
        also have "\<dots> = (SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) * (((1\<^sub>m 2) \<Otimes> (SWAP_up (Suc (Suc n)))) *
                        ( |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>))"
          using assoc_mult_mat
          by (smt (verit, ccfv_threshold) Groups.mult_ac(2) Groups.mult_ac(3) One_nat_def 
              SWAP_up.simps(3) SWAP_up_carrier_mat carrier_matD(2) carrier_matI dim_col_tensor_mat 
              dim_row_mat(1) dim_row_tensor_mat index_mult_mat(2) index_one_mat(3) 
              index_unit_vec(3) ket_vec_def left_mult_one_mat power_Suc2 power_one_right 
              state_basis_def)
        also have "\<dots> = (SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) * (((1\<^sub>m 2) \<Otimes> (SWAP_up (Suc (Suc n)))) *
                        (( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes> 
                           |state_basis (Suc n) ((j div 2) mod 2^Suc n)\<rangle>)
                         \<Otimes> |state_basis 1 (j mod 2)\<rangle>))"
          using state_basis_dec
          by (metis jl less_mult_imp_div_less power_Suc2)
        also have "\<dots> = (SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) * (((1\<^sub>m 2) \<Otimes> (SWAP_up (Suc (Suc n)))) *
                        ( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes> 
                         ( |state_basis (Suc n) ((j div 2) mod 2^Suc n)\<rangle>
                         \<Otimes> |state_basis 1 (j mod 2)\<rangle>)))"
          using tensor_mat_is_assoc state_basis_carrier_mat by auto
        also have "\<dots> = (SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) * (((1\<^sub>m 2) \<Otimes> (SWAP_up (Suc (Suc n)))) *
                        ( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes> 
                        ( |state_basis (Suc n) ((j mod 2^Suc (Suc n)) div 2)\<rangle>
                        \<Otimes> |state_basis 1 ((j mod 2^Suc (Suc n)) mod 2)\<rangle>)))"
          using jl power_Suc power_add power_one_right
          by (smt (z3) Suc_1 add_0 div_Suc div_exp_mod_exp_eq lessI mod_less mod_mod_cancel 
              mod_mult_self2 n_not_Suc_n odd_Suc_div_two plus_1_eq_Suc)
        also have "\<dots> = (SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) *
                        (((1\<^sub>m 2) * |state_basis 1 ((j div 2) div 2^Suc n)\<rangle>) \<Otimes>
                        ((SWAP_up (Suc (Suc n)))) *
                        ( |state_basis (Suc n) ((j mod 2^Suc (Suc n)) div 2)\<rangle>
                        \<Otimes> |state_basis 1 ((j mod 2^Suc (Suc n)) mod 2)\<rangle>))"
          using mult_distr_tensor
          by (metis SWAP_up_carrier_mat carrier_matD(1) carrier_matD(2) index_one_mat(3) 
              less_numeral_extra(1) mod_less_divisor pos2 power_one_right state_basis_carrier_mat 
              state_basis_dec' zero_less_power)
        also have "\<dots> = (SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) *
                        ( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes>
                        ( |state_basis 1 ((j mod 2^Suc (Suc n)) mod 2)\<rangle> \<Otimes>
                          |state_basis (Suc n) ((j mod 2^Suc (Suc n)) div 2)\<rangle>))"
          using HI
          by (metis left_mult_one_mat mod_less_divisor pos2 power_one_right state_basis_carrier_mat
              zero_less_power)
        also have "\<dots> = (SWAP \<Otimes> (1\<^sub>m (2^(Suc n)))) *
                        (( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes>
                           |state_basis 1 ((j mod 2^Suc (Suc n)) mod 2)\<rangle>) \<Otimes>
                           |state_basis (Suc n) ((j mod 2^Suc (Suc n)) div 2)\<rangle>)"
          using tensor_mat_is_assoc by simp
        also have "\<dots> = (SWAP * ( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes>
                                  |state_basis 1 ((j mod 2^Suc (Suc n)) mod 2)\<rangle>)) \<Otimes>
                        ((1\<^sub>m (2^(Suc n))) * |state_basis (Suc n) ((j mod 2^Suc (Suc n)) div 2)\<rangle>)"
          using mult_distr_tensor 
          by (smt (verit, del_insts) One_nat_def SWAP_ncols SWAP_nrows SWAP_tensor carrier_matD(2) 
              dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat index_mult_mat(2) 
              index_one_mat(3) index_unit_vec(3) ket_vec_def lessI one_power2 pos2 power_Suc2 
              power_one_right state_basis_carrier_mat state_basis_def zero_less_power)
        also have "\<dots> = ( |state_basis 1 ((j mod 2^Suc (Suc n)) mod 2)\<rangle> \<Otimes>
                          |state_basis 1 ((j div 2) div 2^Suc n)\<rangle>) \<Otimes>
                          |state_basis (Suc n) ((j mod 2^Suc (Suc n)) div 2)\<rangle>"
          using SWAP_tensor
          by (metis left_mult_one_mat power_one_right state_basis_carrier_mat)
        also have "\<dots> = |state_basis 1 ((j mod 2^Suc (Suc n)) mod 2)\<rangle> \<Otimes>
                      ( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes>
                        |state_basis (Suc n) ((j mod 2^Suc (Suc n)) div 2)\<rangle>)"
          using tensor_mat_is_assoc by simp
        also have "\<dots> = |state_basis 1 (j mod 2)\<rangle> \<Otimes>
                      ( |state_basis 1 ((j div 2) div 2^Suc n)\<rangle> \<Otimes>
                        |state_basis (Suc n) ((j div 2) mod 2^Suc n)\<rangle>)" 
        proof -
          have f1: "\<forall>n na. (n::nat) ^ (1 + na) = n ^ Suc na"
            by simp
          have "\<forall>n na. (n::nat) dvd n ^ Suc na"
            by simp
          then show ?thesis
            using f1 by (smt (z3) div_exp_mod_exp_eq mod_mod_cancel power_one_right)
        qed
        also have "\<dots> = |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n)) (j div 2)\<rangle>"
          using state_basis_dec jl
          by (metis less_mult_imp_div_less power_Suc2)
        finally show ?thesis by this
      qed
    qed
  qed
qed



lemma SWAP_down_action:
  "\<forall>j. j < 2 ^Suc (Suc n) \<longrightarrow> 
    SWAP_down (Suc (Suc n)) * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc n) (j div 2)\<rangle>) =
    |state_basis (Suc n) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
proof (induct n)
  case 0
  show ?case
  proof
    fix j::nat
    show "j < 2 ^ Suc (Suc 0) \<longrightarrow>
         SWAP_down (Suc (Suc 0)) * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc 0) (j div 2)\<rangle>) =
         |state_basis (Suc 0) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
    proof
      assume "j < 2 ^ Suc (Suc 0)"
      show "SWAP_down (Suc (Suc 0))*( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc 0) (j div 2)\<rangle>)
         = |state_basis (Suc 0) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
      proof -
        have "SWAP_down (Suc (Suc 0))*( |state_basis 1 (j mod 2)\<rangle>\<Otimes>|state_basis (Suc 0) (j div 2)\<rangle>)
            = SWAP * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc 0) (j div 2)\<rangle>)" 
          using SWAP_down.simps by simp
        also have "\<dots> = |state_basis (Suc 0) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
          using SWAP_tensor state_basis_carrier_mat 
          by (metis One_nat_def power_one_right)
        finally show ?thesis by this
      qed
    qed
  qed
next
  case (Suc n)
  assume HI:"\<forall>j<2 ^ Suc (Suc n).
            SWAP_down (Suc (Suc n))*( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc n) (j div 2)\<rangle>)
          = |state_basis (Suc n) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
  show "\<forall>j<2 ^ Suc (Suc (Suc n)).
            SWAP_down (Suc (Suc (Suc n)))*( |state_basis 1 (j mod 2)\<rangle> \<Otimes> 
            |state_basis (Suc (Suc n)) (j div 2)\<rangle>)
          = |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
  proof
    fix j::nat
    show "j < 2 ^ Suc (Suc (Suc n)) \<longrightarrow>
         SWAP_down (Suc (Suc (Suc n))) * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n))
            (j div 2)\<rangle>) =
         |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
    proof
      assume jl:"j < 2 ^ Suc (Suc (Suc n))"
      show "SWAP_down (Suc (Suc (Suc n))) * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> 
            |state_basis (Suc (Suc n)) (j div 2)\<rangle>) =
            |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
      proof -
        define x where "x = 2*((j div 2) div 2) + (j mod 2)"
        have xl:"x < 2^Suc (Suc n)"
        proof -
          have "j mod 2 < 2" by auto
          moreover have 0:"(j div 2) div 2 < 2^Suc n" using jl by auto
          moreover have "2*((j div 2) div 2) < 2^Suc (Suc n)" using 0 by auto
          ultimately show ?thesis using x_def
            by (metis (no_types, lifting) Suc_double_not_eq_double add.right_neutral add_Suc_right 
                less_2_cases_iff linorder_neqE_nat not_less_eq power_Suc)
        qed
        have xm:"x mod 2 = j mod 2" using x_def by auto
        have xd:"x div 2 = j div 2 div 2" using x_def by auto
        have "SWAP_down (Suc (Suc (Suc n))) * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> 
              |state_basis (Suc (Suc n)) (j div 2)\<rangle>) =
              (((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) * ((SWAP_down (Suc (Suc n))) \<Otimes> (1\<^sub>m 2))) *
            ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n)) (j div 2)\<rangle>)"
          using SWAP_down.simps by simp
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) * (((SWAP_down (Suc (Suc n))) \<Otimes> (1\<^sub>m 2)) *
                        ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n)) (j div 2)\<rangle>))"
        proof (rule assoc_mult_mat)
          show "1\<^sub>m (2 ^ Suc n) \<Otimes> SWAP \<in> carrier_mat (2^Suc (Suc (Suc n))) (2^Suc (Suc (Suc n)))"
            by (simp add: SWAP_ncols SWAP_nrows carrier_matI)
          show "SWAP_down (Suc (Suc n)) \<Otimes> 1\<^sub>m 2
                \<in> carrier_mat (2 ^ Suc (Suc (Suc n))) (2 ^ Suc (Suc (Suc n)))"
            by (metis One_nat_def SWAP_down.simps(2) SWAP_down_carrier_mat power_Suc2
                power_one_right tensor_carrier_mat)
          show "|state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis (Suc (Suc n)) (j div 2)\<rangle>
                \<in> carrier_mat (2 ^ Suc (Suc (Suc n))) 1"
            by (metis Suc_1 one_power2 power_Suc power_one_right state_basis_carrier_mat 
                tensor_carrier_mat)
        qed
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) * (((SWAP_down (Suc (Suc n))) \<Otimes> (1\<^sub>m 2)) *
                        ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> 
                        ( |state_basis (Suc n) ((j div 2) div 2)\<rangle> \<Otimes>
                          |state_basis 1 ((j div 2) mod 2)\<rangle>)))"
          using state_basis_dec' jl 
          by (metis less_mult_imp_div_less power_Suc2)
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) * (((SWAP_down (Suc (Suc n))) \<Otimes> (1\<^sub>m 2)) *
                        (( |state_basis 1 (j mod 2)\<rangle> \<Otimes> 
                          |state_basis (Suc n) ((j div 2) div 2)\<rangle>) \<Otimes>
                          |state_basis 1 ((j div 2) mod 2)\<rangle>))"
          using tensor_mat_is_assoc by simp
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) * 
                        (((SWAP_down (Suc (Suc n))) * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> 
                          |state_basis (Suc n) ((j div 2) div 2)\<rangle>)) \<Otimes>
                        ((1\<^sub>m 2) * |state_basis 1 ((j div 2) mod 2)\<rangle>))"
          using mult_distr_tensor
          by (smt (verit, ccfv_threshold) SWAP_down_carrier_mat carrier_matD(1) carrier_matD(2)
              dim_col_tensor_mat dim_row_tensor_mat index_one_mat(3) mult.right_neutral 
              nat_zero_less_power_iff pos2 power_Suc2 power_commutes power_one_right 
              state_basis_carrier_mat zero_less_one_class.zero_less_one)
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) * 
                        (((SWAP_down (Suc (Suc n))) * ( |state_basis 1 (x mod 2)\<rangle> \<Otimes> 
                          |state_basis (Suc n) (x div 2)\<rangle>)) \<Otimes>
                        ((1\<^sub>m 2) * |state_basis 1 ((j div 2) mod 2)\<rangle>))"
          using xm xd by simp
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) *
                        (( |state_basis (Suc n) (x div 2)\<rangle> \<Otimes> |state_basis 1 (x mod 2)\<rangle>) \<Otimes>
                           |state_basis 1 ((j div 2) mod 2)\<rangle>)"
          using HI
          by (metis dim_row_mat(1) index_unit_vec(3) ket_vec_def left_mult_one_mat' power_one_right 
              state_basis_def xl)
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) \<Otimes> SWAP) *
                        ( |state_basis (Suc n) (x div 2)\<rangle> \<Otimes> ( |state_basis 1 (x mod 2)\<rangle> \<Otimes>
                           |state_basis 1 ((j div 2) mod 2)\<rangle>))"
          using tensor_mat_is_assoc by force
        also have "\<dots> = ((1\<^sub>m (2^(Suc n))) * |state_basis (Suc n) (x div 2)\<rangle>) \<Otimes>
                        (SWAP * ( |state_basis 1 (x mod 2)\<rangle> \<Otimes> |state_basis 1 ((j div 2) mod 2)\<rangle>))"
          using mult_distr_tensor state_basis_carrier_mat SWAP_carrier_mat
          by (smt (verit, del_insts) SWAP_tensor carrier_matD(1) carrier_matD(2) dim_col_tensor_mat
              index_mult_mat(2) index_one_mat(3) nat_0_less_mult_iff power_one_right 
              tensor_mat_is_assoc zero_less_numeral zero_less_one_class.zero_less_one 
              zero_less_power) 
        also have "\<dots> = |state_basis (Suc n) (x div 2)\<rangle> \<Otimes>
                      ( |state_basis 1 ((j div 2) mod 2)\<rangle> \<Otimes> |state_basis 1 (x mod 2)\<rangle>)"
          using SWAP_tensor
          by (metis left_mult_one_mat power_one_right state_basis_carrier_mat)
        also have "\<dots> = ( |state_basis (Suc n) (x div 2)\<rangle> \<Otimes> |state_basis 1 ((j div 2) mod 2)\<rangle>) \<Otimes>
                          |state_basis 1 (x mod 2)\<rangle>"
          using assoc_mult_mat tensor_mat_is_assoc by presburger
        also have "\<dots> = |state_basis (Suc (Suc n)) (j div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
          using state_basis_dec' xd xm
          by (metis jl less_mult_imp_div_less power_Suc2)
        finally show ?thesis by this
      qed
    qed
  qed
qed


text \<open>Action of the controlled-R gates in the circuit\<close>

lemma controlR_action:
  assumes "j < 2 ^ Suc (Suc n)"
  shows "(control (Suc (Suc n)) (R (Suc (Suc n)))) *
         (( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat (j div 2) / 2^(Suc n)) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
          |state_basis n ((j mod 2^(Suc n)) div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) =
          ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^(Suc (Suc n))) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
          |state_basis n ((j mod 2^(Suc n)) div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
proof (cases n)
  case 0
  then show ?thesis
  proof -
    assume n0:"n = 0"
    show "control (Suc (Suc n)) (R (Suc (Suc n))) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) =
          |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc (Suc n)) \<cdot>\<^sub>m
          |Deutsch.one\<rangle> \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>"
    proof -
      have "control (Suc (Suc 0)) (R (Suc (Suc 0))) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis 0 (j mod 2 ^ Suc 0 div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) =
          control2 (R 2) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis 0 (j mod 2 ^ Suc 0 div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)"
        using control.simps by (metis One_nat_def Suc_1)
      also have "\<dots> = control2 (R 2) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)"
        using state_basis_def unit_vec_def ket_vec_def
        by (smt (verit, del_insts) H_inv H_is_gate One_nat_def gate_def index_mult_mat(2) 
            index_one_mat(2) mod_less_divisor mod_mod_trivial pos2 state_basis_dec' 
            tensor_mat_is_assoc)
      also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^(Suc (Suc 0))) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
                      |state_basis 1 (j mod 2)\<rangle>"
      proof (rule disjE)
        show "j mod 2 = 0 \<or> j mod 2 = 1" by auto
      next
        assume jm0:"j mod 2 = 0"
        hence jdj:"j div 2 = j/2" by auto
        have "control2 (R 2) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) =
          control2 (R 2) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |zero\<rangle>)"
          using jm0 state_basis_def mat_of_cols_list_def by fastforce
        also have "\<dots> = |Deutsch.zero\<rangle> + exp (2*\<i>*pi* complex_of_nat (j div 2) / 2 ^ Suc 0)
                        \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |zero\<rangle>"
          using control2_zero by (simp add: ket_vec_def)
        also have "\<dots> = |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi *
                        complex_of_nat j / 2 ^ Suc (Suc 0)) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
                        |state_basis 1 (j mod 2)\<rangle>" 
          using jm0 state_basis_def mat_of_cols_list_def jdj 
          by (smt (verit, best) Euclidean_Rings.div_eq_0_iff One_nat_def Suc_1 assms 
              divide_divide_eq_left divide_eq_0_iff less_2_cases_iff less_power_add_imp_div_less n0
              neq_imp_neq_div_or_mod of_nat_0 of_nat_1 of_nat_Suc of_nat_numeral of_real_1 
              of_real_divide of_real_numeral power_Suc power_one_right times_divide_eq_right 
              two_div_two two_mod_two)
        finally show ?thesis by this
      next
        assume jm1:"j mod 2 = 1"
        have "control2 (R 2) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) =
          control2 (R 2) *
          ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
          \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |one\<rangle>)"
          using jm1 by (simp add: state_basis_def)
        also have "\<dots> = ((R 2) * 
           ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc 0)
            \<cdot>\<^sub>m |Deutsch.one\<rangle>)) \<Otimes> |one\<rangle>"
          using control2_one ket_vec_def R_def mat_of_cols_list_def by simp
        also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j/2^Suc (Suc 0)) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> |one\<rangle>"
          using R_action jm1 assms by (metis One_nat_def Suc_1 n0)
        finally show ?thesis by (metis jm1 power_one_right state_basis_def)
      qed
      finally show ?thesis
        by (smt (verit, best) Euclidean_Rings.div_eq_0_iff Suc_1 mod_less_divisor n0 
            not_mod2_eq_Suc_0_eq_0 one_mod_two_eq_one pos2 power_0 power_one_right state_basis_dec' 
            tensor_mat_is_assoc)
    qed
  qed
next
  case (Suc nat)
  then show ?thesis
  proof -
    assume "n = Suc nat"
    define jd2 where "jd2 = j div 2"
    define jm2 where "jm2 = j mod 2"
    define jm2sn where "jm2sn = j mod 2^Suc n"
    have jeq:"jm2sn mod 2 = j mod 2" using jm2sn_def 
      by (metis One_nat_def Suc_le_mono mod_mod_power_cancel power_one_right zero_order(1))
    have "(control (Suc (Suc n)) (R (Suc (Suc n)))) * ( |Deutsch.zero\<rangle> + 
          exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
          |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) = 
          (((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) \<Otimes> (1\<^sub>m (2^n))) * 
          ((1\<^sub>m 2) \<Otimes> SWAP_up (Suc n))) * ( |Deutsch.zero\<rangle> + 
          exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
          |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)"
      using control.simps Suc by presburger
    also have "\<dots> = (((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) \<Otimes> (1\<^sub>m (2^n)))) * 
          (((1\<^sub>m 2) \<Otimes> SWAP_up (Suc n)) * ( |Deutsch.zero\<rangle> + 
          exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
          |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>))"
    proof (rule assoc_mult_mat)
      show "(1\<^sub>m 2 \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) \<Otimes> 1\<^sub>m (2 ^ n))
            \<in> carrier_mat (2^Suc (Suc n)) (2^Suc (Suc n))"
        using SWAP_down_carrier_mat SWAP_up_carrier_mat control2_carrier_mat 
        by (smt (verit) Suc carrier_matD(1) carrier_matD(2) carrier_matI control.simps(4) 
            control_carrier_mat dim_col_tensor_mat index_mult_mat(2) index_mult_mat(3) 
            index_one_mat(3) mult_numeral_left_semiring_numeral num_double power_Suc)
      show "1\<^sub>m 2 \<Otimes> SWAP_up (Suc n) \<in> carrier_mat (2 ^ Suc (Suc n)) (2 ^ Suc (Suc n))"
        using SWAP_up_carrier_mat
        by (metis One_nat_def SWAP_up.simps(2) power_Suc power_one_right tensor_carrier_mat)
      show "|Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi *  complex_of_nat (j div 2) /
            2 ^ Suc n) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes>
            |state_basis 1 (j mod 2)\<rangle> \<in> carrier_mat (2 ^ Suc (Suc n)) 1"
        using ket_vec_def state_basis_carrier_mat
        by (simp add: carrier_matI state_basis_def)
    qed
    also have "\<dots> = (((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) \<Otimes> (1\<^sub>m (2^n)))) * 
          (((1\<^sub>m 2) \<Otimes> SWAP_up (Suc n)) * ( |Deutsch.zero\<rangle> + 
          exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
          ( |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)))"
      using tensor_mat_is_assoc by presburger
    also have "\<dots> = (((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) \<Otimes> (1\<^sub>m (2^n)))) *
          (((1\<^sub>m 2) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m 
            |Deutsch.one\<rangle>)) \<Otimes> ((SWAP_up (Suc n)) * ( |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> 
            |state_basis 1 (j mod 2)\<rangle>)))"
      using mult_distr_tensor
      by (smt (verit, del_insts) SWAP_up_carrier_mat carrier_matD(2) dim_col_mat(1) 
          dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat index_add_mat(2) index_add_mat(3) 
          index_one_mat(3) index_smult_mat(2) index_smult_mat(3) index_unit_vec(3) ket_vec_def 
          one_power2 pos2 power_Suc2 power_one_right state_basis_def 
          zero_less_one_class.zero_less_one zero_less_power)   
    also have "\<dots> = (((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) \<Otimes> (1\<^sub>m (2^n)))) *
          (( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m 
            |one\<rangle>) \<Otimes> ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>))"
      using SWAP_up_action jeq 
      by (smt (verit, best) Suc index_add_mat(2) index_smult_mat(2) jm2sn_def ket_one_is_state 
          left_mult_one_mat' mod_less_divisor pos2 power_one_right state.dim_row zero_less_power)
    also have "\<dots> = (((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) \<Otimes> (1\<^sub>m (2^n)))) *
          ((( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m 
            |one\<rangle>) \<Otimes>  |state_basis 1 (j mod 2)\<rangle>) \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>)"
      using tensor_mat_is_assoc by presburger
    also have "\<dots> = ((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (((control2 (R (Suc (Suc n))) \<Otimes> (1\<^sub>m (2^n)))) *
          ((( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m 
            |one\<rangle>) \<Otimes>  |state_basis 1 (j mod 2)\<rangle>) \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>))"
    proof (rule assoc_mult_mat)
      show "1\<^sub>m 2 \<Otimes> SWAP_down (Suc n) \<in> carrier_mat (2^Suc (Suc n)) (2^Suc (Suc n))"
        using SWAP_down_carrier_mat 
        by (metis One_nat_def SWAP_down.simps(2) power_Suc power_one_right tensor_carrier_mat)
      show "control2 (R (Suc (Suc n))) \<Otimes> 1\<^sub>m (2 ^ n) \<in> carrier_mat (2^Suc (Suc n)) (2^Suc (Suc n))"
        using control2_carrier_mat by simp
      show "|Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n)
             \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>
            \<in> carrier_mat (2 ^ Suc (Suc n)) 1"
        using state_basis_carrier_mat ket_vec_def
        by (simp add: carrier_matI state_basis_def)
    qed
    also have "\<dots> = ((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * (((control2 (R (Suc (Suc n)))) *
              (( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |one\<rangle>)
            \<Otimes> |state_basis 1 (j mod 2)\<rangle>)) \<Otimes> ((1\<^sub>m (2^n)) * |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>))"
      using mult_distr_tensor 
      by (smt (verit, del_insts) SWAP_nrows SWAP_tensor carrier_matD(1) carrier_matD(2) 
          carrier_matI control2_carrier_mat dim_col_tensor_mat index_add_mat(2) index_add_mat(3) 
          index_mult_mat(2) index_one_mat(3) index_smult_mat(2) index_smult_mat(3) ket_one_is_state
          less_numeral_extra(1) one_power2 power_Suc2 power_one_right state_basis_carrier_mat
          state_def zero_less_numeral zero_less_power)
    also have "\<dots> = ((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * 
               (( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat j / 2 ^ Suc (Suc n)) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
               |state_basis 1 (j mod 2)\<rangle> \<Otimes> ((1\<^sub>m (2^n)) * |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>))"
    proof (rule disjE)
      show "j mod 2 = 0 \<or> j mod 2 = 1" by auto
    next
      assume jm0:"j mod 2 = 0"
      hence jid:"j / 2 = j div 2" by auto
      have "(control2 (R (Suc (Suc n)))) *
              (( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |one\<rangle>)
              \<Otimes> |state_basis 1 (j mod 2)\<rangle>) = 
            (control2 (R (Suc (Suc n)))) *
              (( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |one\<rangle>)
              \<Otimes> |zero\<rangle>)"
        using state_basis_def jm0 by fastforce
      also have "\<dots> = (( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |one\<rangle>)
              \<Otimes> |zero\<rangle>)"
        using control2_zero by (simp add: ket_vec_def)
      also have "\<dots> = ( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat j / 2 ^ Suc (Suc n)) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
                        |zero\<rangle>"
        using jid 
        by (smt (verit, del_insts) dbl_simps(3) dbl_simps(5) divide_divide_eq_left numerals(1) 
            of_nat_1 of_nat_numeral of_real_divide of_real_of_nat_eq power_Suc
            times_divide_eq_right)
      finally show "(1\<^sub>m 2 \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) * ( |Deutsch.zero\<rangle> +
                    exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m
                    |Deutsch.one\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) \<Otimes> 1\<^sub>m (2 ^ n) *
                    |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>) = (1\<^sub>m 2 \<Otimes> SWAP_down (Suc n)) *
                  ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j /
                    2 ^ Suc (Suc n)) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle> \<Otimes> 1\<^sub>m (2 ^ n) *
                    |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>)" 
        by (metis jm0 power_one_right state_basis_def)
    next
      assume jm1:"j mod 2 = 1"
      have "(control2 (R (Suc (Suc n)))) *
              (( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |one\<rangle>)
              \<Otimes> |state_basis 1 (j mod 2)\<rangle>) = 
            (control2 (R (Suc (Suc n)))) *
              (( |Deutsch.zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |one\<rangle>)
              \<Otimes> |one\<rangle>)"
        using jm1 state_basis_def by fastforce
      also have "\<dots> = ((R (Suc (Suc n))) * 
                      ( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |one\<rangle>))
                      \<Otimes> |one\<rangle>"
        using control2_one by (simp add: ket_vec_def R_def mat_of_cols_list_def)
      also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^(Suc (Suc n))) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> |one\<rangle>"
        using R_action
        by (metis assms jm1)
      finally show "(1\<^sub>m 2 \<Otimes> SWAP_down (Suc n)) * (control2 (R (Suc (Suc n))) * ( |Deutsch.zero\<rangle> +
                    exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m
                    |Deutsch.one\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) \<Otimes> 1\<^sub>m (2 ^ n) *
                    |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>) =
                    (1\<^sub>m 2 \<Otimes> SWAP_down (Suc n)) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> * 
                    complex_of_real pi * complex_of_nat j / 2 ^ Suc (Suc n)) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
                 |state_basis 1 (j mod 2)\<rangle> \<Otimes> 1\<^sub>m (2 ^ n) * |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>)" 
        by (metis jm1 power_one_right state_basis_def)
    qed
    also have "\<dots> = ((1\<^sub>m 2) \<Otimes> SWAP_down (Suc n)) * 
                    (( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat j / 2 ^ Suc (Suc n)) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
                  ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> ((1\<^sub>m (2^n)) * 
                    |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>)))"
      using tensor_mat_is_assoc ket_vec_def by auto
    also have "\<dots> = ( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat j / 2 ^ Suc (Suc n)) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
                    ((SWAP_down (Suc n)) * ( |state_basis 1 (j mod 2)\<rangle> \<Otimes> ((1\<^sub>m (2^n)) * 
                    |state_basis n (j mod 2 ^ Suc n div 2)\<rangle>)))"
      using mult_distr_tensor
      by (smt (verit, del_insts) SWAP_down_carrier_mat carrier_matD(1) carrier_matD(2) 
          dim_col_tensor_mat dim_row_tensor_mat index_add_mat(2) index_add_mat(3) index_one_mat(3)
          index_smult_mat(2) index_smult_mat(3) ket_one_is_state left_mult_one_mat' one_power2 pos2
          power.simps(2) power_one_right state_basis_carrier_mat state_def 
          zero_less_one_class.zero_less_one zero_less_power)
    also have "\<dots> = ( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat j / 2 ^ Suc (Suc n)) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
                    ( |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>)"
      using SWAP_down_action jeq 
      by (metis Suc dim_row_mat(1) index_unit_vec(3) jm2sn_def ket_vec_def left_mult_one_mat' 
          mod_less_divisor pos2 state_basis_def zero_less_power)
    finally show "control (Suc (Suc n)) (R (Suc (Suc n))) * ( |Deutsch.zero\<rangle> + exp (2 * \<i> *
                  complex_of_real pi * complex_of_nat (j div 2) / 2 ^ Suc n) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
                  |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes> |state_basis 1 (j mod 2)\<rangle>) =
                  |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j /
                  2 ^ Suc (Suc n)) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes> |state_basis n (j mod 2 ^ Suc n div 2)\<rangle> \<Otimes>
                  |state_basis 1 (j mod 2)\<rangle>"
      using tensor_mat_is_assoc ket_vec_def by auto
  qed
qed


text \<open>Action of the controlled rotations subcircuit\<close>

lemma controlled_rotations_ind:
  "\<forall>j. j < 2 ^ Suc n \<longrightarrow> 
  controlled_rotations (Suc n) * 
  (( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat (j div 2^n))/2) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> |state_basis n (j mod 2^n)\<rangle>) =
  ( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> |state_basis n (j mod 2^n)\<rangle>" 
proof (induct n)
  case 0
  then show ?case
  proof (rule allI)
    fix j::nat
    show "j < 2 ^ Suc 0 \<longrightarrow>
         controlled_rotations (Suc 0) * ( |zero\<rangle> +
          exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ 0) / 2) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
          |state_basis 0 (j mod 2 ^ 0)\<rangle>) =
         |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc 0) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
         |state_basis 0 (j mod 2 ^ 0)\<rangle>"
    proof
      assume "j < 2 ^ Suc 0"
      hence j2:"j < 2" by auto
      have "controlled_rotations (Suc 0) * ( |zero\<rangle> +
            exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ 0) / 2) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
            |state_basis 0 (j mod 2 ^ 0)\<rangle>) = 
            (1\<^sub>m 2)  * ( |zero\<rangle> +
            exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ 0) / 2) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
            |state_basis 0 (j mod 2 ^ 0)\<rangle>)"
        using controlled_rotations.simps by simp
      also have "\<dots> = |zero\<rangle> +
                      exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ 0) / 2) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
                      |state_basis 0 (j mod 2 ^ 0)\<rangle>"
        using left_mult_one_mat by (simp add: ket_vec_def state_basis_def)
      also have "\<dots> = |zero\<rangle> +
                      exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2^Suc 0) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
                      |state_basis 0 (j mod 2 ^ 0)\<rangle>"
        by auto
      finally show "controlled_rotations (Suc 0) * ( |zero\<rangle> +
                    exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ 0) / 2) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
                    |state_basis 0 (j mod 2 ^ 0)\<rangle>) =
                    |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc 0) \<cdot>\<^sub>m |one\<rangle>
                    \<Otimes> |state_basis 0 (j mod 2 ^ 0)\<rangle>"
        by this
    qed
  qed
next
  case (Suc n')
  define n where "n = Suc n'"
  assume HI:" \<forall>j<2 ^ Suc n'. controlled_rotations (Suc n') * ( |zero\<rangle> +
             exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ n') / 2) \<cdot>\<^sub>m |one\<rangle> \<Otimes>
             |state_basis n' (j mod 2 ^ n')\<rangle>) =
            |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc n') \<cdot>\<^sub>m
            |Deutsch.one\<rangle> \<Otimes> |state_basis n' (j mod 2 ^ n')\<rangle>"
  show "\<forall>j<2 ^ Suc (Suc n').
            controlled_rotations (Suc (Suc n')) *
            ( |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * 
              complex_of_nat (j div 2 ^ Suc n') / 2) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
             |state_basis (Suc n') (j mod 2 ^ Suc n')\<rangle>) =
            |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * 
            complex_of_nat j / 2 ^ Suc (Suc n')) \<cdot>\<^sub>m |Deutsch.one\<rangle> \<Otimes>
            |state_basis (Suc n') (j mod 2 ^ Suc n')\<rangle>"
  proof (rule allI)
    fix j::nat
    show "j < 2 ^ Suc (Suc n') \<longrightarrow>
         controlled_rotations (Suc (Suc n')) * ( |Deutsch.zero\<rangle> +
          exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ Suc n') / 2) \<cdot>\<^sub>m
          |Deutsch.one\<rangle> \<Otimes> |state_basis (Suc n') (j mod 2 ^ Suc n')\<rangle>) =
         |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc (Suc n')) \<cdot>\<^sub>m
         |Deutsch.one\<rangle> \<Otimes> |state_basis (Suc n') (j mod 2 ^ Suc n')\<rangle>"
    proof 
      assume jass:"j < 2 ^ Suc (Suc n')"
      show "controlled_rotations (Suc (Suc n')) * ( |Deutsch.zero\<rangle> +
            exp (2 * \<i> * complex_of_real pi * complex_of_nat (j div 2 ^ Suc n') / 2) \<cdot>\<^sub>m
            |Deutsch.one\<rangle> \<Otimes> |state_basis (Suc n') (j mod 2 ^ Suc n')\<rangle>) =
            |Deutsch.zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ Suc (Suc n'))\<cdot>\<^sub>m
            |Deutsch.one\<rangle> \<Otimes> |state_basis (Suc n') (j mod 2 ^ Suc n')\<rangle>"
      proof -
        define jd2n jm2n where "jd2n = j div 2^n" and "jm2n = j mod 2^n"
        define jlast where "jlast = jm2n mod 2"
        define jmm where "jmm = jm2n div 2"
        define jd2 where "jd2 = j div 2"
        have jlastj:"jlast = j mod 2" using jlast_def jm2n_def 
          by (metis less_Suc_eq_0_disj less_Suc_eq_le mod_mod_power_cancel n_def power_Suc0_right)
        have "controlled_rotations (Suc n) * ( |Deutsch.zero\<rangle> +
            exp (2 * \<i> * complex_of_real pi * complex_of_nat jd2n / 2) \<cdot>\<^sub>m
            |Deutsch.one\<rangle> \<Otimes> |state_basis n jm2n\<rangle>) = 
            ((control (Suc n) (R (Suc n))) * ((controlled_rotations n) \<Otimes> (1\<^sub>m 2))) * ( |zero\<rangle> +
            exp (2 * \<i> * complex_of_real pi * complex_of_nat jd2n / 2) \<cdot>\<^sub>m
            |Deutsch.one\<rangle> \<Otimes> |state_basis n jm2n\<rangle>)"
          using controlled_rotations.simps n_def by simp
        also have "\<dots> = ((control (Suc n) (R (Suc n))) * ((controlled_rotations n) \<Otimes> (1\<^sub>m 2))) * 
            ( |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat jd2n / 2) \<cdot>\<^sub>m  |one\<rangle> \<Otimes> 
            ( |state_basis n' jmm\<rangle> \<Otimes> |state_basis 1 jlast\<rangle>))"
          using state_basis_dec' jass n_def jlast_def jmm_def jm2n_def mod_less_divisor pos2
          by presburger
        also have "\<dots> = (control (Suc n) (R (Suc n))) * ((((controlled_rotations n) \<Otimes> (1\<^sub>m 2))) * 
            ( |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat jd2n / 2) \<cdot>\<^sub>m  |one\<rangle> \<Otimes> 
            ( |state_basis n' jmm\<rangle> \<Otimes> |state_basis 1 jlast\<rangle>)))"
        proof (rule assoc_mult_mat)
          show "control (Suc n) (R (Suc n)) \<in> carrier_mat (2^(Suc n)) (2^(Suc n))"
            using control_carrier_mat n_def by blast
          show "controlled_rotations n \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (2 ^ Suc n) (2 ^ Suc n)"
            using controlled_rotations_carrier_mat n_def
            by (metis One_nat_def controlled_rotations.simps(2) power_Suc2 power_one_right 
                tensor_carrier_mat)
          show "|zero\<rangle> + exp (2*\<i>*pi*complex_of_nat jd2n /2) \<cdot>\<^sub>m |one\<rangle> \<Otimes> ( |state_basis n' jmm\<rangle> \<Otimes>
                |state_basis 1 jlast\<rangle>) \<in> carrier_mat (2 ^ Suc n) 1"
            using state_basis_carrier_mat ket_vec_def 
            by (simp add: carrier_matI n_def state_basis_def)
        qed
        also have "\<dots> = (control (Suc n) (R (Suc n))) * ((((controlled_rotations n) \<Otimes> (1\<^sub>m 2))) * 
            (( |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat jd2n / 2) \<cdot>\<^sub>m  |one\<rangle> \<Otimes> 
             |state_basis n' jmm\<rangle>) \<Otimes> |state_basis 1 jlast\<rangle>))"
          using tensor_mat_is_assoc control_carrier_mat n_def controlled_rotations_carrier_mat
            state_basis_carrier_mat ket_vec_def by simp
        also have "\<dots> = (control (Suc n) (R (Suc n))) * (((controlled_rotations n) *
                        (( |zero\<rangle> + exp (2 * \<i> * pi * complex_of_nat jd2n / 2) \<cdot>\<^sub>m  |one\<rangle>) \<Otimes>
                        |state_basis n' jmm\<rangle>)) \<Otimes> ((1\<^sub>m 2) * |state_basis 1 jlast\<rangle>))"
          using mult_distr_tensor control_carrier_mat n_def controlled_rotations_carrier_mat
            state_basis_carrier_mat ket_vec_def 
          by (smt (verit) carrier_matD(1) carrier_matD(2) dim_col_tensor_mat dim_row_tensor_mat
              index_add_mat(2) index_add_mat(3) index_one_mat(3) index_smult_mat(2) 
              index_smult_mat(3) ket_one_is_state one_power2 pos2 power_Suc power_one_right 
              state_def zero_less_one_class.zero_less_one zero_less_power)
        also have "\<dots> = (control (Suc n) (R (Suc n))) * 
                        (( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat jd2 / 2^n) \<cdot>\<^sub>m
                        |one\<rangle> \<Otimes> |state_basis n' (jd2 mod 2 ^ n')\<rangle>) \<Otimes> 
                        ((1\<^sub>m 2) * |state_basis 1 jlast\<rangle>))"
          using HI jd2_def n_def
          by (smt (verit, del_insts) Suc_eq_plus1 div_exp_eq div_exp_mod_exp_eq jass jd2n_def 
              jm2n_def jmm_def less_power_add_imp_div_less plus_1_eq_Suc power_one_right)
        also have "\<dots> = (control (Suc n) (R (Suc n))) * 
                        (( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat jd2 / 2^n) \<cdot>\<^sub>m
                        |one\<rangle> \<Otimes> |state_basis n' jmm\<rangle>) \<Otimes> 
                        |state_basis 1 jlast\<rangle>)"
          using jmm_def jd2_def 
          by (metis div_exp_mod_exp_eq jm2n_def left_mult_one_mat n_def plus_1_eq_Suc
              power_one_right state_basis_carrier_mat)
        also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
                        |state_basis n' jmm\<rangle> \<Otimes> |state_basis 1 jlast\<rangle>"
          using controlR_action jmm_def jlast_def jd2_def n_def jm2n_def jass jlastj by presburger
        also have "\<dots> = ( |zero\<rangle> + exp (2*\<i>*pi*complex_of_nat j / 2^Suc n) \<cdot>\<^sub>m |one\<rangle>) \<Otimes>
                        |state_basis n jm2n\<rangle>"
          using state_basis_dec' jm2n_def jmm_def jlast_def
          by (metis mod_less_divisor n_def pos2 tensor_mat_is_assoc zero_less_power)
        finally show ?thesis using jm2n_def n_def jd2n_def by meson
      qed
    qed
  qed
qed


lemma controlled_rotations_on_first_qubit:
  assumes "j < 2 ^ Suc n"
  shows "controlled_rotations (Suc n) *
        (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat (j div 2^n))/2) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> 
        |state_basis n (j mod 2^n)\<rangle>) =
        (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes> |state_basis n (j mod 2^n)\<rangle>)"
proof -
  have "controlled_rotations (Suc n) *
        (1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat (j div 2^n))/2) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> 
        |state_basis n (j mod 2^n)\<rangle>) = 
        controlled_rotations (Suc n) *
        (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat (j div 2^n))/2) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> 
        |state_basis n (j mod 2^n)\<rangle>))"
    using smult_mat_def tensor_mat_def 
    by (smt (verit) One_nat_def carrier_matD(2) index_add_mat(3) index_smult_mat(3) lessI power_one_right smult_tensor1 state_basis_carrier_mat state_basis_def)
  also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m (controlled_rotations (Suc n) * 
                  (( |zero\<rangle> + exp(2*\<i>*pi*(complex_of_nat (j div 2^n))/2) \<cdot>\<^sub>m |one\<rangle>) \<Otimes> 
                  |state_basis n (j mod 2^n)\<rangle>))"
    using mult_smult_distrib controlled_rotations_carrier_mat state_basis_carrier_mat
    by (smt (verit) carrier_matI dim_row_mat(1) dim_row_tensor_mat index_add_mat(2) 
        index_smult_mat(2) index_unit_vec(3) ket_vec_def power_Suc state_basis_def)
  also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m 
                  (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes> |state_basis n (j mod 2^n)\<rangle>)"
    using assms controlled_rotations_ind ket_vec_def by simp
  finally show ?thesis by this
qed


text \<open>More useful lemmas:\<close>

lemma exp_j:
  assumes "l < Suc n"
  shows "exp (2*\<i>*pi*j/(2^l)) = exp (2*\<i>*pi*(j mod 2^n)/(2^l))"
proof -
  define jd jm where "jd = j div 2^n" and "jm = j mod 2^n"
  have 0:"real (2^n)/(2^l) = (2^(n-l))"
  proof -
    have 1:"(2::nat) \<noteq> 0" by simp
    have 2:"l \<le> n" using assms by simp
    show ?thesis
      using 1 2 power_diff
      by (metis numeral_power_eq_of_nat_cancel_iff zero_neq_numeral)
  qed
  have "j = jd*(2^n) + jm" using jd_def jm_def by presburger
  hence "exp (2*\<i>*pi*j/(2^l)) = exp (2*pi*\<i>*(jd*(2^n) + jm)/(2^l))"
    by (simp add: mult.commute mult.left_commute)
  also have "\<dots> = exp (2*pi*\<i>*(jd*(2^n))/(2^l) + 2*\<i>*pi*jm/(2^l))"
    by (simp add: add_divide_distrib distrib_left mult.left_commute semigroup_mult_class.mult.assoc)
  also have "\<dots> = exp (2*pi*\<i>*(jd*(2^n))/(2^l)) * exp (2*\<i>*pi*jm/(2^l))" using exp_add by blast
  also have "\<dots> = exp (2*pi*\<i>*jd*((2^n)/(2^l))) * exp (2*\<i>*pi*jm/(2^l))"
    by (simp add: semigroup_mult_class.mult.assoc)
  also have "\<dots> = exp (2*pi*\<i>*jd*((2^(n-l)))) * exp (2*\<i>*pi*jm/(2^l))" 
    using 0 by (smt (verit) dbl_simps(3) dbl_simps(5) numerals(1) of_nat_1 of_nat_numeral 
        of_nat_power of_real_divide of_real_of_nat_eq)
  also have "\<dots> = exp ((2*pi*\<i>*jd)*(of_nat (2^(n-l)))) * exp (2*\<i>*pi*jm/(2^l))" by auto
  also have "\<dots> = (exp (2*pi*\<i>))^(2^(n-l)) * exp (2*\<i>*pi*jm/(2^l))" 
    using exp_of_nat2_mult by (smt (verit, best) cis_2pi cis_conv_exp exp_power_int exp_zero 
        mult.commute mult_zero_right)
  also have "\<dots> = 1^(2^(n-l)) * exp (2*\<i>*pi*jm/(2^l))" using exp_two_pi_i by auto
  also have "\<dots> = exp (2*\<i>*pi*jm/(2^l))" by auto
  finally show ?thesis using jd_def jm_def by simp
qed



lemma kron_list_fun[simp]:
  "\<forall>x. List.member xs x \<longrightarrow> f x = g x \<Longrightarrow> kron f xs = kron g xs"
proof (induct xs)
  case Nil
  show "kron f [] = kron g []" by simp
next
  fix a xs
  assume HI:"(\<forall>x. List.member xs x \<longrightarrow> f x = g x \<Longrightarrow> kron f xs = kron g xs)"
  show "\<forall>x. List.member (a # xs) x \<longrightarrow> f x = g x \<Longrightarrow> kron f (a # xs) = kron g (a # xs)"
  proof -
    assume 1:"\<forall>x. List.member (a # xs) x \<longrightarrow> f x = g x"
    show "kron f (a # xs) = kron g (a # xs)"
    proof -
      from 1 have "List.member (a # xs) a \<longrightarrow> f a = g a" by auto
      moreover have "List.member (a # xs) a" by (simp add: List.member_rec(1))
      ultimately have 2:"f a = g a" by auto
      have "kron f (a#xs) = f a \<Otimes> kron f xs" by simp
      also have "\<dots> = g a \<Otimes> kron f xs" using 2 by simp
      also have "\<dots> = g a \<Otimes> kron g xs" using HI 1 by (simp add: member_rec(1))
      also have "\<dots> = kron g (a#xs)" using kron.simps(2) by simp
      finally show ?thesis by this
    qed
  qed
qed


lemma member_rev:
  shows "List.member (rev xs) x = List.member xs x"
proof (induct xs)
  show "List.member (rev []) x = List.member [] x" by simp
next
  case (Cons a xs)
  assume HI:"List.member (rev xs) x = List.member xs x"
  have "List.member (rev (a#xs)) x = List.member ((rev xs)@[a]) x" using rev_append by auto
  also have "\<dots> = (x \<in> set ((rev xs) @ [a]))" using List.member_def by metis
  also have "\<dots> = (x \<in> set (rev xs) \<union> set [a])" using set_append by metis
  also have "\<dots> = (x \<in> set [a] \<or> x \<in> set (rev xs))" by blast
  also have "\<dots> = (x = a \<or> List.member (rev xs) x)" using List.member_def by fastforce
  also have "\<dots> = (x = a \<or> List.member xs x)" using HI by metis
  also have "\<dots> = List.member (a#xs) x" using List.member_rec(1) by metis
  finally show "List.member (rev (a#xs)) x = List.member (a#xs) x" by this
qed


lemma kron_j:
  shows "kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..n])) =
         kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*(complex_of_nat (j mod 2^n))/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
         (map nat (rev [1..n]))"
proof -
  define fj fjm where "fj = (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>)"
    and "fjm = (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*(complex_of_nat (j mod 2^n))/(2^l)) \<cdot>\<^sub>m |one\<rangle>)" 
  have "\<forall>x. ((List.member (map nat (rev [1..n])) x) \<longrightarrow> (x < Suc n))"
  proof (rule allI)
    fix x
    show "List.member (map nat (rev [1..int n])) x \<longrightarrow> x < Suc n"
    proof
      assume "List.member (map nat (rev [1..int n])) x"
      hence "List.member (rev (map nat [1..int n])) x" using rev_map by metis
      hence "List.member (map nat [1..int n]) x" using member_rev by metis
      hence "x \<in> set (map nat [1..int n])" using List.member_def by metis
      hence "x \<in> {1..n}" by auto
      thus "x < Suc n" by auto
    qed
  qed
  hence "\<forall>x. ((List.member (map nat (rev [1..n])) x) \<longrightarrow> 
             (exp (2*\<i>*pi*j/(2^x)) = exp (2*\<i>*pi*(j mod 2^n)/(2^x))))"
    using exp_j
    by (metis (mono_tags, lifting) of_int_of_nat_eq of_nat_numeral of_nat_power zmod_int)
  hence "\<forall>x. ((List.member (map nat (rev [1..n])) x) \<longrightarrow> (fj x = fjm x))"
    using fj_def fjm_def by presburger
  hence "kron fj (map nat (rev [1..n])) = kron fjm (map nat (rev [1..n]))"
    by simp
  thus ?thesis using fj_def fjm_def by auto
qed


text \<open>We proof that the QFT circuit is correct:\<close>

theorem QFT_is_correct:
  shows "\<forall>j. j < 2^n \<longrightarrow> (QFT n) * |state_basis n j\<rangle> = reverse_QFT_product_representation j n"
proof (induct n rule: QFT.induct)
  case 1
  thus ?case
  proof (rule allI)
    fix j::nat
    show "j < 2 ^ 0 \<longrightarrow> QFT 0 * |state_basis 0 j\<rangle> = reverse_QFT_product_representation j 0"
    proof 
      assume "j < 2 ^ 0"
      hence j0:"j = 0" by auto
      have "QFT 0 * |state_basis 0 j\<rangle> = (1\<^sub>m 1) * |state_basis 0 j\<rangle>" using QFT.simps by simp
      also have "\<dots> = |unit_vec 1 j\<rangle>" using state_basis_def
        by (metis left_mult_one_mat power_0 state_basis_carrier_mat)
      also have "\<dots> = (1\<^sub>m 1)" using unit_vec_def unit_vec_carrier ket_vec_def j0 by auto
      also have "\<dots> = reverse_QFT_product_representation j 0"
        using reverse_QFT_product_representation_def by auto
      finally show "QFT 0 * |state_basis 0 j\<rangle> = reverse_QFT_product_representation j 0" by this
    qed
  qed
next
  case 2
  thus ?case
  proof (rule allI)
    fix j::nat
    show "j < 2 ^ Suc 0 \<longrightarrow>
         QFT (Suc 0) *
         |state_basis (Suc 0) j\<rangle> =
         reverse_QFT_product_representation j
          (Suc 0)"
    proof 
      assume a1:"j < 2^Suc 0"
      then show "QFT (Suc 0) * |state_basis (Suc 0) j\<rangle> = 
                 reverse_QFT_product_representation j (Suc 0)"
      proof -
        have "QFT (Suc 0) * |state_basis (Suc 0) j\<rangle> = H * |unit_vec (2^(Suc 0)) j\<rangle>"
          using QFT.simps(2) state_basis_def by auto
        also have "\<dots> = reverse_QFT_product_representation j (Suc 0)"
        proof (rule disjE)
          show "j=0 \<or> j=1" using a1 by auto
        next
          assume j0:"j=0"
          hence "H * |unit_vec (2^(Suc 0)) j\<rangle> = H * |unit_vec (2^(Suc 0)) 0\<rangle>" by simp
          also have "\<dots> = H * |zero\<rangle>" by auto
          also have "\<dots> = mat_of_cols_list 2 [[1/sqrt(2),1/sqrt(2)]]"
            using H_on_ket_zero by simp
          also have "\<dots> = 1/sqrt(2) \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,1]])"
          proof 
            fix i j::nat
            define \<psi>1 \<psi>2 where "\<psi>1 = mat_of_cols_list 2 [[1/sqrt(2),1/sqrt(2)]]" and 
              "\<psi>2 = 1/sqrt(2) \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,1]])"
            assume "i < dim_row \<psi>2" and "j < dim_col \<psi>2"
            hence a2:"i \<in> {0,1} \<and> j=0"
              by (simp add: Tensor.mat_of_cols_list_def \<psi>2_def less_Suc_eq_0_disj numerals(2))
            have "\<psi>1 $$ (0,0) = 1/sqrt 2" using mat_of_cols_list_def \<psi>1_def by simp
            moreover have "\<psi>1 $$ (1,0) = 1/sqrt 2" using mat_of_cols_list_def \<psi>1_def by simp
            moreover have "\<psi>2 $$ (0,0) = 1/sqrt 2" 
              using smult_mat_def mat_of_cols_list_def \<psi>2_def by simp
            moreover have "\<psi>2 $$ (1,0) = 1/sqrt 2" 
              using smult_mat_def mat_of_cols_list_def \<psi>2_def by simp
            ultimately show "\<psi>1 $$ (i,j) = \<psi>2 $$ (i,j)" using a2 by auto
          next
            define \<psi>1 \<psi>2 where "\<psi>1 = mat_of_cols_list 2 [[1/sqrt(2),1/sqrt(2)]]" and 
              "\<psi>2 = 1/sqrt(2) \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,1]])"
            show "dim_row \<psi>1 = dim_row \<psi>2" using \<psi>1_def \<psi>2_def Tensor.mat_of_cols_list_def by simp
          next
            define \<psi>1 \<psi>2 where "\<psi>1 = mat_of_cols_list 2 [[1/sqrt(2),1/sqrt(2)]]" and 
              "\<psi>2 = 1/sqrt(2) \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,1]])"
            show "dim_col \<psi>1 = dim_col \<psi>2" using \<psi>1_def \<psi>2_def Tensor.mat_of_cols_list_def by simp
          qed
          also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + |one\<rangle>)"
          proof -
            have "mat_of_cols_list 2 [[1,1]] = |zero\<rangle> + |one\<rangle>"
            proof 
              fix i j::nat 
              define s1 s2 where "s1 = mat_of_cols_list 2 [[1,1]]" and "s2 = |zero\<rangle> + |one\<rangle>"
              assume "i < dim_row s2" and "j < dim_col s2"
              hence "i \<in> {0,1} \<and> j = 0" using index_add_mat 
                by (simp add: ket_vec_def less_Suc_eq numerals(2) s2_def)
              thus "s1 $$ (i,j) = s2 $$ (i,j)" using s1_def s2_def mat_of_cols_list_def 
                  \<open>i < dim_row s2\<close> ket_one_to_mat_of_cols_list by force
            next
              define s1 s2 where "s1 = mat_of_cols_list 2 [[1,1]]" and "s2 = |zero\<rangle> + |one\<rangle>"
              thus "dim_row s1 = dim_row s2" using mat_of_cols_list_def by (simp add: ket_vec_def)
            next
              define s1 s2 where "s1 = mat_of_cols_list 2 [[1,1]]" and "s2 = |zero\<rangle> + |one\<rangle>"
              thus "dim_col s1 = dim_col s2" using mat_of_cols_list_def by (simp add: ket_vec_def)
            qed
            thus ?thesis by simp
          qed
          also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m (kron (\<lambda> l. |zero\<rangle> + |one\<rangle>) [1])" using kron.simps by auto
          also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m (kron (\<lambda> l. |zero\<rangle> + exp (2*\<i>*pi*0/(2^l)) \<cdot>\<^sub>m |one\<rangle>) [1])"
            using exp_zero smult_mat_def by auto
          also have "\<dots> = reverse_QFT_product_representation 0 (Suc 0)"
            using reverse_QFT_product_representation_def rev_def map_def by auto
          finally show "H * |unit_vec (2 ^ Suc 0) j\<rangle> = reverse_QFT_product_representation j (Suc 0)"
            using j0 by simp
        next
          assume j1:"j = 1"
          hence "H * |unit_vec (2 ^ Suc 0) j\<rangle> = H * |one\<rangle>" by simp
          also have "\<dots> = mat_of_cols_list 2 [[1/sqrt(2), -1/sqrt(2)]]" using H_on_ket_one by simp
          also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,-1]])"
          proof
            fix i j::nat
            define \<phi>1 \<phi>2 where "\<phi>1 = mat_of_cols_list 2 [[1/sqrt(2), -1/sqrt(2)]]" and
              "\<phi>2 = 1/sqrt 2 \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,-1]])"
            assume "i < dim_row \<phi>2" and "j < dim_col \<phi>2"
            hence a3:"i \<in> {0,1} \<and> j = 0" 
              using \<phi>2_def mat_of_cols_list_def numerals(2) less_2_cases by simp
            have "\<phi>1 $$ (0,0) = \<phi>2 $$ (0,0)"
              using \<phi>1_def \<phi>2_def smult_def mat_of_cols_list_def by simp
            moreover have "\<phi>1 $$ (1,0) = \<phi>2 $$ (1,0)"
              using \<phi>1_def \<phi>2_def smult_def mat_of_cols_list_def by simp
            ultimately show "\<phi>1 $$ (i,j) = \<phi>2 $$ (i,j)" using a3 by auto
          next
            define \<phi>1 \<phi>2 where "\<phi>1 = mat_of_cols_list 2 [[1/sqrt(2), -1/sqrt(2)]]" and
              "\<phi>2 = 1/sqrt 2 \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,-1]])"
            then show "dim_row \<phi>1 = dim_row \<phi>2" using smult_def mat_of_cols_list_def by simp
          next
            define \<phi>1 \<phi>2 where "\<phi>1 = mat_of_cols_list 2 [[1/sqrt(2), -1/sqrt(2)]]" and
              "\<phi>2 = 1/sqrt 2 \<cdot>\<^sub>m (mat_of_cols_list 2 [[1,-1]])"
            then show "dim_col \<phi>1 = dim_col \<phi>2" using smult_def mat_of_cols_list_def by simp
          qed
          also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> - |one\<rangle>)"
          proof -
            have "mat_of_cols_list 2 [[1,-1]] = |zero\<rangle> - |one\<rangle>"
            proof
              fix i j::nat
              define r1 r2 where "r1 = mat_of_cols_list 2 [[1,-1]]" and "r2 = |zero\<rangle> - |one\<rangle>"
              assume "i < dim_row r2" and "j < dim_col r2"
              hence a4:"i \<in> {0,1} \<and> j=0" 
                using ket_vec_def index_add_mat by (simp add: less_2_cases r2_def)
              have "r1 $$ (0,0) = r2 $$ (0,0)" using r1_def r2_def mat_of_cols_list_def
                by (smt (verit, ccfv_threshold) One_nat_def add.commute diff_zero dim_row_mat(1) 
                    index_mat(1) index_mat_of_cols_list ket_one_is_state ket_one_to_mat_of_cols_list 
                    ket_zero_to_mat_of_cols_list list.size(3) list.size(4) minus_mat_def nth_Cons_0 
                    plus_1_eq_Suc pos2 state_def zero_less_one_class.zero_less_one)
              moreover have "r1 $$ (1,0) = r2 $$ (1,0)" 
                using r1_def r2_def mat_of_cols_list_def ket_vec_def by simp
              ultimately show "r1 $$ (i,j) = r2 $$ (i,j)" using a4 by auto
            next
              define r1 r2 where "r1 = mat_of_cols_list 2 [[1,-1]]" and "r2 = |zero\<rangle> - |one\<rangle>"
              thus "dim_row r1 = dim_row r2" using mat_of_cols_list_def ket_vec_def by simp
            next
              define r1 r2 where "r1 = mat_of_cols_list 2 [[1,-1]]" and "r2 = |zero\<rangle> - |one\<rangle>"
              thus "dim_col r1 = dim_col r2" using mat_of_cols_list_def ket_vec_def by simp
            qed
            thus ?thesis by simp
          qed
          also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m (kron (\<lambda>l. |zero\<rangle> - |one\<rangle>) [1])"
            using kron.simps by auto
          also have "\<dots> = 1/sqrt 2 \<cdot>\<^sub>m (kron (\<lambda>l. |zero\<rangle> + exp (2*\<i>*pi*1/(2^l)) \<cdot>\<^sub>m |one\<rangle>) [1])"
          proof -
            have "exp (2*\<i>*pi*1/(2^1)) = -1" using exp_pi_i by auto
            hence "|zero\<rangle> + exp (2*\<i>*pi*1/(2^1)) \<cdot>\<^sub>m |one\<rangle> = |zero\<rangle> + (-1) \<cdot>\<^sub>m |one\<rangle>" by simp
            also have "\<dots> = |zero\<rangle> - |one\<rangle>" by auto
            thus ?thesis by auto
          qed
          also have "\<dots> = reverse_QFT_product_representation 1 (Suc 0)" 
            using reverse_QFT_product_representation_def by auto
          finally show "H * |unit_vec (2 ^ Suc 0) j\<rangle> = reverse_QFT_product_representation j (Suc 0)"
            using j1 by simp
        qed
        finally show ?thesis by this
      qed
    qed
  qed
next
  case 3
  fix n'::nat
  define n where "n = Suc n'"
  assume HI:"\<forall>j<2 ^ n. QFT n * |state_basis n j\<rangle> = reverse_QFT_product_representation j n"
  show "\<forall>j<2^Suc n.
           QFT (Suc n) * |state_basis (Suc n) j\<rangle> = reverse_QFT_product_representation j (Suc n)"
  proof (rule allI)
    fix j::nat
    show "j < 2 ^ Suc n \<longrightarrow> QFT (Suc n) * |state_basis (Suc n) j\<rangle> =
                            reverse_QFT_product_representation j (Suc n)"
    proof 
      assume aj:"j < 2 ^ Suc n"
      show "QFT (Suc n) *
         |state_basis (Suc n) j\<rangle> =
         reverse_QFT_product_representation j
          (Suc n)"
      proof -
        define jd jm where "jd = j div 2^n" and "jm = j mod 2^n"
        hence "jm < 2^n" by auto
        hence HI_jm:"QFT n * |state_basis n jm\<rangle> = reverse_QFT_product_representation jm n" 
          using HI by auto
        have "(QFT (Suc n)) * |state_basis (Suc n) j\<rangle> = 
        (((1\<^sub>m 2) \<Otimes> (QFT n)) * (controlled_rotations (Suc n)) * (H \<Otimes> ((1\<^sub>m (2^n))))) * 
        |state_basis (Suc n) j\<rangle>"
          using QFT.simps(3) n_def by simp
        also have "\<dots> = (((1\<^sub>m 2) \<Otimes> (QFT n)) * (controlled_rotations (Suc n))) * 
                        (((H \<Otimes> ((1\<^sub>m (2^n))))) * |state_basis (Suc n) j\<rangle>)"
        proof (rule assoc_mult_mat)
          show "(1\<^sub>m 2 \<Otimes> QFT n) * controlled_rotations (Suc n) \<in> carrier_mat (2^(Suc n)) (2^(Suc n))"
          proof (rule mult_carrier_mat)
            show "1\<^sub>m 2 \<Otimes> QFT n \<in> carrier_mat (2 ^ Suc n) (2 ^ Suc n)" by simp
            show "controlled_rotations (Suc n) \<in> carrier_mat (2 ^ Suc n) (2 ^ Suc n)"
              using controlled_rotations_carrier_mat by blast
          qed
        next
          show "H \<Otimes> 1\<^sub>m (2 ^ n) \<in> carrier_mat (2 ^ Suc n) (2 ^ Suc n)"
            using tensor_carrier_mat 
            by (metis QFT.simps(2) QFT_carrier_mat one_carrier_mat power_Suc power_Suc0_right)
        next
          show "|state_basis (Suc n) j\<rangle> \<in> carrier_mat (2 ^ Suc n) 1"
            using state_basis_carrier_mat by blast
        qed
        also have "\<dots> = (((1\<^sub>m 2) \<Otimes> (QFT n)) * (controlled_rotations (Suc n))) *
                        ((1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*jd/2) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes> |state_basis n jm\<rangle>)"
          using aj H_on_first_qubit jd_def jm_def by simp
        also have "\<dots> = ((1\<^sub>m 2) \<Otimes> (QFT n)) * (controlled_rotations (Suc n) *
                        (((1/sqrt 2 \<cdot>\<^sub>m ( |zero\<rangle> + exp(2*\<i>*pi*jd/2) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes> |state_basis n jm\<rangle>)))"
          using assoc_mult_mat tensor_carrier_mat QFT_carrier_mat one_carrier_mat 
            state_basis_carrier_mat
          by (smt (verit, ccfv_threshold) H_on_first_qubit QFT.simps(2) aj 
              controlled_rotations_carrier_mat jd_def jm_def mult_carrier_mat power_Suc 
              power_Suc0_right)
        also have "\<dots> = ((1\<^sub>m 2) \<Otimes> (QFT n)) * 
                        (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes> 
                        |state_basis n jm\<rangle>)"
          using controlled_rotations_on_first_qubit aj jd_def jm_def by simp
        also have "\<dots> = ((1\<^sub>m 2) * (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)))) \<Otimes>
                        ((QFT n) * |state_basis n jm\<rangle>)"
        proof -
          have "dim_col (1\<^sub>m 2) = dim_row (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)))"
          proof -
            have "dim_col (1\<^sub>m 2) = 2" by simp
            moreover have "dim_row (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>))) = 2"
              using smult_carrier_mat mat_of_cols_list_def add_carrier_mat ket_vec_def by simp
            ultimately show ?thesis by simp
          qed
          moreover have "dim_col (QFT n) = dim_row |state_basis n jm\<rangle>"
            using state_basis_carrier_mat QFT_carrier_mat
            by (metis carrier_matD(1) carrier_matD(2))
          moreover have "dim_col (1\<^sub>m 2) > 0" by simp
          moreover have "dim_col (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>))) > 0"
            using smult_carrier_mat mat_of_cols_list_def add_carrier_mat ket_vec_def by simp
          moreover have "dim_col (QFT n) > 0" using QFT_carrier_mat
            by (metis carrier_matD(2) pos2 zero_less_power)
          moreover have "dim_col |state_basis n jm\<rangle> > 0" using state_basis_carrier_mat
            by (simp add: ket_vec_def)
          ultimately show "((1\<^sub>m 2) \<Otimes> (QFT n)) * 
                (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes> |state_basis n jm\<rangle>) =
                ((1\<^sub>m 2) * (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)))) \<Otimes>
                ((QFT n) * |state_basis n jm\<rangle>)" 
            using mult_distr_tensor by (smt (verit, best))
        qed
        also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>))) \<Otimes>
                        reverse_QFT_product_representation jm n"
          using ket_one_is_state state.dim_row HI_jm by auto
        also have "\<dots> = reverse_QFT_product_representation j (Suc n)"
        proof -
          have "(1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>))) \<Otimes>
                reverse_QFT_product_representation jm n =
                (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>))) \<Otimes>
                (1/sqrt (2^n) \<cdot>\<^sub>m (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*jm/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                                 (map nat (rev [1..n]))))"
            using reverse_QFT_product_representation_def by simp
          also have "\<dots> = (1/sqrt 2 \<cdot>\<^sub>m (( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>))) \<Otimes>
                          (1/sqrt (2^n) \<cdot>\<^sub>m (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                          (map nat (rev [1..n]))))"
            using kron_j jm_def by simp
          also have "\<dots> = ((1/sqrt 2)*(1/sqrt (2^n))) \<cdot>\<^sub>m 
                          ((( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes>
                          (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                          (map nat (rev [1..n]))))"
          proof -
            have "dim_col ( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>) > 0"
              by (simp add: ket_vec_def)
            moreover have "dim_col (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                          (map nat (rev [1..n]))) > 0"
              using kron_carrier_mat ket_vec_def
              by (metis (no_types, lifting) calculation carrier_matD(2) dim_col_mat(1) 
                  dim_row_mat(1) index_add_mat(2) index_add_mat(3) index_smult_mat(2) 
                  index_smult_mat(3) index_unit_vec(3))
            ultimately show ?thesis by simp
          qed
          also have "\<dots> = (1/sqrt (2^(Suc n))) \<cdot>\<^sub>m 
                          ((( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes>
                          (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                          (map nat (rev [1..n]))))"
            by (simp add: real_sqrt_mult)
          also have "\<dots> = (1/sqrt (2^(Suc n))) \<cdot>\<^sub>m 
                          (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                          (map nat (rev [1..(Suc n)])))"
          proof -
            define f where "f = (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>)"
            hence "|zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle> = f (Suc n)" by simp
            hence "((( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes>
                   (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                   (map nat (rev [1..n])))) = 
                   (f (Suc n)) \<Otimes> (kron f (map nat (rev [1..n])))"
              using f_def by simp
            also have "\<dots> = kron f ((Suc n)#(map nat (rev [1..n])))"
              using kron.simps(2) by simp
            also have "\<dots> = kron f (map nat (rev [1..(Suc n)]))"
              using map_def rev_append
              by (smt (z3) append_Cons append_self_conv2 list.simps(9) nat_int negative_zless 
                  of_nat_Suc rev_eq_Cons_iff rev_is_Nil_conv upto_rec2)
            finally have "((( |zero\<rangle> + exp(2*\<i>*pi*j/(2^(Suc n))) \<cdot>\<^sub>m |one\<rangle>)) \<Otimes>
                          (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                          (map nat (rev [1..n])))) =
                          (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) 
                          (map nat (rev [1..(Suc n)])))"
              using f_def by simp
            thus ?thesis by simp
          qed
          also have "\<dots> = reverse_QFT_product_representation j (Suc n)"
            using reverse_QFT_product_representation_def by simp
          finally show ?thesis by this
        qed
        finally show ?thesis by this
      qed
    qed
  qed
qed


subsection \<open>QFT with qubits reordering correctness\<close>

lemma SWAP_down_kron:
  assumes "\<forall>m. dim_row (f m) = 2 \<and> dim_col (f m) = 1" 
  shows "SWAP_down (length (x#xs)) * kron f (x#xs) = kron f xs \<Otimes> f x"
proof (induct xs rule: rev_induct)
  case Nil
  have "SWAP_down (length [x]) * kron f [x] = (1\<^sub>m 2) * f x" using SWAP_down.simps(2) kron.simps(2)
    by (metis carrier_matI kron.simps(1) length_0_conv length_Cons right_tensor_id)
  also have "\<dots> = f x" using left_mult_one_mat' assms by auto
  also have "\<dots> = (1\<^sub>m 1) \<Otimes> f x" using left_tensor_id by auto
  also have "\<dots> = kron f [] \<Otimes> f x" using kron.simps by auto
  finally show ?case by this
next
  case (snoc a xs)
  assume HI:"SWAP_down (length (x#xs)) * kron f (x#xs) = kron f xs \<Otimes> f x"
  define n::nat where "n = length xs"
  show ?case
  proof (cases)
    assume Nil:"xs = []"
    hence "n = 0" using n_def by auto
    have "SWAP_down (length (x#xs@[a])) * kron f (x#xs@[a]) =
          SWAP_down (Suc (Suc 0)) * kron f (x#[a])"
      using n_def Nil by simp
    also have "\<dots> = SWAP * kron f (x#[a])" using SWAP_down.simps(3) by simp
    also have "\<dots> = SWAP * ((f x) \<Otimes> (f a))" using kron.simps(2)
      by (metis carrier_matI kron.simps(1) right_tensor_id)
    also have "\<dots> = (f a) \<Otimes> (f x)" using SWAP_tensor assms by auto
    also have "\<dots> = kron f (xs@[a]) \<Otimes> (f x)" using kron.simps Nil
      by (metis carrier_mat_triv kron_cons_right left_tensor_id)
    finally show ?case by this
  next
    assume NNil:"xs \<noteq> []"
    hence "n > 0" using n_def by auto
    hence e:"\<exists>m. n = Suc m" by (simp add: gr0_implies_Suc)
    have "SWAP_down (length (x#xs@[a])) * kron f (x#xs@[a]) =
          SWAP_down (Suc (Suc n)) * kron f (x#xs@[a])"
      using n_def by auto
    also have "\<dots> = ((1\<^sub>m (2^n)) \<Otimes> SWAP) * ((SWAP_down (Suc n)) \<Otimes> (1\<^sub>m 2)) * kron f (x#xs@[a])"
      using SWAP_down.simps e by auto
    also have "\<dots> = ((1\<^sub>m (2^n)) \<Otimes> SWAP) * (((SWAP_down (Suc n)) \<Otimes> (1\<^sub>m 2)) * kron f (x#xs@[a]))"
    proof (rule assoc_mult_mat)
      show "((1\<^sub>m (2^n)) \<Otimes> SWAP) \<in> carrier_mat (2^(Suc (Suc n))) (2^(Suc (Suc n)))"
      proof -
        have "(1\<^sub>m (2^n)) \<in> carrier_mat (2^n) (2^n)" by simp
        moreover have "SWAP \<in> carrier_mat 4 4" using SWAP_carrier_mat by simp
        ultimately show ?thesis using tensor_carrier_mat
          by (smt (verit, ccfv_threshold) mult_numeral_left_semiring_numeral num_double 
              numeral_times_numeral power_Suc power_commuting_commutes)
      qed
    next
      show "SWAP_down (Suc n) \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (2 ^ Suc (Suc n)) (2 ^ Suc (Suc n))"
      proof -
        have "SWAP_down (Suc n) \<in> carrier_mat (2^(Suc n)) (2^(Suc n))" using SWAP_down_carrier_mat
          by blast
        moreover have "1\<^sub>m 2 \<in> carrier_mat 2 2" by simp
        ultimately show ?thesis using tensor_carrier_mat by auto
      qed
    next
      show "kron f (x # xs @ [a]) \<in> carrier_mat (2 ^ Suc (Suc n)) 1" using kron_carrier_mat
        by (metis assms length_Cons length_append_singleton n_def)
    qed
    also have "\<dots> = ((1\<^sub>m (2^n)) \<Otimes> SWAP) * (((SWAP_down (Suc n)) \<Otimes> (1\<^sub>m 2)) * 
                    (kron f (x#xs) \<Otimes> f a))"
      using kron.simps by (metis append_Cons kron_cons_right)
    also have "\<dots> = ((1\<^sub>m (2^n)) \<Otimes> SWAP) * (((SWAP_down (Suc n))*(kron f (x#xs))) \<Otimes>
                                            (1\<^sub>m 2) * (f a))"
    proof -
      have c1:"dim_col (SWAP_down (Suc n)) = 2^(Suc n)" using SWAP_down_carrier_mat by blast
      hence a3: "dim_col (SWAP_down (Suc n)) > 0" by simp
      have r2:"dim_row (kron f (x#xs)) = 2^(Suc n)" using kron_carrier_mat assms n_def by auto
      hence a4:"dim_row (kron f (x#xs)) > 0" by simp
      with c1 r2 have a1:"dim_col (SWAP_down (Suc n)) = dim_row (kron f (x#xs))" by simp
      have c3:"dim_col (1\<^sub>m 2) = 2" by simp
      have r4:"dim_row (f a) = 2" using assms by simp
      hence a6:"dim_row (f a) > 0" by simp
      with c3 r4 have a2:"dim_col (1\<^sub>m 2) = dim_row (f a)" by simp
      have "(((SWAP_down (Suc n)) \<Otimes> (1\<^sub>m 2)) * (kron f (x#xs) \<Otimes> f a)) = 
            (((SWAP_down (Suc n))*(kron f (x#xs))) \<Otimes> (1\<^sub>m 2) * (f a))"
        using a1 a2 a3 a4 a6
        by (metis assms carrier_matD(2) gr0I kron_carrier_mat mult_distr_tensor zero_neq_one)
      thus ?thesis by simp
    qed
    also have "\<dots> = ((1\<^sub>m (2^n)) \<Otimes> SWAP) * (kron f xs \<Otimes> f x \<Otimes> f a)"
      using HI by (simp add: assms n_def)
    also have "\<dots> = ((1\<^sub>m (2^n)) \<Otimes> SWAP) * (kron f xs \<Otimes> (f x \<Otimes> f a))"
      using tensor_mat_is_assoc by auto 
    also have "\<dots> = ((1\<^sub>m (2^n)) * (kron f xs)) \<Otimes> (SWAP * (f x \<Otimes> f a))"
      using mult_distr_tensor 
      by (smt (verit, del_insts) SWAP_ncols assms carrier_matD(2) dim_col_tensor_mat 
          dim_row_tensor_mat index_mult_mat(2) index_one_mat(2) index_one_mat(3) kron_carrier_mat
          left_mult_one_mat n_def numeral_One numeral_times_numeral semiring_norm(11) 
          semiring_norm(13) zero_less_numeral zero_less_power)
    also have "\<dots> = kron f xs \<Otimes> f a \<Otimes> f x" using SWAP_tensor
      by (metis assms carrier_matI kron_carrier_mat left_mult_one_mat n_def tensor_mat_is_assoc)
    also have "\<dots> = kron f (xs@[a]) \<Otimes> f x" using kron.simps kron_cons_right by presburger 
    finally show ?thesis by this
  qed
qed


lemma SWAP_down_kron_map_rev:
  assumes "\<forall>m. dim_row (f m) = 2 \<and> dim_col (f m) = 1"
  shows "(SWAP_down (Suc k)) * 
        kron f (map nat (rev [1..int (Suc k)])) = 
         (kron f (map nat (rev [1..int k])) \<Otimes> (f (Suc k)))"
proof -
  have "rev [1..int (Suc k)] = int (Suc k) # rev [1..int k]" using rev_append upto_rec2 by simp
  hence 1:"map nat (rev [1..int (Suc k)]) = Suc k # (map nat (rev [1.. int k]))"
    using list.map(2) by simp
  define x xs where "x = Suc k" and "xs = (map nat (rev [1.. int k]))"
  have "length xs = k" using xs_def by simp
  hence 2:"length (x#xs) = Suc k" by simp
  with 1 2 x_def xs_def have "(SWAP_down (Suc k)) * kron f (map nat (rev [1..int (Suc k)])) =
                              (SWAP_down (length (x#xs))) * kron f (x#xs)" by auto
  also have "\<dots> = kron f xs \<Otimes> f x" using SWAP_down_kron x_def xs_def assms by blast
  finally show ?thesis using x_def xs_def by simp
qed


lemma reverse_qubits_kron:
  assumes "\<forall>m. dim_row (f m) = 2 \<and> dim_col (f m) = 1"
  shows "(reverse_qubits n) * (kron f (map nat (rev [1..n]))) = kron f (map nat [1..n])"
proof (induct n rule: reverse_qubits.induct)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case
  proof -
    have 1:"rev [1] = [1]" using rev_def by auto
    have 2:"reverse_qubits (Suc 0) = 1\<^sub>m 2" by simp
    have 3:"(f 1) \<in> carrier_mat 2 1" using assms carrier_mat_def by auto
    have 4:"kron f [1] = (f 1)" using kron.simps(2) by auto
    show ?case using 1 2 3 4 by auto
  qed
next
  case 3
  have "reverse_qubits (Suc (Suc 0)) * kron f (map nat (rev [1..int (Suc (Suc 0))])) = 
        SWAP * kron f [2,1]"
    using reverse_qubits.simps(3) upto_rec1 by auto
  also have "\<dots> = SWAP * ((f 2) \<Otimes> (f 1))"
    using right_tensor_id by (metis carrier_mat_triv kron.simps(1) kron.simps(2))
  also have "\<dots> = (f 1) \<Otimes> (f 2)" using SWAP_tensor assms by auto
  also have "\<dots> = kron f [1,2]" using upto_rec1 assms by auto
  also have "\<dots> = kron f (map nat [1..int (Suc (Suc 0))])" using right_tensor_id assms 
    by (auto simp add: upto_rec1)
  finally show "reverse_qubits (Suc (Suc 0)) * kron f (map nat (rev [1..int (Suc (Suc 0))])) =
                kron f (map nat [1..int (Suc (Suc 0))])" by this
next 
  case 4
  fix n::nat
  define k::nat where "k = Suc (Suc n)"
  assume HI:"reverse_qubits (Suc (Suc n)) * kron f (map nat (rev [1..int (Suc (Suc n))])) =
             kron f (map nat [1..int (Suc (Suc n))])"
  have sk:"(SWAP_down (Suc k)) * kron f (map nat (rev [1..int (Suc k)])) = 
        (kron f (map nat (rev [1..int k])) \<Otimes> (f (Suc k)))" 
    using SWAP_down_kron_map_rev assms by this
  have "reverse_qubits (Suc k) * kron f (map nat (rev [1..int (Suc k)])) =
        ((reverse_qubits k) \<Otimes> (1\<^sub>m 2)) * (SWAP_down (Suc k)) * 
        kron f (map nat (rev [1..int (Suc k)]))"
    using reverse_qubits.simps(4) k_def by simp
  also have "\<dots> = ((reverse_qubits k) \<Otimes> (1\<^sub>m 2)) * ((SWAP_down (Suc k)) * 
            kron f (map nat (rev [1..int (Suc k)])))"
  proof (rule assoc_mult_mat)
    show "(reverse_qubits k) \<Otimes> (1\<^sub>m 2) \<in> carrier_mat (2^(k+1)) (2^(k+1))"
    proof -
      have "reverse_qubits k \<in> carrier_mat (2^k) (2^k)" by simp
      moreover have "1\<^sub>m 2 \<in> carrier_mat 2 2" by simp
      ultimately show ?thesis using tensor_carrier_mat by (smt (verit) power_add power_one_right)
    qed
  next
    show "(SWAP_down (Suc k)) \<in> carrier_mat (2^(k+1)) (2^(k+1))"
      using Suc_eq_plus1 SWAP_down_carrier_mat by presburger
  next
    show "kron f (map nat (rev [1..int (Suc k)])) \<in> carrier_mat (2 ^ (k + 1)) 1"
    proof -
      define xs where "xs = (map nat (rev [1..int (Suc k)]))"
      then have k1:"length xs = k + 1" by auto
      then have "kron f xs \<in> carrier_mat (2 ^ (k + 1)) 1"
        using kron_carrier_mat assms k1 by metis
      thus ?thesis using xs_def by simp
    qed
  qed
  also have "\<dots> = ((reverse_qubits k) \<Otimes> (1\<^sub>m 2)) * (kron f (map nat (rev [1..int k])) \<Otimes> (f (Suc k)))"
    using sk by simp
  also have "\<dots> = ((reverse_qubits k) * (kron f (map nat (rev [1..int k])))) \<Otimes> ((1\<^sub>m 2) * (f (Suc k)))"
  proof -
    have c1:"dim_col (reverse_qubits k) = 2^k" using reverse_qubits_carrier_mat by blast
    have r2:"dim_row (kron f (map nat (rev [1..int k]))) = 2^k" 
      using kron_carrier_mat by (metis HI assms carrier_matD(1) index_mult_mat(2) k_def length_map 
          length_rev reverse_qubits_carrier_mat)
    with c1 r2 have a1:"dim_col (reverse_qubits k) = dim_row (kron f (map nat (rev [1..int k])))"
      by auto
    have c3:"dim_col (1\<^sub>m 2) = 2" by simp
    have r4:"dim_row (f (Suc k)) = 2" using assms by simp
    with c3 r4 have a2:"dim_col (1\<^sub>m 2) = dim_row (f (Suc k))" by simp
    have a3:"dim_col (reverse_qubits k) > 0" using c1 by auto
    have a4:"dim_row (kron f (map nat (rev [1..int k]))) > 0" using r2 by auto
    have a6:"dim_row (f (Suc k)) > 0" using r4 by auto
    show ?thesis using a1 a2 a3 a4 a6 mult_distr_tensor
      by (metis assms carrier_matD(2) kron_carrier_mat zero_less_one_class.zero_less_one)
  qed
  also have "\<dots> = kron f (map nat [1..int k]) \<Otimes> (f (Suc k))"
    using HI k_def assms by auto
  also have "\<dots> = kron f (map nat [1..int (Suc k)])" using kron_cons_right
    by (smt (verit, ccfv_threshold) list.simps(8) list.simps(9) map_append nat_int negative_zless 
        of_nat_Suc upto_rec2)
  finally show "reverse_qubits (Suc (Suc (Suc n))) * 
                kron f (map nat (rev [1..int (Suc (Suc (Suc n)))])) =
                kron f (map nat [1..int (Suc (Suc (Suc n)))])" using k_def by simp
qed


lemma prod_rep_fun:
  assumes "f = (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>)"
  shows "\<forall>m. dim_row (f m) = 2 \<and> dim_col (f m) = 1"
  apply (rule allI)
  apply (rule conjI)
   apply (simp add: assms ket_vec_def cpx_vec_length_def)+
  done

lemma rev_upto:
  assumes "n1 \<le> n2"
  shows "rev [n1..n2] = n2 # rev [n1..(n2-1)]"
  apply (simp)
  apply (rule upto_rec2)
  apply (simp add:assms)
  done

lemma dim_row_kron:
  shows "dim_row (kron f xs) = (\<Prod>x\<leftarrow>xs. dim_row (f x))"
proof (induct xs)
  case Nil
  show ?case using kron.simps(1) prod_list_def by auto
next
  case (Cons a xs)
  assume HI:"dim_row (kron f xs) = (\<Prod>x\<leftarrow>xs. dim_row (f x))"
  have "dim_row (kron f (a#xs)) = dim_row ((f a) \<Otimes> (kron f xs))" using kron.simps(2) by auto
  hence "\<dots> = (dim_row (f a)) * (dim_row (kron f xs))" by auto
  hence "\<dots> = (dim_row (f a)) * (\<Prod>x\<leftarrow>xs. dim_row (f x))" using HI by auto
  hence "\<dots> = (\<Prod>x\<leftarrow>a # xs. dim_row (f x))" by auto
  thus ?case using HI by auto
qed

lemma dim_col_kron:
  shows "dim_col (kron f xs) = (\<Prod>x\<leftarrow>xs. dim_col (f x))"
proof (induct xs)
  case Nil
  show ?case using kron.simps(1) prod_list_def by auto
next
  case (Cons a xs)
  assume HI:"dim_col (kron f xs) = (\<Prod>x\<leftarrow>xs. dim_col (f x))"
  have "dim_col (kron f (a#xs)) = dim_col ((f a) \<Otimes> (kron f xs))" using kron.simps(2) by auto
  hence "\<dots> = (dim_col (f a)) * (dim_col (kron f xs))" by auto
  hence "\<dots> = (dim_col (f a)) * (\<Prod>x\<leftarrow>xs. dim_col (f x))" using HI by auto
  hence "\<dots> = (\<Prod>x\<leftarrow>a # xs. dim_col (f x))" by auto
  thus ?case using HI by auto
qed

lemma prod_2_n:
  "(\<Prod>x\<leftarrow>map nat (rev [1..int n]). 2) = 2 ^ n"
  apply (induct n)
   apply (simp add: rev_upto)+
  done

lemma prod_2_n_b:
  "(\<Prod>x\<leftarrow>map nat [1..int n]. 2) = 2 ^ n"
  apply (induct n)
   apply simp
  apply (simp add: upto_rec2 power_commutes)
  done

lemma prod_1_n:
  "(\<Prod>x\<leftarrow>map nat (rev [1..int n]). 1) = 1"
  apply (induct n)
   apply (simp add: rev_upto)+
  done

lemma prod_1_n_b:
  "(\<Prod>x\<leftarrow>map nat [1..int n]. Suc 0) = Suc 0"
  apply (induct n)
   apply simp
  apply (simp add: upto_rec2)
  done

lemma reverse_qubits_product_representation:
  "reverse_qubits n * reverse_QFT_product_representation j n = QFT_product_representation j n"
proof -
  have "(reverse_qubits n) * reverse_QFT_product_representation j n = (reverse_qubits n) *
       ((1/sqrt(2^n)) \<cdot>\<^sub>m kron (\<lambda>l. |zero\<rangle> + exp (2*\<i>*pi*j/2^l) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..int n])))"
    using reverse_QFT_product_representation_def by simp
  also have "\<dots> = (1/sqrt(2^n)) \<cdot>\<^sub>m ((reverse_qubits n) *
                kron (\<lambda>l. |zero\<rangle> + exp (2*\<i>*pi*j/2^l) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..int n])))"
  proof (rule mult_smult_distrib)
    show "reverse_qubits n \<in> carrier_mat (2^n) (2^n)" by simp
  next
    show "kron (\<lambda>l. |zero\<rangle> + exp (2*\<i>*pi*j/2^l) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..int n])) 
          \<in> carrier_mat (2^n) 1"
    proof
      show "dim_row (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..n])))
          = 2 ^ n"
      proof -
        have a1:"dim_row (kron (\<lambda>l. |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ l) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..int n])))
            = (\<Prod>x\<leftarrow>(map nat (rev [1..int n])). (dim_row ((\<lambda>l. |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ l) \<cdot>\<^sub>m |one\<rangle>) x)))"
          using dim_row_kron by simp
        hence b1:"\<dots> = (\<Prod>x\<leftarrow>(map nat (rev [1..int n])). 2)" using prod_rep_fun by auto
        hence "\<dots> = 2 ^ n" using prod_2_n by simp
        thus ?thesis using a1 b1 by auto
      qed
    next
      show "dim_col (kron (\<lambda>(l::nat). |zero\<rangle> + exp (2*\<i>*pi*j/(2^l)) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..n])))
            = 1"
      proof -
        have a2:"dim_col (kron (\<lambda>l. |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ l) \<cdot>\<^sub>m |one\<rangle>) (map nat (rev [1..int n])))
            = (\<Prod>x\<leftarrow>(map nat (rev [1..int n])). (dim_col ((\<lambda>l. |zero\<rangle> + exp (2 * \<i> * complex_of_real pi * complex_of_nat j / 2 ^ l) \<cdot>\<^sub>m |one\<rangle>) x)))"
          using dim_col_kron by simp
        also have "\<dots> = (\<Prod>x\<leftarrow>(map nat (rev [1..int n])). 1)" using prod_rep_fun by auto
        also have "\<dots> = 1" using prod_1_n by metis
        finally show ?thesis using a2 by auto
      qed
    qed
  qed
  also have "\<dots> = (1 / sqrt (2^n)) \<cdot>\<^sub>m kron (\<lambda>l. |zero\<rangle> + exp (2*\<i>*pi*j/2^l) \<cdot>\<^sub>m |one\<rangle>) (map nat [1..int n])"
    using reverse_qubits_kron prod_rep_fun by presburger
  also have "\<dots> = QFT_product_representation j n" using QFT_product_representation_def by simp
  finally show ?thesis by this
qed

text \<open>Finally, we proof the correctness of the algorithm\<close>

theorem ordered_QFT_is_correct:
  assumes "j < 2^n"
  shows "(ordered_QFT n) * |state_basis n j\<rangle> = QFT_product_representation j n"
proof -
  have "(ordered_QFT n) * |state_basis n j\<rangle> = (reverse_qubits n) * (QFT n) * |state_basis n j\<rangle>"
    using ordered_QFT_def by simp
  also have "\<dots> = (reverse_qubits n) * ((QFT n) * |state_basis n j\<rangle>)"
  proof (rule assoc_mult_mat)
    show "reverse_qubits n \<in> carrier_mat (2^n) (2^n)" by simp
  next
    show "QFT n \<in> carrier_mat (2^n) (2^n)" by simp
  next
    show "|state_basis n j\<rangle> \<in> carrier_mat (2 ^ n) 1" using state_basis_carrier_mat by simp
  qed
  also have "\<dots> = (reverse_qubits n) * reverse_QFT_product_representation j n"
    using QFT_is_correct assms by simp
  also have "\<dots> = QFT_product_representation j n"
    using reverse_qubits_product_representation by simp
  finally show ?thesis by this
qed


(* -------------------------------------------------------------------------------------------- *)

section \<open>Unitarity\<close>

text \<open>Although unitarity is not required to proof QFT's correctness, in this section we will prove
it, i.e., QFT and ordered\_QFT functions create quantum gates and QFT product representation is a 
quantum state.\<close>


lemma state_basis_is_state:
  assumes "j < n"
  shows "state n |state_basis n j\<rangle>"
proof
  show "dim_col |state_basis n j\<rangle> = 1" by (simp add: ket_vec_def)
  show "dim_row |state_basis n j\<rangle> = 2^n" by (simp add: ket_vec_def state_basis_def)
  show "\<parallel>Matrix.col |state_basis n j\<rangle> 0\<parallel> = 1"
    by (metis assms ket_vec_col less_exp order_less_trans state_basis_def unit_cpx_vec_length)
qed

lemma R_dagger_mat:
  shows "(R k)\<^sup>\<dagger> = Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i=0 then 1 else exp(-2*pi*\<i>/2^k)))"
proof
  let ?Rkd = "(R k)\<^sup>\<dagger>" 
  define m where "m = Matrix.mat 2 2 
  (\<lambda>(i,j). if i\<noteq>j then 0 else (if i=0 then 1 else exp(-2*pi*\<i>/2^k)))"
  thus "\<And>i j. i < dim_row m \<Longrightarrow> j < dim_col m \<Longrightarrow> ?Rkd $$ (i, j) = m $$ (i, j)"
  proof -
    fix i j
    assume "i < dim_row m"
    hence i2:"i < 2" using m_def by auto
    assume "j < dim_col m"
    hence j2:"j < 2" using m_def by auto
    show "?Rkd $$ (i, j) = m $$ (i, j)"
    proof (rule disjE)
      show "i = 0 \<or> i = 1" using i2 by auto
    next
      assume i0:"i = 0"
      show "?Rkd $$ (i, j) = m $$ (i, j)"
      proof (rule disjE)
        show "j = 0 \<or> j = 1" using j2 by auto
      next 
        assume j0:"j = 0"
        show "?Rkd $$ (i, j) = m $$ (i, j)" 
        proof -
          have "?Rkd $$ (0,0) = cnj (R k $$ (0,0))" 
            using dagger_def
            by (metis (no_types, lifting) One_nat_def R_def Suc_1 Suc_eq_plus1 
                Tensor.mat_of_cols_list_def dim_col_mat(1) dim_row_mat(1) index_mat(1) list.size(3)
                list.size(4) old.prod.case power_eq_0_iff power_zero_numeral)
          also have "\<dots> = 1" 
            using R_def mat_of_cols_list_def
            by (metis One_nat_def Suc_1 Suc_eq_plus1 complex_cnj_one_iff index_mat_of_cols_list 
                list.size(3) list.size(4) nth_Cons_0 pos2)
          also have "\<dots> = m $$ (0,0)" using m_def by simp
          finally show ?thesis using i0 j0 by auto
        qed
      next
        assume j1:"j = 1"
        show "?Rkd $$ (i, j) = m $$ (i, j)"
        proof -
          have "?Rkd $$ (0,1) = cnj (R k $$ (1,0))"
            using dagger_def 
            by (metis (no_types, lifting) One_nat_def R_def Suc_1 Suc_eq_plus1 
                Tensor.mat_of_cols_list_def \<open>j < dim_col m\<close> dim_col_mat(1) dim_row_mat(1) 
                index_mat(1) j1 list.size(3) list.size(4) m_def old.prod.case pos2)
          also have "\<dots> = 0"
            using R_def mat_of_cols_list_def
            by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 \<open>j < dim_col m\<close> 
                complex_cnj_zero_iff dim_col_mat(1) index_mat_of_cols_list j1 list.size(3) 
                list.size(4) m_def nth_Cons_0 nth_Cons_Suc pos2)
          also have "\<dots> = m $$ (0,1)" using m_def by auto
          finally show ?thesis using i0 j1 by auto
        qed
      qed
    next
      assume i1:"i = 1"
      show "?Rkd $$ (i, j) = m $$ (i, j)"
      proof (rule disjE)
        show "j = 0 \<or> j = 1" using j2 by auto
      next 
        assume j0:"j = 0"
        show "?Rkd $$ (i, j) = m $$ (i, j)"
        proof -
          have "?Rkd $$ (1,0) = cnj (R k $$ (0,1))"
            using dagger_def
            by (metis (no_types, lifting) One_nat_def R_def Suc_1 Suc_eq_plus1 
                Tensor.mat_of_cols_list_def dim_col_mat(1) dim_row_mat(1) index_mat(1) 
                less_Suc_numeral list.size(3) list.size(4) old.prod.case power_eq_0_iff 
                power_zero_numeral pred_numeral_simps(2))
          also have "\<dots> = 0"
            using R_def mat_of_cols_list_def
            by (metis One_nat_def Suc_eq_plus1 complex_cnj_zero_iff index_mat_of_cols_list
                less_Suc_eq_0_disj list.size(4) nth_Cons_0 nth_Cons_Suc pos2)
          also have "\<dots> = m $$ (1,0)" using m_def by simp
          finally show ?thesis using i1 j0 by simp
        qed
      next
        assume j1:"j = 1"
        show "?Rkd $$ (i, j) = m $$ (i, j)" 
        proof -
          have "?Rkd $$ (1,1) = cnj (R k $$ (1,1))"
            using dagger_def
            by (metis (no_types, lifting) One_nat_def R_def Suc_1 Suc_eq_plus1 
                Tensor.mat_of_cols_list_def dim_col_mat(1) dim_row_mat(1) index_mat(1) 
                less_Suc_numeral list.size(3) list.size(4) old.prod.case power_eq_0_iff 
                power_zero_numeral pred_numeral_simps(2))
          also have "\<dots> = cnj (exp(2*pi*\<i>/2^k))"
            using R_def mat_of_cols_list_def 
            by (metis One_nat_def Suc_1 Suc_eq_plus1 index_mat_of_cols_list lessI list.size(3) 
                list.size(4) nth_Cons_0 nth_Cons_Suc)
          also have "\<dots> = exp (-2*pi*\<i>/2^k)"
            by (smt (verit, ccfv_threshold) exp_of_real_cnj mult.commute mult.left_commute 
                mult_1s_ring_1(1) of_real_divide of_real_minus of_real_numeral of_real_power 
                times_divide_eq_right)
          also have "\<dots> = m $$ (1,1)" using m_def by simp
          finally have "?Rkd $$ (i, j) = m $$ (i, j)" using i1 j1 by simp
          thus ?thesis by this
        qed
      qed
    qed
  qed
next
  define m where "m = Matrix.mat 2 2 
  (\<lambda>(i,j). if i\<noteq>j then 0 else (if i=0 then 1 else exp(-2*pi*\<i>/2^k)))"
  thus "dim_row ((R k)\<^sup>\<dagger>) = dim_row m" 
    by (metis (no_types, lifting) One_nat_def R_def Suc_1 Suc_eq_plus1 Tensor.mat_of_cols_list_def
        dim_col_mat(1) dim_row_mat(1) dim_row_of_dagger list.size(3) list.size(4))
next
  define m where "m = Matrix.mat 2 2 
  (\<lambda>(i,j). if i\<noteq>j then 0 else (if i=0 then 1 else exp(-2*pi*\<i>/2^k)))"
  thus "dim_col ((R k)\<^sup>\<dagger>) = dim_col m" 
    by (simp add: R_def Tensor.mat_of_cols_list_def)
qed

lemma R_is_gate:
  shows "gate 1 (R n)"
proof
  let ?Rnd = "(R n)\<^sup>\<dagger>" 
  show "dim_row (R n) = 2^1" using R_def by (simp add: Tensor.mat_of_cols_list_def)
  show "square_mat (R n)" using R_def by (simp add: Tensor.mat_of_cols_list_def)
  show "unitary (R n)"
  proof -
    have "?Rnd * R n = 1\<^sub>m 2 \<and> R n * ?Rnd = 1\<^sub>m 2"
    proof
      show "?Rnd * R n = 1\<^sub>m 2"
      proof
        show "\<And>i j. i < dim_row (1\<^sub>m 2) \<Longrightarrow> j < dim_col (1\<^sub>m 2) \<Longrightarrow> 
              (?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
        proof -
          fix i j
          assume "i < dim_row (1\<^sub>m 2)"
          hence i2:"i < 2" by auto
          assume "j < dim_col (1\<^sub>m 2)"
          hence j2:"j < 2" by auto
          show "(?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
          proof (rule disjE)
            show "i = 0 \<or> i = 1" using i2 by auto
          next
            assume i0:"i = 0"
            show "(?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
            proof (rule disjE)
              show "j = 0 \<or> j = 1" using j2 by auto
            next
              assume j0:"j = 0"
              show "(?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
              proof -
                have "(?Rnd * R n) $$ (0,0) = (?Rnd $$ (0,0)) * ((R n) $$ (0,0)) +
                      (?Rnd $$ (0,1)) * ((R n) $$ (1,0))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = 1" using R_dagger_mat R_def index_mat_of_cols_list
                  by (smt (verit, del_insts) Suc_1 Suc_eq_plus1 add.commute add_0 index_mat(1) 
                      lessI list.size(3) list.size(4) mult_1 mult_zero_left nth_Cons_0 
                      nth_Cons_Suc old.prod.case pos2)
                also have "\<dots> = 1\<^sub>m 2 $$ (0,0)" by simp
                finally show ?thesis using i0 j0 by simp
              qed 
            next
              assume j1:"j = 1"
              show "(?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)" 
              proof -
                have "(?Rnd * R n) $$ (0,1) = (?Rnd $$ (0,0)) * ((R n) $$ (0,1)) +
                      (?Rnd $$ (0,1)) * ((R n) $$ (1,1))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = 0" using R_dagger_mat R_def index_mat_of_cols_list
                  by (smt (verit) Suc_1 Suc_eq_plus1 add_cancel_left_left index_mat(1) lessI
                      list.size(3) list.size(4) mult_eq_0_iff nth_Cons_0 nth_Cons_Suc old.prod.case 
                      pos2)
                also have "\<dots> = 1\<^sub>m 2 $$ (0,1)" by simp
                finally show ?thesis using i0 j1 by simp
              qed
            qed
          next
            assume i1:"i = 1"
            show "(?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
            proof (rule disjE)
              show "j = 0 \<or> j = 1" using j2 by auto
            next
              assume j0:"j = 0"
              show "(?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
              proof -
                have "(?Rnd * R n) $$ (1,0) = (?Rnd $$ (1,0)) * ((R n) $$ (0,0)) +
                      (?Rnd $$ (1,1)) * ((R n) $$ (1,0))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = 0" using R_dagger_mat R_def index_mat_of_cols_list
                  by (smt (verit) Suc_1 Suc_eq_plus1 add_cancel_right_right index_mat(1) lessI 
                      list.size(3) list.size(4) mult_eq_0_iff nth_Cons_0 nth_Cons_Suc old.prod.case
                      plus_1_eq_Suc pos2)
                also have "\<dots> = 1\<^sub>m 2 $$ (1,0)" by simp
                finally show ?thesis using i1 j0 by simp
              qed
            next
              assume j1:"j = 1"
              show "(?Rnd * R n) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
              proof -
                have "(?Rnd * R n) $$ (1,1) = (?Rnd $$ (1,0)) * ((R n) $$ (0,1)) +
                      (?Rnd $$ (1,1)) * ((R n) $$ (1,1))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = exp(-2*pi*\<i>/2^n) * exp(2*pi*\<i>/2^n)"
                  using R_dagger_mat R_def index_mat_of_cols_list by auto
                also have "\<dots> = 1"
                  by (metis (no_types, lifting) exp_minus_inverse minus_divide_divide 
                      minus_divide_right mult_minus_left of_real_minus)
                also have "\<dots> = 1\<^sub>m 2 $$ (1,1)" by simp
                finally show ?thesis using i1 j1 by simp
              qed
            qed
          qed
        qed
      next
        show "dim_row (?Rnd * R n) = dim_row (1\<^sub>m 2)"
          using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> by auto
      next
        show "dim_col (?Rnd * R n) = dim_col (1\<^sub>m 2)"
          using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> by auto
      qed
    next
      show "R n * ?Rnd = 1\<^sub>m 2"
      proof
        show "\<And>i j. i < dim_row (1\<^sub>m 2) \<Longrightarrow> j < dim_col (1\<^sub>m 2) \<Longrightarrow>
              (R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
        proof -
          fix i j
          assume "i < dim_row (1\<^sub>m 2)"
          hence i2:"i < 2" by auto
          assume "j < dim_col (1\<^sub>m 2)"
          hence j2:"j < 2" by auto
          show "(R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
          proof (rule disjE)
            show "i = 0 \<or> i = 1" using i2 by auto
          next
            assume i0:"i = 0"
            show "(R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
            proof (rule disjE)
              show "j = 0 \<or> j = 1" using j2 by auto
            next
              assume j0:"j = 0"
              show "(R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
              proof -
                have "(R n * ?Rnd) $$ (0,0) = ((R n) $$ (0,0)) * (?Rnd $$ (0,0)) +
                      ((R n) $$ (0,1)) * (?Rnd $$ (1,0))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = 1" using R_dagger_mat R_def index_mat_of_cols_list by simp
                also have "\<dots> = 1\<^sub>m 2 $$ (0,0)" by simp
                finally show ?thesis using i0 j0 by simp
              qed
            next
              assume j1:"j = 1"
              show "(R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
              proof -
                have "(R n * ?Rnd) $$ (0,1) = ((R n) $$ (0,0)) * (?Rnd $$ (0,1)) +
                      (R n $$ (0,1)) * (?Rnd $$ (1,1))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = 0" using R_dagger_mat R_def index_mat_of_cols_list by simp
                also have "\<dots> = 1\<^sub>m 2 $$ (0,1)" by simp
                finally show ?thesis using i0 j1 by simp
              qed
            qed
          next
            assume i1:"i = 1"
            show "(R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
            proof (rule disjE)
              show "j = 0 \<or> j = 1" using j2 by auto
            next
              assume j0:"j = 0"
              show "(R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
              proof -
                have "(R n * ?Rnd) $$ (1,0) = ((R n) $$ (1,0)) * (?Rnd $$ (0,0)) +
                      ((R n) $$ (1,1)) * (?Rnd $$ (1,0))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = 1\<^sub>m 2 $$ (1,0)" 
                  using R_dagger_mat R_def index_mat_of_cols_list by simp
                finally show ?thesis using i1 j0 by simp
              qed
            next
              assume j1:"j = 1"
              show "(R n * ?Rnd) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)" 
              proof -
                have "(R n * ?Rnd) $$ (1,1) = (R n $$ (1,0)) * (?Rnd $$ (0,1)) +
                      (R n $$ (1,1)) * (?Rnd $$ (1,1))"
                  using \<open>dim_row (R n) = 2 ^ 1\<close> \<open>square_mat (R n)\<close> sumof2 by fastforce
                also have "\<dots> = exp(2*pi*\<i>/2^n) * exp(-2*pi*\<i>/2^n)"
                  using R_dagger_mat R_def index_mat_of_cols_list by simp
                also have "\<dots> = 1"
                  by (simp add: exp_minus_inverse)
                also have "\<dots> = 1\<^sub>m 2 $$ (1,1)" by simp
                finally show ?thesis using i1 j1 by simp
              qed
            qed
          qed
        qed
      next
        show "dim_row (R n * ?Rnd) = dim_row (1\<^sub>m 2)"
          by (simp add: \<open>dim_row (R n) = 2 ^ 1\<close>)
      next
        show "dim_col (R n * ?Rnd) = dim_col (1\<^sub>m 2)"
          by (simp add: \<open>dim_row (R n) = 2 ^ 1\<close>)
      qed
    qed
    thus ?thesis using unitary_def R_def mat_of_cols_list_def by auto
  qed
qed

lemma SWAP_dagger_mat:
  shows "SWAP\<^sup>\<dagger> = SWAP"
proof -
  have "SWAP\<^sup>\<dagger> = Matrix.mat 4 4 (\<lambda>(i,j). cnj (SWAP $$ (j,i)))" 
    using dagger_def SWAP_carrier_mat 
    by (metis SWAP_ncols carrier_matD(1))
  also have "\<dots> = Matrix.mat 4 4 (\<lambda>(i,j). cnj (SWAP $$ (i,j)))" 
    using SWAP_def SWAP_index
  proof -
    obtain nn :: "(nat \<times> nat \<Rightarrow> complex) \<Rightarrow> (nat \<times> nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" and nna :: "(nat \<times> nat \<Rightarrow> complex) \<Rightarrow> (nat \<times> nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
      "\<forall>x0 x1 x3 x5. (\<exists>v6 v7. (v6 < x5 \<and> v7 < x3) \<and> x1 (v6, v7) \<noteq> x0 (v6, v7)) = ((nn x0 x1 x3 x5 < x5 \<and> nna x0 x1 x3 x5 < x3) \<and> x1 (nn x0 x1 x3 x5, nna x0 x1 x3 x5) \<noteq> x0 (nn x0 x1 x3 x5, nna x0 x1 x3 x5))"
      by moura
    then have "\<forall>n na nb nc f fa. (n \<noteq> na \<or> nb \<noteq> nc \<or> (nn fa f nb n < n \<and> nna fa f nb n < nb) \<and> f (nn fa f nb n, nna fa f nb n) \<noteq> fa (nn fa f nb n, nna fa f nb n)) \<or> Matrix.mat n nb f = Matrix.mat na nc fa"
      by (meson cong_mat)
    moreover
    { assume "nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 3 \<or> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 3"
      then have "(if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 2 \<or> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 1 then if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 3 \<or> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 3 then (if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 0 else (if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1 else (if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1) \<longrightarrow> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<or> (if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 0"
        by presburger }
    moreover
    { assume "nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3"
      then have "(if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 2 \<or> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 1 then if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 3 \<or> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 \<noteq> 3 then (if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 0 else (if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1 else (if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1) \<longrightarrow> (if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1"
        by presburger }
    moreover
    { assume "(if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 0 \<and> (if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 0"
      moreover
      { assume "((if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 then 1::complex else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 then 1 else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 then 1 else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 then 1 else 0) = 0 \<and> (if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 then 1::complex else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 then 1 else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 then 1 else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 then 1 else 0) = 0) \<and> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (n, na))) \<noteq> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (na, n)))"
        then have "Matrix.mat 4 4 (\<lambda>(n, na). if n = 0 \<and> na = 0 then 1::complex else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) $$ (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) = (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) \<longrightarrow> ((if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 then 1::complex else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 then 1 else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 then 1 else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 then 1 else 0) = 0 \<and> (if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 then 1::complex else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 then 1 else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 then 1 else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 then 1 else 0) = 0) \<and> SWAP $$ (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) \<noteq> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0)"
          by (smt (z3) SWAP_def old.prod.case)
        then have "Matrix.mat 4 4 (\<lambda>(n, na). if n = 0 \<and> na = 0 then 1::complex else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) $$ (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) \<noteq> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) \<or> SWAP $$ (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) \<noteq> (case (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0)"
          by fastforce }
      ultimately have "SWAP $$ (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) = (case (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) \<and> Matrix.mat 4 4 (\<lambda>(n, na). if n = 0 \<and> na = 0 then 1::complex else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) $$ (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) = (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) \<longrightarrow> \<not> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 < 4 \<or> \<not> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 < 4 \<or> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (n, na))) = (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (na, n)))"
        by blast }
    moreover
    { assume "(if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1 \<and> (if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1"
      moreover
      { assume "((if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 then 1::complex else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 then 1 else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 then 1 else if nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 \<and> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 then 1 else 0) = 1 \<and> (if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 0 then 1::complex else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 then 1 else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 2 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 1 then 1 else if nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 \<and> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 = 3 then 1 else 0) = 1) \<and> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (n, na))) \<noteq> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (na, n)))"
        then have "((if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1 \<and> (if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 0 then 1::complex else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 2 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 1 then 1 else if nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 \<and> nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4 = 3 then 1 else 0) = 1) \<and> SWAP $$ (nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4, nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4) \<noteq> SWAP $$ (nn (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4, nna (\<lambda>(na, n). cnj (SWAP $$ (n, na))) (\<lambda>(na, n). cnj (SWAP $$ (na, n))) 4 4)"
          by (smt (z3) old.prod.case)
        then have "Matrix.mat 4 4 (\<lambda>(n, na). if n = 0 \<and> na = 0 then 1::complex else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) $$ (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) \<noteq> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) \<or> SWAP $$ (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) \<noteq> (case (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0)"
          using SWAP_def by auto }
      ultimately have "SWAP $$ (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) = (case (nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) \<and> Matrix.mat 4 4 (\<lambda>(n, na). if n = 0 \<and> na = 0 then 1::complex else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) $$ (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) = (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> if n = 0 \<and> na = 0 then 1 else if n = 1 \<and> na = 2 then 1 else if n = 2 \<and> na = 1 then 1 else if n = 3 \<and> na = 3 then 1 else 0) \<longrightarrow> \<not> nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 < 4 \<or> \<not> nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4 < 4 \<or> (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (n, na))) = (case (nn (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4, nna (\<lambda>(n, na). cnj (SWAP $$ (na, n))) (\<lambda>(n, na). cnj (SWAP $$ (n, na))) 4 4) of (n, na) \<Rightarrow> cnj (SWAP $$ (na, n)))"
        by linarith }
    ultimately show ?thesis
      by (smt (z3) SWAP_def index_mat(1))
  qed
  also have "\<dots> = SWAP" using SWAP_def SWAP_index
    by (smt (verit, ccfv_SIG) case_prod_conv complex_cnj_one complex_cnj_zero cong_mat index_mat(1))
  finally show ?thesis by this
qed

lemma SWAP_inv:
  shows "SWAP * (SWAP\<^sup>\<dagger>) = 1\<^sub>m 4"
  apply (simp add: SWAP_def times_mat_def one_mat_def)
  apply (rule cong_mat)
  by (auto simp: scalar_prod_def complex_eqI)

lemma SWAP_inv':
  shows "(SWAP\<^sup>\<dagger>) * SWAP = 1\<^sub>m 4"
  apply (simp add: SWAP_def times_mat_def one_mat_def)
  apply (rule cong_mat)
  by (auto simp: scalar_prod_def complex_eqI)

lemma SWAP_is_gate:
  shows "gate 2 SWAP"
proof
  show "dim_row SWAP = 2\<^sup>2" using SWAP_carrier_mat by (simp add: numeral_Bit0)
next
  show "square_mat SWAP" using SWAP_carrier_mat by (simp add: numeral_Bit0)
next
  show "unitary SWAP"
    using unitary_def SWAP_inv SWAP_inv' SWAP_ncols SWAP_nrows by presburger
qed


lemma control2_inv:
  assumes "gate 1 U"
  shows "(control2 U) * ((control2 U)\<^sup>\<dagger>) = 1\<^sub>m 4"
proof 
  show "\<And>i j. i < dim_row (1\<^sub>m 4) \<Longrightarrow> j < dim_col (1\<^sub>m 4) \<Longrightarrow>
           (control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
  proof -
    fix i j
    assume "i < dim_row (1\<^sub>m 4)"
    hence i4:"i < 4" by auto
    assume "j < dim_col (1\<^sub>m 4)"
    hence j4:"j < 4" by auto
    show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
    proof (rule disjE)
      show "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" using i4 by auto
    next
      assume i0:"i = 0"
      show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
      proof (rule disjE)
        show "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
      next
        assume j0:"j = 0"
        show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof -
          have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (0,0) = 
                (control2 U) $$ (0,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,0) +
                (control2 U) $$ (0,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,0) +
                (control2 U) $$ (0,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,0) +
                (control2 U) $$ (0,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,0)"
            using times_mat_def sumof4
            by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dagger_def 
                dim_col_of_dagger dim_row_mat(1) i0 i4 index_matrix_prod)
          also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,0)"
            using control2_def index_mat_of_cols_list by force
          also have "\<dots> = cnj ((control2 U) $$ (0,0))"
            using dagger_def 
            by (metis carrier_matD(1) carrier_matD(2) control2_carrier_mat i0 i4 index_mat(1) 
                old.prod.case)
          also have "\<dots> = 1" using control2_def index_mat_of_cols_list by auto
          also have "\<dots> = 1\<^sub>m 4 $$ (0,0)" by simp
          finally show ?thesis using i0 j0 by simp
        qed
      next
        assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
        show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof (rule disjE)
          show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
        next
          assume j1:"j = 1"
          show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof -
            have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (0,1) = 
                  (control2 U) $$ (0,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,1) +
                  (control2 U) $$ (0,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,1) +
                  (control2 U) $$ (0,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,1) +
                  (control2 U) $$ (0,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,1)"
              using times_mat_def sumof4
              by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                  dim_row_of_dagger i0 i4 index_matrix_prod j1 j4)
            also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,1)"
              using control2_def index_mat_of_cols_list by force
            also have "\<dots> = cnj ((control2 U) $$ (1,0))"
              using dagger_def 
              by (metis (mono_tags, lifting) One_nat_def Suc_1 add_Suc_right carrier_matD(1) 
                  carrier_matD(2) control2_carrier_mat index_mat(1) less_Suc_eq_0_disj numeral_Bit0
                  prod.simps(2))
            also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
            also have "\<dots> = 1\<^sub>m 4 $$ (0,1)" by simp
            finally show ?thesis using i0 j1 by simp
          qed
        next
          assume jl2:"j = 2 \<or> j = 3"
          show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 2 \<or> j = 3" using jl2 by this
          next
            assume j2:"j = 2"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (0,2) = 
                    (control2 U) $$ (0,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,2) +
                    (control2 U) $$ (0,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,2) +
                    (control2 U) $$ (0,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,2) +
                    (control2 U) $$ (0,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,2)"
                using times_mat_def sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger i0 i4 index_matrix_prod j2 j4)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,2)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (2,0))"
                using dagger_def 
                by (smt (verit, del_insts) carrier_matD(1) carrier_matD(2) control2_carrier_mat 
                    index_mat(1) less_add_same_cancel2 numeral_Bit0 prod.simps(2) zero_less_numeral)
              also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (0,2)" by simp
              finally show ?thesis using i0 j2 by simp
            qed
          next
            assume j3:"j = 3"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (0,3) = 
                    (control2 U) $$ (0,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,3) +
                    (control2 U) $$ (0,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,3) +
                    (control2 U) $$ (0,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,3) +
                    (control2 U) $$ (0,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,3)"
                using times_mat_def sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger i0 i4 index_matrix_prod j3 j4)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,3)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (3,0))"
                using dagger_def 
                by (metis carrier_matD(1) carrier_matD(2) control2_carrier_mat index_mat(1) j3 j4 
                    prod.simps(2) zero_less_numeral)
              also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (0,3)" by simp
              finally show ?thesis using i0 j3 by simp
            qed
          qed
        qed
      qed
    next
      assume il3:"i = 1 \<or> i = 2 \<or> i = 3"
      show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
      proof (rule disjE)
        show "i = 1 \<or> i = 2 \<or> i = 3" using il3 by this
      next
        assume i1:"i = 1"
        show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof (rule disjE)
          show jl4:"j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
        next
          assume j0:"j = 0"
          show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof -
            have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (1,0) = 
                    (control2 U) $$ (1,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,0) +
                    (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,0) +
                    (control2 U) $$ (1,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,0) +
                    (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,0)"
              using times_mat_def sumof4
              by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                  dim_row_of_dagger i1 i4 index_matrix_prod j0 j4)
            also have "\<dots> = (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,0) + 
                              (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,0)"
              using control2_def index_mat_of_cols_list by force
            also have "\<dots> = (control2 U) $$ (1,1) * (cnj ((control2 U) $$ (0,1))) + 
                              (control2 U) $$ (1,3) * (cnj ((control2 U) $$ (0,3)))"
              using dagger_def
              by (smt (verit, ccfv_threshold) One_nat_def Suc_1 add.commute add_Suc_right 
                  carrier_matD(1) carrier_matD(2) control2_carrier_mat i1 i4 index_mat(1) j0 j4 
                  lessI numeral_3_eq_3 numeral_Bit0 plus_1_eq_Suc prod.simps(2))
            also have "\<dots> = (control2 U) $$ (1,1) * (cnj 0) +
                              (control2 U) $$ (1,3) * (cnj 0)"
              using control2_def index_mat_of_cols_list by simp
            also have "\<dots> = 0" by auto
            also have "\<dots> = 1\<^sub>m 4 $$ (1,0)" by simp
            finally show ?thesis using i1 j0 by simp
          qed
        next
          assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
          show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
          next
            assume j1:"j = 1"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (1,1) = 
                    (control2 U) $$ (1,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,1) +
                    (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,1) +
                    (control2 U) $$ (1,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,1) +
                    (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,1)"
                using times_mat_def sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger i1 i4 index_matrix_prod j1 j4)
              also have "\<dots> = (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,1) + 
                                (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,1)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = (control2 U) $$ (1,1) * (cnj ((control2 U) $$ (1,1))) + 
                                (control2 U) $$ (1,3) * (cnj ((control2 U) $$ (1,3)))"
                using dagger_def
                by (smt (verit, best) One_nat_def Suc_1 add.commute add_Suc_right carrier_matD(1)
                    carrier_matD(2) control2_carrier_mat i1 i4 index_mat(1) lessI numeral_3_eq_3 
                    numeral_Bit0 plus_1_eq_Suc prod.simps(2))
              also have "\<dots> = U $$ (0,0) * (cnj (U $$ (0,0))) +
                              U $$ (0,1) * (cnj (U $$ (0,1)))"
                using control2_def index_mat_of_cols_list by simp
              also have "\<dots> = (U $$ (0,0)) * ((U\<^sup>\<dagger>) $$ (0,0)) +
                              (U $$ (0,1)) * ((U\<^sup>\<dagger>) $$ (1,0))"
                using dagger_def assms(1) gate_def by force
              also have "\<dots> = (U * (U\<^sup>\<dagger>)) $$ (0,0)" 
                using times_mat_def assms(1) gate_carrier_mat sumof2
                by (smt (z3) carrier_matD(2) dagger_def dim_col_mat(1) dim_row_of_dagger 
                    gate.dim_row index_matrix_prod pos2 power_one_right)
              also have "\<dots> = (1\<^sub>m 2) $$ (0,0)" using assms(1) gate_def unitary_def by auto
              also have "\<dots> = 1" by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (1,1)" by simp
              finally show ?thesis using i1 j1 by simp
            qed
          next
            assume jl2:"j = 2 \<or> j = 3"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof (rule disjE)
              show "j = 2 \<or> j = 3" using jl2 by this
            next
              assume j2:"j = 2"
              show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (1,2) = 
                    (control2 U) $$ (1,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,2) +
                    (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,2) +
                    (control2 U) $$ (1,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,2) +
                    (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,2)"
                  using times_mat_def sumof4
                  by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                      dim_row_of_dagger i1 i4 index_matrix_prod j2 j4)
                also have "\<dots> = (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,2) + 
                                (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,2)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = (control2 U) $$ (1,1) * (cnj ((control2 U) $$ (2,1))) + 
                                (control2 U) $$ (1,3) * (cnj ((control2 U) $$ (2,3)))"
                  using dagger_def
                  by (smt (verit, ccfv_threshold) One_nat_def Suc_1 add.commute add_Suc_right 
                      carrier_matD(1) carrier_matD(2) control2_carrier_mat i1 i4 index_mat(1) j2 j4 
                      lessI numeral_3_eq_3 numeral_Bit0 plus_1_eq_Suc prod.simps(2))
                also have "\<dots> = (control2 U) $$ (1,1) * (cnj 0) +
                                (control2 U) $$ (1,3) * (cnj 0)"
                  using control2_def index_mat_of_cols_list by simp
                also have "\<dots> = 0" by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (1,2)" by simp
                finally show ?thesis using i1 j2 by simp
              qed
            next
              assume j3:"j = 3"
              show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (1,3) = 
                    (control2 U) $$ (1,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,3) +
                    (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,3) +
                    (control2 U) $$ (1,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,3) +
                    (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,3)"
                  using times_mat_def sumof4
                  by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                      dim_row_of_dagger i1 i4 index_matrix_prod j3 j4)
                also have "\<dots> = (control2 U) $$ (1,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,3) + 
                                (control2 U) $$ (1,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,3)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = (control2 U) $$ (1,1) * (cnj ((control2 U) $$ (3,1))) + 
                                (control2 U) $$ (1,3) * (cnj ((control2 U) $$ (3,3)))"
                  using dagger_def
                  by (smt (verit, best) One_nat_def Suc_1 add.commute add_Suc_right carrier_matD(1)
                      carrier_matD(2) control2_carrier_mat i1 i4 index_mat(1) lessI numeral_3_eq_3 
                      numeral_Bit0 plus_1_eq_Suc prod.simps(2))
                also have "\<dots> = U $$ (0,0) * (cnj (U $$ (1,0))) +
                              U $$ (0,1) * (cnj (U $$ (1,1)))"
                  using control2_def index_mat_of_cols_list by simp
                also have "\<dots> = (U $$ (0,0)) * ((U\<^sup>\<dagger>) $$ (0,1)) +
                              (U $$ (0,1)) * ((U\<^sup>\<dagger>) $$ (1,1))"
                  using dagger_def assms(1) gate_def by force
                also have "\<dots> = (U * (U\<^sup>\<dagger>)) $$ (0,1)" 
                  using times_mat_def assms(1) gate_carrier_mat sumof2
                  by (smt (z3) Suc_1 carrier_matD(2) dagger_def dim_col_mat(1) dim_row_of_dagger 
                      gate.dim_row index_matrix_prod lessI pos2 power_one_right)
                also have "\<dots> = (1\<^sub>m 2) $$ (0,1)" using assms(1) gate_def unitary_def by auto
                also have "\<dots> = 0" by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (1,3)" by simp
                finally show ?thesis using i1 j3 by simp
              qed
            qed
          qed
        qed
      next
        assume il2:"i = 2 \<or> i = 3"
        show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof (rule disjE)
          show "i = 2 \<or> i = 3" using il2 by this
        next
          assume i2:"i = 2"
          show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
          next
            assume j0:"j = 0"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (2,0) = 
                  (control2 U) $$ (2,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,0) +
                  (control2 U) $$ (2,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,0) +
                  (control2 U) $$ (2,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,0) +
                  (control2 U) $$ (2,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,0)"
                using times_mat_def sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger i2 i4 index_matrix_prod j0 j4)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,0)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (0,2))"
                using dagger_def 
                by (metis carrier_matD(1) carrier_matD(2) control2_carrier_mat i2 i4 index_mat(1) 
                    j0 j4 prod.simps(2))
              also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (2,0)" by simp
              finally show ?thesis using i2 j0 by simp
            qed
          next
            assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof (rule disjE)
              show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
            next
              assume j1:"j = 1"
              show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (2,1) = 
                  (control2 U) $$ (2,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,1) +
                  (control2 U) $$ (2,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,1) +
                  (control2 U) $$ (2,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,1) +
                  (control2 U) $$ (2,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,1)"
                  using times_mat_def sumof4
                  by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                      dim_row_of_dagger i2 i4 index_matrix_prod j1 j4)
                also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,1)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = cnj ((control2 U) $$ (1,2))"
                  using dagger_def 
                  by (metis carrier_matD(1) carrier_matD(2) control2_carrier_mat i2 i4 index_mat(1) 
                      j1 j4 prod.simps(2))
                also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (2,1)" by simp
                finally show ?thesis using i2 j1 by simp
              qed
            next
              assume jl2:"j = 2 \<or> j = 3"
              show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof (rule disjE)
                show "j = 2 \<or> j = 3" using jl2 by this
              next
                assume j2:"j = 2"
                show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (2,2) = 
                  (control2 U) $$ (2,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,2) +
                  (control2 U) $$ (2,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,2) +
                  (control2 U) $$ (2,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,2) +
                  (control2 U) $$ (2,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,2)"
                    using times_mat_def sumof4
                    by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                        dim_row_of_dagger i2 i4 index_matrix_prod j2 j4)
                  also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,2)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = cnj ((control2 U) $$ (2,2))"
                    using dagger_def 
                    by (metis carrier_matD(1) carrier_matD(2) control2_carrier_mat i2 index_mat(1) 
                        j2 j4 prod.simps(2))
                  also have "\<dots> = 1" using control2_def index_mat_of_cols_list by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (2,2)" by simp
                  finally show ?thesis using i2 j2 by simp
                qed
              next
                assume j3:"j = 3"
                show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (2,3) = 
                  (control2 U) $$ (2,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,3) +
                  (control2 U) $$ (2,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,3) +
                  (control2 U) $$ (2,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,3) +
                  (control2 U) $$ (2,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,3)"
                    using times_mat_def sumof4
                    by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                        dim_row_of_dagger i2 i4 index_matrix_prod j3 j4)
                  also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,3)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = cnj ((control2 U) $$ (3,2))"
                    using dagger_def 
                    by (metis carrier_matD(1) carrier_matD(2) control2_carrier_mat i2 i4 index_mat(1) 
                        j3 j4 prod.simps(2))
                  also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (2,3)" by simp
                  finally show ?thesis using i2 j3 by simp
                qed
              qed
            qed
          qed
        next
          assume i3:"i = 3"
          show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
          next
            assume j0:"j = 0"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (3,0) = 
                    (control2 U) $$ (3,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,0) +
                    (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,0) +
                    (control2 U) $$ (3,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,0) +
                    (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,0)"
                using times_mat_def sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger i3 i4 index_matrix_prod j0 j4)
              also have "\<dots> = (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,0) + 
                            (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,0)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = (control2 U) $$ (3,1) * (cnj ((control2 U) $$ (0,1))) + 
                            (control2 U) $$ (3,3) * (cnj ((control2 U) $$ (0,3)))"
                using dagger_def Tensor.mat_of_cols_list_def control2_def by auto
              also have "\<dots> = (control2 U) $$ (3,1) * (cnj 0) +
                            (control2 U) $$ (3,3) * (cnj 0)"
                using control2_def index_mat_of_cols_list by simp
              also have "\<dots> = 0" by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (3,0)" by simp
              finally show ?thesis using i3 j0 by simp
            qed
          next
            assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
            show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof (rule disjE)
              show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
            next
              assume j1:"j = 1"
              show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (3,1) = 
                    (control2 U) $$ (3,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,1) +
                    (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,1) +
                    (control2 U) $$ (3,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,1) +
                    (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,1)"
                  using times_mat_def sumof4
                  by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                      dim_row_of_dagger i3 i4 index_matrix_prod j1 j4)
                also have "\<dots> = (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,1) + 
                              (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,1)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = (control2 U) $$ (3,1) * (cnj ((control2 U) $$ (1,1))) + 
                              (control2 U) $$ (3,3) * (cnj ((control2 U) $$ (1,3)))"
                  using dagger_def Tensor.mat_of_cols_list_def control2_def by auto
                also have "\<dots> = U $$ (1,0) * (cnj (U $$ (0,0))) +
                            U $$ (1,1) * (cnj (U $$ (0,1)))"
                  using control2_def index_mat_of_cols_list by simp
                also have "\<dots> = (U $$ (1,0)) * ((U\<^sup>\<dagger>) $$ (0,0)) +
                            (U $$ (1,1)) * ((U\<^sup>\<dagger>) $$ (1,0))"
                  using dagger_def assms(1) gate_def by force
                also have "\<dots> = (U * (U\<^sup>\<dagger>)) $$ (1,0)" 
                  using times_mat_def assms(1) gate_carrier_mat sumof2
                  by (smt (z3) Suc_1 carrier_matD(2) dagger_def dim_col_mat(1) dim_row_of_dagger 
                      gate.dim_row index_matrix_prod lessI pos2 power_one_right)
                also have "\<dots> = (1\<^sub>m 2) $$ (1,0)" using assms(1) gate_def unitary_def by auto
                also have "\<dots> = 0" by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (3,1)" by simp
                finally show ?thesis using i3 j1 by simp
              qed
            next
              assume jl2:"j = 2 \<or> j = 3"
              show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof (rule disjE)
                show "j = 2 \<or> j = 3" using jl2 by this
              next
                assume j2:"j = 2"
                show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (3,2) = 
                    (control2 U) $$ (3,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,2) +
                    (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,2) +
                    (control2 U) $$ (3,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,2) +
                    (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,2)"
                    using times_mat_def sumof4
                    by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                        dim_row_of_dagger i3 i4 index_matrix_prod j2 j4)
                  also have "\<dots> = (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,2) + 
                                (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,2)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = (control2 U) $$ (3,1) * (cnj ((control2 U) $$ (2,1))) + 
                                (control2 U) $$ (3,3) * (cnj ((control2 U) $$ (2,3)))"
                    using dagger_def Tensor.mat_of_cols_list_def control2_def by auto
                  also have "\<dots> = (control2 U) $$ (3,1) * (cnj 0) +
                                (control2 U) $$ (3,3) * (cnj 0)"
                    using control2_def index_mat_of_cols_list by simp
                  also have "\<dots> = 0" by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (3,2)" by simp
                  finally show ?thesis using i3 j2 by simp
                qed
              next
                assume j3:"j = 3"
                show "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "(control2 U * ((control2 U)\<^sup>\<dagger>)) $$ (3,3) = 
                    (control2 U) $$ (3,0) * ((control2 U)\<^sup>\<dagger>) $$ (0,3) +
                    (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,3) +
                    (control2 U) $$ (3,2) * ((control2 U)\<^sup>\<dagger>) $$ (2,3) +
                    (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,3)"
                    using times_mat_def sumof4
                    by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                        dim_row_of_dagger i3 i4 index_matrix_prod j3 j4)
                  also have "\<dots> = (control2 U) $$ (3,1) * ((control2 U)\<^sup>\<dagger>) $$ (1,3) + 
                                (control2 U) $$ (3,3) * ((control2 U)\<^sup>\<dagger>) $$ (3,3)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = (control2 U) $$ (3,1) * (cnj ((control2 U) $$ (3,1))) + 
                                (control2 U) $$ (3,3) * (cnj ((control2 U) $$ (3,3)))"
                    using dagger_def Tensor.mat_of_cols_list_def control2_def by auto
                  also have "\<dots> = U $$ (1,0) * (cnj (U $$ (1,0))) +
                              U $$ (1,1) * (cnj (U $$ (1,1)))"
                    using control2_def index_mat_of_cols_list by simp
                  also have "\<dots> = (U $$ (1,0)) * ((U\<^sup>\<dagger>) $$ (0,1)) +
                              (U $$ (1,1)) * ((U\<^sup>\<dagger>) $$ (1,1))"
                    using dagger_def assms(1) gate_def by force
                  also have "\<dots> = (U * (U\<^sup>\<dagger>)) $$ (1,1)" 
                    using times_mat_def assms(1) gate_carrier_mat sumof2
                    by (smt (z3) Suc_1 carrier_matD(2) dagger_def dim_col_mat(1) dim_row_of_dagger 
                        gate.dim_row index_matrix_prod lessI pos2 power_one_right)
                  also have "\<dots> = (1\<^sub>m 2) $$ (1,1)" using assms(1) gate_def unitary_def by auto
                  also have "\<dots> = 1" by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (3,3)" by simp
                  finally show ?thesis using i3 j3 by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  show "dim_row (control2 U * ((control2 U)\<^sup>\<dagger>)) = dim_row (1\<^sub>m 4)"
    by (metis carrier_matD(1) control2_carrier_mat index_mult_mat(2) index_one_mat(2))
next
  show "dim_col (control2 U * ((control2 U)\<^sup>\<dagger>)) = dim_col (1\<^sub>m 4)"
    by (metis carrier_matD(1) control2_carrier_mat dim_col_of_dagger index_mult_mat(3) 
        index_one_mat(3))
qed

lemma control2_inv':
  assumes "gate 1 U"
  shows "(control2 U)\<^sup>\<dagger> * (control2 U) = 1\<^sub>m 4"
proof
  show "\<And>i j. i < dim_row (1\<^sub>m 4) \<Longrightarrow> j < dim_col (1\<^sub>m 4) \<Longrightarrow>
           ((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
  proof -
    fix i j
    assume "i < dim_row (1\<^sub>m 4)"
    hence i4:"i < 4" by auto
    assume "j < dim_col (1\<^sub>m 4)"
    hence j4:"j < 4" by auto
    show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
    proof (rule disjE)
      show "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" using i4 by auto
    next
      assume i0:"i = 0"
      show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
      proof (rule disjE)
        show "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
      next
        assume j0:"j = 0"
        show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof -
          have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (0,0) =
                ((control2 U)\<^sup>\<dagger>) $$ (0,0) * (control2 U) $$ (0,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,1) * (control2 U) $$ (1,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,2) * (control2 U) $$ (2,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,3) * (control2 U) $$ (3,0)"
            using sumof4
            by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) control2_carrier_mat 
                dim_col_of_dagger dim_row_of_dagger i0 i4 index_matrix_prod)
          also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,0)"
            using control2_def index_mat_of_cols_list by force
          also have "\<dots> = cnj ((control2 U) $$ (0,0))"
            using dagger_def
            by (simp add: Tensor.mat_of_cols_list_def control2_def)
          also have "\<dots> = 1" using control2_def index_mat_of_cols_list by auto
          also have "\<dots> = 1\<^sub>m 4 $$ (0,0)" by simp
          finally show ?thesis using i0 j0 by simp
        qed
      next
        assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
        show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof (rule disjE)
          show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
        next
          assume j1:"j = 1"
          show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof -
            have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (0,1) =
                ((control2 U)\<^sup>\<dagger>) $$ (0,0) * (control2 U) $$ (0,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,1) * (control2 U) $$ (1,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,2) * (control2 U) $$ (2,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,3) * (control2 U) $$ (3,1)"
              using sumof4
              by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                  dim_row_of_dagger index_matrix_prod one_less_numeral_iff semiring_norm(76) 
                  zero_less_numeral)
            also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,1) * (control2 U) $$ (1,1) +
                            ((control2 U)\<^sup>\<dagger>) $$ (0,3) * (control2 U) $$ (3,1)"
              using control2_def index_mat_of_cols_list by force
            also have "\<dots> = cnj ((control2 U) $$ (1,0)) * (control2 U) $$ (1,1) +
                            cnj ((control2 U) $$ (3,0)) * (control2 U) $$ (3,1)"
              using dagger_def
              by (simp add: Tensor.mat_of_cols_list_def control2_def)
            also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
            also have "\<dots> = 1\<^sub>m 4 $$ (0,1)" by simp
            finally show ?thesis using i0 j1 by simp
          qed
        next
          assume jl2:"j = 2 \<or> j = 3"
          show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 2 \<or> j = 3" using jl2 by this
          next
            assume j2:"j = 2"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (0,2) =
                ((control2 U)\<^sup>\<dagger>) $$ (0,0) * (control2 U) $$ (0,2) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,1) * (control2 U) $$ (1,2) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,2) * (control2 U) $$ (2,2) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,3) * (control2 U) $$ (3,2)"
                using sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger index_matrix_prod j2 j4 zero_less_numeral)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,2)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (2,0))"
                using dagger_def
                by (simp add: Tensor.mat_of_cols_list_def control2_def)
              also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (0,2)" by simp
              finally show ?thesis using i0 j2 by simp
            qed
          next
            assume j3:"j = 3"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (0,3) =
                ((control2 U)\<^sup>\<dagger>) $$ (0,0) * (control2 U) $$ (0,3) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,1) * (control2 U) $$ (1,3) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,2) * (control2 U) $$ (2,3) +
                ((control2 U)\<^sup>\<dagger>) $$ (0,3) * (control2 U) $$ (3,3)"
                using sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger index_matrix_prod j3 j4 zero_less_numeral)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (0,1) * (control2 U) $$ (1,3) +
                              ((control2 U)\<^sup>\<dagger>) $$ (0,3) * (control2 U) $$ (3,3)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (1,0)) * (control2 U) $$ (1,3) +
                              cnj ((control2 U) $$ (3,0)) * (control2 U) $$ (3,3)"
                using dagger_def
                by (simp add: Tensor.mat_of_cols_list_def control2_def)
              also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (0,3)" by simp
              finally show ?thesis using i0 j3 by simp
            qed
          qed
        qed
      qed
    next
      assume il3:"i = 1 \<or> i = 2 \<or> i = 3"
      show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
      proof (rule disjE)
        show "i = 1 \<or> i = 2 \<or> i = 3" using il3 by this
      next
        assume i1:"i = 1"
        show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof (rule disjE)
          show "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
        next
          assume j0:"j = 0"
          show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof -
            have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (1,0) =
                ((control2 U)\<^sup>\<dagger>) $$ (1,0) * (control2 U) $$ (0,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,1) * (control2 U) $$ (1,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,2) * (control2 U) $$ (2,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,3) * (control2 U) $$ (3,0)"
              using sumof4
              by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                  dim_row_of_dagger index_matrix_prod one_less_numeral_iff semiring_norm(76) 
                  zero_less_numeral)
            also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (1,0)"
              using control2_def index_mat_of_cols_list by force
            also have "\<dots> = cnj ((control2 U) $$ (0,1))"
              using dagger_def
              by (simp add: Tensor.mat_of_cols_list_def control2_def)
            also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
            also have "\<dots> = 1\<^sub>m 4 $$ (1,0)" by simp
            finally show ?thesis using i1 j0 by simp
          qed
        next
          assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
          show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
          next
            assume j1:"j = 1"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (1,1) =
                ((control2 U)\<^sup>\<dagger>) $$ (1,0) * (control2 U) $$ (0,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,1) * (control2 U) $$ (1,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,2) * (control2 U) $$ (2,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,3) * (control2 U) $$ (3,1)"
                using sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger 
                    dim_row_of_dagger index_matrix_prod one_less_numeral_iff semiring_norm(76) 
                    zero_less_numeral)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (1,1) * (control2 U) $$ (1,1) +
                              ((control2 U)\<^sup>\<dagger>) $$ (1,3) * (control2 U) $$ (3,1)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (1,1)) * (control2 U) $$ (1,1) +
                              cnj ((control2 U) $$ (3,1)) * (control2 U) $$ (3,1)"
                using dagger_def
                by (simp add: Tensor.mat_of_cols_list_def control2_def)
              also have "\<dots> = cnj (U $$ (0,0)) * (U $$ (0,0)) +
                              cnj (U $$ (1,0)) * (U $$ (1,0))"
                using control2_def index_mat_of_cols_list by simp
              also have "\<dots> = ((U\<^sup>\<dagger>) * U) $$ (0,0)"
                using times_mat_def sumof2 assms(1) gate_carrier_mat
                by (smt (verit, del_insts) Suc_1 carrier_matD(2) dagger_def dim_col_mat(1) 
                    dim_row_of_dagger gate.dim_row index_mat(1) index_matrix_prod lessI 
                    old.prod.case pos2 power_one_right)
              also have "\<dots> = (1\<^sub>m 2) $$ (0,0)" using assms(1) gate_def unitary_def by auto
              also have "\<dots> = 1" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (1,1)" by simp
              finally show ?thesis using i1 j1 by simp
            qed
          next
            assume jl2:"j = 2 \<or> j = 3"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof (rule disjE)
              show "j = 2 \<or> j = 3" using jl2 by this
            next
              assume j2:"j = 2"
              show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (1,2) =
                ((control2 U)\<^sup>\<dagger>) $$ (1,0) * (control2 U) $$ (0,2) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,1) * (control2 U) $$ (1,2) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,2) * (control2 U) $$ (2,2) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,3) * (control2 U) $$ (3,2)"
                  using sumof4
                  by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat 
                      dim_col_of_dagger dim_row_of_dagger index_matrix_prod j2 j4 
                      one_less_numeral_iff semiring_norm(76))
                also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (1,2)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = cnj ((control2 U) $$ (2,1))"
                  using dagger_def
                  by (simp add: Tensor.mat_of_cols_list_def control2_def)
                also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (1,2)" by simp
                finally show ?thesis using i1 j2 by simp
              qed
            next
              assume j3:"j = 3"
              show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (1,3) =
                ((control2 U)\<^sup>\<dagger>) $$ (1,0) * (control2 U) $$ (0,3) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,1) * (control2 U) $$ (1,3) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,2) * (control2 U) $$ (2,3) +
                ((control2 U)\<^sup>\<dagger>) $$ (1,3) * (control2 U) $$ (3,3)"
                  using sumof4
                  by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) 
                      control2_carrier_mat dim_col_of_dagger dim_row_of_dagger i1 i4 
                      index_matrix_prod j3 j4)
                also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (1,1) * (control2 U) $$ (1,3) +
                                ((control2 U)\<^sup>\<dagger>) $$ (1,3) * (control2 U) $$ (3,3)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = cnj ((control2 U) $$ (1,1)) * (control2 U) $$ (1,3) +
                                cnj ((control2 U) $$ (3,1)) * (control2 U) $$ (3,3)"
                  using dagger_def
                  by (simp add: Tensor.mat_of_cols_list_def control2_def)
                also have "\<dots> = cnj (U $$ (0,0)) * (U $$ (0,1)) +
                                cnj (U $$ (1,0)) * (U $$ (1,1))"
                  using control2_def index_mat_of_cols_list by simp
                also have "\<dots> = ((U\<^sup>\<dagger>) * U) $$ (0,1)"
                  using times_mat_def sumof2 assms(1) gate_carrier_mat
                  by (smt (verit, del_insts) Suc_1 carrier_matD(2) dagger_def dim_col_mat(1) 
                      dim_row_of_dagger gate.dim_row index_mat(1) index_matrix_prod lessI 
                      old.prod.case pos2 power_one_right)
                also have "\<dots> = (1\<^sub>m 2) $$ (0,1)" using assms(1) gate_def unitary_def by auto
                also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (1,3)" by simp
                finally show ?thesis using i1 j3 by simp
              qed
            qed
          qed
        qed
      next
        assume il2:"i = 2 \<or> i = 3"
        show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
        proof (rule disjE)
          show "i = 2 \<or> i = 3" using il2 by this
        next
          assume i2:"i = 2"
          show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
          next
            assume j0:"j = 0"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (2,0) =
                ((control2 U)\<^sup>\<dagger>) $$ (2,0) * (control2 U) $$ (0,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (2,1) * (control2 U) $$ (1,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (2,2) * (control2 U) $$ (2,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (2,3) * (control2 U) $$ (3,0)"
                using sumof4
                by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger
                    dim_row_of_dagger i2 i4 index_matrix_prod zero_less_numeral)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,0)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (0,2))"
                using dagger_def
                by (simp add: Tensor.mat_of_cols_list_def control2_def)
              also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (2,0)" by simp
              finally show ?thesis using i2 j0 by simp
            qed
          next
            assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof (rule disjE)
              show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
            next
              assume j1:"j = 1"
              show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (2,1) =
                ((control2 U)\<^sup>\<dagger>) $$ (2,0) * (control2 U) $$ (0,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (2,1) * (control2 U) $$ (1,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (2,2) * (control2 U) $$ (2,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (2,3) * (control2 U) $$ (3,1)"
                  using sumof4
                  by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat 
                      dim_col_of_dagger dim_row_of_dagger i2 i4 index_matrix_prod 
                      one_less_numeral_iff semiring_norm(76))
                also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,1) * (control2 U) $$ (1,1) +
                                ((control2 U)\<^sup>\<dagger>) $$ (2,3) * (control2 U) $$ (3,1)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = cnj ((control2 U) $$ (1,2)) * (control2 U) $$ (1,1) +
                                cnj ((control2 U) $$ (3,2)) * (control2 U) $$ (3,1)"
                  using dagger_def
                  by (simp add: Tensor.mat_of_cols_list_def control2_def)
                also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (2,1)" by simp
                finally show ?thesis using i2 j1 by simp
              qed
            next
              assume jl2:"j = 2 \<or> j = 3"
              show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof (rule disjE)
                show "j = 2 \<or> j = 3" using jl2 by this
              next
                assume j2:"j = 2"
                show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (2,2) =
                        ((control2 U)\<^sup>\<dagger>) $$ (2,0) * (control2 U) $$ (0,2) +
                        ((control2 U)\<^sup>\<dagger>) $$ (2,1) * (control2 U) $$ (1,2) +
                        ((control2 U)\<^sup>\<dagger>) $$ (2,2) * (control2 U) $$ (2,2) +
                        ((control2 U)\<^sup>\<dagger>) $$ (2,3) * (control2 U) $$ (3,2)"
                    using sumof4
                    by (smt (z3) carrier_matD(1) carrier_matD(2) control2_carrier_mat dim_col_of_dagger
                        dim_row_of_dagger i2 i4 index_matrix_prod zero_less_numeral)
                  also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,2)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = cnj ((control2 U) $$ (2,2))"
                    using dagger_def
                    by (simp add: Tensor.mat_of_cols_list_def control2_def)
                  also have "\<dots> = 1" using control2_def index_mat_of_cols_list by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (2,2)" by simp
                  finally show ?thesis using i2 j2 by simp
                qed
              next
                assume j3:"j = 3"
                show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (2,3) =
                        ((control2 U)\<^sup>\<dagger>) $$ (2,0) * (control2 U) $$ (0,3) +
                        ((control2 U)\<^sup>\<dagger>) $$ (2,1) * (control2 U) $$ (1,3) +
                        ((control2 U)\<^sup>\<dagger>) $$ (2,2) * (control2 U) $$ (2,3) +
                        ((control2 U)\<^sup>\<dagger>) $$ (2,3) * (control2 U) $$ (3,3)"
                    using sumof4
                    by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) 
                        control2_carrier_mat dim_col_of_dagger dim_row_of_dagger i2 i4 
                        index_matrix_prod j3 j4)
                  also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (2,1) * (control2 U) $$ (1,3) +
                                  ((control2 U)\<^sup>\<dagger>) $$ (2,3) * (control2 U) $$ (3,3)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = cnj ((control2 U) $$ (1,2)) * (control2 U) $$ (1,3) +
                                  cnj ((control2 U) $$ (3,2)) * (control2 U) $$ (3,3)"
                    using dagger_def
                    by (simp add: Tensor.mat_of_cols_list_def control2_def)
                  also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (2,3)" by simp
                  finally show ?thesis using i2 j3 by simp
                qed
              qed
            qed
          qed
        next
          assume i3:"i = 3"
          show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
          proof (rule disjE)
            show "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using j4 by auto
          next
            assume j0:"j = 0"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof -
              have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (3,0) =
                ((control2 U)\<^sup>\<dagger>) $$ (3,0) * (control2 U) $$ (0,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (3,1) * (control2 U) $$ (1,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (3,2) * (control2 U) $$ (2,0) +
                ((control2 U)\<^sup>\<dagger>) $$ (3,3) * (control2 U) $$ (3,0)"
                using sumof4
                by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) control2_carrier_mat 
                    dim_col_of_dagger dim_row_of_dagger i3 i4 index_matrix_prod j0 j4)
              also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (3,0)"
                using control2_def index_mat_of_cols_list by force
              also have "\<dots> = cnj ((control2 U) $$ (0,3))"
                using dagger_def
                by (simp add: Tensor.mat_of_cols_list_def control2_def)
              also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
              also have "\<dots> = 1\<^sub>m 4 $$ (3,0)" by simp
              finally show ?thesis using i3 j0 by simp
            qed
          next
            assume jl3:"j = 1 \<or> j = 2 \<or> j = 3"
            show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
            proof (rule disjE)
              show "j = 1 \<or> j = 2 \<or> j = 3" using jl3 by this
            next
              assume j1:"j = 1"
              show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof -
                have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (3,1) =
                ((control2 U)\<^sup>\<dagger>) $$ (3,0) * (control2 U) $$ (0,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (3,1) * (control2 U) $$ (1,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (3,2) * (control2 U) $$ (2,1) +
                ((control2 U)\<^sup>\<dagger>) $$ (3,3) * (control2 U) $$ (3,1)"
                  using sumof4
                  by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) 
                      control2_carrier_mat dim_col_of_dagger dim_row_of_dagger i3 i4 
                      index_matrix_prod j1 j4)
                also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (3,1) * (control2 U) $$ (1,1) +
                                ((control2 U)\<^sup>\<dagger>) $$ (3,3) * (control2 U) $$ (3,1)"
                  using control2_def index_mat_of_cols_list by force
                also have "\<dots> = cnj ((control2 U) $$ (1,3)) * (control2 U) $$ (1,1) +
                                cnj ((control2 U) $$ (3,3)) * (control2 U) $$ (3,1)"
                  using dagger_def
                  by (simp add: Tensor.mat_of_cols_list_def control2_def)
                also have "\<dots> = cnj (U $$ (0,1)) * (U $$ (0,0)) +
                                cnj (U $$ (1,1)) * (U $$ (1,0))"
                  using control2_def index_mat_of_cols_list by simp
                also have "\<dots> = ((U\<^sup>\<dagger>) * U) $$ (1,0)"
                  using times_mat_def sumof2 assms(1) gate_carrier_mat
                  by (smt (verit, del_insts) Suc_1 carrier_matD(2) dagger_def dim_col_mat(1) 
                      dim_row_of_dagger gate.dim_row index_mat(1) index_matrix_prod lessI 
                      old.prod.case pos2 power_one_right)
                also have "\<dots> = (1\<^sub>m 2) $$ (1,0)" using assms(1) gate_def unitary_def by auto
                also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                also have "\<dots> = 1\<^sub>m 4 $$ (3,1)" by simp
                finally show ?thesis using i3 j1 by simp
              qed
            next
              assume jl2:"j = 2 \<or> j = 3"
              show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
              proof (rule disjE)
                show "j = 2 \<or> j = 3" using jl2 by this
              next
                assume j2:"j = 2"
                show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (3,2) =
                        ((control2 U)\<^sup>\<dagger>) $$ (3,0) * (control2 U) $$ (0,2) +
                        ((control2 U)\<^sup>\<dagger>) $$ (3,1) * (control2 U) $$ (1,2) +
                        ((control2 U)\<^sup>\<dagger>) $$ (3,2) * (control2 U) $$ (2,2) +
                        ((control2 U)\<^sup>\<dagger>) $$ (3,3) * (control2 U) $$ (3,2)"
                    using sumof4
                    by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) control2_carrier_mat 
                        dim_col_of_dagger dim_row_of_dagger i3 i4 index_matrix_prod j2 j4)
                  also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (3,2)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = cnj ((control2 U) $$ (2,3))"
                    using dagger_def
                    by (simp add: Tensor.mat_of_cols_list_def control2_def)
                  also have "\<dots> = 0" using control2_def index_mat_of_cols_list by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (3,2)" by simp
                  finally show ?thesis using i3 j2 by simp
                qed
              next
                assume j3:"j = 3"
                show "((control2 U)\<^sup>\<dagger> * control2 U) $$ (i, j) = 1\<^sub>m 4 $$ (i, j)"
                proof -
                  have "((control2 U)\<^sup>\<dagger> * control2 U) $$ (3,3) =
                        ((control2 U)\<^sup>\<dagger>) $$ (3,0) * (control2 U) $$ (0,3) +
                        ((control2 U)\<^sup>\<dagger>) $$ (3,1) * (control2 U) $$ (1,3) +
                        ((control2 U)\<^sup>\<dagger>) $$ (3,2) * (control2 U) $$ (2,3) +
                        ((control2 U)\<^sup>\<dagger>) $$ (3,3) * (control2 U) $$ (3,3)"
                    using sumof4
                    by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) 
                        control2_carrier_mat dim_col_of_dagger dim_row_of_dagger i3 
                        index_matrix_prod j3 j4)
                  also have "\<dots> = ((control2 U)\<^sup>\<dagger>) $$ (3,1) * (control2 U) $$ (1,3) +
                                  ((control2 U)\<^sup>\<dagger>) $$ (3,3) * (control2 U) $$ (3,3)"
                    using control2_def index_mat_of_cols_list by force
                  also have "\<dots> = cnj ((control2 U) $$ (1,3)) * (control2 U) $$ (1,3) +
                                  cnj ((control2 U) $$ (3,3)) * (control2 U) $$ (3,3)"
                    using dagger_def
                    by (simp add: Tensor.mat_of_cols_list_def control2_def)
                  also have "\<dots> = cnj (U $$ (0,1)) * (U $$ (0,1)) +
                                  cnj (U $$ (1,1)) * (U $$ (1,1))"
                    using control2_def index_mat_of_cols_list by simp
                  also have "\<dots> = ((U\<^sup>\<dagger>) * U) $$ (1,1)"
                    using times_mat_def sumof2 assms(1) gate_carrier_mat
                    by (smt (verit, del_insts) Suc_1 carrier_matD(2) dagger_def dim_col_mat(1) 
                        dim_row_of_dagger gate.dim_row index_mat(1) index_matrix_prod lessI 
                        old.prod.case pos2 power_one_right)
                  also have "\<dots> = (1\<^sub>m 2) $$ (1,1)" using assms(1) gate_def unitary_def by auto
                  also have "\<dots> = 1" using control2_def index_mat_of_cols_list by auto
                  also have "\<dots> = 1\<^sub>m 4 $$ (3,3)" by simp
                  finally show ?thesis using i3 j3 by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  show "dim_row ((control2 U)\<^sup>\<dagger> * control2 U) = dim_row (1\<^sub>m 4)"
    by (metis carrier_matD(2) control2_carrier_mat dim_row_of_dagger 
        index_mult_mat(2) index_one_mat(2))
next
  show "dim_col ((control2 U)\<^sup>\<dagger> * control2 U) = dim_col (1\<^sub>m 4)"
    by (metis carrier_matD(2) control2_carrier_mat index_mult_mat(3) 
        index_one_mat(3))
qed

lemma control2_is_gate:
  assumes "gate 1 U"
  shows "gate 2 (control2 U)"
proof
  show "dim_row (control2 U) = 2^2" using control2_carrier_mat 
    by (simp add: Tensor.mat_of_cols_list_def control2_def)
next
  show "square_mat (control2 U)"
    by (metis carrier_matD(1) carrier_matD(2) control2_carrier_mat square_mat.elims(3))
next
  show "unitary (control2 U)" 
    using control2_inv control2_inv' unitary_def
    by (metis assms carrier_matD(1) carrier_matD(2) control2_carrier_mat)
qed

lemma SWAP_down_is_gate:
  shows "gate n (SWAP_down n)"
proof (induct n rule: SWAP_down.induct)
  case 1
  then show ?case
    by (metis Quantum.Id_def SWAP_down.simps(1) SWAP_up.simps(1) SWAP_up_carrier_mat 
        carrier_matD(2) id_is_gate index_one_mat(3))
next
  case 2
  then show ?case
    by (metis H_inv H_is_gate One_nat_def SWAP_down.simps(2) prod_of_gate_is_gate)
next
  case 3
  then show ?case
    by (metis One_nat_def SWAP_down.simps(3) SWAP_is_gate Suc_1)
next
  case (4 v)
  then show ?case
  proof -
    assume HI:"gate (Suc (Suc v)) (SWAP_down (Suc (Suc v)))"
    show "gate (Suc (Suc (Suc v))) (SWAP_down (Suc (Suc (Suc v))))"
    proof -
      have "gate (Suc (Suc (Suc v))) (((1\<^sub>m (2^Suc v)) \<Otimes> SWAP) * 
                                      ((SWAP_down (Suc (Suc v))) \<Otimes> (1\<^sub>m 2)))"
      proof (rule prod_of_gate_is_gate)
        show "gate (Suc (Suc (Suc v))) (1\<^sub>m (2 ^ Suc v) \<Otimes> SWAP)"
          using SWAP_is_gate tensor_gate
          by (metis Quantum.Id_def add_2_eq_Suc' id_is_gate)
      next
        show "gate (Suc (Suc (Suc v))) (SWAP_down (Suc (Suc v)) \<Otimes> 1\<^sub>m 2)"
          using HI tensor_gate
          by (metis Suc_eq_plus1 Y_inv Y_is_gate prod_of_gate_is_gate)
      qed
      thus ?thesis using SWAP_down.simps by auto
    qed
  qed
qed

lemma SWAP_up_is_gate:
  shows "gate n (SWAP_up n)"
proof (induct n rule: SWAP_up.induct)
  case 1
  then show ?case using id_is_gate SWAP_up.simps
    by (metis SWAP_down.simps(1) SWAP_down_is_gate)
next
  case 2
  then show ?case
    by (metis SWAP_down.simps(2) SWAP_down_is_gate SWAP_up.simps(2))
next
  case 3
  then show ?case 
    by (metis One_nat_def SWAP_is_gate SWAP_up.simps(3) Suc_1)
next
  case (4 v)
  then show ?case
  proof -
    assume HI:"gate (Suc (Suc v)) (SWAP_up (Suc (Suc v)))"
    show "gate (Suc (Suc (Suc v))) (SWAP_up (Suc (Suc (Suc v))))"
    proof -
      have "gate (Suc (Suc (Suc v))) ((SWAP \<Otimes> (1\<^sub>m (2^(Suc v)))) * ((1\<^sub>m 2) \<Otimes> 
                                      (SWAP_up (Suc (Suc v)))))"
      proof (rule prod_of_gate_is_gate)
        show "gate (Suc (Suc (Suc v))) (SWAP \<Otimes> 1\<^sub>m (2 ^ Suc v))"
          using tensor_gate SWAP_is_gate
          by (metis Quantum.Id_def add_2_eq_Suc id_is_gate)
      next
        show "gate (Suc (Suc (Suc v))) (1\<^sub>m 2 \<Otimes> SWAP_up (Suc (Suc v)))"
          using tensor_gate HI 
          by (metis One_nat_def SWAP_down.simps(2) SWAP_down_is_gate plus_1_eq_Suc)
      qed
      thus ?thesis using SWAP_up.simps(3) by simp
    qed
  qed
qed

lemma control_is_gate:
  assumes "gate 1 U"
  shows "gate n (control n U)"
proof (cases n)
  case 0
  then show ?thesis
    by (metis SWAP_up.simps(1) SWAP_up_is_gate control.simps(1))
next
  case (Suc nat)
  then show ?thesis
  proof -
    assume nnat:"n = Suc nat"
    show "gate n (control n U)"
    proof -
      have "gate (Suc nat) (control (Suc nat) U)"
      proof (cases nat)
        case 0
        then show ?thesis 
          by (simp add: gate_def)
      next
        case (Suc nata)
        then show ?thesis
        proof -
          assume nnat_:"nat = Suc nata"
          show "gate (Suc nat) (control (Suc nat) U)"
          proof -
            have "gate (Suc (Suc nata)) (control (Suc (Suc nata)) U)"
            proof (cases nata)
              case 0
              then show ?thesis
                using One_nat_def Suc_1 assms control.simps(3) control2_is_gate by presburger
            next
              case (Suc natb)
              then show ?thesis
              proof -
                assume nnatb:"nata = Suc natb"
                show "gate (Suc (Suc nata)) (control (Suc (Suc nata)) U)"
                proof -
                  have "gate (Suc (Suc (Suc natb))) (control (Suc (Suc (Suc natb))) U)"
                  proof -
                    have "gate (Suc (Suc (Suc natb))) (((1\<^sub>m 2) \<Otimes> SWAP_down (Suc (Suc natb))) * 
                        (control2 U \<Otimes> (1\<^sub>m (2^(Suc natb)))) * ((1\<^sub>m 2) \<Otimes> SWAP_up (Suc (Suc natb))))"
                    proof (rule prod_of_gate_is_gate)+
                      show "gate (Suc (Suc (Suc natb))) (1\<^sub>m 2 \<Otimes> SWAP_down (Suc (Suc natb)))"
                        using SWAP_down_is_gate id_is_gate tensor_gate
                        by (metis One_nat_def SWAP_up.simps(2) SWAP_up_is_gate plus_1_eq_Suc)
                    next
                      show "gate (Suc (Suc (Suc natb))) (control2 U \<Otimes> 1\<^sub>m (2 ^ Suc natb))"
                        using control2_is_gate id_is_gate tensor_gate
                        by (metis Quantum.Id_def add_2_eq_Suc assms)
                    next
                      show "gate (Suc (Suc (Suc natb))) (1\<^sub>m 2 \<Otimes> SWAP_up (Suc (Suc natb)))"
                        using SWAP_up_is_gate id_is_gate tensor_gate
                        by (metis Y_inv Y_is_gate plus_1_eq_Suc prod_of_gate_is_gate)
                    qed
                    thus ?thesis using control.simps by simp
                  qed
                  thus ?thesis using nnatb by simp
                qed
              qed
            qed
            thus ?thesis using nnat_ by simp
          qed
        qed
      qed
      thus ?thesis using nnat by simp
    qed
  qed
qed

lemma controlled_rotations_is_gate:
  shows "gate n (controlled_rotations n)"
proof (induct n rule: controlled_rotations.induct)
  case 1
  then show ?case 
    by (metis SWAP_down.simps(1) SWAP_down_is_gate controlled_rotations.simps(1))
next
  case 2
  then show ?case 
    by (metis SWAP_down.simps(2) SWAP_down_is_gate controlled_rotations.simps(2))
next
  case (3 v)
  then show ?case
  proof -
    assume HI:"gate (Suc v) (controlled_rotations (Suc v))"
    show "gate (Suc (Suc v)) (controlled_rotations (Suc (Suc v)))"
    proof -
      have "gate (Suc (Suc v)) ((control (Suc (Suc v)) (R (Suc (Suc v)))) * 
                               ((controlled_rotations (Suc v)) \<Otimes> (1\<^sub>m 2)))"
      proof (rule prod_of_gate_is_gate)
        show "gate (Suc (Suc v)) (control (Suc (Suc v)) (R (Suc (Suc v))))"
          using control_is_gate R_is_gate by blast
      next
        show "gate (Suc (Suc v)) (controlled_rotations (Suc v) \<Otimes> 1\<^sub>m 2)"
          using tensor_gate HI id_is_gate 
          by (metis One_nat_def SWAP_up.simps(2) SWAP_up_is_gate Suc_eq_plus1)
      qed
      thus ?thesis using controlled_rotations.simps by simp
    qed
  qed
qed

theorem QFT_is_gate:
  shows "gate n (QFT n)"
proof (induction n rule: QFT.induct)
  case 1
  then show ?case
    by (metis QFT.simps(1) controlled_rotations.simps(1) controlled_rotations_is_gate)
next
  case 2
  then show ?case
    using H_is_gate by auto
next
  case (3 v)
  then show ?case
  proof -
    assume HI:"gate (Suc v) (QFT (Suc v))"
    show "gate (Suc (Suc v)) (QFT (Suc (Suc v)))"
    proof -
      have "gate (Suc (Suc v)) (((1\<^sub>m 2) \<Otimes> (QFT (Suc v))) * 
                                (controlled_rotations (Suc (Suc v))) * (H \<Otimes> ((1\<^sub>m (2^Suc v)))))"
      proof (rule prod_of_gate_is_gate)+
        show "gate (Suc (Suc v)) (1\<^sub>m 2 \<Otimes> QFT (Suc v))"
          using HI tensor_gate id_is_gate
          by (metis One_nat_def controlled_rotations.simps(2) controlled_rotations_is_gate 
              plus_1_eq_Suc)
        show "gate (Suc (Suc v)) (controlled_rotations (Suc (Suc v)))"
          using controlled_rotations_is_gate by metis
        show "gate (Suc (Suc v)) (H \<Otimes> 1\<^sub>m (2 ^ Suc v))"
          using H_is_gate id_is_gate tensor_gate 
          by (metis Quantum.Id_def plus_1_eq_Suc)
      qed
      thus ?thesis using QFT.simps by simp
    qed
  qed
qed

corollary QFT_is_unitary:
  shows "unitary (QFT n)"
  using QFT_is_gate gate_def by simp

corollary reverse_product_rep_is_state:
  assumes "j < 2^n"
  shows "state n (reverse_QFT_product_representation j n)"
  using QFT_is_gate QFT_is_correct gate_on_state_is_state assms state_basis_is_state
  by (metis dim_col_mat(1) dim_row_mat(1) index_unit_vec(3) ket_vec_col ket_vec_def 
      state_basis_def state_def unit_cpx_vec_length)

lemma reverse_qubits_is_gate:
  shows "gate n (reverse_qubits n)"
proof (induct n rule: reverse_qubits.induct)
  case 1
  then show ?case 
    by (metis QFT.simps(1) QFT_is_gate reverse_qubits.simps(1))
next
  case 2
  then show ?case
    using Y_is_gate prod_of_gate_is_gate by fastforce
next
  case 3
  then show ?case
    using One_nat_def SWAP_is_gate Suc_1 reverse_qubits.simps(3) by presburger
next
  case (4 va)
  then show ?case
  proof -
    assume HI:"gate (Suc (Suc va)) (reverse_qubits (Suc (Suc va)))"
    show "gate (Suc (Suc (Suc va))) (reverse_qubits (Suc (Suc (Suc va))))"
    proof -
      have "gate (Suc (Suc (Suc va))) (((reverse_qubits (Suc (Suc va))) \<Otimes> (1\<^sub>m 2)) *
                                         (SWAP_down (Suc (Suc (Suc va)))))"
      proof (rule prod_of_gate_is_gate)
        show "gate (Suc (Suc (Suc va))) (reverse_qubits (Suc (Suc va)) \<Otimes> 1\<^sub>m 2)"
          using HI id_is_gate tensor_gate 
          by (metis One_nat_def Suc_eq_plus1 controlled_rotations.simps(2) 
              controlled_rotations_is_gate)
      next
        show "gate (Suc (Suc (Suc va))) (SWAP_down (Suc (Suc (Suc va))))"
          using SWAP_down_is_gate by metis
      qed
      thus ?thesis using reverse_qubits.simps by simp
    qed
  qed
qed

theorem ordered_QFT_is_gate:
  shows "gate n (ordered_QFT n)"
  using reverse_qubits_is_gate QFT_is_gate ordered_QFT_def prod_of_gate_is_gate by auto

corollary ordered_QFT_is_unitary:
  shows "unitary (ordered_QFT n)"
  using ordered_QFT_is_gate gate_def by simp

corollary product_rep_is_state:
  assumes "j < 2^n"
  shows "state n (QFT_product_representation j n)"
  using ordered_QFT_is_gate ordered_QFT_is_correct gate_on_state_is_state assms 
    state_basis_is_state
  by (metis reverse_product_rep_is_state reverse_qubits_is_gate 
      reverse_qubits_product_representation)

end