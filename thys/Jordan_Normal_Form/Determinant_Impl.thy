(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Equations for Determinants\<close>

text \<open>We compute determinants on arbitrary rings by applying elementary row-operations
  to bring a matrix on upper-triangular form. Then the determinant can be determined
  by multiplying all entries on the diagonal. Moreover the final result has to be divided
  by a factor which is determined by the row-operations that we performed. To this end,
  we require a division operation on the element type.\<close>

theory Determinant_Impl
imports
  Determinant
begin

context
begin

subsection {* Properties of triangular matrices *}

text {*
  Each column of a triangular matrix should satisfy the following property.
*}

definition triangular_column::"nat \<Rightarrow> 'a::zero mat \<Rightarrow> bool"
  where "triangular_column j A \<equiv> \<forall>i. j < i \<longrightarrow> i < dim\<^sub>r A \<longrightarrow> A $$ (i,j) = 0"

lemma triangular_columnD [dest]:
  "triangular_column j A \<Longrightarrow> j < i \<Longrightarrow> i < dim\<^sub>r A \<Longrightarrow> A $$ (i,j) = 0"
  unfolding triangular_column_def by auto

lemma triangular_columnI [intro]:
  "(\<And>i. j < i \<Longrightarrow> i < dim\<^sub>r A \<Longrightarrow> A $$ (i,j) = 0) \<Longrightarrow> triangular_column j A"
  unfolding triangular_column_def by auto

text {*
  The following predicate states that the first $k$ columns satisfy
  triangularity.
*}

definition triangular_to:: "nat \<Rightarrow> 'a::zero mat \<Rightarrow> bool"
  where "triangular_to k A == \<forall>j. j<k \<longrightarrow> triangular_column j A"

lemma triangular_to_triangular: "upper_triangular A = triangular_to (dim\<^sub>r A) A"
  unfolding triangular_to_def triangular_column_def upper_triangular_def
  by auto

lemma triangular_toD [dest]:
  "triangular_to k A \<Longrightarrow> j < k \<Longrightarrow> j < i \<Longrightarrow> i < dim\<^sub>r A \<Longrightarrow> A $$ (i,j) = 0"
  unfolding triangular_to_def triangular_column_def by auto

lemma triangular_toI [intro]:
  "(\<And>i j. j < k \<Longrightarrow> j < i \<Longrightarrow> i < dim\<^sub>r A \<Longrightarrow> A $$ (i,j) = 0) \<Longrightarrow> triangular_to k A"
  unfolding triangular_to_def triangular_column_def by auto

lemma triangle_growth:
  assumes tri:"triangular_to k A"
  and col:"triangular_column k A"
  shows "triangular_to (Suc k) A"
  unfolding triangular_to_def
proof (intro allI impI)
  fix i assume iSk:"i < Suc k"
  show "triangular_column i A"
  proof (cases "i = k")
    case True
      then show ?thesis using col by auto next
    case False
      then have "i < k" using iSk by auto
      thus ?thesis using tri unfolding triangular_to_def by auto
  qed
qed

lemma triangle_trans: "triangular_to k A \<Longrightarrow> k > k' \<Longrightarrow> triangular_to k' A"
  by (intro triangular_toI, elim triangular_toD, auto)


subsection {* Algorithms for Triangulization *}

private definition mute :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat"
  where
  "mute k l rA = (fst rA * snd rA $$ (l,l), addrow (-(snd rA $$ (k,l))) k l (multrow k (snd rA $$ (l,l)) (snd rA)))"

lemma mute_code[code]: "mute k l (r,A) \<equiv>
  let q = A $$ (l,l) in (r * q, addrow (-(A $$ (k,l))) k l (multrow k q A))"
  unfolding mute_def Let_def by auto

lemma mute_preserves_dimensions:
  assumes "mute k l (r,A) = (r',A')"
  shows [simp]: "dim\<^sub>r A' = dim\<^sub>r A" and [simp]: "dim\<^sub>c A' = dim\<^sub>c A"
using assms unfolding mute_def by auto

text {*
  Algorithm @{term "mute k l"} makes $k$-th row $l$-th column element to 0.
*}

lemma mute_makes_0 :
 "mute k l (r,A) = (r',A') \<Longrightarrow>
  l < dim\<^sub>r A \<Longrightarrow>
  l < dim\<^sub>c A \<Longrightarrow>
  k < dim\<^sub>r A \<Longrightarrow>
  k \<noteq> l \<Longrightarrow>
  A' $$ (k,l) = 0"
  unfolding mute_def mat_addrow_def by auto

text {* It will not touch unexpected rows. *}
lemma mute_preserves:
  "mute k l (r,A) = (r',A') \<Longrightarrow>
   i < dim\<^sub>r A \<Longrightarrow>
   j < dim\<^sub>c A \<Longrightarrow>
   l < dim\<^sub>r A \<Longrightarrow>
   k < dim\<^sub>r A \<Longrightarrow>
   i \<noteq> k \<Longrightarrow>
   A' $$ (i,j) = A $$ (i,j)"
unfolding mute_def by auto

text {* It preserves $0$s in the touched row. *}
lemma mute_preserves_0:
  "mute k l (r,A) = (r',A') \<Longrightarrow>
   i < dim\<^sub>r A \<Longrightarrow>
   j < dim\<^sub>c A \<Longrightarrow>
   l < dim\<^sub>r A \<Longrightarrow>
   k < dim\<^sub>r A \<Longrightarrow>
   A $$ (i,j) = 0 \<Longrightarrow>
   A $$ (l,j) = 0 \<Longrightarrow>
   A' $$ (i,j) = 0"
  unfolding mute_def by auto

text {* Hence, it will respect partially triangular matrix. *}
lemma mute_preserves_triangle:
 assumes rA' : "mute k l (r,A) = (r',A')"
 and triA: "triangular_to l A"
 and lk: "l < k"
 and kr: "k < dim\<^sub>r A"
 and lr: "l < dim\<^sub>r A"
 and lc: "l < dim\<^sub>c A"
 shows "triangular_to l A'"
proof (rule triangular_toI)
  fix i j
  assume jl: "j < l" and ji: "j < i" and ir': "i < dim\<^sub>r A'"
  then have A0: "A $$ (i,j) = 0" using triA rA' by auto
  moreover have "A $$ (l,j) = 0" using triA jl jl lr by auto
  moreover have jc:"j < dim\<^sub>c A" using jl lc by auto
  moreover have ir: "i < dim\<^sub>r A" using ir' rA' by auto
  ultimately show "A' $$ (i,j) = 0"
    using mute_preserves_0[OF rA'] lr kr by auto
qed


text {* Recursive application of @{const mute} *}

private fun sub1 :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat"
where "sub1 0 l rA = rA"
  | "sub1 (Suc k) l rA = mute (l + Suc k) l (sub1 k l rA)"

lemma sub1_preserves_dimensions[simp]:
  "sub1 k l (r,A) = (r',A') \<Longrightarrow> dim\<^sub>r A' = dim\<^sub>r A"
  "sub1 k l (r,A) = (r',A') \<Longrightarrow> dim\<^sub>c A' = dim\<^sub>c A"
proof (induction k arbitrary: r' A')
  case (Suc k)
    moreover obtain r' A' where rA': "sub1 k l (r, A) = (r', A')" by force
    moreover fix r'' A'' assume "sub1 (Suc k) l (r, A) = (r'', A'')" 
    ultimately show "dim\<^sub>r A'' = dim\<^sub>r A" "dim\<^sub>c A'' = dim\<^sub>c A" by auto
qed auto

lemma sub1_closed [simp]:
  "sub1 k l (r,A) = (r',A') \<Longrightarrow> A \<in> carrier\<^sub>m m n \<Longrightarrow> A' \<in> carrier\<^sub>m m n"
  unfolding mat_carrier_def by auto

lemma sub1_preserves_diagnal:
  assumes "sub1 k l (r,A) = (r',A')"
  and "l < dim\<^sub>c A"
  and "k + l < dim\<^sub>r A"
  shows "A' $$ (l,l) = A $$ (l,l)"
using assms
proof -
  show "k + l < dim\<^sub>r A \<Longrightarrow> sub1 k l (r,A) = (r',A') \<Longrightarrow>
    A' $$ (l,l) = A $$ (l,l)"
  proof (induction k arbitrary: r' A')
    case (Suc k)
      obtain r'' A'' where rA''[simp]: "sub1 k l (r,A) = (r'',A'')" by force
      have [simp]:"dim\<^sub>r A'' = dim\<^sub>r A" and [simp]:"dim\<^sub>c A'' = dim\<^sub>c A"
        using snd_conv sub1_preserves_dimensions[OF rA''] by auto
      have "A'' $$ (l,l) = A $$ (l,l)" using assms Suc by auto
      have rA': "mute (l + Suc k) l (r'', A'') = (r',A')"
        using Suc by auto
      show ?case using subst mute_preserves[OF rA'] Suc assms by auto
  qed auto
qed

text {* Triangularity is respected by @{const sub1}. *}
lemma sub1_preserves_triangle:
  assumes "sub1 k l (r,A) = (r',A')"
  and tri: "triangular_to l A"
  and lr: "l < dim\<^sub>r A"
  and lc: "l < dim\<^sub>c A"
  and lkr: "l + k < dim\<^sub>r A"
  shows "triangular_to l A'"
using assms
proof -
  show "sub1 k l (r,A) = (r',A') \<Longrightarrow> l + k < dim\<^sub>r A \<Longrightarrow>
    triangular_to l A'"
  proof (induction k arbitrary: r' A')
  case (Suc k)
    then have "sub1 (Suc k) l (r,A) = (r',A')" by auto
    moreover obtain r'' A''
      where rA'': "sub1 k l (r, A) = (r'',A'')" by force
    ultimately
      have rA': "mute (Suc (l + k)) l (r'',A'') = (r',A')" by auto
    have "triangular_to l A''" using rA'' Suc by auto
    thus ?case
      using Suc assms mute_preserves_triangle[OF rA'] rA'' by auto
  qed (insert assms,auto)
qed auto

lemma sub1_makes_0s:
  assumes "sub1 k l (r,A) = (r',A')"
  and lr: "l < dim\<^sub>r A"
  and lc: "l < dim\<^sub>c A"
  and li: "l < i"
  and "i \<le> k + l"
  and "k + l < dim\<^sub>r A"
  shows "A' $$ (i,l) = 0"
using assms
proof -
  show "sub1 k l (r,A) = (r',A') \<Longrightarrow> i \<le> k + l \<Longrightarrow> k + l < dim\<^sub>r A \<Longrightarrow>
    A' $$ (i,l) = 0"
  using lr lc li
  proof (induction k arbitrary: r' A')
  case (Suc k)
    obtain r' A' where rA': "sub1 k l (r, A) = (r',A')" by force
    fix r'' A''
    assume "sub1 (Suc k) l (r, A) = (r'',A'')"
    then have rA'': "mute (Suc (l + k)) l (r', A') = (r'', A'')"
      using rA' by simp
    have ir: "i < dim\<^sub>r A" using Suc by auto
    have il: "i \<noteq> l" using li by auto
    have lr': "l < dim\<^sub>r A'" using lr rA' by auto
    have lc': "l < dim\<^sub>c A'" using lc rA' by auto
    have Slkr': "Suc (l+k) < dim\<^sub>r A'" using Suc rA' by auto
    show "A'' $$ (i,l) = 0"
    proof (cases "Suc(l + k) = i")
      case True {
        have l: "Suc (l + k) \<noteq> l" by auto
        show ?thesis
          using mute_makes_0[OF rA'' lr' lc' Slkr' l] ir il rA'
          by (simp add:True)
      } next
      case False {
        then have ikl: "i \<le> k+l" using Suc by auto
        have ir': "i < dim\<^sub>r A'" using ir rA' by auto
        have lc': "l < dim\<^sub>c A'" using lc rA' by auto
        have IH: "A' $$ (i,l) = 0" using rA' Suc False by auto
        thus ?thesis using mute_preserves[OF rA'' ir' lc'] rA' False Suc
          by simp
      }
    qed
  qed auto
qed auto

lemma sub1_triangulizes_column:
  assumes rA': "sub1 (dim\<^sub>r A - Suc l) l (r,A) = (r',A')"
  and tri:"triangular_to l A"
  and r: "dim\<^sub>r A > 0"
  and lr: "l < dim\<^sub>r A"
  and lc: "l < dim\<^sub>c A"
  shows "triangular_column l A'"
proof (intro triangular_columnI)
  fix i
  assume li: "l < i"
  assume ir: "i < dim\<^sub>r A'"
    also have "... = dim\<^sub>r A" using sub1_preserves_dimensions[OF rA'] by auto
    also have "... = dim\<^sub>r A - l + l" using lr li by auto
    finally have ir2: "i \<le> dim\<^sub>r A - l + l" by auto
  show "A' $$ (i,l) = 0"
    apply (subst sub1_makes_0s[OF rA' lr lc])
    using li ir assms
    by auto
qed

text {*
  The algorithm @{const sub1} increases the number of columns that form triangle.
*}
lemma sub1_grows_triangle:
  assumes rA': "sub1 (dim\<^sub>r A - Suc l) l (r,A) = (r',A')"
  and r: "dim\<^sub>r A > 0"
  and tri:"triangular_to l A"
  and lr: "l < dim\<^sub>r A"
  and lc: "l < dim\<^sub>c A"
  shows "triangular_to (Suc l) A'"
proof -
  have "triangular_to l A'"
    using sub1_preserves_triangle[OF rA'] assms by auto
  moreover have "triangular_column l A'"
    using sub1_triangulizes_column[OF rA'] assms by auto
  ultimately show ?thesis by (rule triangle_growth)
qed

subsection {* Finding Non-Zero Elements *}

private fun find_non0_sub :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::zero mat \<Rightarrow> nat option"
where "find_non0_sub d 0 l A = None"
 | " find_non0_sub d (Suc k) l A =
     (if A $$ (d - Suc k,l) \<noteq> 0
      then Some (d - Suc k)
      else find_non0_sub d k l A)"

private definition find_non0 :: "nat \<Rightarrow> 'a::zero mat \<Rightarrow> nat option"
where "find_non0 l A = find_non0_sub (dim\<^sub>r A) (dim\<^sub>r A - Suc l) l A"

lemma finds_non0_sub :
  "find_non0_sub d k l A = Some i \<Longrightarrow> A $$ (i,l) \<noteq> 0"
proof (induction k arbitrary: i)
  case (Suc k)
    show "A $$ (i,l) \<noteq> 0"
    proof (cases "A $$ (d - Suc k,l) \<noteq> 0")
      case True
        then have "find_non0_sub d (Suc k) l A = Some (d-Suc k)" by auto
        hence "i = d - Suc k" using Suc by auto
        thus ?thesis using True by auto
        next
      case False
        then show ?thesis using Suc by auto
    qed
qed auto

lemma finds_non0:
  "find_non0 l A = Some m \<Longrightarrow> A $$ (m,l) \<noteq> 0"
  unfolding find_non0_def by (subst finds_non0_sub, auto)

lemma find_non0_sub_ordered:
  shows "find_non0_sub d k l A = Some m \<Longrightarrow> l + k < d \<Longrightarrow> l < m \<and> m < d"
proof (induction k arbitrary: m)
  case (Suc k) then show ?case
    using assms by (cases "A $$ (d - Suc k, l) \<noteq> 0", auto)
qed auto

lemma find_non0_ordered:
  "find_non0 l A = Some m \<Longrightarrow> l < dim\<^sub>r A \<Longrightarrow> l < m \<and> m < dim\<^sub>r A"
  unfolding find_non0_def
proof -
  assume m: "find_non0_sub (dim\<^sub>r A) (dim\<^sub>r A - Suc l) l A = Some m"
  assume "l < dim\<^sub>r A"
  then show ?thesis using find_non0_sub_ordered[OF m] by auto
qed

lemma finds_all0_sub:
  assumes "find_non0_sub d k l A = None"
  and "d - Suc k < i"
  and id: "i < d"
  shows "A $$ (i,l) = 0"
  using assms
proof -
  show "find_non0_sub d k l A = None \<Longrightarrow> d - Suc k < i \<Longrightarrow> A $$ (i,l) = 0"
  proof (induction k)
    case 0 then show ?thesis using id by simp next
    case (Suc k) {
      let ?ret = "find_non0_sub d (Suc k) l A"
      have none: "?ret = None" using Suc by auto
      have now0: "A $$ (d - Suc k,l) = 0"
      proof (rule ccontr)
        assume "A $$ (d - Suc k,l) \<noteq> 0"
        then have "?ret = Some (d - Suc k)" by simp
        thus False using none by auto
      qed
      show "A $$ (i,l) = 0"
      proof (cases "i = d - Suc k")
        case True
          then show ?thesis using now0 by auto
          next
        case False
          then have "?ret = find_non0_sub d k l A" using now0 by simp
          hence "find_non0_sub d k l A = None" using Suc by auto
          moreover have "d - Suc k < i" using id Suc False by auto
          ultimately show ?thesis using Suc by auto
      qed
    }
  qed
qed

text {*
  If @{term "find_non0 l A"} fails,
  then $A$ is already triangular to $l$-th column.
*}

lemma finds_all0:
  "find_non0 l A = None \<Longrightarrow> triangular_column l A"
  unfolding find_non0_def
  by (intro triangular_columnI, elim finds_all0_sub, auto)

subsection {* Determinant Preserving Growth of Triangle *}

text {*
  The algorithm @{const sub1} does not preserve determinants when it hits
  a $0$-valued diagonal element. To avoid this case, we introduce the following
  operation:
*}

private fun sub2 :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat"
  where "sub2 d l (r,A) = (
    case find_non0 l A of None \<Rightarrow> (r,A)
    | Some m \<Rightarrow> sub1 (d - Suc l) l (-r, swaprows m l A))"

lemma sub2_preserves_dimensions[simp]:
  assumes rA': "sub2 d l (r,A) = (r',A')"
  shows "dim\<^sub>r A' = dim\<^sub>r A \<and> dim\<^sub>c A' = dim\<^sub>c A"
proof (cases "find_non0 l A")
  case None then show ?thesis using rA' by auto next
  case (Some m) then show ?thesis using rA' by (cases "m = l", auto)
qed

lemma sub2_closed [simp]:
  "sub2 d l (r,A) = (r',A') \<Longrightarrow> A \<in> carrier\<^sub>m m n \<Longrightarrow> A' \<in> carrier\<^sub>m m n"
  unfolding mat_carrier_def by auto


lemma sub2_preserves_triangle:
  assumes rA': "sub2 d l (r,A) = (r',A')"
  and tri: "triangular_to l A"
  and lc: "l < dim\<^sub>c A"
  and ld: "l < d"
  and dr: "d \<le> dim\<^sub>r A"
  shows "triangular_to l A'"
proof -
  have lr: "l < dim\<^sub>r A" using ld dr by auto
  show ?thesis
  proof (cases "find_non0 l A")
    case None then show ?thesis using rA' tri by simp next
    case (Some m) {
      have lm : "l < m" and mr : "m < dim\<^sub>r A"
        using find_non0_ordered[OF Some lr] by auto
      let ?A1 = "swaprows m l A"
  
      have tri'': "triangular_to l ?A1"
      proof (intro triangular_toI)
        fix i j
        assume jl:"j < l" and ji:"j < i" and ir1: "i < dim\<^sub>r ?A1"
        have jm: "j < m" using jl lm by auto
        have ir: "i < dim\<^sub>r A" using ir1 by auto
        have jc: "j < dim\<^sub>c A" using jl lc by auto
        show "?A1 $$ (i, j) = 0"
        proof (cases "m=i")
          case True {
            then have li: "l \<noteq> i" using lm by auto
            hence "?A1 $$ (i,j) = A $$ (l,j)" using ir jc \<open>m=i\<close> by auto
            also have "... = 0" using tri jl lr by auto
            finally show ?thesis.
           }  next
          case False show ?thesis
            proof (cases "l=i")
              case True {
                then have "?A1 $$ (i,j) = A $$ (m,j)"
                  using ir jc \<open>m\<noteq>i\<close> by auto
                thus "?A1 $$ (i,j) = 0" using tri jl jm mr by auto
              } next
              case False {
                then have "?A1 $$ (i,j) = A $$ (i,j)"
                  using ir jc \<open>m\<noteq>i\<close> by auto
                thus "?A1 $$ (i,j) = 0" using tri jl ji ir by auto
              }
           qed
        qed
      qed
  
      let ?rA3 = "sub1 (d - Suc l) l (-r,?A1)"
      have [simp]: "dim\<^sub>r ?A1 = dim\<^sub>r A \<and> dim\<^sub>c ?A1 = dim\<^sub>c A" by auto
      have rA'2: "?rA3 = (r',A')" using rA' Some by simp
      have "l + (d - Suc l) < dim\<^sub>r A" using ld dr by auto
      thus ?thesis
        using sub1_preserves_triangle[OF rA'2 tri''] lr lc rA' by auto
    }
  qed
qed

lemma sub2_grows_triangle:
  assumes rA': "sub2 (dim\<^sub>r A) l (r,A) = (r',A')"
  and tri: "triangular_to l A"
  and lc: "l < dim\<^sub>c A"
  and lr: "l < dim\<^sub>r A"
  shows "triangular_to (Suc l) A'"
proof (rule triangle_growth)
  show "triangular_to l A'"
    using sub2_preserves_triangle[OF rA' tri lc lr] by auto
    next
  have r0: "0 < dim\<^sub>r A" using lr by auto
  show "triangular_column l A'"
    proof (cases "find_non0 l A")
      case None {
        then have "A' = A" using rA' by simp
        moreover have "triangular_column l A"  using finds_all0[OF None].
        ultimately show ?thesis by auto
      } next
      case (Some m) {
        have lm: "l < m" and mr: "m < dim\<^sub>r A"
          using find_non0_ordered[OF Some lr] by auto
        let ?A = "swaprows m l A"
        have tri2: "triangular_to l ?A"
          proof
            fix i j assume jl: "j < l" and ji:"j < i" and ir: "i < dim\<^sub>r ?A"
            show "?A $$ (i,j) = 0"
            proof (cases "i = m")
              case True {
                then have "?A $$ (i,j) = A $$ (l,j)"
                  using jl lc ir by simp
                also have "... = 0"
                  using triangular_toD[OF tri jl jl] lr by auto
                finally show ?thesis by auto
              } next
              case False show ?thesis
                proof (cases "i = l")
                  case True {
                    then have "?A $$ (i,j) = A $$ (m,j)"
                      using jl lc ir by auto
                    also have "... = 0"
                      using triangular_toD[OF tri jl] jl lm mr by auto
                    finally show ?thesis by auto
                  } next
                  case False {
                    then have "?A $$ (i,j) = A $$ (i,j)"
                      using \<open>i \<noteq> m\<close> jl lc ir by auto
                    thus ?thesis using tri jl ji ir by auto
                  }
                qed
            qed
          qed
        have rA'2: "sub1 (dim\<^sub>r ?A - Suc l) l (-r, ?A) = (r',A')"
          using lm Some rA' by simp
        show ?thesis
          using sub1_triangulizes_column[OF rA'2 tri2] r0 lr lc by auto
      }
    qed
qed

subsection {* Recursive Triangulization of Columns *}

text {*
  Now we recursively apply @{const sub2} to make the entire matrix to be triangular.
*}

private fun sub3 :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat"
  where "sub3 d 0 rA = rA"
  | "sub3 d (Suc l) rA = sub2 d l (sub3 d l rA)"

lemma sub3_preserves_dimensions[simp]:
  "sub3 d l (r,A) = (r',A') \<Longrightarrow> dim\<^sub>r A' = dim\<^sub>r A"
  "sub3 d l (r,A) = (r',A') \<Longrightarrow> dim\<^sub>c A' = dim\<^sub>c A"
proof (induction l arbitrary: r' A')
  case (Suc l)
    obtain r' A' where rA': "sub3 d l (r, A) = (r', A')" by force
    fix r'' A'' assume rA'': "sub3 d (Suc l) (r, A) = (r'', A'')" 
    then show "dim\<^sub>r A'' = dim\<^sub>r A" "dim\<^sub>c A'' = dim\<^sub>c A"
    using Suc rA' by auto
qed auto

lemma sub3_closed[simp]:
  "sub3 k l (r,A) = (r',A') \<Longrightarrow> A \<in> carrier\<^sub>m m n \<Longrightarrow> A' \<in> carrier\<^sub>m m n"
  unfolding mat_carrier_def by auto

lemma sub3_makes_triangle:
  assumes "sub3 (dim\<^sub>r A) l (r,A) = (r',A')"
  and "l \<le> dim\<^sub>r A"
  and "l \<le> dim\<^sub>c A"
  shows "triangular_to l A'"
  using assms
proof -
  show "sub3 (dim\<^sub>r A) l (r,A) = (r',A') \<Longrightarrow> l \<le> dim\<^sub>r A \<Longrightarrow> l \<le> dim\<^sub>c A \<Longrightarrow>
    triangular_to l A'"
  proof (induction l arbitrary:r' A')
    case (Suc l)
      then have Slr: "Suc l \<le> dim\<^sub>r A" and Slc: "Suc l \<le> dim\<^sub>c A" by auto
      hence lr: "l < dim\<^sub>r A" and lc: "l < dim\<^sub>c A" by auto
      moreover obtain r'' A''
        where rA'': "sub3 (dim\<^sub>r A) l (r,A) = (r'',A'')" by force
      ultimately have IH: "triangular_to l A''" using Suc by auto
      have [simp]:"dim\<^sub>r A'' = dim\<^sub>r A" and [simp]:"dim\<^sub>c A'' = dim\<^sub>c A"
        using Slr Slc rA'' by auto
      fix r' A'
      assume "sub3 (dim\<^sub>r A) (Suc l) (r, A) = (r', A')"
      then have rA': "sub2 (dim\<^sub>r A'') l (r'',A'') = (r',A')"
        using rA'' by auto
      show "triangular_to (Suc l) A'"
        using sub2_grows_triangle[OF rA'] lr lc rA'' IH by auto
  qed auto
qed auto

subsection {* Triangulization *}

definition triangulize :: "'a::comm_ring_1 mat \<Rightarrow> 'a \<times> 'a mat"
where "triangulize A = sub3 (dim\<^sub>r A) (dim\<^sub>r A) (1,A)"

lemma triangulize_preserves_dimensions[simp]:
  "triangulize A = (r',A') \<Longrightarrow> dim\<^sub>r A' = dim\<^sub>r A"
  "triangulize A = (r',A') \<Longrightarrow> dim\<^sub>c A' = dim\<^sub>c A"
  unfolding triangulize_def by auto

lemma triangulize_closed[simp]:
  "triangulize A = (r',A') \<Longrightarrow> A \<in> carrier\<^sub>m m n \<Longrightarrow> A' \<in> carrier\<^sub>m m n"
  unfolding mat_carrier_def by auto


theorem triangulized:
  assumes "A \<in> carrier\<^sub>m n n"
  and "triangulize A = (r',A')"
  shows "upper_triangular A'"
proof (cases "0<n")
  case True
    have rA': "sub3 (dim\<^sub>r A) (dim\<^sub>r A) (1,A) = (r',A')"
      using assms unfolding triangulize_def by auto
    have nr:"n = dim\<^sub>r A" and nc:"n = dim\<^sub>c A" and nr':"n = dim\<^sub>r A'"
    using assms by auto
    thus ?thesis
      unfolding triangular_to_triangular
      using sub3_makes_triangle[OF rA'] True by auto
    next
  case False
    then have nr':"dim\<^sub>r A' = 0" using assms by auto
    thus ?thesis unfolding upper_triangular_def by auto
qed

subsection{* Divisor will not be 0 *}

text {*
  Here we show that each sub-algorithm will not make $r$
  of the input/output pair $(r,A)$ to 0.
  The algorithm @{term "sub1 k l (r,A)"} requires $A_{l,l} \neq 0$.
*}

lemma sub1_divisor [simp]:
  assumes rA': "sub1 k l (r, (A ::'a :: ring_div mat)) = (r',A')"
  and r0: "r \<noteq> 0"
  and All: "A $$ (l,l) \<noteq> 0"
  and "k + l < dim\<^sub>r A "
  and lc: "l < dim\<^sub>c A"
  shows "r' \<noteq> 0"
using assms
proof -
  show "sub1 k l (r,A) = (r',A') \<Longrightarrow> k + l < dim\<^sub>r A \<Longrightarrow> r' \<noteq> 0"
  proof (induction k arbitrary: r' A')
    case (Suc k)
      obtain r'' A'' where rA'': "sub1 k l (r, A) = (r'', A'')" by force
      then have IH: "r'' \<noteq> 0" using Suc by auto
      have "A'' $$ (l,l) \<noteq> 0"
        using sub1_preserves_diagnal[OF rA'' lc] All Suc by auto
      moreover assume "sub1 (Suc k) l (r,A) = (r',A')"
        then have "mute (Suc (l + k)) l (r'',A'') = (r',A')"
          using rA'' by auto
        hence "r'' * A'' $$ (l, l) = r'"
          unfolding mute_code Let_def using IH by auto
      ultimately show "r' \<noteq> 0" using IH by auto
  qed (insert r0, simp)
qed

text {* The algorithm @{term "sub2"} will not require such a condition. *}
lemma sub2_divisor [simp]:
  assumes rA': "sub2 k l (r, (A ::'a :: ring_div mat)) = (r',A')"
  and lk: "l < k"
  and kr: "k \<le> dim\<^sub>r A"
  and lc: "l < dim\<^sub>c A"
  and r0: "r \<noteq> 0"
  shows "r' \<noteq> 0"
using assms
proof (cases "find_non0 l A") {
  case (Some m)
    then have Aml0: "A $$ (m,l) \<noteq> 0" using finds_non0 by auto
    have md: "m < dim\<^sub>r A" using find_non0_ordered[OF Some] lk kr by auto
    let ?A'' = "swaprows m l A"
    have rA'2: "sub1 (k - Suc l) l (-r, ?A'') = (r',A')"
      using rA' Some by simp
    have All0: "?A'' $$ (l,l) \<noteq> 0" using Aml0 md lk kr lc by auto
    show ?thesis using sub1_divisor[OF rA'2 _ All0] r0 lk kr lc by simp
} qed auto

lemma sub3_divisor [simp]:
  assumes "sub3 d l (r,(A ::'a :: ring_div mat)) = (r'',A'')"
  and "l \<le> d"
  and "d \<le> dim\<^sub>r A"
  and "l \<le> dim\<^sub>c A"
  and r0: "r \<noteq> 0"
  shows "r'' \<noteq> 0"
  using assms
proof -
  show
    "sub3 d l (r,A) = (r'',A'') \<Longrightarrow>
     l \<le> d \<Longrightarrow> d \<le> dim\<^sub>r A \<Longrightarrow> l \<le> dim\<^sub>c A \<Longrightarrow> ?thesis"
  proof (induction l arbitrary: r'' A'')
    case 0
      then show ?case using r0 by simp
      next
    case (Suc l)
      obtain r' A' where rA': "sub3 d l (r,A) = (r',A')" by force
      then have [simp]:"dim\<^sub>r A' = dim\<^sub>r A" and [simp]:"dim\<^sub>c A' = dim\<^sub>c A"
        by auto
      from rA' have "r' \<noteq> 0" using Suc r0 by auto
      moreover have "sub2 d l (r',A') = (r'',A'')"
        using rA' Suc by simp
      ultimately show ?case using sub2_divisor using Suc by simp
  qed
qed

theorem triangulize_divisor:
  assumes A: "(A :: 'a :: ring_div mat) \<in> carrier\<^sub>m d d"
  shows "triangulize A = (r',A') \<Longrightarrow> r' \<noteq> 0"
unfolding triangulize_def
proof -
  assume rA': "sub3 (dim\<^sub>r A) (dim\<^sub>r A) (1, A) = (r', A')"
  show ?thesis using sub3_divisor[OF rA'] A by auto 
qed

subsection {* Determinant Preservation Results *}

text {*
  For each sub-algorithm $f$,
  we show $f(r,A) = (r',A')$ implies @{term "r * det A' = r' * det A"}.
*}

lemma mute_det:
  assumes "A \<in> carrier\<^sub>m n n"
  and rA': "mute k l (r,A) = (r',A')"
  and "k < n"
  and "l < n"
  and "k \<noteq> l"
  shows "r * det A' = r' * det A"
proof -
  let ?All = "A $$ (l,l)"
  let ?Akl = "- A $$ (k,l)"
  let ?B = "multrow k ?All A"
  let ?C = "addrow ?Akl k l ?B"
  have "r * det A' = r * det ?C"  using assms unfolding mute_def by auto
  also have "det ?C = det ?B" using assms by (auto simp: det_addrow)
  also have "\<dots> = ?All * det A" using assms det_multrow by auto
  also have "r * \<dots> = (r * ?All) * det A" by simp
  also have r: "r * ?All = r'" using assms unfolding mute_def by auto
  finally show ?thesis.
qed

lemma sub1_det:
  assumes A: "(A :: 'a :: ring_div mat) \<in> carrier\<^sub>m n n"
  and "sub1 k l (r,A) = (r'',A'')"
  and r0: "r \<noteq> 0"
  and All0: "A $$ (l,l) \<noteq> 0"
  and "l + k < n"
  shows "r * det A'' = r'' * det A"
  using assms
proof -
  show "sub1 k l (r,A) = (r'',A'') \<Longrightarrow> l + k < n \<Longrightarrow> r * det A'' = r'' * det A"
  proof (induction k arbitrary:A'' r'')
  case (Suc k)
    let ?rA' = "sub1 k l (r,A)"
    obtain r' A' where rA':"?rA' = (r',A')" by force
    have A':"A' \<in> carrier\<^sub>m n n" using sub1_closed[OF rA'] A by auto
    have IH: "r * det A' = r' * det A" using Suc assms rA' by auto
    assume "sub1 (Suc k) l (r,A) = (r'',A'')"
    then have rA'':"mute (Suc (l+k)) l (r',A') = (r'',A'')" using rA' by auto
    hence lem: "r' * det A'' = r'' * det A'"
      using assms Suc A' mute_det[OF A' rA''] by auto
    hence "r * r' * det A'' = r * r'' * det A'" by auto
      also from IH have "... = r'' * r' * det A" by auto
      finally have "r * r' * det A'' div r' = r'' * r' * det A div r'" by auto
    moreover have "r' \<noteq> 0"
      using r0 sub1_divisor[OF rA'] All0 Suc A by auto
    ultimately show ?case by auto
  qed auto
qed

lemma sub2_det:
  assumes A: "(A :: 'a :: ring_div mat) \<in> carrier\<^sub>m d d"
  and rA': "sub2 d l (r,A) = (r',A')"
  and r0: "r \<noteq> 0"
  and ld: "l < d"
  shows "r * det A' = r' * det A"
proof (cases "find_non0 l A")
  case None then show ?thesis using assms by auto next
  case (Some m) {
    then have lm: "l < m" and md: "m < d"
      using A find_non0_ordered[OF Some] ld by auto
    hence "m \<noteq> l" by auto
    let ?A'' = "swaprows m l A"
    have rA'2: "sub1 (d - Suc l) l (-r, ?A'') = (r',A')"
      using rA' Some by simp
    have A'': "?A'' \<in> carrier\<^sub>m d d" using A by auto
    hence A''ll0: "?A'' $$ (l,l) \<noteq> 0"
      using finds_non0[OF Some] ld by auto
    hence "-r * det A' = r' * det ?A''"
      using sub1_det[OF A'' rA'2] ld A r0 by auto
    also have "r * ... = -r * r' * det A"
      using det_swaprows[OF md ld \<open>m\<noteq>l\<close> A] by auto
    finally have "r * -r * det A' = -r * r' * det A" by auto
    thus ?thesis using r0 by auto
  }
qed

lemma sub3_det:
  assumes A:"(A :: 'a :: ring_div mat) \<in> carrier\<^sub>m d d"
  and "sub3 d l (r,A) = (r'',A'')"
  and r0: "r \<noteq> 0"
  and "l \<le> d"
  shows "r * det A'' = r'' * det A"
  using assms
proof -
  have d: "d = dim\<^sub>r A" using A by auto
  show "sub3 d l (r,A) = (r'',A'') \<Longrightarrow> l \<le> d \<Longrightarrow> r * det A'' = r'' * det A"
  proof (induction l arbitrary: r'' A'')
    case (Suc l)
      let ?rA' = "sub3 d l (r,A)"
      obtain r' A' where rA':"?rA' = (r',A')" by force
      then have rA'': "sub2 d l (r',A') = (r'',A'')"
        using Suc by auto
      have A': "A' \<in> carrier\<^sub>m d d" using A rA' rA'' by auto
      have r'0: "r' \<noteq> 0" using r0 sub3_divisor[OF rA'] A Suc by auto
      have "r' * det A'' = r'' * det A'"
        using Suc r'0 A by(subst sub2_det[OF A' rA''],auto)
      also have "r * ... = r'' * (r * det A')" by auto
      also have "r * det A' = r' * det A" using Suc rA' by auto
      also have "r'' * ... div r' = r'' * r' * det A div r'" by auto
      finally show "r * det A'' = r'' * det A" using r'0 by auto
  qed simp
qed

theorem triangulize_det:
  assumes A: "(A :: 'a :: ring_div mat) \<in> carrier\<^sub>m d d"
  and rA': "triangulize A = (r',A')"
  shows "det A * r' = det A'"
proof -
  have rA'2: "sub3 d d (1,A) = (r',A')"
    using A rA' unfolding triangulize_def by auto
  show ?thesis
  proof (cases "d = 0")
    case True
      then have A': "A' \<in> carrier\<^sub>m 0 0" using A rA'2 by auto
      have rA'3: "(r',A') = (1,A)" using True rA'2 by simp
      thus ?thesis by auto
      next
    case False
      then show ?thesis using sub3_det[OF A rA'2] assms by auto
  qed
qed

subsection {* Determinant Computation *}

fun det_code :: "'a :: ring_div mat \<Rightarrow> 'a" where
  "det_code A = (if dim\<^sub>r A = dim\<^sub>c A then
     case triangulize A of (m,A') \<Rightarrow>
       listprod (mat_diag A') div m
   else 0)"


lemma det_code[code]: "det A = det_code A"
proof (cases "dim\<^sub>r A = dim\<^sub>c A")
  case True
  then have A: "A \<in> carrier\<^sub>m (dim\<^sub>r A) (dim\<^sub>r A)" unfolding mat_carrier_def by auto
  obtain r' A' where rA': "triangulize A = (r',A')" by force
  from triangulize_divisor[OF A] rA' have r'0: "r' \<noteq> 0" by auto
  from triangulize_det[OF A rA'] have det': "det A * r' = det A'" by auto
  from triangulized[OF A, unfolded rA'] have tri': "upper_triangular A'" by simp
  have A': "A' \<in> carrier\<^sub>m (dim\<^sub>r A') (dim\<^sub>r A')"
    using triangulize_closed[OF rA' A] by auto
  from tri' have tr: "triangular_to (dim\<^sub>r A') A'" by auto
  have "det_code A = listprod (mat_diag A') div r'" using rA' True by simp
  also have "listprod (mat_diag A') = det A'"
    unfolding det_upper_triangular[OF tri' A'] ..
  also have "\<dots> = det A * r'" by (simp add: det')
  also have "\<dots> div r' = det A" using r'0 by auto
  finally show ?thesis ..
qed (simp add: det_def)
end

end