(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Newton Interpolation\<close>

text \<open>We proved soundness of Newton interpolation, i.e., a method to interpolate a polynomial $p$
  from a list of points $(x_1,p(x_1)), (x_2, p(x_2)), \ldots$. In experiments it performs
  much faster than Lagrange-interpolation.

  We further proved soundness of Neville-Aitken's polynomial interpolation\<close>
theory Newton_Interpolation
imports 
  Polynomial
  Lagrange_Interpolation
  "../Matrix/Utility"
begin

context
  fixes x :: "nat \<Rightarrow> 'a :: field"
  and f :: "nat \<Rightarrow> 'a"
begin

private definition Xp :: "nat \<Rightarrow> 'a poly" where [code_unfold]: "Xp i = [:-x i, 1:]"

function neville_aitken_main :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "neville_aitken_main i j = (if i < j then 
      (smult (inverse (x j - x i)) (Xp i * neville_aitken_main (i + 1) j -
      Xp j * neville_aitken_main i (j - 1))) 
    else [:f i:])"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (i,j). j - i)", auto)

definition neville_aitken :: "nat \<Rightarrow> 'a poly" where
  "neville_aitken = neville_aitken_main 0"

declare neville_aitken_main.simps[simp del]

lemma neville_aitken_main: assumes dist: "\<And> i j. i < j \<Longrightarrow> j \<le> n \<Longrightarrow> x i \<noteq> x j"
  shows "i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> j \<le> n \<Longrightarrow> poly (neville_aitken_main i j) (x k) = (f k)"
proof (induct i j arbitrary: k rule: neville_aitken_main.induct)
  case (1 i j k)
  note neville_aitken_main.simps[of i j, simp]
  show ?case
  proof (cases "i < j")
    case False
    with 1(3-) have "k = i" by auto
    with False show ?thesis by auto
  next
    case True note ij = this
    from dist[OF True 1(5)] have diff: "x i \<noteq> x j" by auto
    from True have id: "neville_aitken_main i j = 
      (smult (inverse (x j - x i)) (Xp i * neville_aitken_main (i + 1) j - Xp j * neville_aitken_main i (j - 1)))" by simp
    note IH = 1(1-2)[OF True]
    show ?thesis
    proof (cases "k = i")
      case True
      show ?thesis unfolding id True poly_smult using IH(2)[of i] ij 1(3-) diff
        by (simp add: Xp_def field_simps)
    next
      case False note ki = this
      show ?thesis 
      proof (cases "k = j")
        case True
        show ?thesis unfolding id True poly_smult using IH(1)[of j] ij 1(3-) diff
          by (simp add: Xp_def field_simps)
      next
        case False
        with ki show ?thesis unfolding id poly_smult using IH(1-2)[of k] ij 1(3-) diff
          by (simp add: Xp_def field_simps)
      qed
    qed
  qed
qed
end

lemma neville_aitken: assumes "\<And> i j. i < j \<Longrightarrow> j \<le> n \<Longrightarrow> x i \<noteq> x j"
  shows "j \<le> n \<Longrightarrow> poly (neville_aitken x f n) (x j) = (f j)"
  unfolding neville_aitken_def
  by (rule neville_aitken_main[OF assms, of n], auto)

text \<open>For Newton interpolation, we start with an efficient implementation (which in prior examples
  we used as an uncertified oracle). Later on, a more abstract definition of the algorithm
  is described for which soundness is proven, and which is provably equivalent to the efficient
  implementation.

  The implementation is based on divided differences and the Horner schema.\<close>
context
fixes 
  ty :: "'a :: field itself"
  and xs :: "'a list"
  and fs :: "'a list"
begin


private fun combine_rows :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "combine_rows [] fj xj xis = [fj]"
| "combine_rows (xi_j1 # x_j1s) fj xj (xi # xis) = (let 
    x_js = combine_rows x_j1s fj xj xis;
    new = (hd x_js - xi_j1) / (xj - xi)
    in new # x_js)"
    

qualified fun newton_coefficients_main :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "newton_coefficients_main [fj] xjs = [[fj]]"
| "newton_coefficients_main (fj # fjs) (xj # xjs) = (
    let rec = newton_coefficients_main fjs xjs; row = hd rec;
      new_row = combine_rows row fj xj xs
    in new_row # rec)"
| "newton_coefficients_main _ _ = []"

qualified definition newton_coefficients :: "'a list" where
  "newton_coefficients = map hd (newton_coefficients_main (rev fs) (rev xs))"

qualified fun newton_composition :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a poly" where
  "newton_composition [cn] xis = [:cn:]"
| "newton_composition (ci # cs) (xi # xis) = newton_composition cs xis * [:- xi, 1:] + [:ci:]"
| "newton_composition _ _ = 0"

definition newton_poly_impl :: "'a poly" where
  "newton_poly_impl = newton_composition (rev newton_coefficients) xs"

qualified definition "x i = xs ! i"
qualified definition "f i = fs ! i"

private definition "xd i j = x i - x j"

lemma [simp]: "xd i i = 0" "xd i j + xd j k = xd i k" "xd i j + xd k i = xd k j" unfolding xd_def by simp_all

(* divided differences [xi,..,xj]f *)
private function xij_f :: "nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "xij_f i j = (if i < j then (xij_f (i + 1) j - xij_f i (j - 1)) / xd j i else f i)"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (i,j). j - i)", auto)

private definition c :: "nat \<Rightarrow> 'a" where
  "c i = xij_f 0 i"

private definition "X j = [: - x j, 1:]"

private function b :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "b i n = (if i \<ge> n then [:c n:] else b (Suc i) n * X i + [:c i:])"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (i,n). Suc n - i)", auto)

declare b.simps[simp del]

definition newton_poly :: "nat \<Rightarrow> 'a poly" where
  "newton_poly n = b 0 n"

private definition "Xij i j = listprod (map X [i ..< j])"

private definition "N i = Xij 0 i"

lemma Xii_1[simp]: "Xij i i = 1" unfolding Xij_def by simp
lemma smult_1[simp]: "smult d 1 = [:d:]"
  by (simp add: one_poly_def)

private lemma newton_poly_sum: 
  "newton_poly n = listsum (map (\<lambda> i. smult (c i) (N i)) [0 ..< Suc n])"
  unfolding newton_poly_def N_def
proof -
  {
    fix j
    assume "j \<le> n"
    hence "b j n = (\<Sum>i\<leftarrow>[j..<Suc n]. smult (c i) (Xij j i))"
    proof (induct j n rule: b.induct)
      case (1 j n)
      show ?case
      proof (cases "j \<ge> n")
        case True
        with 1(2) have j: "j = n" by auto
        hence "b j n = [:c n:]" unfolding b.simps[of j n] by simp
        thus ?thesis unfolding j by simp
      next
        case False
        hence b: "b j n = b (Suc j) n * X j + [: c j:]" unfolding b.simps[of j n] by simp
        def nn \<equiv> "Suc n"
        from 1(2) have id: "[j..< nn] = j # [Suc j ..< nn]" unfolding nn_def by (simp add: upt_rec)
        from False have "Suc j \<le> n" by auto
        note IH = 1(1)[OF False this]
        have id2: "(\<Sum>x\<leftarrow>[Suc j..< nn]. smult (c x) (Xij (Suc j) x * X j)) =
          (\<Sum>i\<leftarrow>[Suc j..< nn]. smult (c i) (Xij j i))"
        proof (rule arg_cong[of _ _ listsum], rule map_ext, intro impI, goal_cases)
          case (1 i)
          hence "Xij (Suc j) i * X j = Xij j i" by (simp add: Xij_def upt_conv_Cons)
          thus ?case by simp
        qed
        show ?thesis unfolding b IH listsum_mult_const[symmetric]
          unfolding nn_def[symmetric] id
          by (simp add: id2)
      qed
    qed
  }
  from this[of 0] show "b 0 n = (\<Sum>i\<leftarrow>[0..<Suc n]. smult (c i) (Xij 0 i))" by simp
qed

private lemma poly_newton_poly: "poly (newton_poly n) y = listsum (map (\<lambda> i. c i * poly (N i) y) [0 ..< Suc n])"
  unfolding newton_poly_sum poly_listsum map_map o_def by simp

private definition "pprod k i j = (\<Prod>l\<leftarrow>[i..<j]. xd k l)"

private lemma poly_N_xi: "poly (N i) (x j) = pprod j 0 i"
proof -
  have "poly (N i) (x j) = (\<Prod>l\<leftarrow>[0..<i]. xd j l)"
    unfolding N_def Xij_def poly_listprod X_def[abs_def] map_map o_def xd_def by simp
  also have "\<dots> = pprod j 0 i" unfolding pprod_def ..
  finally show ?thesis .
qed

private lemma poly_N_xi_cond: "poly (N i) (x j) = (if j < i then 0 else pprod j 0 i)"
proof -
  show ?thesis
  proof (cases "j < i")
    case False
    thus ?thesis using poly_N_xi by simp
  next
    case True
    hence "j \<in> set [0 ..< i]" by auto
    from split_list[OF this] obtain bef aft where id2: "[0 ..< i] = bef @ j # aft" by auto
    have "(\<Prod>k\<leftarrow>[0..<i]. xd j k) = 0" unfolding id2 by auto
    with True show ?thesis unfolding poly_N_xi pprod_def by auto
  qed
qed

private lemma poly_newton_poly_xj: assumes "j \<le> n"
  shows "poly (newton_poly n) (x j) = listsum (map (\<lambda> i. c i * poly (N i) (x j)) [0 ..< Suc j])"
proof -
  from assms have id: "[0 ..< Suc n] = [0 ..< Suc j] @ [Suc j ..< Suc n]" 
    by (metis Suc_le_mono le_Suc_ex less_eq_nat.simps(1) upt_add_eq_append)
  have id2: "(\<Sum>i\<leftarrow>[Suc j..< Suc n]. c i * poly (N i) (x j)) = 0"
    by (rule listsum_0, unfold poly_N_xi_cond, auto)
  show ?thesis unfolding poly_newton_poly id map_append listsum_append id2 by simp
qed

declare xij_f.simps[simp del]

context
  fixes n
  assumes dist: "\<And> i j. i < j \<Longrightarrow> j \<le> n \<Longrightarrow> x i \<noteq> x j"
begin
private lemma xd_diff: "i < j \<Longrightarrow> j \<le> n \<Longrightarrow> xd i j \<noteq> 0"
   "i < j \<Longrightarrow> j \<le> n \<Longrightarrow> xd j i \<noteq> 0" using dist[of i j] dist[of j i] unfolding xd_def by auto

text \<open>This is the key technical lemma for soundness of Newton interpolation.\<close>

private lemma divided_differences_main: assumes "k \<le> n" "i < k"
  shows "listsum (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i]) = 
  listsum (map (\<lambda> j. xij_f (Suc i) (Suc i + j) * pprod k (Suc i) (Suc i + j)) [0..<Suc k - Suc i])"
proof -
  let ?exp = "\<lambda> i j. xij_f i (i + j) * pprod k i (i + j)"
  def ei \<equiv> "?exp i"
  def esi \<equiv> "?exp (Suc i)"  
  let ?ki = "k - i"
  let ?sumi = "\<lambda> xs. listsum (map ei xs)"
  let ?sumsi = "\<lambda> xs. listsum (map esi xs)"
  let ?mid = "\<lambda> j. xij_f i (k - j) * pprod k (Suc i) (k - j) * xd (k - j) i"
  let ?sum = "\<lambda> j. ?sumi [0 ..< ?ki - j] + ?sumsi [?ki - j ..< ?ki] + ?mid j"
  def fin \<equiv> "?ki - 1"
  have fin: "fin < ?ki" unfolding fin_def using assms by auto
  have id: "[ 0 ..< Suc k - i] = [0 ..< ?ki] @ [?ki]" and 
    id2: "[i..<k] = i # [Suc i ..< k]" and
    id3: "k - (i + (k - Suc i)) = 1" "k - (?ki - 1) = Suc i" using assms 
    by (auto simp: Suc_diff_le upt_conv_Cons)
  have neq: "xd (Suc i) i \<noteq> 0" using xd_diff[of i "Suc i"] assms by auto
  have "listsum (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i])
    = ?sumi [0 ..< Suc k - i]" unfolding ei_def by simp
  also have "\<dots> = ?sumi [0 ..< ?ki] + ?sumsi [?ki ..< ?ki] + ei ?ki" 
    unfolding id by simp
  also have "\<dots> = ?sum 0"
    unfolding ei_def using assms by (simp add: pprod_def id2)
  also have "?sum 0 = ?sum fin" using fin
  proof (induct fin)
    case (Suc fin)
    from Suc(2) assms 
    have fki: "fin < ?ki" and ikf: "i < k - Suc fin" "i < k - fin" and kfn: "k - fin \<le> n" by auto
    from xd_diff[OF ikf(2) kfn] have nz: "xd (k - fin) i \<noteq> 0" by auto
    note IH = Suc(1)[OF fki]
    have id4: "[0 ..< ?ki - fin] = [0 ..< ?ki - Suc fin] @ [?ki - Suc fin]" 
      "i + (k - i - Suc fin) = k - Suc fin" 
      "Suc (k - Suc fin) = k - fin" using Suc(2) assms  \<open>fin < ?ki\<close>
      by (metis Suc_diff_Suc le0 upt_Suc) (insert Suc(2), auto)      
    from Suc(2) assms have id5: "[i..<k - Suc fin] = i # [Suc i ..< k - Suc fin]"
      "[Suc i..<k - fin] = [Suc i..<k - Suc fin] @ [k - Suc fin]"
      by (force simp: upt_rec) (metis Suc_leI id4(3) ikf(1) upt_Suc)
    have "?sum 0 = ?sum fin" by (rule IH)
    also have "\<dots> = ?sumi [0 ..< ?ki - Suc fin] + ?sumsi [?ki - fin ..< ?ki] + 
      (ei (?ki - Suc fin) + ?mid fin)"
      unfolding id4 by simp
    also have "?mid fin = (xij_f (Suc i) (k - fin) - xij_f i (k - Suc fin))
      * pprod k (Suc i) (k - fin)" unfolding xij_f.simps[of i "k - fin"]
      using ikf nz by simp
    also have "\<dots> = xij_f (Suc i) (k - fin) * pprod k (Suc i) (k - fin) -
      xij_f i (k - Suc fin) * pprod k (Suc i) (k - fin)" by algebra
    also have "xij_f (Suc i) (k - fin) * pprod k (Suc i) (k - fin) = esi (?ki - Suc fin)"
      unfolding esi_def using ikf by (simp add: id4)
    also have "ei (?ki - Suc fin) = xij_f i (k - Suc fin) * pprod k i (k - Suc fin)"       
      unfolding ei_def id4 using ikf by (simp add: ac_simps)
    finally have "?sum 0 = ?sumi [0 ..< ?ki - Suc fin] 
      + (esi (?ki - Suc fin) + ?sumsi [?ki - fin ..< ?ki])
      + (xij_f i (k - Suc fin) * (pprod k i (k - Suc fin) - pprod k (Suc i) (k - fin)))"
      by algebra
    also have "esi (?ki - Suc fin) + ?sumsi [?ki - fin ..< ?ki] 
      = ?sumsi ((?ki - Suc fin) # [?ki - fin ..< ?ki])" by simp
    also have "(?ki - Suc fin) # [?ki - fin ..< ?ki] = [?ki - Suc fin ..< ?ki]"
      using Suc(2) by (simp add: Suc_diff_Suc upt_rec)
    also have "pprod k i (k - Suc fin) - pprod k (Suc i) (k - fin) 
      = (xd k i) * pprod k (Suc i) (k - Suc fin) - (xd k (k - Suc fin)) * pprod k (Suc i) (k - Suc fin)"
      unfolding pprod_def id5 by simp
    also have "\<dots> = (xd k i - xd k (k - Suc fin)) * pprod k (Suc i) (k - Suc fin)"
      by algebra
    also have "\<dots> = (xd (k - Suc fin) i) * pprod k (Suc i) (k - Suc fin)" unfolding xd_def by simp
    also have "xij_f i (k - Suc fin) * \<dots> = ?mid (Suc fin)" by simp
    finally show ?case by simp
  qed simp
  also have "\<dots> = (ei 0 + ?mid (k - i - 1)) + ?sumsi [1 ..< k - i]" 
    unfolding fin_def by (simp add: id3)
  also have "ei 0 + ?mid (k - i - 1) = esi 0" unfolding id3
    unfolding ei_def esi_def xij_f.simps[of i i]  using neq assms
    by (simp add: field_simps xij_f.simps pprod_def)
  also have "esi 0 + ?sumsi [1 ..< k - i] = ?sumsi (0 # [1 ..< k - i])" by simp
  also have "0 # [1 ..< k - i] = [0 ..< Suc k - Suc i]" 
    using assms by (simp add: upt_rec)
  also have "?sumsi \<dots> = listsum (map (\<lambda> j. xij_f (Suc i) (Suc i + j) * 
    pprod k (Suc i) (Suc i + j)) [0..<Suc k - Suc i])"
    unfolding esi_def using assms by simp
  finally show ?thesis .
qed

private lemma divided_differences: assumes kn: "k \<le> n" and ik: "i \<le> k"
  shows "listsum (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i]) = f k"
proof -
  {
    fix ii
    assume "i + ii \<le> k"
    hence "listsum (map (\<lambda> j. xij_f i (i + j) * pprod k i (i + j)) [0..<Suc k - i])
      = listsum (map (\<lambda> j. xij_f (i + ii) (i + ii + j) * pprod k (i + ii) (i + ii + j)) [0..<Suc k - (i + ii)])"
    proof (induct ii)
      case (Suc ii)
      hence le1: "i + ii \<le> k" and le2: "i + ii < k" by simp_all
      show ?case unfolding Suc(1)[OF le1] unfolding divided_differences_main[OF kn le2]
        using Suc(2) by simp
    qed simp
  } note main = this
  have ik: "i + (k - i) \<le> k" and id: "i + (k - i) = k" using ik by simp_all
  show ?thesis unfolding main[OF ik] unfolding id
    by (simp add: xij_f.simps pprod_def)
qed      

lemma newton_poly_sound: assumes "k \<le> n"
  shows "poly (newton_poly n) (x k) = f k"
proof -
  have "poly (newton_poly n) (x k) = 
    listsum (map (\<lambda> j. xij_f 0 (0 + j) * pprod k 0 (0 + j)) [0..<Suc k - 0])"
    unfolding poly_newton_poly_xj[OF assms] c_def poly_N_xi by simp
  also have "\<dots> = f k"
    by (rule divided_differences[OF assms], simp)
  finally show ?thesis by simp
qed
end

lemma newton_poly_degree: "degree (newton_poly n) \<le> n" 
proof -
  {
    fix i
    have "i \<le> n \<Longrightarrow> degree (b i n) \<le> n - i"
    proof (induct i n rule: b.induct)
      case (1 i n)
      note b = b.simps[of i n]
      show ?case 
      proof (cases "n \<le> i")
        case True
        thus ?thesis unfolding b by auto
      next
        case False
        have "degree (b i n) = degree (b (Suc i) n * X i + [:c i:])" using False unfolding b by simp
        also have "\<dots> \<le> max (degree (b (Suc i) n * X i)) (degree [:c i:])"
          by (rule degree_add_le_max)
        also have "\<dots> = degree (b (Suc i) n * X i)" by simp
        also have "\<dots> \<le> degree (b (Suc i) n) + degree (X i)"
          by (rule degree_mult_le)
        also have "\<dots> \<le> n - Suc i + degree (X i)" 
          using 1(1)[OF False] 1(2) False add_le_mono1 not_less_eq_eq by blast
        also have "\<dots> = n - Suc i + 1" unfolding X_def by simp
        also have "\<dots> = n - i" using 1(2) False by auto
        finally show ?thesis .
      qed
    qed
  }
  from this[of 0] show ?thesis unfolding newton_poly_def by simp
qed

context
  fixes n
  assumes xs: "length xs = n"
    and fs: "length fs = n"
begin
lemma newton_coefficients_main: 
  "k < n \<Longrightarrow> newton_coefficients_main (rev (map f [0..<Suc k])) (rev (map x [0..<Suc k]))
    = rev (map (\<lambda> i. map (\<lambda> j. xij_f j i) [0..<Suc i]) [0..<Suc k])"
proof (induct k)
  case 0
  show ?case
    by (simp add: xij_f.simps)
next
  case (Suc k)
  hence "k < n" by auto
  note IH = Suc(1)[OF this]
  have id: "\<And> f. rev (map f [0..<Suc (Suc k)]) = f (Suc k) # f k # rev (map f [0..< k])" 
    and id2: "\<And> f. f k # rev (map f [0..<k]) = rev (map f [0..< Suc k])" by simp_all
  show ?case unfolding id newton_coefficients_main.simps Let_def
    unfolding id2 IH
    unfolding list.simps id2[symmetric]
  proof (rule conjI, goal_cases)
    case 1
    have xs: "xs = map x [0 ..< n]" using xs unfolding x_def[abs_def] 
      by (intro nth_equalityI, auto)
    def nn \<equiv> "0 :: nat"
    def m \<equiv> "Suc k - nn"
    have prems: "m = Suc k - nn" "nn < Suc (Suc k)" unfolding m_def nn_def by auto
    have "?case = (combine_rows (map ((\<lambda>j. xij_f j k)) [nn..< Suc k]) (f (Suc k)) (x (Suc k)) (map x [nn ..< n]) =
      map ((\<lambda>j. xij_f j (Suc k))) [nn..<Suc (Suc k)])"
      unfolding nn_def xs[symmetric] by simp
    also have "\<dots>" using prems
    proof (induct m arbitrary: nn)
      case 0
      hence nn: "nn = Suc k" by auto
      show ?case unfolding nn by (simp add: xij_f.simps)
    next
      case (Suc m)
      with \<open>Suc k < n\<close> have "nn < n" and le: "nn < Suc k" by auto
      with Suc(2-) have id: 
        "[nn..<Suc k] = nn # [Suc nn..< Suc k]"
        "[nn..<n] = nn # [Suc nn..< n]"
      and id2: "[nn..<Suc (Suc k)] = nn # [Suc nn..<Suc (Suc k)]"
        "[Suc nn..<Suc (Suc k)] = Suc nn # [Suc (Suc nn)..<Suc (Suc k)]"
        by (auto simp: upt_rec)
      from Suc(2-) have "m = Suc k - Suc nn" "Suc nn < Suc (Suc k)" by auto
      note IH = Suc(1)[OF this]
      show ?case unfolding id list.simps combine_rows.simps IH Let_def
        unfolding id2 list.simps 
        using le
        by (simp add: xij_f.simps[of nn "Suc k"] xd_def)
    qed
    finally show ?case by simp
  qed simp
qed

lemma newton_coefficients: "newton_coefficients = rev (map c [0 ..< n])"
proof (cases n)
  case 0
  hence xs: "xs = []" "fs = []" using xs fs by auto
  show ?thesis unfolding newton_coefficients_def 0 
    using newton_coefficients_main.simps
    unfolding xs by simp
next
  case (Suc nn)
  hence sn: "Suc nn = n" and nn: "nn < n" by auto
  from fs have fs: "map f [0..<Suc nn] = fs" unfolding sn
    by (intro nth_equalityI, auto simp: f_def)
  from xs have xs: "map x [0..<Suc nn] = xs" unfolding sn
    by (intro nth_equalityI, auto simp: x_def)
  show ?thesis
    unfolding newton_coefficients_def
      newton_coefficients_main[OF nn, unfolded fs xs]
    unfolding sn rev_map[symmetric] map_map o_def map_upt_Suc
    by (rule arg_cong[of _ _ rev], intro nth_equalityI, auto simp: c_def)
qed

lemma newton_poly_impl: assumes "n = Suc nn"
  shows "newton_poly_impl = newton_poly nn"
proof -
  def i \<equiv> "0 :: nat"
  have xs: "map x [0..<n] = xs" using xs
    by (intro nth_equalityI, auto simp: x_def)
  have "i \<le> nn" unfolding i_def by simp
  hence "newton_composition (map c [i..<Suc nn]) (map x [i..<Suc nn]) = b i nn"
  proof (induct i nn rule: b.induct)
    case (1 i n)
    show ?case
    proof (cases "n \<le> i")
      case True
      with 1(2) have i: "i = n" by simp
      show ?thesis unfolding i b.simps[of n n] by simp
    next
      case False
      hence "Suc i \<le> n" by simp
      note IH = 1(1)[OF False this]
      have bi: "b i n = b (Suc i) n * X i + [:c i:]" using False by (simp add: b.simps)    
      from False have id: "[i ..< Suc n] = i # [Suc i ..< Suc n]" by (simp add: upt_rec)
      from False have id2: "[Suc i ..< Suc n] = Suc i # [Suc (Suc i) ..< Suc n]" by (simp add: upt_rec)
      show ?thesis unfolding id bi list.simps newton_composition.simps id2
        unfolding IH[unfolded id2 list.simps] by (simp add: X_def)
    qed
  qed
  thus ?thesis
    unfolding newton_poly_impl_def newton_coefficients rev_rev_ident newton_poly_def i_def
      assms[symmetric] xs .
qed
end
end

definition newton_interpolation_poly :: "('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "newton_interpolation_poly x_fs = (let 
    xs = map fst x_fs; fs = map snd x_fs in
    newton_poly_impl xs fs)"

lemma newton_interpolation_poly: assumes dist: "distinct (map fst xs_ys)"
  and p: "p = newton_interpolation_poly xs_ys"
  and xy: "(x,y) \<in> set xs_ys"
  shows "poly p x = y"
proof (cases "length xs_ys")
  case 0
  thus ?thesis using xy by (cases xs_ys, auto)
next
  case (Suc nn)
  let ?xs = "map fst xs_ys" let ?fs = "map snd xs_ys" let ?n = "Suc nn"
  from xy[unfolded set_conv_nth] obtain i where xy: "i \<le> nn" "x = ?xs ! i" "y = ?fs ! i"
    using Suc
    by (metis (no_types, lifting) fst_conv in_set_conv_nth less_Suc_eq_le nth_map snd_conv xy)
  have id: "newton_interpolation_poly xs_ys = newton_poly ?xs ?fs nn"
    unfolding newton_interpolation_poly_def Let_def
    by (rule newton_poly_impl[OF _ _ Suc], auto)
  show ?thesis
    unfolding p id
  proof (rule newton_poly_sound[of nn ?xs _ ?fs, unfolded 
      Newton_Interpolation.x_def Newton_Interpolation.f_def, OF _ xy(1), folded xy(2-)])
    fix i j
    show "i < j \<Longrightarrow> j \<le> nn \<Longrightarrow> ?xs ! i \<noteq> ?xs ! j" using dist Suc nth_eq_iff_index_eq by fastforce
  qed
qed

lemma degree_newton_interpolation_poly:  
  shows "degree (newton_interpolation_poly xs_ys) \<le> length xs_ys - 1"
proof (cases "length xs_ys")
  case 0
  hence id: "xs_ys = []" by (cases xs_ys, auto)
  show ?thesis unfolding 
    id newton_interpolation_poly_def Let_def list.simps newton_poly_impl_def
    Newton_Interpolation.newton_coefficients_def
    by simp
next
  case (Suc nn)
  let ?xs = "map fst xs_ys" let ?fs = "map snd xs_ys" let ?n = "Suc nn"
  have id: "newton_interpolation_poly xs_ys = newton_poly ?xs ?fs nn"
    unfolding newton_interpolation_poly_def Let_def
    by (rule newton_poly_impl[OF _ _ Suc], auto)
  show ?thesis unfolding id using newton_poly_degree[of ?xs ?fs nn] Suc by simp
qed

hide_const 
  Newton_Interpolation.x
  Newton_Interpolation.f

end