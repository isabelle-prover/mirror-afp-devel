(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Matrix Kernel\<close>

text \<open>We define the kernel of a matrix $A$ and prove the following properties.

\begin{itemize}
\item The kernel stays invariant when multiplying $A$ with an invertible matrix from the left.
\item The dimension of the kernel stays invariant when 
  multiplying $A$ with an invertible matrix from the right.
\item The function find-base-vectors returns a basis of the kernel if $A$ is in row-echelon form.
\item The dimension of the kernel of a block-diagonal matrix is the sum of the dimensions of
  the kernels of the blocks.
\item There is an executable algorithm which computes the dimension of the kernel of a matrix
  (which just invokes Gauss-Jordan and then counts the number of pivot elements).
\end{itemize}
\<close>

theory Matrix_Kernel
imports 
  VS_Connect
  Missing_VectorSpace
  Determinant
begin

definition mat_kernel :: "'a :: comm_ring_1 mat \<Rightarrow> 'a vec set" where
  "mat_kernel A = { v . v \<in> carrier\<^sub>v (dim\<^sub>c A) \<and> A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v (dim\<^sub>r A)}"

lemma mat_kernelI: assumes "A \<in> carrier\<^sub>m nr nc" "v \<in> carrier\<^sub>v nc" "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr"
  shows "v \<in> mat_kernel A"
  using assms unfolding mat_kernel_def by auto

lemma mat_kernelD: assumes "A \<in> carrier\<^sub>m nr nc" "v \<in> mat_kernel A"
  shows "v \<in> carrier\<^sub>v nc" "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr"
  using assms unfolding mat_kernel_def by auto

lemma mat_kernel: assumes "A \<in> carrier\<^sub>m nr nc" 
  shows "mat_kernel A = {v. v \<in> carrier\<^sub>v nc \<and> A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr}"
  unfolding mat_kernel_def using assms by auto

lemma mat_kernel_carrier:
  assumes "A \<in> carrier\<^sub>m nr nc" shows "mat_kernel A \<subseteq> carrier\<^sub>v nc"
  using assms mat_kernel by auto

lemma mat_kernel_mult_subset: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and B: "B \<in> carrier\<^sub>m n nr"
  shows "mat_kernel A \<subseteq> mat_kernel (B \<otimes>\<^sub>m A)"
proof -
  from A B have BA: "B \<otimes>\<^sub>m A \<in> carrier\<^sub>m n nc" by auto
  show ?thesis unfolding mat_kernel[OF BA] mat_kernel[OF A] using A B by auto
qed

lemma mat_kernel_smult: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and v: "v \<in> mat_kernel A"
  shows "a \<odot>\<^sub>v v \<in>  mat_kernel A"
proof -
  from mat_kernelD[OF A v] have v: "v \<in> carrier\<^sub>v nc"
    and z: "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr" by auto
  from arg_cong[OF z, of "\<lambda> v. a \<odot>\<^sub>v v"] v 
  have "a \<odot>\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v) = \<zero>\<^sub>v nr" by auto
  also have "a \<odot>\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v) = A \<otimes>\<^sub>m\<^sub>v (a \<odot>\<^sub>v v)" using A v by auto
  finally show ?thesis using v A
    by (intro mat_kernelI, auto)
qed

lemma mat_kernel_mult_eq: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and B: "B \<in> carrier\<^sub>m nr nr"
  and C: "C \<in> carrier\<^sub>m nr nr"
  and inv: "C \<otimes>\<^sub>m B = \<one>\<^sub>m nr"
  shows "mat_kernel (B \<otimes>\<^sub>m A) = mat_kernel A"
proof 
  from B A have BA: "B \<otimes>\<^sub>m A \<in> carrier\<^sub>m nr nc" by auto
  show "mat_kernel A \<subseteq> mat_kernel (B \<otimes>\<^sub>m A)" by (rule mat_kernel_mult_subset[OF A B])
  {
    fix v
    assume v: "v \<in> mat_kernel (B \<otimes>\<^sub>m A)"
    from mat_kernelD[OF BA this] have v: "v \<in> carrier\<^sub>v nc" and z: "B \<otimes>\<^sub>m A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr" by auto
    from arg_cong[OF z, of "\<lambda> v. C \<otimes>\<^sub>m\<^sub>v v"] 
    have "C \<otimes>\<^sub>m\<^sub>v (B \<otimes>\<^sub>m A \<otimes>\<^sub>m\<^sub>v v) = \<zero>\<^sub>v nr" using C v by auto
    also have "C \<otimes>\<^sub>m\<^sub>v (B \<otimes>\<^sub>m A \<otimes>\<^sub>m\<^sub>v v) = ((C \<otimes>\<^sub>m B) \<otimes>\<^sub>m A) \<otimes>\<^sub>m\<^sub>v v" 
      unfolding mat_vec_mult_assoc[symmetric, OF C BA v]    
      unfolding mat_mult_assoc[OF C B A] by simp
    also have "\<dots> = A \<otimes>\<^sub>m\<^sub>v v" unfolding inv using A v by auto
    finally have "v \<in> mat_kernel A"
      by (intro mat_kernelI[OF A v])
  }
  thus "mat_kernel (B \<otimes>\<^sub>m A) \<subseteq> mat_kernel A" by auto
qed

locale kernel = 
  fixes nr :: nat
    and nc :: nat
    and A :: "'a :: field mat"
  assumes A: "A \<in> carrier\<^sub>m nr nc"
begin
sublocale NC: vec_space "TYPE('a)" nc .

abbreviation F where "F \<equiv> class_field TYPE('a)"
abbreviation V where "V \<equiv> module\<^sub>v TYPE('a) nc"

abbreviation "VK \<equiv> V\<lparr>carrier := mat_kernel A\<rparr>"

sublocale VKMod: module F VK
  rewrites "carrier VK = mat_kernel A"
  by (rule NC.submodule_is_module, unfold_locales,
    insert A mat_mult_vec_right_distrib[OF A] mat_mult_vec[OF A] mat_kernel[OF A], auto)

sublocale Ker: vectorspace F VK 
  rewrites "carrier VK = mat_kernel A" 
  by (unfold_locales, auto)

abbreviation dim where "dim \<equiv> Ker.dim"
abbreviation basis where "basis \<equiv> Ker.basis"
abbreviation gen_set where "gen_set \<equiv> VKMod.gen_set"

lemma finsum_same:
  assumes "f : S \<rightarrow> mat_kernel A"
  shows "finsum VK f S = finsum NC.V f S"
  using assms
proof (induct S rule: infinite_finite_induct)
  case (insert s S)
    hence base: "finite S" "s \<notin> S"
      and f_VK: "f : S \<rightarrow> mat_kernel A" "f s : mat_kernel A" by auto
    hence f_NC: "f : S \<rightarrow> carrier\<^sub>v nc" "f s : carrier\<^sub>v nc" using mat_kernel[OF A] by auto
    have IH: "finsum VK f S = finsum NC.V f S" using insert f_VK by auto
    thus ?case
      unfolding NC.module.M.finsum_insert[OF base f_NC]
      unfolding VKMod.M.finsum_insert[OF base f_VK]
      by simp
qed auto

lemma lincomb_same:
  assumes S_kernel: "S \<subseteq> mat_kernel A"
  shows "VKMod.lincomb a S = NC.module.lincomb a S"
  unfolding VKMod.lincomb_def
  unfolding NC.module.lincomb_def
  apply(subst finsum_same)
  using S_kernel VKMod.smult_closed[unfolded vec_module_simps class_ring_simps] by auto

lemma span_same:
  assumes S_kernel: "S \<subseteq> mat_kernel A"
  shows "VKMod.span S = NC.module.span S"
proof (rule;rule)
  fix v assume L: "v : VKMod.span S" show "v : NC.module.span S"
  proof -
    obtain a U where know: "finite U" "U \<subseteq> S" "a : U \<rightarrow> UNIV" "v = VKMod.lincomb a U"
      using L unfolding VKMod.span_def by auto
    hence v: "v = NC.module.lincomb a U" using lincomb_same S_kernel by auto
    show ?thesis
      unfolding NC.module.span_def by (rule,intro exI conjI;fact)
  qed
  next fix v assume R: "v : NC.module.span S" show "v : VKMod.span S"
  proof -
    obtain a U where know: "finite U" "U \<subseteq> S" "v = NC.module.lincomb a U"
      using R unfolding NC.module.span_def by auto
    hence v: "v = VKMod.lincomb a U" using lincomb_same S_kernel by auto
    have a: "a : U \<rightarrow> carrier F" by (simp add: vec_module_simps class_ring_simps)
    show ?thesis unfolding VKMod.span_def by (rule, intro exI conjI; fact)
  qed
qed

lemma lindep_same:
  assumes S_kernel: "S \<subseteq> mat_kernel A"
  shows "VKMod.lin_dep S = NC.module.lin_dep S"
proof
  note [simp] = vec_module_simps class_ring_simps
  { assume L: "VKMod.lin_dep S"
    then obtain v a U
    where finU: "finite U" and US: "U \<subseteq> S"
      and lc: "VKMod.lincomb a U = \<zero>\<^sub>v nc"
      and vU: "v \<in> U"
      and av0: "a v \<noteq> 0"
      unfolding VKMod.lin_dep_def by auto
    have lc': "NC.module.lincomb a U = \<zero>\<^sub>v nc"
      using lc lincomb_same US S_kernel by auto
    have aU: "a : U \<rightarrow> UNIV" by auto
    show "NC.module.lin_dep S" unfolding NC.module.lin_dep_def
      by (intro exI conjI,(fact finU US aU lc' vU av0)+)
  }
  assume R: "NC.module.lin_dep S"
  then obtain v a U
  where finU: "finite U" and US: "U \<subseteq> S"
    and lc: "NC.module.lincomb a U = \<zero>\<^sub>v nc"
    and vU: "v : U"
    and av0: "a v \<noteq> zero F"
    unfolding NC.module.lin_dep_def by auto
  have lc': "VKMod.lincomb a U = zero VK"
    using lc lincomb_same US S_kernel by auto
  have aU: "a : U \<rightarrow> carrier F" by auto
  show "VKMod.lin_dep S" unfolding VKMod.lin_dep_def
    by (intro exI conjI,(fact finU US aU lc' vU av0)+)
qed

lemma lincomb_index:
  assumes i: "i < nc"
    and Xk: "X \<subseteq> mat_kernel A"
  shows "VKMod.lincomb a X $ i = setsum (\<lambda>x. a x * x $ i) X"
proof -
  have X: "X \<subseteq> carrier\<^sub>v nc" using Xk mat_kernel_def A by auto
  show ?thesis
    using vec_space.lincomb_index[OF i X]
    using lincomb_same[OF Xk] by auto
qed

end

lemma find_base_vectors: assumes ref: "row_echelon_form A" 
  and A: "A \<in> carrier\<^sub>m nr nc" shows
  "set (find_base_vectors A) \<subseteq> mat_kernel A"
  "\<zero>\<^sub>v nc \<notin> set (find_base_vectors A)"
  "kernel.basis nc A (set (find_base_vectors A))"
  "card (set (find_base_vectors A)) = nc - card { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
  "length (pivot_positions A) = card { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
  "kernel.dim nc A = nc - card { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
proof -
  note non_pivot_base = non_pivot_base[OF ref A]
  let ?B = "set (find_base_vectors A)"
  let ?pp = "set (pivot_positions A)"
  from A have dim: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
  where pivot: "pivot_fun A p nc" using dim by auto
  note piv = pivot_funD[OF dim(1) pivot]
  {
    fix v
    assume "v \<in> ?B"
    from this[unfolded find_base_vectors_def Let_def dim]
      obtain c where c: "c < nc" "c \<notin> snd ` ?pp"
      and res: "v = non_pivot_base A (pivot_positions A) c" by auto
    from non_pivot_base[OF c, folded res] c
    have "v \<in> mat_kernel A" "v \<noteq> \<zero>\<^sub>v nc" 
      by (intro mat_kernelI[OF A], auto)
  }
  thus sub: "?B \<subseteq> mat_kernel A" and
    "\<zero>\<^sub>v nc \<notin> ?B" by auto
  {
    fix j j'
    assume j: "j < nc" "j \<notin> snd ` ?pp" and j': "j' < nc" "j' \<notin> snd ` ?pp" and neq: "j' \<noteq> j"
    from non_pivot_base(2)[OF j] non_pivot_base(4)[OF j' j neq]
    have "non_pivot_base A (pivot_positions A) j \<noteq> non_pivot_base A (pivot_positions A) j'" by auto
  }
  hence inj: "inj_on (non_pivot_base A (pivot_positions A))
     (set [j\<leftarrow>[0..<nc] . j \<notin> snd ` ?pp])" unfolding inj_on_def by auto
    note pp = pivot_positions[OF A pivot]
  have lc: "length (pivot_positions A) = card (snd ` ?pp)"
    using distinct_card[OF pp(3)] by auto
  show card: "card ?B = nc - card { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
    "length (pivot_positions A) = card { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
    unfolding find_base_vectors_def Let_def dim set_map  card_image[OF inj] pp(4)[symmetric]
    unfolding pp(1) lc
  proof -
    have "nc - card (snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})
      = card {0 ..< nc} - card (snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})" by auto
    also have "\<dots> = card ({0 ..< nc} - snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})"
      by (rule card_Diff_subset[symmetric], insert piv(1), force+)
    also have "{0 ..< nc} - snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc} = (set [j\<leftarrow>[0..<nc] . j \<notin> snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc}])"
      by auto
    finally show "card (set [j\<leftarrow>[0..<nc] . j \<notin> snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc}]) =
      nc - card (snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})" by simp
  qed auto
  interpret kernel nr nc A by (unfold_locales, rule A)
  show basis: "basis ?B"
    unfolding Ker.basis_def
  proof (intro conjI)
    show "VKMod.span ?B = mat_kernel A"
    proof
      show "VKMod.span ?B \<subseteq> mat_kernel A"
        using sub by (rule VKMod.span_is_subset2)
      show "mat_kernel A \<subseteq> VKMod.span ?B"
      proof
        fix v
        assume "v \<in> mat_kernel A" 
        from mat_kernelD[OF A this]
        have v: "v \<in> carrier\<^sub>v nc" and Av: "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr" by auto
        let ?bi = "non_pivot_base A (pivot_positions A)"
        let ?ran = "set [j\<leftarrow>[0..<nc] . j \<notin> snd ` ?pp]"
        let ?ran' = "set [j\<leftarrow>[0..<nc] . j \<in> snd ` ?pp]"
        have dimv: "dim\<^sub>v v = nc" using v by auto
        def I \<equiv> "\<lambda> b. SOME i. i \<in> ?ran \<and> ?bi i = b"
        {
          fix j
          assume j: "j \<in> ?ran"
          hence "\<exists> i. i \<in> ?ran \<and> ?bi i = ?bi j" unfolding find_base_vectors_def Let_def dim by auto
          from someI_ex[OF this] have I: "I (?bi j) \<in> ?ran" and id: "?bi (I (?bi j)) = ?bi j" unfolding I_def by blast+
          from inj_onD[OF inj id I j] have "I (?bi j) = j" .
        } note I = this        
        def a \<equiv> "\<lambda> b. v $ (I b)"
        have a: "a \<in> ?B \<rightarrow> carrier F" by (auto simp: class_field_def)
        from VKMod.lincomb_closed[OF sub a] have diml: "dim\<^sub>v (VKMod.lincomb a ?B) = nc"
          unfolding mat_kernel_def using dim lincomb_same by auto
        have "v = VKMod.lincomb a ?B"
        proof (rule vec_eqI; unfold diml dimv)
          fix j
          assume j: "j < nc"
          have "VKMod.lincomb a ?B $ j = (\<Sum>b\<in> ?B. a b * b $ j)" by (rule lincomb_index[OF j sub])
          also have "\<dots> = (\<Sum> i\<in> ?ran. v $ i * ?bi i $ j)"
          proof (subst setsum.reindex_cong[OF inj])
            show "?B = ?bi ` ?ran"  unfolding find_base_vectors_def Let_def dim by auto
            fix i
            assume "i \<in> ?ran"
            hence "I (?bi i) = i" by (rule I)
            hence "a (?bi i) = v $ i" unfolding a_def by simp
            thus "a (?bi i) * ?bi i $ j = v $ i * ?bi i $ j" by simp
          qed auto
          also have "\<dots> = v $ j"
          proof (cases "j \<in> ?ran")
            case True
            hence nmem: "j \<notin> snd ` set (pivot_positions A)" by auto 
            note npb = non_pivot_base[OF j nmem]
            have "(\<Sum> i\<in> ?ran. v $ i * (?bi i) $ j) =
              v $ j * ?bi j $ j + (\<Sum> i\<in> ?ran - {j}. v $ i * ?bi i $ j)"
              by (subst setsum.remove[OF _ True], auto)
            also have "?bi j $ j = 1" using npb by simp
            also have "(\<Sum> i \<in> ?ran - {j}. v $ i * ?bi i $ j) = 0"
              using insert non_pivot_base(4)[OF _ _ j nmem] by (intro setsum.neutral, auto)
            finally show ?thesis by simp
          next
            case False
            with j have jpp: "j \<in> snd ` ?pp" by auto
            with j pp obtain i where i: "i < nr" and ji: "j = p i" and pi: "p i < nc" by auto
            from arg_cong[OF Av, of "\<lambda> u. u $ i"] i A
            have "v $ j = v $ j - row A i \<bullet> v" by auto
            also have "row A i \<bullet> v = (\<Sum> j = 0 ..< nc. A $$ (i,j) * v $ j)" unfolding scalar_prod_def using v A i by auto
            also have "\<dots> = (\<Sum> j \<in> ?ran. A $$ (i,j) * v $ j) +  (\<Sum> j \<in> ?ran'. A $$ (i,j) * v $ j)"
              by (subst setsum.union_disjoint[symmetric], auto intro: setsum.cong)
            also have "(\<Sum> j \<in> ?ran'. A $$ (i,j) * v $ j) =
              A $$ (i,p i) * v $ j + (\<Sum> j \<in> ?ran' - {p i}. A $$ (i,j) * v $ j)"
              using jpp by (subst setsum.remove, auto simp: ji i pi)
            also have "A $$ (i, p i) = 1" using piv(4)[OF i] pi ji by auto
            also have "(\<Sum> j \<in> ?ran' - {p i}. A $$ (i,j) * v $ j) = 0"
            proof (rule setsum.neutral, intro ballI)
              fix j'
              assume "j' \<in> ?ran' - {p i}"
              then obtain i' where i': "i' < nr" and j': "j' = p i'" and pi': "p i' \<noteq> nc" and neq: "p i' \<noteq> p i"
                unfolding pp by auto
              from pi' piv[OF i'] have pi': "p i' < nc" by auto
              from pp pi' neq j i' i have "i \<noteq> i'" by auto
              from piv(5)[OF i' pi' i this]
              show "A $$ (i,j') * v $ j' = 0" unfolding j' by simp
            qed
            also have "(\<Sum> j \<in> ?ran. A $$ (i,j) * v $ j) = - (\<Sum> j \<in> ?ran. v $ j * - A $$ (i,j))" 
              unfolding setsum_negf[symmetric] by (rule setsum.cong, auto)
            finally have vj: "v $ j = (\<Sum> j \<in> ?ran. v $ j * - A $$ (i,j))" by simp
            show ?thesis unfolding vj j
            proof (rule setsum.cong[OF refl])
              fix j'
              assume j': "j' \<in> ?ran"
              from jpp j' have jj': "j \<noteq> j'" by auto
              let ?map = "map prod.swap (pivot_positions A)"
              from ji i j have "(i,j) \<in> set (pivot_positions A)" unfolding pp by auto
              hence mem: "(j,i) \<in> set ?map" by auto
              from pp have "distinct (map fst ?map)" unfolding map_map o_def prod.swap_def fst_conv by auto
              from map_of_is_SomeI[OF this mem] have "map_of ?map j = Some i" by auto
              hence "?bi j' $ j = - A $$ (i, j')" 
                unfolding non_pivot_base_def Let_def dim using j jj' by auto
              thus "v $ j' * ?bi j' $ j = v $ j' * - A $$ (i,j')" by simp
            qed
          qed
          finally show "v $ j = VKMod.lincomb a ?B $ j" ..
        qed auto
        thus "v \<in> VKMod.span ?B" using a unfolding VKMod.span_def by auto
      qed
    qed
    show "?B \<subseteq> mat_kernel A" by (rule sub)
    {
      fix a v
      assume lc: "VKMod.lincomb a ?B = \<zero>\<^sub>v nc" and vB: "v \<in> ?B"
      from vB[unfolded find_base_vectors_def Let_def dim]
        obtain j where j: "j < nc" "j \<notin> snd ` ?pp" and v: "v = non_pivot_base A (pivot_positions A) j"
        by auto         
      from arg_cong[OF lc, of "\<lambda> v. v $ j"] j
      have "0 = VKMod.lincomb a ?B $ j" by auto
      also have "\<dots> = (\<Sum>v\<in>?B. a v * v $ j)" 
        by (subst lincomb_index[OF j(1) sub], simp)
      also have "\<dots> = a v * v $ j + (\<Sum>w\<in>?B - {v}. a w * w $ j)"
        by (subst setsum.remove[OF _ vB], auto)
      also have "a v * v $ j = a v" using non_pivot_base[OF j, folded v] by simp
      also have "(\<Sum>w\<in>?B - {v}. a w * w $ j) = 0"
      proof (rule setsum.neutral, intro ballI)
        fix w
        assume wB: "w \<in> ?B - {v}"
        from this[unfolded find_base_vectors_def Let_def dim]
        obtain j' where j': "j' < nc" "j' \<notin> snd ` ?pp" and w: "w = non_pivot_base A (pivot_positions A) j'"
          by auto    
        with wB v have "j' \<noteq> j" by auto
        from non_pivot_base(4)[OF j' j this]
        show "a w * w $ j = 0" unfolding w by simp
      qed
      finally have "a v = 0" by simp
    }
    thus "\<not> VKMod.lin_dep ?B"     
      by (intro VKMod.finite_lin_indpt2[OF finite_set sub], auto simp: class_field_def)
  qed
  show "dim = nc - card { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
    using Ker.dim_basis[OF finite_set basis] card by simp
qed


definition kernel_dim :: "'a :: field mat \<Rightarrow> nat" where
  [code del]: "kernel_dim A = kernel.dim (dim\<^sub>c A) A"

lemma (in kernel) kernel_dim [simp]: "kernel_dim A = dim" unfolding kernel_dim_def
  using A by simp

lemma kernel_dim_code[code]: 
  "kernel_dim A = dim\<^sub>c A - length (pivot_positions (gauss_jordan_single A))"
proof -
  def nr \<equiv> "dim\<^sub>r A" def nc \<equiv> "dim\<^sub>c A"
  let ?B = "gauss_jordan_single A"
  have A: "A \<in> carrier\<^sub>m nr nc" unfolding nr_def nc_def by auto
  from gauss_jordan_single[OF A refl]
    obtain P Q where AB: "?B = P \<otimes>\<^sub>m A" and QP: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m nr" and
    P: "P \<in> carrier\<^sub>m nr nr" and Q: "Q \<in> carrier\<^sub>m nr nr" and B: "?B \<in> carrier\<^sub>m nr nc" 
    and row: "row_echelon_form ?B" by auto
  interpret K: kernel nr nc ?B
    by (unfold_locales, rule B)
  from mat_kernel_mult_eq[OF A P Q QP, folded AB]
  have "kernel_dim A = K.dim" unfolding kernel_dim_def using A by simp
  also have "\<dots> = nc - length (pivot_positions ?B)" using find_base_vectors[OF row B] by auto
  also have "\<dots> = dim\<^sub>c A - length (pivot_positions ?B)"
    unfolding nc_def by simp
  finally show ?thesis .
qed


lemma kernel_one_mat: fixes A :: "'a :: field mat" and n :: nat
  defines A: "A \<equiv> \<one>\<^sub>m n"
  shows 
    "kernel.dim n A = 0"
    "kernel.basis n A {}"
proof -
  have Ac: "A \<in> carrier\<^sub>m n n" unfolding A by auto
  have "pivot_fun A id n"
    unfolding A by (rule pivot_funI, auto)
  hence row: "row_echelon_form A" unfolding row_echelon_form_def A by auto
  have "{i. i < n \<and> row A i \<noteq> \<zero>\<^sub>v n} = {0 ..< n}" unfolding A by auto
  hence id: "card {i. i < n \<and> row A i \<noteq> \<zero>\<^sub>v n} = n" by auto
  interpret kernel n n A by (unfold_locales, rule Ac)
  from find_base_vectors[OF row Ac, unfolded id]
  show "dim = 0" "basis {}" by auto
qed

lemma kernel_upper_triangular: assumes A: "A \<in> carrier\<^sub>m n n"
  and ut: "upper_triangular A" and 0: "0 \<notin> set (mat_diag A)"
  shows "kernel.dim n A = 0" "kernel.basis n A {}"
proof -
  def ma \<equiv> "mat_diag A"
  from det_upper_triangular[OF ut A] have "det A = listprod (mat_diag A)" .
  also have "\<dots> \<noteq> 0" using 0 unfolding ma_def[symmetric]
    by (induct ma, auto)
  finally have "det A \<noteq> 0" .
  from det_non_zero_imp_unit[OF A this, unfolded Units_def, of "()"]
    obtain B where B: "B \<in> carrier\<^sub>m n n" and BA: "B \<otimes>\<^sub>m A = \<one>\<^sub>m n" and AB: "A \<otimes>\<^sub>m B = \<one>\<^sub>m n"
    by (auto simp: mat_ring_def)
  from mat_kernel_mult_eq[OF A B A AB, unfolded BA]
  have id: "mat_kernel A = mat_kernel (\<one>\<^sub>m n)" ..
  show "kernel.dim n A = 0" "kernel.basis n A {}"
    unfolding id by (rule kernel_one_mat)+
qed

lemma kernel_basis_exists: assumes A: "A \<in> carrier\<^sub>m nr nc"
  shows "\<exists> B. finite B \<and> kernel.basis nc A B"
proof -
  obtain C where gj: "gauss_jordan_single A = C" by auto
  from gauss_jordan_single[OF A gj]
  obtain P Q where CPA: "C = P \<otimes>\<^sub>m A" and QP: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m nr"
    and P: "P \<in> carrier\<^sub>m nr nr" and Q: "Q \<in> carrier\<^sub>m nr nr"   
    and C: "C \<in> carrier\<^sub>m nr nc" and row: "row_echelon_form C"
    by auto
  from find_base_vectors[OF row C] have "\<exists> B. finite B \<and> kernel.basis nc C B" by blast
  also have "mat_kernel C = mat_kernel A" unfolding CPA
    by (rule mat_kernel_mult_eq[OF A P Q QP])
  finally show ?thesis .
qed


lemma mat_kernel_mult_right_gen_set: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and B: "B \<in> carrier\<^sub>m nc nc"
  and C: "C \<in> carrier\<^sub>m nc nc"
  and inv: "B \<otimes>\<^sub>m C = \<one>\<^sub>m nc"
  and gen_set: "kernel.gen_set nc (A \<otimes>\<^sub>m B) gen" and gen: "gen \<subseteq> mat_kernel (A \<otimes>\<^sub>m B)"
  shows "kernel.gen_set nc A ((op \<otimes>\<^sub>m\<^sub>v B) ` gen)" "op \<otimes>\<^sub>m\<^sub>v B ` gen \<subseteq> mat_kernel A" "card ((op \<otimes>\<^sub>m\<^sub>v B) ` gen) = card gen"
proof -
  let ?AB = "A \<otimes>\<^sub>m B"
  let ?gen = "(op \<otimes>\<^sub>m\<^sub>v B) ` gen"
  from A B have AB: "A \<otimes>\<^sub>m B \<in> carrier\<^sub>m nr nc" by auto
  from B have dimB: "dim\<^sub>r B = nc" by auto
  from inv B C have CB: "C \<otimes>\<^sub>m B = \<one>\<^sub>m nc" by (metis mat_mult_left_right_inverse)
  interpret AB: kernel nr nc ?AB 
    by (unfold_locales, rule AB)
  interpret A: kernel nr nc A
    by (unfold_locales, rule A)
  {
    fix w
    assume "w \<in> ?gen"
    then obtain v where w: "w = B \<otimes>\<^sub>m\<^sub>v v" and v: "v \<in> gen" by auto
    from v have "v \<in> mat_kernel ?AB" using gen by auto
    hence v: "v \<in> carrier\<^sub>v nc" and 0: "?AB \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr" unfolding mat_kernel[OF AB] by auto
    have "?AB \<otimes>\<^sub>m\<^sub>v v = A \<otimes>\<^sub>m\<^sub>v w" unfolding w using v A B by simp
    with 0 have 0: "A \<otimes>\<^sub>m\<^sub>v w = \<zero>\<^sub>v nr" by auto
    from w B v have w: "w \<in> carrier\<^sub>v nc" by auto
    from 0 w have "w \<in> mat_kernel A" unfolding mat_kernel[OF A] by auto
  } 
  thus genn: "?gen \<subseteq> mat_kernel A" by auto
  hence one_dir: "A.VKMod.span ?gen \<subseteq> mat_kernel A" by fastforce
  {
    fix v v'
    assume v: "v \<in> gen" and v': "v' \<in> gen" and id: "B \<otimes>\<^sub>m\<^sub>v v = B \<otimes>\<^sub>m\<^sub>v v'"
    from v v' have v: "v \<in> carrier\<^sub>v nc" and v': "v' \<in> carrier\<^sub>v nc" 
      using gen unfolding mat_kernel[OF AB] by auto
    from arg_cong[OF id, of "\<lambda> v. C \<otimes>\<^sub>m\<^sub>v v"]
    have "v = v'" using v v'
      unfolding mat_vec_mult_assoc[symmetric, OF C B v] 
        mat_vec_mult_assoc[symmetric, OF C B v'] CB
      by auto
  } note inj = this
  hence inj_gen: "inj_on (op \<otimes>\<^sub>m\<^sub>v B) gen" unfolding inj_on_def by auto
  show "card ?gen = card gen" using inj_gen by (rule card_image)
  {
    fix v
    let ?Cv = "C \<otimes>\<^sub>m\<^sub>v v"
    assume "v \<in> mat_kernel A"
    from mat_kernelD[OF A this] have v: "v \<in> carrier\<^sub>v nc" and 0: "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v nr" by auto
    have "?AB \<otimes>\<^sub>m\<^sub>v ?Cv = (A \<otimes>\<^sub>m (B \<otimes>\<^sub>m C)) \<otimes>\<^sub>m\<^sub>v v" using A B C v 
      by (subst mat_vec_mult_assoc[symmetric, OF AB C v], subst mat_mult_assoc[OF A B C], simp)
    also have "\<dots> = \<zero>\<^sub>v nr" unfolding inv using 0 A v by simp
    finally have 0: "?AB \<otimes>\<^sub>m\<^sub>v ?Cv = \<zero>\<^sub>v nr" and Cv: "?Cv \<in> carrier\<^sub>v nc" using C v by auto
    hence "?Cv \<in> mat_kernel ?AB" unfolding mat_kernel[OF AB] by auto
    with gen_set have "?Cv \<in> AB.VKMod.span gen" by auto
    from this[unfolded AB.VKMod.span_def] obtain a gen' where 
      Cv: "?Cv = AB.VKMod.lincomb a gen'" and sub: "gen' \<subseteq> gen" and fin: "finite gen'" by auto
    let ?gen' = "(op \<otimes>\<^sub>m\<^sub>v B) ` gen'"
    from sub gen have gen': "gen' \<subseteq> mat_kernel ?AB" by auto
    have lin1: "AB.VKMod.lincomb a gen' \<in> carrier\<^sub>v nc"
      using AB.VKMod.lincomb_closed[OF gen', of a]
      unfolding mat_kernel[OF AB] by (auto simp: class_field_def)
    hence dim1: "dim\<^sub>v (AB.VKMod.lincomb a gen') = nc" by auto
    hence dim1b: "dim\<^sub>v (B \<otimes>\<^sub>m\<^sub>v (AB.VKMod.lincomb a gen')) = nc" using B by auto
    from genn sub have genn': "?gen' \<subseteq> mat_kernel A" by auto
    from gen sub have gen'nc: "gen' \<subseteq> carrier\<^sub>v nc" unfolding mat_kernel[OF AB] by auto
    def a' \<equiv> "\<lambda> b. a (C \<otimes>\<^sub>m\<^sub>v b)"
    from A.VKMod.lincomb_closed[OF genn']
    have lin2: "A.VKMod.lincomb a' ?gen' \<in> carrier\<^sub>v nc"
      unfolding mat_kernel[OF A] by (auto simp: class_field_def)
    hence dim2: "dim\<^sub>v (A.VKMod.lincomb a' ?gen') = nc" by auto
    have "v = B \<otimes>\<^sub>m\<^sub>v ?Cv" 
      by (unfold mat_vec_mult_assoc[symmetric, OF B C v] inv, insert v, simp)
    hence "v = B \<otimes>\<^sub>m\<^sub>v AB.VKMod.lincomb a gen'" unfolding Cv by simp
    also have "\<dots> = A.VKMod.lincomb a' ?gen'"
    proof (rule vec_eqI; unfold dim1 dim1b dim2)
      fix i
      assume i: "i < nc"
      with dimB have ii: "i < dim\<^sub>r B" by auto
      from sub inj have inj: "inj_on (op \<otimes>\<^sub>m\<^sub>v B) gen'" unfolding inj_on_def by auto
      {
        fix v
        assume "v \<in> gen'"
        with gen'nc have v: "v \<in> carrier\<^sub>v nc" by auto
        hence "a' (B \<otimes>\<^sub>m\<^sub>v v) = a v" unfolding a'_def mat_vec_mult_assoc[symmetric, OF C B v] CB by auto
      } note a' = this
      have "A.VKMod.lincomb a' ?gen' $ i = (\<Sum>v\<in>op \<otimes>\<^sub>m\<^sub>v B ` gen'. a' v * v $ i)"
        unfolding A.lincomb_index[OF i genn']  by simp
      also have "\<dots> = (\<Sum>v\<in>gen'. a v * ((B \<otimes>\<^sub>m\<^sub>v v) $ i))"
        by (rule setsum.reindex_cong[OF inj refl], auto simp: a')
      also have "\<dots> = (\<Sum>v\<in>gen'. (\<Sum>j = 0..< nc. a v * row B i $ j * v $ j))"
        unfolding mat_mult_vec_def dimB scalar_prod_def vec_index_vec[OF i]
        by (rule setsum.cong, insert gen'nc, auto simp: setsum_right_distrib ac_simps)
      also have "\<dots> = (\<Sum>j = 0 ..< nc. (\<Sum>v \<in> gen'. a v * row B i $ j * v $ j))"
        by (rule setsum.commute)
      also have "\<dots> = (\<Sum>j = 0..<nc. row B i $ j * (\<Sum>v\<in>gen'. a v * v $ j))"
        by (rule setsum.cong, auto simp: setsum_right_distrib ac_simps)
      also have "\<dots> = (B \<otimes>\<^sub>m\<^sub>v AB.VKMod.lincomb a gen') $ i"
        unfolding index_mat_mult_vec[OF ii]
        unfolding scalar_prod_def dim1
        by (rule setsum.cong[OF refl], subst AB.lincomb_index[OF _ gen'], auto)
      finally show "(B \<otimes>\<^sub>m\<^sub>v AB.VKMod.lincomb a gen') $ i = A.VKMod.lincomb a' ?gen' $ i" ..
    qed auto
    finally have "v \<in> A.VKMod.span ?gen" using sub fin
      unfolding A.VKMod.span_def by (auto simp: class_field_def intro!: exI[of _ a'] exI[of _ ?gen'])
  }
  hence other_dir: "A.VKMod.span ?gen \<supseteq> mat_kernel A" by fastforce
  from one_dir other_dir show "kernel.gen_set nc A ((op \<otimes>\<^sub>m\<^sub>v B) ` gen)" by auto
qed

lemma mat_kernel_mult_right_basis: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and B: "B \<in> carrier\<^sub>m nc nc"
  and C: "C \<in> carrier\<^sub>m nc nc"
  and inv: "B \<otimes>\<^sub>m C = \<one>\<^sub>m nc"
  and fin: "finite gen"
  and basis: "kernel.basis nc (A \<otimes>\<^sub>m B) gen"
  shows "kernel.basis nc A ((op \<otimes>\<^sub>m\<^sub>v B) ` gen)" 
  "card ((op \<otimes>\<^sub>m\<^sub>v B) ` gen) = card gen"
proof -
  let ?AB = "A \<otimes>\<^sub>m B"
  let ?gen = "(op \<otimes>\<^sub>m\<^sub>v B) ` gen"
  from A B have AB: "?AB \<in> carrier\<^sub>m nr nc" by auto
  from B have dimB: "dim\<^sub>r B = nc" by auto
  from inv B C have CB: "C \<otimes>\<^sub>m B = \<one>\<^sub>m nc" by (metis mat_mult_left_right_inverse)
  interpret AB: kernel nr nc ?AB 
    by (unfold_locales, rule AB)
  interpret A: kernel nr nc A
    by (unfold_locales, rule A)
  from basis[unfolded AB.Ker.basis_def] have gen_set: "AB.gen_set gen" and genAB: "gen \<subseteq> mat_kernel ?AB" by auto
  from mat_kernel_mult_right_gen_set[OF A B C inv gen_set genAB]
  have gen: "A.gen_set ?gen" and sub: "?gen \<subseteq> mat_kernel A" and card: "card ?gen = card gen" .
  from card show "card ?gen = card gen" .
  from fin have fing: "finite ?gen" by auto
  from gen have gen: "A.VKMod.span ?gen = mat_kernel A" by auto
  have ABC: "A \<otimes>\<^sub>m B \<otimes>\<^sub>m C = A" using A B C inv by simp
  from kernel_basis_exists[OF A] obtain bas where finb: "finite bas" and bas: "A.basis bas" by auto
  from bas have bas': "A.gen_set bas" "bas \<subseteq> mat_kernel A" unfolding A.Ker.basis_def by auto
  let ?bas = "op \<otimes>\<^sub>m\<^sub>v C ` bas"
  from mat_kernel_mult_right_gen_set[OF AB C B CB, unfolded ABC, OF bas']
  have bas': "?bas \<subseteq> mat_kernel ?AB" "AB.VKMod.span ?bas = mat_kernel ?AB" "card ?bas = card bas" by auto
  from finb bas have cardb: "A.dim = card bas" by (rule A.Ker.dim_basis)
  from fin basis have cardg: "AB.dim = card gen" by (rule AB.Ker.dim_basis)
  from AB.Ker.gen_ge_dim[OF _ bas'(1-2)] finb bas'(3) cardb cardg
  have ineq1: "card gen \<le> A.dim" by auto
  from A.Ker.dim_gen_is_basis[OF fing sub gen, unfolded card, OF this]
  show "A.basis ?gen" .
qed  
  
  
lemma mat_kernel_dim_mult_eq_right: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and B: "B \<in> carrier\<^sub>m nc nc"
  and C: "C \<in> carrier\<^sub>m nc nc"
  and BC: "B \<otimes>\<^sub>m C = \<one>\<^sub>m nc"
  shows "kernel.dim nc (A \<otimes>\<^sub>m B) = kernel.dim nc A"
proof -
  let ?AB = "A \<otimes>\<^sub>m B"
  from A B have AB: "?AB \<in> carrier\<^sub>m nr nc" by auto
  interpret AB: kernel nr nc ?AB 
    by (unfold_locales, rule AB)
  interpret A: kernel nr nc A
    by (unfold_locales, rule A)
  from kernel_basis_exists[OF AB] obtain bas where finb: "finite bas" and bas: "AB.basis bas" by auto
  let ?bas = "(op \<otimes>\<^sub>m\<^sub>v B) ` bas"
  from mat_kernel_mult_right_basis[OF A B C BC finb bas] finb
  have bas': "A.basis ?bas" and finb': "finite ?bas" and card: "card ?bas = card bas" by auto
  show "AB.dim = A.dim" unfolding A.Ker.dim_basis[OF finb' bas'] AB.Ker.dim_basis[OF finb bas] card ..
qed


locale vardim =
  fixes f_ty :: "'a :: field itself"
begin

abbreviation "K == class_field TYPE('a::field)"
abbreviation "M == \<lambda>k. module\<^sub>v TYPE('a) k"

abbreviation "span == \<lambda>k. module.span K (M k)"
abbreviation "lincomb == \<lambda>k. module.lincomb (M k)"
abbreviation "lin_dep == \<lambda>k. module.lin_dep K (M k)"
abbreviation "padr m v == v @\<^sub>v \<zero>\<^sub>v m"
definition "unpadr m v == vec (dim\<^sub>v v - m) (\<lambda>i. v $ i)"
abbreviation "padl m v == \<zero>\<^sub>v m @\<^sub>v v"
definition "unpadl m v == vec (dim\<^sub>v v - m) (\<lambda>i. v $ (m+i))"

lemma unpadr_padr[simp]: "unpadr m (padr m v) = v" unfolding unpadr_def by auto
lemma unpadl_padl[simp]: "unpadl m (padl m v) = v" unfolding unpadl_def by auto

lemma padr_unpadr[simp]: "v : padr m ` U \<Longrightarrow> padr m (unpadr m v) = v" by auto
lemma padl_unpadl[simp]: "v : padl m ` U \<Longrightarrow> padl m (unpadl m v) = v" by auto

(* somehow not automatically proven *)
lemma padr_image:
  assumes "U \<subseteq> carrier\<^sub>v n" shows "padr m ` U \<subseteq> carrier\<^sub>v (n + m)"
proof(rule subsetI)
  fix v assume "v : padr m ` U"
  then obtain u where "u : U" and vmu: "v = padr m u" by auto
  hence "u : carrier\<^sub>v n" using assms by auto
  thus "v : carrier\<^sub>v (n + m)"
    unfolding vmu
    using vec_zero_carrier[of m] vec_append_carrier by metis
qed
lemma padl_image:
  assumes "U \<subseteq> carrier\<^sub>v n" shows "padl m ` U \<subseteq> carrier\<^sub>v (m + n)"
proof(rule subsetI)
  fix v assume "v : padl m ` U"
  then obtain u where "u : U" and vmu: "v = padl m u" by auto
  hence "u : carrier\<^sub>v n" using assms by auto
  thus "v : carrier\<^sub>v (m + n)"
    unfolding vmu
    using vec_zero_carrier[of m] vec_append_carrier by metis
qed

lemma padr_inj:
  shows "inj_on (padr m) (carrier\<^sub>v n :: 'a vec set)"
  apply(intro inj_onI) using vec_append_eq by auto

lemma padl_inj:
  shows "inj_on (padl m) (carrier\<^sub>v n :: 'a vec set)"
  apply(intro inj_onI)
  using vec_append_eq[OF vec_zero_carrier vec_zero_carrier] by auto

lemma lincomb_pad:
  fixes m n a
  assumes U: "(U :: 'a vec set) \<subseteq> carrier\<^sub>v n"
      and finU: "finite U"
  defines "goal pad unpad W == pad m (lincomb n a W) = lincomb (n+m) (a o unpad m) (pad m ` W)"
  shows "goal padr unpadr U" (is ?R) and "goal padl unpadl U" (is "?L")
proof -
  interpret N: vectorspace K "M n" using vec_vs.
  interpret NM: vectorspace "K" "M (n+m)" using vec_vs.
  note [simp] = vec_module_simps class_ring_simps
  have "?R \<and> ?L" using finU U
  proof (induct set:finite)
    case empty thus ?case
      unfolding goal_def unfolding N.lincomb_def NM.lincomb_def by auto next
    case (insert u U)
      hence finU: "finite U"
        and U: "U \<subseteq> carrier\<^sub>v n"
        and u[simp]: "u : carrier\<^sub>v n"
        and uU: "u \<notin> U"
        and auU: "a : insert u U \<rightarrow> UNIV"
        and aU: "a : U \<rightarrow> UNIV"
        and au: "a u : UNIV"
        by auto
      have IHr: "goal padr unpadr U" and IHl: "goal padl unpadl U"
        using insert(3) U aU by auto
      note N_lci = N.lincomb_insert2[unfolded vec_module_simps]
      note NM_lci = NM.lincomb_insert2[unfolded vec_module_simps]
      have auu[simp]: "a u \<odot>\<^sub>v u : carrier\<^sub>v n" using au u by simp
      have laU[simp]: "lincomb n a U : carrier\<^sub>v n"
        using N.lincomb_closed[unfolded vec_module_simps class_ring_simps, OF U aU].
      let ?m0 = "\<zero>\<^sub>v m :: 'a vec"
      have m0: "?m0 : carrier\<^sub>v m" by auto
      have ins: "lincomb n a (insert u U) = a u \<odot>\<^sub>v u \<oplus>\<^sub>v lincomb n a U"
        using N_lci[OF finU U] auU uU u by auto
      show ?case
      proof
        have "padr m (a u \<odot>\<^sub>v u \<oplus>\<^sub>v lincomb n a U) =
          (a u \<odot>\<^sub>v u \<oplus>\<^sub>v lincomb n a U) @\<^sub>v (?m0 \<oplus>\<^sub>v ?m0)" by auto
        also have "... = padr m (a u \<odot>\<^sub>v u) \<oplus>\<^sub>v padr m (lincomb n a U)"
          using vec_append_add[symmetric, OF auu laU]
          using vec_zero_carrier[of m] by metis
        also have "padr m (lincomb n a U) = lincomb (n+m) (a o unpadr m) (padr m ` U)"
          using IHr unfolding goal_def.
        also have "padr m (a u \<odot>\<^sub>v u) = a u \<odot>\<^sub>v padr m u" by auto
        also have "... = (a o unpadr m) (padr m u) \<odot>\<^sub>v padr m u" by auto
        also have "... \<oplus>\<^sub>v lincomb (n+m) (a o unpadr m) (padr m ` U) =
          lincomb (n+m) (a o unpadr m) (insert (padr m u) (padr m ` U))"
          apply(subst NM_lci[symmetric])
          using finU uU U vec_append_eq[OF u] by auto
        also have "insert (padr m u) (padr m ` U) = padr m ` insert u U"
          by auto
        finally show "goal padr unpadr (insert u U)" unfolding goal_def ins.
        have [simp]: "n+m = m+n" by auto
        have "padl m (a u \<odot>\<^sub>v u \<oplus>\<^sub>v lincomb n a U) =
          (?m0 \<oplus>\<^sub>v ?m0) @\<^sub>v (a u \<odot>\<^sub>v u \<oplus>\<^sub>v lincomb n a U)" by auto
        also have "... = padl m (a u \<odot>\<^sub>v u) \<oplus>\<^sub>v padl m (lincomb n a U)"
          using vec_append_add[symmetric, OF _ _ auu laU]
          using vec_zero_carrier[of m] by metis
        also have "padl m (lincomb n a U) = lincomb (n+m) (a o unpadl m) (padl m ` U)"
          using IHl unfolding goal_def.
        also have "padl m (a u \<odot>\<^sub>v u) = a u \<odot>\<^sub>v padl m u" by auto
        also have "... = (a o unpadl m) (padl m u) \<odot>\<^sub>v padl m u" by auto
        also have "... \<oplus>\<^sub>v lincomb (n+m) (a o unpadl m) (padl m ` U) =
          lincomb (n+m) (a o unpadl m) (insert (padl m u) (padl m ` U))"
          apply(subst NM_lci[symmetric])
          using finU uU U vec_append_eq[OF m0] by auto
        also have "insert (padl m u) (padl m ` U) = padl m ` insert u U"
          by auto
        finally show "goal padl unpadl (insert u U)" unfolding goal_def ins.
      qed
  qed
  thus ?R ?L by auto
qed

lemma span_pad:
  assumes U: "(U::'a vec set) \<subseteq> carrier\<^sub>v n"
  defines "goal pad m == pad m ` span n U = span (n+m) (pad m ` U)"
  shows "goal padr m" "goal padl m"
proof -
  interpret N: vectorspace K "M n" using vec_vs.
  interpret NM: vectorspace "K" "M (n+m)" using vec_vs.
  { fix pad :: "'a vec \<Rightarrow> 'a vec" and unpad :: "'a vec \<Rightarrow> 'a vec"
    assume main: "\<And>A a. A \<subseteq> U \<Longrightarrow> finite A \<Longrightarrow>
      pad (lincomb n a A) = lincomb (n+m) (a o unpad) (pad ` A)"
    assume [simp]: "\<And>v. unpad (pad v) = v"
    assume pU: "pad ` U \<subseteq> carrier\<^sub>v (n+m)"
    have "pad ` (span n U) = span (n+m) (pad ` U)"
    proof (intro Set.equalityI subsetI)
      fix x assume "x : pad ` (span n U)"
      then obtain v where "v : span n U" and xv: "x = pad v" by auto
      then obtain a A
        where AU: "A \<subseteq> U" and finA: "finite A" and a: "a : A \<rightarrow> UNIV"
          and vaA: "v = lincomb n a A"
        unfolding N.span_def by auto
      hence A: "A \<subseteq> carrier\<^sub>v n" using U by auto
      show "x : span (n+m) (pad ` U)" unfolding NM.span_def
      proof (intro CollectI exI conjI)
        show "x = lincomb (n+m) (a o unpad) (pad ` A)"
          using xv vaA main[OF AU finA] by auto
        show "pad ` A \<subseteq> pad ` U" using AU by auto
      qed (insert finA, auto simp: class_ring_simps)
      next
      fix x assume "x : span (n+m) (pad ` U)"
      then obtain a' A'
        where A'U: "A' \<subseteq> pad ` U" and finA': "finite A'" and a': "a' : A' \<rightarrow> UNIV"
          and xa'A': "x = lincomb (n+m) a' A'"
        unfolding NM.span_def by auto
      then obtain A where finA: "finite A" and AU: "A \<subseteq> U" and A'A: "A' = pad ` A"
        using finite_subset_image[OF finA' A'U] by auto
      hence A: "A \<subseteq> carrier\<^sub>v n" using U by auto
      have A': "A' \<subseteq> carrier\<^sub>v (n+m)" using A'U pU by auto
      def a == "a' o pad"
      def a'' == "(a' o pad) o unpad"
      have a: "a : A \<rightarrow> UNIV" by auto
      have restr: "restrict a' A' = restrict a'' A'"
      proof(rule restrict_ext)
        fix u' assume "u' : A'"
        then obtain u where "u : A" and "u' = pad u" unfolding A'A by auto
        thus "a' u' = a'' u'" unfolding a''_def a_def by auto
      qed
      have "x = lincomb (n+m) a' A'" using xa'A' unfolding A'A.
      also have "... = lincomb (n+m) a'' A'"
        apply (subst NM.lincomb_restrict)
        using finA' A' restr by (auto simp: vec_module_simps class_ring_simps)
      also have "... = lincomb (n+m) a'' (pad ` A)" unfolding A'A..
      also have "... = pad (lincomb n a A)"
        unfolding a''_def using main[OF AU finA] unfolding a_def by auto
      finally show "x : pad ` (span n U)" unfolding N.span_def
      apply(rule image_eqI, intro CollectI exI conjI)
        using finA AU by (auto simp: class_ring_simps)
    qed
  }
  note main = this
  have AUC: "\<And>A. A \<subseteq> U \<Longrightarrow> A \<subseteq> carrier\<^sub>v n" using U by simp
  have [simp]: "n+m = m+n" by auto
  show "goal padr m" unfolding goal_def
    apply (subst main[OF _ _ padr_image[OF U]])
    using lincomb_pad[OF AUC] unpadr_padr by auto
  show "goal padl m" unfolding goal_def
    apply (subst main)
    using lincomb_pad[OF AUC] unpadl_padl padl_image[OF U] by auto
qed

lemma kernel_padr:
  assumes aA: "a : mat_kernel (A :: 'a :: field mat)"
      and A: "A : carrier\<^sub>m nr1 nc1"
      and B: "B : carrier\<^sub>m nr1 nc2"
      and D: "D : carrier\<^sub>m nr2 nc2"
  shows "padr nc2 a : mat_kernel (four_block_mat A B (\<zero>\<^sub>m nr2 nc1) D)" (is "_ : mat_kernel ?ABCD")
  unfolding mat_kernel_def
proof (rule, intro conjI)
  have [simp]: "dim\<^sub>r A = nr1" "dim\<^sub>r D = nr2" "dim\<^sub>r ?ABCD = nr1 + nr2" using A D by auto
  have a: "a : carrier\<^sub>v nc1" using mat_kernel_carrier[OF A] aA by auto
  show "?ABCD \<otimes>\<^sub>m\<^sub>v padr nc2 a = \<zero>\<^sub>v (dim\<^sub>r ?ABCD)" (is "?l = ?r")
  proof
    fix i assume i: "i < dim\<^sub>v ?r"
    hence "?l $ i = row ?ABCD i \<bullet> padr nc2 a" by auto
    also have "... = 0"
    proof (cases "i < nr1")
      case True
        hence rows: "row A i : carrier\<^sub>v nc1" "row B i : carrier\<^sub>v nc2"
          using A B by auto
        have "row ?ABCD i = row A i @\<^sub>v row B i"
          using row_four_block_mat(1)[OF A B _ D True] by auto
        also have "... \<bullet> padr nc2 a = row A i \<bullet> a + row B i \<bullet> \<zero>\<^sub>v nc2"
          using scalar_prod_append[OF rows] a by auto
        also have "row A i \<bullet> a = (A \<otimes>\<^sub>m\<^sub>v a) $ i" using True A by auto
        also have "... = 0" using mat_kernelD[OF A aA] True by auto
        also have "row B i \<bullet> \<zero>\<^sub>v nc2 = 0" using True rows by auto
        finally show ?thesis by simp
      next case False
        let ?C = "\<zero>\<^sub>m nr2 nc1"
        let ?i = "i - nr1"
        have rows:
            "row ?C ?i : carrier\<^sub>v nc1" "row D ?i : carrier\<^sub>v nc2"
          using D i False A by auto
        have "row ?ABCD i = row ?C ?i @\<^sub>v row D ?i"
          using row_four_block_mat(2)[OF A B _ D False] i A D by auto
        also have "... \<bullet> padr nc2 a = row ?C ?i \<bullet> a + row D ?i \<bullet> \<zero>\<^sub>v nc2"
          using scalar_prod_append[OF rows] a by auto
        also have "row ?C ?i \<bullet> a = \<zero>\<^sub>v nc1 \<bullet> a" using False A i by auto
        also have "... = 0" using a by auto
        also have "row D ?i \<bullet> \<zero>\<^sub>v nc2 = 0" using False rows by auto
        finally show ?thesis by simp
    qed
    finally show "?l $ i = ?r $ i" using i by auto
  qed auto
  show "padr nc2 a : carrier\<^sub>v (dim\<^sub>c ?ABCD)" using a A D by auto
qed

lemma kernel_padl:
  assumes dD: "d : mat_kernel (D :: 'a :: field mat)"
      and A: "A : carrier\<^sub>m nr1 nc1"
      and C: "C : carrier\<^sub>m nr2 nc1"
      and D: "D : carrier\<^sub>m nr2 nc2"
  shows "padl nc1 d : mat_kernel (four_block_mat A (\<zero>\<^sub>m nr1 nc2) C D)" (is "_ : mat_kernel ?ABCD")
  unfolding mat_kernel_def
proof (rule, intro conjI)
  have [simp]: "dim\<^sub>r A = nr1" "dim\<^sub>r D = nr2" "dim\<^sub>r ?ABCD = nr1 + nr2" using A D by auto
  have d: "d : carrier\<^sub>v nc2" using mat_kernel_carrier[OF D] dD by auto
  show "?ABCD \<otimes>\<^sub>m\<^sub>v padl nc1 d = \<zero>\<^sub>v (dim\<^sub>r ?ABCD)" (is "?l = ?r")
  proof
    fix i assume i: "i < dim\<^sub>v ?r"
    hence "?l $ i = row ?ABCD i \<bullet> padl nc1 d" by auto
    also have "... = 0"
    proof (cases "i < nr1")
      case True
        let ?B = "\<zero>\<^sub>m nr1 nc2"
        have rows: "row A i : carrier\<^sub>v nc1" "row ?B i : carrier\<^sub>v nc2"
          using A True by auto
        have "row ?ABCD i = row A i @\<^sub>v row ?B i"
          using row_four_block_mat(1)[OF A _ C D True] by auto
        also have "... \<bullet> padl nc1 d = row A i \<bullet> \<zero>\<^sub>v nc1 + row ?B i \<bullet> d"
          using scalar_prod_append[OF rows] d by auto
        also have "row A i \<bullet> \<zero>\<^sub>v nc1 = 0" using A True by auto
        also have "row ?B i \<bullet> d = 0" using True d by auto
        finally show ?thesis by simp
      next case False
        let ?i = "i - nr1"
        have rows:
            "row C ?i : carrier\<^sub>v nc1" "row D ?i : carrier\<^sub>v nc2"
          using C D i False A by auto
        have "row ?ABCD i = row C ?i @\<^sub>v row D ?i"
          using row_four_block_mat(2)[OF A _ C D False] i A D by auto
        also have "... \<bullet> padl nc1 d = row C ?i \<bullet> \<zero>\<^sub>v nc1 + row D ?i \<bullet> d"
          using scalar_prod_append[OF rows] d by auto
        also have "row C ?i \<bullet> \<zero>\<^sub>v nc1 = 0" using False A C i by auto
        also have "row D ?i \<bullet> d = (D \<otimes>\<^sub>m\<^sub>v d) $ ?i" using D d False i by auto
        also have "... = 0" using mat_kernelD[OF D dD] using False i by auto
        finally show ?thesis by simp
    qed
    finally show "?l $ i = ?r $ i" using i by auto
  qed auto
  show "padl nc1 d : carrier\<^sub>v (dim\<^sub>c ?ABCD)" using d A D by auto
qed

lemma mat_kernel_split:
  assumes A: "A : carrier\<^sub>m n n"
      and D: "D : carrier\<^sub>m m m"
      and kAD: "k : mat_kernel (four_block_mat A (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) D)"
           (is "_ : mat_kernel ?A00D")
  shows "vec_first k n : mat_kernel A" (is "?a : _")
    and "vec_last k m : mat_kernel D" (is "?d : _")
proof -
  have "\<zero>\<^sub>v n @\<^sub>v \<zero>\<^sub>v m = \<zero>\<^sub>v (n+m)" by auto
  also
    have A00D: "?A00D : carrier\<^sub>m (n+m) (n+m)" using four_block_mat_carrier[OF A D].
    hence k: "k : carrier\<^sub>v (n+m)" using kAD mat_kernel_carrier by auto
    hence "?a @\<^sub>v ?d = k" by simp
    hence "\<zero>\<^sub>v (n+m) = ?A00D \<otimes>\<^sub>m\<^sub>v (?a @\<^sub>v ?d)" using mat_kernelD[OF A00D] kAD by auto
  also have "... = A \<otimes>\<^sub>m\<^sub>v ?a @\<^sub>v D \<otimes>\<^sub>m\<^sub>v ?d"
    using mat_mult_vec_split[OF A D] by auto
  finally have "\<zero>\<^sub>v n @\<^sub>v \<zero>\<^sub>v m = A \<otimes>\<^sub>m\<^sub>v ?a @\<^sub>v D \<otimes>\<^sub>m\<^sub>v ?d".
  hence "\<zero>\<^sub>v n = A \<otimes>\<^sub>m\<^sub>v ?a \<and> \<zero>\<^sub>v m = D \<otimes>\<^sub>m\<^sub>v ?d"
    apply(subst vec_append_eq[of _ n, symmetric]) using A D by auto
  thus "?a : mat_kernel A" "?d : mat_kernel D" unfolding mat_kernel_def using A D by auto
qed

lemma padr_padl_eq:
  assumes v: "v : carrier\<^sub>v n"
  shows "padr m v = padl n u \<longleftrightarrow> v = \<zero>\<^sub>v n \<and> u = \<zero>\<^sub>v m"
  apply (subst vec_append_eq) using v by auto


lemma pad_disjoint:
  assumes A: "A \<subseteq> carrier\<^sub>v n" and A0: "\<zero>\<^sub>v n \<notin> A" and B: "B \<subseteq> carrier\<^sub>v m"
  shows "padr m ` A \<inter> padl n ` B = {}" (is "?A \<inter> ?B = _")
proof (intro equals0I)
  fix ab assume "ab : ?A \<inter> ?B"
  then obtain a b
    where "ab = padr m a" "ab = padl n b" and dim: "a : A" "b : B" by force
  hence "padr m a = padl n b" by auto
  hence "a = \<zero>\<^sub>v n" using dim A B by auto
  thus "False" using dim A0 by auto
qed

lemma padr_padl_lindep:
  assumes A: "A \<subseteq> carrier\<^sub>v n" and liA: "~ lin_dep n A"
      and B: "B \<subseteq> carrier\<^sub>v m" and liB: "~ lin_dep m B"
  shows "~ lin_dep (n+m) (padr m ` A \<union> padl n ` B)" (is "~ lin_dep _ (?A \<union> ?B)")
proof -
  interpret N: vectorspace K "M n" using vec_vs.
  interpret M: vectorspace K "M m" using vec_vs.
  interpret NM: vectorspace "K" "M (n+m)" using vec_vs.
  note [simp] = vec_module_simps class_ring_simps
  have AB: "?A \<union> ?B \<subseteq> carrier\<^sub>v (n+m)"
    using padr_image[OF A] padl_image[OF B] by auto
  show ?thesis
    unfolding NM.lin_dep_def
    unfolding not_ex not_imp[symmetric] not_not
  proof(intro allI impI)
    fix U f u
    assume finU: "finite U"
       and UAB: "U \<subseteq> ?A \<union> ?B"
       and f: "f : U \<rightarrow> carrier K"
       and 0: "lincomb (n+m) f U = \<zero>\<^bsub>M (n+m)\<^esub>"
       and uU: "u : U"
    let ?UA = "U \<inter> ?A" and ?UB = "U \<inter> ?B"
    have "?UA \<subseteq> ?A" "?UB \<subseteq> ?B" by auto
    then obtain A' B'
      where A'A: "A' \<subseteq> A" and B'B: "B' \<subseteq> B"
        and UAA': "?UA = padr m ` A'" and UBB': "?UB = padl n ` B'"
      unfolding subset_image_iff by auto
    hence A': "A' \<subseteq> carrier\<^sub>v n" and B': "B' \<subseteq> carrier\<^sub>v m" using A B by auto
    have finA': "finite A'" and finB': "finite B'"
    proof -
      have "padr m ` A' \<subseteq> U" "padl n ` B' \<subseteq> U" using UAA' UBB' by auto
      hence pre: "finite (padr m ` A')" "finite (padl n ` B')"
        using finite_subset[OF _ finU] by auto
      show "finite A'"
        apply (rule finite_imageD) using subset_inj_on[OF padr_inj A'] pre by auto
      show "finite B'"
        apply (rule finite_imageD) using subset_inj_on[OF padl_inj B'] pre by auto
    qed
    have "\<zero>\<^sub>v n \<notin> A" using N.zero_nin_lin_indpt[OF _ liA] A N.one_zeroI by auto
    hence "?A \<inter> ?B = {}" using pad_disjoint A B by auto
    hence disj: "?UA \<inter> ?UB = {}" by auto
    have split: "U = padr m ` A' \<union> padl n ` B'"
      unfolding UAA'[symmetric] UBB'[symmetric] using UAB by auto
    show "f u = \<zero>\<^bsub>K\<^esub>"
    proof -
      let ?a = "f \<circ> padr m"
      let ?b = "f \<circ> padl n"
  
      have a': "?a : A' \<rightarrow> carrier K" by auto
      hence lcA': "lincomb n ?a A' : carrier\<^sub>v n" using N.lincomb_closed A' by auto
      have b': "?b : B' \<rightarrow> carrier K" by auto
      hence lcB': "lincomb m ?b B' : carrier\<^sub>v m" using M.lincomb_closed B' by auto
  
      have "\<zero>\<^sub>v n @\<^sub>v \<zero>\<^sub>v m = \<zero>\<^sub>v (n+m)" by auto
      also have "... = lincomb (n+m) f U" using 0 by auto
      also have "U = ?UA \<union> ?UB" using UAB by auto
      also have "lincomb (n+m) f ... = lincomb (n+m) f ?UA \<oplus>\<^sub>v lincomb (n+m) f ?UB"
        apply(subst NM.lincomb_union) using A B finU disj by auto
      also have "lincomb (n+m) f ?UA = lincomb (n+m) (restrict f ?UA) ?UA"
        apply (subst NM.lincomb_restrict) using A finU by auto
      also have "restrict f ?UA = restrict (?a \<circ> unpadr m) ?UA"
        apply(rule restrict_ext) by auto
      also have "lincomb (n+m) ... ?UA = lincomb (n+m) (?a \<circ> unpadr m) ?UA"
        apply(subst NM.lincomb_restrict) using A finU by auto
      also have "?UA = padr m ` A'" using UAA'.
      also have "lincomb (n+m) (?a \<circ> unpadr m) ... =
        padr m (lincomb n ?a A')"
        using lincomb_pad(1)[OF A' finA',symmetric].
      also have "lincomb (n+m) f ?UB = lincomb (n+m) (restrict f ?UB) ?UB"
        apply (subst NM.lincomb_restrict) using B finU by auto
      also have "restrict f ?UB = restrict (?b \<circ> unpadl n) ?UB"
        apply(rule restrict_ext) by auto
      also have "lincomb (n+m) ... ?UB = lincomb (n+m) (?b \<circ> unpadl n) ?UB"
        apply(subst NM.lincomb_restrict) using B finU by auto
      also have "n+m = m+n" by auto
      also have "?UB = padl n ` B'" using UBB'.
      also have "lincomb (m+n) (?b \<circ> unpadl n) ... =
        padl n (lincomb m ?b B')"
        using lincomb_pad(2)[OF B' finB',symmetric].
      also have "padr m (lincomb n ?a A') \<oplus>\<^sub>v ... =
          (lincomb n ?a A' \<oplus>\<^sub>v \<zero>\<^sub>v n) @\<^sub>v (\<zero>\<^sub>v m \<oplus>\<^sub>v lincomb m ?b B')"
        apply (rule vec_append_add) using lcA' lcB' by auto
      also have "... = lincomb n ?a A' @\<^sub>v lincomb m ?b B'" using lcA' lcB' by auto
      finally have "\<zero>\<^sub>v n @\<^sub>v \<zero>\<^sub>v m = lincomb n ?a A' @\<^sub>v lincomb m ?b B'".
      hence "\<zero>\<^sub>v n = lincomb n ?a A' \<and> \<zero>\<^sub>v m = lincomb m ?b B'"
        apply(subst vec_append_eq[symmetric]) using lcA' lcB' by auto
      from conjunct1[OF this] conjunct2[OF this]
      have "?a : A' \<rightarrow> {0}" "?b : B' \<rightarrow> {0}"
        using N.not_lindepD[OF liA finA' A'A a']
        using M.not_lindepD[OF liB finB' B'B b'] by auto
      hence "f : padr m ` A' \<rightarrow> {0}" "f : padl n ` B' \<rightarrow> {0}" by auto
      hence "f : padr m ` A' \<union> padl n ` B' \<rightarrow> {0}" by auto
      hence "f : U \<rightarrow> {0}" using split by auto
      hence "f u = 0" using uU by auto
      thus ?thesis by simp
    qed
  qed
qed

end

lemma kernel_four_block_0_mat:
  assumes Adef: "(A :: 'a::field mat) = four_block_mat B (\<zero>\<^sub>m n m) (\<zero>\<^sub>m m n) D"
  and B: "B \<in> carrier\<^sub>m n n"
  and D: "D \<in> carrier\<^sub>m m m"
  shows "kernel.dim (n + m) A = kernel.dim n B + kernel.dim m D"
proof -
  have [simp]: "n + m = m + n" by auto
  have A: "A \<in> carrier\<^sub>m (n+m) (n+m)"
    using Adef four_block_mat_carrier[OF B D] by auto
  interpret vardim "TYPE('a)".
  interpret MN: vectorspace "K" "M (n+m)" using vec_vs.
  interpret KA: kernel "n+m" "n+m" A by (unfold_locales, rule A)
  interpret KB: kernel n n B by (unfold_locales, rule B)
  interpret KD: kernel m m D by (unfold_locales, rule D)

  note [simp] = vec_module_simps

  from kernel_basis_exists[OF B]
    obtain baseB where fin_bB: "finite baseB" and bB: "KB.basis baseB" by blast
  hence bBkB: "baseB \<subseteq> mat_kernel B" unfolding KB.Ker.basis_def by auto
  hence bBc: "baseB \<subseteq> carrier\<^sub>v n" using mat_kernel_carrier[OF B] by auto
  have bB0: "\<zero>\<^sub>v n \<notin> baseB"
    using bB unfolding KB.Ker.basis_def
    using KB.Ker.vs_zero_lin_dep[OF bBkB] by auto
  have bBkA: "padr m ` baseB \<subseteq> mat_kernel A"
  proof
    fix a assume "a : padr m ` baseB"
    then obtain b where ab: "a = padr m b" and "b : baseB" by auto
    hence "b : mat_kernel B" using bB unfolding KB.Ker.basis_def by auto
    hence "padr m b : mat_kernel A"
      unfolding Adef using kernel_padr[OF _ B _ D] by auto
    thus "a : mat_kernel A" using ab by auto
  qed
  from kernel_basis_exists[OF D]
    obtain baseD where fin_bD: "finite baseD" and bD: "KD.basis baseD" by blast
  hence bDkD: "baseD \<subseteq> mat_kernel D" unfolding KD.Ker.basis_def by auto
  hence bDc: "baseD \<subseteq> carrier\<^sub>v m" using mat_kernel_carrier[OF D] by auto
  have bDkA: "padl n ` baseD \<subseteq> mat_kernel A"
  proof
    fix a assume "a : padl n ` baseD"
    then obtain d where ad: "a = padl n d" and "d : baseD" by auto
    hence "d : mat_kernel D" using bD unfolding KD.Ker.basis_def by auto
    hence "padl n d : mat_kernel A"
      unfolding Adef using kernel_padl[OF _ B _ D] by auto
    thus "a : mat_kernel A" using ad by auto
  qed
  let ?BD = "(padr m ` baseB \<union> padl n ` baseD)"
  have finBD: "finite ?BD" using fin_bB fin_bD by auto
  have "KA.basis  ?BD"
    unfolding KA.Ker.basis_def
  proof (intro conjI Set.equalityI)
    show BDk: "?BD \<subseteq> mat_kernel A" using bBkA bDkA by auto
    also have "mat_kernel A \<subseteq> carrier\<^sub>v (m+n)" using mat_kernel_carrier A by auto
    finally have BD: "?BD \<subseteq> carrier (M (n + m))" by auto
    show "mat_kernel A \<subseteq> KA.VKMod.span ?BD"
      unfolding KA.span_same[OF BDk]
    proof
      have BD: "?BD \<subseteq> carrier\<^sub>v (n+m)" (is "_ \<subseteq> ?R")
      proof(rule)
        fix v assume "v : ?BD"
        moreover
        { assume "v : padr m ` baseB"
          then obtain b where "b : baseB" and vb: "v = padr m b" by auto
          hence "b : carrier\<^sub>v n" using bBc by auto
          hence "v : ?R" unfolding vb apply(subst vec_append_carrier) by auto
        }
        moreover
        { assume "v : padl n ` baseD"
          then obtain d where "d : baseD" and vd: "v = padl n d" by auto
          hence "d : carrier\<^sub>v m" using bDc by auto
          hence "v : ?R" unfolding vd apply(subst vec_append_carrier) by auto
        }
        ultimately show "v: ?R" by auto
      qed
      fix a assume a: "a : mat_kernel A"
      hence "a : carrier\<^sub>v (n+m)" using a mat_kernel_carrier[OF A] by auto
      hence "a = vec_first a n @\<^sub>v vec_last a m" (is "_ = ?b @\<^sub>v ?d") by simp
      also have "... = padr m ?b \<oplus>\<^sub>v padl n ?d" by auto
      finally have 1: "a = padr m ?b \<oplus>\<^sub>v padl n ?d".
  
      have subkernel: "?b : mat_kernel B" "?d : mat_kernel D"
        using mat_kernel_split[OF B D] a Adef by auto
      hence "?b : span n baseB"
        using bB unfolding KB.Ker.basis_def using KB.span_same by auto
      hence "padr m ?b : padr m ` span n baseB" by auto
      also have "padr m ` span n baseB = span (n+m) (padr m ` baseB)"
        using span_pad[OF bBc] by auto
      also have "... \<subseteq> span (n+m) ?BD" using MN.span_is_monotone by auto
      finally have 2: "padr m ?b : span (n+m) ?BD".
      have "?d : span m baseD"
        using subkernel bD unfolding KD.Ker.basis_def using KD.span_same by auto
      hence "padl n ?d : padl n ` span m baseD" by auto
      also have "padl n ` span m baseD = span (n+m) (padl n ` baseD)"
        using span_pad[OF bDc] by auto
      also have "... \<subseteq> span (n+m) ?BD" using MN.span_is_monotone by auto
      finally have 3: "padl n ?d : span (n+m) ?BD".
  
      have "padr m ?b \<oplus>\<^sub>v padl n ?d : span (n+m) ?BD"
        using MN.span_add1[OF _ 2 3] BD by auto
      thus "a \<in> span (n+m) ?BD" using 1 by auto
    qed
    show "KA.VKMod.span ?BD \<subseteq> mat_kernel A" using KA.Ker.span_closed[OF BDk] by auto
    have li: "~ lin_dep n baseB" "~ lin_dep m baseD"
      using bB[unfolded KB.Ker.basis_def]
      unfolding KB.lindep_same[OF bBkB]
      using bD[unfolded KD.Ker.basis_def]
      unfolding KD.lindep_same[OF bDkD] by auto
    show "~ KA.VKMod.lin_dep ?BD"
      unfolding KA.lindep_same[OF BDk]
      apply(rule padr_padl_lindep) using bBc bDc li by auto
  qed
  hence "KA.dim = card ?BD" using KA.Ker.dim_basis[OF finBD] by auto
  also have "card ?BD = card (padr m ` baseB) + card (padl n ` baseD)"
    apply(rule card_Un_disjoint)
    using pad_disjoint[OF bBc bB0 bDc] fin_bB fin_bD by auto
  also have "... = card baseB + card baseD"
    using card_image[OF subset_inj_on[OF padr_inj]]
    using card_image[OF subset_inj_on[OF padl_inj]] bBc bDc by auto
  also have "card baseB = KB.dim" using KB.Ker.dim_basis[OF fin_bB] bB by auto
  also have "card baseD = KD.dim" using KD.Ker.dim_basis[OF fin_bD] bD by auto
  finally show ?thesis.

qed

lemma mat_similar_wit_kernel_dim: assumes A: "A \<in> carrier\<^sub>m n n"
  and wit: "mat_similar_wit A B P Q"
  shows "kernel.dim n A = kernel.dim n B"
proof -
  from mat_similar_witD2[OF A wit]
  have QP: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" and AB: "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" and 
    A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n n" and P: "P \<in> carrier\<^sub>m n n" and Q: "Q \<in> carrier\<^sub>m n n" by auto
  from P B have PB: "P \<otimes>\<^sub>m B \<in> carrier\<^sub>m n n" by auto
  show ?thesis unfolding AB mat_kernel_dim_mult_eq_right[OF PB Q P QP] mat_kernel_mult_eq[OF B P Q QP]
    by simp
qed


end