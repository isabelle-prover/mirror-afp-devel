(*
    Authors:    René Thiemann
                BSD
*)

section \<open>Certification of External LLL Invocations\<close>

text \<open>Instead of using a fully verified algorithm, we also provide a technique to invoke
an external LLL solver. In order to check its result, we not only need the reduced basic,
but also the matrices which translate between the input basis and the reduced basis. 
Then we can easily check whether the resulting lattices are indeed identical and just have
to start the verified algorithm on the already reduced basis.
This invocation will then usually just require one computation of Gram--Schmidt in order
to check that the basis is already reduced. Alternatively, one could also through an error
message in case the basis is not reduced.\<close>

theory LLL_Certification
  imports
    LLL_Mu_Integer_Impl
begin

context vec_module
begin

lemma mat_mult_sub_lattice: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and gs: "set gs \<subseteq> carrier_vec n" 
  and A: "A \<in> carrier_mat (length fs) (length gs)" 
  and prod: "mat_of_rows n fs = map_mat of_int A * mat_of_rows n gs" 
  shows "lattice_of fs \<subseteq> lattice_of gs" 
proof 
  let ?m = "length fs"
  let ?m' = "length gs" 
  let ?i = "of_int :: int \<Rightarrow> 'a" 
  let ?I = "map_mat ?i" 
  let ?A = "?I A" 
  have gsC: "mat_of_rows n gs \<in> carrier_mat ?m' n" by auto
  from A have A: "?A \<in> carrier_mat ?m ?m'" by auto
  from fs have fsi[simp]: "\<And> i. i < ?m \<Longrightarrow> fs ! i \<in> carrier_vec n" by auto
  hence fsi'[simp]: "\<And> i. i < ?m \<Longrightarrow> dim_vec (fs ! i) = n" by simp
  from gs have fsi[simp]: "\<And> i. i < ?m' \<Longrightarrow> gs ! i \<in> carrier_vec n" by auto
  hence gsi'[simp]: "\<And> i. i < ?m' \<Longrightarrow> dim_vec (gs ! i) = n" by simp
  fix v
  assume "v \<in> lattice_of fs" 
  from in_latticeE[OF this]
  obtain c where v: "v = M.sumlist (map (\<lambda>i. ?i (c i) \<cdot>\<^sub>v fs ! i) [0..<?m])" by auto
  let ?c = "vec ?m (\<lambda> i. ?i (c i))" 
  let ?d = "A\<^sup>T *\<^sub>v vec ?m c" 
  note v
  also have "\<dots> = mat_of_cols n fs *\<^sub>v ?c" 
    by (rule eq_vecI, auto intro!: dim_sumlist sum.cong 
      simp: sumlist_nth scalar_prod_def mat_of_cols_def)
  also have "mat_of_cols n fs = (mat_of_rows n fs)\<^sup>T" 
    by (simp add: transpose_mat_of_rows)
  also have "\<dots> = (?A * mat_of_rows n gs)\<^sup>T" unfolding prod ..
  also have "\<dots> = (mat_of_rows n gs)\<^sup>T * ?A\<^sup>T" 
    by (rule transpose_mult[OF A gsC])
  also have "(mat_of_rows n gs)\<^sup>T = mat_of_cols n gs" 
    by (simp add: transpose_mat_of_rows)
  finally have "v = (mat_of_cols n gs * ?A\<^sup>T) *\<^sub>v ?c" .
  also have "\<dots> = mat_of_cols n gs *\<^sub>v (?A\<^sup>T *\<^sub>v ?c)" 
    by (rule assoc_mult_mat_vec, insert A, auto)
  also have "?A\<^sup>T = ?I (A\<^sup>T)" by fastforce
  also have "?c = map_vec ?i (vec ?m c)" by auto
  also have "?I (A\<^sup>T) *\<^sub>v \<dots> = map_vec ?i ?d" 
    using A by (simp add: of_int_hom.mult_mat_vec_hom)
  finally have "v = mat_of_cols n gs *\<^sub>v map_vec ?i ?d" .
  define d where "d = ?d" 
  have d: "d \<in> carrier_vec ?m'" unfolding d_def using A by auto
  have "v = mat_of_cols n gs *\<^sub>v map_vec ?i d" unfolding d_def by fact
  also have "\<dots> =  M.sumlist (map (\<lambda>i. ?i (d $ i) \<cdot>\<^sub>v gs ! i) [0..<?m'])" 
    by (rule sym, rule eq_vecI, insert d, auto intro!: dim_sumlist sum.cong 
      simp: sumlist_nth scalar_prod_def mat_of_cols_def)
  finally show "v \<in> lattice_of gs" 
    by (intro in_latticeI, auto)
qed
end

context LLL_with_assms
begin

text \<open>This is the key lemma. It permits to change from the initial basis
@{term fs_init} to an arbitrary @{term gs} that has been computed by some
external tool. Here, two change-of-basis matrices U1 and U2 are required 
to certify the change via the conditions prod1 and prod2.\<close>

lemma LLL_change_basis: assumes gs: "set gs \<subseteq> carrier_vec n" 
  and len': "length gs = m" 
  and U1: "U1 \<in> carrier_mat m m" 
  and U2: "U2 \<in> carrier_mat m m" 
  and prod1: "mat_of_rows n fs_init = U1 * mat_of_rows n gs" 
  and prod2: "mat_of_rows n gs = U2 * mat_of_rows n fs_init" 
  and missing: False
shows "lattice_of gs = lattice_of fs_init" "LLL_with_assms n m gs \<alpha>" 
proof -
  let ?i = "of_int :: int \<Rightarrow> int" 
  have "U1 = map_mat ?i U1" by (intro eq_matI, auto)
  with prod1 have prod1: "mat_of_rows n fs_init = map_mat ?i U1 * mat_of_rows n gs" by simp
  have "U2 = map_mat ?i U2" by (intro eq_matI, auto)
  with prod2 have prod2: "mat_of_rows n gs = map_mat ?i U2 * mat_of_rows n fs_init" by simp
  have "lattice_of gs \<subseteq> lattice_of fs_init" 
    by (rule mat_mult_sub_lattice[OF gs fs_init _ prod2], auto simp: U2 len len')
  moreover have "lattice_of gs \<supseteq> lattice_of fs_init"
    by (rule mat_mult_sub_lattice[OF fs_init gs _ prod1], auto simp: U1 len len')
  ultimately show "lattice_of gs = lattice_of fs_init" by blast
  show "LLL_with_assms n m gs \<alpha>"
  proof
    show "4/3 \<le> \<alpha>" by (rule \<alpha>)
    show "length gs = m" by fact
    show "lin_indep gs" using lin_dep missing by auto
    text \<open>TODO: continue without missing\<close>
  qed
qed
end

consts lll_oracle :: "integer list list \<Rightarrow> (integer list list \<times> integer list list \<times> integer list list) option" 

definition short_vector_external :: "rat \<Rightarrow> int vec list \<Rightarrow> int vec" where
  "short_vector_external \<alpha> fs = (let sv = short_vector \<alpha>;
    fsi = map (map integer_of_int o list_of_vec) fs;
    n = dim_vec (hd fs);
    m = length fs in 
  case lll_oracle fsi of 
    None \<Rightarrow> sv fs
  | Some (gsi, u1i, u2i) \<Rightarrow> let 
     u1 = mat_of_rows_list m (map (map int_of_integer) u1i);
     u2 = mat_of_rows_list m (map (map int_of_integer) u2i);
     gs = (map (vec_of_list o map int_of_integer) gsi);
     Fs = mat_of_rows n fs;
     Gs = mat_of_rows n gs in 
     if (dim_row u1 = m \<and> dim_col u1 = m \<and> dim_row u2 = m \<and> dim_col u2 = m 
         \<and> length gs = m \<and> Fs = u1 * Gs \<and> Gs = u2 * Fs \<and> (\<forall> gi \<in> set gs. dim_vec gi = n))
      then sv gs
      else Code.abort (STR ''error in external lll invocation'') (\<lambda> _. sv fs))" 

instance bool :: prime_card
  by (standard, auto)


context LLL_with_assms
begin

lemma short_vector_external: assumes res: "short_vector_external \<alpha> fs_init = v"
  and m0: "m \<noteq> 0"
  and missing: False
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)"
  "v \<noteq> 0\<^sub>v j"
proof (atomize(full), goal_cases)
  case 1
  show ?case
  proof (cases "short_vector \<alpha> fs_init = v")
    case True
    from short_vector[OF True m0] show ?thesis by auto
  next
    case False
    from m0 fs_init len have dim_fs_n: "dim_vec (hd fs_init) = n" by (cases fs_init, auto)
    let ?ext = "lll_oracle (map (map integer_of_int \<circ> list_of_vec) fs_init)" 
    note res = res[unfolded short_vector_external_def Let_def Code.abort_def]
    from res False obtain gsi u1i u2i where ext: "?ext = Some (gsi, u1i, u2i)" by (cases ?ext, auto)
    define u1 where "u1 = mat_of_rows_list m (map (map int_of_integer) u1i)"
    define u2 where "u2 = mat_of_rows_list m (map (map int_of_integer) u2i)" 
    define gs where "gs = map (vec_of_list o map int_of_integer) gsi" 
    note res = res[unfolded ext option.simps split len dim_fs_n, folded u1_def u2_def gs_def]
    from res False 
    have u1: "u1 \<in> carrier_mat m m" 
      and u2: "u2 \<in> carrier_mat m m" 
      and len_gs: "length gs = m" 
      and prod1: "mat_of_rows n fs_init = u1 * mat_of_rows n gs" 
      and prod2: "mat_of_rows n gs = u2 * mat_of_rows n fs_init" 
      and gs_v: "short_vector \<alpha> gs = v" 
      and gs: "set gs \<subseteq> carrier_vec n" 
      by (auto split: if_splits)
    from LLL_change_basis[OF gs len_gs u1 u2 prod1 prod2 missing]
    have id: "lattice_of gs = lattice_of fs_init" 
      and assms: "LLL_with_assms n m gs \<alpha>" by auto
    from LLL_with_assms.short_vector[OF assms gs_v m0]
    show ?thesis using id by (simp add: LLL.L_def)
  qed
qed

end

code_printing
  code_module "LLL_Extern" \<rightharpoonup> (Haskell) \<open>
  import Prelude (Maybe(Nothing, Just), Integer);
  import External_LLL (external_lll);

  lll_extern :: [[Integer]] -> Maybe ([[Integer]], [[Integer]], [[Integer]]);
  lll_extern fs = Just (external_lll fs);\<close>

code_reserved Haskell LLL_Extern External_LLL lll_extern external_lll

code_printing
 constant lll_oracle \<rightharpoonup> (Haskell) "LLL'_Extern.lll'_extern"

(* export_code short_vector_external in Haskell module_name LLL file "~/Code" *)

end
