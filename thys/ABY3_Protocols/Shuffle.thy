theory Shuffle
  imports 
    CryptHOL.CryptHOL
    Additive_Sharing
    Spmf_Common
    Sharing_Lemmas
begin

text \<open>
This is the formalization of the array shuffling protocol defined in \cite{laud2016secure}
adapted for the ABY3 sharing scheme.
For the moment, we assume an oracle that generates uniformly distributed permutations,
instead of instantiating it with e.g. Fischer-Yates algorithm.
\<close>

no_notation (ASCII) comp  (infixl "o" 55)
no_notation m_inv ("inv\<index> _" [81] 80)

no_adhoc_overloading Monad_Syntax.bind bind_pmf

fun shuffleF :: "natL sharing list \<Rightarrow> natL sharing list spmf" where
  "shuffleF xsl = spmf_of_set (permutations_of_multiset (mset xsl))"

type_synonym zero_sharing = "natL sharing list"
type_synonym party2_data = "natL list"
type_synonym party01_permutation = "nat \<Rightarrow> nat"
type_synonym phase_msg = "zero_sharing \<times> party2_data \<times> party01_permutation"

type_synonym role_msg = "(natL list \<times> natL list \<times> natL list) \<times> party2_data \<times> (party01_permutation \<times> party01_permutation)"

(* (a, b, c) \<rightarrow> (a, b+c, 0) *)
definition aby3_stack_sharing :: "Role \<Rightarrow> natL sharing \<Rightarrow> natL sharing" where
  "aby3_stack_sharing r s = make_sharing' r (next_role r) (prev_role r)
                             (get_party r s)
                             (get_party (next_role r) s + get_party (prev_role r) s)
                             0"

(* one permutation step *)
definition aby3_do_permute :: "Role \<Rightarrow> natL sharing list \<Rightarrow> (phase_msg \<times> natL sharing list) spmf" where
  "aby3_do_permute r x = (do {
    let n = length x;
    \<zeta> \<leftarrow> sequence_spmf (replicate n zero_sharing);
    \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
    let x2 = map (get_party (prev_role r)) x;
    let y' = map (aby3_stack_sharing r) x;
    let y = map2 (map_sharing2 (+)) (permute_list \<pi> y') \<zeta>;
    let msg = (\<zeta>, x2, \<pi>);
    return_spmf (msg, y)
  })"

(* the shuffling protocol, consisting of three shuffling steps *)
definition aby3_shuffleR :: "natL sharing list \<Rightarrow> (role_msg sharing \<times> natL sharing list) spmf" where
  "aby3_shuffleR x = (do {
    ((\<zeta>a,x',\<pi>a), a) \<leftarrow> aby3_do_permute Party1 x;     \<comment> \<open>1st round\<close>
    ((\<zeta>b,a',\<pi>b), b) \<leftarrow> aby3_do_permute Party2 a;     \<comment> \<open>2nd round\<close>
    ((\<zeta>c,b',\<pi>c), c) \<leftarrow> aby3_do_permute Party3 b;     \<comment> \<open>3rd round\<close>
    let msg1 = ((map (get_party Party1) \<zeta>a, map (get_party Party1) \<zeta>b, map (get_party Party1) \<zeta>c), b', \<pi>a, \<pi>c);
    let msg2 = ((map (get_party Party2) \<zeta>a, map (get_party Party2) \<zeta>b, map (get_party Party2) \<zeta>c), x', \<pi>a, \<pi>b);
    let msg3 = ((map (get_party Party3) \<zeta>a, map (get_party Party3) \<zeta>b, map (get_party Party3) \<zeta>c), a', \<pi>b, \<pi>c);
    let msg = make_sharing msg1 msg2 msg3;
    return_spmf (msg, c)
  })"


(* the ideal functionality of shuffling *)
definition aby3_shuffleF :: "natL sharing list \<Rightarrow> natL sharing list spmf" where
  "aby3_shuffleF x = (do {
    \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<length x}};
    let x1 = map reconstruct x;
    let x\<pi> = permute_list \<pi> x1;
    y \<leftarrow> sequence_spmf (map share_nat x\<pi>);
    return_spmf y
  })"

(* the simulator for party 1 *)
definition S1 :: "natL list \<Rightarrow> natL list \<Rightarrow> role_msg spmf" where
    "S1 x1 yc1 = (do {
       let n = length x1;

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         ya1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         yb1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         yb2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) ya1 (permute_list \<pi>a x1);

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = yb1;

\<comment> \<open>round 3\<close>
         let b' = yb2;
         let \<zeta>c1 = map2 (-) (yc1) (permute_list \<pi>c (map2 (+) yb1 yb2));  \<comment> \<open>non-free message\<close>

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf msg1
    })"

(* the simulator for party 2 *)
definition S2 :: "natL list \<Rightarrow> natL list \<Rightarrow> role_msg spmf" where
    "S2 x2 yc2 = (do {
       let n = length x2;
       x3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         ya2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         yb2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

\<comment> \<open>round 1\<close>
         let x' = x3;
         let \<zeta>a2 = map2 (-) ya2 (permute_list \<pi>a (map2 (+) x2 x3));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) yb2 (permute_list \<pi>b ya2);

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = yc2;  \<comment> \<open>non-free message\<close>

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf msg2
    })"

(* the simulator for party 3 *)
definition S3 :: "natL list \<Rightarrow> natL list \<Rightarrow> role_msg spmf" where
    "S3 x3 yc3 = (do {
       let n = length x3;

         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         ya3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         ya1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         yb3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = ya3;

\<comment> \<open>round 2\<close>
         let a' = ya1;
         let \<zeta>b3 = map2 (-) yb3 (permute_list \<pi>b (map2 (+) ya3 ya1));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) yc3 (permute_list \<pi>c yb3);  \<comment> \<open>non-free message\<close>

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf msg3

    })"

definition S :: "Role \<Rightarrow> natL list \<Rightarrow> natL list \<Rightarrow> role_msg spmf" where
  "S r = get_party r (make_sharing S1 S2 S3)"
  
definition is_uniform_sharing_list :: "natL sharing list spmf \<Rightarrow> bool" where
  "is_uniform_sharing_list xss \<longleftrightarrow> (\<exists>xs. xss = bind_spmf xs (sequence_spmf \<circ> map share_nat))"

lemma case_prod_nesting_same:
  "case_prod (\<lambda>a b. f (case_prod g x) a b ) x = case_prod (\<lambda>a b. f (g a b) a b ) x"
  by (cases x) simp

lemma zip_map_map_same:
  "map (\<lambda>x. (f x, g x)) xs = zip (map f xs) (map g xs)"
  unfolding zip_map_map
  unfolding zip_same_conv_map
  by simp

lemma dup_map_eq:
  "length xs = length ys \<Longrightarrow> (xs, map2 f ys xs) = (\<lambda>xys. (map fst xys, map snd xys)) (map2 (\<lambda>x y. (y, f x y)) ys xs)"
  by (auto simp: map_snd_zip[unfolded snd_def])


abbreviation "map2_spmf f xs ys \<equiv> map_spmf (case_prod f) (pair_spmf xs ys)"
abbreviation "map3_spmf f xs ys zs \<equiv> map2_spmf (\<lambda>a. case_prod (f a)) xs (pair_spmf ys zs)"

lemma map_spmf_cong2:
  assumes "p = map_spmf m q" "\<And>x. x\<in>set_spmf q \<Longrightarrow> f (m x) = g x"
  shows "map_spmf f p = map_spmf g q"
  using assms by (simp add: spmf.map_comp cong: map_spmf_cong)

lemma bind_spmf_cong2:
  assumes "p = map_spmf m q" "\<And>x. x\<in>set_spmf q \<Longrightarrow> f (m x) = g x"
  shows "bind_spmf p f = bind_spmf q g"
  using assms by (simp add: map_spmf_conv_bind_spmf cong: bind_spmf_cong)

lemma map2_spmf_map2_sequence:
  "length xss = length yss \<Longrightarrow> map2_spmf (map2 f) (sequence_spmf xss) (sequence_spmf yss) = sequence_spmf (map2 (map2_spmf f) xss yss)"
  apply (induction xss yss rule: list_induct2)
  subgoal by simp
  subgoal premises IH for x xs y ys
    apply simp
    apply (fold IH)
    apply (unfold pair_map_spmf)
    apply (unfold spmf.map_comp)
    apply (rule map_spmf_cong2[where m="\<lambda>((x,y),(xs,ys)). ((x,xs),(y,ys))"])
    subgoal 
      unfolding pair_spmf_alt_def
      apply (simp add: map_spmf_conv_bind_spmf)
      apply (subst bind_commute_spmf[where q=y])
      ..
    subgoal by auto
    done
  done

abbreviation map3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list" where
  "map3 f a b c \<equiv> map2 (\<lambda>a (b,c). f a b c) a (zip b c)"

lemma map3_spmf_map3_sequence:
  "length xss = length yss \<Longrightarrow> length yss = length zss \<Longrightarrow> map3_spmf (map3 f) (sequence_spmf xss) (sequence_spmf yss) (sequence_spmf zss) = sequence_spmf (map3 (map3_spmf f) xss yss zss)"
  apply (induction xss yss zss rule: list_induct3)
  subgoal by simp
  subgoal premises IH for x xs y ys z zs
    apply simp
    apply (fold IH)
    apply (unfold pair_map_spmf)
    apply (unfold spmf.map_comp)
    apply (rule map_spmf_cong2[where m="\<lambda>((x,y,z),(xs,ys,zs)). ((x,xs),(y,ys),(z,zs))"])
    subgoal 
      unfolding pair_spmf_alt_def
      apply (simp add: map_spmf_conv_bind_spmf)
      apply (subst bind_commute_spmf[where q=y])
      apply (subst bind_commute_spmf[where q=z])
      apply (subst bind_commute_spmf[where q=z])
      ..
    subgoal by auto
    done
  done


lemma in_pairD2:
  "x \<in> A \<times> B \<Longrightarrow> snd x \<in> B"
  by auto

lemma list_map_cong2:
  "x = map m y \<Longrightarrow> (\<And>z. z\<in>set y =simp=> f (m z) = g z) \<Longrightarrow> map f x = map g y"
  unfolding simp_implies_def
  by simp

lemma map_swap_zip:
  "map prod.swap (zip xs ys) = zip ys xs"
  apply (induction xs arbitrary: ys)
  subgoal by simp
  subgoal for x xs ys
    by (cases ys) auto
  done

lemma inv_zero_sharing_sequence:
  "n = length x \<Longrightarrow>
   map_spmf (\<lambda>\<zeta>s. (\<zeta>s, map2 (map_sharing2 (+)) x \<zeta>s)) (sequence_spmf (replicate n zero_sharing))
   =
   map_spmf (\<lambda>ys. (map2 (map_sharing2 (-)) ys x, ys)) (sequence_spmf (map (share_nat \<circ>reconstruct) x))"
proof -
  assume n: "n = length x"
  have "map_spmf (\<lambda>\<zeta>s. (\<zeta>s, map2 (map_sharing2 (+)) x \<zeta>s)) (sequence_spmf (replicate n zero_sharing))
=
map2_spmf (\<lambda>\<zeta>s x. (\<zeta>s, map2 (map_sharing2 (+)) x \<zeta>s)) (sequence_spmf (replicate n zero_sharing)) (sequence_spmf (map return_spmf x))"
    unfolding sequence_map_return_spmf
    apply (rule map_spmf_cong2[where m="fst"])
    subgoal by simp
    subgoal by (auto simp: case_prod_unfold dest: in_pairD2)
    done

  also have "... = map_spmf (\<lambda>\<zeta>xs. (map fst \<zeta>xs, map snd \<zeta>xs)) (map2_spmf (map2 (\<lambda>\<zeta> x. (\<zeta>, map_sharing2 (+) x \<zeta>))) (sequence_spmf (replicate n zero_sharing)) (sequence_spmf (map return_spmf x)))"
    apply (unfold spmf.map_comp)
    apply (rule map_spmf_cong[OF refl])
    using n by (auto simp: case_prod_unfold comp_def set_sequence_spmf list_all2_iff map_swap_zip intro: list_map_cong2[where m=prod.swap])

  also have "... = map_spmf (\<lambda>\<zeta>xs. (map fst \<zeta>xs, map snd \<zeta>xs)) (map2_spmf (map2 (\<lambda>y x. (map_sharing2 (-) y x, y))) (sequence_spmf (map (share_nat \<circ> reconstruct) x)) (sequence_spmf (map return_spmf x)))"
    apply (rule arg_cong[where f="map_spmf _"])
    using n     apply (simp add: map2_spmf_map2_sequence)
    apply (rule arg_cong[where f=sequence_spmf])
    apply (unfold list_eq_iff_nth_eq)
    apply safe
    subgoal by simp
    apply (simp add: )
    apply (subst map_spmf_cong2[where p="pair_spmf _ (return_spmf _)"])
      apply (rule pair_spmf_return_spmf2)
     apply simp
    apply (subst map_spmf_cong2[where p="pair_spmf _ (return_spmf _)"])
      apply (rule pair_spmf_return_spmf2)
     apply simp
    using inv_zero_sharing .

  also have "... = map2_spmf (\<lambda>ys x. (map2 (map_sharing2 (-)) ys x, ys)) (sequence_spmf (map (share_nat \<circ>reconstruct) x)) (sequence_spmf (map return_spmf x))"
    apply (unfold spmf.map_comp)
    apply (rule map_spmf_cong[OF refl])
    using n by (auto simp: case_prod_unfold comp_def set_sequence_spmf list_all2_iff map_swap_zip intro: list_map_cong2[where m=prod.swap])

  also have "... = map_spmf (\<lambda>ys. (map2 (map_sharing2 (-)) ys x, ys)) (sequence_spmf (map (share_nat \<circ>reconstruct) x))"
    unfolding sequence_map_return_spmf
    apply (rule map_spmf_cong2[where m="fst", symmetric])
    subgoal by simp
    subgoal by (auto simp: case_prod_unfold dest: in_pairD2)
    done

  finally show ?thesis .
qed

lemma get_party_map_sharing2:
  "get_party p \<circ> (case_prod (map_sharing2 f)) = case_prod f \<circ> map_prod (get_party p) (get_party p)"
  by auto

lemma map_map_prod_zip:
  "map (map_prod f g) (zip xs ys) = zip (map f xs) (map g ys)"
  by (simp add: map_prod_def zip_map_map)

lemma map_map_prod_zip':
  "map (h \<circ> map_prod f g) (zip xs ys) = map h (zip (map f xs) (map g ys))"
  by (simp add: map_prod_def zip_map_map)

lemma eq_map_spmf_conv:
  assumes "\<And>x. f (f' x) = x" "f' = inv f" "map_spmf f' x = y"
  shows "x = map_spmf f y"
proof -
  have surj: "surj f"
    apply (rule surjI) using assms(1) .
  have "map_spmf f (map_spmf f' x) = map_spmf f y"
    unfolding assms(3) ..
  thus ?thesis
    using assms(1) by (simp add: spmf.map_comp surj_iff comp_def)
qed


lemma lift_map_spmf_pairs:
  "map2_spmf f = F \<Longrightarrow> map_spmf (case_prod f) (pair_spmf A B) = F A B"
  by auto

lemma measure_pair_spmf_times':
    "C = A \<times> B \<Longrightarrow> measure (measure_spmf (pair_spmf p q)) C = measure (measure_spmf p) A * measure (measure_spmf q) B"
  by (simp add: measure_pair_spmf_times)

lemma map_spmf_pairs_tmp:
  "map_spmf (\<lambda>(a,b,c,d,e,f,g). (a,e,b,f,c,g,d)) (pair_spmf A (pair_spmf B (pair_spmf C (pair_spmf D (pair_spmf E (pair_spmf F G))))))
       = (pair_spmf A (pair_spmf E (pair_spmf B (pair_spmf F (pair_spmf C (pair_spmf G  D))))))"
  apply (rule spmf_eqI)
  apply (clarsimp simp add: spmf_map)
  subgoal for a e b f c g d
    apply (subst measure_pair_spmf_times'[where A="{a}"]) defer
    apply (subst measure_pair_spmf_times'[where A="{b}"]) defer
    apply (subst measure_pair_spmf_times'[where A="{c}"]) defer
    apply (subst measure_pair_spmf_times'[where A="{d}"]) defer
    apply (subst measure_pair_spmf_times'[where A="{e}"]) defer
         apply (subst measure_pair_spmf_times'[where A="{f}" and B="{g}"]) defer
          apply (auto simp: spmf_conv_measure_spmf)
    done
  done

lemma case_case_prods_tmp:
  "(case case x of (a, b, c, d, e, f, g) \<Rightarrow> (a, e, b, f, c, g, d) of
                (ya, yb, yc, yd, ye, yf, yg) \<Rightarrow> F ya yb yc yd ye yf yg)
      = (case x of (a,b,c,d,e,f,g) \<Rightarrow> F a e b f c g d)"
  by (cases x) simp

lemma bind_spmf_permutes_cong:
  "(\<And>\<pi>. \<pi> permutes {..<(x::nat)} \<Longrightarrow> f \<pi> = g \<pi>)
    \<Longrightarrow> bind_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<x}}) f = bind_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<x}}) g"
  by (rule bind_spmf_cong[OF refl]) (simp add: set_spmf_of_set finite_permutations set_sequence_spmf[unfolded list_all2_iff])

lemma map_eq_iff_list_all2:
  "map f xs = map g ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = g y) xs ys"
  apply (induction xs arbitrary: ys)
  subgoal by auto
  subgoal for x xs ys by (cases ys) (auto)
  done

lemma bind_spmf_sequence_map_share_nat_cong:
  "(\<And>l. map reconstruct l = x \<Longrightarrow> f l = g l)
    \<Longrightarrow> bind_spmf (sequence_spmf (map share_nat x)) f = bind_spmf (sequence_spmf (map share_nat x)) g"
  subgoal premises prems
    apply (rule bind_spmf_cong[OF refl])
    apply (rule prems)
    unfolding set_sequence_spmf mem_Collect_eq
    apply (simp add: map_eq_iff_list_all2[where g=id, simplified])
    apply (simp add: list_all2_map2)
    apply (erule list_all2_mono)
    unfolding share_nat_def
    by simp
  done

lemma map_reconstruct_comp_eq_iff:
  "(\<And>x. x\<in>set xs \<Longrightarrow> reconstruct (f x) = reconstruct x) \<Longrightarrow> map (reconstruct \<circ> f) xs = map reconstruct xs"
  by (induction xs) auto

lemma permute_list_replicate:
  "p permutes {..<n} \<Longrightarrow> permute_list p (replicate n x) = replicate n x"
  apply (fold map_replicate_const[where lst="[0..<n]", simplified])
  apply (simp add: permute_list_map)
  unfolding map_replicate_const
  by simp

lemma map2_minus_zero:
  "length xs = length ys \<Longrightarrow> (\<And>y::natL. y\<in>set ys \<Longrightarrow> y = 0) \<Longrightarrow> map2 (-) xs ys = xs"
  by (induction xs ys rule: list_induct2) auto

lemma permute_comp_left_inj:
  "p permutes {..<n} \<Longrightarrow> inj (\<lambda>p'. p \<circ> p')"
  by (rule fun.inj_map) (rule permutes_inj_on)

lemma permute_comp_left_inj_on:
  "p permutes {..<n} \<Longrightarrow> inj_on (\<lambda>p'. p \<circ> p') A"
  using permute_comp_left_inj inj_on_subset by blast

lemma permute_comp_right_inj:
  "p permutes {..<n} \<Longrightarrow> inj (\<lambda>p'. p' \<circ> p)"
  using inj_onI comp_id o_assoc permutes_surj surj_iff
  by (smt)

lemma permute_comp_right_inj_on:
  "p permutes {..<n} \<Longrightarrow> inj_on (\<lambda>p'. p' \<circ> p) A"
  using permute_comp_right_inj inj_on_subset by blast

lemma permutes_inv_comp_left:
  "p permutes {..<n} \<Longrightarrow> inv (\<lambda>p'. p \<circ> p') = (\<lambda>p'. inv p \<circ> p')"
  by (rule inv_unique_comp; rule ext, simp add: permutes_inv_o comp_assoc[symmetric])

lemma permutes_inv_comp_right:
  "p permutes {..<n} \<Longrightarrow> inv (\<lambda>p'. p' \<circ> p) = (\<lambda>p'. p' \<circ> inv p)"
  by (rule inv_unique_comp; rule ext, simp add: permutes_inv_o comp_assoc)

lemma permutes_inv_comp_left_right:
  "\<pi>a permutes {..<n} \<Longrightarrow> \<pi>b permutes {..<n} \<Longrightarrow> inv (\<lambda>p'. \<pi>a \<circ> p' \<circ> \<pi>b) = (\<lambda>p'. inv \<pi>a \<circ> p' \<circ> inv \<pi>b)"
  by (rule inv_unique_comp; rule ext, simp add: permutes_inv_o comp_assoc, simp add: permutes_inv_o comp_assoc[symmetric])

lemma permutes_inv_comp_left_left:
  "\<pi>a permutes {..<n} \<Longrightarrow> \<pi>b permutes {..<n} \<Longrightarrow> inv (\<lambda>p'. \<pi>a \<circ> \<pi>b \<circ> p') = (\<lambda>p'. inv \<pi>b \<circ> inv \<pi>a \<circ> p')"
  by (rule inv_unique_comp; rule ext, simp add: permutes_inv_o comp_assoc, simp add: permutes_inv_o comp_assoc[symmetric])

lemma permutes_inv_comp_right_right:
  "\<pi>a permutes {..<n} \<Longrightarrow> \<pi>b permutes {..<n} \<Longrightarrow> inv (\<lambda>p'. p' \<circ> \<pi>a \<circ>  \<pi>b) = (\<lambda>p'. p' \<circ> inv \<pi>b \<circ> inv \<pi>a)"
  by (rule inv_unique_comp; rule ext, simp add: permutes_inv_o comp_assoc, simp add: permutes_inv_o comp_assoc[symmetric])

lemma image_compose_permutations_left_right:
  fixes S
  assumes "\<pi>a permutes S" "\<pi>b permutes S"
  shows "{\<pi>a \<circ> \<pi> \<circ> \<pi>b |\<pi>. \<pi> permutes S} = {\<pi>. \<pi> permutes S}"
proof -
  have *: "(\<lambda>\<pi>. \<pi>a \<circ> \<pi> \<circ> \<pi>b) = (\<lambda>\<pi>'. \<pi>a \<circ> \<pi>') \<circ> (\<lambda>\<pi>. \<pi> \<circ> \<pi>b)"
    by (simp add: comp_def)
  then show ?thesis
    apply (fold image_Collect)
    apply (unfold *)
    apply (fold image_comp)
    apply (subst image_Collect)
    apply (unfold image_compose_permutations_right[OF assms(2)])
    apply (subst image_Collect)
    apply (unfold image_compose_permutations_left[OF assms(1)])
    ..
qed

lemma image_compose_permutations_left_left:
  fixes S
  assumes "\<pi>a permutes S" "\<pi>b permutes S"
  shows "{\<pi>a \<circ> \<pi>b \<circ> \<pi> |\<pi>. \<pi> permutes S} = {\<pi>. \<pi> permutes S}"
  using image_compose_permutations_left image_compose_permutations_right 
proof -
  have *: "(\<lambda>\<pi>. \<pi>a \<circ> \<pi>b \<circ> \<pi>) = (\<lambda>\<pi>'. \<pi>a \<circ> \<pi>') \<circ> (\<lambda>\<pi>. \<pi>b \<circ> \<pi>)"
    by (simp add: comp_def)
  show ?thesis
    apply (fold image_Collect)
    apply (unfold *)
    apply (fold image_comp)
    apply (subst image_Collect)
    apply (unfold image_compose_permutations_left[OF assms(2)])
    apply (subst image_Collect)
    apply (unfold image_compose_permutations_left[OF assms(1)])
    ..
qed

lemma image_compose_permutations_right_right:
  fixes S
  assumes "\<pi>a permutes S" "\<pi>b permutes S"
  shows "{\<pi> \<circ> \<pi>a \<circ> \<pi>b |\<pi>. \<pi> permutes S} = {\<pi>. \<pi> permutes S}"
  using image_compose_permutations_left image_compose_permutations_right 
proof -
  have *: "(\<lambda>\<pi>. \<pi> \<circ> \<pi>a \<circ> \<pi>b) = (\<lambda>\<pi>. \<pi> \<circ> \<pi>b) \<circ> (\<lambda>\<pi>'. \<pi>' \<circ> \<pi>a)"
    by (simp add: comp_def)
  show ?thesis
    apply (fold image_Collect)
    apply (unfold *)
    apply (fold image_comp)
    apply (subst image_Collect)
    apply (unfold image_compose_permutations_right[OF assms(1)])
    apply (subst image_Collect)
    apply (unfold image_compose_permutations_right[OF assms(2)])
    ..
qed

lemma random_perm_middle:
  defines "random_perm n \<equiv> spmf_of_set {\<pi>. \<pi> permutes {..<n::nat}}"
  shows
    "map_spmf (\<lambda>(\<pi>a,\<pi>b,\<pi>c). ((\<pi>a,\<pi>b,\<pi>c),\<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (pair_spmf (random_perm n) (pair_spmf (random_perm n) (random_perm n)))
     = map_spmf (\<lambda>(\<pi>,\<pi>a,\<pi>c). ((\<pi>a,inv \<pi>a \<circ> \<pi> \<circ> inv \<pi>c,\<pi>c),\<pi>)) (pair_spmf (random_perm n) (pair_spmf (random_perm n) (random_perm n)))"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = (do {\<pi>a \<leftarrow> random_perm n; \<pi>c \<leftarrow> random_perm n; (\<pi>b,p) \<leftarrow> map_spmf (\<lambda>\<pi>b. (\<pi>b,\<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (random_perm n); return_spmf ((\<pi>a, \<pi>b, \<pi>c), p)})"
    unfolding map_spmf_conv_bind_spmf pair_spmf_alt_def
    apply simp
    apply (subst (4) bind_commute_spmf)
    ..
  also
  have "\<dots> = (do {\<pi>a \<leftarrow> random_perm n; \<pi>c \<leftarrow> random_perm n; map_spmf (\<lambda>p. ((\<pi>a, inv \<pi>a \<circ> p \<circ> inv \<pi>c,\<pi>c),p)) (random_perm n)})"
    unfolding random_perm_def
    supply [intro!] =
      bind_spmf_permutes_cong
    apply rule+
    apply (subst inv_uniform)
    subgoal for \<pi>a \<pi>c
      apply (rule inj_compose[unfolded comp_def, where f="\<lambda>p. p \<circ> \<pi>c"])
      subgoal by (rule permute_comp_right_inj_on)
      subgoal by (rule permute_comp_left_inj_on)
      done
    apply (simp add: permutes_inv_comp_left_right map_spmf_conv_bind_spmf image_Collect image_compose_permutations_left_right)
    done
  also
  have "\<dots> = ?rhs"
    unfolding map_spmf_conv_bind_spmf pair_spmf_alt_def
    apply (subst (2) bind_commute_spmf)
    apply (subst (1) bind_commute_spmf)
    apply simp
    done
  finally show ?thesis .
qed

lemma random_perm_right:
  defines "random_perm n \<equiv> spmf_of_set {\<pi>. \<pi> permutes {..<n::nat}}"
  shows
    "map_spmf (\<lambda>(\<pi>a,\<pi>b,\<pi>c). ((\<pi>a,\<pi>b,\<pi>c),\<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (pair_spmf (random_perm n) (pair_spmf (random_perm n) (random_perm n)))
     = map_spmf (\<lambda>(\<pi>,\<pi>a,\<pi>b). ((\<pi>a,\<pi>b,inv \<pi>b \<circ> inv \<pi>a \<circ> \<pi>),\<pi>)) (pair_spmf (random_perm n) (pair_spmf (random_perm n) (random_perm n)))"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = (do {\<pi>a \<leftarrow> random_perm n; \<pi>b \<leftarrow> random_perm n; (\<pi>c,\<pi>) \<leftarrow> map_spmf (\<lambda>\<pi>c. (\<pi>c,\<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (random_perm n); return_spmf ((\<pi>a, \<pi>b, \<pi>c), \<pi>)})"
    unfolding map_spmf_conv_bind_spmf pair_spmf_alt_def
    by simp
  also
  have "\<dots> = (do {\<pi>a \<leftarrow> random_perm n; \<pi>b \<leftarrow> random_perm n; map_spmf (\<lambda>\<pi>. ((\<pi>a, \<pi>b, inv \<pi>b \<circ> inv \<pi>a \<circ> \<pi>),\<pi>)) (random_perm n)})"
    unfolding random_perm_def
    supply [intro!] =
      bind_spmf_permutes_cong
    apply rule+
    apply (subst inv_uniform)
    subgoal
      apply (rule permute_comp_left_inj_on)
      using permutes_compose .
    apply (simp add: permutes_inv_comp_left_left map_spmf_conv_bind_spmf image_Collect image_compose_permutations_left_left)
    done
  also
  have "\<dots> = ?rhs"
    unfolding map_spmf_conv_bind_spmf pair_spmf_alt_def
    apply (subst (2) bind_commute_spmf)
    apply (subst (1) bind_commute_spmf)
    apply simp
    done
  finally show ?thesis .
qed

lemma random_perm_left:
  defines "random_perm n \<equiv> spmf_of_set {\<pi>. \<pi> permutes {..<n::nat}}"
  shows
    "map_spmf (\<lambda>(\<pi>a,\<pi>b,\<pi>c). ((\<pi>a,\<pi>b,\<pi>c),\<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (pair_spmf (random_perm n) (pair_spmf (random_perm n) (random_perm n)))
     = map_spmf (\<lambda>(\<pi>,\<pi>b,\<pi>c). ((\<pi> \<circ> inv \<pi>c \<circ> inv \<pi>b,\<pi>b,\<pi>c),\<pi>)) (pair_spmf (random_perm n) (pair_spmf (random_perm n) (random_perm n)))"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = (do {\<pi>b \<leftarrow> random_perm n; \<pi>c \<leftarrow> random_perm n; (\<pi>a,\<pi>) \<leftarrow> map_spmf (\<lambda>\<pi>a. (\<pi>a,\<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (random_perm n); return_spmf ((\<pi>a, \<pi>b, \<pi>c), \<pi>)})"
    unfolding map_spmf_conv_bind_spmf pair_spmf_alt_def
    apply simp
    apply (subst (4) bind_commute_spmf)
    apply (subst (3) bind_commute_spmf)
    ..
  also
  have "\<dots> = (do {\<pi>b \<leftarrow> random_perm n; \<pi>c \<leftarrow> random_perm n; map_spmf (\<lambda>\<pi>. ((\<pi> \<circ> inv \<pi>c \<circ> inv \<pi>b, \<pi>b, \<pi>c),\<pi>)) (random_perm n)})"
    unfolding random_perm_def
    supply [intro!] =
      bind_spmf_permutes_cong
    apply rule+
    apply (subst inv_uniform)
    subgoal
      apply (unfold comp_assoc)
      apply (rule permute_comp_right_inj_on)
      using permutes_compose .
    apply (simp add: permutes_inv_comp_right_right map_spmf_conv_bind_spmf image_Collect image_compose_permutations_right_right)
    done
  also
  have "\<dots> = ?rhs"
    unfolding map_spmf_conv_bind_spmf pair_spmf_alt_def
    apply (subst (2) bind_commute_spmf)
    apply (subst (1) bind_commute_spmf)
    apply simp
    done
  finally show ?thesis .
qed

lemma case_prod_return_spmf:
  "case_prod (\<lambda>a b. return_spmf (f a b)) = (\<lambda>x. return_spmf (case_prod f x))"
  by auto

lemma sequence_share_nat_calc':
  assumes "r1\<noteq>r2" "r2\<noteq>r3" "r3\<noteq>r1"
  shows
  "sequence_spmf (map share_nat xs) = (do {
    let n = length xs;
    let random_seq = sequence_spmf (replicate n (spmf_of_set UNIV));
    (dp, dpn) \<leftarrow> (pair_spmf random_seq random_seq);
    return_spmf (map3 (\<lambda>x a b. make_sharing' r1 r2 r3 a b (x - (a + b))) xs dp dpn)
  })" (is "_ = ?rhs")
proof -
  have
  "sequence_spmf (map share_nat xs) = (do {
    let n = length xs;
    let random_seq = sequence_spmf (replicate n (spmf_of_set UNIV));
    (xs, dp, dpn) \<leftarrow> pair_spmf (sequence_spmf (map return_spmf xs)) (pair_spmf random_seq random_seq);
    return_spmf (map3 (\<lambda>x a b. make_sharing' r1 r2 r3 a b (x - (a + b))) xs dp dpn)
  })"
    apply (unfold Let_def)
    apply (unfold case_prod_return_spmf)
    apply (fold map_spmf_conv_bind_spmf)
    apply (subst map3_spmf_map3_sequence)
    subgoal by simp
    subgoal by simp
    apply (rule arg_cong[where f=sequence_spmf])
    apply (unfold map_eq_iff_list_all2)
    apply (rule list_all2_all_nthI)
    subgoal by simp
    unfolding share_nat_def_calc'[OF assms]
    apply (auto simp: map_spmf_conv_bind_spmf pair_spmf_alt_def)
    done
  also have "\<dots> = ?rhs"
    by (auto simp: pair_spmf_alt_def sequence_map_return_spmf)
  finally show ?thesis .
qed


lemma reconstruct_stack_sharing_eq_reconstruct:
  "reconstruct \<circ> aby3_stack_sharing r = reconstruct"
  unfolding aby3_stack_sharing_def reconstruct_def
  by (cases r) (auto simp: make_sharing'_sel)

lemma map2_ignore1:
  "length xs = length ys \<Longrightarrow> map2 (\<lambda>_. f) xs ys = map f ys"
  apply (unfold map_eq_iff_list_all2)
  apply (rule list_all2_all_nthI)
  by auto

lemma map2_ignore2:
  "length xs = length ys \<Longrightarrow> map2 (\<lambda>a b. f a) xs ys = map f xs"
  apply (unfold map_eq_iff_list_all2)
  apply (rule list_all2_all_nthI)
  by auto


lemma map_sequence_share_nat_reconstruct:
  "map_spmf (\<lambda>x. (x, map reconstruct x)) (sequence_spmf (map share_nat y)) = map_spmf (\<lambda>x. (x, y)) (sequence_spmf (map share_nat y))"
  apply (unfold map_spmf_conv_bind_spmf)
  apply (rule bind_spmf_cong[OF refl])
  apply (auto simp: set_sequence_spmf list_eq_iff_nth_eq list_all2_conv_all_nth share_nat_def)
  done

(* the main theorem of security of the shuffling protocol *)
theorem shuffle_secrecy:
  assumes
    "is_uniform_sharing_list x_dist"
  shows
    "(do {
       x \<leftarrow> x_dist;
       (msg, y) \<leftarrow> aby3_shuffleR x;
       return_spmf (map (get_party r) x,
                    get_party r msg,
                    y)
     })
     =
     (do {
       x \<leftarrow> x_dist;
       y \<leftarrow> aby3_shuffleF x;
       let xr = map (get_party r) x;
       let yr = map (get_party r) y;
       msg \<leftarrow> S r xr yr;
       return_spmf (xr, msg, y)
     })"
    (is "?lhs = ?rhs")
proof -
  obtain xs where xs: "x_dist = xs \<bind> (sequence_spmf \<circ> map share_nat)"
    using assms unfolding is_uniform_sharing_list_def by auto

  have left_unfolded:
    "(do {
       x \<leftarrow> x_dist;
       (msg, y) \<leftarrow> aby3_shuffleR x;
       return_spmf (map (get_party r) x, get_party r msg, y)})
     =
     (do {
       xs \<leftarrow> xs;
       x \<leftarrow> sequence_spmf (map share_nat xs); 

\<comment> \<open>round 1\<close>
         let n = length x;
         \<zeta>a \<leftarrow> sequence_spmf (replicate n zero_sharing);
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let x' = map (get_party (prev_role Party1)) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let a = map2 (map_sharing2 (+)) (permute_list \<pi>a y') \<zeta>a;

\<comment> \<open>round 2\<close>
         let n = length a;
         \<zeta>b \<leftarrow> sequence_spmf (replicate n zero_sharing);
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let a' = map (get_party (prev_role Party2)) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let b = map2 (map_sharing2 (+)) (permute_list \<pi>b y') \<zeta>b;

\<comment> \<open>round 3\<close>
         let n = length b;
         \<zeta>c \<leftarrow> sequence_spmf (replicate n zero_sharing);
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let b' = map (get_party (prev_role Party3)) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let c = map2 (map_sharing2 (+)) (permute_list \<pi>c y') \<zeta>c;

       let msg1 = ((map (get_party Party1) \<zeta>a, map (get_party Party1) \<zeta>b, map (get_party Party1) \<zeta>c), b', \<pi>a, \<pi>c);
       let msg2 = ((map (get_party Party2) \<zeta>a, map (get_party Party2) \<zeta>b, map (get_party Party2) \<zeta>c), x', \<pi>a, \<pi>b);
       let msg3 = ((map (get_party Party3) \<zeta>a, map (get_party Party3) \<zeta>b, map (get_party Party3) \<zeta>c), a', \<pi>b, \<pi>c);
       let msg = make_sharing msg1 msg2 msg3;
       return_spmf (map (get_party r) x, get_party r msg, c)
   })"
    unfolding xs aby3_shuffleR_def aby3_do_permute_def
    by (auto simp: case_prod_unfold Let_def)

  also have clarify_length:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs); 

\<comment> \<open>round 1\<close>
         \<zeta>a \<leftarrow> sequence_spmf (replicate n zero_sharing);
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let x' = map (get_party (prev_role Party1)) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let a = map2 (map_sharing2 (+)) (permute_list \<pi>a y') \<zeta>a;

\<comment> \<open>round 2\<close>
         \<zeta>b \<leftarrow> sequence_spmf (replicate n zero_sharing);
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let a' = map (get_party (prev_role Party2)) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let b = map2 (map_sharing2 (+)) (permute_list \<pi>b y') \<zeta>b;

\<comment> \<open>round 3\<close>
         \<zeta>c \<leftarrow> sequence_spmf (replicate n zero_sharing);
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let b' = map (get_party (prev_role Party3)) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let c = map2 (map_sharing2 (+)) (permute_list \<pi>c y') \<zeta>c;

       let msg1 = ((map (get_party Party1) \<zeta>a, map (get_party Party1) \<zeta>b, map (get_party Party1) \<zeta>c), b', \<pi>a, \<pi>c);
       let msg2 = ((map (get_party Party2) \<zeta>a, map (get_party Party2) \<zeta>b, map (get_party Party2) \<zeta>c), x', \<pi>a, \<pi>b);
       let msg3 = ((map (get_party Party3) \<zeta>a, map (get_party Party3) \<zeta>b, map (get_party Party3) \<zeta>c), a', \<pi>b, \<pi>c);
       let msg = make_sharing msg1 msg2 msg3;
       return_spmf (map (get_party r) x, get_party r msg, c)
   })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
    by (auto simp: Let_def)

  also have hoist_permutations:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs); 

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

\<comment> \<open>round 1\<close>
         let x' = map (get_party (prev_role Party1)) x;
         let y' = map (aby3_stack_sharing Party1) x;
         \<zeta>a \<leftarrow> sequence_spmf (replicate n zero_sharing);
         let a = map2 (map_sharing2 (+)) (permute_list \<pi>a y') \<zeta>a;

\<comment> \<open>round 2\<close>
         let a' = map (get_party (prev_role Party2)) a;
         let y' = map (aby3_stack_sharing Party2) a;
         \<zeta>b \<leftarrow> sequence_spmf (replicate n zero_sharing);
         let b = map2 (map_sharing2 (+)) (permute_list \<pi>b y') \<zeta>b;

\<comment> \<open>round 3\<close>
         let b' = map (get_party (prev_role Party3)) b;
         let y' = map (aby3_stack_sharing Party3) b;
         \<zeta>c \<leftarrow> sequence_spmf (replicate n zero_sharing);
         let c = map2 (map_sharing2 (+)) (permute_list \<pi>c y') \<zeta>c;

       let msg1 = ((map (get_party Party1) \<zeta>a, map (get_party Party1) \<zeta>b, map (get_party Party1) \<zeta>c), b', \<pi>a, \<pi>c);
       let msg2 = ((map (get_party Party2) \<zeta>a, map (get_party Party2) \<zeta>b, map (get_party Party2) \<zeta>c), x', \<pi>a, \<pi>b);
       let msg3 = ((map (get_party Party3) \<zeta>a, map (get_party Party3) \<zeta>b, map (get_party Party3) \<zeta>c), a', \<pi>b, \<pi>c);
       let msg = make_sharing msg1 msg2 msg3;
       return_spmf (map (get_party r) x, get_party r msg, c)
   })"
    apply (simp add: Let_def)
    apply (subst (1) bind_commute_spmf[where q="spmf_of_set _"])
    apply (subst (2) bind_commute_spmf[where q="spmf_of_set _"])
    apply (subst (2) bind_commute_spmf[where q="spmf_of_set _"])
    apply (subst (3) bind_commute_spmf[where q="spmf_of_set _"])
    apply (subst (3) bind_commute_spmf[where q="spmf_of_set _"])
    apply (subst (3) bind_commute_spmf[where q="spmf_of_set _"])
    by simp

  also have hoist_permutations:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs); 

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

\<comment> \<open>round 1\<close>
         let x' = map (get_party (prev_role Party1)) x;
         let y' = map (aby3_stack_sharing Party1) x;
         a \<leftarrow> sequence_spmf (map (share_nat \<circ> reconstruct) (permute_list \<pi>a y'));
         let \<zeta>a = map2 (map_sharing2 (-)) a (permute_list \<pi>a y');

\<comment> \<open>round 2\<close>
         let a' = map (get_party (prev_role Party2)) a;
         let y' = map (aby3_stack_sharing Party2) a;
         b \<leftarrow> sequence_spmf (map (share_nat \<circ> reconstruct) (permute_list \<pi>b y'));
         let \<zeta>b = map2 (map_sharing2 (-)) b (permute_list \<pi>b y');

\<comment> \<open>round 3\<close>
         let b' = map (get_party (prev_role Party3)) b;
         let y' = map (aby3_stack_sharing Party3) b;
         c \<leftarrow> sequence_spmf (map (share_nat \<circ> reconstruct) (permute_list \<pi>c y'));
         let \<zeta>c = map2 (map_sharing2 (-)) c (permute_list \<pi>c y');

       let msg1 = ((map (get_party Party1) \<zeta>a, map (get_party Party1) \<zeta>b, map (get_party Party1) \<zeta>c), b', \<pi>a, \<pi>c);
       let msg2 = ((map (get_party Party2) \<zeta>a, map (get_party Party2) \<zeta>b, map (get_party Party2) \<zeta>c), x', \<pi>a, \<pi>b);
       let msg3 = ((map (get_party Party3) \<zeta>a, map (get_party Party3) \<zeta>b, map (get_party Party3) \<zeta>c), a', \<pi>b, \<pi>c);
       let msg = make_sharing msg1 msg2 msg3;
       return_spmf (map (get_party r) x, get_party r msg, c)
   })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

    apply rule+
    apply (subst hoist_map_spmf[where s="sequence_spmf (replicate _ _)" and f = "map2 (map_sharing2 (+)) _"])
    apply (subst hoist_map_spmf'[where s="sequence_spmf (map _ _)" and f = "\<lambda>ys. map2 (map_sharing2 (-)) ys _"])
    apply (subst inv_zero_sharing_sequence)
    subgoal by simp
    apply (unfold map_spmf_conv_bind_spmf)
    apply (unfold bind_spmf_assoc)
    apply (unfold return_bind_spmf)
    apply rule+
    apply (subst (1 12) Let_def)
    apply rule+

    apply (subst hoist_map_spmf[where s="sequence_spmf (replicate _ _)" and f = "map2 (map_sharing2 (+)) _"])
    apply (subst hoist_map_spmf'[where s="sequence_spmf (map _ _)" and f = "\<lambda>ys. map2 (map_sharing2 (-)) ys _"])
    apply (subst inv_zero_sharing_sequence)
    subgoal by simp
    apply (unfold map_spmf_conv_bind_spmf)
    apply (unfold bind_spmf_assoc)
    apply (unfold return_bind_spmf)
    apply rule+
    apply (subst (1 9) Let_def)
    apply rule+

    apply (subst hoist_map_spmf[where s="sequence_spmf (replicate _ _)" and f = "map2 (map_sharing2 (+)) _"])
    apply (subst hoist_map_spmf'[where s="sequence_spmf (map _ _)" and f = "\<lambda>ys. map2 (map_sharing2 (-)) ys _"])
    apply (subst inv_zero_sharing_sequence)
    subgoal by simp
    apply (unfold map_spmf_conv_bind_spmf)
    apply (unfold bind_spmf_assoc)
    apply (unfold return_bind_spmf)
    apply rule+
    apply (subst (1 6) Let_def)
    apply rule+

    done

  also have reconstruct:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs); 

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

\<comment> \<open>round 1\<close>
         let x' = map (get_party (prev_role Party1)) x;
         let y' = map (aby3_stack_sharing Party1) x;
         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         let \<zeta>a = map2 (map_sharing2 (-)) a (permute_list \<pi>a y');

\<comment> \<open>round 2\<close>
         let a' = map (get_party (prev_role Party2)) a;
         let y' = map (aby3_stack_sharing Party2) a;
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         let \<zeta>b = map2 (map_sharing2 (-)) b (permute_list \<pi>b y');

\<comment> \<open>round 3\<close>
         let b' = map (get_party (prev_role Party3)) b;
         let y' = map (aby3_stack_sharing Party3) b;
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));
         let \<zeta>c = map2 (map_sharing2 (-)) c (permute_list \<pi>c y');

       let msg1 = ((map (get_party Party1) \<zeta>a, map (get_party Party1) \<zeta>b, map (get_party Party1) \<zeta>c), b', \<pi>a, \<pi>c);
       let msg2 = ((map (get_party Party2) \<zeta>a, map (get_party Party2) \<zeta>b, map (get_party Party2) \<zeta>c), x', \<pi>a, \<pi>b);
       let msg3 = ((map (get_party Party3) \<zeta>a, map (get_party Party3) \<zeta>b, map (get_party Party3) \<zeta>c), a', \<pi>b, \<pi>c);
       let msg = make_sharing msg1 msg2 msg3;
       return_spmf (map (get_party r) x, get_party r msg, c)
   })"

    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
      bind_spmf_sequence_map_share_nat_cong

    apply rule+
    apply (subst list.map_comp[symmetric])
    apply (rule bind_spmf_cong)
    subgoal by (auto simp:permute_list_map[symmetric] map_reconstruct_comp_eq_iff reconstruct_def set_sequence_spmf[unfolded list_all2_iff] make_sharing'_sel reconstruct_stack_sharing_eq_reconstruct comp_assoc)
    apply rule+
    apply (subst list.map_comp[symmetric])
    apply (rule bind_spmf_cong)
    subgoal for x l xa \<pi>a \<pi>b \<pi>c xb xc xd xe xf xg
      apply (subst permute_list_map[symmetric] )
      subgoal by (auto simp add: set_sequence_spmf[unfolded list_all2_iff])
      apply simp
      apply (subst map_reconstruct_comp_eq_iff)
      subgoal by (simp add: reconstruct_def make_sharing'_sel aby3_stack_sharing_def)
      unfolding set_sequence_spmf mem_Collect_eq 
      unfolding list_all2_map2
      apply (subst map_eq_iff_list_all2[where f=reconstruct and g=id and xs=xd and ys="permute_list \<pi>a x", simplified, THEN iffD2])
      subgoal by (erule list_all2_mono) (simp add: share_nat_def)
      apply (subst permute_list_compose)
      subgoal by auto
      ..
    apply rule+
    apply (subst list.map_comp[symmetric])
    apply (rule bind_spmf_cong)
    subgoal for x l xa \<pi>a \<pi>b \<pi>c xb xc xd xe xf xg xh xi xj xk
      apply (subst permute_list_map[symmetric] )
      subgoal by (auto simp add: set_sequence_spmf[unfolded list_all2_iff])
      apply simp
      apply (subst map_reconstruct_comp_eq_iff)
      subgoal by (simp add: reconstruct_def make_sharing'_sel aby3_stack_sharing_def)
      unfolding set_sequence_spmf mem_Collect_eq 
      unfolding list_all2_map2
      apply (subst map_eq_iff_list_all2[where f=reconstruct and g=id and xs=xh and ys="permute_list (\<pi>a \<circ> \<pi>b) x", simplified, THEN iffD2])
      subgoal by (erule list_all2_mono) (simp add: share_nat_def)
      apply (subst permute_list_compose[symmetric])
      subgoal by auto
      ..
    ..

  also have hoist:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party (prev_role Party1)) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let \<zeta>a = map2 (map_sharing2 (-)) a (permute_list \<pi>a y');

\<comment> \<open>round 2\<close>
         let a' = map (get_party (prev_role Party2)) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let \<zeta>b = map2 (map_sharing2 (-)) b (permute_list \<pi>b y');

\<comment> \<open>round 3\<close>
         let b' = map (get_party (prev_role Party3)) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let \<zeta>c = map2 (map_sharing2 (-)) c (permute_list \<pi>c y');

       let msg1 = ((map (get_party Party1) \<zeta>a, map (get_party Party1) \<zeta>b, map (get_party Party1) \<zeta>c), b', \<pi>a, \<pi>c);
       let msg2 = ((map (get_party Party2) \<zeta>a, map (get_party Party2) \<zeta>b, map (get_party Party2) \<zeta>c), x', \<pi>a, \<pi>b);
       let msg3 = ((map (get_party Party3) \<zeta>a, map (get_party Party3) \<zeta>b, map (get_party Party3) \<zeta>c), a', \<pi>b, \<pi>c);
       let msg = make_sharing msg1 msg2 msg3;
       return_spmf (map (get_party r) x, get_party r msg, c)
   })"
    unfolding Let_def ..
  finally have hoisted_save: "?lhs = \<dots>" .
  let ?hoisted = \<dots>

  { assume r: "r = Party1"
    have project_to_Party1:
    "?hoisted = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let \<zeta>a1 = map (case_prod (-)) (zip (map (get_party Party1) a) (map (get_party Party1) (permute_list \<pi>a y')));

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let \<zeta>b1 = map (case_prod (-)) (zip (map (get_party Party1) b) (map (get_party Party1) (permute_list \<pi>b y')));

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let \<zeta>c1 = map (case_prod (-)) (zip (map (get_party Party1) c) (map (get_party Party1) (permute_list \<pi>c y')));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
   })"
      by (simp add: r Let_def get_party_map_sharing2 map_map_prod_zip')

    also have project_to_Party1:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let \<zeta>a1 = map2 (-) (map (get_party Party1) a) (permute_list \<pi>a (map (get_party Party1) y'));

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let \<zeta>b1 = map2 (-) (map (get_party Party1) b) (permute_list \<pi>b (map (get_party Party1) y'));

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map (get_party Party1) y'));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp
      ..

    also have reduce_Lets:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) (map (get_party Party1) a) (permute_list \<pi>a (map (get_party Party1) x));

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = map2 (-) (map (get_party Party1) b) (permute_list \<pi>b (replicate (length a) 0));

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map2 (+) (map (get_party Party1) b) (map (get_party Party2) b)));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
      unfolding Let_def
      unfolding aby3_stack_sharing_def
      by (simp add: comp_def make_sharing'_sel map_replicate_const zip_map_map_same[symmetric])

    also have simplify_minus_zero:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) (map (get_party Party1) a) (permute_list \<pi>a (map (get_party Party1) x));

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = (map (get_party Party1) b);

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map2 (+) (map (get_party Party1) b) (map (get_party Party2) b)));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

      apply rule+
      apply (subst permute_list_replicate)
      subgoal by simp

      apply (subst map2_minus_zero)
      subgoal by simp
      subgoal by simp

      ..

    also have break_perms_1:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         (\<pi>a,\<pi>b,\<pi>c) \<leftarrow> pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (spmf_of_set {\<pi>. \<pi> permutes {..<n}}));

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) (map (get_party Party1) a) (permute_list \<pi>a (map (get_party Party1) x));

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = (map (get_party Party1) b);

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map2 (+) (map (get_party Party1) b) (map (get_party Party2) b)));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
      unfolding pair_spmf_alt_def by simp

    also have break_perms_2:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         ((\<pi>a,\<pi>b,\<pi>c),\<pi>) \<leftarrow> map_spmf (\<lambda>(\<pi>a,\<pi>b,\<pi>c). ((\<pi>a,\<pi>b,\<pi>c), \<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (spmf_of_set {\<pi>. \<pi> permutes {..<n}})));

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) (map (get_party Party1) a) (permute_list \<pi>a (map (get_party Party1) x));

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = (map (get_party Party1) b);

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map2 (+) (map (get_party Party1) b) (map (get_party Party2) b)));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
      unfolding pair_spmf_alt_def map_spmf_conv_bind_spmf by simp

    also have break_perms_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let \<pi>b = inv \<pi>a \<circ> \<pi> \<circ> inv \<pi>c;

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) (map (get_party Party1) a) (permute_list \<pi>a (map (get_party Party1) x));

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = (map (get_party Party1) b);

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map2 (+) (map (get_party Party1) b) (map (get_party Party2) b)));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
      apply (unfold random_perm_middle)
      apply (unfold map_spmf_conv_bind_spmf pair_spmf_alt_def)
      by simp

    also have break_seqs_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;

       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let \<pi>b = inv \<pi>a \<circ> \<pi> \<circ> inv \<pi>c;

         a1 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         a2 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         let a = map3 (\<lambda>a b c. make_sharing b c (a - (b + c))) (permute_list \<pi>a xs) a1 a2;
         b1 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         b2 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         let b = map3 (\<lambda>a b c. make_sharing b c (a - (b + c))) (permute_list (\<pi>a \<circ> \<pi>b) xs) b1 b2;
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) (map (get_party Party1) a) (permute_list \<pi>a (map (get_party Party1) x));

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = (map (get_party Party1) b);

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map2 (+) (map (get_party Party1) b) (map (get_party Party2) b)));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
      apply (unfold sequence_share_nat_calc'[of Party1 Party2 Party3, simplified])
      apply (simp add: pair_spmf_alt_def Let_def)
      done

    also have break_seqs_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;

       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         a2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         b1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         b2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a1 = map2 (-) a1 (permute_list \<pi>a (map (get_party Party1) x));

\<comment> \<open>round 2\<close>
         let \<zeta>b1 = b1;

\<comment> \<open>round 3\<close>
         let b' = b2;
         let \<zeta>c1 = map2 (-) (map (get_party Party1) c) (permute_list \<pi>c (map2 (+) b1 b2));

       let msg1 = ((\<zeta>a1, \<zeta>b1, \<zeta>c1), b', \<pi>a, \<pi>c);
       return_spmf (map (get_party Party1) x, msg1, c)
    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
      unfolding Let_def
      apply rule+
      apply (auto simp: map2_ignore1 map2_ignore2 comp_def prod.case_distrib bind_spmf_const)
      done

    also have
      "\<dots> = (do {x \<leftarrow> x_dist; y \<leftarrow> aby3_shuffleF x; let xr = map (get_party r) x; let yr = map (get_party r) y; msg \<leftarrow> S r xr yr; return_spmf (xr, msg, y)})"
      unfolding xs
      unfolding aby3_shuffleF_def
      apply (simp add: bind_spmf_const map_spmf_conv_bind_spmf)
      apply (subst lossless_sequence_spmf[unfolded lossless_spmf_def])
      subgoal by simp
      apply simp
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])

      apply (subst (3) hoist_map_spmf[where s="sequence_spmf (map share_nat _)" and f="map reconstruct"])
      apply (subst map_sequence_share_nat_reconstruct)
      apply (simp add: map_spmf_conv_bind_spmf)
      apply (subst Let_def)

      supply [intro!] =
        bind_spmf_cong[OF refl]
        let_cong[OF refl]
        prod.case_cong[OF refl]
        bind_spmf_sequence_map_cong
        bind_spmf_sequence_replicate_cong
        bind_spmf_permutes_cong

      supply [simp] = finite_permutations

      apply rule
      apply rule
      apply simp
      apply rule
      apply rule
      unfolding S_def S1_def r
      apply (simp add: Let_def)
      done

    finally have "?hoisted = \<dots>" .
  } note simulate_party1 = this

  { assume r: "r = Party2"
    have project_to_Party2:
    "?hoisted = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let \<zeta>a2 = map (case_prod (-)) (zip (map (get_party Party2) a) (map (get_party Party2) (permute_list \<pi>a y')));

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let \<zeta>b2 = map (case_prod (-)) (zip (map (get_party Party2) b) (map (get_party Party2) (permute_list \<pi>b y')));

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let \<zeta>c2 = map (case_prod (-)) (zip (map (get_party Party2) c) (map (get_party Party2) (permute_list \<pi>c y')));

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (map (get_party Party2) x, msg2, c)
   })"
      by (simp add: r Let_def get_party_map_sharing2 map_map_prod_zip')

    also have project_to_Party2:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let \<zeta>a2 = map2 (-) (map (get_party Party2) a) (permute_list \<pi>a (map (get_party Party2) y'));

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let \<zeta>b2 = map2 (-) (map (get_party Party2) b) (permute_list \<pi>b (map (get_party Party2) y'));

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let \<zeta>c2 = map2 (-) (map (get_party Party2) c) (permute_list \<pi>c (map (get_party Party2) y'));

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (map (get_party Party2) x, msg2, c)
    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp
      ..

    also have reduce_Lets:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let \<zeta>a2 = map2 (-) (map (get_party Party2) a) (permute_list \<pi>a (map2 (+) (map (get_party Party2) x) (map (get_party Party3) x)));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) (map (get_party Party2) b) (permute_list \<pi>b (map (get_party Party2) a));

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = map2 (-) (map (get_party Party2) c) (permute_list \<pi>c (replicate (length b) 0));

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);

       return_spmf (map (get_party Party2) x, msg2, c)
    })"
      unfolding Let_def
      unfolding aby3_stack_sharing_def
      by (simp add: comp_def make_sharing'_sel map_replicate_const zip_map_map_same[symmetric])

    also have simplify_minus_zero:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let \<zeta>a2 = map2 (-) (map (get_party Party2) a) (permute_list \<pi>a (map2 (+) (map (get_party Party2) x) (map (get_party Party3) x)));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) (map (get_party Party2) b) (permute_list \<pi>b (map (get_party Party2) a));

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = (map (get_party Party2) c);

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (map (get_party Party2) x, msg2, c)
    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

      apply rule+
      apply (subst permute_list_replicate)
      subgoal by simp

      apply (subst map2_minus_zero)
      subgoal by simp
      subgoal by simp

      ..

    also have break_perms_1:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         (\<pi>a,\<pi>b,\<pi>c) \<leftarrow> pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (spmf_of_set {\<pi>. \<pi> permutes {..<n}}));

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let \<zeta>a2 = map2 (-) (map (get_party Party2) a) (permute_list \<pi>a (map2 (+) (map (get_party Party2) x) (map (get_party Party3) x)));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) (map (get_party Party2) b) (permute_list \<pi>b (map (get_party Party2) a));

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = (map (get_party Party2) c);

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (map (get_party Party2) x, msg2, c)
    })"
      unfolding pair_spmf_alt_def by simp

    also have break_perms_2:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         ((\<pi>a,\<pi>b,\<pi>c),\<pi>) \<leftarrow> map_spmf (\<lambda>(\<pi>a,\<pi>b,\<pi>c). ((\<pi>a,\<pi>b,\<pi>c), \<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (spmf_of_set {\<pi>. \<pi> permutes {..<n}})));

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let \<zeta>a2 = map2 (-) (map (get_party Party2) a) (permute_list \<pi>a (map2 (+) (map (get_party Party2) x) (map (get_party Party3) x)));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) (map (get_party Party2) b) (permute_list \<pi>b (map (get_party Party2) a));

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = (map (get_party Party2) c);

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (map (get_party Party2) x, msg2, c)
    })"
      unfolding pair_spmf_alt_def map_spmf_conv_bind_spmf by simp

    also have break_perms_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let \<pi>c = inv \<pi>b \<circ> inv \<pi>a \<circ> \<pi>;

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let \<zeta>a2 = map2 (-) (map (get_party Party2) a) (permute_list \<pi>a (map2 (+) (map (get_party Party2) x) (map (get_party Party3) x)));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) (map (get_party Party2) b) (permute_list \<pi>b (map (get_party Party2) a));

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = (map (get_party Party2) c);

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (map (get_party Party2) x, msg2, c)
    })"
      apply (unfold random_perm_right)
      apply (unfold map_spmf_conv_bind_spmf pair_spmf_alt_def)
      by simp

    also have break_seqs_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;

       x2 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       x3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       let x = map3 (\<lambda>a b c. make_sharing' Party2 Party3 Party1 b c (a - (b + c))) xs x2 x3;


         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a2 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         a3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         let a = map3 (\<lambda>a b c. make_sharing' Party2 Party3 Party1 b c (a - (b + c))) (permute_list \<pi>a xs) a2 a3;
         b2 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         b3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         let b = map3 (\<lambda>a b c. make_sharing' Party2 Party3 Party1 b c (a - (b + c))) (permute_list (\<pi>a \<circ> \<pi>b) xs) b2 b3;
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let \<zeta>a2 = map2 (-) (map (get_party Party2) a) (permute_list \<pi>a (map2 (+) (map (get_party Party2) x) (map (get_party Party3) x)));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) (map (get_party Party2) b) (permute_list \<pi>b (map (get_party Party2) a));

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = (map (get_party Party2) c);

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (map (get_party Party2) x, msg2, c)
    })"
      apply (unfold sequence_share_nat_calc'[of Party2 Party3 Party1, simplified])
      apply (simp add: pair_spmf_alt_def Let_def)
      done

    also have break_seqs_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;

       x2 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       x3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         a3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         b2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         b3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let x' = x3;
         let \<zeta>a2 = map2 (-) a2 (permute_list \<pi>a (map2 (+) x2 x3));

\<comment> \<open>round 2\<close>
         let \<zeta>b2 = map2 (-) b2 (permute_list \<pi>b a2);

\<comment> \<open>round 3\<close>
         let \<zeta>c2 = (map (get_party Party2) c);

       let msg2 = ((\<zeta>a2, \<zeta>b2, \<zeta>c2), x', \<pi>a, \<pi>b);
       return_spmf (x2, msg2, c)

    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
      unfolding Let_def
      apply rule+
      apply (auto simp: map2_ignore1 map2_ignore2 comp_def prod.case_distrib bind_spmf_const make_sharing'_sel)
      done

    also have
      "\<dots> = (do {x \<leftarrow> x_dist; y \<leftarrow> aby3_shuffleF x; let xr = map (get_party r) x; let yr = map (get_party r) y; msg \<leftarrow> S r xr yr; return_spmf (xr, msg, y)})"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

      unfolding xs
      unfolding aby3_shuffleF_def
      apply (simp add: bind_spmf_const map_spmf_conv_bind_spmf)
      apply (subst lossless_sequence_spmf[unfolded lossless_spmf_def])
      subgoal by simp
      apply (subst lossless_sequence_spmf[unfolded lossless_spmf_def])
      subgoal by simp
      apply simp

      apply rule

      apply (subst (2) sequence_share_nat_calc'[of Party2 Party3 Party1, simplified])
      apply (subst (2) Let_def)
      apply (simp add: pair_spmf_alt_def)
      apply (subst Let_def)
      unfolding S_def r
      apply (simp add: pair_spmf_alt_def comp_def prod.case_distrib map2_ignore2 make_sharing'_sel)

      apply (rule trans[rotated])
      apply (rule bind_spmf_sequence_replicate_cong)
       apply (rule bind_spmf_sequence_replicate_cong)
       apply (simp add: map2_ignore1 map2_ignore2)
      apply (subst bind_spmf_const)
      apply (subst lossless_sequence_spmf[unfolded lossless_spmf_def])
      subgoal by simp
      apply simp

      apply (subst (2) bind_commute_spmf[where p="sequence_spmf (replicate _ _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])

      apply rule
      apply rule
      apply rule

      unfolding S2_def Let_def
      apply simp
      done

    finally have "?hoisted = \<dots>" .
  } note simulate_party2 = this


  { assume r: "r = Party3"
    have project_to_Party3:
    "?hoisted = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let \<zeta>a3 = map (case_prod (-)) (zip (map (get_party Party3) a) (map (get_party Party3) (permute_list \<pi>a y')));

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let \<zeta>b3 = map (case_prod (-)) (zip (map (get_party Party3) b) (map (get_party Party3) (permute_list \<pi>b y')));

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let \<zeta>c3 = map (case_prod (-)) (zip (map (get_party Party3) c) (map (get_party Party3) (permute_list \<pi>c y')));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
   })"
      by (simp add: r Let_def get_party_map_sharing2 map_map_prod_zip')

    also have project_to_Party1:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let x' = map (get_party Party3) x;
         let y' = map (aby3_stack_sharing Party1) x;
         let \<zeta>a3 = map2 (-) (map (get_party Party3) a) (permute_list \<pi>a (map (get_party Party3) y'));

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let y' = map (aby3_stack_sharing Party2) a;
         let \<zeta>b3 = map2 (-) (map (get_party Party3) b) (permute_list \<pi>b (map (get_party Party3) y'));

\<comment> \<open>round 3\<close>
         let b' = map (get_party Party2) b;
         let y' = map (aby3_stack_sharing Party3) b;
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c (map (get_party Party3) y'));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)

    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp

      apply rule+
      apply (subst permute_list_map[symmetric])
      subgoal by simp
      ..

    also have reduce_Lets:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = map2 (-) (map (get_party Party3) a) (permute_list \<pi>a (replicate (length x) 0));

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let \<zeta>b3 = map2 (-) (map (get_party Party3) b) (permute_list \<pi>b (map2 (+) (map (get_party Party3) a) (map (get_party Party1) a)));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c (map (get_party Party3) b));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
    })"
      unfolding Let_def
      unfolding aby3_stack_sharing_def
      by (simp add: comp_def make_sharing'_sel map_replicate_const zip_map_map_same[symmetric])

    also have simplify_minus_zero:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = (map (get_party Party3) a);

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let \<zeta>b3 = map2 (-) (map (get_party Party3) b) (permute_list \<pi>b (map2 (+) (map (get_party Party3) a) (map (get_party Party1) a)));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c (map (get_party Party3) b));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

      apply rule+
      apply (subst permute_list_replicate)
      subgoal by simp

      apply (subst map2_minus_zero)
      subgoal by simp
      subgoal by simp

      ..

    also have break_perms_1:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         (\<pi>a,\<pi>b,\<pi>c) \<leftarrow> pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (spmf_of_set {\<pi>. \<pi> permutes {..<n}}));

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b \<circ> \<pi>c) xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = (map (get_party Party3) a);

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let \<zeta>b3 = map2 (-) (map (get_party Party3) b) (permute_list \<pi>b (map2 (+) (map (get_party Party3) a) (map (get_party Party1) a)));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c (map (get_party Party3) b));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
    })"
      unfolding pair_spmf_alt_def by simp

    also have break_perms_2:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         ((\<pi>a,\<pi>b,\<pi>c),\<pi>) \<leftarrow> map_spmf (\<lambda>(\<pi>a,\<pi>b,\<pi>c). ((\<pi>a,\<pi>b,\<pi>c), \<pi>a \<circ> \<pi>b \<circ> \<pi>c)) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (pair_spmf (spmf_of_set {\<pi>. \<pi> permutes {..<n}}) (spmf_of_set {\<pi>. \<pi> permutes {..<n}})));

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = (map (get_party Party3) a);

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let \<zeta>b3 = map2 (-) (map (get_party Party3) b) (permute_list \<pi>b (map2 (+) (map (get_party Party3) a) (map (get_party Party1) a)));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c (map (get_party Party3) b));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
    })"
      unfolding pair_spmf_alt_def map_spmf_conv_bind_spmf by simp

    also have break_perms_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let \<pi>a = \<pi> \<circ> inv \<pi>c \<circ> inv \<pi>b;

         a \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi>a xs));
         b \<leftarrow> sequence_spmf (map share_nat (permute_list (\<pi>a \<circ> \<pi>b) xs));
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = (map (get_party Party3) a);

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let \<zeta>b3 = map2 (-) (map (get_party Party3) b) (permute_list \<pi>b (map2 (+) (map (get_party Party3) a) (map (get_party Party1) a)));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c (map (get_party Party3) b));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
    })"
      apply (unfold random_perm_left)
      apply (unfold map_spmf_conv_bind_spmf pair_spmf_alt_def)
      by (simp add: Let_def)

    also have break_seqs_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;
       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let \<pi>a = \<pi> \<circ> inv \<pi>c \<circ> inv \<pi>b;

         a3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         a1 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         let a = map3 (\<lambda>a b c. make_sharing' Party3 Party1 Party2 b c (a - (b + c))) (permute_list \<pi>a xs) a3 a1;
         b3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         b1 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         let b = map3 (\<lambda>a b c. make_sharing' Party3 Party1 Party2 b c (a - (b + c))) (permute_list (\<pi>a \<circ> \<pi>b) xs) b3 b1;
         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = (map (get_party Party3) a);

\<comment> \<open>round 2\<close>
         let a' = map (get_party Party1) a;
         let \<zeta>b3 = map2 (-) (map (get_party Party3) b) (permute_list \<pi>b (map2 (+) (map (get_party Party3) a) (map (get_party Party1) a)));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c (map (get_party Party3) b));

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
    })"
      apply (unfold sequence_share_nat_calc'[of Party3 Party1 Party2, simplified])
      apply (simp add: pair_spmf_alt_def Let_def)
      done

    also have break_seqs_3:
    "\<dots> = (do {
       xs \<leftarrow> xs;
       let n = length xs;

       x \<leftarrow> sequence_spmf (map share_nat xs);

         \<pi> \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
         let \<pi>a = \<pi> \<circ> inv \<pi>c \<circ> inv \<pi>b;

         a3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         a1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         b3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
         b1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

         c \<leftarrow> sequence_spmf (map share_nat (permute_list \<pi> xs));

\<comment> \<open>round 1\<close>
         let \<zeta>a3 = a3;

\<comment> \<open>round 2\<close>
         let a' = a1;
         let \<zeta>b3 = map2 (-) b3 (permute_list \<pi>b (map2 (+) a3 a1));

\<comment> \<open>round 3\<close>
         let \<zeta>c3 = map2 (-) (map (get_party Party3) c) (permute_list \<pi>c b3);

       let msg3 = ((\<zeta>a3, \<zeta>b3, \<zeta>c3), a', \<pi>b, \<pi>c);
       return_spmf (map (get_party Party3) x, msg3, c)
    })"
    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
      unfolding Let_def
      apply rule+
      apply (auto simp: map2_ignore1 map2_ignore2 comp_def prod.case_distrib bind_spmf_const make_sharing'_sel)
      done

    also have
      "\<dots> = (do {x \<leftarrow> x_dist; y \<leftarrow> aby3_shuffleF x; let xr = map (get_party r) x; let yr = map (get_party r) y; msg \<leftarrow> S r xr yr; return_spmf (xr, msg, y)})"
      unfolding xs
      unfolding aby3_shuffleF_def
      apply (subst bind_spmf_const)
      apply (subst lossless_sequence_spmf[unfolded lossless_spmf_def])
      subgoal by simp
      apply (simp add:  map_spmf_conv_bind_spmf)
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])
      apply (subst bind_commute_spmf[where q="sequence_spmf (map share_nat _)"])

      apply (subst (3) hoist_map_spmf[where s="sequence_spmf (map share_nat _)" and f="map reconstruct"])
      apply (subst map_sequence_share_nat_reconstruct)
      apply (simp add: map_spmf_conv_bind_spmf)
      apply (subst Let_def)

    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong

    supply [simp] = finite_permutations

      apply rule
      apply rule
      apply simp
      apply rule
      apply rule
      unfolding S_def S3_def r
      apply (simp add: Let_def)
      done

    finally have "?hoisted = \<dots>" .
  } note simulate_party3 = this

  show ?thesis
    unfolding hoisted_save
    apply (cases r)
    subgoal using simulate_party1 .
    subgoal using simulate_party2 .
    subgoal using simulate_party3 .
    done
qed


lemma Collect_case_prod:
  "{f x y | x y. P x y} = (case_prod f) ` (Collect (case_prod P))"
  by auto

lemma inj_split_Cons': "inj_on (\<lambda>(n, xs). n#xs) X"
  by (auto intro!: inj_onI)

lemma finite_indicator_eq_sum:
  "finite A \<Longrightarrow> indicat_real A x = sum (indicat_real {x}) A"
  by (induction rule: finite_induct) (auto  simp: indicator_def)

lemma spmf_of_set_Cons:
  "spmf_of_set (set_Cons A B) = map2_spmf (#) (spmf_of_set A) (spmf_of_set B)"
  unfolding set_Cons_def pair_spmf_of_set
  apply (rule spmf_eq_iff_set)
  subgoal unfolding Collect_case_prod apply (auto simp: set_spmf_of_set )
     apply (subst (asm) finite_image_iff)
    subgoal by (rule inj_split_Cons')
    subgoal by (auto simp: finite_cartesian_product_iff)
    done
  subgoal unfolding Collect_case_prod
    apply (auto simp: spmf_of_set map_spmf_conv_bind_spmf spmf_bind integral_spmf_of_set)
    apply (subst card_image)
    subgoal by (rule inj_split_Cons')
    apply (auto simp: card_eq_0_iff indicator_single_Some)
    apply (subst (asm) finite_indicator_eq_sum)
    subgoal by (simp add: finite_image_iff inj_split_Cons')
    apply (subst (asm) sum.reindex)
    subgoal by (simp add: finite_image_iff inj_split_Cons')
    apply (auto)
    done
  done

lemma sequence_spmf_replicate:
  "sequence_spmf (replicate n (spmf_of_set A)) = spmf_of_set (listset (replicate n A))"
  apply (induction n)
  subgoal by (auto simp: spmf_of_set_singleton)
  subgoal by (auto simp: spmf_of_set_Cons)
  done

lemma listset_replicate:
  "listset (replicate n A) = {l. length l = n \<and> set l \<subseteq> A}"
  apply (induction n)
   apply (auto simp: set_Cons_def)
  subgoal for n x
    by (cases x; simp)
  done

lemma map2_map2_map3:
  "map2 f (map2 g x y) z = map3 (\<lambda>x y. f (g x y)) x y z"
  by (auto simp: zip_assoc map_zip_map)

lemma inv_add_sequence:
  assumes "n = length x"
  shows "
  map_spmf (\<lambda>\<zeta>::natL list. (\<zeta>, map2 (+) \<zeta> x)) (sequence_spmf (replicate n (spmf_of_set UNIV)))
  =
  map_spmf (\<lambda>y. (map2 (-) y x, y)) (sequence_spmf (replicate n (spmf_of_set UNIV)))"
  unfolding sequence_spmf_replicate
  apply (subst map_spmf_of_set_inj_on)
  subgoal   unfolding inj_on_def by simp
  apply (subst map_spmf_of_set_inj_on)
  subgoal  unfolding inj_on_def by simp
  apply (rule arg_cong[where f="spmf_of_set"])
  using assms apply (auto simp: image_def listset_replicate map2_map2_map3 zip_same_conv_map map_zip_map2 map2_ignore2)
  done
  
lemma S1_def_simplified:
    "S1 x1 yc1 = (do {
       let n = length x1;

       \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
       \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
       \<zeta>a1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       yb1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       yb2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

       let \<zeta>c1 = map2 (-) (yc1) (permute_list \<pi>c (map2 (+) yb1 yb2));
       return_spmf ((\<zeta>a1, yb1, \<zeta>c1), yb2, \<pi>a, \<pi>c)
    })"

  unfolding S1_def

    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
      bind_spmf_sequence_map_share_nat_cong

  apply rule
  apply rule
  apply rule
  apply (subst hoist_map_spmf'[where s="sequence_spmf _" and f="\<lambda>x. map2 (-) x _"])
  apply (subst inv_add_sequence[symmetric])
  subgoal by simp
  unfolding map_spmf_conv_bind_spmf
  apply simp
  done

lemma S2_def_simplified:
    "S2 x2 yc2 = (do {
       let n = length x2;

       x3 \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       \<pi>a \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
       \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
       \<zeta>a2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       \<zeta>b2::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

       let msg2 = ((\<zeta>a2, \<zeta>b2, yc2), x3, \<pi>a, \<pi>b);
       return_spmf msg2
    })"
  unfolding S2_def

    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
      bind_spmf_sequence_map_share_nat_cong

  apply rule
  apply rule
  apply rule
  apply rule
  apply (rule trans)
  apply (rule bind_spmf_sequence_replicate_cong)

  apply (subst hoist_map_spmf'[where s="sequence_spmf _" and f="\<lambda>x. map2 (-) x _"])
  apply (subst inv_add_sequence[symmetric])
  subgoal by simp
   apply (rule refl)
  apply (unfold map_spmf_conv_bind_spmf)
  apply simp
  apply (subst hoist_map_spmf'[where s="sequence_spmf _" and f="\<lambda>x. map2 (-) x _"])
  apply (subst inv_add_sequence[symmetric])
  subgoal by simp
  apply (unfold map_spmf_conv_bind_spmf)
  apply simp
  done

lemma S3_def_simplified:
    "S3 x3 yc3 = (do {
       let n = length x3;

       \<pi>b \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
       \<pi>c \<leftarrow> spmf_of_set {\<pi>. \<pi> permutes {..<n}};
       ya3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       ya1::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));
       \<zeta>b3::natL list \<leftarrow> sequence_spmf (replicate n (spmf_of_set UNIV));

       let \<zeta>c3 = map2 (-) yc3 (permute_list \<pi>c (map2 (+) \<zeta>b3 (permute_list \<pi>b (map2 (+) ya3 ya1))));
       return_spmf ((ya3, \<zeta>b3, \<zeta>c3), ya1, \<pi>b, \<pi>c)
    })"

  unfolding S3_def

    supply [intro!] =
      bind_spmf_cong[OF refl]
      let_cong[OF refl]
      prod.case_cong[OF refl]
      bind_spmf_sequence_map_cong
      bind_spmf_sequence_replicate_cong
      bind_spmf_permutes_cong
      bind_spmf_sequence_map_share_nat_cong

  apply rule
  apply rule
  apply rule
  apply rule
  apply rule
  apply (subst hoist_map_spmf'[where s="sequence_spmf _" and f="\<lambda>x. map2 (-) x _"])
  apply (subst inv_add_sequence[symmetric])
  subgoal by simp
  apply (unfold map_spmf_conv_bind_spmf)
  apply simp
  done

end
