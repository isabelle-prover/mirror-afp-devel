(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

section "Preliminaries"

text \<open>Some preliminaries on LTL, Transition Systems and Buchi Automata\<close>

subsection "Linear Temporal Logic and Auxillaries"
theory Preliminaries
imports "HOL-Library.Sublist" "HOL-Library.Linear_Temporal_Logic_on_Streams"
"HOL-Library.Code_Target_Int" 
begin

(* PRELIMINARIES *)

definition "any \<equiv> undefined"

lemma Suc_disj:"j < i \<Longrightarrow> Suc j < i \<or> Suc j = i" by auto

(* *)

lemma distinct_wrap_around:
  assumes "distinct c"
  assumes "j > i"
  shows "distinct (drop j c @ take i c)"
proof (subst distinct_append, intro conjI)
  \<comment> \<open>Part 1: Individual segments are distinct\<close>
  show "distinct (drop j c)" 
    using assms(1) distinct_drop by blast
  show "distinct (take i c)" 
    using assms(1) distinct_take by blast

  \<comment> \<open>Part 2: The sets are disjoint\<close>
  show "set (drop j c) \<inter> set (take i c) = {}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> set (drop j c) \<inter> set (take i c)"
    then obtain k m where 
      k: "k < length c" "k \<ge> j" "x = butlast c ! k" and
      m: "m < Suc i" "x = butlast c ! m"
      by (metis assms(1,2) empty_iff inf_commute less_or_eq_imp_le set_take_disj_set_drop_if_distinct)
    
    from k(2) m(1) assms(2) have "m < k" by simp
    hence "m \<noteq> k" by simp
    
    with assms(1) k(1) m(1) have "butlast c ! m \<noteq> butlast c ! k"
      using nth_eq_iff_index_eq[OF assms(1)] 
      
      by (metis \<open>x \<in> set (drop j c) \<inter> set (take i c)\<close> assms(2) empty_iff inf_sup_aci(1) less_or_eq_imp_le
          set_take_disj_set_drop_if_distinct)
      
    thus "x \<in> {}" using k(3) m(2) by simp
  qed simp
qed

lemma distinct_outside_index:
  assumes 
    "0 < j" "0 < length c" "distinct c"
    "\<forall>j<length c. 0 \<noteq> j \<longrightarrow> c ! 0 \<noteq> c ! j"
  shows  "c ! 0 \<notin> (!) c ` {j..<length c}"
proof -
            {
              fix k
              assume "k \<in> {j..<length c}"
              hence "j \<le> k" and "k < length c" by auto
              with \<open>0 < j\<close> have "0 < k" by simp
              with \<open>k < length c\<close> have "c ! 0 \<noteq> c ! k" 
                by (metis assms  length_butlast nat_neq_iff nth_butlast
                    nth_eq_iff_index_eq)
            }
            thus ?thesis by (auto simp: image_def)
          qed 

lemma distinct_outside_index':
  assumes 
    "distinct (butlast c)"
    "Suc i < length (butlast c)"
    "\<forall>j<length (butlast c). Suc i \<noteq> j \<longrightarrow> butlast c ! Suc i \<noteq> butlast c ! j"
  shows "c ! Suc i \<notin> (!) (butlast c) ` {j..<i}"
proof -
            {
              fix k
              assume "k \<in> {j..<i}"
              hence "j \<le> k" and "k < i" by auto
              with assms(1) have "c ! Suc i \<noteq> butlast c ! k" 
                using assms nth_butlast nth_eq_iff_index_eq by fastforce
            }
            thus ?thesis by (auto simp: image_def)
          qed 

(* *)

definition fToList :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where 
"fToList n f \<equiv> map f [0..<n]"

lemma length_fToList[simp]: "length (fToList n f) = n"
unfolding fToList_def by simp

lemma nth_fToList[simp]: "i < n \<Longrightarrow> (fToList n f)!i = f i"
unfolding fToList_def by simp

lemma fToList_nth[simp]: "(fToList (length xs) (nth xs)) = xs"
by (metis length_fToList nth_equalityI nth_fToList)

lemma list_split2: 
assumes "i < j" and "j < length xs"
obtains xs1 xs2 xs3 where "xs = xs1 @ (xs!i) # xs2 @ (xs!j) # xs3"  
proof-
  have 0: "xs = take i xs @ drop i xs" and "xs!i = hd (drop i xs)"
    by simp (metis Suc_lessD assms hd_drop_conv_nth less_trans_Suc)
  have 1: "xs!j = (drop i xs)!(j-i)" apply(subst nth_drop) using assms by auto
  hence 2: "xs!j \<in> set (tl (drop i xs))" 
    by (smt Cons_nth_drop_Suc assms diff_is_0_eq diff_less_mono length_Cons length_drop less_Suc_eq 
     less_imp_le_nat less_trans list.sel(3) not_less nth_equal_first_eq nth_mem set_ConsD)
  thus thesis using that  
  by (metis assms drop_Suc id_take_nth_drop less_trans split_list tl_drop)
qed

(* List obtained by repeating a given list a given number of times: *)
definition repeat :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"repeat n xs \<equiv> concat (replicate n xs)"

lemma repeat_0[simp]: "repeat 0 xs = []"
unfolding repeat_def by simp

lemma repeat_Suc[simp]: "repeat (Suc n) xs = xs @ repeat n xs"
unfolding repeat_def by simp

lemma repeat_Suc2: "repeat (Suc n) xs = repeat n xs @ xs"
unfolding repeat_def by (metis append_self_conv concat.simps(2) concat_append 
  replicate_Suc replicate_append_same)

lemma set_repeat[simp]: "n > 0 \<Longrightarrow> set (repeat n xs) = set xs"
apply(induct n) by fastforce+

lemma nth_repeat[simp]: "length (repeat n xs) = n * length xs"
by (induct n, auto)

lemma repeat_nth: 
"i < n * length xs \<Longrightarrow> repeat n xs ! i = xs ! (i mod length xs)"
apply(induct n arbitrary: i) 
  subgoal by simp
  subgoal for n i apply(cases "i < length xs")
  by (auto simp: nth_append mod_if) .

lemma tl_last':
  "tl xs \<noteq> [] \<Longrightarrow> last xs = last (tl xs)"
by (induct xs) simp_all
(* *)

definition fToStream :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream" where 
"fToStream f \<equiv> smap f nats"

lemma snth_fToStream[simp]: "(fToStream f)!!i = f i"
  unfolding fToStream_def by simp

lemma shd_fToStream[simp]:"shd (fToStream f) = f 0" unfolding fToStream_def by simp

lemma stl_fToStream:"stl (fToStream f) !! n = (fToStream f) !! Suc n" unfolding fToStream_def by simp

lemma fToStream_snth[simp]: "(fToStream (snth xs)) = xs"
by (metis fToStream_def stream_smap_nats)

lemma sdrop_shift_length: "length xs = m \<Longrightarrow> sdrop m (xs @- ys) = ys"
  by (simp add: sdrop_shift)

lemma sdrop_shift_length': "sdrop (length xs) (xs @- ys) = ys"
by (simp add: sdrop_shift)

lemma snth_equalityI: "(\<And>i. xs !! i = ys !! i) \<Longrightarrow> xs = ys"  
  by (metis ext fToStream_snth)

lemma hd_u_append[simp]:"hd (u @ [hd u]) = hd u" by (simp add: hd_append)

lemma stake_len_append:"stake (length v) (v @- u) = v" 
  using stake_shift[of "length v" v u] by auto

lemma last_stake_Suc:"last (stake (Suc x') r) = r !! x'" using last_conv_nth[of "stake (Suc x') r"] gr0_conv_Suc by (auto split: if_splits) 

(* *)

abbreviation "srepeat \<equiv> cycle"
hide_const cycle
declare cycle.simps[simp del]
declare snth.simps[simp del]

lemma stake_srepeat:"(stake (length u) (sdrop 0 (srepeat u))) = u" 
  apply(induct "length u")
  subgoal by auto
  by (metis Zero_not_Suc length_0_conv sdrop.simps(1) stake_cycle_eq)

lemma sdrop_evI: "\<phi> (sdrop m xs) \<Longrightarrow> ev \<phi> xs"
using ev_iff_sdrop by auto

lemma srepeat_snth[simp]: "xs \<noteq> [] \<Longrightarrow> (srepeat xs) !! i = xs!(i mod (length xs))"
apply(induct i) 
  apply (simp add: cycle.simps hd_conv_nth snth.simps)
  by (metis cycle.simps(1) hd_rotate_conv_nth rotate_conv_mod sdrop_cycle sdrop_simps(1))

(* *)

lemma sset_eq_snth: "sset xs = {xs!!i | i . True}"
using sset_range unfolding image_def by (simp add: full_SetCompr_eq sset_range)  
(* *)

lemma repeat_eq_stake_srepeat: 
"repeat n xs = stake (n * length xs) (srepeat xs)"
apply(rule nth_equalityI)
  subgoal by simp
  subgoal by simp (metis list.size(3) mult_0_right not_less0 repeat_nth srepeat_snth) .

lemma repeat_nth_eq_srepeat_snth: "i < n * length xs \<Longrightarrow> repeat n xs ! i = srepeat xs !! i"
by (simp add: repeat_eq_stake_srepeat)

lemma srepeat_repeat: 
"n \<noteq> 0 \<Longrightarrow> srepeat (repeat n xs) = srepeat xs"
apply(cases "xs = []")
  subgoal by (simp add: repeat_eq_stake_srepeat)
  subgoal apply(rule snth_equalityI)  
  apply (subst srepeat_snth)
    subgoal by (simp add: repeat_eq_stake_srepeat)
    subgoal for i apply(subst srepeat_snth)
      subgoal by simp
      subgoal apply(subst repeat_nth)
        subgoal by simp
        subgoal by simp (metis (no_types, lifting) less_not_refl2 mod_mult_right_eq mult_cancel1 mult_mod_right) 
        . . . .

(* *)
lemma last_replicate_app: "k>0 \<Longrightarrow> last (concat (replicate k (ls @ [l']))) = l'" by(induct k, auto)

lemma last_stake_Suc_app:"last (p # stake (Suc x') r) = last (stake (Suc x') r)" by simp


lemma upt_Suc_hd:"Suc x' \<le> y' \<Longrightarrow> ([Suc x'..<y'] @ [y']) ! 0 = Suc x'" 
  unfolding le_eq_less_or_eq using upt_rec apply-by(erule disjE, auto) 


lemma stl_Suc_eq:"stl r !! k = r !! Suc k" by (simp add: snth.simps(2))

lemma stl_Suc:"k>0 \<Longrightarrow> stl r !! (k - Suc 0) = r !! k" by(induct k, simp_all add: stl_Suc_eq)
lemma stl_Suc':"k>0 \<Longrightarrow> stl r !! (k - 1) = r !! k" by(induct k, simp_all add: stl_Suc_eq)
lemma replicate_within_i:"(Suc i) \<le> m \<Longrightarrow> (replicate m s @- x) !! i = s" by(induction "(Suc i) - m" arbitrary: i, simp_all)

lemma replicate_beyond_i:"(Suc i) > m \<Longrightarrow> (replicate m s @- x) !! i = x !! (i-m)" by(induction "(Suc i) - m" arbitrary: i, simp_all)

lemma last_stake_i:"n > 0 \<Longrightarrow> last (stake n x) = x !! (n-1)" using last_conv_nth[of "stake n x"] by auto 
lemma last_stake_replicate:"(Suc i) \<le> m \<Longrightarrow> 0 < i  \<Longrightarrow> last (stake i (replicate m s @- x)) = s" 
  using last_conv_nth[of "stake i (replicate m s @- x)"] by simp


lemma Suc_leq:"Suc (Suc n) \<le> m \<Longrightarrow> n \<le> m-Suc (Suc 0)" by auto


(**)

lemma alw_ev_iff_sdrop: "alw (ev \<phi>) xs = (\<forall>m. \<exists>n\<ge>m. \<phi> (sdrop n xs))"
unfolding alw_iff_sdrop ev_iff_sdrop sdrop_add  
using nat_le_iff_add by force

lemma ev_alw_iff_sdrop: "ev (alw \<phi>) xs = (\<exists>m. \<forall>n\<ge>m. \<phi> (sdrop n xs))"
unfolding alw_iff_sdrop ev_iff_sdrop sdrop_add  
using nat_le_iff_add by force

lemma ev_alw_ev_iff_sdrop: "ev (alw (ev \<phi>)) xs = (\<exists>l. \<forall>m\<ge>l. \<exists>n\<ge>m. \<phi> (sdrop n xs))"
unfolding alw_iff_sdrop ev_iff_sdrop sdrop_add  
using nat_le_iff_add by force

lemma "ev (alw (ev \<phi>)) xs \<longleftrightarrow> alw (ev \<phi>) xs" 
using ev.base ev_alw_imp_alw_ev by fastforce

lemma alw_ev_sdrop: "alw (ev \<phi>) (sdrop m xs) \<longleftrightarrow> alw (ev \<phi>) xs"
by (metis alw_ev_sdrop alw_sdrop)

lemma ev_alw_sdrop: "ev (alw \<phi>) (sdrop m xs) \<longleftrightarrow> ev (alw \<phi>) xs"  
by (metis alw.cases alw_alw ev_alw_imp_alw_ev alw_ev_sdrop) 

lemma ev_alw_aand_alw_ev_sdrop: 
"(ev (alw \<phi>) aand alw (ev \<psi>)) (sdrop m xs) \<longleftrightarrow> (ev (alw \<phi>) aand alw (ev \<psi>)) xs"
by (simp add: ev_alw_sdrop alw_ev_sdrop)

(* *)



fun holds2 where "holds2 P xs \<longleftrightarrow> P (shd xs) (shd (stl xs))"

fun second where "second (a,b,c) = b"
lemma second':"second x = (case x of (a, b, c) \<Rightarrow> b)" by (cases x) auto

fun third where "third (a,b,c) = c"
lemma third':"third x = (case x of (a, b, c) \<Rightarrow> c)" by (cases x) auto

lemma third_ssnd:"third = (\<lambda>x. snd (snd x))" by auto

lemma third_snd:"(third \<circ> snd) = (\<lambda>x. third (snd x))" by auto
lemma stake_replicate:"stake n (replicate n X @- S) = replicate n X" by(induct n, auto)

lemma sdrop_replicate:"sdrop n (replicate n X @- S) = S" by(induct n, auto)

definition "holdsS S = holds (\<lambda>x. x \<in> S)"

(* *)

lemma alw_holds_iff_snth: "alw (holds P) xs \<longleftrightarrow> (\<forall>i. P(xs!!i))"
unfolding alw_iff_sdrop by auto

lemma alw_holdsS_iff_snth: "alw (holdsS S) xs \<longleftrightarrow> (\<forall>i. xs!!i \<in> S)"
by (simp add: alw_holds_iff_snth holdsS_def)

lemma alw_holds2_iff_snth: "alw (holds2 R) xs \<longleftrightarrow> (\<forall>i. R (xs!!i) (xs!!(Suc i)))"
unfolding alw_iff_sdrop by (auto simp: snth.simps)

(* *)
lemma ev_holds_iff_snth: "ev (holds P) xs \<longleftrightarrow> (\<exists>i. P(xs!!i))"
unfolding ev_iff_sdrop by auto

lemma ev_holdsS_iff_snth: "ev (holdsS S) xs \<longleftrightarrow> (\<exists>i. xs!!i \<in> S)"
by (simp add: ev_holds_iff_snth holdsS_def)

lemma ev_holds2_iff_snth: "ev (holds2 R) xs \<longleftrightarrow> (\<exists>i. R (xs!!i) (xs!!(Suc i)))"
unfolding ev_iff_sdrop by (auto simp: snth.simps)

(* *)

lemma alw_ev_holds_iff_snth: "alw (ev (holds P)) xs \<longleftrightarrow> (\<forall>i. \<exists>j\<ge>i. P(xs!!j))"
unfolding alw_ev_iff_sdrop by auto

lemma alw_ev_holdsS_iff_snth: "alw (ev (holdsS S)) xs \<longleftrightarrow> (\<forall>i. \<exists>j\<ge>i. xs!!j \<in> S)"
by (simp add: alw_ev_holds_iff_snth holdsS_def)

lemma alw_ev_holds2_iff_snth: "alw (ev (holds2 R)) xs \<longleftrightarrow> (\<forall>i. \<exists>j\<ge>i. R (xs!!j) (xs!!(Suc j)))"
unfolding alw_ev_iff_sdrop by (auto simp: snth.simps)

(* *)

lemma ev_alw_holds_iff_snth: "ev (alw (holds P)) xs \<longleftrightarrow> (\<exists>i. \<forall>j\<ge>i. P(xs!!j))"
unfolding ev_alw_iff_sdrop by auto

lemma ev_alw_holdsS_iff_snth: "ev (alw (holdsS S)) xs \<longleftrightarrow> (\<exists>i. \<forall>j\<ge>i. xs!!j \<in> S)"
by (simp add: ev_alw_holds_iff_snth holdsS_def)

lemma ev_alw_holds2_iff_snth: "ev (alw (holds2 R)) xs \<longleftrightarrow> (\<exists>i. \<forall>j\<ge>i. R (xs!!j) (xs!!(Suc j)))"
unfolding ev_alw_iff_sdrop by (auto simp: snth.simps)

lemma ev_alw_holds2_aand_holdsS_iff_snth: 
"ev (alw (holdsS S aand holds2 R)) xs \<longleftrightarrow> (\<exists>i. \<forall>j\<ge>i. xs!!j \<in> S \<and> R (xs!!j) (xs!!(Suc j)))"
unfolding ev_alw_iff_sdrop by (simp add: ev_alw_holds_iff_snth holdsS_def snth.simps)

(* *)

lemma nat_cases:"(x::nat) = y \<or> y < x \<or> y > x" by auto

lemma snth_hd_app_eq[simp]:"(x ## xs) !! 0 = x" unfolding snth.simps by auto
lemma stream_inclI:"x \<in> S \<Longrightarrow> k>0 \<longrightarrow> xs!!(k-1) \<in> S \<Longrightarrow> (x ## xs)!!k \<in> S" by(cases k, auto simp: snth_Stream)
lemma sdrop_1:"(sdrop (Suc 0) nds) = stl nds" by simp


(*Modulo arithmetic results*)

lemma disj_mod:"((k::nat) div N = 0 \<and> k mod N = 0) \<or> (0 < k div N \<and> k mod N = 0) \<or> (0 < k mod N)"
  by auto

lemma mod_bound:"y' > x' \<Longrightarrow> k mod (y' - x') - Suc 0 < Suc y' - Suc x'"
  by (simp add: less_imp_diff_less)

lemma mod_contr1: assumes "k mod (y' - x') = Suc l'" 
              "y' < Suc (l' + x') " "y'-x' \<noteq> 0" 
     shows "HOL.False" 
proof -
  have "Suc l' < y' - x'" using assms(1) by (metis assms(3) mod_less_divisor neq0_conv) 
  also have "y' - x' < Suc l'" using assms(2) by auto
  ultimately show "HOL.False" by simp
qed

lemma mod_contr2: assumes "k mod (y' - x') = Suc l'"  "y' = Suc (l' + x') " "y'-x' \<noteq> 0" 
     shows "HOL.False" 
proof -
  have "Suc l' = y' - x'" using assms by auto
  also have "k mod (Suc l')  = Suc l'" using assms by auto
  ultimately show "HOL.False" by (metis Zero_not_Suc mod_mod_trivial mod_self)
qed

lemma mod_contr3:
  assumes "y' < k mod (y' - x') + x'" "Suc x' < y'"
  shows "HOL.False"
proof -
  obtain q where "q = k div (y'-x')"
    using assms  by simp
  hence "k = q * (y'-x') +k mod (y' - x')"
    using assms  by presburger

  define r where "r = k mod (y' - x')"
  then have "0\<le> r" "r < y' -x'" apply blast unfolding r_def using pos_mod_bound assms by auto
  also have y_le: "y' < r + x'" using assms unfolding r_def by auto
  ultimately have r_leq:"r + x' \<le> (y'-x'-1) + x'" by auto
  have "y' - x' - 1 + x' = y' -1" 
    using \<open>r < y' - x'\<close> less_diff_conv y_le by fastforce

  hence "y' < y' -1" using y_le r_leq by auto
  thus "HOL.False" by auto
qed

lemma mod_arith1:assumes "Suc x' < y'"
  shows "Suc (k mod (y' - x') + x') \<le> y'" 
        "(k mod (y' - x')) \<le> y' - Suc x'" 
        "Suc x' + k mod (y' - x') < Suc y'"
proof - 
  have "x' < y' - 1" using assms by auto
  hence "y'-x' > 0" by auto
  also have "0\<le> k mod (y' - x')" "k mod (y' - x') < y' - x'" 
    using calculation mod_less_divisor by blast+
  moreover have "x' \<le> k mod (y' - x') + x'" "k mod (y' - x') + x' < y'" 
    using calculation(3) less_diff_conv by auto

  thus "Suc (k mod (y' - x') + x') \<le> y'" "k mod (y' - x') \<le> y' - Suc x'" 
        "Suc x' + k mod (y' - x') < Suc y'" by auto
qed

lemma le_xy_mod:"(x'::nat) < y' \<Longrightarrow> k mod (y' - x') < y' - x'" by(cases k, auto)

(**)

(*A list of indexes between i and j-1 from a stream *)

definition "map_ind x i j \<equiv> map ((!!) x) [i..<j]"

lemma map_ind_ne[simp]:"i < j \<Longrightarrow> map_ind x i j \<noteq>[]" unfolding map_ind_def by(cases j, auto)

lemma map_ind_len[simp]:"i < j \<Longrightarrow> length (map_ind x i j) = j-i"unfolding map_ind_def  by auto 

lemma srepeat_map_ind_eq:"i < j\<Longrightarrow> srepeat (map_ind x i j) !! k = x !! ([i..<j] ! (k mod (j - i)))"
  using srepeat_snth[OF map_ind_ne, of i j x k]  unfolding map_ind_def by auto

lemma hd_map_ind:"i < j \<Longrightarrow> hd (map_ind x i j) = x !! i" unfolding map_ind_def using list.map_sel(1)[of "[i..<j]"] by auto


lemma map_ind_sing[simp]:"map_ind r i (Suc i) = [r !! i]"
  unfolding map_ind_def by auto

lemma tl_map_ind:"i < j \<Longrightarrow>tl (map_ind x i j) = (map_ind x (Suc i) j)"
    apply(cases "map ((!!) x) [i..<j]")
    subgoal using map_ind_ne by auto
    subgoal using tl_upt[of i j] unfolding map_ind_def by fastforce .

lemma nth_map_ind: "k < j-i \<Longrightarrow> (map_ind x i j) ! k = x !! (i+k)"
  using nth_map_upt[of k j i "(!!) x"] unfolding map_ind_def by auto

lemma map_ind_Suc:"y'\<ge>x' \<Longrightarrow> map_ind r x' y' @ [r !! y'] = map_ind r x' (Suc y')"
  unfolding map_ind_def by auto

lemma last_replicate_map_ind:"0 < k \<Longrightarrow> y'\<ge>x' \<Longrightarrow> last (concat (replicate k (map_ind r x' (Suc y')))) = r !! y'"
  using last_replicate_app[of k "map_ind r x' y'" "r!! y'"] map_ind_Suc[of x' y' r] by auto


lemma srepeat_map_ind_snth_eq:"i < j \<Longrightarrow> srepeat (map_ind x i j) !! k = x !! (i + k mod (j - i))"
  unfolding srepeat_snth[OF map_ind_ne] map_ind_len nth_map_ind[OF le_xy_mod] by auto

lemma last_take_Suc':"k = Suc n \<Longrightarrow> last (stake k r) =  r !! n" 
  apply(cases n)
  subgoal by (simp add: snth.simps(1))
  using last_stake_Suc by blast

(**)

lemma two_ls_app:"[y, v] = [y] @ [v]" by auto

lemma list_unf:"(v # xs' @ [y]) @ z' # zs' @ [v] = v # xs' @ y # z' # zs' @ [v]" by simp


lemma set_nemp:"V' \<noteq> {} \<longleftrightarrow> (\<exists>v. v \<in> V')" by auto


lemma exI2:"P a b \<Longrightarrow> \<exists>a b. P a b" by auto
lemma exI3:"P a b c \<Longrightarrow> \<exists>a b c. P a b c" by auto
lemma exI4:"P a b c d \<Longrightarrow> \<exists>a b c d. P a b c d" by auto

lemma exI5:"P a b c d e \<Longrightarrow> \<exists>a b c d e. P a b c d e" by(rule exI4[of _ a b c d], auto)

end 