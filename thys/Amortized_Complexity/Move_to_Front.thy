section "Online Algorithms and List Update"

theory Move_to_Front
imports Complex_Main Inversion
begin

declare Let_def[simp]

subsection "Function @{text mtf}"

definition "mtf x xs =
  (if x \<in> set xs then x # (take (index xs x) xs) @ drop (index xs x + 1) xs
   else xs)"

lemma mtf_id[simp]: "x \<notin> set xs \<Longrightarrow> mtf x xs = xs"
by(simp add: mtf_def)

lemma mtf0[simp]: "x \<in> set xs \<Longrightarrow> mtf x xs ! 0 = x"
by(auto simp: mtf_def)

lemma before_in_mtf: assumes "z \<in> set xs"
shows "x < y in mtf z xs  \<longleftrightarrow>
      (y \<noteq> z \<and> (if x=z then y \<in> set xs else x < y in xs))"
proof-
  have 0: "index xs z < size xs" by (metis assms index_less_size_conv)
  let ?xs = "take (index xs z) xs @ xs ! index xs z # drop (Suc (index xs z)) xs"
  have "x < y in mtf z xs = (y \<noteq> z \<and> (if x=z then y \<in> set ?xs else x < y in ?xs))"
    using assms
    by(auto simp add: mtf_def before_in_def index_append)
      (metis add_lessD1 index_less_size_conv length_take less_Suc_eq not_less_eq)
  with id_take_nth_drop[OF 0, symmetric] show ?thesis by(simp)
qed

lemma Inv_mtf: "set xs = set ys \<Longrightarrow> z : set ys \<Longrightarrow> Inv xs (mtf z ys) =
 Inv xs ys \<union> {(x,z)|x. x < z in xs \<and> x < z in ys}
 - {(z,x)|x. z < x in xs \<and> x < z in ys}"
by(auto simp add: Inv_def before_in_mtf not_before_in dest: before_in_setD1)

lemma set_mtf[simp]: "set(mtf x xs) = set xs"
by(simp add: mtf_def)
  (metis append_take_drop_id Cons_nth_drop_Suc index_less le_refl Un_insert_right nth_index set_append set_simps(2))

lemma length_mtf[simp]: "size (mtf x xs) = size xs"
by (auto simp add: mtf_def min_def) (metis index_less_size_conv leD)

lemma distinct_mtf[simp]: "distinct (mtf x xs) = distinct xs"
by (metis length_mtf set_mtf card_distinct distinct_card)


subsection "Function @{text swapSuc}"

definition "swapSuc n xs =
  (if Suc n < size xs then xs[n := xs!Suc n, Suc n := xs!n] else xs)"

lemma length_swapSuc[simp]: "length(swapSuc i xs) = length xs"
by(simp add: swapSuc_def)

lemma swapSuc_id[simp]: "Suc n \<ge> size xs \<Longrightarrow> swapSuc n xs = xs"
by(simp add: swapSuc_def)

lemma distinct_swapSuc[simp]:
  "distinct(swapSuc i xs) = distinct xs"
by(simp add: swapSuc_def)

lemma swapSuc_Suc[simp]: "swapSuc (Suc n) (a # xs) = a # swapSuc n xs"
by(induction xs) (auto simp: swapSuc_def)

lemma index_swapSuc_distinct:
  "distinct xs \<Longrightarrow> Suc n < length xs \<Longrightarrow>
  index (swapSuc n xs) x =
  (if x = xs!n then Suc n else if x = xs!Suc n then n else index xs x)"
by(auto simp add: swapSuc_def index_swap_if_distinct)

lemma set_swapSuc[simp]: "set(swapSuc n xs) = set xs"
by(auto simp add: swapSuc_def set_conv_nth nth_list_update) metis

lemma nth_swapSuc_id[simp]: "Suc i < length xs \<Longrightarrow> swapSuc i xs ! i = xs!(i+1)"
by(simp add: swapSuc_def)

lemma before_in_swapSuc:
 "dist_perm xs ys \<Longrightarrow> Suc n < size xs \<Longrightarrow>
  x < y in (swapSuc n xs) \<longleftrightarrow>
  x < y in xs \<and> \<not> (x = xs!n \<and> y = xs!Suc n) \<or> x = xs!Suc n \<and> y = xs!n"
by(simp add:before_in_def index_swapSuc_distinct)
  (metis Suc_lessD Suc_lessI index_less_size_conv index_nth_id less_Suc_eq n_not_Suc_n nth_index)

lemma Inv_swap: assumes "dist_perm xs ys"
shows "Inv xs (swapSuc n ys) = 
  (if Suc n < size xs
   then if ys!n < ys!Suc n in xs
        then Inv xs ys \<union> {(ys!n, ys!Suc n)}
        else Inv xs ys - {(ys!Suc n, ys!n)}
   else Inv xs ys)"
proof-
  have "length xs = length ys" using assms by (metis distinct_card)
  with assms show ?thesis
    by(simp add: Inv_def set_eq_iff)
      (metis before_in_def not_before_in before_in_swapSuc)
qed


abbreviation swapSucs where "swapSucs == foldr swapSuc"

lemma swapSucs_inv[simp]:
  "set (swapSucs sws xs) = set xs \<and>
  size(swapSucs sws xs) = size xs \<and>
  distinct(swapSucs sws xs) = distinct xs"
by (induct sws arbitrary: xs) (simp_all add: swapSuc_def)

lemma swapSucs_eq_Nil_iff[simp]: "swapSucs acts xs = [] \<longleftrightarrow> xs = []"
by(induction acts)(auto simp: swapSuc_def)

lemma swapSucs_map_Suc[simp]:
  "swapSucs (map Suc sws) (a # xs) = a # swapSucs sws xs"
by(induction sws arbitrary: xs) auto

lemma card_Inv_swapSucs_le:
  "distinct xs \<Longrightarrow> card (Inv xs (swapSucs sws xs)) \<le> length sws"
by(induction sws) (auto simp: Inv_swap card_insert_if card_Diff_singleton_if)

lemma nth_swapSucs: "\<forall>i\<in>set is. j < i \<Longrightarrow> swapSucs is xs ! j = xs ! j"
by(induction "is")(simp_all add: swapSuc_def)

lemma not_before0[simp]: "~ x < xs ! 0 in xs"
apply(cases "xs = []")
by(auto simp: before_in_def neq_Nil_conv)

lemma before_id[simp]: "\<lbrakk> distinct xs; i < size xs; j < size xs \<rbrakk> \<Longrightarrow>
  xs ! i < xs ! j in xs \<longleftrightarrow> i < j"
by(simp add: before_in_def index_nth_id)

lemma before_swapSucs:
  "\<lbrakk> distinct is; \<forall>i\<in>set is. Suc i < size xs; distinct xs; i \<notin> set is; i < j; j < size xs \<rbrakk> \<Longrightarrow>
  swapSucs is xs ! i < swapSucs is xs ! j in xs"
apply(induction "is" arbitrary: i j)
 apply simp
apply(auto simp: swapSuc_def nth_list_update)
done

lemma card_Inv_swapSucs:
  "\<lbrakk> distinct is; \<forall>i\<in>set is. Suc i < size xs; distinct xs \<rbrakk> \<Longrightarrow>
  card(Inv xs (swapSucs is xs)) = length is"
apply(induction "is")
 apply simp
apply(simp add: Inv_swap before_swapSucs card_insert_if)
apply(simp add: Inv_def)
done

subsection "Function @{text mtf2}"

definition mtf2 :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"mtf2 n x xs = (if x : set xs then swapSucs [index xs x - n..<index xs x] xs else xs)"

lemma length_mtf2[simp]: "length (mtf2 n x xs) = length xs"
by (auto simp: mtf2_def index_less_size_conv[symmetric]
  simp del:index_conv_size_if_notin)

lemma set_mtf2[simp]: "set(mtf2 n x xs) = set xs"
by (auto simp: mtf2_def index_less_size_conv[symmetric]
  simp del:index_conv_size_if_notin)

lemma distinct_mtf2[simp]: "distinct (mtf2 n x xs) = distinct xs"
by (metis length_mtf2 set_mtf2 card_distinct distinct_card)


lemma card_Inv_mtf2: "xs!j = ys!0 \<Longrightarrow> j < length xs \<Longrightarrow> dist_perm xs ys \<Longrightarrow>
   card (Inv (swapSucs [i..<j] xs) ys) = card (Inv xs ys) - int(j-i)"
proof(induction j arbitrary: xs)
  case (Suc j)
  show ?case
  proof cases
    assume "i > j" thus ?thesis by simp
  next
    assume [arith]: "\<not> i > j"
    have 0: "Suc j < length ys" by (metis Suc.prems(2,3) distinct_card)
    have 1: "(ys ! 0, xs ! j) : Inv ys xs"
    proof (auto simp: Inv_def)
      show "ys ! 0 < xs ! j in ys" using Suc.prems
        by (metis Suc_lessD n_not_Suc_n not_before0 not_before_in nth_eq_iff_index_eq nth_mem)
      show "xs ! j < ys ! 0 in xs" using Suc.prems
        by (metis Suc_lessD before_id lessI)
    qed
    have 2: "card(Inv ys xs) \<noteq> 0" using 1 by auto
    have "int(card (Inv (swapSucs [i..<Suc j] xs) ys)) =
          card (Inv (swapSuc j xs) ys) - int (j-i)" using Suc by simp
    also have "\<dots> = card (Inv ys (swapSuc j xs)) - int (j-i)"
      by(simp add: card_Inv_sym)
    also have "\<dots> = card (Inv ys xs - {(ys ! 0, xs ! j)}) - int (j - i)"
      using Suc.prems 0 by(simp add: Inv_swap)
    also have "\<dots> = int(card (Inv ys xs) - 1) - (j - i)"
      using 1 by(simp add: card_Diff_singleton)
    also have "\<dots> = card (Inv ys xs) - int (Suc j - i)" using 2 by arith
    also have "\<dots> = card (Inv xs ys) - int (Suc j - i)" by(simp add: card_Inv_sym)
    finally show ?thesis .
  qed
qed simp


subsection "Function @{text mtf1}"

definition "mtf1 x xs = mtf2 (length xs) x xs"

lemma swapSucs_eq_nth_take_drop: "i < length xs \<Longrightarrow>
    swapSucs [0..<i] xs = xs!i # take i xs @ drop (Suc i) xs"
apply(induction i arbitrary: xs)
apply (auto simp add: neq_Nil_conv swapSuc_def drop_update_swap
  take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric])
done

lemma mtf1_eq_mtf: "mtf1 x xs = mtf x xs"
by(auto simp: mtf1_def mtf_def mtf2_def swapSucs_eq_nth_take_drop index_le_size)


subsection "Locales for Online/Offline Algorithms"

locale On_Off =
fixes step :: "'state \<Rightarrow> 'query \<Rightarrow> 'action \<Rightarrow> 'state"
fixes t :: "'state \<Rightarrow> 'query \<Rightarrow> 'action \<Rightarrow> nat"
begin

type_synonym ('s,'q,'a)alg_off = "'s \<Rightarrow> 'q list \<Rightarrow> 'a list"
type_synonym ('s,'q,'a)alg_on = "'q list \<Rightarrow> 's \<Rightarrow> 'q \<Rightarrow> 'a"

fun T :: "'state \<Rightarrow> 'query list \<Rightarrow> 'action list \<Rightarrow> nat" where
"T s [] [] = 0" |
"T s (q#qs) (a#as) = t s q a + T (step s q a) qs as"

fun off :: "('state,'query,'action) alg_on \<Rightarrow> 'query list \<Rightarrow> ('state,'query,'action) alg_off" where
"off A h s [] = []" |
"off A h s (q#qs) = A h s q # off A (q#h) (step s q (A h s q)) qs"

abbreviation T_off :: "('state,'query,'action) alg_off \<Rightarrow> 'state \<Rightarrow> 'query list \<Rightarrow> nat" where
"T_off A init qs == T init qs (A init qs)"

abbreviation T_on :: "('state,'query,'action) alg_on \<Rightarrow> 'query list \<Rightarrow> 'state \<Rightarrow> 'query list \<Rightarrow> nat" where
"T_on A h == T_off (off A h)"

definition T_opt :: "'state \<Rightarrow> 'query list \<Rightarrow> nat" where
"T_opt s qs = Inf {T s qs as | as. size as = size qs}"

definition compet :: "('state,'query,'action) alg_on \<Rightarrow> real \<Rightarrow> 'state set \<Rightarrow> bool" where
"compet A c S0 = (\<exists>b \<ge> 0. \<forall>s0\<in>S0. \<forall>qs. real(T_on A [] s0 qs) \<le> c * T_opt s0 qs + b)"

lemma length_off[simp]: "length(off A h s qs) = length qs"
by (induction qs arbitrary: h s) auto

lemma compet_mono: assumes "compet A c S0" and "c \<le> c'"
shows "compet A c' S0"
proof-
  let ?compt = "\<lambda>s0 qs b (c::real). T_on A [] s0 qs \<le> c * T_opt s0 qs + b"
  from assms(1) obtain b where "b \<ge> 0" and 1: "\<forall>s0\<in>S0. \<forall>qs. ?compt s0 qs b c"
    by(auto simp: compet_def)
  { fix s0 qs assume "s0 \<in> S0"
    hence "?compt s0 qs b c" using 1 by auto
    hence "?compt s0 qs b c'"
      using mult_right_mono[OF assms(2) real_of_nat_ge_zero[of "T_opt s0 qs"]]
      by arith }
  thus ?thesis using `b\<ge>0` by(auto simp add: compet_def)
qed

lemma competE: fixes c :: real
assumes "compet A c S0" "c \<ge> 0" "\<forall>s0 qs. size(aoff s0 qs) = length qs"
shows "\<exists>b\<ge>0. \<forall>s0\<in>S0. \<forall>qs. T_on A [] s0 qs \<le> c * T_off aoff s0 qs + b"
proof -
  from assms(1) obtain b where "b\<ge>0" and
    1: "\<forall>s0\<in>S0. \<forall>qs. T_on A [] s0 qs \<le> c * T_opt s0 qs + b"
    by(auto simp add: compet_def)
  { fix s0 qs assume "s0 \<in> S0"
    hence 2: "real(T_on A [] s0 qs) \<le> c * Inf {T s0 qs as | as. size as = size qs} + b"
      (is "_ \<le> _ * real(Inf ?T) + _")
      using 1 by(auto simp add: T_opt_def)
    have "Inf ?T \<le> T_off aoff s0 qs"
      using assms(3) by (intro cInf_lower) auto
    from mult_left_mono[OF real_of_nat_le_iff[THEN iffD2, OF this] assms(2)]
    have "T_on A [] s0 qs \<le> c * T_off aoff s0 qs + b" using 2 by arith
  }
  thus ?thesis using `b\<ge>0` by(auto simp: compet_def)
qed

end


subsection "List Update as Online/Offline Algorithm"

lemma mtf20[simp]: "mtf2 0 x xs = xs"
by(auto simp add: mtf2_def)


type_synonym 'a state = "'a list"
type_synonym 'a action = "nat * nat list"

definition step :: "'a state \<Rightarrow> 'a \<Rightarrow> 'a action \<Rightarrow> 'a state" where
"step s q a =
  (let (k,sws) = a in mtf2 k q (swapSucs sws s))"

definition t :: "'a state \<Rightarrow> 'a \<Rightarrow> 'a action \<Rightarrow> nat" where
"t s q a = (let (mf,sws) = a in index (swapSucs sws s) q + 1 + size sws)"

interpretation On_Off step t .

type_synonym 'a alg_off = "'a state \<Rightarrow> 'a list \<Rightarrow> 'a action list"
type_synonym 'a alg_on = "'a list \<Rightarrow> 'a state \<Rightarrow> 'a \<Rightarrow> 'a action"

lemma T_ge_len: "length as = length qs \<Longrightarrow> T s qs as \<ge> length qs"
by(induction arbitrary: s rule: list_induct2)
  (auto simp: t_def trans_le_add2)

lemma T_off_neq0: "(\<And>qs s0. size(alg s0 qs) = length qs) \<Longrightarrow>
  qs \<noteq> [] \<Longrightarrow> T_off alg s0 qs \<noteq> 0"
apply(erule_tac x=qs in meta_allE)
apply(erule_tac x=s0 in meta_allE)
apply (auto simp: neq_Nil_conv length_Suc_conv t_def)
done

lemma length_step[simp]: "length (step s q as) = length s"
by(simp add: step_def split_def)

lemma step_Nil_iff[simp]: "step xs q act = [] \<longleftrightarrow> xs = []"
by(auto simp add: step_def mtf2_def split: prod.splits)

lemma set_step2: "\<forall>n \<in> set sws. n+1 < length s \<Longrightarrow> set(step s q (mf,sws)) = set s"
by(auto simp add: step_def)

lemma set_step: "\<forall>n \<in> set(snd act). n+1 < length s \<Longrightarrow> set(step s q act) = set s"
by(cases act)(simp add: set_step2)

lemma distinct_step: "s \<noteq> [] \<Longrightarrow> distinct(step s q as) = distinct s"
by (auto simp: step_def split_def)


subsection "Online Algorithm Move-to-Front is 2-Competitive"

definition MTF :: "'a list \<Rightarrow> 'a state \<Rightarrow> 'a \<Rightarrow> 'a action" where
"MTF h s q = (size s,[])"

text{* It was first proved by Sleator and Tarjan~\cite{SleatorT-CACM85} that
the Move-to-Front algorithm is 2-competitive. *}

(* The core idea with upper bounds: *)
lemma potential:
fixes t :: "nat \<Rightarrow> 'a::linordered_ab_group_add" and p :: "nat \<Rightarrow> 'a"
assumes p0: "p 0 = 0" and ppos: "\<And>n. p n \<ge> 0"
and ub: "\<And>n. t n + p(n+1) - p n \<le> u n"
shows "(\<Sum>i<n. t i) \<le> (\<Sum>i<n. u i)"
proof-
  let ?a = "\<lambda>n. t n + p(n+1) - p n"
  have 1: "(\<Sum>i<n. t i) = (\<Sum>i<n. ?a i) - p(n)"
    by(induction n) (simp_all add: p0)
  thus ?thesis
    by (metis (erased, lifting) add.commute diff_add_cancel le_add_same_cancel2 order.trans ppos setsum_mono ub)
qed

abbreviation "before x xs \<equiv> {y. y < x in xs}"
abbreviation "after x xs \<equiv> {y. x < y in xs}"

lemma finite_before[simp]: "finite (before x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD1)
done

lemma finite_after[simp]: "finite (after x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD2)
done

lemma before_conv_take:
  "x : set xs \<Longrightarrow> before x xs = set(take (index xs x) xs)"
by (auto simp add: before_in_def set_take_if_index index_le_size) (metis index_take leI)

lemma card_before: "distinct xs \<Longrightarrow> x : set xs \<Longrightarrow> card (before x xs) = index xs x"
using  index_le_size[of xs x]
by(simp add: before_conv_take distinct_card[OF distinct_take] min_def)

lemma before_Un: "set xs = set ys \<Longrightarrow> x : set xs \<Longrightarrow>
  before x ys = before x xs \<inter> before x ys Un after x xs \<inter> before x ys"
by(auto)(metis before_in_setD1 not_before_in)

lemma phi_diff_aux:
  "card (Inv xs ys \<union>
             {(y, x) |y. y < x in xs \<and> y < x in ys} -
             {(x, y) |y. x < y in xs \<and> y < x in ys}) =
   card(Inv xs ys) + card(before x xs \<inter> before x ys)
   - int(card(after x xs \<inter> before x ys))"
  (is "card(?I \<union> ?B - ?A) = card ?I + card ?b - int(card ?a)")
proof-
  have 1: "?I \<inter> ?B = {}" by(auto simp: Inv_def) (metis no_before_inI)
  have 2: "?A \<subseteq> ?I \<union> ?B" by(auto simp: Inv_def)
  have 3: "?A \<subseteq> ?I" by(auto simp: Inv_def)
  have "int(card(?I \<union> ?B - ?A)) = int(card ?I + card ?B) - int(card ?A)"
    using  card_mono[OF _ 3]
    by(simp add: card_Un_disjoint[OF _ _ 1] card_Diff_subset[OF _ 2])
  also have "card ?B = card (fst ` ?B)" by(auto simp: card_image inj_on_def)
  also have "fst ` ?B = ?b" by force
  also have "card ?A = card (snd ` ?A)" by(auto simp: card_image inj_on_def)
  also have "snd ` ?A = ?a" by force
  finally show ?thesis .
qed

lemma not_before_Cons[simp]: "\<not> x < y in y # xs"
by (simp add: before_in_def)

lemma before_Cons[simp]:
  "q \<in> set xs \<Longrightarrow> q \<noteq> x \<Longrightarrow> before q (x#xs) = insert x (before q xs)"
by(auto simp: before_in_def)

lemma card_before_le_index: "card (before q xs) \<le> index xs q"
apply(cases "q \<in> set xs")
 prefer 2 apply (simp add: before_in_def)
apply(induction xs)
 apply (simp add: before_in_def)
apply (auto simp: card_insert_if)
done

(*fixme start from Inv*)

lemma amor_mtf_ub: assumes "q : set ys" "set xs = set ys"
shows "int(card(before q xs Int before q ys)) - card(after q xs Int before q ys)
  \<le> 2 * int(index xs q) - card (before q ys)" (is "?m - ?n \<le> 2 * ?j - ?k")
proof-
  have qxs: "q \<in> set xs" using assms(1,2) by simp
  let ?bqxs = "before q xs" let ?bqys = "before q ys" let ?aqxs = "after q xs"
  have 0: "?bqxs \<inter> ?aqxs = {}" by (auto simp: before_in_def)
  hence 1: "(?bqxs \<inter> ?bqys) \<inter> (?aqxs \<inter> ?bqys) = {}" by blast
  have "(?bqxs \<inter> ?bqys) \<union> (?aqxs \<inter> ?bqys) = ?bqys"
    using assms(2) before_Un qxs by fastforce
  hence "?m + ?n = ?k"
    using card_Un_disjoint[OF _ _ 1] by(simp add: zadd_int del: of_nat_add)
  hence "?m - ?n = 2 * ?m - ?k" by arith
  also have "?m \<le> ?j"
    using card_before_le_index[of q xs] card_mono[of ?bqxs, OF _ Int_lower1]
    by(auto intro: order_trans)
  finally show ?thesis by auto
qed

locale MTF_Off =
fixes acts :: "'a action list"
fixes qs :: "'a list"
fixes init :: "'a list"
assumes dist_init[simp]: "distinct init"
assumes len_acts: "length acts = length qs"
begin

definition mtf_A :: "nat list" where
"mtf_A = map fst acts"

definition sw_A :: "nat list list" where
"sw_A = map snd acts"

fun s_A :: "nat \<Rightarrow> 'a list" where
"s_A 0 = init" |
"s_A(Suc n) = step (s_A n) (qs!n) (mtf_A!n, sw_A!n)"

lemma length_s_A[simp]: "length(s_A n) = length init"
by (induction n) simp_all

lemma dist_s_A[simp]: "distinct(s_A n)" 
by(induction n) (simp_all add: step_def)

lemma set_s_A[simp]: "set(s_A n) = set init"
by(induction n) (simp_all add: step_def)


fun s_mtf :: "nat \<Rightarrow> 'a list" where
"s_mtf 0 = init" |
"s_mtf (Suc n) = mtf (qs!n) (s_mtf n)"

definition t_mtf :: "nat \<Rightarrow> int" where
"t_mtf n = index (s_mtf n) (qs!n) + 1"

definition T_mtf :: "nat \<Rightarrow> int" where
"T_mtf n = (\<Sum>i<n. t_mtf i)"

definition c_A :: "nat \<Rightarrow> int" where
"c_A n = index (swapSucs (sw_A!n) (s_A n)) (qs!n) + 1"

definition f_A :: "nat \<Rightarrow> int" where
"f_A n = min (mtf_A!n) (index (swapSucs (sw_A!n) (s_A n)) (qs!n))"

definition p_A :: "nat \<Rightarrow> int" where
"p_A n = size(sw_A!n)"

definition t_A :: "nat \<Rightarrow> int" where
"t_A n = c_A n + p_A n"

definition T_A :: "nat \<Rightarrow> int" where
"T_A n = (\<Sum>i<n. t_A i)"

lemma length_s_mtf[simp]: "length(s_mtf n) = length init"
by (induction n) simp_all

lemma dist_s_mtf[simp]: "distinct(s_mtf n)"
apply(induction n)
 apply (simp)
apply (auto simp: mtf_def index_take set_drop_if_index)
apply (metis set_drop_if_index index_take less_Suc_eq_le linear)
done

lemma set_s_mtf[simp]: "set (s_mtf n) = set init"
by (induction n) (simp_all)

lemma dperm_inv: "dist_perm (s_A n) (s_mtf n)"
by (metis dist_s_mtf dist_s_A set_s_mtf set_s_A)

definition Phi :: "nat \<Rightarrow> int" ("\<Phi>") where
"Phi n = card(Inv (s_A n) (s_mtf n))"

lemma phi0: "Phi 0 = 0"
by(simp add: Phi_def)

lemma phi_pos: "Phi n \<ge> 0"
by(simp add: Phi_def)

lemma mtf_ub: "t_mtf n + Phi (n+1) - Phi n \<le> 2 * c_A n - 1 + p_A n - f_A n"
proof -
  let ?xs = "s_A n" let ?ys = "s_mtf n" let ?x = "qs!n"
  let ?xs' = "swapSucs (sw_A!n) ?xs" let ?ys' = "mtf ?x ?ys"
  show ?thesis
  proof cases
  assume xin: "?x \<in> set ?ys"
  let ?bb = "before ?x ?xs \<inter> before ?x ?ys"
  let ?ab = "after ?x ?xs \<inter> before ?x ?ys"
  have phi_mtf:
    "card(Inv ?xs' ?ys') - int(card (Inv ?xs' ?ys))
   \<le> 2 * int(index ?xs' ?x) - int(card (before ?x ?ys))"
      using xin by(simp add: Inv_mtf phi_diff_aux amor_mtf_ub)
  have phi_sw: "card(Inv ?xs' ?ys) \<le> Phi n + length(sw_A!n)"
  proof -
    have "int(card (Inv ?xs' ?ys)) \<le> card(Inv ?xs' ?xs) + int(card(Inv ?xs ?ys))"
      using card_Inv_tri_ineq[of ?xs' ?xs ?ys] xin by (simp)
    also have "card(Inv ?xs' ?xs) = card(Inv ?xs ?xs')"
      by (rule card_Inv_sym)
    also have "card(Inv ?xs ?xs') \<le> size(sw_A!n)"
      by (metis card_Inv_swapSucs_le dist_s_A)
    finally show ?thesis by(fastforce simp: Phi_def)
  qed
  have phi_free: "card(Inv ?xs' ?ys') - Phi (Suc n) = f_A n" using xin
    by(simp add: Phi_def mtf2_def step_def card_Inv_mtf2 index_less_size_conv f_A_def)
  show ?thesis using xin phi_sw phi_mtf phi_free card_before[of "s_mtf n"]
    by(simp add: t_mtf_def c_A_def p_A_def)
  next
    assume notin: "?x \<notin> set ?ys"
    have "int (card (Inv ?xs' ?ys)) - card (Inv ?xs ?ys) \<le> card(Inv ?xs ?xs')"
      using card_Inv_tri_ineq[OF _ dperm_inv, of ?xs' n]
            swapSucs_inv[of "sw_A!n" "s_A n"]
      by(simp add: card_Inv_sym)
    also have "\<dots> \<le> size(sw_A!n)"
      by(simp add: card_Inv_swapSucs_le dperm_inv)
    finally show ?thesis using notin
      by(simp add: t_mtf_def step_def c_A_def p_A_def f_A_def Phi_def mtf2_def)
  qed
qed

theorem Sleator_Tarjan: "T_mtf n \<le> (\<Sum>i<n. 2*c_A i + p_A i - f_A i) - n"
proof-
  have "(\<Sum>i<n. t_mtf i) \<le> (\<Sum>i<n. 2*c_A i - 1 + p_A i - f_A i)"
    by(rule potential[where p=Phi,OF phi0 phi_pos mtf_ub])
  also have "\<dots> = (\<Sum>i<n. (2*c_A i + p_A i - f_A i) - 1)"
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>i<n. 2*c_A i + p_A i - f_A i) - n"
    by(simp add: sumr_diff_mult_const2[symmetric])
  finally show ?thesis by(simp add: T_mtf_def)
qed

lemma T_A_nneg: "0 \<le> T_A n"
by(auto simp add: setsum_nonneg T_A_def t_A_def c_A_def p_A_def)

lemma T_mtf_ub: "\<forall>i<n. qs!i \<in> set init \<Longrightarrow> T_mtf n \<le> n * size init"
proof(induction n)
  case 0 show ?case by(simp add: T_mtf_def)
next
  case (Suc n)  thus ?case
    using index_less_size_conv[of "s_mtf n" "qs!n"]
      by(simp add: T_mtf_def t_mtf_def less_Suc_eq del: index_less)
qed

corollary T_mtf_competitive: assumes "init \<noteq> []" and "\<forall>i<n. qs!i \<in> set init"
shows "T_mtf n \<le> (2 - 1/(size init)) * T_A n"
proof cases
  assume 0: "real(T_A n) \<le> n * (size init)"
  have "T_mtf n \<le> 2 * T_A n - n"
  proof -
    have "T_mtf n \<le> (\<Sum>i<n. 2*c_A i + p_A i - f_A i) - n" by(rule Sleator_Tarjan)
    also have "(\<Sum>i<n. 2*c_A i + p_A i - f_A i) \<le> (\<Sum>i<n. 2*(c_A i + p_A i))"
      by(intro setsum_mono) (simp add: p_A_def f_A_def)
    also have "\<dots> \<le> 2 * T_A n" by (simp add: setsum_right_distrib T_A_def t_A_def)
    finally show ?thesis by simp
  qed
  hence "real(T_mtf n) \<le> 2 * real(T_A n) - n" by linarith
  also have "\<dots> = 2 * real(T_A n) - (n * size init) / size init"
    using assms(1) by simp
  also have "\<dots> \<le> 2 * real(T_A n) - T_A n / size init"
    by(rule diff_left_mono[OF  divide_right_mono[OF 0]]) simp
  also have "\<dots> = (2 - 1 / size init) * T_A n" by algebra
  finally show ?thesis .
next
  assume 0: "\<not> real(T_A n) \<le> n * (size init)"
  have "2 - 1 / size init \<ge> 1" using assms(1)
    by (auto simp add: field_simps neq_Nil_conv)
  have "real (T_mtf n) \<le> n * size init" using T_mtf_ub[OF assms(2)] by linarith
  also have "\<dots> < real(T_A n)" using 0 by linarith
  also have "\<dots> \<le> (2 - 1 / size init) * T_A n" using assms(1) T_A_nneg[of n]
    by(auto simp add: mult_le_cancel_right1 field_simps neq_Nil_conv
        simp del: real_of_int_setsum)
  finally show ?thesis by linarith
qed

lemma t_A_t: "n < length qs \<Longrightarrow> t_A n = int (t (s_A n) (qs ! n) (acts ! n))"
by(simp add: t_A_def t_def c_A_def p_A_def sw_A_def len_acts split: prod.split)

lemma T_A_eq_lem: "(\<Sum>i=0..<length qs. t_A i) =
  T (s_A 0) (drop 0 qs) (drop 0 acts)"
proof(induction rule: zero_induct[of _ "size qs"])
  case 1 thus ?case by (simp add: len_acts)
next
  case (2 n)
  show ?case
  proof cases
    assume "n < length qs"
    thus ?case using 2
    by(simp add: Cons_nth_drop_Suc[symmetric,where i=n] len_acts setsum_head_upt_Suc
      t_A_t mtf_A_def sw_A_def)
  next
    assume "\<not> n < length qs" thus ?case by (simp add: len_acts)
  qed
qed

lemma T_A_eq: "T_A (length qs) = T init qs acts"
using T_A_eq_lem by(simp add: T_A_def atLeast0LessThan)

lemma nth_off_MTF: "n < length qs \<Longrightarrow> off MTF h s qs ! n = (size s,[])"
by(induction qs arbitrary: h s n)(auto simp add: MTF_def nth_Cons')

lemma t_mtf_MTF: "n < length qs \<Longrightarrow>
  t_mtf n = int (t (s_mtf n) (qs ! n) (off MTF h s qs ! n))"
by(simp add: t_mtf_def t_def nth_off_MTF)

lemma mtf_MTF: "n < length qs \<Longrightarrow> length s = length init \<Longrightarrow> mtf (qs ! n) s =
       step s (qs ! n) (off MTF [] init qs ! n)"
using mtf1_def[symmetric, of s "qs!n"]
by(auto simp add: nth_off_MTF step_def mtf1_eq_mtf)

lemma T_mtf_eq_lem: "(\<Sum>i=0..<length qs. t_mtf i) =
  T (s_mtf 0) (drop 0 qs) (drop 0 (off MTF [] init qs))"
proof(induction rule: zero_induct[of _ "size qs"])
  case 1 thus ?case by (simp add: len_acts)
next
  case (2 n)
  show ?case
  proof cases
    assume "n < length qs"
    thus ?case using 2
      by(simp add: Cons_nth_drop_Suc[symmetric,where i=n] len_acts setsum_head_upt_Suc
        t_mtf_MTF[where h="[]" and s=init] mtf_A_def sw_A_def mtf_MTF)
  next
    assume "\<not> n < length qs" thus ?case by (simp add: len_acts)
  qed
qed

lemma T_mtf_eq: "T_mtf (length qs) = T_on MTF [] init qs"
using T_mtf_eq_lem by(simp add: T_mtf_def atLeast0LessThan)

corollary MTF_competitive2: "init \<noteq> [] \<Longrightarrow> \<forall>i<length qs. qs!i \<in> set init \<Longrightarrow>
  T_on MTF [] init qs \<le> (2 - 1/(size init)) * T init qs acts"
by (metis T_mtf_competitive T_A_eq T_mtf_eq real_of_int_of_nat_eq)

end

theorem compet_MTF: assumes "init \<noteq> []" "distinct init" "set qs \<subseteq> set init"
shows "T_on MTF [] init qs \<le> (2 - 1/(size init)) * T_opt init qs"
proof-
  from assms(3) have 1: "\<forall>i < length qs. qs!i \<in> set init" by auto
  { fix acts :: "'a action list" assume len: "length acts = length qs"
    interpret MTF_Off acts qs init proof qed (auto simp: assms(2) len)
    from MTF_competitive2[OF assms(1) 1] assms(1)
    have "T_on MTF [] init qs / (2 - 1 / (length init)) \<le> real(T init qs acts)"
      by(simp add: field_simps length_greater_0_conv[symmetric]
        del: length_greater_0_conv) }
  hence "T_on MTF [] init qs / (2 - 1/(size init)) \<le> T_opt init qs"
    apply(simp add: T_opt_def Inf_nat_def)
    apply(rule LeastI2_wellorder)
    using length_replicate[of "length qs" undefined] apply fastforce
    apply auto
    done
  thus ?thesis using assms by(simp add: field_simps
    length_greater_0_conv[symmetric] del: length_greater_0_conv)
qed

subsection "Lower Bound for Competitiveness"

lemma rat_fun_lem:
   fixes l c :: real
   assumes [simp]: "F \<noteq> bot"
   assumes "0 < l"
   assumes ev: 
     "eventually (\<lambda>n. l \<le> f n / g n) F"
     "eventually (\<lambda>n. (f n + c) / (g n + d) \<le> u) F"
   and
     g: "LIM n F. g n :> at_top"
   shows "l \<le> u"
proof (rule dense_le_bounded[OF `0 < l`])
   fix x assume x: "0 < x" "x < l"

   def m \<equiv> "(x - l) / 2"
   def k \<equiv> "l / (x - m)"
   have "x = l / k + m" "1 < k" "m < 0"
     unfolding k_def m_def using x by (auto simp: divide_simps)
   
   from `1 < k` have "LIM n F. (k - 1) * g n :> at_top"
     by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ g]) (simp add: field_simps)
   then have "eventually (\<lambda>n. d \<le> (k - 1) * g n) F"
     by (simp add: filterlim_at_top)
   moreover have "eventually (\<lambda>n. 1 \<le> g n) F" "eventually (\<lambda>n. 1 - d \<le> g n) F" "eventually (\<lambda>n. c / m - d \<le> g n) F"
     using g by (auto simp add: filterlim_at_top)
   ultimately have "eventually (\<lambda>n. x \<le> u) F"
     using ev
   proof eventually_elim
     fix n assume d: "d \<le> (k - 1) * g n" "1 \<le> g n" "1 - d \<le> g n" "c / m - d \<le> g n"
       and l: "l \<le> f n / g n" and u: "(f n + c) / (g n + d) \<le> u"
     from d have "g n + d \<le> k * g n"
       by (simp add: field_simps)
     from d have g: "0 < g n" "0 < g n + d"
       by (auto simp: field_simps)
     with `0 < l` l have "0 < f n"
       by (auto simp: field_simps intro: mult_pos_pos less_le_trans)

     note `x = l / k + m`
     also have "l / k \<le> f n / (k * g n)"
       using l `1 < k` by (simp add: field_simps)
     also have "\<dots> \<le> f n / (g n + d)"
       using d `1 < k` `0 < f n` by (intro divide_left_mono mult_pos_pos) (auto simp: field_simps)
     also have "m \<le> c / (g n + d)"
       using `c / m - d \<le> g n` `0 < g n` `0 < g n + d` `m < 0` by (simp add: field_simps)
     also have "f n / (g n + d) + c / (g n + d) = (f n + c) / (g n + d)"
       using `0 < g n + d` by (auto simp: add_divide_distrib)
     also note u
     finally show "x \<le> u" by simp
   qed
   then show "x \<le> u"
     by (auto simp: eventually_const)
qed


lemma compet_lb0:
fixes a Aon Aoff cruel 
defines "f s0 qs == real(T_on Aon [] s0 qs)"
defines "g s0 qs == real(T_off Aoff s0 qs)"
assumes "\<And>qs s0. size(Aoff s0 qs) = length qs" and "\<And>n. cruel n \<noteq> []"
assumes "compet Aon c S0" and "c\<ge>0" and "s0 \<in> S0"
 and l: "eventually (\<lambda>n. f s0 (cruel n) / (g s0 (cruel n) + a) \<ge> l) sequentially"
 and g: "LIM n sequentially. g s0 (cruel n) :> at_top"
 and "l > 0"
shows "l \<le> c"
proof-
  let ?h = "\<lambda>b s0 qs. (f s0 qs - b) / g s0 qs"
  have g': "LIM n sequentially. g s0 (cruel n) + a :> at_top"
    using filterlim_tendsto_add_at_top[OF tendsto_const g]
    by (simp add: ac_simps)
  from competE[OF assms(5) `c\<ge>0`] assms(3) obtain b where
    "\<forall>qs.\<forall>s0\<in>S0. qs \<noteq> [] \<longrightarrow> ?h b s0 qs \<le> c "
    by (fastforce simp del: neq0_conv simp: neq0_conv[symmetric]
        field_simps f_def g_def T_off_neq0[of Aoff, OF assms(3)])
  hence "\<forall>s0\<in>S0.\<forall>n. (?h b s0 o cruel) n \<le> c" using assms(4) by simp
  with rat_fun_lem[OF sequentially_bot `l>0` _ _ g', of "f s0 o cruel" "-b" "- a" c] assms(7) l
  show "l \<le> c" by (auto)
qed

subsubsection "Sorting"

fun ins_sws where
"ins_sws k x [] = []" |
"ins_sws k x (y#ys) = (if k x \<le> k y then [] else map Suc (ins_sws k x ys) @ [0])"

fun sort_sws where
"sort_sws k [] = []" |
"sort_sws k (x#xs) =
  ins_sws k x (sort_key k xs) @  map Suc (sort_sws k xs)"

lemma length_ins_sws: "length(ins_sws k x xs) \<le> length xs"
by(induction xs) auto

lemma length_sort_sws_le: "length(sort_sws k xs) \<le> length xs ^ 2"
proof(induction xs)
  case (Cons x xs) thus ?case
    using length_ins_sws[of k x "sort_key k xs"] by (simp add: numeral_eq_Suc)
qed simp

lemma swapSucs_ins_sws:
  "swapSucs (ins_sws k x xs) (x#xs) = insort_key k x xs"
by(induction xs)(auto simp: swapSuc_def[of 0] )

lemma swapSucs_sort_sws[simp]:
  "swapSucs (sort_sws k xs) xs = sort_key k xs"
by(induction xs)(auto simp: swapSucs_ins_sws)

fun cruel :: "'a alg_on \<Rightarrow> 'a list \<Rightarrow> 'a state \<Rightarrow> nat \<Rightarrow> 'a list" where
"cruel A h s 0 = []" |
"cruel A h s (Suc n) = last s # cruel A (last s # h) (step s (last s) (A h s (last s))) n"

definition adv :: "'a alg_on \<Rightarrow> ('a::linorder) alg_off" where
"adv A s qs = (if qs=[] then [] else
  let crs = cruel A [last s] (step s (last s) (A [] s (last s))) (size qs - 1)
  in (0,sort_sws (\<lambda>x. size qs - 1 - List.count crs x) s) # replicate (size qs - 1) (0,[]))"

definition wf_on :: "'a alg_on \<Rightarrow> bool" where
"wf_on A = (\<forall>h s q. \<forall>n \<in> set(snd(A h s q)). n+1 < length s)"

lemma set_cruel: "wf_on A \<Longrightarrow> s \<noteq> [] \<Longrightarrow> set(cruel A h s n) \<subseteq> set s"
apply(induction n arbitrary: s h)
apply(auto simp: step_def wf_on_def split: prod.split)
by (metis empty_iff swapSucs_inv last_in_set list.set(1) rev_subsetD set_mtf2)

lemma index_swapSucs_size: "distinct s \<Longrightarrow>
  index s q \<le> index (swapSucs sws s) q + length sws"
apply(induction sws arbitrary: s)
apply simp
 apply (fastforce simp: swapSuc_def index_swap_if_distinct index_nth_id)
done

lemma index_swapSucs_last_size: "distinct s \<Longrightarrow>
  size s \<le> index (swapSucs sws s) (last s) + length sws + 1"
apply(cases "s = []")
 apply simp
using index_swapSucs_size[of s "last s" sws] by simp

(* Do not convert into structured proof - eta conversion screws it up! *)
lemma T_on_cruel:
  "wf_on A \<Longrightarrow> s \<noteq> [] \<Longrightarrow> distinct s \<Longrightarrow> T_on A h s (cruel A h s n) \<ge> n*(length s)"
apply(induction n arbitrary: s h)
 apply(simp)
apply(erule_tac x = "step s (last s) (A h s (last s))" in meta_allE)
apply(erule_tac x = "last s # h" in meta_allE)
apply(frule_tac sws = "snd(A h s (last s))" in index_swapSucs_last_size)
apply(simp add: distinct_step t_def split_def wf_on_def
        length_greater_0_conv[symmetric] del: length_greater_0_conv)
done

lemma length_cruel[simp]: "length (cruel A h s n) = n"
by (induction n arbitrary: s h) (auto)

lemma t_sort_sws: "t s q (mf, sort_sws k s) \<le> size s ^ 2 + size s + 1"
using length_sort_sws_le[of k s] index_le_size[of "sort_key k s" q]
by (simp add: t_def add_mono index_le_size algebra_simps)

lemma T_noop:
  "n = length qs \<Longrightarrow> T s qs (replicate n (0, [])) = (\<Sum>q\<leftarrow>qs. index s q + 1)"
by(induction qs arbitrary: s n)(auto simp: t_def step_def)


lemma sorted_asc: "j\<le>i \<Longrightarrow> i<size ss \<Longrightarrow> \<forall>x \<in> set ss. \<forall>y \<in> set ss. k(x) \<le> k(y) \<longrightarrow> f y \<le> f x
  \<Longrightarrow> sorted (map k ss) \<Longrightarrow> f (ss ! i) \<le> f (ss ! j)"
by (simp add: sorted_equals_nth_mono)


lemma sorted_weighted_gauss_Ico_div2:
fixes f :: "nat \<Rightarrow> nat"
assumes "\<And>i j. i \<le> j \<Longrightarrow> j<n \<Longrightarrow> f(i) \<ge> f(j)"
shows "(\<Sum>i=0..<n. (i+1) * f(i)) \<le> (n+1) * setsum f {0..<n} div 2"
proof cases
  assume "n = 0" thus ?thesis by simp
next
  assume "n \<noteq> 0"
  have "n * (\<Sum>i=0..<n. (i+1) * f i) \<le> (\<Sum>i=0..<n. i+1) * setsum f {0..<n}"
    using assms by(intro Chebyshev_sum_upper_nat[of n "%i. i+1" f]) auto
  hence "2 * (n * (\<Sum>i=0..<n. (i+1) * f i)) \<le> 2*(\<Sum>i=0..<n. i+1) * setsum f {0..<n}"
    by simp
  also have "2*(\<Sum>i=0..<n. i+1) = n*(n+1)"
    using arith_series_general[where 'a=nat,of 1 1 n] `n \<noteq> 0`
    by(simp add:atLeast0LessThan)
  finally have "2 * (\<Sum>i = 0..<n. (i + 1) * f i) \<le> (n+1) * setsum f {0..<n}"
    using `n \<noteq> 0` by(simp del: One_nat_def)
  thus ?thesis by linarith
qed

lemma T_adv: assumes "wf_on A" "l \<noteq> 0"
shows "T_off (adv A) [0..<l] (cruel A [] [0..<l] (Suc n))
  \<le> l\<^sup>2 + l + 1 + (l + 1) * (n+1) div 2"  (is "?l \<le> ?r")
proof-
  let ?s = "[0..<l]"
  let ?q = "last ?s"
  let ?s' = "step ?s ?q (A [] ?s ?q)"
  let ?cr = "cruel A [?q] ?s' n"
  let ?c = "List.count ?cr"
  let ?k = "\<lambda>x. n - ?c x"
  let ?sort = "sort_key ?k ?s"
  have 1: "set ?s' = {0..<l}"
    apply(subst set_step) using assms(1) by(fastforce simp: wf_on_def)+
  have 3: "\<And>x. x < l \<Longrightarrow> ?c x \<le> n"
    by(simp) (metis count_le_length length_cruel)
  have "?l = t ?s (last ?s) (0, sort_sws ?k ?s) + (\<Sum>x\<in>set ?s'. ?c x * (index ?sort x + 1))"
    using assms(1,2)
    apply(simp add:  adv_def T_noop listsum_map_eq_setsum_count2[OF set_cruel])
    apply(subst (3) step_def)
    apply(simp add: wf_on_def)
    done
  also have "(\<Sum>x\<in>set ?s'. ?c x * (index ?sort x + 1)) = (\<Sum>x\<in>{0..<l}. ?c x * (index ?sort x + 1))"
    by (simp add: 1)
  also have "\<dots> = (\<Sum>x\<in>{0..<l}. ?c (?sort ! x) * (index ?sort (?sort ! x) + 1))"
    by(rule setsum.reindex_bij_betw[where ?h = "nth ?sort", symmetric])
      (simp add: bij_betw_imageI inj_on_nth nth_image)
  also have "\<dots> = (\<Sum>x\<in>{0..<l}. ?c (?sort ! x) * (x+1))"
    by(simp add: index_nth_id)
  also have "\<dots> \<le> (\<Sum>x\<in>{0..<l}. (x+1) * ?c (?sort ! x))"
    by (simp add: algebra_simps)
  also(ord_eq_le_subst) have "\<dots> \<le> (l+1) * (\<Sum>x\<in>{0..<l}. ?c (?sort ! x)) div 2"
    apply(rule sorted_weighted_gauss_Ico_div2)
    apply(erule sorted_asc[where k = "\<lambda>x. n - List.count (cruel A [last ?s] ?s' n) x"])
    apply(auto simp add: index_nth_id dest!: 3)
    using assms(2) [[linarith_split_limit = 20]] apply simp by arith
  also have "(\<Sum>x\<in>{0..<l}. ?c (?sort ! x)) = (\<Sum>x\<in>{0..<l}. ?c (?sort ! (index ?sort x)))"
    by(rule setsum.reindex_bij_betw[where ?h = "index ?sort", symmetric])
      (simp add: bij_betw_imageI inj_on_index2 index_image)
  also have "\<dots> = (\<Sum>x\<in>{0..<l}. ?c x)" by(simp)
  also have "\<dots> = length ?cr"
    using set_cruel[OF assms(1), of ?s' "[last ?s]" n] assms(2) 1
    by(auto simp: setsum_count_set)
  also have "\<dots> = n" by simp
  also have "t ?s (last ?s) (0, sort_sws ?k ?s) \<le> (length ?s)^2 + length ?s + 1"
    by(rule t_sort_sws)
  also have "\<dots> = l^2 + l + 1" by simp
  finally have "?l \<le> l\<^sup>2 + l + 1 + (l + 1) * n div 2" by auto
  also have "\<dots> \<le> l\<^sup>2 + l + 1 + (l + 1) * (n+1) div 2" by auto
  finally show ?thesis .
qed

theorem compet_lb2:
assumes "wf_on A" and "compet A c {xs::nat list. size xs = l}" and "l \<noteq> 0" and "c \<ge> 0"
shows "c \<ge> 2*l/(l+1)"
proof (rule compet_lb0[OF _ _ assms(2) `c\<ge>0`])
  let ?S0 = "{xs::nat list. size xs = l}"
  let ?s0 = "[0..<l]"
  let ?cruel = "cruel A [] ?s0 o Suc"
  let ?on = "\<lambda>n. T_on A [] ?s0 (?cruel n)"
  let ?off = "\<lambda>n. T_off (adv A) ?s0 (?cruel n)"
  show "\<And>s0 qs. length (adv A s0 qs) = length qs" by(simp add: adv_def)
  show "\<And>n. ?cruel n \<noteq> []" by auto
  show "?s0 \<in> ?S0" by simp
  { fix Z::real and n::nat assume "n \<ge> nat(ceiling Z)"
    have "?off n \<ge> length(?cruel n)" by(rule T_ge_len) (simp add: adv_def)
    hence "?off n > n" by simp
    hence "Z \<le> ?off n" using `n \<ge> nat(ceiling Z)` by linarith }
  thus "LIM n sequentially. real (?off n) :> at_top"
    by(auto simp only: filterlim_at_top eventually_sequentially)
  let ?a = "- (l^2 + l + 1)"
  { fix n assume "n \<ge> l^2 + l + 1"
    have "2*l/(l+1) = 2*l*(n+1) / ((l+1)*(n+1))"
      by (simp del: One_nat_def)
    also have "\<dots> = 2*real(l*(n+1)) / ((l+1)*(n+1))" by simp
    also have "l * (n+1) \<le> ?on n"
      using T_on_cruel[OF assms(1), of ?s0 "Suc n"] `l \<noteq> 0`
      by (simp add: ac_simps)
    also have "2*real(?on n) / ((l+1)*(n+1)) \<le> 2*real(?on n)/(2*(?off n + ?a))"
    proof -
      have 0: "2*real(?on n) \<ge> 0" by simp
      have 1: "0 < real ((l + 1) * (n + 1))" by(simp)
      have "?off n \<ge> length(?cruel n)"
        by(rule T_ge_len) (simp add: adv_def)
      hence "?off n > n" by simp
      hence "?off n + ?a > 0" using `n \<ge> l^2 + l + 1` by linarith
      hence 2: "real(2*(?off n + ?a)) > 0"
        by(simp only: real_of_int_gt_zero_cancel_iff zero_less_mult_iff zero_less_numeral simp_thms)
      have "?off n + ?a \<le> (l+1)*(n+1) div 2"
        using T_adv[OF assms(1) `l\<noteq>0`, of n] by(simp)
      hence "2*(?off n + ?a) \<le> (l+1)*(n+1)" by simp
      hence "real(2*(?off n + ?a)) \<le> real((l+1)*(n+1))" by (simp only: real_of_int_le_iff)
      from divide_left_mono[OF this 0 mult_pos_pos[OF 1 2]] show ?thesis .
    qed
    also have "\<dots> = ?on n / (?off n + ?a)"
      by (simp del: Int.distrib_left_numeral One_nat_def cruel.simps)
    finally have "2*l/(l+1) \<le> ?on n / (real (?off n) + ?a)"
      by (auto simp: divide_right_mono)
  }
  thus "eventually (\<lambda>n. (2 * l) / (l + 1) \<le> ?on n / (real(?off n) + ?a)) sequentially"
    by(auto simp add: filterlim_at_top eventually_sequentially)
  show "0 < 2*l / (l+1)" using `l \<noteq> 0` by(simp)
qed


end
