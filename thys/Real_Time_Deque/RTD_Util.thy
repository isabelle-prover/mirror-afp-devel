section \<open>Basic Lemma Library\<close>

theory RTD_Util 
imports Main
begin

lemma take_last_length: "\<lbrakk>take (Suc 0) (rev xs) = [last xs]\<rbrakk> \<Longrightarrow> Suc 0 \<le> length xs"
  by(induction xs) auto

lemma take_last: "xs \<noteq> [] \<Longrightarrow> take 1 (rev xs) = [last xs]"
  by(induction xs)(auto simp: take_last_length)

lemma take_hd [simp]: "xs \<noteq> [] \<Longrightarrow> take (Suc 0) xs = [hd xs]"
  by(induction xs) auto

lemma cons_tl: "x # xs = ys \<Longrightarrow> xs = tl ys"
  by auto

lemma cons_hd: "x # xs = ys \<Longrightarrow> x = hd ys"
  by auto

lemma take_hd': "ys \<noteq> [] \<Longrightarrow> take (size ys) (x # xs) = take (Suc (size xs)) ys \<Longrightarrow> hd ys = x"
  by(induction ys) auto

lemma rev_app_single: "rev xs @ [x] = rev (x # xs)"
  by auto

lemma hd_drop_1 [simp]: "xs \<noteq> [] \<Longrightarrow> hd xs # drop (Suc 0) xs = xs"
  by(induction xs) auto

lemma hd_drop [simp]: "n < length xs \<Longrightarrow> hd (drop n xs) # drop (Suc n) xs = drop n xs"
  by(induction xs)(auto simp: list.expand tl_drop)

lemma take_1: "0 < x \<and> 0 < y \<Longrightarrow> take x xs  = take y ys \<Longrightarrow> take 1 xs = take 1 ys"
  by (metis One_nat_def bot_nat_0.not_eq_extremum hd_take take_Suc take_eq_Nil)

lemma last_drop_rev: "xs \<noteq> [] \<Longrightarrow> last xs # drop 1 (rev xs) = rev xs"
  by (metis One_nat_def hd_drop_1 hd_rev rev.simps(1) rev_rev_ident)

lemma Suc_min [simp]: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> Suc (min (x - Suc 0) (y - Suc 0)) = min x y"
  by auto

lemma rev_tl_hd: "xs \<noteq> [] \<Longrightarrow> rev (tl xs) @ [hd xs] = rev xs" 
  by (simp add: rev_app_single)

lemma app_rev: "as @ rev bs = cs @ rev ds \<Longrightarrow> bs @ rev as = ds @ rev cs"
  by (metis rev_append rev_rev_ident)

lemma tl_drop_2: "tl (drop n xs) = drop (Suc n) xs" 
  by (simp add: drop_Suc tl_drop)

lemma Suc_sub: "Suc n = m \<Longrightarrow> n = m - 1"
  by simp

lemma length_one_hd: "length xs = 1 \<Longrightarrow> xs = [hd xs]" 
  by(induction xs) auto

end
