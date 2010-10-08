theory ListAdd
imports Main
begin 

(* Additional Lemmas for Lists *)

lemma hd_mem: "s\<noteq>[] \<Longrightarrow> (hd s) mem s"
  apply (induct s)
  apply(auto)
done

lemma (in linorder) sorted_hd_min: "\<lbrakk>xs \<noteq> []; sorted xs\<rbrakk> \<Longrightarrow> \<forall>x \<in> set xs. hd xs \<le> x"
  by(induct xs, auto simp add: sorted_Cons)

lemma map_hd: "\<lbrakk>xs \<noteq> []\<rbrakk> \<Longrightarrow> f (hd xs) = hd (map f xs)"
 apply(induct xs)
 apply(auto)
done

lemma map_tl: "map f (tl xs) = tl (map f xs)"
  apply(induct xs)
  apply(auto)
done

lemma drop_1_tl: "drop 1 xs = tl xs"
  apply(induct xs)
  apply(auto)
done

lemma remove1_tl: "xs \<noteq> [] \<Longrightarrow> remove1 (hd xs) xs = tl xs"
  apply(induct xs, simp)
  apply(auto)
done

lemma sorted_append_bigger: 
  "\<lbrakk>sorted xs; \<forall>x \<in> set xs. x \<le> y\<rbrakk> \<Longrightarrow> sorted (xs @ [y])"
  apply (induct xs)
  apply simp
proof -
  case goal1
  from goal1 have s: "sorted xs" by (cases xs) simp_all
  from goal1 have a: "\<forall>x\<in>set xs. x \<le> y" by simp
  from goal1(1)[OF s a] goal1(2-) show ?case by (cases xs) simp_all
qed
end