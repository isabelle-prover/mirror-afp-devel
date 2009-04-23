(*  Title:      JinjaThreads/Framework/FWBisimulation.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{(Weak) Bisimulation relations} *}

theory FWBisimulation imports FWProgressAux begin

definition EqBR :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a + 'b) \<Rightarrow> ('a + 'b) \<Rightarrow> bool"
where 
  "EqBR bs \<equiv> (\<lambda>s1 s2. (\<exists>s1' s2'. s1 = Inl s1' \<and> s2 = Inr s2' \<and> bs s1' s2') \<or>
                       (\<exists>s1' s2'. s1 = Inr s1' \<and> s2 = Inl s2' \<and> bs s2' s1'))^**"

lemma rtranclp_conv_rtrancl: "r^** = curry ((split r)^*)"
unfolding rtrancl_def
by(auto simp add: mem_def Collect_def)

lemma rtrancl_conv_rtranclp: "r^* = split ((curry r)^**)"
unfolding rtrancl_def
by(auto simp add: mem_def curry_def)

lemma EqBR_refl: "refl (split (EqBR bs))"
unfolding EqBR_def rtranclp_conv_rtrancl split_curry
by(rule refl_rtrancl)

lemma EqBR_sym: "sym (split (EqBR bs))"
unfolding EqBR_def rtranclp_conv_rtrancl split_curry
by(rule sym_rtrancl)(auto intro!: symI simp add: mem_def)

lemma EqBR_symD:
  assumes 1: "EqBR bs a b"
  shows "EqBR bs b a"
proof -
  from 1 have "(a, b) \<in> split (EqBR bs)" by(simp add: mem_def)
  from symD[OF EqBR_sym this] show ?thesis by(simp add: mem_def)
qed

lemma EqBR_trans: "trans (split (EqBR bs))"
unfolding EqBR_def rtranclp_conv_rtrancl split_curry
by(rule trans_rtrancl)

types ('a, 'b) trsys = "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
types ('a, 'b) bisim = "'a \<Rightarrow> 'b \<Rightarrow> bool"

locale trsys = 
  fixes trsys :: "('s, 'tl) trsys"
begin

abbreviation Trsys :: "('s, 'tl list) trsys" ("_/ -_\<rightarrow>*/ _" [50,0,50] 60)
where "\<And>tl. s -tl\<rightarrow>* s' \<equiv> rtrancl3p trsys s tl s'"

end


locale bisimulation_base = r1!: trsys trsys1 + r2!: trsys trsys2
  for trsys1 :: "('s1, 'tl1) trsys" ("_/ -1-_\<rightarrow>/ _" [50,0,50] 60)
  and trsys2 :: "('s2, 'tl2) trsys" ("_/ -2-_\<rightarrow>/ _" [50,0,50] 60) +
  fixes bisim :: "('s1, 's2) bisim" ("_/ \<approx> _" [50, 50] 60)
  and tlsim :: "('tl1, 'tl2) bisim" ("_/ \<sim> _" [50, 50] 60)
begin

notation r1.Trsys ("_/ -1-_\<rightarrow>*/ _" [50,0,50] 60)
notation r2.Trsys ("_/ -2-_\<rightarrow>*/ _" [50,0,50] 60)

abbreviation Tlsim :: "('tl1 list, 'tl2 list) bisim" ("_/ [\<sim>] _" [50, 50] 60)
where "Tlsim tl1 tl2 \<equiv> list_all2 tlsim tl1 tl2"

end

locale bisimulation = bisimulation_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  assumes simulation1: "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2' tl2. s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
  and simulation2: "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1' tl1. s1 -1-tl1\<rightarrow> s1' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
begin

lemma simulation1_rtrancl:
  "\<lbrakk>s1 -1-tls1\<rightarrow>* s1'; s1 \<approx> s2\<rbrakk>
  \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by(auto intro: rtrancl3p.rtrancl3p_refl)
next
  case (rtrancl3p_step s1 tls1 s1' tl1 s1'')
  from `s1 \<approx> s2 \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2` `s1 \<approx> s2`
  obtain s2' tls2 where "s2 -2-tls2\<rightarrow>* s2'" "s1' \<approx> s2'" "tls1 [\<sim>] tls2" by blast
  moreover from `s1' -1-tl1\<rightarrow> s1''` `s1' \<approx> s2'`
  obtain s2'' tl2 where "s2' -2-tl2\<rightarrow> s2''" "s1'' \<approx> s2''" "tl1 \<sim> tl2" by(auto dest: simulation1)
  ultimately have "s2 -2-tls2 @ [tl2]\<rightarrow>* s2''" "tls1 @ [tl1] [\<sim>] tls2 @ [tl2]"
    by(auto intro: rtrancl3p.rtrancl3p_step list_all2_appendI)
  with `s1'' \<approx> s2''` show ?case by(blast)
qed

lemma simulation2_rtrancl:
  "\<lbrakk>s2 -2-tls2\<rightarrow>* s2'; s1 \<approx> s2\<rbrakk>
  \<Longrightarrow> \<exists>s1' tls1. s1 -1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by(auto intro: rtrancl3p.rtrancl3p_refl)
next
  case (rtrancl3p_step s2 tls2 s2' tl2 s2'')
  from `s1 \<approx> s2 \<Longrightarrow> \<exists>s1' tls1. s1 -1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2` `s1 \<approx> s2`
  obtain s1' tls1 where "s1 -1-tls1\<rightarrow>* s1'" "s1' \<approx> s2'" "tls1 [\<sim>] tls2" by blast
  moreover from `s2' -2-tl2\<rightarrow> s2''` `s1' \<approx> s2'`
  obtain s1'' tl1 where "s1' -1-tl1\<rightarrow> s1''" "s1'' \<approx> s2''" "tl1 \<sim> tl2" by(auto dest: simulation2)
  ultimately have "s1 -1-tls1 @ [tl1]\<rightarrow>* s1''" "tls1 @ [tl1] [\<sim>] tls2 @ [tl2]"
    by(auto intro: rtrancl3p.rtrancl3p_step list_all2_appendI)
  with `s1'' \<approx> s2''` show ?case by(blast)
qed

inductive joint_trsys :: "('s1 + 's2, 'tl1 + 'tl2) trsys" ("_/ -12-_\<rightarrow>/ _" [50, 0, 50] 60)
  where
  joint_trsys_left:  "s1 -1-tl1\<rightarrow> s2 \<Longrightarrow> Inl s1 -12-Inl tl1\<rightarrow> Inl s2"
| joint_trsys_right: "s1 -2-tl2\<rightarrow> s2 \<Longrightarrow> Inr s1 -12-Inr tl2\<rightarrow> Inr s2"

lemma EqBR_bisim: "bisimulation joint_trsys joint_trsys (EqBR bisim) (EqBR tlsim)"
proof -
  { fix s1 s1' tl1 s2
    assume eq: "EqBR bisim s1 s1'"
    assume "s1 -12-tl1\<rightarrow> s2"
    with eq[unfolded EqBR_def]
    have "\<exists>s2' tl1'. s1' -12-tl1'\<rightarrow> s2' \<and> EqBR bisim s2 s2' \<and> EqBR tlsim tl1 tl1'"
    proof induct
      case base
      note jts = `s1 -12-tl1\<rightarrow> s2`
      show ?case
      proof(rule exI conjI)+
	from jts show "s1 -12-tl1\<rightarrow> s2" .
      next
	show "EqBR bisim s2 s2 \<and> EqBR tlsim tl1 tl1" unfolding EqBR_def by(auto)
      qed
    next
      case (step s3 s4)
      hence eqbr: "EqBR bisim s1 s3" unfolding EqBR_def by -
      note IH = `s1 -12-tl1\<rightarrow> s2 \<Longrightarrow> \<exists>s2' tl1'. s3 -12-tl1'\<rightarrow> s2' \<and> EqBR bisim s2 s2' \<and> EqBR tlsim tl1 tl1'`
      with `s1 -12-tl1\<rightarrow> s2` obtain s3' tl1'
	where "s3 -12-tl1'\<rightarrow> s3'" "EqBR bisim s2 s3'" "EqBR tlsim tl1 tl1'" by blast
      note step' = `(\<exists>s1' s2'. s3 = Inl s1' \<and> s4 = Inr s2' \<and> bisim s1' s2') \<or> (\<exists>s1' s2'. s3 = Inr s1' \<and> s4 = Inl s2' \<and> bisim s2' s1')`
      from `s3 -12-tl1'\<rightarrow> s3'` show ?case
      proof cases
	case (joint_trsys_left S3 TL3 S3')
	hence [simp]: "s3 = Inl S3" "tl1' = Inl TL3" "s3' = Inl S3'" by -
	from step' obtain S4 where [simp]: "s4 = Inr S4" and bisim': "S3 \<approx> S4" by auto
	from simulation1[OF bisim' `S3 -1-TL3\<rightarrow> S3'`] obtain S4' TL4
	  where "S4 -2-TL4\<rightarrow> S4'" "S3' \<approx> S4'" "TL3 \<sim> TL4" by blast
	hence "Inr S4 -12-Inr TL4\<rightarrow> Inr S4'" by -(rule joint_trsys_right)
	moreover from `EqBR bisim s2 s3'` `S3' \<approx> S4'`
	have "EqBR bisim s2 (Inr S4')" unfolding EqBR_def
	  by -(erule rtranclp.rtrancl_into_rtrancl, simp)
	moreover from `EqBR tlsim tl1 tl1'` `TL3 \<sim> TL4`
	have "EqBR tlsim tl1 (Inr TL4)" unfolding EqBR_def
	  by -(erule rtranclp.rtrancl_into_rtrancl, simp)
	ultimately show ?thesis by auto
      next
	case (joint_trsys_right S3 TL3 S3')
	hence [simp]: "s3 = Inr S3" "tl1' = Inr TL3" "s3' = Inr S3'" by -
	from step' obtain S4 where [simp]: "s4 = Inl S4" and bisim': "S4 \<approx> S3" by auto
	from simulation2[OF bisim' `S3 -2-TL3\<rightarrow> S3'`] obtain S4' TL4
	  where "S4 -1-TL4\<rightarrow> S4'" "S4' \<approx> S3'" "TL4 \<sim> TL3" by blast
	hence "Inl S4 -12-Inl TL4\<rightarrow> Inl S4'" by -(rule joint_trsys_left)
	moreover from `EqBR bisim s2 s3'` `S4' \<approx> S3'`
	have "EqBR bisim s2 (Inl S4')" unfolding EqBR_def
	  by -(erule rtranclp.rtrancl_into_rtrancl, simp)
	moreover from `EqBR tlsim tl1 tl1'` `TL4 \<sim> TL3`
	have "EqBR tlsim tl1 (Inl TL4)" unfolding EqBR_def
	  by -(erule rtranclp.rtrancl_into_rtrancl, simp)
	ultimately show ?thesis by auto
      qed
    qed }
  note r = this
  show ?thesis
  proof
    fix s1 s1' tl1 s2
    assume "EqBR bisim s1 s1'" "s1 -12-tl1\<rightarrow> s2"
    thus "\<exists>s2' tl1'. s1' -12-tl1'\<rightarrow> s2' \<and> EqBR bisim s2 s2' \<and> EqBR tlsim tl1 tl1'" by(rule r)
  next
    fix s1 s1' tl2 s2'
    assume bs: "EqBR bisim s1 s1'" and jts: "s1' -12-tl2\<rightarrow> s2'"
    from bs have "EqBR bisim s1' s1" by(rule EqBR_symD)
    from r[OF this jts] obtain s2 tl1 where "s1 -12-tl1\<rightarrow> s2"
      "EqBR bisim s2' s2" "EqBR tlsim tl2 tl1" by blast
    thus "\<exists>s2 tl1. s1 -12-tl1\<rightarrow> s2 \<and> EqBR bisim s2 s2' \<and> EqBR tlsim tl1 tl2"
      by(auto dest: EqBR_symD)
  qed
qed

end

locale \<tau>trsys = trsys trsys 
  for trsys :: "('s, 'tl) trsys" ("_/ -_\<rightarrow>/ _" [50,0,50] 60) +
  fixes \<tau>move :: "('s, 'tl) trsys" ("_/ -\<tau>-_\<rightarrow>/ _" [50, 0, 50] 60)
begin

definition \<tau>moves :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_/ -\<tau>\<rightarrow>* _" [50, 50] 60)
  where "\<tau>moves \<equiv> (\<lambda>s s'. \<exists>tl. s -tl\<rightarrow> s' \<and> s -\<tau>-tl\<rightarrow> s')^**"

lemma \<tau>moves_trans [trans]:
  "\<lbrakk>s1 -\<tau>\<rightarrow>* s2; s2 -\<tau>\<rightarrow>* s3\<rbrakk> \<Longrightarrow> s1 -\<tau>\<rightarrow>* s3"
unfolding \<tau>moves_def by auto

lemma \<tau>moves_refl [intro!, simp]: "s1 -\<tau>\<rightarrow>* s1"
unfolding \<tau>moves_def by blast

lemma \<tau>move_into_\<tau>moves [intro]:
  fixes tl
  shows "\<lbrakk> s -tl\<rightarrow> s'; s -\<tau>-tl\<rightarrow> s' \<rbrakk> \<Longrightarrow> s -\<tau>\<rightarrow>* s'"
unfolding \<tau>moves_def by blast

lemma \<tau>moves_into_\<tau>moves:
  fixes tl
  shows "\<lbrakk> s -\<tau>\<rightarrow>* s'; s' -tl\<rightarrow> s''; s' -\<tau>-tl\<rightarrow> s'' \<rbrakk> \<Longrightarrow> s -\<tau>\<rightarrow>* s''"
unfolding \<tau>moves_def by(erule rtranclp.rtrancl_into_rtrancl) blast

definition obs_move :: "'s \<Rightarrow> 'tl \<Rightarrow> 's \<Rightarrow> bool"
where "\<And>tl. obs_move s tl s'' \<equiv> \<exists>s'. s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> s' -\<tau>-tl\<rightarrow> s''"

end

locale weak_bisimulation_base =
  bisimulation_base _ _ bisim tlsim +
  trsys1: \<tau>trsys trsys1 \<tau>move1 +
  trsys2: \<tau>trsys trsys2 \<tau>move2 
  for bisim :: "('s1, 's2) bisim" ("_/ \<approx> _" [50, 50] 60)
  and tlsim :: "('tl1, 'tl2) bisim" ("_/ \<sim> _" [50, 50] 60)
  and \<tau>move1 :: "('s1, 'tl1) trsys" ("_/ -\<tau>1-_\<rightarrow>/ _" [50, 0, 50] 60)
  and \<tau>move2 :: "('s2, 'tl2) trsys"  ("_/ -\<tau>2-_\<rightarrow>/ _" [50, 0, 50] 60)
begin

notation trsys1.\<tau>moves ("_/ -\<tau>1\<rightarrow>* _" [50, 50] 60)
notation trsys2.\<tau>moves ("_/ -\<tau>2\<rightarrow>* _" [50, 50] 60)

lemmas \<tau>moves1_def = trsys1.\<tau>moves_def
lemmas \<tau>moves2_def = trsys2.\<tau>moves_def
lemmas \<tau>moves1_trans = trsys1.\<tau>moves_trans
lemmas \<tau>moves2_trans = trsys2.\<tau>moves_trans

abbreviation obs_move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
where "obs_move1 \<equiv> trsys1.obs_move"

abbreviation obs_move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool"
where "obs_move2 \<equiv> trsys2.obs_move"

lemmas obs_move1_def = trsys1.obs_move_def
lemmas obs_move2_def = trsys2.obs_move_def

end

locale weak_bisimulation = weak_bisimulation_base _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool" ("_/ -\<tau>1-_\<rightarrow>/ _" [50, 0, 50] 60)
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool" ("_/ -\<tau>2-_\<rightarrow>/ _" [50, 0, 50] 60) +
  assumes simulation_silent1:
  "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; s1 -\<tau>1-tl1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
  and simulation_silent2:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2'; s2 -\<tau>2-tl2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'"
  and simulation1:
  "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; \<not> s1 -\<tau>1-tl1\<rightarrow> s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' s2'' tl2. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> s2' -\<tau>2-tl2\<rightarrow> s2'' \<and> s1' \<approx> s2'' \<and> tl1 \<sim> tl2"
  assumes simulation2:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2'; \<not> s2 -\<tau>2-tl2\<rightarrow> s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' -1-tl1\<rightarrow> s1'' \<and> \<not> s1' -\<tau>1-tl1\<rightarrow> s1'' \<and> s1'' \<approx> s2' \<and> tl1 \<sim> tl2"
begin

lemma simulation_silents1:
  assumes bisim: "s1 \<approx> s2" and moves: "s1 -\<tau>1\<rightarrow>* s1'"
  shows "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
using moves bisim unfolding \<tau>moves1_def
proof induct
  case base thus ?case unfolding \<tau>moves2_def by(blast)
next
  case (step s1' s1'')
  from `s1 \<approx> s2 \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'` `s1 \<approx> s2`
  obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
  from `\<exists>tl1. s1' -1-tl1\<rightarrow> s1'' \<and> s1' -\<tau>1-tl1\<rightarrow> s1''` obtain tl1
    where "s1' -1-tl1\<rightarrow> s1''" "s1' -\<tau>1-tl1\<rightarrow> s1''" by blast
  from simulation_silent1[OF `s1' \<approx> s2'` this]
  obtain s2'' where "s2' -\<tau>2\<rightarrow>* s2''" "s1'' \<approx> s2''" by blast
  from `s2 -\<tau>2\<rightarrow>* s2'` `s2' -\<tau>2\<rightarrow>* s2''` have "s2 -\<tau>2\<rightarrow>* s2''" by(rule \<tau>moves2_trans)
  with `s1'' \<approx> s2''` show ?case by blast
qed

lemma simulation_silents2:
  assumes bisim: "s1 \<approx> s2" and moves: "s2 -\<tau>2\<rightarrow>* s2'"
  shows "\<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'"
using moves bisim unfolding \<tau>moves2_def
proof induct
  case base thus ?case unfolding \<tau>moves1_def by(blast)
next
  case (step s2' s2'')
  from `s1 \<approx> s2 \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'` `s1 \<approx> s2`
  obtain s1' where "s1 -\<tau>1\<rightarrow>* s1'" "s1' \<approx> s2'" by blast
  from `\<exists>tl2. s2' -2-tl2\<rightarrow> s2'' \<and> s2' -\<tau>2-tl2\<rightarrow> s2''` obtain tl2
    where "s2' -2-tl2\<rightarrow> s2''" "s2' -\<tau>2-tl2\<rightarrow> s2''" by blast
  from simulation_silent2[OF `s1' \<approx> s2'` this]
  obtain s1'' where "s1' -\<tau>1\<rightarrow>* s1''" "s1'' \<approx> s2''" by blast
  from `s1 -\<tau>1\<rightarrow>* s1'` `s1' -\<tau>1\<rightarrow>* s1''` have "s1 -\<tau>1\<rightarrow>* s1''" by(rule \<tau>moves1_trans)
  with `s1'' \<approx> s2''` show ?case by blast
qed

lemma obs_bisimulation: "bisimulation obs_move1 obs_move2 bisim tlsim"
proof
  fix s1 s2 tl1 s1''
  assume bisim1: "s1 \<approx> s2" and move: "obs_move1 s1 tl1 s1''"
  from move obtain s1' where \<tau>1: "s1 -\<tau>1\<rightarrow>* s1'" and red1: "s1' -1-tl1\<rightarrow> s1''"
    and \<tau>2: "\<not> s1' -\<tau>1-tl1\<rightarrow> s1''" unfolding obs_move1_def by blast
  from simulation_silents1[OF bisim1 \<tau>1] obtain s2'
    where \<tau>1': "s2 -\<tau>2\<rightarrow>* s2'" and bisim2: "s1' \<approx> s2'" by blast
  from simulation1[OF bisim2 red1 \<tau>2] obtain s2'' s2''' tl2
    where \<tau>21: "s2' -\<tau>2\<rightarrow>* s2''" and red2: "s2'' -2-tl2\<rightarrow> s2'''"
    and \<tau>22: "\<not> s2'' -\<tau>2-tl2\<rightarrow> s2'''" and bisim3: "s1'' \<approx> s2'''"
    and tlsim: "tl1 \<sim> tl2" by(blast)
  from \<tau>moves2_trans[OF \<tau>1' \<tau>21] \<tau>22 red2 bisim3 tlsim
  show "\<exists>s2' tl2. obs_move2 s2 tl2 s2' \<and> s1'' \<approx> s2' \<and> tl1 \<sim> tl2"
    unfolding obs_move2_def by blast
next
  fix s2 s1 tl2 s2''
  assume bisim1: "bisim s1 s2" and move: "obs_move2 s2 tl2 s2''"
  from move obtain s2' where \<tau>1: "s2 -\<tau>2\<rightarrow>* s2'" and red2: "s2' -2-tl2\<rightarrow> s2''"
    and \<tau>2: "\<not> s2' -\<tau>2-tl2\<rightarrow> s2''" unfolding obs_move2_def by blast
  from simulation_silents2[OF bisim1 \<tau>1] obtain s1'
    where \<tau>1': "s1 -\<tau>1\<rightarrow>* s1'" and bisim2: "s1' \<approx> s2'" by blast
  from simulation2[OF bisim2 red2 \<tau>2] obtain s1'' s1''' tl1
    where \<tau>21: "s1' -\<tau>1\<rightarrow>* s1''" and red1: "s1'' -1-tl1\<rightarrow> s1'''"
    and \<tau>22: "\<not> s1'' -\<tau>1-tl1\<rightarrow> s1'''" and bisim3: "s1''' \<approx> s2''"
    and tlsim: "tl1 \<sim> tl2" by(blast)
  from \<tau>moves1_trans[OF \<tau>1' \<tau>21] \<tau>22 red1 bisim3 tlsim
  show "\<exists>s1' tl1. obs_move1 s1 tl1 s1' \<and> s1' \<approx> s2'' \<and> tl1 \<sim> tl2"
    unfolding obs_move1_def by blast
qed

end

locale \<tau>inv = weak_bisimulation_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and \<tau>moves1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>moves2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes \<tau>inv: "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; s2 -2-tl2\<rightarrow> s2'; s1' \<approx> s2'; tl1 \<sim> tl2 \<rbrakk>
                 \<Longrightarrow> s1 -\<tau>1-tl1\<rightarrow> s1' \<longleftrightarrow> s2 -\<tau>2-tl2\<rightarrow> s2'"

locale bisimulation_into_weak =
  bisimulation + \<tau>inv +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and \<tau>moves1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>moves2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"
begin

lemma weak_bisimulation:
  "weak_bisimulation trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
proof
  fix s1 s2 tl1 s1'
  assume bisim: "s1 \<approx> s2" and tr1: "s1 -1-tl1\<rightarrow> s1'" and \<tau>1: "s1 -\<tau>1-tl1\<rightarrow> s1'"
  from simulation1[OF bisim tr1] obtain s2' tl2 where tr2: "s2 -2-tl2\<rightarrow> s2'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>1 have \<tau>2: "s2 -\<tau>2-tl2\<rightarrow> s2'" by simp
  with bisim' tr2 show "\<exists>s2'.  s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'" by(auto simp add: \<tau>moves2_def)
next
  fix s1 s2 tl2 s2'
  assume bisim: "s1 \<approx> s2" and tr2: "s2 -2-tl2\<rightarrow> s2'" and \<tau>2: "s2 -\<tau>2-tl2\<rightarrow> s2'"
  from simulation2[OF bisim tr2] obtain s1' tl1 where tr1: "s1 -1-tl1\<rightarrow> s1'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>2 have \<tau>1: "s1 -\<tau>1-tl1\<rightarrow> s1'" by simp
  with bisim' tr1 show "\<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'" by(auto simp add: \<tau>moves1_def)
next
  fix s1 s2 tl1 s1'
  assume bisim: "s1 \<approx> s2" and tr1: "s1 -1-tl1\<rightarrow> s1'" and \<tau>1: "\<not> s1 -\<tau>1-tl1\<rightarrow> s1'"
  from simulation1[OF bisim tr1] obtain s2' tl2 where tr2: "s2 -2-tl2\<rightarrow> s2'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>1 have \<tau>2: "\<not> s2 -\<tau>2-tl2\<rightarrow> s2'" by simp
  with bisim' tr2 tlsim
  show "\<exists>s2' s2'' tl2. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> s2' -\<tau>2-tl2\<rightarrow> s2'' \<and>
                       s1' \<approx> s2'' \<and> tl1 \<sim> tl2" unfolding \<tau>moves2_def by blast
next
  fix s1 s2 tl2 s2'
  assume bisim: "s1 \<approx> s2" and tr2: "s2 -2-tl2\<rightarrow> s2'" and \<tau>2: "\<not> s2 -\<tau>2-tl2\<rightarrow> s2'"
  from simulation2[OF bisim tr2] obtain s1' tl1 where tr1: "s1 -1-tl1\<rightarrow> s1'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>2 have \<tau>1: "\<not> s1 -\<tau>1-tl1\<rightarrow> s1'" by simp
  with bisim' tr1 tlsim
  show "\<exists>s1' s1'' tl1. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' -1-tl1\<rightarrow> s1'' \<and> \<not> s1' -\<tau>1-tl1\<rightarrow> s1'' \<and>
                  s1'' \<approx> s2' \<and> tl1 \<sim> tl2" unfolding \<tau>moves1_def by blast
qed

end

sublocale bisimulation_into_weak < weak_bisimulation
by(intro \<tau>moves1_def \<tau>moves2_def weak_bisimulation)+

definition bisim_compose :: "('s1, 's2) bisim \<Rightarrow> ('s2, 's3) bisim \<Rightarrow> ('s1, 's3) bisim" (infixr "\<circ>\<^isub>B" 60)
where "(bisim1 \<circ>\<^isub>B bisim2) s1 s3 \<equiv> \<exists>s2. bisim1 s1 s2 \<and> bisim2 s2 s3"

lemma bisim_composeI [intro?]:
  "\<lbrakk> bisim12 s1 s2; bisim23 s2 s3 \<rbrakk> \<Longrightarrow> (bisim12 \<circ>\<^isub>B bisim23) s1 s3"
by(auto simp add: bisim_compose_def)

lemma bisim_composeE [elim!]:
  assumes bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
  obtains s2 where "bisim12 s1 s2" "bisim23 s2 s3"
by(atomize_elim)(rule bisim[unfolded bisim_compose_def])

lemma bisim_compose_assoc [simp]:
  "(bisim12 \<circ>\<^isub>B bisim23) \<circ>\<^isub>B bisim34 = bisim12 \<circ>\<^isub>B bisim23 \<circ>\<^isub>B bisim34"
by(auto simp add: expand_fun_eq intro: bisim_composeI)

lemma bisimulation_bisim_compose:
  assumes bisim12: "bisimulation trsys1 trsys2 bisim12 tlsim12"
  and bisim23: "bisimulation trsys2 trsys3 bisim23 tlsim23"
  shows "bisimulation trsys1 trsys3 (bisim_compose bisim12 bisim23) (bisim_compose tlsim12 tlsim23)"
proof -
  interpret b12!: bisimulation trsys1 trsys2 bisim12 tlsim12 by(rule bisim12)
  interpret b23!: bisimulation trsys2 trsys3 bisim23 tlsim23 by(rule bisim23)
  show ?thesis
  proof
    fix s1 s3 tl1 s1'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3" and tr1: "trsys1 s1 tl1 s1'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2"
      and bisim2: "bisim23 s2 s3" by blast
    from b12.simulation1[OF bisim1 tr1] obtain s2' tl2
      where tr2: "trsys2 s2 tl2 s2'" and bisim1': "bisim12 s1' s2'"
      and tlsim1: "tlsim12 tl1 tl2" by blast
    from b23.simulation1[OF bisim2 tr2] obtain s3' tl3
      where "trsys3 s3 tl3 s3'" "bisim23 s2' s3'" "tlsim23 tl2 tl3" by blast
    thus "\<exists>s3' tl3. trsys3 s3 tl3 s3' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1' s3' \<and> (tlsim12 \<circ>\<^isub>B tlsim23) tl1 tl3"
      using bisim1' tlsim1 by(blast intro: bisim_composeI)
  next
    fix s3 s1 tl3 s3'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3" and tr3: "trsys3 s3 tl3 s3'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2"
      and bisim2: "bisim23 s2 s3" by blast
    from b23.simulation2[OF bisim2 tr3] obtain s2' tl2
      where tr2: "trsys2 s2 tl2 s2'" and bisim2': "bisim23 s2' s3'"
      and tlsim2: "tlsim23 tl2 tl3" by blast
    from b12.simulation2[OF bisim1 tr2] obtain s1' tl1
      where "trsys1 s1 tl1 s1'" "bisim12 s1' s2'" "tlsim12 tl1 tl2" by blast
    thus "\<exists>s1' tl1. trsys1 s1 tl1 s1' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1' s3' \<and> (tlsim12 \<circ>\<^isub>B tlsim23) tl1 tl3"
      using bisim2' tlsim2 by(blast intro: bisim_composeI)
  qed
qed


lemma weak_bisimulation_compose:
  assumes wbisim12: "weak_bisimulation trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2"
  and wbisim23: "weak_bisimulation trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3"
  shows "weak_bisimulation trsys1 trsys3 (bisim12 \<circ>\<^isub>B bisim23) (tlsim12 \<circ>\<^isub>B tlsim23) \<tau>move1 \<tau>move3"
proof -
  interpret trsys1!: \<tau>trsys trsys1 \<tau>move1 .
  interpret trsys2!: \<tau>trsys trsys2 \<tau>move2 .
  interpret trsys3!: \<tau>trsys trsys3 \<tau>move3 .
  interpret wb12!: weak_bisimulation trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2 by(auto intro: wbisim12)
  interpret wb23!: weak_bisimulation trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3 by(auto intro: wbisim23)
  show ?thesis
  proof
    fix s1 s3 tl1 s1'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
      and tr1: "trsys1 s1 tl1 s1'" and \<tau>1: "\<tau>move1 s1 tl1 s1'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb12.simulation_silent1[OF bisim1 tr1 \<tau>1] obtain s2'
      where tr2: "trsys2.\<tau>moves s2 s2'" and bisim1': "bisim12 s1' s2'" by blast
    from wb23.simulation_silents1[OF bisim2 tr2] obtain s3'
      where "trsys3.\<tau>moves s3 s3'" "bisim23 s2' s3'" by blast
    with bisim1' show "\<exists>s3'. trsys3.\<tau>moves s3 s3' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1' s3'"
      by(blast intro: bisim_composeI)
  next
    fix s1 s3 tl3 s3'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
      and tr3: "trsys3 s3 tl3 s3'" and \<tau>3: "\<tau>move3 s3 tl3 s3'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb23.simulation_silent2[OF bisim2 tr3 \<tau>3] obtain s2'
      where tr2: "trsys2.\<tau>moves s2 s2'" and bisim2': "bisim23 s2' s3'" by blast
    from wb12.simulation_silents2[OF bisim1 tr2] obtain s1'
      where "trsys1.\<tau>moves s1 s1'" "bisim12 s1' s2'" by blast
    with bisim2' show "\<exists>s1'. trsys1.\<tau>moves s1 s1' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1' s3'"
      by(blast intro: bisim_composeI)
  next
    fix s1 s3 tl1 s1'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
      and tr1: "trsys1 s1 tl1 s1'" and \<tau>1: "\<not> \<tau>move1 s1 tl1 s1'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb12.simulation1[OF bisim1 tr1 \<tau>1] obtain s2' s2'' tl2
      where tr21: "trsys2.\<tau>moves s2 s2'" and tr22: "trsys2 s2' tl2 s2''" and \<tau>2: "\<not> \<tau>move2 s2' tl2 s2''"
      and bisim1': "bisim12 s1' s2''" and tlsim1: "tlsim12 tl1 tl2" by blast
    from wb23.simulation_silents1[OF bisim2 tr21] obtain s3'
      where tr31: "trsys3.\<tau>moves s3 s3'" and bisim2': "bisim23 s2' s3'" by blast
    from wb23.simulation1[OF bisim2' tr22 \<tau>2] obtain s3'' s3''' tl3
      where "trsys3.\<tau>moves s3' s3''" "trsys3 s3'' tl3 s3'''"
      "\<not> \<tau>move3 s3'' tl3 s3'''" "bisim23 s2'' s3'''" "tlsim23 tl2 tl3" by blast
    with tr31 bisim1' tlsim1 
    show "\<exists>s3' s3'' tl3. trsys3.\<tau>moves s3 s3' \<and> trsys3 s3' tl3 s3'' \<and> \<not> \<tau>move3 s3' tl3 s3'' \<and>
                         (bisim12 \<circ>\<^isub>B bisim23) s1' s3'' \<and> (tlsim12 \<circ>\<^isub>B tlsim23) tl1 tl3"
      unfolding trsys3.\<tau>moves_def by(blast intro: rtranclp_trans bisim_composeI)
  next
    fix s1 s3 tl3 s3'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
      and tr3: "trsys3 s3 tl3 s3'" and \<tau>3: "\<not> \<tau>move3 s3 tl3 s3'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb23.simulation2[OF bisim2 tr3 \<tau>3] obtain s2' s2'' tl2
      where tr21: "trsys2.\<tau>moves s2 s2'" and tr22: "trsys2 s2' tl2 s2''" and \<tau>2: "\<not> \<tau>move2 s2' tl2 s2''"
      and bisim2': "bisim23 s2'' s3'" and tlsim2: "tlsim23 tl2 tl3" by blast
    from wb12.simulation_silents2[OF bisim1 tr21] obtain s1'
      where tr11: "trsys1.\<tau>moves s1 s1'" and bisim1': "bisim12 s1' s2'" by blast
    from wb12.simulation2[OF bisim1' tr22 \<tau>2] obtain s1'' s1''' tl1
      where "trsys1.\<tau>moves s1' s1''" "trsys1 s1'' tl1 s1'''"
      "\<not> \<tau>move1 s1'' tl1 s1'''" "bisim12 s1''' s2''" "tlsim12 tl1 tl2" by blast
    with tr11 bisim2' tlsim2
    show "\<exists>s1' s1'' tl1. trsys1.\<tau>moves s1 s1' \<and> trsys1 s1' tl1 s1'' \<and> \<not> \<tau>move1 s1' tl1 s1'' \<and>
                         (bisim12 \<circ>\<^isub>B bisim23) s1'' s3' \<and> (tlsim12 \<circ>\<^isub>B tlsim23) tl1 tl3"
      unfolding trsys1.\<tau>moves_def by(blast intro: rtranclp_trans bisim_composeI)
  qed
qed


fun nta_bisim :: "('a \<times> 'b, 'c \<times> 'b) bisim \<Rightarrow> (('t,'a,'b) new_thread_action, ('t,'c,'b) new_thread_action) bisim"
  where
  [code del]: "nta_bisim bisim (NewThread t x m) ta = (\<exists>x' m'. ta = NewThread t x' m' \<and> bisim (x, m) (x', m'))"
| "nta_bisim bisim NewThreadFail ta = (ta = NewThreadFail)"
| "nta_bisim bisim (ThreadExists t) ta = (ta = ThreadExists t)"

lemma nta_bisim_1_code [code]:
  "nta_bisim bisim (NewThread t x m) ta = (case ta of NewThread t' x' m' \<Rightarrow> t = t' \<and> bisim (x, m) (x', m') | _ \<Rightarrow> False)"
by(auto split: new_thread_action.split)
  
lemma nta_bisim_simps_sym [simp]:
  "nta_bisim bisim ta (NewThread t x m) = (\<exists>x' m'. ta = NewThread t x' m' \<and> bisim (x', m') (x, m))"
  "nta_bisim bisim ta NewThreadFail = (ta = NewThreadFail)"
  "nta_bisim bisim ta (ThreadExists t) = (ta = ThreadExists t)"
by(cases ta, auto)+

definition ta_bisim :: "('a \<times> 'b, 'c \<times> 'b) bisim \<Rightarrow> (('d,'e,'a,'b,'f) thread_action, ('d,'e,'c,'b,'f) thread_action) bisim"
where
  "ta_bisim bisim ta1 ta2 \<equiv>
  \<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub> \<and> list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>"

lemma ta_bisim_empty [iff]: "ta_bisim bisim \<epsilon> \<epsilon>"
by(auto simp add: ta_bisim_def)

lemma ta_bisim_\<epsilon> [simp]:
  "ta_bisim b \<epsilon> ta' \<longleftrightarrow> ta' = \<epsilon>" "ta_bisim b ta \<epsilon> \<longleftrightarrow> ta = \<epsilon>"
apply(cases ta', fastsimp simp add: ta_bisim_def)
apply(cases ta, fastsimp simp add: ta_bisim_def)
done

lemma nta_bisim_mono:
  assumes major: "nta_bisim bisim ta ta'"
  and mono: "\<And>s1 s2. bisim s1 s2 \<Longrightarrow> bisim' s1 s2"
  shows "nta_bisim bisim' ta ta'"
using major by(cases ta)(auto intro: mono)

lemma ta_bisim_mono:
  assumes major: "ta_bisim bisim ta1 ta2"
  and mono: "\<And>s1 s2. bisim s1 s2 \<Longrightarrow> bisim' s1 s2"
  shows "ta_bisim bisim' ta1 ta2"
using major
by(auto simp add: ta_bisim_def elim!: list_all2_mono nta_bisim_mono intro: mono)

locale FWbisimulation_base =
  r1!: multithreaded final1 r1 +
  r2!: multithreaded final2 r2 
  for final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l,'t,'x1,'m,'w) semantics" ("_ -1-_\<rightarrow> _" [50,0,50] 80)
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l,'t,'x2,'m,'w) semantics" ("_ -2-_\<rightarrow> _" [50,0,50] 80) +
  fixes bisim :: "('x1 \<times> 'm, 'x2 \<times> 'm) bisim" ("_/ \<approx> _" [50, 50] 60)
(*  assumes type_constraint:
  "\<lbrakk> bisim (x1, m1) (x2, m2); r1 (x1, m1) ta1 (x1', m1'); r2 (x2, m2) ta2 (x2', m2');
     \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>; \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>; \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> True" *)
begin

notation r1.redT_syntax1 ("_ -1-_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)
notation r2.redT_syntax1 ("_ -2-_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)

notation r1.RedT ("_ -1-\<triangleright>_\<rightarrow>* _" [50,0,50] 80)
notation r2.RedT ("_ -2-\<triangleright>_\<rightarrow>* _" [50,0,50] 80)

notation r1.must_sync ("\<langle>_,/ _\<rangle>/ \<wrong>1" [0,0] 81)
notation r2.must_sync ("\<langle>_,/ _\<rangle>/ \<wrong>2" [0,0] 81)

notation r1.can_sync  ("\<langle>_,/ _\<rangle>/ _/ \<wrong>1" [0,0,0] 81)
notation r2.can_sync  ("\<langle>_,/ _\<rangle>/ _/ \<wrong>2" [0,0,0] 81)

abbreviation ta_bisim_bisim_syntax ("_/ \<sim>m _" [50, 50] 60)
where "ta1 \<sim>m ta2 \<equiv> ta_bisim bisim ta1 ta2"

definition tbisim :: "('x1 \<times> ('l \<Rightarrow>\<^isub>f nat)) option \<Rightarrow> 'm \<Rightarrow> ('x2 \<times> ('l \<Rightarrow>\<^isub>f nat)) option \<Rightarrow> 'm \<Rightarrow> bool" where
  "tbisim ts1 m1 ts2 m2 \<longleftrightarrow> (case ts1 of None \<Rightarrow> ts2 = None
                                 | \<lfloor>(x1, ln)\<rfloor> \<Rightarrow> (\<exists>x2. ts2 = \<lfloor>(x2, ln)\<rfloor> \<and> (x1, m1) \<approx> (x2, m2)))"

definition mbisim :: "(('l,'t,'x1,'m,'w) state, ('l,'t,'x2,'m,'w) state) bisim" ("_ \<approx>m _" [50, 50] 60)
where
  "s1 \<approx>m s2 \<equiv> locks s1 = locks s2 \<and> wset s1 = wset s2 \<and> (\<forall>t. tbisim (thr s1 t) (shr s1) (thr s2 t) (shr s2))"

lemma mbisim_thrNone_eq: "s1 \<approx>m s2 \<Longrightarrow> thr s1 t = None \<longleftrightarrow> thr s2 t = None"
unfolding mbisim_def tbisim_def
apply(clarify)
apply(erule_tac x=t in allE)
apply(clarsimp)
done

lemma mbisim_thrD1: "\<lbrakk> s1 \<approx>m s2; thr s1 t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>x'. thr s2 t = \<lfloor>(x', ln)\<rfloor> \<and> (x, shr s1) \<approx> (x', shr s2)"
by(auto simp add: mbisim_def tbisim_def)

lemma mbisim_thrD2: "\<lbrakk> s1 \<approx>m s2; thr s2 t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>x'. thr s1 t = \<lfloor>(x', ln)\<rfloor> \<and> (x', shr s1) \<approx> (x, shr s2)"
by(frule mbisim_thrNone_eq[where t=t])(cases "thr s1 t",(fastsimp simp add: mbisim_def tbisim_def)+)

lemma mbisimI:
  "\<lbrakk> locks s1 = locks s2; wset s1 = wset s2;
     \<And>t. thr s1 t = None \<Longrightarrow> thr s2 t = None;
     \<And>t x1 ln. thr s1 t = \<lfloor>(x1, ln)\<rfloor> \<Longrightarrow> \<exists>x2. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<and> (x1, shr s1) \<approx> (x2, shr s2) \<rbrakk>
  \<Longrightarrow> s1 \<approx>m s2"
by(auto simp add: mbisim_def tbisim_def)

lemma mbisimI2:
  "\<lbrakk> locks s1 = locks s2; wset s1 = wset s2;
     \<And>t. thr s2 t = None \<Longrightarrow> thr s1 t = None;
     \<And>t x2 ln. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<Longrightarrow> \<exists>x1. thr s1 t = \<lfloor>(x1, ln)\<rfloor> \<and> (x1, shr s1) \<approx> (x2, shr s2) \<rbrakk>
  \<Longrightarrow> s1 \<approx>m s2"
apply(auto simp add: mbisim_def tbisim_def)
apply(case_tac [!] "thr s2 t")
by fastsimp+

definition mta_bisim :: "('t \<times> ('l,'t,'x1,'m,'w) thread_action, 't \<times> ('l,'t,'x2,'m,'w) thread_action) bisim"
  ("_/ \<sim>T _" [50, 50] 60)
where "tta1 \<sim>T tta2 \<equiv> fst tta1 = fst tta2 \<and> snd tta1 \<sim>m snd tta2"

lemma mta_bisim_conv [simp]: "(t, ta1) \<sim>T (t', ta2) \<longleftrightarrow> t = t' \<and> ta1 \<sim>m ta2"
by(simp add: mta_bisim_def)

definition bisim_inv :: "bool" where
  "bisim_inv \<equiv> (\<forall>s1 ta1 s1' s2. s1 \<approx> s2 \<longrightarrow> s1 -1-ta1\<rightarrow> s1' \<longrightarrow> (\<exists>s2'. s1' \<approx> s2')) \<and>
               (\<forall>s2 ta2 s2' s1. s1 \<approx> s2 \<longrightarrow> s2 -2-ta2\<rightarrow> s2' \<longrightarrow> (\<exists>s1'. s1' \<approx> s2'))"

lemma bisim_invI:
  "\<lbrakk> \<And>s1 ta1 s1' s2. \<lbrakk> s1 \<approx> s2; s1 -1-ta1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. s1' \<approx> s2';
     \<And>s2 ta2 s2' s1. \<lbrakk> s1 \<approx> s2; s2 -2-ta2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1' \<approx> s2' \<rbrakk>
  \<Longrightarrow> bisim_inv"
by(auto simp add: bisim_inv_def)

lemma bisim_invD1:
  "\<lbrakk> bisim_inv; s1 \<approx> s2; s1 -1-ta1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. s1' \<approx> s2'"
unfolding bisim_inv_def by blast

lemma bisim_invD2:
  "\<lbrakk> bisim_inv; s1 \<approx> s2; s2 -2-ta2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1' \<approx> s2'"
unfolding bisim_inv_def by blast

lemma thread_oks_bisim_inv:
  "\<lbrakk> \<forall>t. ts1 t = None \<longleftrightarrow> ts2 t = None; list_all2 (nta_bisim bisim) tas1 tas2 \<rbrakk>
  \<Longrightarrow> thread_oks ts1 tas1 \<longleftrightarrow> thread_oks ts2 tas2"
proof(induct tas2 arbitrary: tas1 ts1 ts2)
  case Nil thus ?case by(simp)
next
  case (Cons ta2 TAS2 tas1 TS1 TS2)
  note IH = `\<And>ts1 tas1 ts2. \<lbrakk> \<forall>t. ts1 t = None \<longleftrightarrow> ts2 t = None; list_all2 (nta_bisim bisim) tas1 TAS2 \<rbrakk>
             \<Longrightarrow> thread_oks ts1 tas1 \<longleftrightarrow> thread_oks ts2 TAS2`
  note eqNone = `\<forall>t. TS1 t = None \<longleftrightarrow> TS2 t = None`[rule_format]
  hence fti: "free_thread_id TS1 = free_thread_id TS2" by(auto simp add: free_thread_id_def)
  from `list_all2 (nta_bisim bisim) tas1 (ta2 # TAS2)`
  obtain ta1 TAS1 where "tas1 = ta1 # TAS1" "nta_bisim bisim ta1 ta2" "list_all2 (nta_bisim bisim) TAS1 TAS2"
    by(auto simp add: list_all2_Cons2)
  moreover
  { fix t
    from `nta_bisim bisim ta1 ta2` have "redT_updT' TS1 ta1 t = None \<longleftrightarrow> redT_updT' TS2 ta2 t = None"
      by(cases ta1, auto split: split_if_asm simp add: eqNone) }
  ultimately have "thread_oks (redT_updT' TS1 ta1) TAS1 \<longleftrightarrow> thread_oks (redT_updT' TS2 ta2) TAS2"
    by -(rule IH, auto)
  moreover from `nta_bisim bisim ta1 ta2` fti have "thread_ok TS1 ta1 = thread_ok TS2 ta2" by(cases ta1, auto)
  ultimately show ?case using `tas1 = ta1 # TAS1` by auto
qed

lemma redT_updT_nta_bisim_inv:
  "\<lbrakk> nta_bisim bisim ta1 ta2; ts1 T = None \<longleftrightarrow> ts2 T = None \<rbrakk> \<Longrightarrow> redT_updT ts1 ta1 T = None \<longleftrightarrow> redT_updT ts2 ta2 T = None"
by(cases ta1, auto)

lemma redT_updTs_nta_bisim_inv:
  "\<lbrakk> list_all2 (nta_bisim bisim) tas1 tas2; ts1 T = None \<longleftrightarrow> ts2 T = None \<rbrakk>
  \<Longrightarrow> redT_updTs ts1 tas1 T = None \<longleftrightarrow> redT_updTs ts2 tas2 T = None"
proof(induct tas1 arbitrary: tas2 ts1 ts2)
  case Nil thus ?case by(simp)
next
  case (Cons TA1 TAS1 tas2 TS1 TS2)
  note IH = `\<And>tas2 ts1 ts2. \<lbrakk>list_all2 (nta_bisim bisim) TAS1 tas2; (ts1 T = None) = (ts2 T = None)\<rbrakk>
            \<Longrightarrow> (redT_updTs ts1 TAS1 T = None) = (redT_updTs ts2 tas2 T = None)`
  from `list_all2 (nta_bisim bisim) (TA1 # TAS1) tas2`
  obtain TA2 TAS2 where "tas2 = TA2 # TAS2" "nta_bisim bisim TA1 TA2" "list_all2 (nta_bisim bisim) TAS1 TAS2"
    by(auto simp add: list_all2_Cons1)
  from `nta_bisim bisim TA1 TA2` `(TS1 T = None) = (TS2 T = None)`
  have "redT_updT TS1 TA1 T = None \<longleftrightarrow> redT_updT TS2 TA2 T = None"
    by(rule redT_updT_nta_bisim_inv)
  with IH[OF `list_all2 (nta_bisim bisim) TAS1 TAS2`, of "redT_updT TS1 TA1" "redT_updT TS2 TA2"] `tas2 = TA2 # TAS2`
  show ?case by simp
qed

end

locale FWbisimulation_base_aux = FWbisimulation_base _ _ _ r2 bisim
  for r2 :: "('l,'t,'x2,'m,'w) semantics" ("_ -2-_\<rightarrow> _" [50,0,50] 80)
  and bisim :: "('x1 \<times> 'm, 'x2 \<times> 'm) bisim" ("_/ \<approx> _" [50, 50] 60) +
  assumes bisim_final: "(x1, m1) \<approx> (x2, m2) \<Longrightarrow> final1 x1 \<longleftrightarrow> final2 x2"
begin

lemma cond_action_ok_tbisim_inv:
  assumes mbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ts1 t') m1 (ts2 t') m2"
  and ts: "ts1 t = None \<longleftrightarrow> ts2 t = None"
  shows "r1.cond_action_ok (ls, (ts1, m1), ws) t ct = r2.cond_action_ok (ls, (ts2, m2), ws) t ct"
proof(cases ct)
  case (Join t')
  moreover from ts mbisim[of t'] have "ts1 t' = None \<longleftrightarrow> ts2 t' = None"
    by(cases "t' = t")(auto simp add: tbisim_def)
  moreover
  { fix x1 ln1 x2 ln2
    assume ts1t': "ts1 t' = \<lfloor>(x1, ln1)\<rfloor>"
      and ts2t': "ts2 t' = \<lfloor>(x2, ln2)\<rfloor>"
      and t't: "t' \<noteq> t"
    from mbisim[OF t't] ts1t' ts2t'
    have bisim: "(x1, m1) \<approx> (x2, m2)" and ln: "ln1 = ln2" by(simp_all add: tbisim_def)
    from bisim have "final1 x1 \<longleftrightarrow> final2 x2" by(rule bisim_final)
    note this ln }
  ultimately show ?thesis by clarsimp blast
qed

lemma cond_actions_ok_tbisim_inv:
  assumes mbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ts1 t') m1 (ts2 t') m2"
  and ts: "ts1 t = None \<longleftrightarrow> ts2 t = None"
  shows "r1.cond_action_oks (ls, (ts1, m1), ws) t cts = r2.cond_action_oks (ls, (ts2, m2), ws) t cts"
using assms
apply(induct cts)
apply auto
apply(erule cond_action_ok_tbisim_inv[THEN iffD1] cond_action_ok_tbisim_inv[THEN iffD2], simp_all)+
done

lemma tbisim_actions_ok_inv:
  assumes mbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ts1 t') m1 (ts2 t') m2"
  and tasim: "ta_bisim bisim ta1 ta2"
  and ts: "ts1 t = None \<longleftrightarrow> ts2 t = None"
  shows "r1.actions_ok (ls, (ts1, m1), ws) t ta1 = r2.actions_ok (ls, (ts2, m2), ws) t ta2"
proof -
  from tasim have nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>"
    and [simp]: "\<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub>"
    by(auto simp add: ta_bisim_def)
  from mbisim ts
  have cao: "r1.cond_action_oks (ls, (ts1, m1), ws) t \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> = r2.cond_action_oks (ls, (ts2, m2), ws) t \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub>"
    by(rule cond_actions_ok_tbisim_inv)
  moreover
  { fix t'
    from ts have "ts1 t' = None \<longleftrightarrow> ts2 t' = None"
      by(cases "t' = t")(auto dest: mbisim simp add: tbisim_def) }
  hence "thread_oks ts1 \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = thread_oks ts2 \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" using nta
    by(rule thread_oks_bisim_inv[OF allI])
  ultimately show ?thesis by simp
qed

corollary mbisim_actions_ok_inv:
  assumes mbisim: "s1 \<approx>m s2"
  and tasim: "ta_bisim bisim ta1 ta2"
  shows "r1.actions_ok s1 t ta1 = r2.actions_ok s2 t ta2"
proof -
  obtain ls1 ts1 m1 ws1 where s1: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1) auto
  obtain ls2 ts2 m2 ws2 where s2: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2) auto
  from mbisim s1 s2 have tbisim: "\<And>t'. tbisim (ts1 t') m1 (ts2 t') m2" and [simp]: "ls1 = ls2" "ws1 = ws2"
    by(simp_all add: mbisim_def)
  from tbisim[of t] have "ts1 t = None \<longleftrightarrow> ts2 t = None" by(auto simp add: tbisim_def)
  with tbisim tasim 
  have "r1.actions_ok (ls1, (ts1, m1), ws1) t ta1 = r2.actions_ok (ls1, (ts2, m2), ws1) t ta2"
    by(rule tbisim_actions_ok_inv)
  with s1 s2 show ?thesis by simp
qed

end

locale \<tau>multithreaded = multithreaded _ r +
  \<tau>trsys r \<tau>move
  for  r :: "('l,'t,'x,'m,'w) semantics" ("_ -_\<rightarrow> _" [50,0,50] 80)
  and \<tau>move :: "('l,'t,'x,'m,'w) semantics"
begin

inductive m\<tau>move :: "(('l,'t,'x,'m,'w) state, 't \<times> ('l,'t,'x,'m,'w) thread_action) trsys"
where
  "\<lbrakk> shr s = shr s'; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; thr s' t = \<lfloor>(x', ln')\<rfloor>; \<tau>move (x, shr s) \<epsilon> (x', shr s');
     s \<noteq> s' \<Longrightarrow> (THE t. thr s t \<noteq> None \<and> thr s t \<noteq> thr s' t) = t \<rbrakk>
  \<Longrightarrow> m\<tau>move s (t, \<epsilon>) s'"

end

sublocale \<tau>multithreaded < mthr!: \<tau>trsys redT m\<tau>move .

context \<tau>multithreaded begin

definition \<tau>mredT :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "\<tau>mredT s s' \<equiv> (\<exists>t. s -t\<triangleright>\<epsilon>\<rightarrow> s' \<and> m\<tau>move s (t, \<epsilon>) s')"

abbreviation \<tau>mRedT :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "\<tau>mRedT \<equiv> \<tau>mredT^**"

lemma m\<tau>move_silentD: "m\<tau>move s (t, ta) s' \<Longrightarrow> ta = \<epsilon>"
by(auto elim: m\<tau>move.cases)

lemma \<tau>mredT_thread_preserved:
  "\<tau>mredT s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(auto simp add: \<tau>mredT_def elim!: redT.cases split: split_if_asm)

lemma \<tau>mRedT_thread_preserved:
  "\<tau>mRedT s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(induct rule: rtranclp.induct)(auto dest: \<tau>mredT_thread_preserved[where t=t])

lemma \<tau>mredT_add_thread_inv:
  assumes \<tau>red: "\<tau>mredT s s'" and tst: "thr s t = None"
  shows "\<tau>mredT (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s')"
proof -
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by(cases s) auto
  obtain ls' ts' m' ws' where s': "s' = (ls', (ts', m'), ws')" by(cases s') auto
  from \<tau>red s s' obtain t' where red: "(ls, (ts, m), ws) -t'\<triangleright>\<epsilon>\<rightarrow> (ls', (ts', m'), ws')"
    and \<tau>: "m\<tau>move (ls, (ts, m), ws) (t', \<epsilon>) (ls', (ts', m'), ws')" by(auto simp add: \<tau>mredT_def)
  from red have "(ls, (ts(t \<mapsto> xln), m), ws) -t'\<triangleright>\<epsilon>\<rightarrow> (ls', (ts'(t \<mapsto> xln), m'), ws')"
  proof(cases rule: redT_elims4)
    case normal with tst s show ?thesis
      by -(rule redT_normal, auto simp add: fun_upd_twist)
  next
    case acquire with tst s show ?thesis
      by -(rule redT_acquire, auto intro: fun_upd_twist)
  qed
  moreover from red tst s have tt': "t \<noteq> t'" by(cases) auto
  have "(\<lambda>t''. (ts(t \<mapsto> xln)) t'' \<noteq> None \<and> (ts(t \<mapsto> xln)) t'' \<noteq> (ts'(t \<mapsto> xln)) t'') =
        (\<lambda>t''. ts t'' \<noteq> None \<and> ts t'' \<noteq> ts' t'')" using tst s by(auto simp add: expand_fun_eq)
  with \<tau> tst tt' have "m\<tau>move (ls, (ts(t \<mapsto> xln), m), ws) (t', \<epsilon>) (ls', (ts'(t \<mapsto> xln), m'), ws')"
    by(cases)(rule m\<tau>move.intros, fastsimp+)
  ultimately show ?thesis unfolding \<tau>mredT_def s s' by auto
qed

lemma \<tau>mRedT_add_thread_inv:
  "\<lbrakk> \<tau>mRedT s s'; thr s t = None \<rbrakk>
  \<Longrightarrow> \<tau>mRedT (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s')"
apply(induct rule: rtranclp_induct)
apply(blast dest: \<tau>mRedT_thread_preserved[where t=t] \<tau>mredT_add_thread_inv[where xln=xln] intro: rtranclp.rtrancl_into_rtrancl)+
done

end

locale \<tau>multithreaded_wf =
  \<tau>multithreaded _ _ \<tau>move
  for \<tau>move :: "('l,'t,'x,'m,'w) semantics" +
  fixes wfs :: "'x \<times> 'm \<Rightarrow> bool"
  assumes \<tau>move_heap: "\<lbrakk> wfs (x, m); (x, m) -ta\<rightarrow> (x', m'); \<tau>move (x, m) ta (x', m') \<rbrakk> \<Longrightarrow> m = m'"
  and no_change_\<tau>move: "\<lbrakk> wfs s; s -\<epsilon>\<rightarrow> s \<rbrakk> \<Longrightarrow> \<tau>move s \<epsilon> s"
  assumes silent_tl: "\<tau>move s ta s' \<Longrightarrow> ta = \<epsilon>"
begin

definition wfs_inv :: "bool" where
  "wfs_inv \<equiv> (\<forall>s ta s'. wfs s \<longrightarrow> s -ta\<rightarrow> s' \<longrightarrow> wfs s')"

lemma wfs_invI:
  "(\<And>s ta s'. \<lbrakk> wfs s; s -ta\<rightarrow> s' \<rbrakk> \<Longrightarrow> wfs s')
  \<Longrightarrow> wfs_inv"
by(auto simp add: wfs_inv_def)

lemma wfs_invD:
  "\<lbrakk> wfs_inv; wfs s; s -ta\<rightarrow> s' \<rbrakk> \<Longrightarrow> wfs s'"
unfolding wfs_inv_def by blast

lemma wfs_inv_\<tau>s_inv:
  assumes inv: "wfs_inv" and wfs: "wfs s"
  and red: "(\<lambda>s s'. s -\<epsilon>\<rightarrow> s' \<and> \<tau>move s \<epsilon> s')\<^sup>*\<^sup>* s s'"
  shows "wfs s'"
using red wfs
by(induct rule: rtranclp_induct)(fastsimp elim: wfs_invD[OF inv])+

 
declare split_paired_Ex [simp del]

lemma \<tau>red_conv [simp]:
  "(\<lambda>s s'. \<exists>ta. s -ta\<rightarrow> s' \<and> \<tau>move s ta s') = (\<lambda>s s'. s -\<epsilon>\<rightarrow> s' \<and> \<tau>move s \<epsilon> s')"
by(auto intro!: ext dest: silent_tl)

lemma m\<tau>red_conv [simp]:
  "(\<lambda>s s'. \<exists>tta. redT s tta s' \<and> m\<tau>move s tta s') = (\<lambda>s s'. \<exists>t. s -t\<triangleright>\<epsilon>\<rightarrow> s' \<and> m\<tau>move s (t, \<epsilon>) s')"
by(auto intro!: ext dest: m\<tau>move_silentD)

lemma red_rtrancl_\<tau>_into_RedT_\<tau>_inv:
  assumes inv: "wfs_inv"
  and major: "(\<lambda>s s'. s -\<epsilon>\<rightarrow> s' \<and> \<tau>move s \<epsilon> s')\<^sup>*\<^sup>* (x, shr s) (x', m')"
  and bisim: "wfs (x, shr s)"
  and state: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "\<tau>mRedT s (redT_upd s t \<epsilon> x' m')"
using major bisim
proof(induct rule: rtranclp_induct2)
  case refl with state show ?case
    by(cases s)(auto simp add: redT_updLs_def redT_updLns_def fun_upd_idem o_def finfun_Diag_const2)
next
  case (step x' m' x'' m'')
  note IH = `wfs (x, shr s) \<Longrightarrow> \<tau>mRedT s (redT_upd s t \<epsilon> x' m')`
  from `(x', m') -\<epsilon>\<rightarrow> (x'', m'') \<and> \<tau>move (x', m') \<epsilon> (x'', m'')`
  obtain red: "(x', m') -\<epsilon>\<rightarrow> (x'', m'')" and \<tau>: "\<tau>move (x', m') \<epsilon> (x'', m'')" ..
  from red state have "redT_upd s t \<epsilon> x' m' -t\<triangleright>\<epsilon>\<rightarrow> redT_upd s t \<epsilon> x'' m''"
    by -(rule redT_normal, auto simp add: redT_updLns_def redT_updLs_def o_def finfun_Diag_const2)
  moreover from `wfs (x, shr s)` `(\<lambda>s s'. s -\<epsilon>\<rightarrow> s' \<and> \<tau>move s \<epsilon> s')\<^sup>*\<^sup>* (x, shr s) (x', m')`
  have wfs': "wfs (x', m')" by(rule wfs_inv_\<tau>s_inv[OF inv])
  from \<tau> red state have "m\<tau>move (redT_upd s t \<epsilon> x' m') (t, \<epsilon>) (redT_upd s t \<epsilon> x'' m'')"
    by -(rule m\<tau>move.intros, auto dest: \<tau>move_heap[OF wfs'] simp add: redT_updLns_def o_def finfun_Diag_const2)
  ultimately show ?case using IH[OF `wfs (x, shr s)`]
    by -(erule rtranclp.rtrancl_into_rtrancl, auto simp add: \<tau>mredT_def)
qed

lemma red_rtrancl_\<tau>_heapD_inv:
  assumes inv: "wfs_inv"
  shows "\<lbrakk> (\<lambda>s s'. s -\<epsilon>\<rightarrow> s' \<and> \<tau>move s \<epsilon> s')\<^sup>*\<^sup>* s s'; wfs s \<rbrakk> \<Longrightarrow> snd s' = snd s"
proof(induct rule: rtranclp_induct)
  case base show ?case ..
next
  case (step s' s'')
  thus ?case by(cases s, cases s', cases s'')(auto dest: \<tau>move_heap  wfs_inv_\<tau>s_inv[OF inv])
qed

end


locale FWweak_bisimulation_base =
  FWbisimulation_base _ _ _ r2 bisim +
  r1!: \<tau>multithreaded final1 r1 \<tau>move1 +
  r2!: \<tau>multithreaded final2 r2 \<tau>move2 
  for r2 :: "('l,'t,'x2,'m,'w) semantics" ("_ -2-_\<rightarrow> _" [50,0,50] 80)
  and bisim :: "('x1 \<times> 'm, 'x2 \<times> 'm) bisim" ("_/ \<approx> _" [50, 50] 60)
  and \<tau>move1 :: "('l,'t,'x1,'m,'w) semantics"
  and \<tau>move2 :: "('l,'t,'x2,'m,'w) semantics"
begin

(*
locale FWweak_bisimulation_base =
  FWbisimulation_base final1 r1 ("_ -1-_\<rightarrow> _" [50,0,50] 80) final2 r2 ("_ -2-_\<rightarrow> _" [50,0,50] 80) _ +
  \<tau>multithreaded final1 r1 ("_ -1-_\<rightarrow> _" [50,0,50] 80) \<tau>move1 +
  \<tau>multithreaded final2 r2 ("_ -2-_\<rightarrow> _" [50,0,50] 80) \<tau>move2
begin
*)

abbreviation \<tau>mred1 :: "('l,'t,'x1,'m,'w) state \<Rightarrow> ('l,'t,'x1,'m,'w) state \<Rightarrow> bool"
where "\<tau>mred1 \<equiv> r1.\<tau>mredT"

abbreviation \<tau>mred2 :: "('l,'t,'x2,'m,'w) state \<Rightarrow> ('l,'t,'x2,'m,'w) state \<Rightarrow> bool"
where "\<tau>mred2 \<equiv> r2.\<tau>mredT"

abbreviation m\<tau>move1 :: "(('l,'t,'x1,'m,'w) state, 't \<times> ('l,'t,'x1,'m,'w) thread_action) trsys"
where "m\<tau>move1 \<equiv> r1.m\<tau>move"

abbreviation m\<tau>move2 :: "(('l,'t,'x2,'m,'w) state, 't \<times> ('l,'t,'x2,'m,'w) thread_action) trsys"
where "m\<tau>move2 \<equiv> r2.m\<tau>move"

lemma \<tau>mred1_def: "\<tau>mred1 s s' \<equiv> (\<exists>t. s -1-t\<triangleright>\<epsilon>\<rightarrow> s' \<and> m\<tau>move1 s (t, \<epsilon>) s')"
by(rule r1.\<tau>mredT_def)

lemma \<tau>mred1_def_raw: "\<tau>mred1 \<equiv> (\<lambda>s s'. \<exists>t. s -1-t\<triangleright>\<epsilon>\<rightarrow> s' \<and> m\<tau>move1 s (t, \<epsilon>) s')"
by(rule r1.\<tau>mredT_def_raw)

lemma \<tau>mred2_def: "\<tau>mred2 s s' \<equiv> (\<exists>t. s -2-t\<triangleright>\<epsilon>\<rightarrow> s' \<and> m\<tau>move2 s (t, \<epsilon>) s')"
by(rule r2.\<tau>mredT_def)

lemma \<tau>mred2_def_raw: "\<tau>mred2 \<equiv> (\<lambda>s s'. \<exists>t. s -2-t\<triangleright>\<epsilon>\<rightarrow> s' \<and> m\<tau>move2 s (t, \<epsilon>) s')"
by(rule r2.\<tau>mredT_def_raw)

lemma m\<tau>move1_intros:
  "\<lbrakk> shr s = shr s'; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
     thr s' t = \<lfloor>(x', ln')\<rfloor>; \<tau>move1 (x, shr s) \<epsilon> (x', shr s');
    s \<noteq> s' \<Longrightarrow> (THE t. thr s t \<noteq> None \<and> thr s t \<noteq> thr s' t) = t \<rbrakk>
  \<Longrightarrow> m\<tau>move1 s (t, \<epsilon>) s'"
by(rule r1.m\<tau>move.intros)

lemma m\<tau>move2_intros:
  "\<lbrakk> shr s = shr s'; thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>;
     thr s' t = \<lfloor>(x', ln')\<rfloor>; \<tau>move2 (x, shr s) \<epsilon> (x', shr s');
    s \<noteq> s' \<Longrightarrow> (THE t. thr s t \<noteq> None \<and> thr s t \<noteq> thr s' t) = t \<rbrakk>
  \<Longrightarrow> m\<tau>move2 s (t, \<epsilon>) s'"
by(rule r2.m\<tau>move.intros)

lemma m\<tau>move1_cases:
  assumes "m\<tau>move1 s tta s'"
  obtains t x x' ln'
  where "tta = (t, \<epsilon>)" "shr s = shr s'"
    "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "thr s' t = \<lfloor>(x', ln')\<rfloor>" "\<tau>move1 (x, shr s) \<epsilon> (x', shr s')"
    "s \<noteq> s' \<Longrightarrow> (THE t. thr s t \<noteq> None \<and> thr s t \<noteq> thr s' t) = t"
using assms by(rule r1.m\<tau>move.cases) fastsimp

lemma m\<tau>move2_cases:
  assumes "m\<tau>move2 s tta s'"
  obtains t x x' ln'
  where "tta = (t, \<epsilon>)" "shr s = shr s'"
    "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "thr s' t = \<lfloor>(x', ln')\<rfloor>" "\<tau>move2 (x, shr s) \<epsilon> (x', shr s')"
    "s \<noteq> s' \<Longrightarrow> (THE t. thr s t \<noteq> None \<and> thr s t \<noteq> thr s' t) = t"
using assms by(rule r2.m\<tau>move.cases) fastsimp

abbreviation \<tau>mRed1 :: "('l,'t,'x1,'m,'w) state \<Rightarrow> ('l,'t,'x1,'m,'w) state \<Rightarrow> bool"
where "\<tau>mRed1 \<equiv> \<tau>mred1^**"

abbreviation \<tau>mRed2 :: "('l,'t,'x2,'m,'w) state \<Rightarrow> ('l,'t,'x2,'m,'w) state \<Rightarrow> bool"
where "\<tau>mRed2 \<equiv> \<tau>mred2^**"

lemma bisim_inv_\<tau>s1_inv:
  assumes inv: "bisim_inv"
  and bisim: "s1 \<approx> s2"
  and red: "(\<lambda>s1 s1'. s1 -1-\<epsilon>\<rightarrow> s1' \<and> \<tau>move1 s1 \<epsilon> s1')\<^sup>*\<^sup>* s1 s1'"
  obtains s2' where "s1' \<approx> s2'"
proof(atomize_elim)
  from red bisim show "\<exists>s2'. s1' \<approx> s2'"
    by(induct rule: rtranclp_induct)(fastsimp elim: bisim_invD1[OF inv])+
qed

lemma bisim_inv_\<tau>s2_inv:
  assumes inv: "bisim_inv"
  and bisim: "s1 \<approx> s2"
  and red: "(\<lambda>s2 s2'. s2 -2-\<epsilon>\<rightarrow> s2' \<and> \<tau>move2 s2 \<epsilon> s2')\<^sup>*\<^sup>* s2 s2'"
  obtains s1' where "s1' \<approx> s2'"
proof(atomize_elim)
  from red bisim show "\<exists>s1'. s1' \<approx> s2'"
    by(induct rule: rtranclp_induct)(fastsimp elim: bisim_invD2[OF inv])+
qed

end


locale FWweak_bisimulation_lift_aux =
  FWweak_bisimulation_base _ _ _ _ _ \<tau>move1 \<tau>move2 +
  r1!: \<tau>multithreaded_wf final1 r1 \<tau>move1 "\<lambda>s1. \<exists>s2. s1 \<approx> s2" +
  r2!: \<tau>multithreaded_wf final2 r2 \<tau>move2 "\<lambda>s2. \<exists>s1. s1 \<approx> s2"
  for \<tau>move1 :: "('l,'t,'x1,'m,'w) semantics"
  and \<tau>move2 :: "('l,'t,'x2,'m,'w) semantics"
begin

(*
locale FWweak_bisimulation_base_aux =
  FWweak_bisimulation_base final1 r1 ("_ -1-_\<rightarrow> _" [50,0,50] 80) final2 r2 ("_ -2-_\<rightarrow> _" [50,0,50] 80) _ \<tau>move1 \<tau>move2 +
  \<tau>multithreaded_wf final1 r1 ("_ -1-_\<rightarrow> _" [50,0,50] 80) \<tau>move1 wfs1 +
  \<tau>multithreaded_wf final2 r2 ("_ -2-_\<rightarrow> _" [50,0,50] 80) \<tau>move2 wfs2
begin
*)

lemma \<tau>red1_conv:
  "(\<lambda>s1 s1'. \<exists>ta1. s1 -1-ta1\<rightarrow> s1' \<and> \<tau>move1 s1 ta1 s1') = (\<lambda>s1 s1'. s1 -1-\<epsilon>\<rightarrow> s1' \<and> \<tau>move1 s1 \<epsilon> s1')"
by(rule r1.\<tau>red_conv)

lemma \<tau>red2_conv:
  "(\<lambda>s2 s2'. \<exists>ta2. s2 -2-ta2\<rightarrow> s2' \<and> \<tau>move2 s2 ta2 s2') = (\<lambda>s2 s2'. s2 -2-\<epsilon>\<rightarrow> s2' \<and> \<tau>move2 s2 \<epsilon> s2')"
by(rule r2.\<tau>red_conv)

lemma m\<tau>red1_conv:
  "(\<lambda>s1 s1'. \<exists>tta1. r1.redT s1 tta1 s1' \<and> m\<tau>move1 s1 tta1 s1') = (\<lambda>s1 s1'. \<exists>t. s1 -1-t\<triangleright>\<epsilon>\<rightarrow> s1' \<and> m\<tau>move1 s1 (t, \<epsilon>) s1')"
by(rule r1.m\<tau>red_conv)

lemma m\<tau>red2_conv:
  "(\<lambda>s2 s2'. \<exists>tta2. r2.redT s2 tta2 s2' \<and> m\<tau>move2 s2 tta2 s2') = (\<lambda>s2 s2'. \<exists>t. s2 -2-t\<triangleright>\<epsilon>\<rightarrow> s2' \<and> m\<tau>move2 s2 (t, \<epsilon>) s2')"
by(rule r2.m\<tau>red_conv)

lemma silent_tl1: "\<tau>move1 s1 ta1 s1' \<Longrightarrow> ta1 = \<epsilon>"
by(rule r1.silent_tl)

lemma silent_tl2: "\<tau>move2 s2 ta2 s2' \<Longrightarrow> ta2 = \<epsilon>"
by(rule r2.silent_tl)

(*
end

locale FWweak_bisimulation_lift_aux =
  FWweak_bisimulation_base +
  fixes wfs1 :: "'a \<times> 'b \<Rightarrow> bool" 
  and wfs2 :: "'f \<times> 'b \<Rightarrow> bool"
  defines wfs1_def [simp]: "wfs1 \<equiv> (\<lambda>s1. \<exists>s2. s1 \<approx> s2)"
  and wfs2_def [simp]: "wfs2 \<equiv> (\<lambda>s2. \<exists>s1. s1 \<approx> s2)"
  assumes wb: "FWweak_bisimulation_base_aux r1 r2 bisim \<tau>move1 \<tau>move2 wfs1 wfs2"

interpretation FWweak_bisimulation_lift_aux < FWweak_bisimulation_base_aux
by(rule wb)

context FWweak_bisimulation_lift_aux begin
*)

lemma \<tau>move_heap1:
  "\<lbrakk> (x1, m1) \<approx> (x2, m2); (x1, m1) -1-ta1\<rightarrow> (x1', m1'); \<tau>move1 (x1, m1) ta1 (x1', m1') \<rbrakk> \<Longrightarrow> m1 = m1'"
by(blast intro: r1.\<tau>move_heap)

lemma \<tau>move_heap2:
  "\<lbrakk> (x1, m1) \<approx> (x2, m2); (x2, m2) -2-ta2\<rightarrow> (x2', m2'); \<tau>move2 (x2, m2) ta2 (x2', m2') \<rbrakk> \<Longrightarrow> m2 = m2'"
by(blast intro: r2.\<tau>move_heap)

lemma no_change_\<tau>move1:
  "\<lbrakk> (x1, m1) \<approx> (x2, m2); (x1, m1) -1-\<epsilon>\<rightarrow> (x1, m1) \<rbrakk> \<Longrightarrow> \<tau>move1 (x1, m1) \<epsilon> (x1, m1)"
by(blast intro: r1.no_change_\<tau>move)

lemma no_change_\<tau>move2:
  "\<lbrakk> (x1, m1) \<approx> (x2, m2); (x2, m2) -2-\<epsilon>\<rightarrow> (x2, m2) \<rbrakk> \<Longrightarrow> \<tau>move2 (x2, m2) \<epsilon> (x2, m2)"
by(blast intro: r2.no_change_\<tau>move)

end

locale FWweak_bisimulation_lift =
  FWweak_bisimulation_lift_aux _ _ _ _ _ \<tau>move1 \<tau>move2 +
  \<tau>inv r1 r2 bisim "ta_bisim bisim" \<tau>move1 \<tau>move2
  for \<tau>move1 :: "('l,'t,'x1,'m,'w) semantics"
  and \<tau>move2 :: "('l,'t,'x2,'m,'w) semantics"
begin

lemma \<tau>inv_lift: "\<tau>inv r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2"
proof
  fix s1 s2 tl1 s1' tl2 s2'
  assume "s1 \<approx>m s2" "s1' \<approx>m s2'" "tl1 \<sim>T tl2" "r1.redT s1 tl1 s1'" "r2.redT s2 tl2 s2'"
  moreover obtain t ta1 where tl1: "tl1 = (t, ta1)" by(cases tl1)
  moreover obtain t' ta2 where tl2: "tl2 = (t', ta2)" by(cases tl2)
  moreover obtain ls1 ts1 ws1 m1 where s1: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1) auto
  moreover obtain ls2 ts2 ws2 m2 where s2: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2) auto
  moreover obtain ls1' ts1' ws1' m1' where s1': "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1') auto
  moreover obtain ls2' ts2' ws2' m2' where s2': "s2' = (ls2', (ts2', m2'), ws2')" by(cases s2') auto
  ultimately have mbisim: "(ls1, (ts1, m1), ws1) \<approx>m (ls2, (ts2, m2), ws2)"
    and mbisim': "(ls1', (ts1', m1'), ws1') \<approx>m (ls2', (ts2', m2'), ws2')"
    and mred1: "(ls1, (ts1, m1), ws1) -1-t\<triangleright>ta1\<rightarrow> (ls1', (ts1', m1'), ws1')"
    and mred2: "(ls2, (ts2, m2), ws2) -2-t\<triangleright>ta2\<rightarrow> (ls2', (ts2', m2'), ws2')"
    and tasim: "ta1 \<sim>m ta2" and tt': "t' = t" by simp_all
  from mbisim have ls: "ls1 = ls2" and ws: "ws1 = ws2"
    and tbisim: "\<And>t. tbisim (ts1 t) m1 (ts2 t) m2" by(simp_all add: mbisim_def)
  from mbisim' have ls': "ls1' = ls2'" and ws': "ws1' = ws2'"
    and tbisim': "\<And>t. tbisim (ts1' t) m1' (ts2' t) m2'" by(simp_all add: mbisim_def)
  from mred1 obtain x1 ln1 x1' ln1' where tst1: "ts1 t = \<lfloor>(x1, ln1)\<rfloor>"
    and tst1': "ts1' t = \<lfloor>(x1', ln1')\<rfloor>" by(fastsimp elim!: r1.redT.cases)
  from mred2 obtain x2 ln2 x2' ln2' where tst2: "ts2 t = \<lfloor>(x2, ln2)\<rfloor>"
    and tst2': "ts2' t = \<lfloor>(x2', ln2')\<rfloor>" by(fastsimp elim!: r2.redT.cases)
  from tbisim[of t] tst1 tst2 have bisim: "bisim (x1, m1) (x2, m2)"
    and ln: "ln1 = ln2" by(auto simp add: tbisim_def)
  from tbisim'[of t] tst1' tst2' have bisim': "bisim (x1', m1') (x2', m2')"
    and ln': "ln1' = ln2'" by(auto simp add: tbisim_def)
  show "m\<tau>move1 s1 tl1 s1' = m\<tau>move2 s2 tl2 s2'" unfolding s1 s2 s1' s2' tt' tl1 tl2
  proof(cases "(ls1, (ts1, m1), ws1) = (ls1', (ts1', m1'), ws1')")
    case True
    from mred1 have "(x1, m1) -1-ta1\<rightarrow> (x1', m1') \<and> ln1 = no_wait_locks"
    proof cases
      case redT_normal thus ?thesis using tst1 tst1' by clarsimp
    next
      case redT_acquire thus ?thesis using tst1 tst2 True
	by(auto simp add: expand_fun_eq split: split_if_asm)
    qed
    hence red1: "(x1, m1) -1-ta1\<rightarrow> (x1', m1')" and ln1: "ln1 = no_wait_locks" by auto
    from mred2 ln1 ln tst2 tst2' have red2: "(x2, m2) -2-ta2\<rightarrow> (x2', m2')"
      by(fastsimp elim: r2.redT.cases)
    show "m\<tau>move1 (ls1, (ts1, m1), ws1) (t, ta1) (ls1', (ts1', m1'), ws1') =
          m\<tau>move2 (ls2, (ts2, m2), ws2) (t, ta2) (ls2', (ts2', m2'), ws2')"
         (is "?lhs = ?rhs")
    proof
      assume ?lhs
      hence ta1: "ta1 = \<epsilon>" by(auto elim: m\<tau>move1_cases)
      with tasim have ta2: "ta2 = \<epsilon>" by(simp)
      from ta1 True tst1 tst1' bisim red1 have \<tau>1: "\<tau>move1 (x1, m1) ta1 (x1', m1')"
	by(auto intro: no_change_\<tau>move1)
      with \<tau>inv[OF bisim red1 red2 bisim' tasim] ta2 have \<tau>2: "\<tau>move2 (x2, m2) \<epsilon> (x2', m2')" by simp
      with bisim red2 ta2 have m2': "m2' = m2" by(auto intro: sym \<tau>move_heap2)
      { assume neq: "s2' \<noteq> s2"
	have "(THE t. ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t) = t"
	proof
	  from mred2 ln ln1 neq m2' ta2 show "ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t" unfolding s2 s2'
	    by(auto elim!: r2.redT.cases simp add: expand_fun_eq split: split_if_asm)
	next
	  fix t' assume "ts2 t' \<noteq> None \<and> ts2 t' \<noteq> ts2' t'"
	  with mred2 ln ln1 m2' ta2 show "t' = t"
	    by(auto elim!: r2.redT.cases split: split_if_asm)
	qed }
      thus ?rhs using tst2 tst2' ln ln1 \<tau>2 unfolding ta2 m2' s2 s2' by - (rule m\<tau>move2_intros, auto)
    next
      assume ?rhs
      with tst2 tst2' have "ta2 = \<epsilon>" and \<tau>2: "\<tau>move2 (x2, m2) \<epsilon> (x2', m2')" by(auto elim: m\<tau>move2_cases)
      with \<tau>inv[OF bisim red1 red2 bisim' tasim] tasim True tst1 tst1' ln1
      show ?lhs by(auto intro: m\<tau>move1_intros)
    qed
  next
    case False
    note neq = this
    show "m\<tau>move1 (ls1, (ts1, m1), ws1) (t, ta1) (ls1', (ts1', m1'), ws1') =
          m\<tau>move2 (ls2, (ts2, m2), ws2) (t, ta2) (ls2', (ts2', m2'), ws2')"
      (is "?lhs = ?rhs")
    proof
      assume m\<tau>: ?lhs
      hence ta1: "ta1 = \<epsilon>" and m1': "m1' = m1" by(fastsimp elim: m\<tau>move1_cases)+
      from ta1 tasim have ta2: "ta2 = \<epsilon>" by simp
      have "(THE t. ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t) = t"
      proof
	from mred1 show "ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t"
	proof cases
	  case redT_normal with tst1 tst1' False ta1 m1' show ?thesis by(auto simp add: expand_fun_eq)
	next
	  case redT_acquire with tst1 tst1' False ta1 m1' show ?thesis by clarify auto
	qed
      next
	fix t' assume "ts1 t' \<noteq> None \<and> ts1 t' \<noteq> ts1' t'"
	with mred1 tst1 tst1' False ta1 m1' show "t' = t"
	  by(auto elim!: r1.redT.cases split: split_if_asm)
      qed
      with m\<tau> tst1 tst1' m1' False have \<tau>1: "\<tau>move1 (x1, m1) \<epsilon> (x1', m1)" 
	and ln1: "ln1 = no_wait_locks" by(auto elim: m\<tau>move1_cases)
      from mred1 \<tau>1 tst1 tst1' m1' ln1 ta1 have red1: "(x1, m1) -1-\<epsilon>\<rightarrow> (x1', m1)"
	by(auto elim!: r1.redT.cases)
      from mred2 ln1 ln tst2 tst2' ta2 have red2: "(x2, m2) -2-\<epsilon>\<rightarrow> (x2', m2')"
	by(auto elim!: r2.redT.cases)
      from \<tau>1 \<tau>inv[OF bisim red1 red2] bisim' tasim m1'
      have \<tau>2: "\<tau>move2 (x2, m2) \<epsilon> (x2', m2')" by auto
      from \<tau>move_heap2[OF bisim red2 \<tau>2] have m2': "m2' = m2" ..
      show ?rhs
      proof(cases "(ls2, (ts2, m2), ws2) \<noteq> (ls2', (ts2', m2'), ws2')")
	case False with ta2 m2' tst2 tst2' ln ln1 \<tau>2
	show ?thesis by(auto intro: m\<tau>move2_intros)
      next
	case True
	have "(THE t. ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t) = t"
	proof
	  from mred2 ta2 m2' tst2 tst2' True show "ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t"
	    by(auto elim!: r2.redT.cases simp add: expand_fun_eq split: split_if_asm)
	next
	  fix t' assume "ts2 t' \<noteq> None \<and> ts2 t' \<noteq> ts2' t'"
	  with mred2 ta2 m2' tst2 tst2' ln ln1 show "t' = t"
	    by(auto elim!: r2.redT.cases split: split_if_asm)
	qed
	with ta2 m2' True tst2 tst2' ln ln1 \<tau>2 show ?thesis by(auto intro: m\<tau>move2_intros)
      qed
    next
      assume m\<tau>: ?rhs
      hence ta2: "ta2 = \<epsilon>" and m2': "m2' = m2" by(fastsimp elim: m\<tau>move2_cases)+
      from ta2 tasim have ta1: "ta1 = \<epsilon>" by simp
      show ?lhs
      proof(cases "(ls2, (ts2, m2), ws2) \<noteq> (ls2', (ts2', m2'), ws2')")
	case False
	from False tst2 tst2' have x2': "x2' = x2" by simp
	from mred2 have "(x2, m2) -2-\<epsilon>\<rightarrow> (x2, m2) \<and> ln2 = no_wait_locks"
	proof cases
	  case redT_normal thus ?thesis using x2' m2' tst2 tst2' ta2 by clarsimp
	next
	  case redT_acquire thus ?thesis using tst2 False x2' m2' ta2
	    by(fastsimp simp add: expand_fun_eq split: split_if_asm)
	qed
	hence red2: "(x2, m2) -2-\<epsilon>\<rightarrow> (x2, m2)" and ln2: "ln2 = no_wait_locks" by auto
	from red2 bisim have \<tau>2: "\<tau>move2 (x2, m2) \<epsilon> (x2, m2)" by(auto intro: no_change_\<tau>move2)
	from ln2 ln have ln1: "ln1 = no_wait_locks" by simp
	with tst1 tst1' mred1 ta1 have red1: "(x1, m1) -1-\<epsilon>\<rightarrow> (x1', m1')" by(auto elim!: r1.redT.cases)
	from \<tau>inv[OF bisim red1 red2] bisim' tasim \<tau>2 ta1 x2' m2'
	have \<tau>1: "\<tau>move1 (x1, m1) \<epsilon> (x1', m1')" by simp
	with red1 bisim have m1': "m1' = m1" by(auto intro: sym \<tau>move_heap1)
	have "(THE t. ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t) = t"
	proof
	  from mred1 show "ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t"
	  proof cases
	    case redT_normal with neq tst1 tst1' ta1 m1' show ?thesis
	      by clarsimp (auto simp add: expand_fun_eq split: split_if_asm)
	  next
	    case redT_acquire with tst1 tst1' False ta1 m1' show ?thesis by clarify auto
	  qed
	next
	  fix t' assume "ts1 t' \<noteq> None \<and> ts1 t' \<noteq> ts1' t'"
	  with mred1 tst1 tst1' neq ta1 m1' show "t' = t"
	    by(auto elim!: r1.redT.cases split: split_if_asm)
	qed
	with tst1 tst1' \<tau>1 m1' ta1 neq ln ln2 show ?thesis by(auto intro: m\<tau>move1_intros)
      next
	case True
	have "(THE t. ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t) = t"
	proof
	  from mred2 show "ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t"
	  proof cases
	    case redT_normal with tst2 tst2' True ta2 m2' show ?thesis by(auto simp add: expand_fun_eq)
	  next
	    case redT_acquire with tst2 tst2' True ta2 m2' show ?thesis by clarify auto
	  qed
	next
	  fix t' assume "ts2 t' \<noteq> None \<and> ts2 t' \<noteq> ts2' t'"
	  with mred2 tst2 tst2' True ta2 m2' show "t' = t"
	    by(auto elim!: r2.redT.cases split: split_if_asm)
	qed
	with m\<tau> tst2 tst2' m2' True have \<tau>2: "\<tau>move2 (x2, m2) \<epsilon> (x2', m2)" 
	  and ln2: "ln2 = no_wait_locks" by(auto elim: m\<tau>move2_cases)
	from mred2 \<tau>2 tst2 tst2' m2' ln2 ta2 have red2: "(x2, m2) -2-\<epsilon>\<rightarrow> (x2', m2)"
	  by(auto elim!: r2.redT.cases)
	from mred1 ln2 ln tst1 tst1' ta1 have red1: "(x1, m1) -1-\<epsilon>\<rightarrow> (x1', m1')"
	  by(auto elim!: r1.redT.cases)
	from \<tau>2 \<tau>inv[OF bisim red1 red2] bisim' tasim m2'
	have \<tau>1: "\<tau>move1 (x1, m1) \<epsilon> (x1', m1')" by auto
	from \<tau>move_heap1[OF bisim red1 \<tau>1] have m1': "m1' = m1" ..
	have "(THE t. ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t) = t"
	proof
	  from mred1 ta1 m1' tst1 tst1' False show "ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t"
	    by(auto elim!: r1.redT.cases simp add: expand_fun_eq split: split_if_asm)
	next
	  fix t' assume "ts1 t' \<noteq> None \<and> ts1 t' \<noteq> ts1' t'"
	  with mred1 ta1 m1' tst1 tst1' ln ln2 show "t' = t"
	    by(auto elim!: r1.redT.cases split: split_if_asm)
	qed
	with ta1 m1' False tst1 tst1' ln ln2 \<tau>1 show ?thesis by(auto intro: m\<tau>move1_intros)
      qed
    qed
  qed
qed

end

sublocale FWweak_bisimulation_lift < mthr!: \<tau>inv r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2
by(rule \<tau>inv_lift)

locale FWweak_bisimulation =
  FWweak_bisimulation_lift_aux _ _ _ _ _ \<tau>move1 \<tau>move2 +
  FWbisimulation_base_aux +
  weak_bisimulation r1 r2 bisim "ta_bisim bisim" \<tau>move1 \<tau>move2 
  for \<tau>move1 :: "('l,'t,'x1,'m,'w) semantics"
  and \<tau>move2 :: "('l,'t,'x2,'m,'w) semantics" +
  assumes bisim_inv_red_other:
   "\<lbrakk> (x, m1) \<approx> (xx, m2); (x1, m1) \<approx> (x2, m2); 
      (\<lambda>s1 s1'. s1 -1-\<epsilon>\<rightarrow> s1' \<and> \<tau>move1 s1 \<epsilon> s1')\<^sup>*\<^sup>* (x1, m1) (x1', m1);
      (x1', m1) -1-ta1\<rightarrow> (x1'', m1'); \<not> \<tau>move1 (x1', m1) ta1 (x1'', m1');
      (\<lambda>s2 s2'. s2 -2-\<epsilon>\<rightarrow> s2' \<and> \<tau>move2 s2 \<epsilon> s2')\<^sup>*\<^sup>* (x2, m2) (x2', m2);
      (x2', m2) -2-ta2\<rightarrow> (x2'', m2'); \<not> \<tau>move2 (x2', m2) ta2 (x2'', m2');
      (x1'', m1') \<approx> (x2'', m2'); ta_bisim bisim ta1 ta2 \<rbrakk>
   \<Longrightarrow> (x, m1') \<approx> (xx, m2')"
begin

lemma bisim_inv1:
  assumes bisim: "s1 \<approx> s2"
  and red: "s1 -1-ta1\<rightarrow> s1'"
  obtains s2' where "s1' \<approx> s2'"
proof(atomize_elim)
  show "\<exists>s2'. s1' \<approx> s2'"
  proof(cases "\<tau>move1 s1 ta1 s1'")
    case True
    from simulation_silent1[OF bisim red True]
    show ?thesis by auto
  next
    case False
    from simulation1[OF bisim red False] show ?thesis by auto
  qed
qed

lemma bisim_inv2:
  assumes bisim: "s1 \<approx> s2"
  and red: "s2 -2-ta2\<rightarrow> s2'"
  obtains s1' where "s1' \<approx> s2'"
proof(atomize_elim)
  show "\<exists>s1'. s1' \<approx> s2'"
  proof(cases "\<tau>move2 s2 ta2 s2'")
    case True
    from simulation_silent2[OF bisim red True]
    show ?thesis by auto
  next
    case False
    from simulation2[OF bisim red False] show ?thesis by auto
  qed
qed

lemma bisim_inv: "bisim_inv"
by(blast intro!: bisim_invI elim: bisim_inv1 bisim_inv2)

lemma bisim_inv_\<tau>s1:
  assumes "bisim s1 s2" and "(\<lambda>s1 s1'. s1 -1-\<epsilon>\<rightarrow> s1' \<and> \<tau>move1 s1 \<epsilon> s1')\<^sup>*\<^sup>* s1 s1'"
  obtains s2' where "bisim s1' s2'"
using assms by(rule bisim_inv_\<tau>s1_inv[OF bisim_inv])

lemma bisim_inv_\<tau>s2:
  assumes "bisim s1 s2" and "(\<lambda>s2 s2'. s2 -2-\<epsilon>\<rightarrow> s2' \<and> \<tau>move2 s2 \<epsilon> s2')\<^sup>*\<^sup>* s2 s2'"
  obtains s1' where "bisim s1' s2'"
using assms by(rule bisim_inv_\<tau>s2_inv[OF bisim_inv])

lemma wfs1_inv [simp, intro!]: "r1.wfs_inv"
by(rule r1.wfs_invI)(auto elim: bisim_inv1)

lemma wfs2_inv [simp, intro!]: "r2.wfs_inv"
by(rule r2.wfs_invI)(auto elim: bisim_inv2)

lemma red1_rtrancl_\<tau>_into_RedT_\<tau>:
  assumes "(\<lambda>s1 s1'. s1 -1-\<epsilon>\<rightarrow> s1' \<and> \<tau>move1 s1 \<epsilon> s1')\<^sup>*\<^sup>* (x1, shr s1) (x1', m1')" "bisim (x1, shr s1) (x2, m2)"
  and "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" "wset s1 t = None"
  shows "\<tau>mRed1 s1 (r1.redT_upd s1 t \<epsilon> x1' m1')"
using assms by(blast intro: r1.red_rtrancl_\<tau>_into_RedT_\<tau>_inv[OF wfs1_inv])

lemma red2_rtrancl_\<tau>_into_RedT_\<tau>:
  assumes "(\<lambda>s2 s2'. s2 -2-\<epsilon>\<rightarrow> s2' \<and> \<tau>move2 s2 \<epsilon> s2')\<^sup>*\<^sup>* (x2, shr s2) (x2', m2')"
  and "bisim (x1, m1) (x2, shr s2)" "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>" "wset s2 t = None"
  shows "\<tau>mRed2 s2 (r2.redT_upd s2 t \<epsilon> x2' m2')"
using assms by(blast intro: r2.red_rtrancl_\<tau>_into_RedT_\<tau>_inv[OF wfs2_inv])

lemma red1_rtrancl_\<tau>_heapD:
  "\<lbrakk> (\<lambda>s1 s1'. s1 -1-\<epsilon>\<rightarrow> s1' \<and> \<tau>move1 s1 \<epsilon> s1')\<^sup>*\<^sup>* s1 s1'; bisim s1 s2 \<rbrakk> \<Longrightarrow> snd s1' = snd s1"
by(blast intro: r1.red_rtrancl_\<tau>_heapD_inv[OF wfs1_inv])

lemma red2_rtrancl_\<tau>_heapD:
  "\<lbrakk> (\<lambda>s2 s2'. s2 -2-\<epsilon>\<rightarrow> s2' \<and> \<tau>move2 s2 \<epsilon> s2')\<^sup>*\<^sup>* s2 s2'; bisim s1 s2 \<rbrakk> \<Longrightarrow> snd s2' = snd s2"
by(blast intro: r2.red_rtrancl_\<tau>_heapD_inv[OF wfs2_inv])

lemma mbisim_weak_bisimulation:
  "weak_bisimulation r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2"
proof
  fix s1 s2 tl1 s1'
  assume m\<tau>: "m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'" and mbisim: "mbisim s1 s2"
  obtain ls1 ts1 m1 ws1 where [simp]: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1, auto)
  obtain ls1' ts1' m1' ws1' where [simp]: "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1', auto)
  obtain ls2 ts2 m2 ws2 where [simp]: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2, auto)
  from m\<tau> obtain t where m\<tau>: "m\<tau>move1 s1 (t, \<epsilon>) s1'" and redT1: "s1 -1-t\<triangleright>\<epsilon>\<rightarrow> s1'" by(auto elim: m\<tau>move1_cases)
  from m\<tau> have [simp]: "m1' = m1" by(auto elim: m\<tau>move1_cases)
  from mbisim have [simp]: "ls2 = ls1" "ws2 = ws1" by(auto simp add: mbisim_def)
  show "\<exists>s2'. r2.mthr.\<tau>moves s2 s2' \<and> mbisim s1' s2'"
  proof(cases "s1 = s1'")
    case True with `mbisim s1 s2` show ?thesis by blast
  next
    case False
    from redT1 show ?thesis
    proof cases
      case (redT_normal x1 S TA x1' M' T S')
      hence [simp]: "S = s1" "T = t" "TA = \<epsilon>" "S' = s1'"
	and red: "(x1, m1) -1-\<epsilon>\<rightarrow> (x1', M')"
	and tst: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
	and wst: "wset s1 t = None"
	and s1': "s1' = r1.redT_upd s1 t \<epsilon> x1' M'" by auto
      from s1' tst have [simp]: "ls1' = ls1" "ws1' = ws1" "M' = m1'" "ts1' = ts1(t \<mapsto> (x1', no_wait_locks))"
	by(auto simp add: redT_updLs_def redT_updLns_def o_def)
      have "(THE t. ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t) = t"
      proof
	from False tst show "ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t"
	  by(auto simp add: expand_fun_eq split: split_if_asm)
      next
	fix t'
	assume "ts1 t' \<noteq> None \<and> ts1 t' \<noteq> ts1' t'"
	with False tst show "t' = t" by(auto simp add: expand_fun_eq split: split_if_asm)
      qed
      with False m\<tau> tst have \<tau>: "\<tau>move1 (x1, m1) \<epsilon> (x1', m1)" by(auto elim: m\<tau>move1_cases)
      from mbisim tst obtain x2 where tst': "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
	and bisim: "bisim (x1, m1) (x2, m2)" by(auto dest: mbisim_thrD1)
      from simulation_silent1[OF bisim red] \<tau>
      obtain x2' m2' where red: "r2.\<tau>moves (x2, m2) (x2', m2')"
	and bisim': "bisim (x1', m1) (x2', m2')" by auto
      from red bisim have [simp]: "m2' = m2" unfolding r2.\<tau>moves_def
	by(auto dest: red2_rtrancl_\<tau>_heapD)
      from red tst' wst bisim have "\<tau>mRed2 s2 (r2.redT_upd s2 t \<epsilon> x2' m2')"
	unfolding r2.\<tau>moves_def by -(rule red2_rtrancl_\<tau>_into_RedT_\<tau>, auto)
      moreover have "mbisim s1' (r2.redT_upd s2 t \<epsilon> x2' m2')"
      proof(rule mbisimI)
	show "locks s1' = locks (r2.redT_upd s2 t \<epsilon> x2' m2')" by(auto simp add: redT_updLs_def o_def)
      next
	show "wset s1' = wset (r2.redT_upd s2 t \<epsilon> x2' m2')" by auto
      next
	fix t'
	assume "thr s1' t' = None"
	hence "ts1 t' = None" by(auto split: split_if_asm)
	with mbisim_thrNone_eq[OF mbisim] have "ts2 t' = None" by simp
	with tst' show "thr (r2.redT_upd s2 t \<epsilon> x2' m2') t' = None" by auto
      next
	fix t' X1 LN
	assume ts't': "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
	show "\<exists>x2. thr (r2.redT_upd s2 t \<epsilon> x2' m2') t' = \<lfloor>(x2, LN)\<rfloor> \<and> bisim (X1, shr s1') (x2, shr (r2.redT_upd s2 t \<epsilon> x2' m2'))"
	proof(cases "t' = t")
	  case True
	  note this[simp]
	  with s1' tst ts't' have [simp]: "X1 = x1'" "LN = no_wait_locks"
	    by(simp_all)(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	  with bisim' tst' show ?thesis by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	next
	  case False
	  with ts't' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
	  with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "bisim (X1, m1) (X2, m2)"
	    by(auto dest: mbisim_thrD1)
	  with False show ?thesis by auto
	qed
      qed
      ultimately show ?thesis unfolding \<tau>mred2_def_raw r2.mthr.\<tau>moves_def by(auto)
    next
      case (redT_acquire S T x1 ln n S')
      hence [simp]: "S = s1" "T = t" "S' = s1'"
	and tst: "ts1 t = \<lfloor>(x1, ln)\<rfloor>" and wst: "ws1 t = None"
	and maa: "may_acquire_all ls1 t ln" and ln: "0 < ln\<^sub>f n"
	and s1': "s1' = (acquire_all ls1 t ln, (ts1(t \<mapsto> (x1, no_wait_locks)), m1), ws1)"
	by -(cases S, auto)+
      from s1' have [simp]: "ls1' = acquire_all ls1 t ln" 
	"ts1' = ts1(t \<mapsto> (x1, no_wait_locks))" "ws1' = ws1" by auto
      from ln tst have "s1' \<noteq> s1" by(auto simp add: expand_fun_eq)
      have "(THE t. thr s1 t \<noteq> None \<and> thr s1 t \<noteq> thr s1' t) = t"
      proof
	from tst ln show "thr s1 t \<noteq> None \<and> thr s1 t \<noteq> thr s1' t" by auto
      next
	fix t' assume "thr s1 t' \<noteq> None \<and> thr s1 t' \<noteq> thr s1' t'"
	thus "t' = t" using tst ln by(auto split: split_if_asm)
      qed
      with `s1' \<noteq> s1` tst m\<tau> have "ln = no_wait_locks" by(auto elim: m\<tau>move1_cases)
      with ln show ?thesis by simp
    qed
  qed
next
  fix s1 s2 tl2 s2'
  assume m\<tau>: "m\<tau>move2 s2 tl2 s2'" "r2.redT s2 tl2 s2'" and mbisim: "mbisim s1 s2"
  obtain ls1 ts1 m1 ws1 where [simp]: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1, auto)
  obtain ls2 ts2 m2 ws2 where [simp]: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2, auto)
  obtain ls2' ts2' m2' ws2' where [simp]: "s2' = (ls2', (ts2', m2'), ws2')" by(cases s2', auto)
  from m\<tau> obtain t where m\<tau>: "m\<tau>move2 s2 (t, \<epsilon>) s2'" and redT2: "s2 -2-t\<triangleright>\<epsilon>\<rightarrow> s2'" by(auto elim: m\<tau>move2_cases)
  from m\<tau> have [simp]: "m2' = m2" by(auto elim: m\<tau>move2_cases)
  from mbisim have [simp]: "ls1 = ls2" "ws1 = ws2" by(auto simp add: mbisim_def)
  show "\<exists>s1'. r1.mthr.\<tau>moves s1 s1' \<and> mbisim s1' s2'"
  proof(cases "s2 = s2'")
    case True with `mbisim s1 s2` show ?thesis by blast
  next
    case False from redT2 show ?thesis
    proof cases
      case (redT_normal x2 S TA x2' M' T S')
      hence [simp]: "S = s2" "T = t" "TA = \<epsilon>" "S' = s2'"
	and red: "(x2, m2) -2-\<epsilon>\<rightarrow> (x2', M')" and tst: "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
	and wst: "wset s2 t = None" and s2': "s2' = r2.redT_upd s2 t \<epsilon> x2' M'" by auto
      from s2' tst have [simp]: "ls2' = ls2" "ws2' = ws2" "M' = m2'" "ts2' = ts2(t \<mapsto> (x2', no_wait_locks))"
	by(auto simp add: redT_updLs_def redT_updLns_def o_def)
      have "(THE t. ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t) = t"
      proof
	from False tst show "ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t"
	  by(auto simp add: expand_fun_eq split: split_if_asm)
      next
	fix t' assume "ts2 t' \<noteq> None \<and> ts2 t' \<noteq> ts2' t'"
	with False tst show "t' = t" by(auto simp add: expand_fun_eq split: split_if_asm)
      qed
      with False m\<tau> tst have \<tau>: "\<tau>move2 (x2, m2) \<epsilon> (x2', m2)" by(auto elim: m\<tau>move2_cases)
      from mbisim tst obtain x1 where tst': "ts1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
	and bisim: "bisim (x1, m1) (x2, m2)" by(auto dest: mbisim_thrD2)
      from simulation_silent2[OF bisim red] \<tau> obtain x1' m1'
	where red: "r1.\<tau>moves (x1, m1) (x1', m1')"
	and bisim': "bisim (x1', m1') (x2', m2)" by auto
      from red bisim have [simp]: "m1' = m1" unfolding r1.\<tau>moves_def by(auto dest: red1_rtrancl_\<tau>_heapD)
      from red tst' wst bisim have "\<tau>mRed1 s1 (r1.redT_upd s1 t \<epsilon> x1' m1')"
	unfolding r1.\<tau>moves_def by -(rule red1_rtrancl_\<tau>_into_RedT_\<tau>, auto)
      moreover have "mbisim (r1.redT_upd s1 t \<epsilon> x1' m1') s2'"
      proof(rule mbisimI2)
	show "locks (r1.redT_upd s1 t \<epsilon> x1' m1') = locks s2'" by(auto simp add: redT_updLs_def o_def)
      next
	show "wset (r1.redT_upd s1 t \<epsilon> x1' m1') = wset s2'" by auto
      next
	fix t' assume "thr s2' t' = None"
	hence "ts2 t' = None" by(auto split: split_if_asm)
	with mbisim_thrNone_eq[OF mbisim] have "ts1 t' = None" by simp
	with tst' show "thr (r1.redT_upd s1 t \<epsilon> x1' m1') t' = None" by auto
      next
	fix t' X2 LN
	assume ts't': "thr s2' t' = \<lfloor>(X2, LN)\<rfloor>"
	show "\<exists>x1. thr (r1.redT_upd s1 t \<epsilon> x1' m1') t' = \<lfloor>(x1, LN)\<rfloor> \<and> bisim (x1, shr (r1.redT_upd s1 t \<epsilon> x1' m1')) (X2, shr s2')"
	proof(cases "t' = t")
	  case True
	  with s2' tst ts't' have [simp]: "X2 = x2'" "LN = no_wait_locks"
	    by(simp_all)(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	  with bisim' tst' True show ?thesis by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
	next
	  case False
	  with ts't' have "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" by auto
	  with mbisim obtain X1 where "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" "bisim (X1, m1) (X2, m2)"
	    by(auto dest: mbisim_thrD2)
	  with False show ?thesis by auto
	qed
      qed
      ultimately show ?thesis unfolding \<tau>mred1_def_raw r1.mthr.\<tau>moves_def by auto
    next
      case (redT_acquire S T x2 ln n S')
      hence [simp]: "S = s2" "T = t" "S' = s2'"
	and tst: "ts2 t = \<lfloor>(x2, ln)\<rfloor>" and wst: "ws2 t = None"
	and maa: "may_acquire_all ls2 t ln" and ln: "0 < ln\<^sub>f n"
	and s2': "s2' = (acquire_all ls2 t ln, (ts2(t \<mapsto> (x2, no_wait_locks)), m2), ws2)"
	by -(cases S, auto)+
      from s2' have [simp]: "ls2' = acquire_all ls1 t ln" 
	"ts2' = ts2(t \<mapsto> (x2, no_wait_locks))" "ws2' = ws2" by auto
      from ln tst have "s2' \<noteq> s2" by(auto simp add: expand_fun_eq)
      have "(THE t. thr s2 t \<noteq> None \<and> thr s2 t \<noteq> thr s2' t) = t"
      proof
	from tst ln show "thr s2 t \<noteq> None \<and> thr s2 t \<noteq> thr s2' t" by auto
      next
	fix t' assume "thr s2 t' \<noteq> None \<and> thr s2 t' \<noteq> thr s2' t'"
	thus "t' = t" using tst ln by(auto split: split_if_asm)
      qed
      with `s2' \<noteq> s2` tst m\<tau> have "ln = no_wait_locks" by(auto elim: m\<tau>move2_cases)
      with ln show ?thesis by simp
    qed
  qed
next
  fix s1 s2 tl1 s1'
  assume mbisim: "mbisim s1 s2" and "\<not> m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'"
  then obtain t ta1 where tl1 [simp]: "tl1 = (t, ta1)" and redT: "s1 -1-t\<triangleright>ta1\<rightarrow> s1'"
    and m\<tau>: "\<not> m\<tau>move1 s1 (t, ta1) s1'" by(cases tl1) fastsimp
  obtain ls1 ts1 m1 ws1 where [simp]: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1, auto)
  obtain ls1' ts1' m1' ws1' where [simp]: "s1' = (ls1', (ts1', m1'), ws1')" by(cases s1', auto)
  obtain ls2 ts2 m2 ws2 where [simp]: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2, auto)
  from mbisim have [simp]: "ls2 = ls1" "ws2 = ws1" by(auto simp add: mbisim_def)
  from redT show "\<exists>s2' s2'' tl2. r2.mthr.\<tau>moves s2 s2' \<and> r2.redT s2' tl2 s2'' \<and>
    \<not> m\<tau>move2 s2' tl2 s2'' \<and> mbisim s1' s2'' \<and> mta_bisim tl1 tl2"
  proof cases
    case (redT_normal x1 S TA x1' M' T S')
    hence [simp]: "S = s1" "T = t" "TA = ta1" "S' = s1'" "M' = m1'"
      and red: "(x1, m1) -1-ta1\<rightarrow> (x1', m1')" and tst: "ts1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and wst: "ws1 t = None" and aoe: "r1.actions_ok s1 t ta1"
      and s1': "s1' = r1.redT_upd s1 t ta1 x1' m1'" by auto
    from mbisim tst obtain x2 where tst': "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and bisim: "bisim (x1, m1) (x2, m2)" by(auto dest: mbisim_thrD1)
    from m\<tau> have \<tau>: "\<not> \<tau>move1 (x1, m1) ta1 (x1', m1')"
    proof(rule contrapos_nn)
      assume \<tau>: "\<tau>move1 (x1, m1) ta1 (x1', m1')"
      moreover hence [simp]: "ta1 = \<epsilon>" by(rule silent_tl1)
      moreover have [simp]: "m1' = m1" by(rule \<tau>move_heap1[OF bisim red \<tau>, symmetric])
      moreover {	assume sneq: "s1' \<noteq> s1"
	with tst s1' have tstneq: "ts1' t \<noteq> ts1 t"
	  by(auto simp add: redT_updLs_def redT_updLns_def expand_fun_eq o_def split: split_if_asm)
	with tst have "ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t" by(auto)
	hence "(THE t. ts1 t \<noteq> None \<and> ts1 t \<noteq> ts1' t) = t"
	proof(rule the_equality)    
          fix t' assume "ts1 t' \<noteq> None \<and> ts1 t' \<noteq> ts1' t'"
	  with tst tstneq s1' show "t' = t" by(auto split: split_if_asm)
	qed }
      ultimately show "m\<tau>move1 s1 (t, ta1) s1'" using s1' tst
	by(clarsimp simp add: redT_updLs_def o_def)(rule m\<tau>move1_intros, auto)
    qed
    from simulation1[OF bisim red this] obtain x2' M2' x2'' M2'' ta2
      where red21: "r2.\<tau>moves (x2, m2) (x2', M2')"
      and red22: "(x2', M2') -2-ta2\<rightarrow> (x2'', M2'')" and \<tau>2: "\<not> \<tau>move2 (x2', M2') ta2 (x2'', M2'')"
      and bisim': "bisim (x1', m1') (x2'', M2'')"
      and tasim: "ta_bisim bisim ta1 ta2" by auto
    let ?s2' = "r2.redT_upd s2 t \<epsilon> x2' M2'"
    let ?s2'' = "r2.redT_upd ?s2' t ta2 x2'' M2''"
    from red21 tst' wst bisim have "\<tau>mRed2 s2 ?s2'" unfolding r2.\<tau>moves_def by -(rule red2_rtrancl_\<tau>_into_RedT_\<tau>, auto)
    also from red21 bisim have [simp]: "M2' = m2" unfolding r2.\<tau>moves_def by(auto dest: red2_rtrancl_\<tau>_heapD)
    from tasim have [simp]: "\<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub>"
      and nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>" by(auto simp add: ta_bisim_def)
    from mbisim have tbisim: "\<And>t. tbisim (ts1 t) m1 (ts2 t) m2" by(simp add: mbisim_def)
    hence tbisim': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ts1 t') m1 (thr ?s2' t') m2" by(auto)
    
    from tst' have tst'': "thr ?s2' t = \<lfloor>(x2', no_wait_locks)\<rfloor>" by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
    with tst have "thr s1 t = None \<longleftrightarrow> thr ?s2' t = None" by simp
    with tbisim' tasim tst aoe have aoe': "r2.actions_ok ?s2' t ta2"
      by -(drule (1) tbisim_actions_ok_inv[THEN iffD1],(fastsimp simp del: fun_upd_apply)+)
    with red22 wst tst'' have "?s2' -2-t\<triangleright>ta2\<rightarrow> ?s2''"
      by -(rule r2.redT.redT_normal,auto simp add: redT_updLns_def expand_finfun_eq)
    moreover from \<tau>2 have "\<not> m\<tau>move2 ?s2' (t, ta2) ?s2''"
    proof(rule contrapos_nn)
      assume m\<tau>: "m\<tau>move2 ?s2' (t, ta2) ?s2''"
      hence [simp]: "ta2 = \<epsilon>" "M2'' = M2'" by(auto elim: m\<tau>move2_cases)
      show "\<tau>move2 (x2', M2') ta2 (x2'', M2'')"
      proof (cases "?s2' = ?s2''")
	case True
	hence "M2'' = M2'" "x2'' = x2'" by(auto simp add: redT_updLns_def expand_fun_eq split: split_if_asm)
	with red22 bisim' show ?thesis by(auto intro: no_change_\<tau>move2)
      next
	case False
	have "(THE t. thr ?s2' t \<noteq> None \<and> thr ?s2' t \<noteq> thr ?s2'' t) = t"
	proof
	  from False tst' show "thr ?s2' t \<noteq> None \<and> thr ?s2' t \<noteq> thr ?s2'' t"
	    by(auto simp add: expand_fun_eq split: split_if_asm)
	next
	  fix t' assume "thr ?s2' t' \<noteq> None \<and> thr ?s2' t' \<noteq> thr ?s2'' t'"
	  with False tst' show "t' = t" by(auto simp add: expand_fun_eq split: split_if_asm)
	qed
	with False m\<tau> show "\<tau>move2 (x2', M2') ta2 (x2'', M2'')"
	  by(auto simp add: redT_updLns_def elim: m\<tau>move2_cases)
      qed
    qed
    moreover have "mbisim s1' ?s2''"
    proof(rule mbisimI)
      from s1' show "locks s1' = locks ?s2''" by(auto simp add: redT_updLs_def o_def)
    next
      from s1' show "wset s1' = wset ?s2''" by auto
    next
      fix T assume tsT: "thr s1' T = None"
      moreover from mbisim_thrNone_eq[OF mbisim, of T]
      have "(thr s1 T = None) = (thr ?s2' T = None)" using tst tst' by(auto)
      with tbisim'[of T] tst tst'' have "(thr s1 T = None) = (thr ?s2' T = None)" by(auto simp add: tbisim_def)
      hence "(redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> T = None) = (redT_updTs (thr ?s2') \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> T = None)"
	by(rule redT_updTs_nta_bisim_inv[OF nta])
      ultimately show "thr ?s2'' T = None" using s1' by(auto simp add: redT_updLns_def)
    next
      fix T X1 LN
      assume tsT: "thr s1' T = \<lfloor>(X1, LN)\<rfloor>"
      show "\<exists>x2. thr ?s2'' T = \<lfloor>(x2, LN)\<rfloor> \<and> bisim (X1, shr s1') (x2, shr ?s2'')"
      proof(cases "thr s1 T")
	case None
	with tst have "T \<noteq> t" by auto
	from mbisim_thrNone_eq[OF mbisim] None have "thr s2 T = None" by(simp)
	with tst' have tsT': "thr ?s2' T = None" by(auto)
	from None `T \<noteq> t` tsT aoe s1' obtain M1
	  where ntset: "NewThread T X1 M1 \<in> set \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>" and [simp]: "LN = no_wait_locks"
	  by(auto dest!: redT_updTs_new_thread)
	from ntset obtain tas1 tas1' where "\<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = tas1 @ NewThread T X1 M1 # tas1'"
	  by(auto simp add: in_set_conv_decomp)
	with nta	obtain tas2 X2 M2 tas2' where "\<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> = tas2 @ NewThread T X2 M2 # tas2'"
	  "length tas2 = length tas2" "length tas1' = length tas2'" and Bisim: "bisim (X1, M1) (X2, M2)"
	  by(auto simp add: list_all2_append1 list_all2_Cons1, blast intro: sym)
	hence ntset': "NewThread T X2 M2 \<in> set \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" by auto
	with tsT' `T \<noteq> t` aoe' have "thr ?s2'' T = \<lfloor>(X2, no_wait_locks)\<rfloor>"
	  by(auto intro: redT_updTs_new_thread_ts)
	moreover from ntset' red22 have "M2'' = M2" by(auto dest: r2.new_thread_memory)
	moreover from ntset red have "M1 = m1'" by(auto dest: r1.new_thread_memory)
	ultimately show ?thesis using Bisim `T \<noteq> t` by auto
      next
	case (Some a)
	show ?thesis
	proof(cases "t = T")
	  case True
	  with s1' tst tsT have "X1 = x1'" "LN = redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>" by(auto)
	  with True bisim' tst'' show ?thesis by(auto simp add: redT_updLns_def expand_finfun_eq)
	next
	  case False
	  with s1' Some aoe tsT have "thr s1 T = \<lfloor>(X1, LN)\<rfloor>" by(auto dest: redT_updTs_Some)
	  with tbisim'[of T] False obtain X2 
	    where tsT': "thr ?s2' T = \<lfloor>(X2, LN)\<rfloor>" and Bisim: "bisim (X1, m1) (X2, m2)" by(auto simp add: tbisim_def)
	  with aoe' False have "thr ?s2'' T = \<lfloor>(X2, LN)\<rfloor>" by(simp add: redT_updTs_Some)
	  moreover from bisim_inv_red_other[OF Bisim bisim _ red \<tau> _ _ _ bisim' tasim] red21 red22 \<tau>2
	  have "bisim (X1, m1') (X2, M2'')" unfolding r2.\<tau>moves_def by auto
	  ultimately show ?thesis using False by(auto)
	qed
      qed
    qed
    ultimately show ?thesis using tasim unfolding \<tau>mred2_def_raw m\<tau>red2_conv tl1 r2.mthr.\<tau>moves_def by(fastsimp)
  next
    case (redT_acquire S T x1 ln n S')
    hence [simp]: "S = s1" "T = t" "ta1 = \<epsilon>" "S' = s1'"
      and tst: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" and wst: "wset s1 t = None"
      and maa: "may_acquire_all (locks s1) t ln" and ln: "0 < ln\<^sub>f n"
      and s1': "s1' = (acquire_all ls1 t ln, (ts1(t \<mapsto> (x1, no_wait_locks)), m1), ws1)" by auto
    from tst mbisim obtain x2 where tst': "ts2 t = \<lfloor>(x2, ln)\<rfloor>" 
      and bisim: "bisim (x1, m1) (x2, m2)" by(auto dest: mbisim_thrD1)
    let ?s2' = "(acquire_all ls1 t ln, (ts2(t \<mapsto> (x2, no_wait_locks)), m2), ws1)"
    from tst' wst maa ln have "s2 -2-t\<triangleright>\<epsilon>\<rightarrow> ?s2'"
      by-(rule r2.redT.redT_acquire, auto)
    moreover from tst' ln have "\<not> m\<tau>move2 s2 (t, \<epsilon>) ?s2'"
      by(auto simp add: acquire_all_def expand_fun_eq elim!: m\<tau>move2_cases)
    moreover have "mbisim s1' ?s2'"
    proof(rule mbisimI)
      from s1' show "locks s1' = locks ?s2'" by auto
    next
      from s1' show "wset s1' = wset ?s2'" by auto
    next
      fix t' assume "thr s1' t' = None"
      with s1' have "thr s1 t' = None" by(auto split: split_if_asm)
      with mbisim_thrNone_eq[OF mbisim] have "ts2 t' = None" by simp
      with tst' show "thr ?s2' t' = None" by auto
    next
      fix t' X1 LN
      assume ts't: "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
      show "\<exists>x2. thr ?s2' t' = \<lfloor>(x2, LN)\<rfloor> \<and> bisim (X1, shr s1') (x2, shr ?s2')"
      proof(cases "t' = t")
	case True
	with s1' tst ts't have [simp]: "X1 = x1" "LN = no_wait_locks" by simp_all
	with bisim tst True s1' show ?thesis by(auto)
      next
	case False
	with ts't s1' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
	with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "bisim (X1, m1) (X2, m2)"
	  by(auto dest: mbisim_thrD1)
	with False s1' show ?thesis by auto
      qed
    qed
    ultimately show ?thesis by fastsimp
  qed
next
  fix s1 s2 tl2 s2'
  assume mbisim: "mbisim s1 s2" and "r2.redT s2 tl2 s2'" "\<not> m\<tau>move2 s2 tl2 s2'"
  then obtain t ta2 where tl2 [simp]: "tl2 = (t, ta2)" and redT: "s2 -2-t\<triangleright>ta2\<rightarrow> s2'"
    and m\<tau>: "\<not> m\<tau>move2 s2 (t, ta2) s2'" by(cases tl2) fastsimp
  obtain ls1 ts1 m1 ws1 where [simp]: "s1 = (ls1, (ts1, m1), ws1)" by(cases s1, auto)
  obtain ls2 ts2 m2 ws2 where [simp]: "s2 = (ls2, (ts2, m2), ws2)" by(cases s2, auto)
  obtain ls2' ts2' m2' ws2' where [simp]: "s2' = (ls2', (ts2', m2'), ws2')" by(cases s2', auto)
  from mbisim have [simp]: "ls1 = ls2" "ws1 = ws2" by(auto simp add: mbisim_def)
  from redT show "\<exists>s1' s1'' tl1. r1.mthr.\<tau>moves s1 s1' \<and> r1.redT s1' tl1 s1'' \<and>
    \<not> m\<tau>move1 s1' tl1 s1'' \<and> mbisim s1'' s2' \<and> mta_bisim tl1 tl2"
  proof cases
    case (redT_normal x2 S TA x2' M' T S')
    hence [simp]: "S = s2" "T = t" "TA = ta2" "S' = s2'" "M' = m2'"
      and red: "(x2, m2) -2-ta2\<rightarrow> (x2', m2')" and tst: "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and wst: "ws2 t = None" and aoe: "r2.actions_ok s2 t ta2"
      and s2': "s2' = r2.redT_upd s2 t ta2 x2' m2'" by auto
    from mbisim tst obtain x1 where tst': "ts1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and bisim: "bisim (x1, m1) (x2, m2)" by(auto dest: mbisim_thrD2)
    from m\<tau> have \<tau>: "\<not> \<tau>move2 (x2, m2) ta2 (x2', m2')"
    proof(rule contrapos_nn)
      assume \<tau>: "\<tau>move2 (x2, m2) ta2 (x2', m2')"
      moreover hence [simp]: "ta2 = \<epsilon>" by(rule silent_tl2)
      moreover have [simp]: "m2' = m2" by(rule \<tau>move_heap2[OF bisim red \<tau>, symmetric])
      moreover { assume sneq: "s2' \<noteq> s2"
	with tst s2' have tstneq: "ts2' t \<noteq> ts2 t"
	  by(auto simp add: redT_updLs_def redT_updLns_def expand_fun_eq o_def split: split_if_asm)
	have "(THE t. ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t) = t"
	proof
	  from tst tstneq show "ts2 t \<noteq> None \<and> ts2 t \<noteq> ts2' t" by(auto)
	next
          fix t' assume "ts2 t' \<noteq> None \<and> ts2 t' \<noteq> ts2' t'"
	  with tst tstneq s2' show "t' = t" by(auto split: split_if_asm)
	qed }
      ultimately show "m\<tau>move2 s2 (t, ta2) s2'" using s2' tst
	by(clarsimp simp add: redT_updLs_def o_def)(rule m\<tau>move2_intros, auto)
    qed
    from simulation2[OF bisim red this] obtain x1' M1' x1'' M1'' ta1
      where red11: "r1.\<tau>moves (x1, m1) (x1', M1')"
      and red12: "(x1', M1') -1-ta1\<rightarrow> (x1'', M1'')" and \<tau>1: "\<not> \<tau>move1 (x1', M1') ta1 (x1'', M1'')"
      and bisim': "bisim (x1'', M1'') (x2', m2')"
      and tasim: "ta_bisim bisim ta1 ta2" by auto
    let ?s1' = "r1.redT_upd s1 t \<epsilon> x1' M1'"
    let ?s1'' = "r1.redT_upd ?s1' t ta1 x1'' M1''"
    from red11 tst' wst bisim have "\<tau>mRed1 s1 ?s1'" unfolding r1.\<tau>moves_def by -(rule red1_rtrancl_\<tau>_into_RedT_\<tau>, auto)
    also from red11 bisim have [simp]: "M1' = m1" unfolding r1.\<tau>moves_def by(auto dest: red1_rtrancl_\<tau>_heapD)
    from tasim have [simp]: "\<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub>"
      and nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>" by(auto simp add: ta_bisim_def)
    from mbisim have tbisim: "\<And>t. tbisim (ts1 t) m1 (ts2 t) m2" by(simp add: mbisim_def)
    hence tbisim': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (thr ?s1' t') m1 (ts2 t') m2" by(auto)
    
    from tst' have tst'': "thr ?s1' t = \<lfloor>(x1', no_wait_locks)\<rfloor>" by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
    with tst have "thr ?s1' t = None \<longleftrightarrow> thr s2 t = None" by simp
    with tbisim' tasim aoe have aoe': "r1.actions_ok ?s1' t ta1"
      by -(drule (1) tbisim_actions_ok_inv[THEN iffD2],(fastsimp simp del: fun_upd_apply)+)
    
    with red12 wst tst'' have "?s1' -1-t\<triangleright>ta1\<rightarrow> ?s1''"
      by -(rule r1.redT.redT_normal,auto simp add: redT_updLns_def expand_finfun_eq)
    moreover from \<tau>1 have "\<not> m\<tau>move1 ?s1' (t, ta1) ?s1''"
    proof(rule contrapos_nn)
      assume m\<tau>: "m\<tau>move1 ?s1' (t, ta1) ?s1''"
      hence [simp]: "ta1 = \<epsilon>" "M1'' = M1'" by(fastsimp elim: m\<tau>move1_cases)+
      show "\<tau>move1 (x1', M1') ta1 (x1'', M1'')"
      proof (cases "?s1' = ?s1''")
	case True
	hence "M1'' = M1'" "x1'' = x1'" by(auto simp add: redT_updLns_def expand_fun_eq split: split_if_asm)
	with red12 bisim' show ?thesis by(auto intro: no_change_\<tau>move1)
      next
	case False
	have "(THE t. thr ?s1' t \<noteq> None \<and> thr ?s1' t \<noteq> thr ?s1'' t) = t"
	proof
	  from False tst' show "thr ?s1' t \<noteq> None \<and> thr ?s1' t \<noteq> thr ?s1'' t"
	    by(auto simp add: expand_fun_eq split: split_if_asm)
	next
	  fix t' assume "thr ?s1' t' \<noteq> None \<and> thr ?s1' t' \<noteq> thr ?s1'' t'"
	  with False tst' show "t' = t" by(auto simp add: expand_fun_eq split: split_if_asm)
	qed
	with False m\<tau> show "\<tau>move1 (x1', M1') ta1 (x1'', M1'')"
	  by(auto simp add: redT_updLns_def elim: m\<tau>move1_cases)
      qed
    qed
    moreover have "mbisim ?s1'' s2'"
    proof(rule mbisimI2)
      from s2' show "locks ?s1'' = locks s2'" by(auto simp add: redT_updLs_def o_def)
    next
      from s2' show "wset ?s1'' = wset s2'" by auto
    next
      fix T
      assume tsT: "thr s2' T = None"
      moreover from mbisim_thrNone_eq[OF mbisim, of T]
      have "(thr ?s1' T = None) = (thr s2 T = None)" using tst tst' by(auto)
      with tbisim'[of T] tst tst'' have "(thr ?s1' T = None) = (thr s2 T = None)"
	by(auto simp add: tbisim_def split: split_if_asm)
      hence "(redT_updTs (thr ?s1') \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> T = None) = (redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> T = None)"
	by(rule redT_updTs_nta_bisim_inv[OF nta])
      ultimately show "thr ?s1'' T = None" using s2' by(auto simp add: redT_updLns_def)
    next
      fix T X2 LN
      assume tsT: "thr s2' T = \<lfloor>(X2, LN)\<rfloor>"
      show "\<exists>x1. thr ?s1'' T = \<lfloor>(x1, LN)\<rfloor> \<and> bisim (x1, shr ?s1'') (X2, shr s2')"
      proof(cases "thr s2 T")
	case None
	with tst have "T \<noteq> t" by auto
	from mbisim_thrNone_eq[OF mbisim] None have "thr s1 T = None" by(simp)
	with tst' have tsT': "thr ?s1' T = None" by(auto)
	from None `T \<noteq> t` tsT aoe s2' obtain M2
	  where ntset: "NewThread T X2 M2 \<in> set \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" and [simp]: "LN = no_wait_locks"
	  by(auto dest!: redT_updTs_new_thread)
	from ntset obtain tas2 tas2' where "\<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> = tas2 @ NewThread T X2 M2 # tas2'"
	  by(auto simp add: in_set_conv_decomp)
	with nta	obtain tas1 X1 M1 tas1' where "\<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = tas1 @ NewThread T X1 M1 # tas1'"
	  "length tas1 = length tas2" "length tas1' = length tas2'" and Bisim: "bisim (X1, M1) (X2, M2)"
	  by(auto simp add: list_all2_append2 list_all2_Cons2, blast)
	hence ntset': "NewThread T X1 M1 \<in> set \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>" by auto
	with tsT' `T \<noteq> t` aoe' have "thr ?s1'' T = \<lfloor>(X1, no_wait_locks)\<rfloor>"
	  by(auto intro: redT_updTs_new_thread_ts)
	moreover from ntset' red12 have "M1'' = M1" by(auto dest: r1.new_thread_memory)
	moreover from ntset red have "M2 = m2'" by(auto dest: r2.new_thread_memory)
	ultimately show ?thesis using Bisim `T \<noteq> t` by auto
      next
	case (Some a)
	show ?thesis
	proof(cases "t = T")
	  case True
	  with s2' tst tsT have "X2 = x2'" "LN = redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>" by(auto)
	  with True bisim' tst'' show ?thesis by(auto simp add: redT_updLns_def expand_finfun_eq)
	next
	  case False
	  with s2' Some aoe tsT have "thr s2 T = \<lfloor>(X2, LN)\<rfloor>" by(auto dest: redT_updTs_Some)
	  with tbisim'[of T] False obtain X1
	    where tsT': "thr ?s1' T = \<lfloor>(X1, LN)\<rfloor>" and Bisim: "bisim (X1, m1) (X2, m2)"
	    by(auto simp add: tbisim_def split: split_if_asm)
	  with aoe' False have "thr ?s1'' T = \<lfloor>(X1, LN)\<rfloor>" by(simp add: redT_updTs_Some)
	  moreover from bisim_inv_red_other[OF Bisim bisim _ _ _ _ red \<tau> bisim' tasim] red11 red12 \<tau>1
	  have "bisim (X1, M1'') (X2, m2')" unfolding r1.\<tau>moves_def by auto
	  ultimately show ?thesis using False by(auto)
	qed
      qed
    qed
    ultimately show ?thesis using tasim unfolding \<tau>mred1_def_raw m\<tau>red1_conv tl2 r1.mthr.\<tau>moves_def by(fastsimp)
  next
    case (redT_acquire S T x2 ln n S')
    hence [simp]: "S = s2" "T = t" "ta2 = \<epsilon>" "S' = s2'"
      and tst: "thr s2 t = \<lfloor>(x2, ln)\<rfloor>" and wst: "wset s2 t = None"
      and maa: "may_acquire_all (locks s2) t ln" and ln: "0 < ln\<^sub>f n"
      and s2': "s2' = (acquire_all ls2 t ln, (ts2(t \<mapsto> (x2, no_wait_locks)), m2), ws2)" by auto
    from tst mbisim obtain x1 where tst': "ts1 t = \<lfloor>(x1, ln)\<rfloor>" 
      and bisim: "bisim (x1, m1) (x2, m2)" by(auto dest: mbisim_thrD2)
    let ?s1' = "(acquire_all ls2 t ln, (ts1(t \<mapsto> (x1, no_wait_locks)), m1), ws2)"
    from tst' wst maa ln have "s1 -1-t\<triangleright>\<epsilon>\<rightarrow> ?s1'"
      by-(rule r1.redT.redT_acquire, auto)
    moreover from tst' ln have "\<not> m\<tau>move1 s1 (t, \<epsilon>) ?s1'"
      by(auto simp add: acquire_all_def expand_fun_eq elim!: m\<tau>move1_cases)
    moreover have "mbisim ?s1' s2'"
    proof(rule mbisimI2)
      from s2' show "locks ?s1' = locks s2'" by auto
    next
      from s2' show "wset ?s1' = wset s2'" by auto
    next
      fix t'
      assume "thr s2' t' = None"
      with s2' have "thr s2 t' = None" by(auto split: split_if_asm)
      with mbisim_thrNone_eq[OF mbisim] have "ts1 t' = None" by simp
      with tst' show "thr ?s1' t' = None" by auto
    next
      fix t' X2 LN
      assume ts't: "thr s2' t' = \<lfloor>(X2, LN)\<rfloor>"
      show "\<exists>x1. thr ?s1' t' = \<lfloor>(x1, LN)\<rfloor> \<and> bisim (x1, shr ?s1') (X2, shr s2')"
      proof(cases "t' = t")
	case True
	with s2' tst ts't have [simp]: "X2 = x2" "LN = no_wait_locks" by simp_all
	with bisim tst True s2' show ?thesis by(auto)
      next
	case False
	with ts't s2' have "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" by auto
	with mbisim obtain X1 where "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" "bisim (X1, m1) (X2, m2)"
	  by(auto dest: mbisim_thrD2)
	with False s2' show ?thesis by auto
      qed
    qed
    ultimately show ?thesis by fastsimp
  qed
qed

end

sublocale FWweak_bisimulation < mthr!: weak_bisimulation r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2
by(rule mbisim_weak_bisimulation)

lemma list_all2_induct[consumes 1, case_names Nil Cons]:
  assumes major: "list_all2 P xs ys"
  and Nil: "Q [] []"
  and Cons: "\<And>x xs y ys. \<lbrakk> P x y; Q xs ys \<rbrakk> \<Longrightarrow> Q (x # xs) (y # ys)"
  shows "Q xs ys"
using major
by(induct xs arbitrary: ys)(auto simp add: list_all2_Cons1 Nil intro!: Cons)

lemma list_all2_split:
  assumes major: "list_all2 P xs ys"
  and split: "\<And>x y. P x y \<Longrightarrow> \<exists>z. Q x z \<and> R z y"
  shows "\<exists>zs. list_all2 Q xs zs \<and> list_all2 R zs ys"
using major
by(induct rule: list_all2_induct)(auto dest: split)

lemma rtranclp_False: "(\<lambda>a b. False)\<^sup>*\<^sup>* = op ="
by(auto simp add: expand_fun_eq elim: rtranclp_induct)

locale FWbisimulation = FWbisimulation_base_aux _ _ _ r2 bisim +
  bisimulation r1 r2 bisim "ta_bisim bisim"
  for r2 :: "('l,'t,'x2,'m,'w) semantics" ("_ -2-_\<rightarrow> _" [50,0,50] 80)
  and bisim :: "('x1 \<times> 'm, 'x2 \<times> 'm) bisim" ("_/ \<approx> _" [50, 50] 60) +
  assumes bisim_inv_red_other:
   "\<lbrakk> (x, m1) \<approx> (xx, m2); (x1, m1) \<approx> (x2, m2); 
      (x1, m1) -1-ta1\<rightarrow> (x1', m1'); (x2, m2) -2-ta2\<rightarrow> (x2', m2'); (x1', m1') \<approx> (x2', m2'); ta_bisim bisim ta1 ta2 \<rbrakk>
   \<Longrightarrow> (x, m1') \<approx> (xx, m2')"
begin

lemma mbisim_bisimulation:
  "bisimulation r1.redT r2.redT mbisim mta_bisim"
proof
  fix s1 s2 tta1 s1'
  assume mbisim: "s1 \<approx>m s2" and "r1.redT s1 tta1 s1'"
  moreover obtain t ta1 where "tta1 = (t, ta1)" by(cases tta1, blast)
  ultimately have red1: "s1 -1-t\<triangleright>ta1\<rightarrow> s1'" by simp
  
  from mbisim have "locks s1 = locks s2" "wset s1 = wset s2" by(auto simp add: mbisim_def)
  from red1 show "\<exists>s2' tta2. r2.redT s2 tta2 s2' \<and> s1' \<approx>m s2' \<and> tta1 \<sim>T tta2"
  proof(cases rule: r1.redT_elims)
    case (normal x1 x1')
    from `thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>` mbisim
    obtain x2 where "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>" 
      and "(x1, shr s1) \<approx> (x2, shr s2)" by(auto dest: mbisim_thrD1)
    with `(x1, shr s1) -1-ta1\<rightarrow> (x1', shr s1')` obtain x2' m' ta2
      where "(x2, shr s2) -2-ta2\<rightarrow> (x2', m')" "(x1', shr s1') \<approx> (x2', m')"
      and "ta1 \<sim>m ta2" by(auto dest: simulation1)
    
    let ?s2' = "(redT_updLs (locks s2) t \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>, (redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x2', redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>)), m'), redT_updWs (wset s2) t \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>)"
    from mbisim_actions_ok_inv[OF mbisim `ta1 \<sim>m ta2`, of t, symmetric]
      `lock_ok_las (locks s1) t \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>` `thread_oks (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>` `final_thread.cond_action_oks final1 s1 t \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub>`
    have aoe: "r2.actions_ok s2 t ta2" by auto
    with `(x2, shr s2) -2-ta2\<rightarrow> (x2', m')` `ta1 \<sim>m ta2` normal `thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>`
    have "s2 -2-t\<triangleright>ta2\<rightarrow> ?s2'" by -(erule r2.redT.redT_normal, auto simp add: `wset s1 = wset s2`)
    moreover from `ta1 \<sim>m ta2` have nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>"
      by(auto simp add: ta_bisim_def)
    { fix T
      assume "thr s1' T = None"
      with `thr s1' = redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1', redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>))`
      have "thr ?s2' T = None"
	apply(simp split: split_if_asm)
	apply(rule redT_updTs_nta_bisim_inv[OF nta, THEN iffD1])
	by(rule mbisim_thrNone_eq[OF mbisim]) }
    moreover
    { fix T x ln
      assume tst1'T: "thr s1' T = \<lfloor>(x, ln)\<rfloor>"
      have "\<exists>x'. (redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x2', redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>))) T = \<lfloor>(x', ln)\<rfloor> \<and> bisim (x, shr s1') (x', m')"
      proof(cases "thr s1 T")
	case None
	with `thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>` have "T \<noteq> t" by auto
	with mbisim None have "thr s2 T = None" by(simp add: mbisim_thrNone_eq)
	from None `thr s1' = redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1', redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>))`
	  `T \<noteq> t` tst1'T `thread_oks (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>`
	obtain m1 where "NewThread T x m1 \<in> set \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>" "ln = no_wait_locks" by(auto dest!: redT_updTs_new_thread)
	from `NewThread T x m1 \<in> set \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>` obtain tas1 tas1' where "\<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = tas1 @ NewThread T x m1 # tas1'"
	  by(auto simp add: in_set_conv_decomp)
	with `list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>`
	obtain tas2 x' m2 tas2' where "\<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> = tas2 @ NewThread T x' m2 # tas2'"
	  "length tas2 = length tas1" "length tas2' = length tas1'" "(x, m1) \<approx> (x', m2)" 
	  by(auto simp add: list_all2_append1 list_all2_Cons1, blast)
	with aoe have "redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(x', no_wait_locks)\<rfloor>"
	  by -(rule redT_updTs_new_thread_ts, auto)
	moreover from `NewThread T x m1 \<in> set \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>`  `(x1, shr s1) -1-ta1\<rightarrow> (x1', shr s1')` have "m1 = shr s1'"
	  by(auto dest: r1.new_thread_memory)
	moreover from `\<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> = tas2 @ NewThread T x' m2 # tas2'` `(x2, shr s2) -2-ta2\<rightarrow> (x2', m')`
	have "m2 = m'" by(auto dest: r2.new_thread_memory)
	ultimately show ?thesis using `ln = no_wait_locks` `(x, m1) \<approx> (x', m2)` `T \<noteq> t` by(auto)
      next
	case (Some a)
	show ?thesis
	proof(cases "t = T")
	  case True
	  with tst1'T `thr s1' = redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1', redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>))`
	  have "x = x1'" "ln = redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>" by auto
	  moreover with `ta1 \<sim>m ta2` `locks s1 = locks s2`
	  have "ln = redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>" by(auto simp add: ta_bisim_def)
	  ultimately show ?thesis using `(x1', shr s1') \<approx> (x2', m')` True by(simp)
	next
	  case False
	  with Some `thread_oks (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>` tst1'T
	    `thr s1' = redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1', redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>))`
	  have "a = (x, ln)" by(auto dest: redT_updTs_Some)
	  with Some obtain x' where "thr s2 T = \<lfloor>(x', ln)\<rfloor>" "(x, shr s1) \<approx> (x', shr s2)"
	    by(auto dest: mbisim_thrD1[OF mbisim])
	  with aoe have "redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(x', ln)\<rfloor>"
	    by -(rule redT_updTs_Some, auto simp add: ta_bisim_def)
	  moreover from `(x, shr s1) \<approx> (x', shr s2)` `(x1, shr s1) \<approx> (x2, shr s2)`
	    `(x1, shr s1) -1-ta1\<rightarrow> (x1', shr s1')` `(x2, shr s2) -2-ta2\<rightarrow> (x2', m')`
	      `bisim (x1', shr s1') (x2', m')` `ta_bisim bisim ta1 ta2`
	  have "(x, shr s1') \<approx> (x', m')" by(rule bisim_inv_red_other)
	  ultimately show ?thesis using False by(simp)
	qed
      qed
      hence "\<exists>x'. thr ?s2' T = \<lfloor>(x', ln)\<rfloor> \<and> (x, shr s1') \<approx> (x', shr ?s2')" by simp }
    ultimately have "s1' \<approx>m ?s2'" using `locks s1' = redT_updLs (locks s1) t \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>`
      `wset s1' = redT_updWs (wset s1) t \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>` `ta1 \<sim>m ta2`
      `locks s1 = locks s2` `wset s1 = wset s2` by(auto intro: mbisimI simp add: ta_bisim_def)
    with `ta1 \<sim>m ta2` `s2 -2-t\<triangleright>ta2\<rightarrow> ?s2'` `tta1 = (t, ta1)` show ?thesis by fastsimp
  next
    case (acquire x ln n)
    from `thr s1 t = \<lfloor>(x, ln)\<rfloor>` obtain x' where "thr s2 t = \<lfloor>(x', ln)\<rfloor>" "(x, shr s1) \<approx> (x', shr s2)"
      by(auto dest: mbisim_thrD1[OF mbisim])
    let ?s2' = "(acquire_all (locks s2) t ln, (thr s2(t \<mapsto> (x', no_wait_locks)), shr s2), wset s2)"
    from `wset s1 t = None` `may_acquire_all (locks s1) t ln` `0 < ln\<^sub>f n` 
      `locks s1 = locks s2` `wset s1 = wset s2` `thr s2 t = \<lfloor>(x', ln)\<rfloor>`
    have "s2 -2-t\<triangleright>\<epsilon>\<rightarrow> ?s2'" by(auto intro: r2.redT.redT_acquire)
    moreover have "s1' \<approx>m ?s2'"
    proof(rule mbisimI)
      from `locks s1' = acquire_all (locks s1) t ln` `locks s1 = locks s2`
      show "locks s1' = locks ?s2'" by simp
    next
      from `wset s1' = wset s1` `wset s1 = wset s2`
      show "wset s1' = wset ?s2'" by simp
    next
      fix T
      assume "thr s1' T = None"
      with `thr s1' = thr s1(t \<mapsto> (x, no_wait_locks))` have "T \<noteq> t" "thr s1 T = None" by(auto split: split_if_asm)
      with mbisim_thrNone_eq[OF mbisim] show "thr ?s2' T = None" by simp
    next
      fix T x1 LN
      assume "thr s1' T = \<lfloor>(x1, LN)\<rfloor>"
      show "\<exists>x2. thr ?s2' T = \<lfloor>(x2, LN)\<rfloor> \<and> (x1, shr s1') \<approx> (x2, shr ?s2')"
      proof(cases "T = t")
	case True
	with `(x, shr s1) \<approx> (x', shr s2)` `shr s1' = shr s1` `thr s1' = thr s1(t \<mapsto> (x, no_wait_locks))` 
	  `thr s1' T = \<lfloor>(x1, LN)\<rfloor>`
	show ?thesis by(auto)
      next
	case False
	with `thr s1' T = \<lfloor>(x1, LN)\<rfloor>` `thr s1' = thr s1(t \<mapsto> (x, no_wait_locks))`
	have "thr s1 T = \<lfloor>(x1, LN)\<rfloor>" by simp
	then obtain x2 where "thr s2 T = \<lfloor>(x2, LN)\<rfloor>" "(x1, shr s1) \<approx> (x2, shr s2)"
	  by(auto dest: mbisim_thrD1[OF mbisim])
	with False `shr s1' = shr s1` show ?thesis by(simp)
      qed
    qed
    ultimately show ?thesis using `tta1 = (t, ta1)` `ta1 = \<epsilon>` by(fastsimp)
  qed
next
  fix s2 s1 tta2 s2'
  assume "s1 \<approx>m s2" and "r2.redT s2 tta2 s2'"
  moreover obtain t ta2 where "tta2 = (t, ta2)" by(cases tta2, blast)
  ultimately have red2: "s2 -2-t\<triangleright>ta2\<rightarrow> s2'" and mbisim: "s1 \<approx>m s2" by(simp_all)
  from mbisim have "locks s1 = locks s2" "wset s1 = wset s2" by(auto simp add: mbisim_def)
  from red2 have "\<exists>s1' tta1. r1.redT s1 tta1 s1' \<and> s1' \<approx>m s2' \<and> tta1 \<sim>T tta2"
  proof(cases rule: r2.redT_elims)
    case (normal x2 x2')
    from `thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>` mbisim
    obtain x1 where "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" "(x1, shr s1) \<approx> (x2, shr s2)"
      by(auto dest: mbisim_thrD2)
    with `(x2, shr s2) -2-ta2\<rightarrow> (x2', shr s2')`
    obtain x1' m' ta1 where "(x1, shr s1) -1-ta1\<rightarrow> (x1', m')" "(x1', m') \<approx> (x2', shr s2')" "ta1 \<sim>m ta2"
      by(auto dest: simulation2)
    let ?s1' = "(redT_updLs (locks s1) t \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>, (redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1', redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>)), m'), redT_updWs (wset s1) t \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>)"
    from mbisim_actions_ok_inv[OF mbisim `ta1 \<sim>m ta2`, of t]
      `lock_ok_las (locks s2) t \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>` `thread_oks (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>` `final_thread.cond_action_oks final2 s2 t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>`
    have aoe: "r1.actions_ok s1 t ta1" by auto
    with `(x1, shr s1) -1-ta1\<rightarrow> (x1', m')` `ta1 \<sim>m ta2` normal `thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>`
    have "s1 -1-t\<triangleright>ta1\<rightarrow> ?s1'" by -(erule r1.redT.redT_normal, auto simp add: `wset s1 = wset s2`)
    moreover from `ta1 \<sim>m ta2` have nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>"
      by(auto simp add: ta_bisim_def)
    { fix T
      assume "thr s2' T = None"
      with `thr s2' = redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x2', redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>))`
      have "thr ?s1' T = None"
	apply(simp split: split_if_asm)
	apply(rule redT_updTs_nta_bisim_inv[OF nta, THEN iffD2])
	by(rule mbisim_thrNone_eq[OF mbisim]) }
    moreover { fix T x' ln
      assume tst2'T: "thr s2' T = \<lfloor>(x', ln)\<rfloor>"
      have "\<exists>x. (redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x1', redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>))) T = \<lfloor>(x, ln)\<rfloor> \<and> (x, m') \<approx> (x', shr s2')"
      proof(cases "thr s2 T")
	case None
	with `thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>` have "T \<noteq> t" by auto
	with mbisim None have "thr s1 T = None" by(simp add: mbisim_thrNone_eq)
	from None `thr s2' = redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x2', redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>))`
	  `T \<noteq> t` tst2'T `thread_oks (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>`
	obtain m2 where "NewThread T x' m2 \<in> set \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" "ln = no_wait_locks" by(auto dest!: redT_updTs_new_thread)
	from `NewThread T x' m2 \<in> set \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>` obtain tas2 tas2' where "\<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> = tas2 @ NewThread T x' m2 # tas2'"
	  by(auto simp add: in_set_conv_decomp)
	with `list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>`
	obtain tas1 x m1 tas1' where "\<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = tas1 @ NewThread T x m1 # tas1'"
	  "length tas1 = length tas2" "length tas1' = length tas2'" "(x, m1) \<approx> (x', m2)" 
	  by(auto simp add: list_all2_append2 list_all2_Cons2, blast)
	with aoe have "redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(x, no_wait_locks)\<rfloor>"
	  by -(rule redT_updTs_new_thread_ts, auto)
	moreover from `NewThread T x' m2 \<in> set \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>` `(x2, shr s2) -2-ta2\<rightarrow> (x2', shr s2')` have "m2 = shr s2'"
	  by(auto dest: r2.new_thread_memory)
	moreover from `\<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = tas1 @ NewThread T x m1 # tas1'` `(x1, shr s1) -1-ta1\<rightarrow> (x1', m')`
	have "m1 = m'" by(auto dest: r1.new_thread_memory)
	ultimately show ?thesis using `ln = no_wait_locks` `(x, m1) \<approx> (x', m2)` `T \<noteq> t` by(auto)
      next
	case (Some a)
	show ?thesis
	proof(cases "t = T")
	  case True
	  with tst2'T `thr s2' = redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x2', redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>))`
	  have "x' = x2'" "ln = redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>" by auto
	  moreover with `ta1 \<sim>m ta2` `locks s1 = locks s2`
	  have "ln = redT_updLns (locks s1) t no_wait_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>" by(simp add: ta_bisim_def)
	  ultimately show ?thesis using `(x1', m') \<approx> (x2', shr s2')` True by(simp)
	next
	  case False
	  with Some `thread_oks (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>` tst2'T
	    `thr s2' = redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>(t \<mapsto> (x2', redT_updLns (locks s2) t no_wait_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>))`
	  have "a = (x', ln)" by(auto dest: redT_updTs_Some)
	  with Some obtain x where "thr s1 T = \<lfloor>(x, ln)\<rfloor>" "(x, shr s1) \<approx> (x', shr s2)"
	    by(auto dest: mbisim_thrD2[OF mbisim])
	  with aoe have "redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> T = \<lfloor>(x, ln)\<rfloor>"
	    by -(rule redT_updTs_Some, auto)
	  moreover from `(x, shr s1) \<approx> (x', shr s2)` `(x1, shr s1) \<approx> (x2, shr s2)`
	    `(x1, shr s1) -1-ta1\<rightarrow> (x1', m')` `(x2, shr s2) -2-ta2\<rightarrow> (x2', shr s2')`
	    `(x1', m') \<approx> (x2', shr s2')` `ta1 \<sim>m ta2`
	  have "(x, m') \<approx> (x', shr s2')" by(rule bisim_inv_red_other)
	  ultimately show ?thesis using False by(simp)
	qed
      qed
      hence "\<exists>x. thr ?s1' T = \<lfloor>(x, ln)\<rfloor> \<and> (x, shr ?s1') \<approx> (x', shr s2')" by simp }
    ultimately have "?s1' \<approx>m s2'" using `locks s2' = redT_updLs (locks s2) t \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>`
      `wset s2' = redT_updWs (wset s2) t \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>` `ta1 \<sim>m ta2`
      `locks s1 = locks s2` `wset s1 = wset s2`
      by(auto intro: mbisimI2 simp add: ta_bisim_def simp del: fun_upd_apply)
    with `ta1 \<sim>m ta2` `s1 -1-t\<triangleright>ta1\<rightarrow> ?s1'` `tta2 = (t, ta2)` show ?thesis by fastsimp
  next
    case (acquire x ln n)
    from `thr s2 t = \<lfloor>(x, ln)\<rfloor>` obtain x' where "thr s1 t = \<lfloor>(x', ln)\<rfloor>" "(x', shr s1) \<approx> (x, shr s2)"
      by(auto dest: mbisim_thrD2[OF mbisim])
    let ?s1' = "(acquire_all (locks s1) t ln, (thr s1(t \<mapsto> (x', no_wait_locks)), shr s1), wset s1)"
    from `wset s2 t = None` `may_acquire_all (locks s2) t ln` `0 < ln\<^sub>f n` 
      `locks s1 = locks s2` `wset s1 = wset s2` `thr s1 t = \<lfloor>(x', ln)\<rfloor>`
    have "s1 -1-t\<triangleright>\<epsilon>\<rightarrow> ?s1'" by(auto intro: r1.redT.redT_acquire)
    moreover have "?s1' \<approx>m s2'"
    proof(rule mbisimI2)
      from `locks s2' = acquire_all (locks s2) t ln` `locks s1 = locks s2`
      show "locks ?s1' = locks s2'" by simp
    next
      from `wset s2' = wset s2` `wset s1 = wset s2`
      show "wset ?s1' = wset s2'" by simp
    next
      fix T
      assume "thr s2' T = None"
      with `thr s2' = thr s2(t \<mapsto> (x, no_wait_locks))` have "T \<noteq> t" "thr s2 T = None" by(auto split: split_if_asm)
      with mbisim_thrNone_eq[OF mbisim] show "thr ?s1' T = None" by simp
    next
      fix T x2 LN
      assume "thr s2' T = \<lfloor>(x2, LN)\<rfloor>"
      show "\<exists>x1. thr ?s1' T = \<lfloor>(x1, LN)\<rfloor> \<and> (x1, shr ?s1') \<approx> (x2, shr s2')"
      proof(cases "T = t")
	case True
	with `(x', shr s1) \<approx> (x, shr s2)` `shr s2' = shr s2` `thr s2' = thr s2(t \<mapsto> (x, no_wait_locks))` 
	  `thr s2' T = \<lfloor>(x2, LN)\<rfloor>`
	show ?thesis by(auto)
      next
	case False
	with `thr s2' T = \<lfloor>(x2, LN)\<rfloor>` `thr s2' = thr s2(t \<mapsto> (x, no_wait_locks))`
	have "thr s2 T = \<lfloor>(x2, LN)\<rfloor>" by simp
	then obtain x1 where "thr s1 T = \<lfloor>(x1, LN)\<rfloor>" "(x1, shr s1) \<approx> (x2, shr s2)"
	  by(auto dest: mbisim_thrD2[OF mbisim])
	with False `shr s2' = shr s2` show ?thesis by(simp)
      qed
    qed
    ultimately show ?thesis using `tta2 = (t, ta2)` `ta2 = \<epsilon>` by(fastsimp)
  qed
  thus "\<exists>s1' tta1. r1.redT s1 tta1 s1' \<and> s1' \<approx>m s2' \<and> tta1 \<sim>T tta2" by(simp)
qed

end

sublocale FWbisimulation < mthr!: bisimulation r1.redT r2.redT mbisim mta_bisim
by(rule mbisim_bisimulation)

end