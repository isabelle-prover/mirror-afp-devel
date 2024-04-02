theory Broadcast_Frame
  imports "Psi_Calculi.Frame"
begin

locale assertionAux = Frame.assertionAux SCompose SImp SBottom SChanEq
  for SCompose :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"     (infixr "\<otimes>" 80)
  and SImp :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool"       ("_ \<turnstile> _" [70, 70] 70)
  and SBottom :: 'b                             ("\<bottom>" 90)
  and SChanEq :: "('a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c)"    ("_ \<leftrightarrow> _" [80, 80] 80)
  +
  fixes SOutCon  :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c"   ("_ \<preceq> _" [80, 80] 80)
    and SInCon   :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c"   ("_ \<succeq> _" [80, 80] 80)

assumes statEqvt'''[eqvt]: "\<And>p::name prm. p \<bullet> (M \<preceq> N) = (p \<bullet> M) \<preceq> (p \<bullet> N)"
  and   statEqvt''''[eqvt]: "\<And>p::name prm. p \<bullet> (M \<succeq> N) = (p \<bullet> M) \<succeq> (p \<bullet> N)"

begin

lemma chanInConSupp:
  fixes M :: 'a
    and N :: 'a

shows "(supp(M \<succeq> N)::name set) \<subseteq> ((supp M) \<union> (supp N))"
proof -
  {
    fix x::name
    let ?P = "\<lambda>y. ([(x, y)] \<bullet> M) \<succeq> [(x, y)] \<bullet> N \<noteq> M \<succeq> N"
    let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> M"
    assume "finite {y. ?Q y N}"
    moreover assume "finite {y. ?Q y M}" and "infinite {y. ?P(y)}"
    then have "infinite({y. ?P(y)} - {y. ?Q y M})" by(rule Diff_infinite_finite)
    ultimately have "infinite(({y. ?P(y)} - {y. ?Q y M}) - {y. ?Q y N})" by(rule Diff_infinite_finite)
    then have "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)})" by(simp add: set_diff_eq)
    moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)} = {}" by auto
    ultimately have "infinite {}" by(blast dest: Infinite_cong)
    then have False by simp
  }
  then show ?thesis by(auto simp add: eqvts supp_def)
qed

lemma chanOutConSupp:
  fixes M :: 'a
    and N :: 'a

shows "(supp(M \<preceq> N)::name set) \<subseteq> ((supp M) \<union> (supp N))"
proof -
  {
    fix x::name
    let ?P = "\<lambda>y. ([(x, y)] \<bullet> M) \<preceq> [(x, y)] \<bullet> N \<noteq> M \<preceq> N"
    let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> M"
    assume "finite {y. ?Q y N}"
    moreover assume "finite {y. ?Q y M}" and "infinite {y. ?P(y)}"
    then have "infinite({y. ?P(y)} - {y. ?Q y M})" by(rule Diff_infinite_finite)
    ultimately have "infinite(({y. ?P(y)} - {y. ?Q y M}) - {y. ?Q y N})" by(rule Diff_infinite_finite)
    then have "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)})" by(simp add: set_diff_eq)
    moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)} = {}" by auto
    ultimately have "infinite {}" by(blast dest: Infinite_cong)
    then have False by simp
  }
  then show ?thesis by (auto simp add: eqvts supp_def)
qed

lemma freshInCon[intro]:
  fixes x :: name
    and M :: 'a
    and N :: 'a

assumes "x \<sharp> M"
  and   "x \<sharp> N"

shows "x \<sharp> M \<succeq> N"
  using assms chanInConSupp
  by(auto simp add: fresh_def)

lemma freshInConChain[intro]:
  fixes xvec :: "name list"
    and Xs   :: "name set"
    and M    :: 'a
    and N    :: 'a

shows "\<lbrakk>xvec \<sharp>* M; xvec \<sharp>* N\<rbrakk> \<Longrightarrow> xvec \<sharp>* (M \<succeq> N)"
  and "\<lbrakk>Xs \<sharp>* M; Xs \<sharp>* N\<rbrakk> \<Longrightarrow> Xs \<sharp>* (M \<succeq> N)"
  by(auto simp add: fresh_star_def)

lemma freshOutCon[intro]:
  fixes x :: name
    and M :: 'a
    and N :: 'a

assumes "x \<sharp> M"
  and   "x \<sharp> N"

shows "x \<sharp> M \<preceq> N"
  using assms chanOutConSupp
  by(auto simp add: fresh_def)

lemma freshOutConChain[intro]:
  fixes xvec :: "name list"
    and Xs   :: "name set"
    and M    :: 'a
    and N    :: 'a

shows "\<lbrakk>xvec \<sharp>* M; xvec \<sharp>* N\<rbrakk> \<Longrightarrow> xvec \<sharp>* (M \<preceq> N)"
  and "\<lbrakk>Xs \<sharp>* M; Xs \<sharp>* N\<rbrakk> \<Longrightarrow> Xs \<sharp>* (M \<preceq> N)"
  by(auto simp add: fresh_star_def)

lemma chanOutConClosed:
  fixes \<Psi> :: 'b
    and M :: 'a
    and N :: 'a
    and p :: "name prm"

assumes "\<Psi> \<turnstile> M \<preceq> N"

shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> M) \<preceq> (p \<bullet> N)"
proof -
  from \<open>\<Psi> \<turnstile> M \<preceq> N\<close> have "(p \<bullet> \<Psi>) \<turnstile> p \<bullet> (M \<preceq> N)"
    by(rule statClosed)
  then show ?thesis by(auto simp add: eqvts)
qed

lemma chanInConClosed:
  fixes \<Psi> :: 'b
    and M :: 'a
    and N :: 'a
    and p :: "name prm"

assumes "\<Psi> \<turnstile> M \<succeq> N"

shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> M) \<succeq> (p \<bullet> N)"
proof -
  from \<open>\<Psi> \<turnstile> M \<succeq> N\<close> have "(p \<bullet> \<Psi>) \<turnstile> p \<bullet> (M \<succeq> N)"
    by(rule statClosed)
  then show ?thesis by(auto simp add: eqvts)
qed

end

locale assertion = assertionAux SCompose SImp SBottom SChanEq SOutCon SInCon + assertion SCompose SImp SBottom SChanEq
  for SCompose :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"
  and SImp     :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool"
  and SBottom  :: 'b
  and SChanEq  :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c"
  and SOutCon  :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c"
  and SInCon   :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c" +

  assumes chanOutConSupp: "SImp \<Psi> (SOutCon M N) \<Longrightarrow> (((supp N)::name set) \<subseteq> ((supp M)::name set))"
    and   chanInConSupp:  "SImp \<Psi> (SInCon N M) \<Longrightarrow> (((supp N)::name set) \<subseteq> ((supp M)::name set))"

begin

notation SOutCon ("_ \<preceq> _" [90, 90] 90)
notation SInCon ("_ \<succeq> _" [90, 90] 90)

end

end
