section \<open> Ground Mereology \<close>

(*<*)
theory M
  imports PM
begin
(*>*)

text \<open> The theory of \emph{ground mereology} adds to premereology the antisymmetry of parthood, and
defines proper parthood as nonidentical parthood.\footnote{For this axiomatization of ground mereology see,
for example, \<^cite>\<open>"varzi_parts_1996"\<close> p. 261 and \<^cite>\<open>"casati_parts_1999"\<close> p. 36. For discussion of the 
antisymmetry of parthood see, for example, \<^cite>\<open>"cotnoir_antisymmetry_2010"\<close>. For the definition of 
proper parthood as nonidentical parthood, see for example, \<^cite>\<open>"leonard_calculus_1940"\<close> p. 47.} 
In other words, ground mereology assumes that parthood is a partial order.\<close>

locale M = PM +
  assumes part_antisymmetry: "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"
  assumes nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
begin

subsection \<open> Proper Parthood \<close>

lemma proper_implies_part: "PP x y \<Longrightarrow> P x y"
proof -
  assume "PP x y"
  with nip_eq have "P x y \<and> x \<noteq> y"..
  thus "P x y"..
qed

lemma proper_implies_distinct: "PP x y \<Longrightarrow> x \<noteq> y"
proof -
  assume "PP x y"
  with nip_eq have "P x y \<and> x \<noteq> y"..
  thus "x \<noteq> y"..
qed

lemma proper_implies_not_part: "PP x y \<Longrightarrow> \<not> P y x"
proof -
  assume "PP x y"
  hence "P x y" by (rule proper_implies_part)
  show "\<not> P y x"
  proof
    from \<open>PP x y\<close> have "x \<noteq> y" by (rule proper_implies_distinct)
    moreover assume "P y x"
    with \<open>P x y\<close> have "x = y" by (rule part_antisymmetry)
    ultimately show "False"..
  qed
qed

lemma proper_part_asymmetry: "PP x y \<Longrightarrow> \<not> PP y x"
proof -
  assume "PP x y"
  hence "P x y" by (rule proper_implies_part)
  from \<open>PP x y\<close> have "x \<noteq> y" by (rule proper_implies_distinct)
  show "\<not> PP y x"
  proof
    assume "PP y x"
    hence "P y x" by (rule proper_implies_part)
    with \<open>P x y\<close> have "x = y" by (rule part_antisymmetry)
    with \<open>x \<noteq> y\<close> show "False"..
  qed
qed

lemma proper_implies_overlap: "PP x y \<Longrightarrow> O x y"
proof -
  assume "PP x y"
  hence "P x y" by (rule proper_implies_part)
  thus "O x y" by (rule part_implies_overlap)
qed

end

text \<open> The rest of this section compares four alternative axiomatizations of ground mereology, and
verifies their equivalence. \<close>

text \<open> The first alternative axiomatization defines proper parthood as nonmutual instead of nonidentical parthood.\footnote{
See, for example, \<^cite>\<open>"varzi_parts_1996"\<close> p. 261 and \<^cite>\<open>"casati_parts_1999"\<close> p. 36. For the distinction
between nonmutual and nonidentical parthood, see \<^cite>\<open>"parsons_many_2014"\<close> pp. 6-8.}
In the presence of antisymmetry, the two definitions of proper parthood are equivalent.\footnote{
See \<^cite>\<open>"cotnoir_antisymmetry_2010"\<close> p. 398, \<^cite>\<open>"donnelly_using_2011"\<close> p. 233, 
\<^cite>\<open>"cotnoir_non-wellfounded_2012"\<close> p. 191, \<^cite>\<open>"obojska_remarks_2013"\<close> p. 344,
\<^cite>\<open>"cotnoir_does_2016"\<close> p. 128 and \<^cite>\<open>"cotnoir_is_2018"\<close>.} \<close>

locale M1 = PM +
  assumes nmp_eq: "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x"
  assumes part_antisymmetry: "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"

sublocale M \<subseteq> M1
proof
  fix x y
  show nmp_eq: "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x"
  proof
    assume "PP x y"
    with nip_eq have nip: "P x y \<and> x \<noteq> y"..
    hence "x \<noteq> y"..
    from nip have "P x y"..
    moreover have "\<not> P y x"
    proof
      assume "P y x"
      with \<open>P x y\<close> have "x = y" by (rule part_antisymmetry)
      with \<open>x \<noteq> y\<close> show "False"..
    qed
    ultimately show "P x y \<and> \<not> P y x"..
  next
    assume nmp: "P x y \<and> \<not> P y x"
    hence "\<not> P y x"..
    from nmp have "P x y"..
    moreover have "x \<noteq> y"
    proof
      assume "x = y"
      hence "\<not> P y y" using \<open>\<not> P y x\<close> by (rule subst)
      thus "False" using part_reflexivity..
    qed
    ultimately have "P x y \<and> x \<noteq> y"..
    with nip_eq show "PP x y"..
  qed
  show  "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y" using part_antisymmetry.
qed

sublocale M1 \<subseteq> M
proof
  fix x y
  show nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  proof
    assume "PP x y"
    with nmp_eq have nmp: "P x y \<and> \<not> P y x"..
    hence "\<not> P y x"..
    from nmp have "P x y"..
    moreover have "x \<noteq> y"
    proof
      assume "x = y"
      hence "\<not> P y y" using \<open>\<not> P y x\<close> by (rule subst)
      thus "False" using part_reflexivity..
    qed
    ultimately show "P x y \<and> x \<noteq> y"..
  next
    assume nip: "P x y \<and> x \<noteq> y"
    hence "x \<noteq> y"..
    from nip have "P x y"..
    moreover have "\<not> P y x"
    proof
      assume "P y x"
      with \<open>P x y\<close> have "x = y" by (rule part_antisymmetry)
      with \<open>x \<noteq> y\<close> show "False"..
    qed
    ultimately have "P x y \<and> \<not> P y x"..
    with nmp_eq show "PP x y"..
  qed
  show  "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y" using part_antisymmetry.
qed

text \<open> Conversely, assuming the two definitions of proper parthood are equivalent entails the antisymmetry
of parthood, leading to the second alternative axiomatization, which assumes both equivalencies.\footnote{
For this point see especially \<^cite>\<open>"parsons_many_2014"\<close> pp. 9-10.} \<close>

locale M2 = PM +
  assumes nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  assumes nmp_eq: "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x"

sublocale M \<subseteq> M2
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x" using nmp_eq.
qed

sublocale M2 \<subseteq> M
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y" 
  proof -
    assume "P x y"
    assume "P y x"
    show "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      with \<open>P x y\<close> have "P x y \<and> x \<noteq> y"..
      with nip_eq have "PP x y"..
      with nmp_eq have "P x y \<and> \<not> P y x"..
      hence "\<not> P y x"..
      thus "False" using \<open>P y x\<close>..
    qed
  qed
qed

text \<open> In the context of the other axioms, antisymmetry is equivalent to the extensionality of parthood, 
which gives the third alternative axiomatization.\footnote{For this point see \<^cite>\<open>"cotnoir_antisymmetry_2010"\<close> p. 401 
and \<^cite>\<open>"cotnoir_non-wellfounded_2012"\<close> p. 191-2.} \<close>

locale M3 = PM +
  assumes nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  assumes part_extensionality: "x = y \<longleftrightarrow> (\<forall> z. P z x \<longleftrightarrow> P z y)"

sublocale M \<subseteq> M3
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show part_extensionality: "x = y \<longleftrightarrow> (\<forall> z. P z x \<longleftrightarrow> P z y)"
  proof
    assume "x = y"
    moreover have "\<forall> z. P z x \<longleftrightarrow> P z x" by simp
    ultimately show "\<forall> z. P z x \<longleftrightarrow> P z y" by (rule subst)
  next
    assume z: "\<forall> z. P z x \<longleftrightarrow> P z y"
    show "x = y"
    proof (rule part_antisymmetry)
      from z have "P y x \<longleftrightarrow> P y y"..
      moreover have "P y y" by (rule part_reflexivity)
      ultimately show "P y x"..
    next
      from z have "P x x \<longleftrightarrow> P x y"..
      moreover have "P x x" by (rule part_reflexivity)
      ultimately show "P x y"..
    qed
  qed
qed

sublocale M3 \<subseteq> M
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show part_antisymmetry: "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"
  proof -
    assume "P x y"
    assume "P y x"
    have "\<forall> z. P z x \<longleftrightarrow> P z y"
    proof
      fix z
      show "P z x \<longleftrightarrow> P z y"
      proof
        assume "P z x"
        thus "P z y" using \<open>P x y\<close> by (rule part_transitivity)
      next
        assume "P z y"
        thus "P z x" using \<open>P y x\<close> by (rule part_transitivity)
      qed
    qed
    with part_extensionality show "x = y"..
  qed
qed

text \<open>The fourth axiomatization adopts proper parthood as primitive.\footnote{See, for example, 
\<^cite>\<open>"simons_parts:_1987"\<close>, p. 26 and \<^cite>\<open>"casati_parts_1999"\<close> p. 37.} Improper parthood is
defined as proper parthood or identity.\<close>

locale M4 =
  assumes part_eq: "P x y \<longleftrightarrow> PP x y \<or> x = y"
  assumes  overlap_eq: "O x y \<longleftrightarrow> (\<exists> z. P z x \<and> P z y)"
  assumes proper_part_asymmetry: "PP x y \<Longrightarrow> \<not> PP y x"
  assumes proper_part_transitivity: "PP x y \<Longrightarrow> PP y z \<Longrightarrow> PP x z"
begin

lemma proper_part_irreflexivity: "\<not> PP x x"
proof
  assume "PP x x"
  hence "\<not> PP x x" by (rule proper_part_asymmetry)
  thus "False" using \<open>PP x x\<close>..
qed

end

sublocale M \<subseteq> M4
proof
  fix x y z
  show part_eq: "P x y \<longleftrightarrow> (PP x y \<or> x = y)"
  proof
    assume "P x y"
    show "PP x y \<or> x = y"
    proof cases
      assume "x = y"
      thus "PP x y \<or> x = y"..
    next
      assume "x \<noteq> y"
      with \<open>P x y\<close> have "P x y \<and> x \<noteq> y"..
      with nip_eq have "PP x y"..
      thus "PP x y \<or> x = y"..
    qed
  next
    assume "PP x y \<or> x = y"
    thus "P x y"
    proof
      assume "PP x y"
      thus "P x y" by (rule proper_implies_part)
    next
      assume "x = y" 
      thus "P x y" by (rule identity_implies_part)
    qed
  qed
  show "O x y \<longleftrightarrow> (\<exists> z. P z x \<and> P z y)" using overlap_eq.
  show "PP x y \<Longrightarrow> \<not> PP y x" using proper_part_asymmetry.
  show proper_part_transitivity: "PP x y \<Longrightarrow> PP y z \<Longrightarrow> PP x z"
  proof -
    assume "PP x y"
    assume "PP y z"
    have "P x z \<and> x \<noteq> z"
    proof
      from \<open>PP x y\<close> have "P x y" by (rule proper_implies_part)
      moreover from \<open>PP y z\<close> have "P y z" by (rule proper_implies_part)
      ultimately show "P x z" by (rule part_transitivity)
    next
      show "x \<noteq> z"
      proof
        assume "x = z"
        hence "PP y x" using \<open>PP y z\<close> by (rule ssubst)
        hence "\<not> PP x y" by (rule proper_part_asymmetry)
        thus "False" using \<open>PP x y\<close>..
      qed
    qed
    with nip_eq show "PP x z"..
  qed
qed

sublocale M4 \<subseteq> M
proof
  fix x y z
  show proper_part_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  proof
    assume "PP x y"
    hence "PP x y \<or> x = y"..
    with part_eq have "P x y"..
    moreover have "x \<noteq> y"
    proof
      assume "x = y"
      hence "PP y y" using \<open>PP x y\<close> by (rule subst)
      with proper_part_irreflexivity show "False"..
    qed
    ultimately show "P x y \<and> x \<noteq> y"..
  next
    assume rhs: "P x y \<and> x \<noteq> y"
    hence "x \<noteq> y"..
    from rhs have "P x y"..
    with part_eq have "PP x y \<or> x = y"..
    thus "PP x y" 
    proof
      assume "PP x y"
      thus "PP x y".
    next
      assume "x = y"
      with \<open>x \<noteq> y\<close> show "PP x y"..
    qed
  qed
  show "P x x"
  proof -
    have "x = x" by (rule refl)
    hence "PP x x \<or> x = x"..
    with part_eq show "P x x"..
  qed
  show "O x y \<longleftrightarrow> (\<exists> z. P z x \<and> P z y)" using overlap_eq.
  show "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"
  proof -
    assume "P x y"
    assume "P y x"
    from part_eq have "PP x y \<or> x = y" using \<open>P x y\<close>..
    thus "x = y"
    proof
      assume "PP x y"
      hence "\<not> PP y x" by (rule proper_part_asymmetry)
      from part_eq have "PP y x \<or> y = x" using \<open>P y x\<close>..
      thus "x = y"
      proof
        assume "PP y x"
        with \<open>\<not> PP y x\<close> show "x = y"..
      next
        assume "y = x"
        thus "x = y"..
      qed
    qed
  qed
  show "P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
  proof -
    assume "P x y"
    assume "P y z"
    with part_eq have "PP y z \<or> y = z"..
    hence "PP x z \<or> x = z"
    proof
      assume "PP y z"
      from part_eq have "PP x y \<or> x = y" using \<open>P x y\<close>..
      hence "PP x z"
      proof
        assume "PP x y"
        thus "PP x z" using \<open>PP y z\<close> by (rule proper_part_transitivity)
      next
        assume "x = y"
        thus "PP x z" using \<open>PP y z\<close> by (rule ssubst)
      qed
      thus "PP x z \<or> x = z"..
    next
      assume "y = z"
      moreover from part_eq have "PP x y \<or> x = y" using \<open>P x y\<close>..
      ultimately show "PP x z \<or> x = z" by (rule subst)
    qed
    with part_eq show "P x z"..
  qed
qed

(*<*) end (*>*)