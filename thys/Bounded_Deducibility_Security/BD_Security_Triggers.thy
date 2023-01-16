(*<*)
theory BD_Security_Triggers
  imports BD_Security_TS
begin
(*>*)

subsection \<open>Trigger-preserving BD security\<close>

text \<open>Section 3.3 of \<^cite>\<open>"cosmed-jar2018"\<close> gives a recipe for incorporating declassification
triggers into the bound, and discusses the question whether this is always possible without loss of
generality, giving a partially positive answer:  the transformed security property is equivalent to
a slightly strengthened version of the original one.\<close>

subsubsection \<open>Definition\<close>

context Abstract_BD_Security
begin

text \<open>The strengthened variant of BD Security is called \<^emph>\<open>trigger-preserving\<close> in
\<^cite>\<open>"cosmed-jar2018"\<close>, because the difference to regular BD Security is that the (non-firing of
the) declassification trigger in the original trace is preserved in alternative traces.\<close>

definition secureTT :: bool where
"secureTT \<equiv>
 \<forall>tr vl vl1.
   validSystemTrace tr \<and> TT tr \<and> B vl vl1 \<and> V tr = vl \<longrightarrow>
   (\<exists>tr1. validSystemTrace tr1 \<and> TT tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1)"

text \<open>This indeed strengthens the original notion of BD Security.\<close>

lemma secureTT_secure: "secureTT \<Longrightarrow> secure"
  unfolding secureTT_def secure_def
  by blast

lemma secureTT_E:
  assumes "secureTT"
  and "validSystemTrace tr" and "TT tr" and "B vl vl1" and "V tr = vl"
  obtains tr1 where "validSystemTrace tr1" and "TT tr1" and "O tr1 = O tr" and "V tr1 = vl1"
  using assms unfolding secureTT_def
  by blast

lemma secure_E:
  assumes "secure"
  and "validSystemTrace tr" and "TT tr" and "B vl vl1" and "V tr = vl"
  obtains tr1 where "validSystemTrace tr1" and "O tr1 = O tr" and "V tr1 = vl1"
  using assms unfolding secure_def
  by blast

end

subsubsection \<open>Incorporating static triggers into the bound\<close>

text \<open>By making transitions that fire the trigger emit a dedicated secret value (here \<^term>\<open>None\<close>),
the (non-firing of the) trigger can be incorporated into the bound.\<close>

locale BD_Security_TS_Triggerless = Orig: BD_Security_TS
begin

abbreviation "\<phi>' trn \<equiv> \<phi> trn \<or> T trn"

abbreviation "f' trn \<equiv> (if T trn then None else Some (f trn))"

abbreviation "T' trn \<equiv> False"

abbreviation "B' vl' vl1' \<equiv> B (these vl') (these vl1') \<and> never Option.is_none vl' \<and> never Option.is_none vl1'"

sublocale Prime?: BD_Security_TS where \<phi> = \<phi>' and f = f' and T = T' and B = B' .

lemma map_Some_these: "never Option.is_none xs \<Longrightarrow> map Some (these xs) = xs"
proof (induction xs)
  case (Cons x xs) then show ?case by (cases x) auto
qed auto

lemma V'_never_none_T[simp]: "Prime.V tr = vl \<Longrightarrow> never Option.is_none vl \<longleftrightarrow> never T tr"
proof (induction tr arbitrary: vl)
  case (Cons trn tr) then show ?case by (cases "\<phi>' trn") auto
qed auto

lemma V'_V: "never T tr \<longleftrightarrow> Prime.V tr = map Some (Orig.V tr)"
proof (induction tr)
  case (Cons trn tr) then show ?case by (cases "\<phi>' trn") auto
qed auto

lemma V_Some_never_T: "Prime.V tr = map Some vl \<Longrightarrow> never T tr"
proof (induction tr arbitrary: vl)
  case (Cons trn tr) then show ?case by (cases "\<phi>' trn") auto
qed auto

text \<open>In the modified setup, the notions of trigger-preserving and original BD Security coincide
due to the trigger being vacuously false.\<close>

lemma secureTT_iff_secure: "Prime.secureTT \<longleftrightarrow> Prime.secure"
  unfolding secureTT_def secure_def
  by (auto simp: list_all_iff)

text \<open>The modified property is equivalent to trigger-preserving BD Security in the original setup
\<^cite>\<open>\<open>Proposition 2\<close> in "cosmed-jar2018"\<close>.\<close>

lemma secureTT_iff_secure': "Orig.secureTT \<longleftrightarrow> Prime.secure"
proof
  assume secure: "Orig.secureTT"
  then show "Prime.secure"
  proof (unfold Prime.secure_def, intro allI impI, elim conjE)
    fix tr vl vl1
    assume tr: "Orig.validFrom istate tr" and V: "V tr = vl" and B: "B (these vl) (these vl1)"
       and vl: "never Option.is_none vl" and vl1: "never Option.is_none vl1"
    with secure obtain tr1 where "Orig.validFrom istate tr1" and "never T tr1"
                             and "Prime.O tr1 = Prime.O tr" and "Orig.V tr1 = these vl1"
      by (elim Orig.secureTT_E) (auto simp: V'_V)
    then show "\<exists>tr1. Orig.validFrom istate tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1" using vl1
      by (intro exI[of _ tr1]) (auto simp: V'_V map_Some_these iff: list_all_iff)
  qed
next
  assume secure': "Prime.secure"
  then show "Orig.secureTT"
  proof (unfold Orig.secureTT_def, intro allI impI, elim conjE)
    fix tr vl vl1
    assume "Orig.validFrom istate tr" and "never T tr" and "B vl vl1" and "Orig.V tr = vl"
    with secure' obtain tr1 where "Orig.validFrom istate tr1" and "Prime.O tr1 = Prime.O tr"
                              and V: "Prime.V tr1 = map Some vl1"
      by (elim Prime.secure_E) (auto iff: V'_V list_all_iff)
    moreover have "never T tr1" using V by (intro V_Some_never_T)
    ultimately show "\<exists>tr1. Orig.validFrom istate tr1 \<and> never T tr1 \<and> O tr1 = O tr \<and> Orig.V tr1 = vl1"
      by (intro exI[of _ tr1]) (auto simp: V'_V)
  qed
qed

text \<open>The modified property also strengthens the regular notion of BD Security in the original
setup \<^cite>\<open>\<open>Proposition 1\<close> in "cosmed-jar2018"\<close>.\<close>

lemma secure'_secure: "Prime.secure \<Longrightarrow> Orig.secure"
  using secureTT_iff_secure' Orig.secureTT_secure
  by simp

end

subsubsection \<open>Reflexive-transitive closure of declassification bounds\<close>

text \<open>Another property of trigger-preserving BD Security is that security w.r.t. an arbitrary bound
\<^term>\<open>B\<close> is equivalent to security w.r.t. its reflexive-transitive closure \<^term>\<open>B\<^sup>*\<^sup>*\<close>
\<^cite>\<open>\<open>Proposition 3\<close> in "cosmed-jar2018"\<close>.\<close>

locale Abstract_BD_Security_Transitive_Closure = Orig: Abstract_BD_Security
begin

sublocale Prime?: Abstract_BD_Security where B = "B\<^sup>*\<^sup>*" .

lemma secureTT_iff_secureTT': "Orig.secureTT \<longleftrightarrow> Prime.secureTT"
proof
  assume "Orig.secureTT"
  then show "Prime.secureTT"
  proof (unfold Prime.secureTT_def, intro allI impI, elim conjE)
    fix tr vl vl1
    assume tr: "validSystemTrace tr" and TT: "TT tr" and B: "B\<^sup>*\<^sup>* vl vl1" and V: "V tr = vl"
    from B show "\<exists>tr1. validSystemTrace tr1 \<and> TT tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1"
    proof (induction rule: rtranclp_induct)
      case base
      show "\<exists>tr1. validSystemTrace tr1 \<and> TT tr1 \<and> O tr1 = O tr \<and> V tr1 = vl"
        using tr TT V
        by (intro exI[where x = tr]) auto
    next
      case (step vl' vl1')
      then obtain tr1
        where tr1: "validSystemTrace tr1" "TT tr1" and O1: "O tr1 = O tr" and V1: "V tr1 = vl'"
        by blast
      show "\<exists>tr1. validSystemTrace tr1 \<and> TT tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1'"
        by (rule Orig.secureTT_E[OF \<open>Orig.secureTT\<close> tr1 \<open>B vl' vl1'\<close> V1]) (use O1 V in auto)
    qed
  qed
next
  assume "Prime.secureTT"
  then show "Orig.secureTT"
    unfolding Prime.secureTT_def Orig.secureTT_def
    by blast
qed

end

(*<*)
end
(*>*)
