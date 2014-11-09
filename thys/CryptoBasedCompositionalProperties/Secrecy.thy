(*
   Title: Theory  Secrecy.thy
   Author:    Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)

section {*Secrecy: Definitions and properties *}

theory Secrecy
imports Secrecy_types inout ListExtras
begin

-- "Encryption, decryption, signature creation and signature verification functions"
-- "For these functions we define only their signatures and general axioms,"
-- "because in order to reason effectively, we view them as abstract functions and"
-- "abstract from their implementation details" 
consts 
  Enc  :: "Keys \<Rightarrow> Expression list \<Rightarrow> Expression list"
  Decr :: "Keys \<Rightarrow> Expression list \<Rightarrow> Expression list"
  Sign :: "Keys \<Rightarrow> Expression list \<Rightarrow> Expression list"
  Ext   :: "Keys \<Rightarrow> Expression list \<Rightarrow> Expression list"

-- "Axioms on relations between encription and decription keys"
axiomatization
   EncrDecrKeys :: "Keys  \<Rightarrow> Keys \<Rightarrow> bool"
where
ExtSign: 
 "EncrDecrKeys K1 K2 \<longrightarrow> (Ext K1 (Sign K2 E)) = E"  and
DecrEnc:
 "EncrDecrKeys K1 K2 \<longrightarrow> (Decr K2 (Enc K1 E)) = E"

-- "Set of private keys of a component"
consts
 specKeys :: "specID \<Rightarrow> Keys set"
-- "Set of unguessable values used by a component"
consts 
 specSecrets :: "specID \<Rightarrow> Secrets set"

-- "Join set of private keys and unguessable values used by a component"
definition
  specKeysSecrets :: "specID \<Rightarrow> KS set"
where
 "specKeysSecrets C \<equiv>
  {y .  \<exists> x. y = (kKS x)  \<and> (x \<in> (specKeys C))} \<union>
  {z .  \<exists> s. z = (sKS s)  \<and> (s \<in> (specSecrets C))}"

-- "Predicate defining that a list of expression items does not contain"
-- "any private key  or unguessable value used by a component"
definition
  notSpecKeysSecretsExpr :: "specID \<Rightarrow>  Expression list \<Rightarrow> bool"
where
     "notSpecKeysSecretsExpr P e \<equiv>
     (\<forall> x. (kE x) mem e \<longrightarrow> (kKS x) \<notin> specKeysSecrets P) \<and>
     (\<forall> y. (sE y) mem e \<longrightarrow> (sKS y) \<notin> specKeysSecrets P)"

-- "If a component is a composite one, the set of its private keys" 
-- "is a union of the subcomponents' sets of the private keys"
definition
  correctCompositionKeys ::  "specID \<Rightarrow> bool"
where
  "correctCompositionKeys x \<equiv>
    subcomponents x \<noteq> {} \<longrightarrow> 
    specKeys x =  \<Union> (specKeys ` (subcomponents x))" 

-- "If a component is a composite one, the set of its unguessable values" 
-- "is a union of the subcomponents' sets of the unguessable values"
definition
  correctCompositionSecrets ::  "specID \<Rightarrow> bool"
where
  "correctCompositionSecrets x \<equiv>
    subcomponents x \<noteq> {} \<longrightarrow> 
    specSecrets x =  \<Union> (specSecrets ` (subcomponents x))" 

-- "If a component is a composite one, the set of its private keys and" 
-- "unguessable values is a union of the corresponding sets of its subcomponents"
definition
  correctCompositionKS ::  "specID \<Rightarrow> bool"
where
  "correctCompositionKS x \<equiv>
    subcomponents x \<noteq> {} \<longrightarrow> 
    specKeysSecrets x =  \<Union> (specKeysSecrets ` (subcomponents x))" 

-- "Predicate defining set of correctness properties of the component's"
-- "interface  and relations on its private keys and unguessable values"
definition
  correctComponentSecrecy  ::  "specID \<Rightarrow> bool"
where 
  "correctComponentSecrecy x \<equiv> 
    correctCompositionKS x \<and> 
    correctCompositionSecrets x \<and> 
    correctCompositionKeys x \<and> 
    correctCompositionLoc x \<and>
    correctCompositionIn x \<and>
    correctCompositionOut x \<and> 
    correctInOutLoc x"

-- "Predicate exprChannel I E defines whether the expression item E can be sent via the channel I"    
consts
 exprChannel :: "chanID \<Rightarrow> Expression \<Rightarrow> bool"

-- "Predicate eoutM sP M E defines whether the component sP may eventually"
-- "output an expression E if there exists a time interval t of" 
-- "an output channel which contains this expression E"
definition
  eout :: "specID  \<Rightarrow> Expression \<Rightarrow> bool"
where
 "eout sP E \<equiv> 
  \<exists> (ch :: chanID). ((ch \<in> (out sP)) \<and> (exprChannel ch E))"

-- "Predicate eout sP E defines whether the component sP may eventually"
-- "output an expression E via subset of channels M,"
-- "which is a subset of output channels of sP,"
-- "and if there exists a time interval t of" 
-- "an output channel which contains this expression E"
definition
  eoutM :: "specID  \<Rightarrow> chanID set \<Rightarrow> Expression \<Rightarrow> bool"
where
 "eoutM sP M E \<equiv> 
  \<exists> (ch :: chanID). ((ch \<in> (out sP)) \<and> (ch \<in> M) \<and> (exprChannel ch E))"

-- "Predicate ineM sP M E defines whether a component sP may eventually"
-- "get an expression E  if there exists a time interval t of" 
-- "an input stream  which contains this expression E"
definition
  ine :: "specID  \<Rightarrow> Expression \<Rightarrow> bool"
where
 "ine sP E \<equiv> 
  \<exists> (ch :: chanID). ((ch \<in> (ins sP)) \<and> (exprChannel ch E))"

-- "Predicate ine sP E defines whether a component sP may eventually"
-- "get an expression E via subset of channels M,"
-- "which is a subset of input channels of sP,"
-- "and if there exists a time interval t of" 
-- "an input stream  which contains this expression E"
definition
  ineM :: "specID  \<Rightarrow> chanID set \<Rightarrow> Expression \<Rightarrow> bool"
where
 "ineM sP M E \<equiv> 
  \<exists> (ch :: chanID). ((ch \<in> (ins sP)) \<and> (ch \<in> M) \<and> (exprChannel ch E))"

-- "This predicate defines whether an input channel ch of a component sP "
-- "is the only one input channel of this component "
-- "via which it may eventually output an expression E"
definition
  out_exprChannelSingle :: "specID  \<Rightarrow> chanID \<Rightarrow> Expression \<Rightarrow> bool"
where
 "out_exprChannelSingle sP ch E \<equiv> 
  (ch \<in> (out sP)) \<and>  
  (exprChannel ch E)  \<and>
  (\<forall> (x :: chanID) (t :: nat). ((x \<in> (out sP)) \<and> (x \<noteq> ch) \<longrightarrow> \<not> exprChannel x E))"

-- "This predicate  yields true if only the channels from the set chSet,"
-- "which is a subset of input channels of the  component sP,"
-- "may eventually output an expression E"
definition
 out_exprChannelSet :: "specID  \<Rightarrow> chanID set \<Rightarrow> Expression \<Rightarrow> bool"
where
 "out_exprChannelSet sP chSet E \<equiv> 
   ((\<forall> (x ::chanID). ((x \<in> chSet) \<longrightarrow> ((x \<in> (out sP)) \<and> (exprChannel x E))))
   \<and>
   (\<forall> (x :: chanID). ((x \<notin> chSet) \<and> (x \<in> (out sP)) \<longrightarrow> \<not> exprChannel x E)))"

-- "This redicate defines whether"
-- "an input channel ch of a component sP is the only one input channel"
-- "of this component via which it may eventually get an expression E"
definition
 ine_exprChannelSingle :: "specID  \<Rightarrow> chanID \<Rightarrow> Expression \<Rightarrow> bool"
where
 "ine_exprChannelSingle sP ch E \<equiv> 
  (ch \<in> (ins sP)) \<and>
  (exprChannel ch E)  \<and>
  (\<forall> (x :: chanID) (t :: nat). (( x \<in> (ins sP)) \<and> (x \<noteq> ch) \<longrightarrow> \<not> exprChannel x E))"

-- "This predicate yields true if the component sP may eventually"
-- "get an expression E only via the channels from the set chSet,"
-- "which is a subset of input channels of sP"
definition
 ine_exprChannelSet :: "specID  \<Rightarrow> chanID set \<Rightarrow> Expression \<Rightarrow> bool"
where
 "ine_exprChannelSet sP chSet E \<equiv> 
   ((\<forall> (x ::chanID). ((x \<in> chSet) \<longrightarrow> ((x \<in> (ins sP)) \<and> (exprChannel x E))))
   \<and>
   (\<forall> (x :: chanID). ((x \<notin> chSet) \<and> ( x \<in> (ins sP)) \<longrightarrow> \<not> exprChannel x E)))"

-- "If a list of expression items does not contain any private key"
-- "or unguessable value of a component P, then the first element" 
-- "of the list is neither a private key nor unguessable value of P"
lemma notSpecKeysSecretsExpr_L1:
assumes "notSpecKeysSecretsExpr P (a # l)"
shows    "notSpecKeysSecretsExpr P [a]"
using assms by (simp add: notSpecKeysSecretsExpr_def)

-- "If a list of expression items does not contain any private key"
-- "or unguessable value of a component P, then this list without its first" 
-- "element does not contain them too"
lemma notSpecKeysSecretsExpr_L2:
assumes "notSpecKeysSecretsExpr P (a # l)"
shows    "notSpecKeysSecretsExpr P l" 
using assms by (simp add: notSpecKeysSecretsExpr_def)

-- "If a channel belongs to the set of input channels of a component P"
-- "and does not belong to the set of local channels of the compositon of P and Q" 
-- "then it belongs to the set of input channels of this composition"
lemma correctCompositionIn_L1:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionIn PQ" 
       and "ch \<notin> loc PQ"
       and "ch \<in> ins P" 
shows    "ch \<in> ins PQ"
using assms by (simp add: correctCompositionIn_def)

-- "If a channel belongs to the set of input channels of the compositon of P and Q"
-- "then it belongs to the set of input channels either of P or of Q"
lemma correctCompositionIn_L2:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ" 
       and "ch \<in> ins PQ" 
shows    "(ch \<in> ins P) \<or> (ch \<in> ins Q)" 
using assms by (simp add: correctCompositionIn_def)

lemma ineM_L1:
assumes "ch \<in> M" 
       and "ch \<in> ins P"
       and "exprChannel ch E"
shows    "ineM P M E"
using assms by (simp add: ineM_def, blast)

lemma ineM_ine:
assumes "ineM P M E"
shows    "ine P E"
using assms by (simp add: ineM_def ine_def, blast)

lemma not_ine_ineM:
assumes "\<not> ine P E"
shows    "\<not> ineM P M E"
using assms by (simp add: ineM_def ine_def)

lemma eoutM_eout:
assumes "eoutM P M E"
shows    "eout P E"
using assms by (simp add: eoutM_def eout_def, blast)

lemma not_eout_eoutM:
assumes "\<not> eout P E"
shows    "\<not> eoutM P M E"
using assms by (simp add: eoutM_def eout_def)

lemma correctCompositionKeys_subcomp1:
assumes "correctCompositionKeys C"
        and "x \<in> subcomponents C" 
        and "xb \<in> specKeys C"
shows "\<exists> x \<in> subcomponents C. (xb \<in> specKeys x)"
using assms by (simp add: correctCompositionKeys_def, auto)

lemma correctCompositionSecrets_subcomp1:
assumes "correctCompositionSecrets C" 
        and "x \<in> subcomponents C"
        and "s \<in> specSecrets C"
shows  "\<exists> x \<in> subcomponents C. (s \<in> specSecrets x)"
using assms by (simp add: correctCompositionSecrets_def, auto)

lemma correctCompositionKeys_subcomp2:
assumes "correctCompositionKeys C"
       and "xb \<in> subcomponents C"
       and "xc \<in> specKeys xb"
shows "xc \<in> specKeys C"
using assms by (simp add: correctCompositionKeys_def, auto)

lemma correctCompositionSecrets_subcomp2:
assumes "correctCompositionSecrets C"
        and "xb \<in> subcomponents C"
        and "xc \<in> specSecrets xb"
shows     "xc \<in> specSecrets C"
using assms by (simp add: correctCompositionSecrets_def, auto)

lemma correctCompKS_Keys:
assumes "correctCompositionKS C"
shows    "correctCompositionKeys C"
proof (cases "subcomponents C = {}")
  assume "subcomponents C = {}"
  from this and assms show ?thesis
  by (simp add: correctCompositionKeys_def)
next
  assume "subcomponents C \<noteq> {}"
  from this and assms show ?thesis 
  by (simp add: correctCompositionKS_def 
                correctCompositionKeys_def
                specKeysSecrets_def, blast)
qed

lemma correctCompKS_Secrets:
assumes "correctCompositionKS C"
shows    "correctCompositionSecrets C"
proof (cases "subcomponents C = {}")
  assume "subcomponents C = {}"
  from this and assms show ?thesis
  by (simp add: correctCompositionSecrets_def)
next
  assume "subcomponents C \<noteq> {}"
  from this and assms show ?thesis 
  by (simp add: correctCompositionKS_def 
                correctCompositionSecrets_def
                specKeysSecrets_def, blast)
qed

lemma correctCompKS_KeysSecrets:
assumes "correctCompositionKeys C"
        and "correctCompositionSecrets C"
shows    "correctCompositionKS C"
proof (cases "subcomponents C = {}")
  assume "subcomponents C = {}"
  from this and assms show ?thesis
  by (simp add: correctCompositionKS_def)
next
  assume "subcomponents C \<noteq> {}"
  from this and assms show ?thesis 
  by (simp add: correctCompositionKS_def 
                correctCompositionKeys_def 
                correctCompositionSecrets_def
                specKeysSecrets_def, blast)
qed 

lemma correctCompositionKS_subcomp1:
assumes "correctCompositionKS C"
       and h1:"x \<in> subcomponents C"
       and "xa \<in> specKeys C"
shows    "\<exists> y \<in> subcomponents C. (xa \<in> specKeys y)"
proof (cases "subcomponents C = {}")
  assume "subcomponents C = {}"
  from this and h1 show ?thesis by simp 
next
  assume "subcomponents C \<noteq> {}"
  from this and assms show ?thesis 
  by (simp add: correctCompositionKS_def specKeysSecrets_def, blast) 
qed

lemma correctCompositionKS_subcomp2:
assumes "correctCompositionKS C"
        and h1:"x \<in> subcomponents C"
        and "xa \<in> specSecrets C"
shows    "\<exists> y \<in> subcomponents C. xa \<in> specSecrets y"
proof (cases "subcomponents C = {}")
  assume "subcomponents C = {}"
  from this and h1 show ?thesis by simp 
next
  assume "subcomponents C \<noteq> {}"
  from this and assms show ?thesis 
  by (simp add: correctCompositionKS_def specKeysSecrets_def, blast)
qed

lemma correctCompositionKS_subcomp3:
assumes "correctCompositionKS C"
       and "x \<in> subcomponents C"
       and "xa \<in> specKeys x"
shows    "xa \<in> specKeys C"
using assms 
by (simp add: correctCompositionKS_def specKeysSecrets_def, auto)

lemma correctCompositionKS_subcomp4:
assumes "correctCompositionKS C"
        and "x \<in> subcomponents C"
        and "xa \<in> specSecrets x" 
shows     "xa \<in> specSecrets C"
using assms 
by (simp add: correctCompositionKS_def specKeysSecrets_def, auto)

lemma correctCompositionKS_PQ:
assumes "subcomponents PQ = {P, Q}"
       and "correctCompositionKS PQ" 
       and "ks \<in> specKeysSecrets PQ"
shows    "ks \<in> specKeysSecrets P \<or> ks \<in> specKeysSecrets Q"
using assms by (simp add: correctCompositionKS_def)

lemma correctCompositionKS_neg1:
assumes "subcomponents PQ = {P, Q}"
       and "correctCompositionKS PQ" 
       and "ks \<notin> specKeysSecrets P"
       and "ks \<notin> specKeysSecrets Q"
shows    "ks \<notin> specKeysSecrets PQ"
using assms by (simp add: correctCompositionKS_def)

lemma correctCompositionKS_negP:
assumes "subcomponents PQ = {P, Q}"
        and "correctCompositionKS PQ" 
        and "ks \<notin> specKeysSecrets PQ" 
shows     "ks \<notin> specKeysSecrets P"
using assms by (simp add: correctCompositionKS_def)

lemma correctCompositionKS_negQ:
assumes "subcomponents PQ = {P, Q}"
        and "correctCompositionKS PQ" 
        and "ks \<notin> specKeysSecrets PQ" 
shows     "ks \<notin> specKeysSecrets Q"
using assms by (simp add: correctCompositionKS_def)

lemma out_exprChannelSingle_Set:
assumes "out_exprChannelSingle P ch E"
shows    "out_exprChannelSet P {ch} E"
using assms 
by (simp add: out_exprChannelSingle_def out_exprChannelSet_def)

lemma out_exprChannelSet_Single:
assumes "out_exprChannelSet P {ch} E"
shows    "out_exprChannelSingle P ch E"
using assms
by (simp add: out_exprChannelSingle_def out_exprChannelSet_def)

lemma ine_exprChannelSingle_Set:
assumes "ine_exprChannelSingle P ch E"
  shows "ine_exprChannelSet P {ch} E"
using assms 
by (simp add: ine_exprChannelSingle_def ine_exprChannelSet_def)

lemma ine_exprChannelSet_Single:
assumes "ine_exprChannelSet P {ch} E"
shows    "ine_exprChannelSingle P ch E"
using assms 
by (simp add: ine_exprChannelSingle_def ine_exprChannelSet_def)

lemma ine_ins_neg1:
assumes "\<not> ine P m" 
       and "exprChannel x m"
shows    "x \<notin> ins P"
using assms by (simp add: ine_def, auto)

theorem TBtheorem1a:
assumes "ine PQ E" 
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
shows "ine P E  \<or> ine Q E"
using assms 
by (simp add: ine_def correctCompositionIn_def, auto)

theorem TBtheorem1b:
assumes "ineM PQ M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ" 
shows    "ineM P M E \<or> ineM Q M E"
using assms by (simp add: ineM_def correctCompositionIn_def, auto)

theorem TBtheorem2a:
assumes "eout PQ E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
shows    "eout P E \<or> eout Q E"
using assms by (simp add: eout_def correctCompositionOut_def, auto)

theorem TBtheorem2b:
assumes "eoutM PQ M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
shows    "eoutM P M E \<or> eoutM Q M E"
using assms by (simp add: eoutM_def correctCompositionOut_def, auto)

lemma correctCompositionIn_prop1:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "x \<in> (ins PQ)"
shows   "(x \<in> (ins P)) \<or> (x \<in> (ins Q))" 
using assms by (simp add: correctCompositionIn_def)

lemma correctCompositionOut_prop1:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "x \<in> (out PQ)"
shows    "(x \<in> (out P)) \<or> (x \<in> (out Q))" 
using assms by (simp add: correctCompositionOut_def)

theorem TBtheorem3a:
assumes "\<not> (ine P E)"
       and "\<not> (ine Q E)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
shows    "\<not> (ine PQ E)"
using assms by (simp add: ine_def correctCompositionIn_def, auto )

theorem TBlemma3b:
assumes h1:"\<not> (ineM P M E)"
       and h2:"\<not> (ineM Q M E)"
       and subPQ:"subcomponents PQ = {P,Q}"
       and cCompI:"correctCompositionIn PQ"
       and chM:"ch \<in> M" 
       and chPQ:"ch \<in> ins PQ"
       and eCh:"exprChannel ch E"
shows "False"
proof (cases "ch \<in> ins P")
  assume a1:"ch \<in> ins P"
  from a1 and chM and eCh have "ineM P M E" by (simp add: ineM_L1)
  from this and h1 show ?thesis by simp
next
  assume a2:"ch \<notin> ins P" 
  from subPQ and cCompI and chPQ have "(ch \<in> ins P) \<or> (ch \<in> ins Q)"
    by (simp add: correctCompositionIn_L2)
  from this and a2 have "ch \<in> ins Q" by simp 
  from this and chM and eCh have "ineM Q M E" by (simp add: ineM_L1)
  from this and h2 show ?thesis by simp
qed

theorem TBtheorem3b:
assumes "\<not> (ineM P M E)"
       and "\<not> (ineM Q M E)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
shows    "\<not> (ineM PQ M E)"
using assms by (metis TBtheorem1b)    

theorem TBtheorem4a_empty:
assumes "(ine P E) \<or> (ine Q E)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "loc PQ = {}"
shows    "ine PQ E"
using assms by (simp add: ine_def correctCompositionIn_def, auto)

theorem TBtheorem4a_P:
assumes "ine P E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "\<exists> ch. (ch \<in> (ins P) \<and> exprChannel ch E \<and> ch \<notin> (loc PQ))"
shows    "ine PQ E"
using assms by (simp add: ine_def correctCompositionIn_def, auto) 

theorem TBtheorem4b_P:
assumes "ineM P M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "\<exists> ch. ((ch \<in> (ins Q)) \<and> (exprChannel ch E) \<and> 
                        (ch \<notin> (loc PQ)) \<and> (ch \<in> M))"
shows    "ineM PQ M E"
using assms by (simp add: ineM_def correctCompositionIn_def, auto) 

theorem TBtheorem4a_PQ:
assumes "(ine P E) \<or> (ine Q E)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "\<exists> ch. (((ch \<in> (ins P)) \<or> (ch \<in> (ins Q) )) \<and> 
                         (exprChannel ch E) \<and>  (ch \<notin> (loc PQ)))"
shows    "ine PQ E"
using assms by (simp add: ine_def correctCompositionIn_def, auto) 

theorem TBtheorem4b_PQ:
assumes "(ineM P M E) \<or> (ineM Q M E)" 
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "\<exists> ch. (((ch \<in> (ins P)) \<or> (ch \<in> (ins Q) )) \<and> 
                         (ch \<in> M) \<and> (exprChannel ch E) \<and>  (ch \<notin> (loc PQ)))"
shows     "ineM PQ M E"
using assms by (simp add: ineM_def correctCompositionIn_def, auto) 

theorem TBtheorem4a_notP1:
assumes "ine P E"
       and "\<not> ine Q E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ" 
       and "\<exists> ch. ((ine_exprChannelSingle P ch E) \<and> (ch \<in> (loc PQ)))"
shows    "\<not> ine PQ E"
using assms 
by (simp add: ine_def correctCompositionIn_def 
                     ine_exprChannelSingle_def, auto) 

theorem TBtheorem4b_notP1:
assumes "ineM P M E"
       and "\<not> ineM Q M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"  
       and "\<exists> ch. ((ine_exprChannelSingle P ch E) \<and> (ch \<in> M) 
                     \<and> (ch \<in> (loc PQ)))"
shows    "\<not> ineM PQ M E"
using assms
by (simp add: ineM_def correctCompositionIn_def 
                     ine_exprChannelSingle_def, auto) 

theorem TBtheorem4a_notP2:
assumes "\<not> ine Q E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ" 
       and "ine_exprChannelSet P ChSet E"
       and "\<forall> (x ::chanID). ((x \<in> ChSet) \<longrightarrow> (x \<in> (loc PQ)))" 
shows    "\<not> ine PQ E"
using assms 
by (simp add: ine_def correctCompositionIn_def 
                     ine_exprChannelSet_def, auto) 

theorem TBtheorem4b_notP2:
assumes "\<not> ineM Q M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "ine_exprChannelSet P ChSet E"
       and "\<forall> (x ::chanID). ((x \<in> ChSet) \<longrightarrow> (x \<in> (loc PQ)))"
shows    "\<not> ineM PQ M E"
using assms 
by (simp add: ineM_def correctCompositionIn_def 
                     ine_exprChannelSet_def, auto) 

theorem TBtheorem4a_notPQ:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "ine_exprChannelSet P ChSetP E"
       and "ine_exprChannelSet Q ChSetQ E"
       and "\<forall> (x ::chanID). ((x \<in> ChSetP) \<longrightarrow> (x \<in> (loc PQ)))"
       and "\<forall> (x ::chanID). ((x \<in> ChSetQ) \<longrightarrow> (x \<in> (loc PQ)))"
shows    "\<not> ine PQ E"
using assms 
by (simp add: ine_def correctCompositionIn_def 
                     ine_exprChannelSet_def, auto)

lemma ineM_Un1:
assumes "ineM P A E"
shows    "ineM P (A Un B) E"
using assms by (simp add: ineM_def, auto)

theorem TBtheorem4b_notPQ:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ" 
       and "ine_exprChannelSet P ChSetP E"
       and "ine_exprChannelSet Q ChSetQ E"
       and "\<forall> (x ::chanID). ((x \<in> ChSetP) \<longrightarrow> (x \<in> (loc PQ)))"
       and "\<forall> (x ::chanID). ((x \<in> ChSetQ) \<longrightarrow> (x \<in> (loc PQ)))"
shows    " \<not> ineM PQ M E"
using assms 
by (simp add: ineM_def correctCompositionIn_def 
                     ine_exprChannelSet_def, auto) 

lemma ine_nonempty_exprChannelSet:
assumes "ine_exprChannelSet P ChSet E"
       and "ChSet \<noteq> {}"
shows    "ine P E "
using assms by (simp add: ine_def ine_exprChannelSet_def, auto)

lemma ine_empty_exprChannelSet:
assumes "ine_exprChannelSet P ChSet E"
       and "ChSet = {}"
shows    "\<not> ine P E"
using assms by (simp add: ine_def ine_exprChannelSet_def)

theorem TBtheorem5a_empty:
assumes "(eout P E) \<or> (eout Q E)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "loc PQ = {}"
shows    "eout PQ E"
using assms by (simp add: eout_def correctCompositionOut_def, auto)

theorem TBtheorem45a_P:
assumes "eout P E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "\<exists> ch. ((ch \<in> (out P)) \<and> (exprChannel ch E) \<and> 
                        (ch \<notin> (loc PQ)))"
shows    "eout PQ E"
using assms by (simp add: eout_def correctCompositionOut_def, auto)

theorem TBtheore54b_P:
assumes "eoutM P M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ" 
       and "\<exists> ch. ((ch \<in> (out Q)) \<and> (exprChannel ch E) \<and> 
                        (ch \<notin> (loc PQ)) \<and> (ch \<in> M) )"
shows    "eoutM PQ M E"
using assms by (simp add: eoutM_def correctCompositionOut_def, auto)

theorem TBtheorem5a_PQ:
assumes "(eout P E) \<or> (eout Q E)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "\<exists> ch. (((ch \<in> (out P)) \<or> (ch \<in> (out Q) )) \<and> 
                        (exprChannel ch E) \<and>  (ch \<notin> (loc PQ)))"
shows    "eout PQ E"
using assms by (simp add: eout_def correctCompositionOut_def, auto)

theorem TBtheorem5b_PQ:
assumes "(eoutM P M E) \<or> (eoutM Q M E)" 
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "\<exists> ch. (((ch \<in> (out P)) \<or> (ch \<in> (out Q) )) \<and> (ch \<in> M) 
                      \<and> (exprChannel ch E) \<and>  (ch \<notin> (loc PQ)))"
shows    "eoutM PQ M E"
using assms by (simp add: eoutM_def correctCompositionOut_def, auto) 

theorem TBtheorem5a_notP1:
assumes "eout P E"
       and "\<not> eout Q E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "\<exists> ch. ((out_exprChannelSingle P ch E) \<and> (ch \<in> (loc PQ)))"
shows    "\<not> eout PQ E"
using assms 
by (simp add: eout_def correctCompositionOut_def 
                      out_exprChannelSingle_def, auto) 

theorem TBtheorem5b_notP1:
assumes "eoutM P M E"
       and "\<not> eoutM Q M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "\<exists> ch. ((out_exprChannelSingle P ch E) \<and> (ch \<in> M) 
                   \<and> (ch \<in> (loc PQ)))"
shows    "\<not> eoutM PQ M E"
using assms 
by (simp add: eoutM_def correctCompositionOut_def 
                     out_exprChannelSingle_def, auto) 

theorem TBtheorem5a_notP2:
assumes "\<not> eout Q E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ" 
       and "out_exprChannelSet P ChSet E"
       and "\<forall> (x ::chanID). ((x \<in> ChSet) \<longrightarrow> (x \<in> (loc PQ)))"
shows    "\<not> eout PQ E"
using assms
by (simp add: eout_def correctCompositionOut_def 
                     out_exprChannelSet_def, auto)

theorem TBtheorem5b_notP2:
assumes "\<not> eoutM Q M E"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "out_exprChannelSet P ChSet E"
       and "\<forall> (x ::chanID). ((x \<in> ChSet) \<longrightarrow> (x \<in> (loc PQ)))" 
shows    "\<not> eoutM PQ M E"
using assms
by (simp add: eoutM_def correctCompositionOut_def 
                     out_exprChannelSet_def, auto)

theorem TBtheorem5a_notPQ:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "out_exprChannelSet P ChSetP E"
       and "out_exprChannelSet Q ChSetQ E"
       and "\<forall> (x ::chanID). ((x \<in> ChSetP) \<longrightarrow> (x \<in> (loc PQ)))"
       and "\<forall> (x ::chanID). ((x \<in> ChSetQ) \<longrightarrow> (x \<in> (loc PQ)))"
shows    "\<not> eout PQ E"
using assms
by (simp add: eout_def correctCompositionOut_def 
                     out_exprChannelSet_def, auto) 

theorem TBtheorem5b_notPQ:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionOut PQ"
       and "out_exprChannelSet P ChSetP E"
       and "out_exprChannelSet Q ChSetQ E"
       and "M = ChSetP \<union> ChSetQ"
       and "\<forall> (x ::chanID). ((x \<in> ChSetP) \<longrightarrow> (x \<in> (loc PQ)))"
       and "\<forall> (x ::chanID). ((x \<in> ChSetQ) \<longrightarrow> (x \<in> (loc PQ)))"
shows    "\<not> eoutM PQ M E"
using assms 
by (simp add: eoutM_def correctCompositionOut_def 
                     out_exprChannelSet_def, auto) 

end 