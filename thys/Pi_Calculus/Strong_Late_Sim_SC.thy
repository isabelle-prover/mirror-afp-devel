(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Sim_SC
  imports Strong_Late_Sim
begin

(************** Zero **********************)

lemma nilSim[dest]:
  fixes a :: name
  and   b :: name
  and   x :: name
  and   P :: pi
  and   Q :: pi

  shows "\<zero> \<leadsto>[Rel] \<tau>.(P) \<Longrightarrow> False"
  and   "\<zero> \<leadsto>[Rel] a<x>.P \<Longrightarrow> False"
  and   "\<zero> \<leadsto>[Rel] a{b}.P \<Longrightarrow> False"
by(fastforce simp add: simulation_def intro: Tau Input Output)+

lemma nilSimRight:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  shows "P \<leadsto>[Rel] \<zero>"
by(auto simp add: simulation_def)

(************** Match *********************)

lemma matchIdLeft:
  fixes a   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "[a\<frown>a]P \<leadsto>[Rel] P"
using assms
by(force simp add: simulation_def dest: Match derivativeReflexive)

lemma matchIdRight:
  fixes P   :: pi
  and   a   :: name
  and   Rel :: "(pi \<times> pi) set"

  assumes IdRel: "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] [a\<frown>a]P"
using assms
by(fastforce simp add: simulation_def elim: matchCases intro: derivativeReflexive)

lemma matchNilLeft:
  fixes a :: name
  and   b :: name
  and   P :: pi

  assumes "a \<noteq> b"
  
  shows "\<zero> \<leadsto>[Rel] [a\<frown>b]P"
using assms
by(auto simp add: simulation_def)

(************** Mismatch *********************)

lemma mismatchIdLeft:
  fixes a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"
  and     "a \<noteq> b"

  shows "[a\<noteq>b]P \<leadsto>[Rel] P"
using assms
by(fastforce simp add: simulation_def intro: Mismatch dest: derivativeReflexive)

lemma mismatchIdRight:
  fixes P   :: pi
  and   a   :: name
  and   b   :: name
  and   Rel :: "(pi \<times> pi) set"

  assumes IdRel: "Id \<subseteq> Rel"
  and     aineqb: "a \<noteq> b"

  shows "P \<leadsto>[Rel] [a\<noteq>b]P"
using assms
by(fastforce simp add: simulation_def elim: mismatchCases intro: derivativeReflexive)

lemma mismatchNilLeft:
  fixes a :: name
  and   P :: pi
  
  shows "\<zero> \<leadsto>[Rel] [a\<noteq>a]P"
by(auto simp add: simulation_def)

(************** +-operator *****************)

lemma sumSym:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"
  
  shows "P \<oplus> Q \<leadsto>[Rel] Q \<oplus> P"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: Sum1 Sum2 derivativeReflexive)

lemma sumIdempLeft:
  fixes P :: pi
  and Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P \<oplus> P"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: derivativeReflexive)

lemma sumIdempRight:
  fixes P :: pi
  and Rel :: "(pi \<times> pi) set"

  assumes I: "Id \<subseteq> Rel"

  shows "P \<oplus> P \<leadsto>[Rel] P"
using assms
by(fastforce simp add: simulation_def intro: Sum1 derivativeReflexive)

lemma sumAssocLeft:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "(P \<oplus> Q) \<oplus> R \<leadsto>[Rel] P \<oplus> (Q \<oplus> R)"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: Sum1 Sum2 derivativeReflexive)

lemma sumAssocRight:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "P \<oplus> (Q \<oplus> R) \<leadsto>[Rel] (P \<oplus> Q) \<oplus> R"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: Sum1 Sum2 derivativeReflexive)

lemma sumZeroLeft:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "P \<oplus> \<zero> \<leadsto>[Rel] P"
using assms
by(fastforce simp add: simulation_def intro: Sum1 derivativeReflexive)

lemma sumZeroRight:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P \<oplus> \<zero>"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: derivativeReflexive)

lemma sumResLeft:
  fixes x   :: name
  and   P   :: pi
  and   Q   :: pi

  assumes Id: "Id \<subseteq> Rel"
  and     Eqvt: "eqvt Rel"

  shows "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<leadsto>[Rel] <\<nu>x>(P \<oplus> Q)"
using Eqvt
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y PQ)
  from `y \<sharp> (x, P, Q)` have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by(simp add: fresh_prod)+
  hence "y \<sharp> P \<oplus> Q" by simp
  with `<\<nu>x>(P \<oplus> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` `y \<noteq> x` show ?case
  proof(induct rule: resCasesB)
    case(cOpen a PQ)
    from `P \<oplus> Q \<longmapsto>a[x] \<prec> PQ` `y \<sharp> P` `y \<sharp> Q` have "y \<sharp> PQ" by(force dest: freshFreeDerivative)
    from `P \<oplus> Q \<longmapsto>a[x] \<prec> PQ` show ?case
    proof(induct rule: sumCases)
      case cSum1
      from `P \<longmapsto>a[x] \<prec> PQ` `a \<noteq> x` have "<\<nu>x>P \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Open)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Sum1)
      with `y \<sharp> PQ` have "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>y> \<prec> ([(y, x)] \<bullet> PQ)" 
        by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> PQ) ([(y, x)] \<bullet> PQ) (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    next
      case cSum2
      from `Q \<longmapsto>a[x] \<prec> PQ` `a \<noteq> x` have "<\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Open)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Sum2)
      with `y \<sharp> PQ` have "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>y> \<prec> ([(y, x)] \<bullet> PQ)" 
        by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> PQ) ([(y, x)] \<bullet> PQ) (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    qed
  next
    case(cRes PQ)
    from `P \<oplus> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` show ?case
    proof(induct rule: sumCases)
      case cSum1
      from `P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` `x \<sharp> a` `y \<noteq> x` have "<\<nu>x>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule_tac ResB) auto
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule Sum1)
      moreover from Id have "derivative (<\<nu>x>PQ) (<\<nu>x>PQ) a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    next
      case cSum2
      from `Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` `x \<sharp> a` `y \<noteq> x` have "<\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule_tac ResB) auto
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule Sum2)
      moreover from Id have "derivative (<\<nu>x>PQ) (<\<nu>x>PQ) a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PQ)
  from `<\<nu>x>(P \<oplus> Q) \<longmapsto>\<alpha> \<prec> PQ` show ?case
  proof(induct rule: resCasesF)
    case(cRes PQ)
    from `P \<oplus> Q \<longmapsto>\<alpha> \<prec> PQ` show ?case
    proof(induct rule: sumCases)
      case cSum1 
      from `P \<longmapsto>\<alpha> \<prec> PQ` `x \<sharp> \<alpha>` have "<\<nu>x>P \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule ResF)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule Sum1)
      with Id show ?case by blast
    next
      case cSum2
      from `Q \<longmapsto>\<alpha> \<prec> PQ` `x \<sharp> \<alpha>` have "<\<nu>x>Q \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule ResF)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule Sum2)
      with Id show ?case by blast
    qed
  qed
qed

lemma sumResRight:
  fixes x   :: name
  and   P   :: pi
  and   Q   :: pi

  assumes Id: "Id \<subseteq> Rel"
  and     Eqvt: "eqvt Rel"

  shows "<\<nu>x>(P \<oplus> Q) \<leadsto>[Rel] (<\<nu>x>P) \<oplus> (<\<nu>x>Q)"
using `eqvt Rel`
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y PQ)
  from `y \<sharp> (x, P, Q)` have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by(simp add: fresh_prod)+
  from `(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` show ?case
  proof(induct rule: sumCases)
    case cSum1
    from `<\<nu>x>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` show ?case using `y \<noteq> x` `y \<sharp> P`
    proof(induct rule: resCasesB)
      case(cOpen a P')
      from `P \<longmapsto>a[x] \<prec> P'` `y \<sharp> P` have "y \<sharp> P'" by(rule freshFreeDerivative)
      
      from `P \<longmapsto>a[x] \<prec> P'` have "P \<oplus> Q \<longmapsto>a[x] \<prec> P'" by(rule Sum1)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>x> \<prec> P'" using `a \<noteq> x` by(rule Open)
      with `y \<sharp> P'` have "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>y> \<prec> [(y, x)] \<bullet> P'" by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> P') ([(y, x)] \<bullet> P') (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cRes P')
      from `P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'` have "P \<oplus> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'" by(rule Sum1)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>P'" using `x \<sharp> a` `y \<noteq> x` by(rule_tac ResB) auto
      moreover from Id have "derivative (<\<nu>x>P') (<\<nu>x>P') a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    qed
  next
    case cSum2
    from `<\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` show ?case using `y \<noteq> x` `y \<sharp> Q`
    proof(induct rule: resCasesB)
      case(cOpen a Q')
      from `Q \<longmapsto>a[x] \<prec> Q'` `y \<sharp> Q` have "y \<sharp> Q'" by(rule freshFreeDerivative)
      
      from `Q \<longmapsto>a[x] \<prec> Q'` have "P \<oplus> Q \<longmapsto>a[x] \<prec> Q'" by(rule Sum2)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>x> \<prec> Q'" using `a \<noteq> x` by(rule Open)
      with `y \<sharp> Q'` have "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>y> \<prec> [(y, x)] \<bullet> Q'" by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> Q') ([(y, x)] \<bullet> Q') (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cRes Q')
      from `Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'` have "P \<oplus> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'" by(rule Sum2)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>Q'" using `x \<sharp> a` `y \<noteq> x` by(rule_tac ResB) auto
      moreover from Id have "derivative (<\<nu>x>Q') (<\<nu>x>Q') a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PQ)
  from `(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>\<alpha> \<prec> PQ` show ?case
  proof(induct rule: sumCases)
    case cSum1
    from `<\<nu>x>P \<longmapsto>\<alpha> \<prec> PQ` show ?case
    proof(induct rule: resCasesF)
      case(cRes P')
      from `P \<longmapsto>\<alpha> \<prec> P'` have "P \<oplus> Q \<longmapsto>\<alpha> \<prec> P'" by(rule Sum1)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>P'" using `x \<sharp> \<alpha>` by(rule ResF)
      with Id show ?case by blast
    qed
  next
    case cSum2
    from `<\<nu>x>Q \<longmapsto>\<alpha> \<prec> PQ` show ?case
    proof(induct rule: resCasesF)
      case(cRes Q')
      from `Q \<longmapsto>\<alpha> \<prec> Q'` have "P \<oplus> Q \<longmapsto>\<alpha> \<prec> Q'" by(rule Sum2)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>Q'" using `x \<sharp> \<alpha>` by(rule ResF)
      with Id show ?case by blast
    qed
  qed
qed

(************** |-operator *************)

lemma parZeroLeft:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes ParZero: "\<And>Q. (Q \<parallel> \<zero>, Q) \<in> Rel"

  shows "P \<parallel> \<zero> \<leadsto>[Rel] P"
proof -
  {
    fix P Q a x
    from ParZero have "derivative (P \<parallel> \<zero>) P a x Rel"
      by(case_tac a) (auto simp add: derivative_def)
  }
  thus ?thesis using assms
    by(fastforce simp add: simulation_def intro: Par1B Par1F)
qed

lemma parZeroRight:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes ParZero: "\<And>Q. (Q, Q \<parallel> \<zero>) \<in> Rel"

  shows "P \<leadsto>[Rel] P \<parallel> \<zero>"
proof -
  {
    fix P Q a x
    from ParZero have "derivative P (P \<parallel> \<zero>) a x Rel"
      by(case_tac a) (auto simp add: derivative_def)
  }
  thus ?thesis using assms
    by(fastforce simp add: simulation_def elim: parCasesF parCasesB)+
qed
  
lemma parSym:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  
  assumes Sym: "\<And>R S. (R \<parallel> S, S \<parallel> R) \<in> Rel"
  and     Res: "\<And>R S x. (R, S) \<in> Rel \<Longrightarrow> (<\<nu>x>R, <\<nu>x>S) \<in> Rel"
  
  shows "P \<parallel> Q \<leadsto>[Rel] Q \<parallel> P"
proof(induct rule: simCases)
  case(Bound a x QP)
  from `x \<sharp> (P \<parallel> Q)` have "x \<sharp> Q" and "x \<sharp> P" by simp+
  with `Q \<parallel> P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> QP` show ?case
  proof(induct rule: parCasesB)
    case(cPar1 Q')
    from `Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> Q'` have "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> Q'" using `x \<sharp> P` by(rule Par2B)
    moreover have "derivative (P \<parallel> Q')  (Q' \<parallel> P) a x Rel"
      by(cases a, auto simp add: derivative_def intro: Sym)
    ultimately show ?case by blast
  next
    case(cPar2 P')
    from `P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'` have "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P' \<parallel> Q" using `x \<sharp> Q` by(rule Par1B)
    moreover have "derivative (P' \<parallel> Q)  (Q \<parallel> P') a x Rel"
      by(cases a, auto simp add: derivative_def intro: Sym)
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> QP)
  from `Q \<parallel> P \<longmapsto> \<alpha> \<prec> QP` show ?case
  proof(induct rule: parCasesF[where C="()"])
    case(cPar1 Q')
    from `Q \<longmapsto> \<alpha> \<prec> Q'` have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P \<parallel> Q'" by(rule Par2F)
    moreover have "(P \<parallel> Q', Q' \<parallel> P) \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cPar2 P')
    from `P \<longmapsto> \<alpha> \<prec> P'` have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P' \<parallel> Q" by(rule Par1F)
    moreover have "(P' \<parallel> Q, Q \<parallel> P') \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cComm1 Q' P' a b x)
    from `P \<longmapsto>a[b] \<prec> P'` `Q \<longmapsto>a<x> \<prec> Q'`
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> (Q'[x::=b])" by(rule Comm2)
    moreover have "(P' \<parallel> Q'[x::=b], Q'[x::=b] \<parallel> P') \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cComm2 Q' P' a b x)
    from `P \<longmapsto>a<x> \<prec> P'` `Q \<longmapsto>a[b] \<prec> Q'`
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> (P'[x::=b]) \<parallel> Q'" by(rule Comm1)
    moreover have "(P'[x::=b] \<parallel> Q', Q' \<parallel> P'[x::=b]) \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cClose1 Q' P' a x y)
    from `P \<longmapsto> a<\<nu>y> \<prec> P'` `Q \<longmapsto> a<x> \<prec> Q'` `y \<sharp> Q`
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P' \<parallel> (Q'[x::=y]))" by(rule Close2)
    moreover have "(<\<nu>y>(P' \<parallel> Q'[x::=y]), <\<nu>y>(Q'[x::=y] \<parallel> P')) \<in> Rel" by(metis Res Sym)
    ultimately show ?case by blast
  next
    case(cClose2 Q' P' a x y)
    from `P \<longmapsto> a<x> \<prec> P'` `Q \<longmapsto> a<\<nu>y> \<prec> Q'` `y \<sharp> P`
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>((P'[x::=y]) \<parallel> Q')" by(rule Close1)
    moreover have "(<\<nu>y>(P'[x::=y] \<parallel> Q'), <\<nu>y>(Q' \<parallel> P'[x::=y])) \<in> Rel" by(metis Res Sym)
    ultimately show ?case by blast
  qed
qed

lemma parAssocLeft:
  fixes P    :: pi
  and   Q    :: pi
  and   R    :: pi
  and   Rel  :: "(pi \<times> pi) set"

  assumes Ass:       "\<And>S T U. ((S \<parallel> T) \<parallel> U, S \<parallel> (T \<parallel> U)) \<in> Rel"
  and     Res:       "\<And>S T x. (S, T) \<in> Rel \<Longrightarrow> (<\<nu>x>S, <\<nu>x>T) \<in> Rel"
  and     FreshExt:  "\<And>S T U x. x \<sharp> S \<Longrightarrow> (<\<nu>x>((S \<parallel> T) \<parallel> U), S \<parallel> <\<nu>x>(T \<parallel> U)) \<in> Rel"
  and     FreshExt': "\<And>S T U x. x \<sharp> U \<Longrightarrow> ((<\<nu>x>(S \<parallel> T)) \<parallel> U, <\<nu>x>(S \<parallel> (T \<parallel> U))) \<in> Rel"

  shows "(P \<parallel> Q) \<parallel> R \<leadsto>[Rel] P \<parallel> (Q \<parallel> R)"
proof(induct rule: simCases)
  case(Bound a x PQR)
  from `x \<sharp> (P \<parallel> Q) \<parallel> R` have "x \<sharp> P" and "x \<sharp> Q" and "x \<sharp> R" by simp+
  hence "x \<sharp> (Q \<parallel> R)" by simp
  with `P \<parallel> (Q \<parallel> R) \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> PQR` `x \<sharp> P` show ?case
  proof(induct rule: parCasesB)
    case(cPar1 P')
    from `P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'` have "P \<parallel> Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P' \<parallel> Q" using `x \<sharp> Q` by(rule Par1B)
    hence "(P \<parallel> Q) \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P' \<parallel> Q) \<parallel> R" using `x \<sharp> R` by(rule Par1B)
    moreover have "derivative ((P' \<parallel> Q) \<parallel> R) (P' \<parallel> (Q \<parallel> R)) a x Rel"
      by(cases a, auto intro: Ass simp add: derivative_def)
    ultimately show ?case by blast
  next
    case(cPar2 QR)
    from `Q \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> QR` `x \<sharp> Q` `x \<sharp> R` show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from `Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'` have "P \<parallel> Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> Q'" using `x \<sharp> P` by(rule Par2B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> Q') \<parallel> R" using `x \<sharp> R`by(rule Par1B)
      moreover have "derivative ((P \<parallel> Q') \<parallel> R) (P \<parallel> (Q' \<parallel> R)) a x Rel"
        by(cases a, auto intro: Ass simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from `R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> R'` have "(P \<parallel> Q) \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> Q) \<parallel> R'" using `x \<sharp> P` `x \<sharp> Q` 
        by(rule_tac Par2B) auto
      moreover have "derivative ((P \<parallel> Q) \<parallel> R') (P \<parallel> (Q \<parallel> R')) a x Rel"
        by(cases a, auto intro: Ass simp add: derivative_def)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PQR)
  from `P \<parallel> (Q \<parallel> R) \<longmapsto> \<alpha> \<prec> PQR` show ?case
  proof(induct rule: parCasesF[where C="Q"])
    case(cPar1 P')
    from `P \<longmapsto> \<alpha> \<prec> P'` have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P' \<parallel> Q" by(rule Par1F)
    hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<alpha> \<prec> (P' \<parallel> Q) \<parallel> R" by(rule Par1F)
    moreover from Ass have "((P' \<parallel> Q) \<parallel> R, P' \<parallel> (Q \<parallel> R)) \<in> Rel" by blast
    ultimately show ?case by blast
  next
    case(cPar2 QR)
    from `Q \<parallel> R \<longmapsto> \<alpha> \<prec> QR` show ?case
    proof(induct rule: parCasesF[where C="P"])
      case(cPar1 Q')
      from `Q \<longmapsto> \<alpha> \<prec> Q'` have "(P \<parallel> Q) \<longmapsto> \<alpha> \<prec> P \<parallel> Q'" by(rule Par2F)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<alpha> \<prec> (P \<parallel> Q') \<parallel> R" by(rule Par1F)
      moreover from Ass have "((P \<parallel> Q') \<parallel> R, P \<parallel> (Q' \<parallel> R)) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from `R \<longmapsto> \<alpha> \<prec> R'` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<alpha> \<prec> (P \<parallel> Q) \<parallel> R'" by(rule Par2F)
      moreover from Ass have "((P \<parallel> Q) \<parallel> R', P \<parallel> (Q \<parallel> R')) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cComm1 Q' R' a b x)
      from `Q \<longmapsto>a<x> \<prec> Q'` `x \<sharp> P` have "P \<parallel> Q \<longmapsto>a<x> \<prec> P \<parallel> Q'" by(rule Par2B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P \<parallel> Q')[x::=b] \<parallel> R'" using `R \<longmapsto>a[b] \<prec> R'` by(rule Comm1)
      with `x \<sharp> P` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P \<parallel> (Q'[x::=b])) \<parallel> R'" by(simp add: forget)
      moreover from Ass have "((P \<parallel> (Q'[x::=b])) \<parallel> R', P \<parallel> (Q'[x::=b] \<parallel> R')) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cComm2 Q' R' a b x)
      from `Q \<longmapsto>a[b] \<prec> Q'` have "P \<parallel> Q \<longmapsto>a[b] \<prec> P \<parallel> Q'" by(rule Par2F)
      with `x \<sharp> P` `x \<sharp> Q` `R \<longmapsto>a<x> \<prec> R'` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P \<parallel> Q') \<parallel> R'[x::=b]"
        by(force intro: Comm2)
      moreover from Ass have "((P \<parallel> Q') \<parallel> R'[x::=b], P \<parallel> (Q' \<parallel> R'[x::=b])) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cClose1 Q' R' a x y)
      from `Q \<longmapsto>a<x> \<prec> Q'` `x \<sharp> P` have "P \<parallel> Q \<longmapsto>a<x> \<prec> P \<parallel> Q'" by(rule Par2B)
      with `y \<sharp> P` `y \<sharp> Q` `x \<sharp> P` `R \<longmapsto>a<\<nu>y> \<prec> R'` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P \<parallel> Q')[x::=y] \<parallel> R')"
        by(rule_tac Close1) auto
      with `x \<sharp> P` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P \<parallel> (Q'[x::=y])) \<parallel> R')" by(simp add: forget)
      moreover from `y \<sharp> P` have "(<\<nu>y>((P \<parallel> Q'[x::=y]) \<parallel> R'), P \<parallel> <\<nu>y>(Q'[x::=y] \<parallel> R')) \<in> Rel"
        by(rule FreshExt)
      ultimately show ?case by blast
    next
      case(cClose2 Q' R' a x y)
      from `Q \<longmapsto>a<\<nu>y> \<prec> Q'` `y \<sharp> P` have "P \<parallel> Q \<longmapsto>a<\<nu>y> \<prec> P \<parallel> Q'" by(rule Par2B)
      hence Act: "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P \<parallel> Q') \<parallel> R'[x::=y])" using `R \<longmapsto>a<x> \<prec> R'` `y \<sharp> R` by(rule Close2)
      moreover from `y \<sharp> P` have "(<\<nu>y>((P \<parallel> Q') \<parallel> R'[x::=y]), P \<parallel> <\<nu>y>(Q' \<parallel> R'[x::=y])) \<in> Rel"
        by(rule FreshExt)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 P' QR a b x)
    from `Q \<parallel> R \<longmapsto> a[b] \<prec> QR` show ?case
    proof(induct rule: parCasesF[where C="()"])
      case(cPar1 Q')
      from `P \<longmapsto>a<x> \<prec> P'` `Q \<longmapsto>a[b] \<prec> Q'` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P'[x::=b] \<parallel> Q'" by(rule Comm1)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P'[x::=b] \<parallel> Q') \<parallel> R" by(rule Par1F)
      moreover from Ass have "((P'[x::=b] \<parallel> Q') \<parallel> R, P'[x::=b] \<parallel> (Q' \<parallel> R)) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from `P \<longmapsto>a<x> \<prec> P'` `x \<sharp> Q` have "P \<parallel> Q \<longmapsto> a<x> \<prec> P' \<parallel> Q" by(rule Par1B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P' \<parallel> Q)[x::=b] \<parallel> R'" using `R \<longmapsto> a[b] \<prec> R'` by(rule Comm1)
      with `x \<sharp> Q` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P'[x::=b] \<parallel> Q) \<parallel> R'" by(simp add: forget)
      moreover from Ass have "((P'[x::=b] \<parallel> Q) \<parallel> R', P'[x::=b] \<parallel> (Q \<parallel> R')) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cComm1 Q' R')
      from `a[b] = \<tau>` have False by simp thus ?case by simp
    next
      case(cComm2 Q' R')
      from `a[b] = \<tau>` have False by simp thus ?case by simp
    next
      case(cClose1 Q' R')
      from `a[b] = \<tau>` have False by simp thus ?case by simp
    next
      case(cClose2 Q' R')
      from `a[b] = \<tau>` have False by simp thus ?case by simp
    qed
  next
    case(cComm2 P' QR a b x)
    from `x \<sharp> Q \<parallel> R` have "x \<sharp> Q" and "x \<sharp> R" by simp+
    with `Q \<parallel> R \<longmapsto> a<x> \<prec> QR` show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from `P \<longmapsto>a[b] \<prec> P'` `Q \<longmapsto> a<x> \<prec> Q'` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> (Q'[x::=b])" by(rule Comm2)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P' \<parallel> Q'[x::=b]) \<parallel> R" by(rule Par1F)
      moreover from Ass have "((P' \<parallel> Q'[x::=b]) \<parallel> R, P' \<parallel> Q'[x::=b] \<parallel> R) \<in> Rel" by blast
      with `x \<sharp> R` have "((P' \<parallel> Q'[x::=b]) \<parallel> R, P' \<parallel> (Q' \<parallel> R)[x::=b]) \<in> Rel" by(force simp add: forget)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from `P \<longmapsto>a[b] \<prec> P'` have "P \<parallel> Q \<longmapsto> a[b] \<prec> P' \<parallel> Q" by(rule Par1F)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P' \<parallel> Q) \<parallel> (R'[x::=b])" using `R \<longmapsto>a<x> \<prec> R'` by (rule Comm2)
      moreover from Ass have "((P' \<parallel> Q) \<parallel> R'[x::=b], P' \<parallel> Q \<parallel> (R'[x::=b])) \<in> Rel" by blast
      hence "((P' \<parallel> Q) \<parallel> R'[x::=b], P' \<parallel> (Q \<parallel> R')[x::=b]) \<in> Rel" using `x \<sharp> Q` by(force simp add: forget)
      ultimately show ?case by blast
    qed
  next
    case(cClose1 P' QR a x y)
    from `x \<sharp> Q \<parallel> R` have "x \<sharp> Q" by simp
    from `y \<sharp> Q \<parallel> R` have "y \<sharp> Q" and "y \<sharp> R" by simp+
    from `Q \<parallel> R \<longmapsto> a<\<nu>y> \<prec> QR` `y \<sharp> Q` `y \<sharp> R` show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from `P \<longmapsto>a<x> \<prec> P'` `Q \<longmapsto> a<\<nu>y> \<prec> Q'` `y \<sharp> P` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P'[x::=y] \<parallel> Q')" by(rule Close1)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (<\<nu>y>(P'[x::=y] \<parallel> Q')) \<parallel> R" by(rule Par1F)
      moreover from `y \<sharp> R` have "((<\<nu>y>(P'[x::=y] \<parallel> Q')) \<parallel> R, <\<nu>y>(P'[x::=y] \<parallel> Q' \<parallel> R)) \<in> Rel"
        by(rule FreshExt')
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from `P \<longmapsto>a<x> \<prec> P'` `x \<sharp> Q` have "P \<parallel> Q \<longmapsto> a<x> \<prec> P' \<parallel> Q" by(rule Par1B)
      with `R \<longmapsto> a<\<nu>y> \<prec> R'` `y \<sharp> P` `y \<sharp> Q` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P' \<parallel> Q)[x::=y] \<parallel> R')"
        by(rule_tac Close1) auto
      with `x \<sharp> Q` have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P'[x::=y] \<parallel> Q) \<parallel> R')" by(simp add: forget)
      moreover have "(<\<nu>y>((P'[x::=y] \<parallel> Q) \<parallel> R'), <\<nu>y>(P'[x::=y] \<parallel> (Q \<parallel> R'))) \<in> Rel" by(metis Ass Res)
      ultimately show ?case by blast
    qed
  next
    case(cClose2 P' QR a x y)
    from `y \<sharp> Q \<parallel> R` have "y \<sharp> Q" and "y \<sharp> R" by simp+
    from `x \<sharp> Q \<parallel> R` have "x \<sharp> Q" and "x \<sharp> R" by simp+
    with `Q \<parallel> R \<longmapsto> a<x> \<prec> QR` show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from `P \<longmapsto>a<\<nu>y> \<prec> P'` `Q \<longmapsto>a<x> \<prec> Q'` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P' \<parallel> Q'[x::=y])" using `y \<sharp> Q`
        by(rule Close2)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (<\<nu>y>(P' \<parallel> Q'[x::=y])) \<parallel> R" by(rule Par1F)
      moreover from `y \<sharp> R` have "((<\<nu>y>(P' \<parallel> Q'[x::=y])) \<parallel> R, <\<nu>y>(P' \<parallel>  (Q'[x::=y] \<parallel> R))) \<in> Rel"
        by(rule FreshExt')
      with `x \<sharp> R` have "((<\<nu>y>(P' \<parallel> Q'[x::=y])) \<parallel> R, <\<nu>y>(P' \<parallel>  (Q' \<parallel> R)[x::=y])) \<in> Rel"
        by(simp add: forget)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from `P \<longmapsto>a<\<nu>y> \<prec> P'` `y \<sharp> Q` have "P \<parallel> Q \<longmapsto> a<\<nu>y> \<prec> P' \<parallel> Q" by(rule Par1B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P' \<parallel> Q) \<parallel> R'[x::=y])" using `R \<longmapsto> a<x> \<prec> R'` `y \<sharp> R` by(rule Close2)
      moreover have "((P' \<parallel> Q) \<parallel> R'[x::=y], P' \<parallel> (Q \<parallel> R'[x::=y])) \<in> Rel" by(rule Ass)
      hence "(<\<nu>y>((P' \<parallel> Q) \<parallel> R'[x::=y]), <\<nu>y>(P' \<parallel> (Q \<parallel> R'[x::=y]))) \<in> Rel" by(rule Res) 
      hence "(<\<nu>y>((P' \<parallel> Q) \<parallel> R'[x::=y]), <\<nu>y>(P' \<parallel> (Q \<parallel> R')[x::=y])) \<in> Rel" using `x \<sharp> Q`
        by(simp add: forget)
      ultimately show ?case by blast
    qed
  qed
qed

lemma substRes3:
  fixes a :: name
  and   P :: pi
  and   x :: name

  shows "(<\<nu>a>P)[x::=a] = <\<nu>x>([(x, a)] \<bullet> P)"
proof -
  have "a \<sharp> <\<nu>a>P" by(simp add: name_fresh_abs)
  hence "(<\<nu>a>P)[x::=a] = [(x, a)] \<bullet> <\<nu>a>P" by(rule injPermSubst[THEN sym])
  thus "(<\<nu>a>P)[x::=a] = <\<nu>x>([(x, a)] \<bullet> P)" by(simp add: name_calc)
qed

lemma scopeExtParLeft:
  fixes P   :: pi
  and   Q   :: pi
  and   a   :: name
  and   lst :: "name list"
  and   Rel :: "(pi \<times> pi) set"

  assumes "x \<sharp> P"
  and     Id:         "Id \<subseteq> Rel"
  and     EqvtRel:    "eqvt Rel"
  and     Res:        "\<And>R S y. y \<sharp> R \<Longrightarrow> (<\<nu>y>(R \<parallel> S), R \<parallel> <\<nu>y>S) \<in> Rel"
  and     ScopeExt:   "\<And>R S y z. y \<sharp> R \<Longrightarrow> (<\<nu>y><\<nu>z>(R \<parallel> S), <\<nu>z>(R \<parallel> <\<nu>y>S)) \<in> Rel"

  shows "<\<nu>x>(P \<parallel> Q) \<leadsto>[Rel] P \<parallel> <\<nu>x>Q"
using `eqvt Rel`
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y PxQ)
  from `y \<sharp> (x, P, Q)` have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by simp+
  hence "y \<sharp> P" and "y \<sharp> <\<nu>x>Q" by(simp add: abs_fresh)+
  with `P \<parallel> <\<nu>x>Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> PxQ` show ?case
  proof(induct rule: parCasesB)
    case(cPar1 P')
    from `P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'` `x \<sharp> P` `y \<noteq> x` have "x \<sharp> a" and "x \<sharp> P'"
      by(force intro: freshBoundDerivative)+

    from `P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'` `y \<sharp> Q` have "P \<parallel> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P' \<parallel> Q" by(rule Par1B)
    with `x \<sharp> a` `y \<noteq> x` have "<\<nu>x>(P \<parallel> Q) \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>(P' \<parallel> Q)" by(rule_tac ResB) auto
    moreover have "derivative (<\<nu>x>(P' \<parallel> Q)) (P' \<parallel> <\<nu>x>Q) a y Rel"
    proof(cases a, auto simp add: derivative_def)
      fix u

      show "((<\<nu>x>(P' \<parallel> Q))[y::=u],  P'[y::=u] \<parallel>  ((<\<nu>x>Q)[y::=u])) \<in> Rel"
      proof(cases "x=u")
        case True
        have "(<\<nu>x>(P' \<parallel> Q))[y::=x] = <\<nu>y>(([(y, x)] \<bullet> P') \<parallel> ([(y, x)] \<bullet> Q))"
          by(simp add: substRes3)
        moreover from `x \<sharp> P'` have "P'[y::=x] = [(y, x)] \<bullet> P'" by(rule injPermSubst[THEN sym])
        moreover have "(<\<nu>x>Q)[y::=x] = <\<nu>y>([(y, x)] \<bullet> Q)" by(rule substRes3)
        moreover from `x \<sharp> P'` `y \<noteq> x` have "y \<sharp> [(y, x)] \<bullet> P'" by(simp add: name_fresh_left name_calc)
        ultimately show ?thesis using `x = u`by(force intro: Res)
      next
        case False
        with `y \<noteq> x` have "(<\<nu>x>(P' \<parallel> Q))[y::=u] = <\<nu>x>(P'[y::=u] \<parallel> Q[y::=u])"
          by(simp add: fresh_prod name_fresh)
        moreover from `x \<noteq> u` `y \<noteq> x` have "(<\<nu>x>Q)[y::=u] = <\<nu>x>(Q[y::=u])"
          by(simp add: fresh_prod name_fresh)
        moreover from `x \<sharp> P'` `x \<noteq> u` have "x \<sharp> P'[y::=u]" by(simp add: fresh_fact1)
        ultimately show ?thesis by(force intro: Res)
      qed
    next
      from `x \<sharp> P'` show "(<\<nu>x>(P' \<parallel> Q), P' \<parallel> <\<nu>x>Q) \<in> Rel" by(rule Res)
    qed
    
    ultimately show ?case by blast
  next
    case(cPar2 xQ)
    from `<\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> xQ` `y \<noteq> x` `y \<sharp> Q` show ?case
    proof(induct rule: resCasesB)
      case(cOpen a Q')
      from `Q \<longmapsto>a[x] \<prec> Q'` `y \<sharp> Q` have yFreshQ': "y \<sharp> Q'" by(force intro: freshFreeDerivative)

      from `Q \<longmapsto> a[x] \<prec> Q'` have "P \<parallel> Q \<longmapsto> a[x] \<prec> P \<parallel> Q'" by(rule Par2F)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> a<\<nu>x> \<prec> P \<parallel> Q'" using `a \<noteq> x` by(rule Open)
      with `y \<sharp> P` `y \<sharp> Q'` have "<\<nu>x>(P \<parallel> Q) \<longmapsto> a<\<nu>y> \<prec> [(x, y)] \<bullet> (P \<parallel> Q')"
        by(subst alphaBoundResidual[where x'=x]) (auto simp add: fresh_left calc_atm)
      with `y \<sharp> P` `x \<sharp> P` have "<\<nu>x>(P \<parallel> Q) \<longmapsto> a<\<nu>y> \<prec> P \<parallel> ([(x, y)] \<bullet> Q')"
        by(simp add: name_fresh_fresh)

      moreover have "derivative (P \<parallel> ([(x, y)] \<bullet> Q')) (P \<parallel> ([(y, x)] \<bullet> Q')) (BoundOutputS a) y Rel" using Id
        by(auto simp add: derivative_def name_swap)
         
      ultimately show ?case by blast
    next
      case(cRes Q')

      from `Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> Q'` `y \<sharp> P` have "P \<parallel> Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> P \<parallel> Q'" by(rule Par2B)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>(P \<parallel> Q')" using `x \<sharp> a` `y \<noteq> x`
        by(rule_tac ResB) auto
      moreover have "derivative (<\<nu>x>(P \<parallel> Q')) (P \<parallel> <\<nu>x>Q') a y Rel"
      proof(cases a, auto simp add: derivative_def)
        fix u
        show "((<\<nu>x>(P \<parallel> Q'))[y::=u],  P[y::=u] \<parallel>  (<\<nu>x>Q')[y::=u]) \<in> Rel"
        proof(cases "x=u")
          case True
          from `x \<sharp> P` `y \<sharp> P` have "(<\<nu>x>(P \<parallel> Q'))[y::=x] = <\<nu>y>(P \<parallel> ([(y, x)] \<bullet> Q'))"
            by(simp add: substRes3 perm_fresh_fresh)
          moreover from `y \<sharp> P` have "P[y::=x] = P" by(simp add: forget)
          moreover have "(<\<nu>x>Q')[y::=x] = <\<nu>y>([(y, x)] \<bullet> Q')" by(rule substRes3)
          ultimately show ?thesis using `x=u` `y \<sharp> P` by(force intro: Res)
        next
          case False
          with `y \<noteq> x` have "(<\<nu>x>(P \<parallel> Q'))[y::=u] = <\<nu>x>((P \<parallel> Q')[y::=u])"
            by(simp add: fresh_prod name_fresh)
          moreover from `y \<noteq> x` `x \<noteq> u` have "(<\<nu>x>Q')[y::=u] = <\<nu>x>(Q'[y::=u])"
            by(simp add: fresh_prod name_fresh)
          moreover from `x \<sharp> P` `x \<noteq> u` have "x \<sharp> P[y::=u]" by(force simp add: fresh_fact1)
          ultimately show ?thesis by(force intro: Res)
        qed
      next
        from `x \<sharp> P` show "(<\<nu>x>(P \<parallel> Q'), P \<parallel> <\<nu>x>Q') \<in> Rel" by(rule Res)
      qed
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PxQ)
  from `P \<parallel> <\<nu>x>Q \<longmapsto>\<alpha> \<prec> PxQ` show ?case
  proof(induct rule: parCasesF[where C="x"])
    case(cPar1 P')
    from `P \<longmapsto> \<alpha> \<prec> P'` `x \<sharp> P`have "x \<sharp> \<alpha>" and "x \<sharp> P'" by(force intro: freshFreeDerivative)+
    from `P \<longmapsto> \<alpha> \<prec> P'` have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P' \<parallel> Q" by(rule Par1F)
    hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<alpha> \<prec> <\<nu>x>(P' \<parallel> Q)" using `x \<sharp> \<alpha>` by(rule ResF)
    moreover from `x \<sharp> P'` have "(<\<nu>x>(P' \<parallel> Q), P' \<parallel> <\<nu>x>Q) \<in> Rel" by(rule Res)
    ultimately show ?case by blast
  next
    case(cPar2 Q')
    from `<\<nu>x>Q \<longmapsto> \<alpha> \<prec> Q'` show ?case
    proof(induct rule: resCasesF)
      case(cRes Q')
      from `Q \<longmapsto> \<alpha> \<prec> Q'` have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P \<parallel> Q'" by(rule Par2F)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>(P \<parallel> Q')" using `x \<sharp> \<alpha>`  by(rule ResF)
      moreover from `x \<sharp> P` have "(<\<nu>x>(P \<parallel> Q'), P \<parallel> <\<nu>x>Q') \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 P' xQ a b y)
    from `y \<sharp> x` have "y \<noteq> x" by simp
    from `P \<longmapsto> a<y> \<prec> P'` `x \<sharp> P` `y \<noteq> x` have "x \<sharp> P'" by(force intro: freshBoundDerivative)
    from `<\<nu>x>Q \<longmapsto>a[b] \<prec> xQ` show ?case
    proof(induct rule: resCasesF)
      case(cRes Q')
      from `x \<sharp> a[b]` have "x \<noteq> b" by simp
      from `P \<longmapsto> a<y> \<prec> P'` `Q \<longmapsto> a[b] \<prec> Q'` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P'[y::=b] \<parallel> Q'" by(rule Comm1)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x>(P'[y::=b] \<parallel> Q')" by(rule_tac ResF) auto
      moreover from `x \<sharp> P'` `x \<noteq> b` have "x \<sharp> P'[y::=b]" by(force intro: fresh_fact1)
      hence "(<\<nu>x>(P'[y::=b] \<parallel> Q'), P'[y::=b] \<parallel> <\<nu>x>Q') \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    qed
  next
    case(cComm2 P' xQ a b y)
    from `y \<sharp> x` `y \<sharp> <\<nu>x>Q` have "y \<noteq> x" and "y \<sharp> Q" by(simp add: abs_fresh)+ 
    with `<\<nu>x>Q \<longmapsto>a<y> \<prec> xQ` show ?case
    proof(induct rule: resCasesB)
      case(cOpen b Q')
      from `InputS a = BoundOutputS b` have False by simp
      thus ?case by simp
    next
      case(cRes Q')
      from `P \<longmapsto>a[b] \<prec> P'` `Q \<longmapsto>a<y> \<prec> Q'` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> Q'[y::=b]" by(rule Comm2)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> Q'[y::=b])" by(rule_tac ResF) auto
      moreover from `P \<longmapsto>a[b] \<prec> P'` `x \<sharp> P` have "x \<sharp> P'" and "x \<noteq> b" by(force dest: freshFreeDerivative)+
      from `x \<sharp> P'` have "(<\<nu>x>(P' \<parallel> Q'[y::=b]), P' \<parallel> <\<nu>x>(Q'[y::=b])) \<in> Rel" by(rule Res)
      with `y \<noteq> x` `x \<noteq> b` have "(<\<nu>x>(P' \<parallel> Q'[y::=b]), P' \<parallel> (<\<nu>x>Q')[y::=b]) \<in> Rel" by simp
      ultimately show ?case by blast
    qed
  next
    case(cClose1 P' Q' a y z)
    from `y \<sharp> x` have "y \<noteq> x" by simp
    from `z \<sharp> x` `z \<sharp> <\<nu>x>Q` have "z \<sharp> Q" and "z \<noteq> x" by(simp add: abs_fresh)+
    from `P \<longmapsto>a<y> \<prec> P'` `z \<sharp> P` have "z \<noteq> a" by(force dest: freshBoundDerivative)
    from `<\<nu>x>Q \<longmapsto> a<\<nu>z> \<prec> Q'` `z \<noteq> x` `z \<sharp> Q` show ?case
    proof(induct rule: resCasesB)
      case(cOpen b Q')
      from `BoundOutputS a = BoundOutputS b` have "a = b" by simp
      with `Q \<longmapsto> b[x] \<prec> Q'` have "([(z, x)] \<bullet> Q) \<longmapsto> [(z, x)] \<bullet> (a[x] \<prec> Q')"
        by(rule_tac transitions.eqvt) simp
      with `b \<noteq> x` `z \<noteq> a` `a = b` `z \<noteq> x` have "([(z, x)] \<bullet> Q) \<longmapsto> a[z] \<prec> ([(z, x)] \<bullet> Q')"
        by(simp add: name_calc eqvts)
      with `P \<longmapsto>a<y> \<prec> P'` have "P \<parallel> ([(z, x)] \<bullet> Q) \<longmapsto>\<tau> \<prec> P'[y::=z] \<parallel> ([(z, x)] \<bullet> Q')"
        by(rule Comm1)
      hence "<\<nu>z>(P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto> \<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> ([(z, x)] \<bullet> Q'))"
        by(rule_tac ResF) auto
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> ([(z, x)] \<bullet> Q'))" using `z \<sharp> P` `z \<sharp> Q` `x \<sharp> P`
        by(subst alphaRes[where c=z]) auto
      with Id show ?case by force
    next
      case(cRes Q')
      from `P \<longmapsto>a<y> \<prec> P'` `Q \<longmapsto>a<\<nu>z> \<prec> Q'` `z \<sharp> P` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> Q')"
        by(rule Close1)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x><\<nu>z>(P'[y::=z] \<parallel> Q')" by(rule_tac ResF) auto
      moreover from `P \<longmapsto>a<y> \<prec> P'` `y \<noteq> x` `x \<sharp> P` have "x \<sharp> P'"
        by(force dest: freshBoundDerivative)
      with `z \<noteq> x` have "x \<sharp> P'[y::=z]" by(simp add: fresh_fact1)
      hence "(<\<nu>x><\<nu>z>(P'[y::=z] \<parallel> Q'), <\<nu>z>(P'[y::=z] \<parallel> <\<nu>x>Q')) \<in> Rel"
        by(rule ScopeExt)
      ultimately show ?case by blast
    qed
  next
    case(cClose2 P' xQ a y z)
    from `z \<sharp> x` `z \<sharp> <\<nu>x>Q` have "z \<noteq> x" and "z \<sharp> Q" by(auto simp add: abs_fresh)
    from `y \<sharp> x` `y \<sharp> <\<nu>x>Q` have "y \<noteq> x" and "y \<sharp> Q" by(auto simp add: abs_fresh)
    with `<\<nu>x>Q \<longmapsto>a<y> \<prec> xQ` show ?case
    proof(induct rule: resCasesB)
      case(cOpen b Q')
      from `InputS a = BoundOutputS b` have False by simp
      thus ?case by simp
    next
      case(cRes Q')
      from `P \<longmapsto>a<\<nu>z> \<prec> P'` `Q \<longmapsto>a<y> \<prec> Q'` `z \<sharp> Q` have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>z>(P' \<parallel> Q'[y::=z])"
        by(rule Close2)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x><\<nu>z>(P' \<parallel> (Q'[y::=z]))"
        by(rule_tac ResF) auto
      moreover from `P \<longmapsto>a<\<nu>z> \<prec> P'` `x \<sharp> P` `z \<noteq> x` have "x \<sharp> P'" by(force dest: freshBoundDerivative)
      hence "(<\<nu>x><\<nu>z>(P' \<parallel> (Q'[y::=z])), <\<nu>z>(P' \<parallel> (<\<nu>x>(Q'[y::=z])))) \<in> Rel"
        by(rule ScopeExt)
      with `z \<noteq> x` `y \<noteq> x` have "(<\<nu>x><\<nu>z>(P' \<parallel> (Q'[y::=z])), <\<nu>z>(P' \<parallel> (<\<nu>x>Q')[y::=z])) \<in> Rel"
        by simp
      ultimately show ?case by blast
    qed
  qed
qed

lemma scopeExtParRight:
  fixes P   :: pi
  and   Q   :: pi
  and   a   :: name
  and   Rel :: "(pi \<times> pi) set"

  assumes "x \<sharp> P"
  and     Id:         "Id \<subseteq> Rel"
  and     "eqvt Rel"
  and     Res:        "\<And>R S y. y \<sharp> R \<Longrightarrow> (R \<parallel> <\<nu>y>S, <\<nu>y>(R \<parallel> S)) \<in> Rel"
  and     ScopeExt:   "\<And>R S y z. y \<sharp> R \<Longrightarrow> (<\<nu>z>(R \<parallel> <\<nu>y>S), <\<nu>y><\<nu>z>(R \<parallel> S)) \<in> Rel"

  shows "P \<parallel> <\<nu>x>Q \<leadsto>[Rel] <\<nu>x>(P \<parallel> Q)"
using `eqvt Rel`
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y xPQ)
  from `y \<sharp> (x, P, Q)` have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by simp+
  hence "y \<noteq> x" and "y \<sharp> P \<parallel> Q" by(auto simp add: abs_fresh)
  with `<\<nu>x>(P \<parallel> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> xPQ` show ?case
  proof(induct rule: resCasesB)
    case(cOpen a PQ)
    from `P \<parallel> Q \<longmapsto>a[x] \<prec> PQ` show ?case
    proof(induct rule: parCasesF[where C="()"])
      case(cPar1 P')
      from `P \<longmapsto>a[x] \<prec> P'` `x \<sharp> P` have "x \<noteq> x" by(force dest: freshFreeDerivative)
      thus ?case by simp
    next
      case(cPar2 Q')
      from `Q \<longmapsto>a[x] \<prec> Q'` `y \<sharp> Q` have "y \<sharp> Q'" by(force dest: freshFreeDerivative)
      from `Q \<longmapsto>a[x] \<prec> Q'` `a \<noteq> x` have "<\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> Q'" by(rule Open)
      hence "P \<parallel> <\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> P \<parallel> Q'" using `x \<sharp> P` by(rule Par2B)
      with `y \<sharp> P` `y \<sharp> Q'` `x \<sharp> P` have "P \<parallel> <\<nu>x>Q \<longmapsto>a<\<nu>y> \<prec> ([(y, x)] \<bullet> (P \<parallel> Q'))"
        by(subst alphaBoundResidual[where x'=x]) (auto simp add: fresh_left calc_atm)
      moreover with Id have "derivative ([(y, x)] \<bullet> (P \<parallel>  Q'))
                                        ([(y, x)] \<bullet> (P \<parallel> Q')) (BoundOutputS a) y Rel"
        by(auto simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cComm1 P' Q' b c y)
      from `a[x] = \<tau>` show ?case by simp
    next
      case(cComm2 P' Q' b c y)
      from `a[x] = \<tau>` show ?case by simp
    next
      case(cClose1 P' Q' b y z)
      from `a[x] = \<tau>` show ?case by simp
    next
      case(cClose2 P' Q' b y z)
      from `a[x] = \<tau>` show ?case by simp
    qed
  next
    case(cRes PQ)
    from `P \<parallel> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ` `y \<sharp> P` `y \<sharp> Q`
    show ?case
    proof(induct rule: parCasesB)
      case(cPar1 P')
      from `y \<noteq> x` `x \<sharp> P` `P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'` have "x \<sharp> P'" by(force dest: freshBoundDerivative)
      
      from `P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'` `y \<sharp> Q` have "P \<parallel> <\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P' \<parallel> <\<nu>x>Q"
        by(rule_tac Par1B) (auto simp add: abs_fresh)
      moreover have "derivative (P' \<parallel> <\<nu>x>Q) (<\<nu>x>(P' \<parallel> Q)) a y Rel"
      proof(cases a, auto simp add: derivative_def)
        fix u::name
        obtain z::name where "z \<sharp> Q" and "y \<noteq> z" and "z \<noteq> u" and "z \<sharp> P" and "z \<sharp> P'"
          by(generate_fresh "name") auto
        thus "(P'[y::=u] \<parallel> (<\<nu>x>Q)[y::=u], (<\<nu>x>(P' \<parallel> Q))[y::=u]) \<in> Rel" using `x \<sharp> P'`
          by(subst alphaRes[where c=z and a=x], auto)
            (subst alphaRes[where c=z and a=x], auto intro: Res simp add: fresh_fact1)
      next
        from `x \<sharp> P'` show "(P' \<parallel> <\<nu>x>Q, <\<nu>x>(P' \<parallel> Q)) \<in> Rel"
          by(rule Res)
      qed

      ultimately show ?case by blast
    next
      case(cPar2 Q')
      from `Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'` have "<\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>Q'" using `x \<sharp> a` `y \<noteq> x` 
        by(rule_tac ResB) auto
      hence "P \<parallel> <\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P \<parallel> <\<nu>x>Q'" using `y \<sharp> P` by(rule Par2B)
      
      moreover have "derivative (P \<parallel> <\<nu>x>Q') (<\<nu>x>(P \<parallel> Q')) a y Rel"
      proof(cases a, auto simp add: derivative_def)
        fix u::name
        obtain z::name where "z \<sharp> Q" and "z \<noteq> y" and "z \<noteq> u" and "z \<sharp> P" and "z \<sharp> Q'"
          by(generate_fresh "name") auto
        
        thus  "(P[y::=u] \<parallel> (<\<nu>x>Q')[y::=u], (<\<nu>x>(P \<parallel> Q'))[y::=u]) \<in> Rel" using `x \<sharp> P`
          by(subst alphaRes[where a=x and c=z], auto)
            (subst alphaRes[where a=x and c=z], auto intro: Res simp add: fresh_fact1)
      next
        from `x \<sharp> P` show "(P \<parallel> <\<nu>x>Q', <\<nu>x>(P \<parallel> Q')) \<in> Rel"
          by(rule Res)
      qed
      
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> xPQ)
  from `<\<nu>x>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> xPQ` show ?case
  proof(induct rule: resCasesF)
    case(cRes PQ)
    from `P \<parallel> Q \<longmapsto>\<alpha> \<prec> PQ` show ?case
    proof(induct rule: parCasesF[where C="x"])
      case(cPar1 P')
      from `P \<longmapsto>\<alpha> \<prec> P'` have "P \<parallel> <\<nu>x>Q \<longmapsto>\<alpha> \<prec> P' \<parallel> <\<nu>x>Q" by(rule Par1F)
      moreover from `P \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> P` have "x \<sharp> P'" by(rule freshFreeDerivative)
      hence "(P' \<parallel> <\<nu>x>Q, <\<nu>x>(P' \<parallel> Q)) \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    next
      case(cPar2 Q')
      from `Q \<longmapsto>\<alpha> \<prec> Q'` `x \<sharp> \<alpha>` have "<\<nu>x>Q \<longmapsto>\<alpha> \<prec> <\<nu>x>Q'" by(rule ResF)
      hence "P \<parallel> <\<nu>x>Q \<longmapsto>\<alpha> \<prec> P \<parallel> <\<nu>x>Q'" by(rule Par2F)
      moreover from `x \<sharp> P` have "(P \<parallel> <\<nu>x>Q', <\<nu>x>(P \<parallel> Q')) \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    next
      case(cComm1 P' Q' a b y)
      from `x \<sharp> P` `y \<sharp> x` `P \<longmapsto>a<y> \<prec> P'` have "x \<noteq> a" and "x \<sharp> P'" by(force dest: freshBoundDerivative)+
      show ?case
      proof(cases "b=x")
        case True
        from `Q \<longmapsto>a[b] \<prec> Q'` `x \<noteq> a` `b = x` have "<\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> Q'" by(rule_tac Open) auto
        with `P \<longmapsto>a<y> \<prec> P'` have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> <\<nu>x>(P'[y::=x] \<parallel> Q')" using `x \<sharp> P` by(rule Close1)
        moreover from Id have "(<\<nu>x>(P'[y::=b] \<parallel> Q'), <\<nu>x>(P'[y::=b] \<parallel> Q')) \<in> Rel" by blast
        ultimately show ?thesis using `b=x` by blast
      next
        case False
        from `Q \<longmapsto>a[b] \<prec> Q'` `x \<noteq> a` `b \<noteq> x` have "<\<nu>x>Q \<longmapsto>a[b] \<prec> <\<nu>x>Q'" by(rule_tac ResF) auto
        with `P \<longmapsto>a<y> \<prec> P'` have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> (P'[y::=b] \<parallel> <\<nu>x>Q')" by(rule Comm1)
        moreover from `x \<sharp> P'` `b \<noteq> x` have "(P'[y::=b] \<parallel> <\<nu>x>Q', <\<nu>x>(P'[y::=b] \<parallel> Q')) \<in> Rel"
          by(force intro: Res simp add: fresh_fact1)
        ultimately show ?thesis by blast
      qed
    next
      case(cComm2 P' Q' a b y)
      from `P \<longmapsto>a[b] \<prec> P'` `x \<sharp> P` have "x \<noteq> a" and "x \<noteq> b" and "x \<sharp> P'" by(force dest: freshFreeDerivative)+
      from `Q \<longmapsto>a<y> \<prec> Q'` `y \<sharp> x` `x \<noteq> a` have "<\<nu>x>Q \<longmapsto>a<y> \<prec> <\<nu>x>Q'" by(rule_tac ResB) auto
      with `P \<longmapsto>a[b] \<prec> P'` have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> P' \<parallel> (<\<nu>x>Q')[y::=b]" by(rule Comm2)
      moreover from `x \<sharp> P'` have "(P' \<parallel> <\<nu>x>(Q'[y::=b]), <\<nu>x>(P' \<parallel> Q'[y::=b])) \<in> Rel" by(rule Res)
      ultimately show ?case using `y \<sharp> x` `x \<noteq> b` by force
    next
      case(cClose1 P' Q' a y z)
      from `P \<longmapsto>a<y> \<prec> P'` `x \<sharp> P` `y \<sharp> x` have "x \<noteq> a" and "x \<sharp> P'" by(force dest: freshBoundDerivative)+
      from `Q \<longmapsto>a<\<nu>z> \<prec> Q'` `z \<sharp> x` `x \<noteq> a` have "<\<nu>x>Q \<longmapsto>a<\<nu>z> \<prec> <\<nu>x>Q'" by(rule_tac ResB) auto
      with `P \<longmapsto>a<y> \<prec> P'` have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> <\<nu>x>Q')" using `z \<sharp> P` by(rule Close1)
      moreover from `x \<sharp> P'` `z \<sharp> x` have "(<\<nu>z>(P'[y::=z] \<parallel> <\<nu>x>Q'), <\<nu>x>(<\<nu>z>(P'[y::=z] \<parallel> Q'))) \<in> Rel" 
        by(rule_tac ScopeExt) (auto simp add: fresh_fact1)
      ultimately show ?case by blast
    next
      case(cClose2 P' Q' a y z)
      from `P \<longmapsto>a<\<nu>z> \<prec> P'` `x \<sharp> P` `z \<sharp> x` have "x \<noteq> a" and "x \<sharp> P'" by(force dest: freshBoundDerivative)+
      from `Q \<longmapsto>a<y> \<prec> Q'` `y \<sharp> x` `x \<noteq> a` have "<\<nu>x>Q \<longmapsto>a<y> \<prec> <\<nu>x>Q'" by(rule_tac ResB) auto
      with `P \<longmapsto>a<\<nu>z> \<prec> P'` have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> <\<nu>z>(P' \<parallel> (<\<nu>x>Q')[y::=z])" using `z \<sharp> Q`
        by(rule_tac Close2) (auto simp add: abs_fresh)
      moreover from `x \<sharp> P'` have "(<\<nu>z>(P' \<parallel> <\<nu>x>(Q'[y::=z])), <\<nu>x><\<nu>z>(P' \<parallel> Q'[y::=z])) \<in> Rel" by(rule ScopeExt)
      ultimately show ?case using `z \<sharp> x` `y \<sharp> x` by force
    qed
  qed
qed

lemma resNilRight:
  fixes x   :: name
  and   Rel :: "(pi \<times> pi) set"

  shows "\<zero> \<leadsto>[Rel] <\<nu>x>\<zero>"
by(fastforce simp add: simulation_def pi.inject alpha' elim: resCasesB' resCasesF)

lemma resComm:
  fixes a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes ResComm: "\<And>c d Q. (<\<nu>c><\<nu>d>Q, <\<nu>d><\<nu>c>Q) \<in> Rel"
  and     Id:      "Id \<subseteq> Rel"
  and     EqvtRel: "eqvt Rel"

  shows "<\<nu>a><\<nu>b>P \<leadsto>[Rel] <\<nu>b><\<nu>a>P"
proof(cases "a=b")
  assume "a=b"
  with Id show ?thesis by(force intro: Strong_Late_Sim.reflexive)
next
  assume aineqb: "a \<noteq> b"
  from EqvtRel show ?thesis
  proof(induct rule: simCasesCont[where C="(a, b, P)"])
    case(Bound c x baP)
    from `x \<sharp> (a, b, P)` have "x \<noteq> a" and "x \<noteq> b" and "x \<sharp> P" by simp+
    from `x \<sharp> P` have "x \<sharp> <\<nu>a>P" by(simp add: abs_fresh)
    with `<\<nu>b><\<nu>a>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> baP` `x \<noteq> b` show ?case
    proof(induct rule: resCasesB)
      case(cOpen c aP)
      from `<\<nu>a>P \<longmapsto>c[b] \<prec> aP`
      show ?case
      proof(induct rule: resCasesF)
        case(cRes P')
        from `a \<sharp> c[b]` have "a \<noteq> c" and "a \<noteq> b" by simp+
        from `x \<sharp> P` `P \<longmapsto>c[b] \<prec> P'` have "x \<noteq> c" and "x \<sharp> P'" by(force dest: freshFreeDerivative)+
        from `P \<longmapsto> c[b] \<prec> P'` have "([(x, b)] \<bullet> P) \<longmapsto> [(x, b)] \<bullet> (c[b] \<prec> P')" by(rule transitions.eqvt)
        with `x \<noteq> c` `c \<noteq> b` `x \<noteq> b` have "([(x, b)] \<bullet> P) \<longmapsto> c[x] \<prec> [(x, b)] \<bullet> P'" by(simp add: eqvts calc_atm)
        hence "<\<nu>x>([(x, b)] \<bullet> P) \<longmapsto> c<\<nu>x> \<prec> [(x, b)] \<bullet> P'" using `x \<noteq> c` by(rule_tac Open) auto
        with `x \<sharp> P` have "<\<nu>b>P \<longmapsto> c<\<nu>x> \<prec> [(x, b)] \<bullet> P'" by(simp add: alphaRes)
        hence "<\<nu>a><\<nu>b>P \<longmapsto> c<\<nu>x> \<prec> <\<nu>a>([(x, b)] \<bullet> P')" using `a \<noteq> c` `x \<noteq> a`
          by(rule_tac ResB) auto
        moreover from Id have "derivative (<\<nu>a>([(x, b)] \<bullet> P')) (<\<nu>a>([(x, b)] \<bullet> P')) (BoundOutputS c) x Rel"
          by(force simp add: derivative_def)
        ultimately show ?case using `a \<noteq> b` `x \<noteq> a` `a \<noteq> c` by(force simp add: eqvts calc_atm)
      qed
    next
      case(cRes aP)
      from `<\<nu>a>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> aP` `x \<noteq> a` `x \<sharp> P` `b \<sharp> c` show ?case
      proof(induct rule: resCasesB)
        case(cOpen c P')
        from `P \<longmapsto>c[a] \<prec> P'` `x \<sharp> P` have "x \<sharp> P'" by(force intro: freshFreeDerivative)
        from `b \<sharp> BoundOutputS c` have "b \<noteq> c" by simp
        with `P \<longmapsto>c[a] \<prec> P'` `a \<noteq> b` have "<\<nu>b>P \<longmapsto> c[a] \<prec> <\<nu>b>P'" by(rule_tac ResF) auto
        with `c \<noteq> a` have "<\<nu>a><\<nu>b>P \<longmapsto> c<\<nu>a> \<prec> <\<nu>b>P'" by(rule_tac Open) auto
        hence "<\<nu>a><\<nu>b>P \<longmapsto>c<\<nu>x> \<prec> <\<nu>b>([(x, a)] \<bullet> P')" using `x \<noteq> b` `a \<noteq> b` `x \<sharp> P'`
          apply(subst alphaBoundResidual[where x'=a]) by(auto simp add: abs_fresh fresh_left calc_atm)
        moreover have "derivative (<\<nu>b>([(x, a)] \<bullet> P')) (<\<nu>b>([(x, a)] \<bullet> P')) (BoundOutputS c) x Rel" using Id
          by(force simp add: derivative_def)
        ultimately show ?case by blast
      next
        case(cRes P')
        from `P \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> P'` `b \<sharp> c` `x \<noteq> b` have "<\<nu>b>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> <\<nu>b>P'" by(rule_tac ResB) auto
        hence "<\<nu>a><\<nu>b>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> <\<nu>a><\<nu>b>P'" using `a \<sharp> c` `x \<noteq> a` by(rule_tac ResB) auto
        moreover have "derivative (<\<nu>a><\<nu>b>P') (<\<nu>b><\<nu>a>P') c x Rel"
        proof(cases c, auto simp add: derivative_def)
          fix u::name
          show  "((<\<nu>a><\<nu>b>P')[x::=u],  (<\<nu>b><\<nu>a>P')[x::=u]) \<in> Rel"
          proof(cases "u=a")
            case True
            from `u = a` `a \<noteq> b` show ?thesis
              by(subst injPermSubst[symmetric], auto simp add: abs_fresh)
                (subst injPermSubst[symmetric], auto simp add: abs_fresh calc_atm intro: ResComm)
          next
            case False
            show ?thesis
            proof(cases "u=b")
              case True
              from `u = b` `u \<noteq> a` show ?thesis
              by(subst injPermSubst[symmetric], auto simp add: abs_fresh)
                (subst injPermSubst[symmetric], auto simp add: abs_fresh calc_atm intro: ResComm)
            next
              case False
              from `u \<noteq> a` `u \<noteq> b` `x \<noteq> a` `x \<noteq> b` show ?thesis by(auto intro: ResComm)
            qed
          qed
        next
          show "(<\<nu>a><\<nu>b>P', <\<nu>b><\<nu>a>P') \<in> Rel" by(rule ResComm)
        qed
        ultimately show ?case by blast
      qed
    qed
  next
    case(Free \<alpha> baP)
    from `<\<nu>b><\<nu>a>P \<longmapsto> \<alpha> \<prec> baP` show ?case
    proof(induct rule: resCasesF)
      case(cRes aP)
      from `<\<nu>a>P \<longmapsto> \<alpha> \<prec> aP` show ?case
      proof(induct rule: resCasesF)
        case(cRes P')
        from `P \<longmapsto> \<alpha> \<prec> P'` `b \<sharp> \<alpha>` have "<\<nu>b>P \<longmapsto> \<alpha> \<prec> <\<nu>b>P'" by(rule ResF)
        hence "<\<nu>a><\<nu>b>P \<longmapsto> \<alpha> \<prec> <\<nu>a><\<nu>b>P'" using `a \<sharp> \<alpha>` by(rule ResF)
        moreover have "(<\<nu>a><\<nu>b>P', <\<nu>b><\<nu>a>P') \<in> Rel" by(rule ResComm)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

(***************** !-operator ********************)

lemma bangLeftSC:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "!P \<leadsto>[Rel] P \<parallel> !P"
using assms
by(force simp add: simulation_def dest: Bang derivativeReflexive)

lemma bangRightSC:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes IdRel: "Id \<subseteq> Rel"

  shows "P \<parallel> !P \<leadsto>[Rel] !P"
using assms
by(fastforce simp add: pi.inject simulation_def intro: derivativeReflexive elim: bangCases)

lemma resNilLeft:
  fixes x   :: name
  and   y   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   b   :: name

  shows "\<zero> \<leadsto>[Rel] <\<nu>x>(x<y>.P)"
  and   "\<zero> \<leadsto>[Rel] <\<nu>x>(x{b}.P)"
by(auto simp add: simulation_def)

lemma resInputLeft:
  fixes x :: name
  and   a :: name
  and   y :: name
  and   P :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqy: "x \<noteq> y"
  and     Eqvt: "eqvt Rel"
  and     Id: "Id \<subseteq> Rel"

  shows "<\<nu>x>a<y>.P \<leadsto>[Rel] a<y>.(<\<nu>x>P)"
using Eqvt
proof(induct rule: simCasesCont[where C="(x, y, a, P)"])
  case(Bound b z P')
  from `z \<sharp> (x, y, a, P)` have "z \<noteq> x" and "z \<noteq> y" and "z \<sharp> P" and "z \<noteq> a"  by simp+
  from `z \<sharp> P` have "z \<sharp> <\<nu>x>P" by(simp add: abs_fresh)
  with `a<y>.(<\<nu>x>P) \<longmapsto>b\<guillemotleft>z\<guillemotright> \<prec> P'` `z \<noteq> a` `z \<noteq> y` show ?case
  proof(induct rule: inputCases)
    case cInput
    have "a<y>.P \<longmapsto>a<y> \<prec> P" by(rule Input)
    with `x \<noteq> y` `x \<noteq> a` have "<\<nu>x>a<y>.P \<longmapsto>a<y> \<prec> <\<nu>x>P" by(rule_tac ResB) auto
    hence "<\<nu>x>a<y>.P \<longmapsto>a<z> \<prec> [(y,  z)] \<bullet> <\<nu>x>P" using `z \<sharp> P` 
      by(subst alphaBoundResidual[where x'=y]) (auto simp add: abs_fresh fresh_left calc_atm)
    moreover from Id have "derivative ([(y, z)] \<bullet> <\<nu>x>P) ([(y, z)] \<bullet> <\<nu>x>P) (InputS a) z Rel" 
      by(rule derivativeReflexive)
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> P')
  from `a<y>.(<\<nu>x>P) \<longmapsto>\<alpha> \<prec> P'` have False by auto
  thus ?case by simp
qed

lemma resInputRight:
  fixes a :: name
  and   y :: name
  and   x :: name
  and   P :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqy: "x \<noteq> y"
  and     Eqvt: "eqvt Rel"
  and     Id: "Id \<subseteq> Rel"

  shows "a<y>.(<\<nu>x>P) \<leadsto>[Rel] <\<nu>x>a<y>.P"
  using Eqvt
proof(induct rule: simCasesCont[where C="(x, y, a, P)"])
  case(Bound b z xP)
  from `z \<sharp> (x, y, a, P)` have "z \<noteq> x" and "z \<noteq> y" and "z \<sharp> P" and "z \<noteq> a" by simp+
  from `z \<noteq> a` `z \<sharp> P` have "z \<sharp> a<y>.P" by(simp add: abs_fresh)
  with `<\<nu>x>a<y>.P \<longmapsto>b\<guillemotleft>z\<guillemotright> \<prec> xP` `z \<noteq> x` show ?case
  proof(induct rule: resCasesB)
    case(cOpen b P')
    from `a<y>.P \<longmapsto>b[x] \<prec> P'` have False by auto
    thus ?case by simp
  next
    case(cRes P')
    from `a<y>.P \<longmapsto>b\<guillemotleft>z\<guillemotright> \<prec> P'``z \<noteq> a` `z \<noteq> y` `z \<sharp> P` show ?case
    proof(induct rule: inputCases)
      case cInput
      have "a<y>.(<\<nu>x>P) \<longmapsto>a<y> \<prec> (<\<nu>x>P)" by(rule Input)
      with `z \<sharp> P` `x \<noteq> y` `z \<noteq> x` have "a<y>.(<\<nu>x>P) \<longmapsto>a<z> \<prec> (<\<nu>x>([(y, z)] \<bullet> P))"
        by(subst alphaBoundResidual[where x'=y]) (auto simp add: abs_fresh calc_atm fresh_left)
      moreover from Id have "derivative (<\<nu>x>([(y, z)] \<bullet> P)) (<\<nu>x>([(y, z)] \<bullet> P)) (InputS a) z Rel"
        by(rule derivativeReflexive)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> P')
  from `<\<nu>x>a<y>.P \<longmapsto>\<alpha> \<prec> P'` have False by auto
  thus ?case by simp
qed

lemma resOutputLeft:
  fixes x   :: name
  and   a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqb: "x \<noteq> b"
  and     Id: "Id \<subseteq> Rel"

  shows "<\<nu>x>a{b}.P \<leadsto>[Rel] a{b}.(<\<nu>x>P)"
using assms
by(fastforce simp add: simulation_def elim: outputCases intro: Output ResF)

lemma resOutputRight:
  fixes x   :: name
  and   a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqb: "x \<noteq> b"
  and     Id: "Id \<subseteq> Rel"
  and     Eqvt: "eqvt Rel"

  shows "a{b}.(<\<nu>x>P) \<leadsto>[Rel] <\<nu>x>a{b}.P"
using assms
by(erule_tac simCasesCont[where C=x])
  (force simp add: abs_fresh elim: resCasesB resCasesF outputCases intro: ResF Output)+

lemma resTauLeft:
  fixes x   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "<\<nu>x>(\<tau>.(P)) \<leadsto>[Rel] \<tau>.(<\<nu>x>P)"
using assms
by(force simp add: simulation_def elim: tauCases resCasesF intro: Tau ResF)

lemma resTauRight: 
  fixes x   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id:   "Id \<subseteq> Rel"

  shows "\<tau>.(<\<nu>x>P) \<leadsto>[Rel] <\<nu>x>(\<tau>.(P))"
using assms
by(force simp add: simulation_def elim: tauCases resCasesF intro: Tau ResF)

end
