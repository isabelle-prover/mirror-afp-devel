(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Bisim_SC
  imports Weak_Early_Cong Strong_Early_Bisim_SC
begin

(******** Structural Congruence **********)

lemma matchId:
  fixes a :: name
  and   P :: pi

  shows "[a\<frown>a]P \<simeq> P"
proof -
  have "[a\<frown>a]P \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.matchId)
  thus ?thesis by(rule strongBisimWeakCong)
qed

(******** The \<nu>-operator *****************)

lemma resComm:
  fixes P :: pi
  
  shows "<\<nu>a><\<nu>b>P \<simeq> <\<nu>b><\<nu>a>P"
proof -
  have "<\<nu>a><\<nu>b>P \<sim>\<^sub>e <\<nu>b><\<nu>a>P" by(rule Strong_Early_Bisim_SC.resComm)
  thus ?thesis by(rule strongBisimWeakCong)
qed

(******** The +-operator *********)

lemma sumSym:
  fixes P :: pi
  and   Q :: pi
  
  shows "P \<oplus> Q \<simeq> Q \<oplus> P"
proof -
  have "P \<oplus> Q \<sim>\<^sub>e Q \<oplus> P" by(rule Strong_Early_Bisim_SC.sumSym)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma sumAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<oplus> Q) \<oplus> R \<simeq> P \<oplus> (Q \<oplus> R)"
proof -
  have "(P \<oplus> Q) \<oplus> R \<sim>\<^sub>e P \<oplus> (Q \<oplus> R)" by(rule Strong_Early_Bisim_SC.sumAssoc)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma sumZero:
  fixes P :: pi
  
  shows "P \<oplus> \<zero> \<simeq> P"
proof -
  have "P \<oplus> \<zero> \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.sumZero)
  thus ?thesis by(rule strongBisimWeakCong)
qed

(******** The |-operator *********)

lemma parZero:
  fixes P :: pi

  shows "P \<parallel> \<zero> \<simeq> P"
proof -
  have "P \<parallel> \<zero> \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.parZero)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma parSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<parallel> Q \<simeq> Q \<parallel> P"
proof -
  have "P \<parallel> Q \<sim>\<^sub>e Q \<parallel> P" by(rule Strong_Early_Bisim_SC.parSym)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma scopeExtPar:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<parallel> Q) \<simeq> P \<parallel> <\<nu>x>Q"
proof -
  from `x \<sharp> P` have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>e P \<parallel> <\<nu>x>Q" by(rule Strong_Early_Bisim_SC.scopeExtPar)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma scopeExtPar':
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> Q"

  shows "<\<nu>x>(P \<parallel> Q) \<simeq> (<\<nu>x>P) \<parallel> Q"
proof -
  from `x \<sharp> Q` have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>e (<\<nu>x>P) \<parallel> Q" by(rule Strong_Early_Bisim_SC.scopeExtPar')
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma parAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  shows "(P \<parallel> Q) \<parallel> R \<simeq> P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>e P \<parallel> (Q \<parallel> R)" by(rule Strong_Early_Bisim_SC.parAssoc)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma freshRes:
  fixes P :: pi
  and   a :: name

  assumes "a \<sharp> P"

  shows "<\<nu>a>P \<simeq> P"
proof -
  from `a \<sharp> P` have "<\<nu>a>P \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.freshRes)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma scopeExtSum:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<oplus> Q) \<simeq> P \<oplus> <\<nu>x>Q"
proof -
  from `x \<sharp> P` have "<\<nu>x>(P \<oplus> Q) \<sim>\<^sub>e P \<oplus> <\<nu>x>Q" by(rule Strong_Early_Bisim_SC.scopeExtSum)
  thus ?thesis by(rule strongBisimWeakCong)
qed

lemma bangSC:
  fixes P

  shows "!P \<simeq> P \<parallel> !P"
proof -
  have "!P \<sim>\<^sub>e P \<parallel> !P" by(rule Strong_Early_Bisim_SC.bangSC)
  thus ?thesis by(rule strongBisimWeakCong)
qed

end