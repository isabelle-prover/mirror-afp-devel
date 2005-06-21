(*  Title:       Proving the Correctness of Disk Paxos
    ID:          $Id: DiskPaxos_Invariant.thy,v 1.2 2005-06-21 22:51:28 lsf37 Exp $
    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro@fceia.unr.edu.ar>
*)

theory DiskPaxos_Invariant = DiskPaxos_Inv6:

subsection {* The Complete Invariant *}

constdefs
  HInv :: "state \<Rightarrow> bool"
  "HInv s \<equiv>   HInv1 s 
            \<and> HInv2 s
            \<and> HInv3 s
            \<and> HInv4 s
            \<and> HInv5 s
            \<and> HInv6 s"

theorem I1:
  "HInit s \<Longrightarrow> HInv s"
  using HInit_HInv1 HInit_HInv2 HInit_HInv3 
        HInit_HInv4 HInit_HInv5 HInit_HInv6
  by(auto simp add: HInv_def)

theorem I2:
  assumes inv:  "HInv s"
  and nxt: "HNext s s'"
  shows "HInv s'"
  using inv I2a[OF nxt] I2b[OF nxt] I2c[OF nxt] 
            I2d[OF nxt] I2e[OF nxt] I2f[OF nxt]
  by(simp add: HInv_def)


end
