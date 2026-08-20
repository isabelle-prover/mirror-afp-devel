(*  Title:      Examples.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Worked example derivations exercising the labelled framework:
    provenance-labelled implicational combinators, labelled modus ponens,
    and a possible-world derivation of the modal K axiom.
*)

theory Examples
  imports Provenance_Labels Modal_Labels_Example
begin

text \<open>
This theory collects small derivations that exercise the labelled framework:
provenance-labelled implicational combinators, labelled modus ponens, and a
possible-world derivation of the modal K axiom.
\<close>

lemma K_axiom_labelled:
  "provenance.lderives [] ({}, Imp A (Imp B A))"
proof -
  have a_from_ab: "provenance.lderives [({1}, B), ({0}, A)] ({0}, A)"
    by (rule provenance.LAssm) simp
  have b_imp_a: "provenance.lderives [({0}, A)] ({0}, Imp B A)"
  proof -
    have "provenance.lderives [({0}, A)] ((\<lambda>S T. T - S) {1} {0}, Imp B A)"
      using a_from_ab by (rule provenance.LImpI)
    then show ?thesis
      by auto
  qed
  have "provenance.lderives [] ((\<lambda>S T. T - S) {0} {0}, Imp A (Imp B A))"
    using b_imp_a by (rule provenance.LImpI)
  then show ?thesis
    by auto
qed

lemma S_axiom_labelled:
  "provenance.lderives []
    ({}, Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C)))"
proof -
  let ?F = "Imp A (Imp B C)"
  let ?G = "Imp A B"
  let ?ctx = "[({2}, A), ({1}, ?G), ({0}, ?F)]"
  have f: "provenance.lderives ?ctx ({0}, ?F)"
    by (rule provenance.LAssm) simp
  have g: "provenance.lderives ?ctx ({1}, ?G)"
    by (rule provenance.LAssm) simp
  have a: "provenance.lderives ?ctx ({2}, A)"
    by (rule provenance.LAssm) simp
  have f_applied: "provenance.lderives ?ctx ({0, 2}, Imp B C)"
  proof -
    have raw: "provenance.lderives ?ctx ((\<lambda>S T. S \<union> T) {0} {2}, Imp B C)"
      using f a by (rule provenance.LImpE)
    have "((\<lambda>S T. S \<union> T) ({0}::prov) ({2}::prov)) = {0, 2}"
      by auto
    with raw show ?thesis
      by simp
  qed
  have b: "provenance.lderives ?ctx ({1, 2}, B)"
  proof -
    have raw: "provenance.lderives ?ctx ((\<lambda>S T. S \<union> T) {1} {2}, B)"
      using g a by (rule provenance.LImpE)
    have "((\<lambda>S T. S \<union> T) ({1}::prov) ({2}::prov)) = {1, 2}"
      by auto
    with raw show ?thesis
      by simp
  qed
  have c: "provenance.lderives ?ctx ({0, 1, 2}, C)"
  proof -
    have raw: "provenance.lderives ?ctx ((\<lambda>S T. S \<union> T) {0, 2} {1, 2}, C)"
      using f_applied b by (rule provenance.LImpE)
    have "((\<lambda>S T. S \<union> T) ({0, 2}::prov) ({1, 2}::prov)) = {0, 1, 2}"
      by auto
    with raw show ?thesis
      by simp
  qed
  have imp_a_c: "provenance.lderives [({1}, ?G), ({0}, ?F)] ({0, 1}, Imp A C)"
  proof -
    have raw: "provenance.lderives [({1}, ?G), ({0}, ?F)]
        ((\<lambda>S T. T - S) {2} {0, 1, 2}, Imp A C)"
      using c by (rule provenance.LImpI)
    have "((\<lambda>S T. T - S) ({2}::prov) ({0, 1, 2}::prov)) = {0, 1}"
      by auto
    with raw show ?thesis
      by simp
  qed
  have imp_g_a_c: "provenance.lderives [({0}, ?F)] ({0}, Imp ?G (Imp A C))"
  proof -
    have raw: "provenance.lderives [({0}, ?F)]
        ((\<lambda>S T. T - S) {1} {0, 1}, Imp ?G (Imp A C))"
      using imp_a_c by (rule provenance.LImpI)
    have "((\<lambda>S T. T - S) ({1}::prov) ({0, 1}::prov)) = {0}"
      by auto
    with raw show ?thesis
      by simp
  qed
  have raw: "provenance.lderives []
      ((\<lambda>S T. T - S) {0} {0},
       Imp ?F (Imp ?G (Imp A C)))"
    using imp_g_a_c by (rule provenance.LImpI)
  have "((\<lambda>S T. T - S) ({0}::prov) ({0}::prov)) = {}"
    by auto
  with raw show ?thesis
    by simp
qed

lemma modus_ponens_labelled:
  "provenance.lderives [({0}, Imp A B), ({1}, A)] ({0, 1}, B)"
proof -
  have imp: "provenance.lderives [({0}, Imp A B), ({1}, A)] ({0}, Imp A B)"
    by (rule provenance.LAssm) simp
  have arg: "provenance.lderives [({0}, Imp A B), ({1}, A)] ({1}, A)"
    by (rule provenance.LAssm) simp
  have raw: "provenance.lderives [({0}, Imp A B), ({1}, A)]
      ((\<lambda>S T. S \<union> T) {0} {1}, B)"
    using imp arg by (rule provenance.LImpE)
  have "((\<lambda>S T. S \<union> T) ({0}::prov) ({1}::prov)) = {0, 1}"
    by auto
  with raw show ?thesis
    by simp
qed

lemma modal_K_axiom:
  "mlderives [] R
    (MLam (MWorld w) (MLam (MWorld w) (MBoxI (MWorld w))),
      MImp (Box (MImp A B)) (MImp (Box A) (Box B)))"
proof (rule mlderives.MImpI)
  show "world_of (MWorld w) = world_of (MLam (MWorld w) (MBoxI (MWorld w)))"
    by simp
  show "mlderives [(MWorld w, Box (MImp A B))] R
      (MLam (MWorld w) (MBoxI (MWorld w)), MImp (Box A) (Box B))"
  proof (rule mlderives.MImpI)
    show "world_of (MWorld w) = world_of (MBoxI (MWorld w))"
      by simp
    show "mlderives [(MWorld w, Box A), (MWorld w, Box (MImp A B))] R
        (MBoxI (MWorld w), Box B)"
    proof (rule mlderives.MBoxI)
      fix v
      assume access: "R (world_of (MWorld w)) v"
      have imp: "mlderives [(MWorld w, Box A), (MWorld w, Box (MImp A B))] R
          (MBoxE (MWorld v), MImp A B)"
        by (meson MAssm MBoxE access list.set_intros(1,2))
      have arg: "mlderives [(MWorld w, Box A), (MWorld w, Box (MImp A B))] R
          (MBoxE (MWorld v), A)"
        by (meson MAssm MBoxE access list.set_intros(1))
      have result: "mlderives [(MWorld w, Box A), (MWorld w, Box (MImp A B))] R
          (MApp (MBoxE (MWorld v)) (MBoxE (MWorld v)), B)"
        by (rule mlderives.MImpE[OF _ imp arg]) simp
      show "\<exists>m. world_of m = v \<and>
          mlderives [(MWorld w, Box A), (MWorld w, Box (MImp A B))] R (m, B)"
        using result
        by (intro exI[of _ "MApp (MBoxE (MWorld v)) (MBoxE (MWorld v))"]) simp
    qed
  qed
qed

end
