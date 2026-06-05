(*  Title:      Modal_K_Schema.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

    Derivation of the normal modal K axiom schema and necessitation in
    the labelled modal instance, with a Kripke-validity corollary.
*)

theory Modal_K_Schema
  imports Modal_Labels_Example
begin

text \<open>
The modal instance derives the normal modal K axiom schema directly in the
labelled calculus.  The proof is uniform in the formulae, the accessibility
relation, and the chosen world; necessitation is available only for formulae
that are derivable from the empty context at every world and under every
accessibility relation.
\<close>

theorem modal_K_schema:
  fixes A B :: "'a mfm"
    and R :: "nat \<Rightarrow> nat \<Rightarrow> bool"
    and w :: nat
  shows
    "\<exists>l. world_of l = w \<and>
         mlderives [] R (l, MImp (Box (MImp A B)) (MImp (Box A) (Box B)))"
proof -
  let ?imp_assm = "MWorld w"
  let ?box_assm = "MWorld w"
  let ?box_label = "MBoxI (MWorld w)"
  let ?inner_label = "MLam ?box_assm ?box_label"
  let ?outer_label = "MLam ?imp_assm ?inner_label"
  let ?K = "MImp (Box (MImp A B)) (MImp (Box A) (Box B))"
  let ?\<Gamma> = "[(?box_assm, Box A), (?imp_assm, Box (MImp A B))]"

  have box_deriv: "mlderives ?\<Gamma> R (?box_label, Box B)"
  proof (rule mlderives.MBoxI)
    fix v
    assume accessible: "R (world_of (MWorld w)) v"
    let ?elim_label = "MBoxE (MWorld v)"
    have imp_assm_deriv: "mlderives ?\<Gamma> R (?imp_assm, Box (MImp A B))"
      by (rule mlderives.MAssm) simp
    have imp_at_v: "mlderives ?\<Gamma> R (?elim_label, MImp A B)"
    proof (rule mlderives.MBoxE)
      show "mlderives ?\<Gamma> R (?imp_assm, Box (MImp A B))"
        by (rule imp_assm_deriv)
      show "R (world_of ?imp_assm) v"
        using accessible by simp
    qed
    have box_assm_deriv: "mlderives ?\<Gamma> R (?box_assm, Box A)"
      by (rule mlderives.MAssm) simp
    have A_at_v: "mlderives ?\<Gamma> R (?elim_label, A)"
    proof (rule mlderives.MBoxE)
      show "mlderives ?\<Gamma> R (?box_assm, Box A)"
        by (rule box_assm_deriv)
      show "R (world_of ?box_assm) v"
        using accessible by simp
    qed
    have B_at_v: "mlderives ?\<Gamma> R (MApp ?elim_label ?elim_label, B)"
    proof (rule mlderives.MImpE)
      show "world_of ?elim_label = world_of ?elim_label"
        by simp
      show "mlderives ?\<Gamma> R (?elim_label, MImp A B)"
        by (rule imp_at_v)
      show "mlderives ?\<Gamma> R (?elim_label, A)"
        by (rule A_at_v)
    qed
    show "\<exists>m. world_of m = v \<and> mlderives ?\<Gamma> R (m, B)"
      using B_at_v by (intro exI[of _ "MApp ?elim_label ?elim_label"]) simp
  qed

  have inner_deriv:
    "mlderives [(?imp_assm, Box (MImp A B))] R
      (?inner_label, MImp (Box A) (Box B))"
  proof (rule mlderives.MImpI)
    show "world_of ?box_assm = world_of ?box_label"
      by simp
    show "mlderives ((?box_assm, Box A) # [(?imp_assm, Box (MImp A B))]) R
      (?box_label, Box B)"
      using box_deriv by simp
  qed

  have outer_deriv: "mlderives [] R (?outer_label, ?K)"
  proof (rule mlderives.MImpI)
    show "world_of ?imp_assm = world_of ?inner_label"
      by simp
    show "mlderives ((?imp_assm, Box (MImp A B)) # []) R
      (?inner_label, MImp (Box A) (Box B))"
      using inner_deriv by simp
  qed

  show ?thesis
    using outer_deriv by (intro exI[of _ ?outer_label]) simp
qed

theorem modal_necessitation:
  fixes A :: "'a mfm"
    and R :: "nat \<Rightarrow> nat \<Rightarrow> bool"
    and w :: nat
  assumes provable_everywhere:
    "\<And>v R'. \<exists>l. world_of l = v \<and> mlderives [] R' (l, A)"
  shows
    "\<exists>l. world_of l = w \<and> mlderives [] R (l, Box A)"
proof -
  have box_deriv: "mlderives [] R (MBoxI (MWorld w), Box A)"
  proof (rule mlderives.MBoxI)
    fix v
    assume "R (world_of (MWorld w)) v"
    from provable_everywhere[of v R]
    show "\<exists>m. world_of m = v \<and> mlderives [] R (m, A)" .
  qed
  show ?thesis
    using box_deriv by (intro exI[of _ "MBoxI (MWorld w)"]) simp
qed

corollary modal_K_kripke_valid:
  fixes A B :: "'a mfm"
  shows "\<forall>V R w. modal_kripke_sat V R w
                  (MImp (Box (MImp A B)) (MImp (Box A) (Box B)))"
proof (intro allI)
  fix V R w
  let ?K = "MImp (Box (MImp A B)) (MImp (Box A) (Box B))"
  obtain l where l_world: "world_of l = w"
    and deriv: "mlderives [] R (l, ?K)"
    using modal_K_schema[where A=A and B=B and R=R and w=w] by blast
  have "modal_kripke_sat V R (world_of (fst (l, ?K))) (snd (l, ?K))"
  proof (rule modal_labels_sound)
    show "mlderives [] R (l, ?K)"
      by (rule deriv)
    show "\<forall>(l, A) \<in> set []. modal_kripke_sat V R (world_of l) A"
      by simp
  qed
  with l_world show "modal_kripke_sat V R w ?K"
    by simp
qed

corollary modal_K_example:
  shows "\<exists>l. world_of l = 0 \<and> mlderives [] R
                (l, MImp (Box (MImp (MAtom (0::nat)) (MAtom 1)))
                         (MImp (Box (MAtom 0)) (Box (MAtom 1))))"
  using modal_K_schema[
    where A="MAtom (0::nat)" and B="MAtom (1::nat)" and R=R and w=0]
  by simp

end
