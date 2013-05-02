theory Digraph_Isomorphism imports
  Arc_Walk
  Digraph
  Digraph_Component
begin

section {* Isomorphisms of Digraphs *}

record ('a,'b,'aa,'bb) digraph_isomorphism =
  iso_verts :: "'a \<Rightarrow> 'aa"
  iso_arcs :: "'b \<Rightarrow> 'bb"
  iso_head :: "'bb \<Rightarrow> 'aa"
  iso_tail :: "'bb \<Rightarrow> 'aa"

definition (in pre_digraph) digraph_isomorphism :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> bool" where 
  "digraph_isomorphism hom \<equiv>
    inj_on (iso_verts hom) (verts G) \<and>
    inj_on (iso_arcs hom) (arcs G) \<and>
    (\<forall>a \<in> arcs G. 
    iso_verts hom (tail G a) = iso_tail hom (iso_arcs hom a) \<and>
    iso_verts hom (head G a) = iso_head hom (iso_arcs hom a))"

definition app_iso
    :: "('a,'b,'aa,'bb) digraph_isomorphism \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> ('aa,'bb) pre_digraph" where
  "app_iso hom G \<equiv> \<lparr> verts = iso_verts hom ` verts G, arcs = iso_arcs hom ` arcs G,
    tail = iso_tail hom, head = iso_head hom \<rparr>"

lemma verts_app_iso[simp]: "verts (app_iso hom G) = iso_verts hom ` verts G"
  and arcs_app_iso: "arcs (app_iso hom G) = iso_arcs hom `arcs G"
  and tail_app_iso[simp]: "tail (app_iso hom G) = iso_tail hom"
  and head_app_iso[simp]: "head (app_iso hom G) = iso_head hom"
  by (auto simp: app_iso_def)

context pre_digraph begin

lemma iso_verts_eq_iff[simp]:
  assumes "digraph_isomorphism hom" "u \<in> verts G" "v \<in> verts G"
  shows "iso_verts hom u = iso_verts hom v \<longleftrightarrow> u = v"
  using assms by (auto simp: digraph_isomorphism_def dest: inj_onD)

lemma
  assumes "digraph_isomorphism hom" "e \<in> arcs G"
  shows iso_verts_tail: "iso_tail hom (iso_arcs hom e) = iso_verts hom (tail G e)"
    and iso_verts_head: "iso_head hom (iso_arcs hom e) = iso_verts hom (head G e)"
  using assms unfolding digraph_isomorphism_def by auto

lemma iso_arcs_eq_iff[simp]:
  assumes "digraph_isomorphism hom" "e1 \<in> arcs G" "e2 \<in> arcs G"
  shows "iso_arcs hom e1 = iso_arcs hom e2 \<longleftrightarrow> e1 = e2"
  using assms by (auto simp: digraph_isomorphism_def dest: inj_onD)

end

lemma (in wf_digraph) wf_digraphI_app_iso[intro?]:
  assumes "digraph_isomorphism hom"
  shows "wf_digraph (app_iso hom G)"
proof unfold_locales
  fix e assume "e \<in> arcs (app_iso hom G)"
  then obtain e' where e': "e' \<in> arcs G" "iso_arcs hom e' = e"
    by (auto simp: arcs_app_iso)
  then have "iso_verts hom (head G e') \<in> verts (app_iso hom G)"
      "iso_verts hom (tail G e') \<in> verts (app_iso hom G)"
    by auto
  then show "tail (app_iso hom G) e \<in> verts (app_iso hom G)"
      "head (app_iso hom G) e \<in> verts (app_iso hom G)"
    using e' assms by (auto simp: iso_verts_tail iso_verts_head)
qed

lemma (in pseudo_digraph) pseudo_digraphI_app_iso[intro?]:
  assumes "digraph_isomorphism hom"
  shows "pseudo_digraph (app_iso hom G)"
proof -
  interpret H: wf_digraph "app_iso hom G" using assms ..
  show ?thesis by unfold_locales (auto simp: arcs_app_iso)
qed

context wf_digraph begin

lemma awalk_verts_app_iso_eq:
  assumes "digraph_isomorphism hom" and "awalk u p v"
  shows "pre_digraph.awalk_verts (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p)
    = map (iso_verts hom) (awalk_verts u p)"
  using assms
  by (induct p arbitrary: u)
     (auto simp: pre_digraph.awalk_verts.simps iso_verts_head iso_verts_tail awalk_Cons_iff)

lemma awalk_relabelI:
  assumes w: "awalk u p v" and hom: "digraph_isomorphism hom"
  shows "pre_digraph.awalk (app_iso hom G) (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from assms show ?thesis
    by (induct p arbitrary: u)
       (auto simp: awalk_simps H.awalk_simps arcs_app_iso
         iso_verts_head iso_verts_tail)
qed

lemma reachableI_app_iso:
  assumes r: "u \<rightarrow>\<^isup>* v" and hom: "digraph_isomorphism hom"
  shows "(iso_verts hom u) \<rightarrow>\<^isup>*\<^bsub>app_iso hom G\<^esub> (iso_verts hom v)"
proof -
  interpret H: wf_digraph "app_iso hom G" using hom ..
  from r obtain p where "awalk u p v" by (auto simp: reachable_awalk)
  then have "H.awalk (iso_verts hom u) (map (iso_arcs hom) p) (iso_verts hom v)"
    using hom by (rule awalk_relabelI)
  then show ?thesis by (auto simp: H.reachable_awalk)
qed

lemma arcs_ends_app_iso:
  assumes "digraph_isomorphism hom"
  shows "arcs_ends (app_iso hom G) = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` arcs_ends G"
  using assms by (auto simp: arcs_ends_conv arcs_app_iso image_image iso_verts_head iso_verts_tail
      intro!: rev_image_eqI)

lemma connectedI_app_iso:
  assumes c: "connected G" and hom: "digraph_isomorphism hom"
  shows "connected (app_iso hom G)"
proof -
  have *: "symcl (arcs_ends (app_iso hom G)) = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` symcl (arcs_ends G)"
    using hom by (auto simp add: arcs_ends_app_iso symcl_def)
  { fix u v assume "(u,v) \<in> rtrancl_on (verts G) (symcl (arcs_ends G))"
    then have "(iso_verts hom u, iso_verts hom v) \<in> rtrancl_on (verts (app_iso hom G)) (symcl (arcs_ends (app_iso hom G)))"
    proof induct
      case (step x y)
      have "(iso_verts hom x, iso_verts hom y)
          \<in> rtrancl_on (verts (app_iso hom G)) (symcl (arcs_ends (app_iso hom G)))"
        using step by (rule_tac rtrancl_on_into_rtrancl_on[where b="iso_verts hom x"]) (auto simp: *)
      then show ?case
        by (rule rtrancl_on_trans) (rule step)
    qed auto }
  with c show ?thesis unfolding connected_conv by auto
qed

lemma in_arcs_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "in_arcs (app_iso hom G) (iso_verts hom u) = iso_arcs hom ` in_arcs G u"
  using assms unfolding in_arcs_def by (auto simp: arcs_app_iso iso_verts_head)

lemma out_arcs_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "out_arcs (app_iso hom G) (iso_verts hom u) = iso_arcs hom ` out_arcs G u"
  using assms unfolding out_arcs_def by (auto simp: arcs_app_iso iso_verts_tail)

lemma in_degree_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "in_degree (app_iso hom G) (iso_verts hom u) = in_degree G u"
  unfolding in_degree_def in_arcs_app_iso_eq[OF assms]
proof (rule card_image)
  from assms show "inj_on (iso_arcs hom) (in_arcs G u)"
    unfolding digraph_isomorphism_def by - (rule subset_inj_on, auto)
qed

lemma  out_degree_app_iso_eq:
  assumes "digraph_isomorphism hom" and "u \<in> verts G"
  shows "out_degree (app_iso hom G) (iso_verts hom u) = out_degree G u"
  unfolding out_degree_def out_arcs_app_iso_eq[OF assms]
proof (rule card_image)
  from assms show "inj_on (iso_arcs hom) (out_arcs G u)"
    unfolding digraph_isomorphism_def by - (rule subset_inj_on, auto)
qed

lemmas app_iso_eq =
  awalk_verts_app_iso_eq
  in_arcs_app_iso_eq
  out_arcs_app_iso_eq
  in_degree_app_iso_eq
  out_degree_app_iso_eq

end



end
