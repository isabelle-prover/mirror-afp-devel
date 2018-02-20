section {* Explicit Büchi Automata *}

theory BA_Explicit
imports BA_Nodes
begin

  record ('label, 'state) bae =
    alphabete :: "'label set"
    initiale :: "'state set"
    transe :: "('state \<times> 'label \<times> 'state) set"
    acceptinge :: "'state set"

  definition bae_rel where
    [to_relAPP]: "bae_rel L S M \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabete A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> set_rel \<and>
      (initiale A\<^sub>1, initiale A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (transe A\<^sub>1, transe A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<and>
      (acceptinge A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (bae.more A\<^sub>1, bae.more A\<^sub>2) \<in> M}"

  lemma bae_param[param, autoref_rules]:
    "(bae_ext, bae_ext) \<in> \<langle>L\<rangle> set_rel \<rightarrow> \<langle>S\<rangle> set_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<rightarrow>
      \<langle>S\<rangle> set_rel \<rightarrow> M \<rightarrow> \<langle>L, S, M\<rangle> bae_rel"
    "(alphabete, alphabete) \<in> \<langle>L, S, M\<rangle> bae_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initiale, initiale) \<in> \<langle>L, S, M\<rangle> bae_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(transe, transe) \<in> \<langle>L, S, M\<rangle> bae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel"
    "(acceptinge, acceptinge) \<in> \<langle>L, S, M\<rangle> bae_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(bae.more, bae.more) \<in> \<langle>L, S, M\<rangle> bae_rel \<rightarrow> M"
    unfolding bae_rel_def by auto

  lemma bae_rel_id[simp]: "\<langle>Id, Id, Id\<rangle> bae_rel = Id" unfolding bae_rel_def by auto
  lemma bae_rel_comp[simp]: "\<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2, M\<^sub>1 O M\<^sub>2\<rangle> bae_rel = \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> bae_rel O \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> bae_rel"
  proof safe
    fix A B
    assume 1: "(A, B) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2, M\<^sub>1 O M\<^sub>2\<rangle> bae_rel"
    obtain a b c d e where 2:
      "(alphabete A, a) \<in> \<langle>L\<^sub>1\<rangle> set_rel" "(a, alphabete B) \<in> \<langle>L\<^sub>2\<rangle> set_rel"
      "(initiale A, b) \<in> \<langle>S\<^sub>1\<rangle> set_rel" "(b, initiale B) \<in> \<langle>S\<^sub>2\<rangle> set_rel"
      "(transe A, c) \<in> \<langle>S\<^sub>1 \<times>\<^sub>r L\<^sub>1 \<times>\<^sub>r S\<^sub>1\<rangle> set_rel" "(c, transe B) \<in> \<langle>S\<^sub>2 \<times>\<^sub>r L\<^sub>2 \<times>\<^sub>r S\<^sub>2\<rangle> set_rel"
      "(acceptinge A, d) \<in> \<langle>S\<^sub>1\<rangle> set_rel" "(d, acceptinge B) \<in> \<langle>S\<^sub>2\<rangle> set_rel"
      "(bae.more A, e) \<in> M\<^sub>1" "(e, bae.more B) \<in> M\<^sub>2"
      using 1 unfolding bae_rel_def prod_rel_compp set_rel_compp by auto
    show "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> bae_rel O \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> bae_rel"
    proof
      show "(A, bae_ext a b c d e) \<in> \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> bae_rel" using 2 unfolding bae_rel_def by auto
      show "(bae_ext a b c d e, B) \<in> \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> bae_rel" using 2 unfolding bae_rel_def by auto
    qed
  next
    show "(A, C) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2, M\<^sub>1 O M\<^sub>2\<rangle> bae_rel"
      if "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> bae_rel" "(B, C) \<in> \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> bae_rel" for A B C
      using that unfolding bae_rel_def prod_rel_compp set_rel_compp by auto
  qed

  (* TODO: why do we need all this setup? can't i_of_rel do the trick? *)
  consts i_bae_scheme :: "interface \<Rightarrow> interface \<Rightarrow> interface \<Rightarrow> interface"

  context
  begin

    interpretation autoref_syn by this

    lemma bae_scheme_itype[autoref_itype]:
      "bae_ext ::\<^sub>i \<langle>L\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i
        M \<rightarrow>\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_bae_scheme"
      "alphabete ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_bae_scheme \<rightarrow>\<^sub>i \<langle>L\<rangle>\<^sub>i i_set"
      "initiale ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_bae_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "transe ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_bae_scheme \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set"
      "acceptinge ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_bae_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "bae.more ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_bae_scheme \<rightarrow>\<^sub>i M"
      by auto

  end

  record ('label, 'state) baei =
    alphabetei :: "'label list"
    initialei :: "'state list"
    transei :: "('state \<times> 'label \<times> 'state) list"
    acceptingei :: "'state list"

  definition baei_bae_rel where
    [to_relAPP]: "baei_bae_rel L S M \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabetei A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initialei A\<^sub>1, initiale A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (transei A\<^sub>1, transe A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<and>
      (acceptingei A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (baei.more A\<^sub>1, bae.more A\<^sub>2) \<in> M}"

  lemmas [autoref_rel_intf] = REL_INTFI[of baei_bae_rel i_bae_scheme]

  lemma baei_bae_param[param, autoref_rules]:
    "(baei_ext, bae_ext) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> \<langle>S\<rangle> list_set_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<rightarrow>
      \<langle>S\<rangle> list_set_rel \<rightarrow> M \<rightarrow> \<langle>L, S, M\<rangle> baei_bae_rel"
    "(alphabetei, alphabete) \<in> \<langle>L, S, M\<rangle> baei_bae_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initialei, initiale) \<in> \<langle>L, S, M\<rangle> baei_bae_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(transei, transe) \<in> \<langle>L, S, M\<rangle> baei_bae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel"
    "(acceptingei, acceptinge) \<in> \<langle>L, S, M\<rangle> baei_bae_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(baei.more, bae.more) \<in> \<langle>L, S, M\<rangle> baei_bae_rel \<rightarrow> M"
    unfolding baei_bae_rel_def by auto

  definition bae where
    "bae A \<equiv> \<lparr> alphabete = set (alphabetei A), initiale = set (initialei A),
      transe = set (transei A), acceptinge = set (acceptingei A), \<dots> = baei.more A \<rparr>"

  lemma bae_id[param]: "(bae, id) \<in> \<langle>L, S, M\<rangle> baei_bae_rel \<rightarrow> \<langle>L, S, M\<rangle> bae_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S, M\<rangle> baei_bae_rel"
    have 2: "bae Ai = \<lparr> alphabete = set (alphabetei Ai), initiale = set (initialei Ai),
      transe = set (transei Ai), acceptinge = set (acceptingei Ai), \<dots> = baei.more Ai \<rparr>"
      unfolding bae_def by rule
    have 3: "id A = \<lparr> alphabete = id (alphabete A), initiale = id (initiale A),
      transe = id (transe A), acceptinge = id (acceptinge A), \<dots> = bae.more A \<rparr>" by simp
    show "(bae Ai, id A) \<in> \<langle>L, S, M\<rangle> bae_rel" unfolding 2 3 using 1 by parametricity
  qed

  abbreviation "transitions L S s \<equiv> \<Union> a \<in> L. \<Union> p \<in> S. {p} \<times> {a} \<times> s a p"
  abbreviation "succs T a p \<equiv> (T `` {p}) `` {a}"

  definition ba_bae where "ba_bae A \<equiv> \<lparr>
    alphabete = alphabet A, initiale = initial A, transe = transitions (alphabet A) (nodes A) (succ A),
    acceptinge = Set.filter (accepting A) (nodes A),  \<dots> = ba.more A \<rparr>"
  definition bae_ba where "bae_ba A \<equiv> \<lparr> alphabet = alphabete A, initial = initiale A,
      succ = succs (transe A), accepting = \<lambda> p. p \<in> acceptinge A, \<dots> = bae.more A \<rparr>"

  lemma ba_bae_param[param]: "(ba_bae, ba_bae) \<in> \<langle>L, S, M\<rangle> ba_rel \<rightarrow> \<langle>L, S, M\<rangle> bae_rel"
    unfolding ba_bae_def by parametricity
  lemma bae_ba_param[param]:
    assumes "bijective L" "bijective S"
    shows "(bae_ba, bae_ba) \<in> \<langle>L, S, M\<rangle> bae_rel \<rightarrow> \<langle>L, S, M\<rangle> ba_rel"
    using assms assms(2)[unfolded bijective_alt] unfolding bae_ba_def by parametricity auto

  lemma bae_ba_ba_bae_param[param]:
    "((bae_ba \<circ> ba_bae) A, id A) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A), Id\<rangle> ba_rel"
  proof -
    have 2: "(bae_ba \<circ> ba_bae) A = \<lparr> alphabet = alphabet A, initial = initial A,
      succ = succs (transitions (alphabet A) (nodes A) (succ A)),
      accepting = \<lambda> p. p \<in> Set.filter (accepting A) (nodes A), \<dots> = ba.more A \<rparr>"
      unfolding bae_ba_def ba_bae_def by simp
    also have "(\<dots>, \<lparr> alphabet = alphabet A, initial = initial A, succ = succ A,
      accepting = accepting A, \<dots> = ba.more A \<rparr>) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A), Id\<rangle> ba_rel"
      using ba_rel_eq by parametricity auto
    also have  "\<lparr> alphabet = alphabet A, initial = initial A,
      succ = succ A, accepting = accepting A, \<dots> = ba.more A \<rparr> = id A" by simp
    finally show ?thesis by this
  qed

  definition baei_ba_rel where
    [to_relAPP]: "baei_ba_rel L S M \<equiv> {(Ae, A). (bae_ba (bae Ae), A) \<in> \<langle>L, S, M\<rangle> ba_rel}"
  lemma baei_ba_id[param]: "(bae_ba \<circ> bae, id) \<in> \<langle>L, S, M\<rangle> baei_ba_rel \<rightarrow> \<langle>L, S, M\<rangle> ba_rel"
    unfolding baei_ba_rel_def by auto

end