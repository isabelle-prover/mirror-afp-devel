section {* Explicit Nondeterministic Büchi Automata *}

theory NBA_Explicit
imports NBA_Nodes
begin

  record ('label, 'state) nbae =
    alphabete :: "'label set"
    initiale :: "'state set"
    transe :: "('state \<times> 'label \<times> 'state) set"
    acceptinge :: "'state set"

  definition nbae_rel where
    [to_relAPP]: "nbae_rel L S M \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabete A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> set_rel \<and>
      (initiale A\<^sub>1, initiale A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (transe A\<^sub>1, transe A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<and>
      (acceptinge A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (nbae.more A\<^sub>1, nbae.more A\<^sub>2) \<in> M}"

  lemma nbae_param[param, autoref_rules]:
    "(nbae_ext, nbae_ext) \<in> \<langle>L\<rangle> set_rel \<rightarrow> \<langle>S\<rangle> set_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<rightarrow>
      \<langle>S\<rangle> set_rel \<rightarrow> M \<rightarrow> \<langle>L, S, M\<rangle> nbae_rel"
    "(alphabete, alphabete) \<in> \<langle>L, S, M\<rangle> nbae_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initiale, initiale) \<in> \<langle>L, S, M\<rangle> nbae_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(transe, transe) \<in> \<langle>L, S, M\<rangle> nbae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel"
    "(acceptinge, acceptinge) \<in> \<langle>L, S, M\<rangle> nbae_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(nbae.more, nbae.more) \<in> \<langle>L, S, M\<rangle> nbae_rel \<rightarrow> M"
    unfolding nbae_rel_def by auto

  lemma nbae_rel_id[simp]: "\<langle>Id, Id, Id\<rangle> nbae_rel = Id" unfolding nbae_rel_def by auto
  lemma nbae_rel_comp[simp]: "\<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2, M\<^sub>1 O M\<^sub>2\<rangle> nbae_rel = \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> nbae_rel O \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> nbae_rel"
  proof safe
    fix A B
    assume 1: "(A, B) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2, M\<^sub>1 O M\<^sub>2\<rangle> nbae_rel"
    obtain a b c d e where 2:
      "(alphabete A, a) \<in> \<langle>L\<^sub>1\<rangle> set_rel" "(a, alphabete B) \<in> \<langle>L\<^sub>2\<rangle> set_rel"
      "(initiale A, b) \<in> \<langle>S\<^sub>1\<rangle> set_rel" "(b, initiale B) \<in> \<langle>S\<^sub>2\<rangle> set_rel"
      "(transe A, c) \<in> \<langle>S\<^sub>1 \<times>\<^sub>r L\<^sub>1 \<times>\<^sub>r S\<^sub>1\<rangle> set_rel" "(c, transe B) \<in> \<langle>S\<^sub>2 \<times>\<^sub>r L\<^sub>2 \<times>\<^sub>r S\<^sub>2\<rangle> set_rel"
      "(acceptinge A, d) \<in> \<langle>S\<^sub>1\<rangle> set_rel" "(d, acceptinge B) \<in> \<langle>S\<^sub>2\<rangle> set_rel"
      "(nbae.more A, e) \<in> M\<^sub>1" "(e, nbae.more B) \<in> M\<^sub>2"
      using 1 unfolding nbae_rel_def prod_rel_compp set_rel_compp by auto
    show "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> nbae_rel O \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> nbae_rel"
    proof
      show "(A, nbae_ext a b c d e) \<in> \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> nbae_rel" using 2 unfolding nbae_rel_def by auto
      show "(nbae_ext a b c d e, B) \<in> \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> nbae_rel" using 2 unfolding nbae_rel_def by auto
    qed
  next
    show "(A, C) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2, M\<^sub>1 O M\<^sub>2\<rangle> nbae_rel"
      if "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1, M\<^sub>1\<rangle> nbae_rel" "(B, C) \<in> \<langle>L\<^sub>2, S\<^sub>2, M\<^sub>2\<rangle> nbae_rel" for A B C
      using that unfolding nbae_rel_def prod_rel_compp set_rel_compp by auto
  qed

  (* TODO: why do we need all this setup? can't i_of_rel do the trick? *)
  consts i_nbae_scheme :: "interface \<Rightarrow> interface \<Rightarrow> interface \<Rightarrow> interface"

  context
  begin

    interpretation autoref_syn by this

    lemma nbae_scheme_itype[autoref_itype]:
      "nbae_ext ::\<^sub>i \<langle>L\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i
        M \<rightarrow>\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_nbae_scheme"
      "alphabete ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>L\<rangle>\<^sub>i i_set"
      "initiale ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "transe ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set"
      "acceptinge ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "nbae.more ::\<^sub>i \<langle>L, S, M\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i M"
      by auto

  end

  record ('label, 'state) nbaei =
    alphabetei :: "'label list"
    initialei :: "'state list"
    transei :: "('state \<times> 'label \<times> 'state) list"
    acceptingei :: "'state list"

  definition nbaei_nbae_rel where
    [to_relAPP]: "nbaei_nbae_rel L S M \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabetei A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initialei A\<^sub>1, initiale A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (transei A\<^sub>1, transe A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<and>
      (acceptingei A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (nbaei.more A\<^sub>1, nbae.more A\<^sub>2) \<in> M}"

  lemmas [autoref_rel_intf] = REL_INTFI[of nbaei_nbae_rel i_nbae_scheme]

  lemma nbaei_nbae_param[param, autoref_rules]:
    "(nbaei_ext, nbae_ext) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> \<langle>S\<rangle> list_set_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<rightarrow>
      \<langle>S\<rangle> list_set_rel \<rightarrow> M \<rightarrow> \<langle>L, S, M\<rangle> nbaei_nbae_rel"
    "(alphabetei, alphabete) \<in> \<langle>L, S, M\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initialei, initiale) \<in> \<langle>L, S, M\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(transei, transe) \<in> \<langle>L, S, M\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel"
    "(acceptingei, acceptinge) \<in> \<langle>L, S, M\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(nbaei.more, nbae.more) \<in> \<langle>L, S, M\<rangle> nbaei_nbae_rel \<rightarrow> M"
    unfolding nbaei_nbae_rel_def by auto

  definition nbae where
    "nbae A \<equiv> \<lparr> alphabete = set (alphabetei A), initiale = set (initialei A),
      transe = set (transei A), acceptinge = set (acceptingei A), \<dots> = nbaei.more A \<rparr>"

  lemma nbae_id[param]: "(nbae, id) \<in> \<langle>L, S, M\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>L, S, M\<rangle> nbae_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S, M\<rangle> nbaei_nbae_rel"
    have 2: "nbae Ai = \<lparr> alphabete = set (alphabetei Ai), initiale = set (initialei Ai),
      transe = set (transei Ai), acceptinge = set (acceptingei Ai), \<dots> = nbaei.more Ai \<rparr>"
      unfolding nbae_def by rule
    have 3: "id A = \<lparr> alphabete = id (alphabete A), initiale = id (initiale A),
      transe = id (transe A), acceptinge = id (acceptinge A), \<dots> = nbae.more A \<rparr>" by simp
    show "(nbae Ai, id A) \<in> \<langle>L, S, M\<rangle> nbae_rel" unfolding 2 3 using 1 by parametricity
  qed

  abbreviation "transitions L S s \<equiv> \<Union> a \<in> L. \<Union> p \<in> S. {p} \<times> {a} \<times> s a p"
  abbreviation "succs T a p \<equiv> (T `` {p}) `` {a}"

  definition nba_nbae where "nba_nbae A \<equiv> \<lparr>
    alphabete = alphabet A, initiale = initial A, transe = transitions (alphabet A) (nodes A) (succ A),
    acceptinge = Set.filter (accepting A) (nodes A),  \<dots> = nba.more A \<rparr>"
  definition nbae_nba where "nbae_nba A \<equiv> \<lparr> alphabet = alphabete A, initial = initiale A,
      succ = succs (transe A), accepting = \<lambda> p. p \<in> acceptinge A, \<dots> = nbae.more A \<rparr>"

  lemma nba_nbae_param[param]: "(nba_nbae, nba_nbae) \<in> \<langle>L, S, M\<rangle> nba_rel \<rightarrow> \<langle>L, S, M\<rangle> nbae_rel"
    unfolding nba_nbae_def by parametricity
  lemma nbae_nba_param[param]:
    assumes "bijective L" "bijective S"
    shows "(nbae_nba, nbae_nba) \<in> \<langle>L, S, M\<rangle> nbae_rel \<rightarrow> \<langle>L, S, M\<rangle> nba_rel"
    using assms assms(2)[unfolded bijective_alt] unfolding nbae_nba_def by parametricity auto

  lemma nbae_nba_nba_nbae_param[param]:
    "((nbae_nba \<circ> nba_nbae) A, id A) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A), Id\<rangle> nba_rel"
  proof -
    have "(nbae_nba \<circ> nba_nbae) A = \<lparr> alphabet = alphabet A, initial = initial A,
      succ = succs (transitions (alphabet A) (nodes A) (succ A)),
      accepting = \<lambda> p. p \<in> Set.filter (accepting A) (nodes A), \<dots> = nba.more A \<rparr>"
      unfolding nbae_nba_def nba_nbae_def by simp
    also have "(\<dots>, \<lparr> alphabet = alphabet A, initial = initial A, succ = succ A,
      accepting = accepting A, \<dots> = nba.more A \<rparr>) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A), Id\<rangle> nba_rel"
      using nba_rel_eq by parametricity auto
    also have  "\<lparr> alphabet = alphabet A, initial = initial A,
      succ = succ A, accepting = accepting A, \<dots> = nba.more A \<rparr> = id A" by simp
    finally show ?thesis by this
  qed

  definition nbaei_nba_rel where
    [to_relAPP]: "nbaei_nba_rel L S M \<equiv> {(Ae, A). (nbae_nba (nbae Ae), A) \<in> \<langle>L, S, M\<rangle> nba_rel}"
  lemma nbaei_ba_id[param]: "(nbae_nba \<circ> nbae, id) \<in> \<langle>L, S, M\<rangle> nbaei_nba_rel \<rightarrow> \<langle>L, S, M\<rangle> nba_rel"
    unfolding nbaei_nba_rel_def by auto

end