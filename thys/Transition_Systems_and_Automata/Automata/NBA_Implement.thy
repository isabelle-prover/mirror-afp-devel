section {* Implementation of Nondeterministic Büchi Automata *}

theory NBA_Implement
imports
  "NBA_Refine"
  "../Basic/Implement"
begin

  record ('label, 'state) nbai =
    alphabeti :: "'label list"
    initiali :: "'state list"
    succi :: "'label \<Rightarrow> 'state \<Rightarrow> 'state list"
    acceptingi :: "'state \<Rightarrow> bool"

  definition nbai_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow> ('more\<^sub>1 \<times> 'more\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1, 'more\<^sub>1) nbai_scheme \<times> ('label\<^sub>2, 'state\<^sub>2, 'more\<^sub>2) nbai_scheme) set" where
    [to_relAPP]: "nbai_rel L S M \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabeti A\<^sub>2) \<in> \<langle>L\<rangle> list_rel \<and>
      (initiali A\<^sub>1, initiali A\<^sub>2) \<in> \<langle>S\<rangle> list_rel \<and>
      (succi A\<^sub>1, succi A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel \<and>
      (acceptingi A\<^sub>1, acceptingi A\<^sub>2) \<in> S \<rightarrow> bool_rel \<and>
      (nbai.more A\<^sub>1, nbai.more A\<^sub>2) \<in> M}"

  lemma nbai_param[param]:
    "(nbai_ext, nbai_ext) \<in> \<langle>L\<rangle> list_rel \<rightarrow> \<langle>S\<rangle> list_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel) \<rightarrow>
      (S \<rightarrow> bool_rel) \<rightarrow> M \<rightarrow> \<langle>L, S, M\<rangle> nbai_rel"
    "(alphabeti, alphabeti) \<in> \<langle>L, S, M\<rangle> nbai_rel \<rightarrow> \<langle>L\<rangle> list_rel"
    "(initiali, initiali) \<in> \<langle>L, S, M\<rangle> nbai_rel \<rightarrow> \<langle>S\<rangle> list_rel"
    "(succi, succi) \<in> \<langle>L, S, M\<rangle> nbai_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel"
    "(acceptingi, acceptingi) \<in> \<langle>L, S, M\<rangle> nbai_rel \<rightarrow> (S \<rightarrow> bool_rel)"
    "(nbai.more, nbai.more) \<in> \<langle>L, S, M\<rangle> nbai_rel \<rightarrow> M"
    unfolding nbai_rel_def fun_rel_def by auto

  definition nbai_nba_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow> ('more\<^sub>1 \<times> 'more\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1, 'more\<^sub>1) nbai_scheme \<times> ('label\<^sub>2, 'state\<^sub>2, 'more\<^sub>2) nba_scheme) set" where
    [to_relAPP]: "nbai_nba_rel L S M \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabet A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initiali A\<^sub>1, initial A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (succi A\<^sub>1, succ A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel \<and>
      (acceptingi A\<^sub>1, accepting A\<^sub>2) \<in> S \<rightarrow> bool_rel \<and>
      (nbai.more A\<^sub>1, nba.more A\<^sub>2) \<in> M}"

  lemma nbai_nba_param[param]:
    "(nbai_ext, nba_ext) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> \<langle>S\<rangle> list_set_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel) \<rightarrow>
      (S \<rightarrow> bool_rel) \<rightarrow> M \<rightarrow> \<langle>L, S, M\<rangle> nbai_nba_rel"
    "(alphabeti, alphabet) \<in> \<langle>L, S, M\<rangle> nbai_nba_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initiali, initial) \<in> \<langle>L, S, M\<rangle> nbai_nba_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(succi, succ) \<in> \<langle>L, S, M\<rangle> nbai_nba_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(acceptingi, accepting) \<in> \<langle>L, S, M\<rangle> nbai_nba_rel \<rightarrow> S \<rightarrow> bool_rel"
    "(nbai.more, nba.more) \<in> \<langle>L, S, M\<rangle> nbai_nba_rel \<rightarrow> M"
    unfolding nbai_nba_rel_def fun_rel_def by auto

  definition nba :: "('label, 'state, 'more) nbai_scheme \<Rightarrow> ('label, 'state, 'more) nba_scheme" where
    "nba A \<equiv> \<lparr> alphabet = set (alphabeti A), initial = set (initiali A),
      succ = \<lambda> a p. set (succi A a p), accepting = acceptingi A, \<dots> = nbai.more A \<rparr>"
  definition nbai :: "('label, 'state, 'more) nbai_scheme \<Rightarrow> bool" where
    "nbai A \<equiv> distinct (alphabeti A) \<and> distinct (initiali A) \<and> (\<forall> a p. distinct (succi A a p))"

  lemma nbai_nba_br: "\<langle>Id, Id, Id\<rangle> nbai_nba_rel = br nba nbai"
    unfolding nbai_nba_rel_def nba_def nbai_def
    by (fastforce intro!: nba.equality simp: fun_rel_def in_br_conv list_set_rel_def)

  lemma ba_id_param[param]: "(nba, id) \<in> \<langle>L, S, M\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, S, M\<rangle> nba_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S, M\<rangle> nbai_nba_rel"
    have 2: "nba Ai = \<lparr> alphabet = set (alphabeti Ai), initial = set (initiali Ai),
      succ = \<lambda> a p. set (succi Ai a p), accepting = acceptingi Ai, \<dots> = nbai.more Ai \<rparr>"
      unfolding nba_def by rule
    have 3: "id A = \<lparr> alphabet = id (alphabet A), initial = id (initial A),
      succ = \<lambda> a p. id (succ A a p), accepting = accepting A, \<dots> = nba.more A \<rparr>" by simp
    show "(nba Ai, id A) \<in> \<langle>L, S, M\<rangle> nba_rel" unfolding 2 3 using 1 by parametricity
  qed

  (* TODO: take a look at Digraph_Impl setup to make synthesizing whole nbai/bae possible *)
  lemmas [autoref_rules] = nbai_nba_param(2-6)

end