(*  Title:       InitialTerminal
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter InitialTerminal

theory InitialTerminal
imports EpiMonoIso
begin

  text{*
    This theory defines the notions of initial and terminal object in a category
    and establishes some properties of these notions, including that when they exist
    they are unique up to isomorphism.
  *}

  context category
  begin

    definition initial
    where "initial a \<equiv> ide a \<and> (\<forall>b. ide b \<longrightarrow> (\<exists>!f. f \<in> hom a b))"

    definition terminal
    where "terminal b \<equiv> ide b \<and> (\<forall>a. ide a \<longrightarrow> (\<exists>!f. f \<in> hom a b))"
    
    abbreviation is_initial_arr
    where "is_initial_arr f \<equiv> arr f \<and> initial (dom f)"
    
    abbreviation is_terminal_arr
    where "is_terminal_arr f \<equiv> arr f \<and> terminal (cod f)"
    
    abbreviation point
    where "point f \<equiv> arr f \<and> terminal (dom f)"

    lemma initialI [intro]:
    assumes "ide a" and "\<And>b. ide b \<Longrightarrow> \<exists>!f. f \<in> hom a b"
    shows "initial a"
      using assms initial_def by auto

    lemma initial_arr_exists:
    assumes "initial a" and "ide b"
    obtains f where "f \<in> hom a b"
      using assms initial_def by blast
      
    lemma initial_arr_unique:
    assumes "par f f'" and "is_initial_arr f" and "is_initial_arr f'"
    shows "f = f'"
    proof -
      have "\<exists>!i. i \<in> hom (dom f) (cod f)" using assms initial_def by simp
      thus ?thesis using assms by auto
    qed

    lemma terminalI [intro]:
    assumes "ide b" and "\<And>a. ide a \<Longrightarrow> \<exists>!f. f \<in> hom a b"
    shows "terminal b"
      using assms terminal_def by auto

    lemma terminal_arr_exists:
    assumes "ide a" and "terminal b"
    obtains f where "f \<in> hom a b"
      using assms terminal_def by blast

    lemma terminal_arr_unique:
    assumes "par f f'" and "is_terminal_arr f" and "is_terminal_arr f'"
    shows "f = f'"
    proof -
      have "\<exists>!t. t \<in> hom (dom f) (cod f)" using assms terminal_def by simp
      thus ?thesis using assms by auto
    qed

    lemma terminal_section_retraction:
    assumes "antipar f f'" and "terminal (dom f)"
    shows "section_retraction f f'"
    proof
      show "antipar f f'" using assms(1) by auto
      have "C f' f \<in> hom (dom f) (dom f) \<and> dom f \<in> hom (dom f) (dom f)"
        using assms(1) assms(2) by auto
      thus "ide (C f' f)"
        using assms terminal_def by metis
    qed

    theorem terminal_objs_isomorphic:
    assumes "terminal a" and "terminal b"
    shows "isomorphic a b"
    proof -
      from assms obtain f where f: "f \<in> hom a b" using terminal_def by blast
      from assms obtain f' where f': "f' \<in> hom b a" using terminal_def by blast
      have 1: "antipar f f' \<and> dom f = a \<and> dom f' = b"
        using f f' by auto
      hence "section_retraction f f' \<and> section_retraction f' f"
        using assms terminal_section_retraction by force
      hence "iso f" by fastforce
      thus ?thesis using isomorphicI 1 by force
    qed

    lemma initial_section_retraction:
    assumes "antipar f f'" and "initial (dom f)"
    shows "section_retraction f f'"
    proof
      show "antipar f f'" using assms(1) by auto
      have "C f' f \<in> hom (dom f) (dom f) \<and> dom f \<in> hom (dom f) (dom f)"
        using assms(1) assms(2) by auto
      thus "ide (C f' f)" using assms initial_def by metis
    qed

    theorem initial_objs_isomorphic:
    assumes "initial a" and "initial b"
    shows "isomorphic a b"
    proof -
       from assms obtain f where f: "f \<in> hom a b" using initial_def by blast
       from assms obtain f' where f': "f' \<in> hom b a" using initial_def by blast
       have 1: "antipar f f' \<and> dom f = a \<and> dom f' = b"
         using f f' by auto
       hence "section_retraction f f' \<and> section_retraction f' f"
             using assms initial_section_retraction by force
       hence "iso f" by fastforce
       thus ?thesis using isomorphicI 1 by force
    qed

    lemma point_is_mono:
    assumes "point f"
    shows "mono f"
    proof -
      have "ide (cod f)" using assms by auto
      from this obtain t where "t \<in> hom (cod f) (dom f)"
        using assms terminal_def by blast
      hence "section_retraction f t"
        using assms terminal_section_retraction by simp
      thus ?thesis using section_is_mono by auto
    qed
      
  end

end

