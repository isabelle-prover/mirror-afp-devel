(*  Title:       EpiMonoIso
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter EpiMonoIso

theory EpiMonoIso
imports Category
begin

  text{*
    This theory defines and develops properties of epimorphisms, monomorphisms,
    isomorphisms, sections, and retractions.
  *}

  context category
  begin

     definition epi
     where "epi f = (arr f \<and> inj_on (\<lambda>g. C g f) {g. seq g f})"

     definition mono
     where "mono f = (arr f \<and> inj_on (C f) {g. seq f g})"

     lemma epiI [intro]:
     assumes "arr f" and "\<And>g g'. \<lbrakk> seq g f; seq g' f; C g f = C g' f \<rbrakk> \<Longrightarrow> g = g'"
     shows "epi f"
       using assms epi_def inj_on_def by blast

     lemma epi_implies_arr:
     assumes "epi f"
     shows "arr f"
       using assms epi_def by auto

     lemma epiE [elim]:
     assumes "epi f" and "seq g f" and "seq g' f" and "C g f = C g' f"
     shows "g = g'"
       using assms unfolding epi_def inj_on_def by blast
       
     lemma monoI [intro]:
     assumes "arr g" and "\<And>f f'. \<lbrakk> seq g f; seq g f'; C g f = C g f' \<rbrakk> \<Longrightarrow> f = f'"
     shows "mono g"
       using assms mono_def inj_on_def by blast

     lemma mono_implies_arr:
     assumes "mono f"
     shows "arr f"
       using assms mono_def by auto
       
     lemma monoE [elim]:
     assumes "mono g" and "seq g f" and "seq g f'" and "C g f = C g f'"
     shows "f' = f"
       using assms unfolding mono_def inj_on_def by blast

     definition section_retraction
     where "section_retraction m e \<equiv> antipar m e \<and> ide (C e m)"

     definition inverse_arrows
     where "inverse_arrows f g \<equiv> antipar f g \<and> ide (C g f) \<and> ide (C f g)"

     lemma section_retractionI [intro]:
     assumes "antipar m e" and "ide (C e m)"
     shows "section_retraction m e"
       using assms section_retraction_def by auto

     lemma section_retractionD [dest]:
     assumes "section_retraction m e"
     shows "arr m" and "arr e" and "cod m = dom e" and "cod e = dom m" and "ide (C e m)"
       using assms section_retraction_def by simp_all

     lemma inverse_arrowsI [intro]:
     assumes "antipar f g" and "ide (C g f)" and "ide (C f g)"
     shows "inverse_arrows f g"
       using assms inverse_arrows_def by auto

     lemma inverse_arrowsD [dest]:
     assumes "inverse_arrows f g"
     shows "antipar f g" and "ide (C g f)" and "ide (C f g)"
       using assms inverse_arrows_def by auto

     lemma inverse_arrows_sym:
     shows "inverse_arrows f g \<longleftrightarrow> inverse_arrows g f"
       by fastforce

     lemma inverse_arrow_unique:
     assumes "inverse_arrows f g" and "inverse_arrows f g'"
     shows "g = g'"
     proof -
       have "g = C g (C f g')"
       proof -
         have "dom (C f g') = dom g'"
           using assms(2) by force
         thus ?thesis
           using assms inverse_arrowsD(1) inverse_arrowsD(3) by auto
       qed
       also have "... = C (C g f) g'"
         using assms by fastforce
       also have "... = g'"
       proof -
         have "dom (C g f) = dom f"
           using assms(1) by force
         thus ?thesis using assms by fastforce
       qed
       finally show ?thesis by auto
     qed

     lemma inverse_arrows_compose:
     assumes "seq g f" and "inverse_arrows f f'" and "inverse_arrows g g'"
     shows "inverse_arrows (C g f) (C f' g')"
     proof
       show 1: "antipar (C g f) (C f' g')" using assms by fastforce
       hence 2: "seq g f \<and> seq f f' \<and> seq f' g' \<and> seq g g'"
         using assms by (simp add: inverse_arrowsD(1))
       show "ide (C (C g f) (C f' g'))"
       proof -
         have "C (C g f) (C f' g') = C g (C (C f f') g')"
           using 2 by simp
         thus ?thesis
           using 2 assms inverse_arrowsD(3)
           by (metis comp_cod_arr dom_comp ideD(2))
       qed
       show "ide (C (C f' g') (C g f))"
       proof -
         have "C (C f' g') (C g f) = C f' (C (C g' g) f)"
           using 1 2 by simp
         also have "... = dom f"
           using 2 assms(3) ide_comp_simp
           by (metis assms(2) comp_cod_arr inverse_arrowsD(2))
         finally show ?thesis using 2 by auto
       qed
     qed

     definition "section"
     where "section f \<equiv> \<exists>g. section_retraction f g"

     lemma sectionI [intro]:
     assumes "section_retraction f g"
     shows "section f"
       using assms section_def by auto

     lemma sectionE [elim]:
     assumes "section f"
     obtains g where "section_retraction f g"
       using assms section_def by blast

     definition retraction
     where "retraction g \<equiv> \<exists>f. section_retraction f g"

     lemma retractionI [intro]:
     assumes "section_retraction f g"
     shows "retraction g"
       using assms retraction_def by auto

     lemma retractionE [elim]:
     assumes "retraction g"
     obtains f where "section_retraction f g"
       using assms retraction_def by blast
       
     lemma section_is_mono:
     assumes "section g"
     shows "mono g"
     proof
       show "arr g" using assms section_def section_retraction_def by blast
       from assms obtain h where h: "section_retraction g h" by blast
       have hg: "seq h g" using h by auto
       fix f f'
       assume gf: "seq g f" and gf': "seq g f'" and ff': "C g f = C g f'"
       show "f = f'"
       proof -
         have "f = C (C h g) f"
           using gf h ide_comp_simp by auto
         also have "... = C h (C g f)"
           using gf h by auto
         also have "... = C h (C g f')"
           using ff' by auto
         also have "... = C (C h g) f'"
           using gf' hg h by auto
         also have "... = f'"
           using gf' h ide_comp_simp by auto
         finally show ?thesis by auto
       qed
     qed

     lemma retraction_is_epi:
     assumes "retraction g"
     shows "epi g"
     proof
       show "arr g" using assms retraction_def section_retraction_def by blast
       from assms obtain f where f: "section_retraction f g" by blast
       have gf: "seq g f" using f by auto
       fix h h'
       assume hg: "seq h g" and h'g: "seq h' g" and hh': "C h g = C h' g"
       have "h = C h (C g f)"
         using hg gf f ide_comp_simp section_retractionD(4) by auto
       also have "... = C (C h g) f"
         using hg gf by simp
       also have "... = C (C h' g) f"
         using hh' by simp
       also have "... = C h' (C g f)"
         using h'g gf by simp
       also have "... = h'"
         using h'g gf f ide_comp_simp section_retractionD(4) by auto
       finally show "h = h'" by auto
     qed

     lemma section_retraction_compose:
     assumes "section_retraction m e" and "section_retraction m' e'" and "seq m' m"
     shows "section_retraction (C m' m) (C e e')"
     proof
       show "antipar (C m' m) (C e e')"
         using assms
         by (simp add: section_retractionD(2) section_retractionD(3) section_retractionD(4))
       show "ide (C (C e e') (C m' m))"
       proof -
         have 1: "seq e e' \<and> seq m' m \<and> seq e' m'"
           using assms section_retractionD(2) section_retractionD(3) section_retractionD(4)
           by simp
         hence "C (C e e') (C m' m) = C (C e (C e' m')) m"
           using assms by simp
         also have "... = dom m"
           using assms 1 ide_comp_simp
           by (metis comp_arr_dom section_retractionD(4) section_retractionD(5))
         also have "... = dom (C m' m)"
           using 1 by simp
         finally show ?thesis using assms(3) by simp
       qed
     qed

     lemma sections_compose:
     assumes "section m" and "section m'" and "seq m' m"
     shows "section (C m' m)"
     proof -
       from assms(1) assms(2) obtain e e'
       where "section_retraction m e" and "section_retraction m' e'"
         using section_def by fastforce
       thus ?thesis using assms(3) section_retraction_compose by blast
     qed

     lemma retractions_compose:
     assumes "retraction e" and "retraction e'" and "seq e' e"
     shows "retraction (C e' e)"
     proof -
       from assms(1) assms(2) obtain m m'
       where *: "section_retraction m e" "section_retraction m' e'"
         using retraction_def by fastforce
       then have "seq m m'"
         using assms(3)
         by (simp add: section_retractionD(1) section_retractionD(3) section_retractionD(4))
       with * show ?thesis using section_retraction_compose by blast
     qed
       
     lemma monos_compose:
     assumes "mono m" and "mono m'" and "seq m' m"
     shows "mono (C m' m)"
     proof -
       have "inj_on (C (C m' m)) {f. seq (C m' m) f}"
         unfolding inj_on_def using assms by fastforce
       thus ?thesis using assms(3) mono_def by force
     qed           

     lemma epis_compose:
     assumes "epi e" and "epi e'" and "seq e' e"
     shows "epi (C e' e)"
     proof -
       have "inj_on (\<lambda>g. C g (C e' e)) {g. seq g (C e' e)}"
         unfolding inj_on_def using assms by fastforce
       thus ?thesis using assms(3) epi_def by force
     qed           

     definition iso
     where "iso f \<equiv> \<exists>g. inverse_arrows f g"

     lemma isoI [intro]:
     assumes "inverse_arrows f g"
     shows "iso f"
       using assms iso_def by meson

     lemma isoE [elim]:
     assumes "iso f"
     obtains g where "inverse_arrows f g"
       using assms iso_def by blast
       
     lemma ide_is_iso [simp]:
     assumes "ide a"
     shows "iso a"
       using assms by fastforce

     lemma iso_is_arr [simp]:
     assumes "iso f"
     shows "arr f"
       using assms by blast

     lemma iso_is_section:
     assumes "iso f"
     shows "section f"
       using assms inverse_arrows_def by blast

     lemma iso_is_retraction:
     assumes "iso f"
     shows "retraction f"
     proof -
       from assms obtain g where "inverse_arrows f g" by fast
       hence "inverse_arrows g f" using inverse_arrows_sym by auto
       thus ?thesis by auto
     qed

     lemma iso_iff_section_and_retraction:
     shows "iso f \<longleftrightarrow> section f \<and> retraction f"
     proof
       show "iso f \<Longrightarrow> section f \<and> retraction f"
         by (simp add: iso_is_retraction iso_is_section)
       show "section f \<and> retraction f \<Longrightarrow> iso f"
       proof -
         assume f: "section f \<and> retraction f"
         from f obtain g where g: "section_retraction f g" by blast
         from f obtain g' where g': "section_retraction g' f" by blast
         have "g = g'"
         proof -
           have "g = C g (C f g')"
             using g g'
             by (metis comp_arr_dom ide_comp_simp section_retractionD(2) section_retractionD(3)
                       section_retractionD(4) section_retractionD(5))
           also have "... = C (C g f) g'"
             using g g'
             by (simp add: section_retractionD(1) section_retractionD(2) section_retractionD(3))
           also have "... = g'"
             using g g'
             by (simp add: section_retractionD(1)section_retractionD(3) section_retractionD(5)
                 ide_comp_simp)
           finally show ?thesis by auto
         qed
         hence "\<exists>g. inverse_arrows f g"
           using g g' by fastforce
         thus "iso f" by auto
       qed
     qed

     lemma isos_compose:
     assumes "iso f" and "iso f'" and "seq f' f"
     shows "iso (C f' f)"
     proof -
       from assms(1) obtain g where g: "inverse_arrows f g" by blast
       from assms(2) obtain g' where g': "inverse_arrows f' g'" by blast
       have "inverse_arrows (C f' f) (C g g')"
       proof
         show "antipar (C f' f) (C g g')"
           using assms g g' by (simp add: inverse_arrowsD(1))
         show "ide (C (C f' f) (C g g'))"
           using assms g g' by (simp add: inverse_arrowsD(3) inverse_arrows_compose)
         show "ide (C (C g g') (C f' f))"
           using assms g g' by (simp add: inverse_arrowsD(2) inverse_arrows_compose)
       qed
       thus ?thesis using iso_def by auto
     qed

     definition isomorphic
     where "isomorphic a a' = (\<exists>f. f \<in> hom a a' \<and> iso f)"

     lemma isomorphicI [intro]:
     assumes "iso f"
     shows "isomorphic (dom f) (cod f)"
       using assms isomorphic_def iso_is_arr by fast

     lemma isomorphicE [elim]:
     assumes "isomorphic a a'"
     obtains f where "f \<in> hom a a' \<and> iso f"
       using assms isomorphic_def by meson

     definition inv
     where "inv f = (SOME g. inverse_arrows f g)"

     lemma inv_is_inverse:
     assumes "iso f"
     shows "inverse_arrows f (inv f)"
     proof -
       from assms obtain g where "inverse_arrows f g" by blast
       hence "inverse_arrows f (SOME g. inverse_arrows f g)"
         using someI [of "inverse_arrows f"] by blast
       thus ?thesis using inv_def by auto
     qed
     
     lemma iso_inv_iso:
     assumes "iso f"
     shows "iso (inv f)"
       using assms inv_is_inverse inverse_arrows_sym by blast

     lemma inverse_unique:
     assumes "inverse_arrows f g"
     shows "inv f = g"
     proof -
       have "C f (inv f) = C f g"
         using assms inv_is_inverse inverse_arrow_unique isoI by auto
       thus ?thesis
         using assms
         by (metis (mono_tags, lifting) arr_compD(1) arr_compD(3) arr_comp inverse_arrowsD(1)
             monoE isoI iso_is_section section_is_mono)
     qed

     lemma inv_ide [simp]:
     assumes "ide a"
     shows "inv a = a"
     proof -
       have "inverse_arrows a a" using assms by auto
       thus ?thesis using inverse_unique by simp
     qed

     lemma inv_inv [simp]:
     assumes "iso f"
     shows "inv (inv f) = f"
       using assms inverse_arrows_sym inverse_unique by blast

  end

end


