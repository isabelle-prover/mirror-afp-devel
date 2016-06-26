(*  Title:       DiscreteCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter DiscreteCategory

theory DiscreteCategory
imports Category
begin

  text{*
    The locale defined here permits us to construct a discrete category having
    a specified set of objects, assuming that the set does not exhaust the elements
    of its type.  In that case, we have the convenient situation that the arrows of
    the category can be directly identified with the elements of the given set,
    rather than having to pass between the two via tedious coercion maps.
    If it cannot be guaranteed that the given set is not the universal set at its type,
    then the more general discrete category construction defined (using coercions)
    in @{text FreeCategory} can be used.
  *}

  locale discrete_category =
    fixes Obj :: "'a set"
    assumes Obj_not_UNIV: "Obj \<noteq> UNIV"
  begin

    definition Null :: 'a
    where "Null \<equiv> (SOME x. x \<notin> Obj)"

    lemma Null_not_in_Obj:
    shows "Null \<notin> Obj"
      using Null_def Obj_not_UNIV someI_ex [of "\<lambda>x. x \<notin> Obj"] by auto

    definition comp :: "'a comp"
    where "comp y x \<equiv> (if x \<in> Obj \<and> x = y then x else Null)"

    interpretation partial_magma comp
      apply unfold_locales
      using comp_def by metis

    lemma null_char:
    shows "null = Null"
      using comp_def null_def by auto

    lemma unit_char:
    shows "unit f \<longleftrightarrow> True"
      using comp_def null_char unit_def by auto

    theorem is_category:
    shows "category comp"
      using comp_def
      apply unfold_locales
      (* 6 *) apply (metis null_char)
      (* 5 *) apply (metis null_char)
      (* 4 *) apply (metis null_char)
      (* 3 *) apply (metis null_char)
      (* 2 *) apply auto[1]
      (* 1 *) by (metis (no_types, lifting) has_cod_def has_dom_def)

  end

  sublocale discrete_category \<subseteq> category comp
    using is_category by auto

  context discrete_category
  begin

    lemma arr_char [iff]:
    shows "arr f \<longleftrightarrow> f \<in> Obj"
      using comp_def arr_def has_cod_def has_dom_def null_char unit_char Null_not_in_Obj by metis

    lemma ide_char [iff]:
    shows "ide f \<longleftrightarrow> f \<in> Obj"
      using comp_def arr_char Null_not_in_Obj by (metis comp_cod_arr ideI_cod ideD(1))

    lemma dom_char [iff]:
    shows "dom f = (if f \<in> Obj then f else null)"
      using comp_def arrI arr_char comp_arr_dom dom_def null_char Null_not_in_Obj by metis

    lemma cod_char [iff]:
    shows "cod f = (if f \<in> Obj then f else null)"
      using comp_def arrI arr_char comp_cod_arr cod_def null_char Null_not_in_Obj by metis

    lemma comp_char [iff]:
    shows "comp g f = (if f \<in> Obj \<and> f = g then f else null)"
      using comp_def null_char Null_not_in_Obj by presburger

    lemma is_discrete:
    shows "ide f \<longleftrightarrow> arr f"
      using arr_char ide_char by auto

  end

end
