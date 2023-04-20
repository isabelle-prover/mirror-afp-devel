theory SetCat_Interp
imports SetCat
begin

  text\<open>
    Here we demonstrate the possibility of making a top-level interpretation of
    the \<open>setcat\<close> locale.  It is possible for a locale to be uninterpretable in the
    top-level context, even if the locale definition itself is correct.  This occurs
    due to collisions of multiple entities with the same qualified name that happen
    when Isabelle attempts to construct the interpretation.  To avoid this, we are
    forced to introduce syntactic disambiguations, either for the names of the
    entities themselves, or else for the qualifiers that make up those names.
    It is odd that Isabelle is able to automatically perform such disambiguations
    within a locale context, but not at the top level, but until the situation changes,
    it seems useful to check at various points that certain important locales do
    indeed admit top-level interpretations.
\<close>

  interpretation NatSets: setcat \<open>TYPE(nat)\<close> \<open>\<lambda>x. True\<close>
    by unfold_locales blast+

end
