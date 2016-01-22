section {* Adapting the Isabelle Collection Framework for Jinja Threads *}
theory JT_ICF
imports "../../Collections/ICF/CollectionsV1"
begin

  text {* Hide stuff that may lead to confusions later *}

  hide_const (open) Array
  hide_type (open) array

  hide_type (open) Omega_Words_Fun.word

end
