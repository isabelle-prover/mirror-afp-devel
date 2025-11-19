theory Clause_Typing_Generic
  imports
    Multiset_Typing_Lifting
    Multiset_Extra
    Literal_Functor
begin

locale clause_typing_generic = atom: typing atom_welltyped
  for atom_welltyped
begin

sublocale literal: typing_lifting where
  sub_welltyped = atom_welltyped and to_set = set_literal
  by unfold_locales

sublocale clause: mulitset_typing_lifting where 
  sub_welltyped = literal.welltyped
  by unfold_locales

end

end
