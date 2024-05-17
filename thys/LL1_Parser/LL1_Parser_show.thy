subsection\<open>Interpretation\<close>

theory LL1_Parser_show
  imports LL1_Parser "Show.Show"
begin

global_interpretation parse_show: parse "show" "show"
  defines parse = parse_show.parse
    and parseToString = parse_show.parseToString
    and parseSymbol = parse_show.parseSymbol
    and parseGamma = parse_show.parseGamma
    and mismatchMessage = parse_show.mismatchMessage
  done

end