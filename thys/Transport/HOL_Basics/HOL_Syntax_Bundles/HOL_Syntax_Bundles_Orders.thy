\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Order Syntax\<close>
theory HOL_Syntax_Bundles_Orders
  imports HOL.Orderings
begin

bundle HOL_order_syntax
begin
notation
  less_eq  (\<open>'(\<le>')\<close>) and
  less_eq  (\<open>(\<open>notation=\<open>infix \<le>\<close>\<close>_/ \<le> _)\<close>  [51, 51] 50) and
  less  (\<open>'(<')\<close>) and
  less  (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ < _)\<close>  [51, 51] 50)
notation (input) greater_eq (infix \<open>\<ge>\<close> 50)
notation (input) greater (infix \<open>>\<close> 50)
notation (ASCII)
  less_eq  (\<open>'(<=')\<close>) and
  less_eq  (\<open>(\<open>notation=\<open>infix <=\<close>\<close>_/ <= _)\<close> [51, 51] 50)
notation (input) greater_eq (infix \<open>>=\<close> 50)
end

end