theory Ground_Order_Generic
  imports Ground_Term_Order Term_Order_Lifting
begin

locale ground_order_generic =
  term.order: ground_term_order +
  term_order_lifting

end
