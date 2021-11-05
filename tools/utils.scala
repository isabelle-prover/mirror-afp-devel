package afp


import scala.collection.immutable.ListMap


object Utils
{
  def group_sorted[A, K](l: List[A], f: A => K): ListMap[K, List[A]] =
    l.foldRight(ListMap.empty[K, List[A]]) {
      case (a, m) =>
        m.updatedWith(f(a)) {
          case Some(as) => Some(a :: as)
          case None => Some(List(a))
        }
    }
}