package afp


import isabelle._

import scala.annotation.tailrec
import scala.collection.immutable.ListMap

import java.time.{LocalDate, LocalDateTime, LocalTime, OffsetDateTime}


object TOML
{
  type Key = String
  type V = Any

  type T = Map[Key, V]
  object T
  {
    def apply(entries: (Key, V)*): T = ListMap(entries: _*)
    def apply(entries: List[(Key, V)]): T = ListMap(entries: _*)

    def unapply(t: Map[_, V]): Option[T] = {
      if (t.keys.forall(_.isInstanceOf[Key])) Some(t.asInstanceOf[T])
      else None
    }
  }

  /* format to a subset of TOML */

  object Format
  {
    def apply(toml: T): String =
    {
      val result = new StringBuilder

      /* keys */

      def key(k: Key): Unit =
      {
        val Bare_Key = """[A-Za-z0-9_-].+""".r
        k match {
          case Bare_Key() => result ++= k
          case _ =>
            result += '"'
            result ++= k
            result += '"'
        }
      }

      def keys(ks: List[Key]): Unit =
        Library.separate(None, ks.reverse.map(Some(_))).foreach {
          case None => result += '.'
          case Some(k) => key(k)
        }

      /* string */

      def basic_string(s: String): Unit =
      {
        result += '"'
        result ++=
          s.iterator.map {
            case '\b' => "\\b"
            case '\t' => "\\t"
            case '\n' => "\\n"
            case '\f' => "\\f"
            case '\r' => "\\r"
            case '"'  => "\\\""
            case '\\' => "\\\\"
            case c =>
              if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt)
              else c
          }.mkString
        result += '"'
      }

      def multiline_basic_string(s: String): Unit =
      {
        result ++= "\"\"\"\n"
        result ++=
          s.iterator.map {
            case '\b' => "\\b"
            case '\t' => "\t"
            case '\n' => "\n"
            case '\f' => "\\f"
            case '\f' => "\f"
            case '"'  => "\\\""
            case '\\' => "\\\\"
            case c =>
              if (c <= '\u001f' || c == '\u007f') "\\u%04x".format(c.toInt)
              else c
          }.mkString.replace("\"\"\"", "\"\"\\\"")
        result ++= "\"\"\""
      }

      /* integer, boolean, offset date-time, local date-time, local date, local time */

      object To_String
      {
        def unapply(v: V): Option[String] = v match {
          case _: Int | _: Long | _: Boolean | _: OffsetDateTime |
               _: LocalDateTime | _: LocalDate | _: LocalTime => Some(v.toString)
          case _ => None
        }
      }

      /* inline: string, float, To_String, value array */

      def inline(v: V, indent: Int = 0): Unit =
      {
        def indentation(i: Int): Unit = for (_ <- Range(0, i)) result ++= "  "

        indentation(indent)
        v match {
          case s: String =>
            if (s.contains("\n") && s.length > 20) multiline_basic_string(s)
            else basic_string(s)
          case d: Double =>
            val i = d.toLong
            result ++= (if (i.toDouble == d) i.toString else d.toString)
          case To_String(s) =>
            result ++= s
          case list: List[V] =>
            if (list.isEmpty) {
              result ++= "[]"
            } else {
              result ++= "[\n"
              list.foreach { elem =>
                inline(elem, indent + 1)
                result ++= ",\n"
              }
              indentation(indent)
              result += ']'
            }
          case _ => error("Not inline TOML value: " + v.toString)
        }
      }

      /* array */

      def inline_values(path: List[Key], v: V): Unit =
      {
        v match {
          case T(map) => map.foreach { case (k, v1) => inline_values(k :: path, v1) }
          case _ =>
            keys(path)
            result ++= " = "
            inline(v)
            result += '\n'
        }
      }

      def is_inline(elem: V): Boolean = elem match {
        case To_String(_) | _: Double | _: String => true
        case list: List[V] => list.forall(is_inline)
        case _ => false
      }

      def array(path: List[Key], list: List[V]): Unit =
      {
        if (list.forall(is_inline)) inline_values(path.take(1), list)
        else {
          list.collect {
            case T(map) =>
              result ++= "\n[["
              keys(path)
              result ++= "]]\n"
              table(path, map, is_table_entry = true)
            case _ => error("Array can only contain either all tables or all non-tables")
          }
        }
      }

      /* table */

      def table(path: List[Key], map: T, is_table_entry: Boolean = false): Unit =
      {
        val (values, nodes) = map.toList.partition(kv => is_inline(kv._2))

        if (!is_table_entry && path.nonEmpty) {
          result ++= "\n["
          keys(path)
          result ++= "]\n"
        }

        values.foreach { case (k, v) => inline_values(List(k), v) }

        nodes.foreach {
          case (k, T(map1)) => table(k :: path, map1)
          case (k, list: List[V]) => array(k :: path, list)
          case (_, v) => error("Invalid TOML: " + v.toString)
        }
      }

      table(Nil, toml)
      result.toString
    }
  }
}
